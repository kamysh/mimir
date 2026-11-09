//! Offline executable tests: the signal fixtures run outside libtest's threads.
#[path = "process.rs"]
mod process;

use std::ffi::CString;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::Command;

fn fifo(path: &Path) {
    let path = CString::new(path.as_os_str().as_encoded_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(path.as_ptr(), 0o600) }, 0);
}

fn receive_pid(path: &Path) -> i32 {
    let mut value = String::new();
    fs::File::open(path)
        .unwrap()
        .read_to_string(&mut value)
        .unwrap();
    value.trim().parse().unwrap()
}

fn cancellation_child(root: &Path) {
    let error = process::run(
        Command::new("sh")
            .arg("-c")
            .arg("printf 'before cancellation\n'; printf 'stderr before cancellation\n' >&2; sh -c 'echo $$ > \"$1/grandchild\"; read ignored < \"$1/blocked\"' sh \"$1\" & echo $$ > \"$1/leader\"; wait")
            .arg("sh")
            .arg(root),
        None,
    ).unwrap_err();
    let cancelled = error.downcast_ref::<process::Cancelled>().unwrap();
    assert_eq!(cancelled.signal, libc::SIGINT);
    assert_eq!(cancelled.output.stdout, b"before cancellation\n");
    assert_eq!(cancelled.output.stderr, b"stderr before cancellation\n");
    assert_eq!(
        unsafe { libc::waitpid(-1, std::ptr::null_mut(), libc::WNOHANG) },
        -1
    );
    assert_eq!(
        std::io::Error::last_os_error().raw_os_error(),
        Some(libc::ECHILD)
    );
    fs::write(
        root.join("reaped"),
        b"cancelled; complete output; no unreaped owned child\n",
    )
    .unwrap();
}

fn main() {
    let args: Vec<_> = std::env::args_os().collect();
    if args.get(1).is_some_and(|arg| arg == "--cancellation-child") {
        cancellation_child(Path::new(&args[2]));
        return;
    }
    let root = std::env::temp_dir().join(format!("mimir-eval-lifecycle-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    struct Cleanup(std::path::PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(root.clone());

    // Both pipes exceed kernel capacity, while stdin is also larger than a pipe.
    let input = vec![b'x'; 2 * 1024 * 1024 + 1];
    let output = process::run(
        Command::new("sh").args([
            "-c",
            r"cat; printf '\377' >&2; head -c 2097153 /dev/zero >&2; exit 7",
        ]),
        Some(&input),
    )
    .unwrap();
    assert_eq!(output.status.code(), Some(7));
    assert_eq!(output.stdout, input);
    assert_eq!(output.stderr.len(), 2 * 1024 * 1024 + 2);
    assert_eq!(output.stderr[0], 0xff);
    assert!(output.stderr[1..].iter().all(|byte| *byte == 0));
    println!("PASS complete concurrent input/stdout/stderr and failed exit");

    let missing = process::run(&mut Command::new(root.join("missing")), None).unwrap_err();
    assert!(missing.to_string().contains("start evaluation child"));
    println!("PASS failed spawn restores lifecycle state");

    for name in ["leader", "grandchild", "blocked"] {
        fifo(&root.join(name));
    }
    let mut helper = Command::new(std::env::current_exe().unwrap())
        .arg("--cancellation-child")
        .arg(&root)
        .spawn()
        .unwrap();
    let leader = receive_pid(&root.join("leader"));
    let grandchild = receive_pid(&root.join("grandchild"));
    assert_eq!(unsafe { libc::kill(helper.id() as i32, libc::SIGINT) }, 0);
    assert!(helper.wait().unwrap().success());
    assert!(root.join("reaped").is_file());
    assert_eq!(unsafe { libc::kill(leader, 0) }, -1, "leader was reaped");
    // The killed descendant belongs to the OS reaper after its parent exits;
    // it must be absent or a zombie, never executing or holding an output pipe.
    match fs::read_to_string(format!("/proc/{grandchild}/stat")) {
        Ok(stat) => assert!(stat.split_once(") ").unwrap().1.starts_with('Z')),
        Err(error) => assert_eq!(error.kind(), std::io::ErrorKind::NotFound),
    }
    println!("PASS explicit SIGINT cancels the group, preserves output, reaps owned child");
}
