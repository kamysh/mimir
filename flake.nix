{
  description = "mimir: persistent belief graph MCP server for Claude Code";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "clippy" "rustfmt" "rust-analyzer" ];
          # musl target available in devShell for manual cross-compilation
          targets = [ "x86_64-unknown-linux-musl" ];
        };

        # agda.withPackages wraps the binary and registers stdlib automatically
        agdaWithStdlib = pkgs.agda.withPackages (ps: [ ps.standard-library ]);

        # ── ONNX Runtime static archive (Pyke prebuilt) ──────────────────────
        #
        # ort-sys with the `ort-download-binaries-*` Cargo feature normally
        # fetches libonnxruntime.a from cdn.pyke.io at build time. The Nix
        # sandbox has no network, so we mirror the same archive via a
        # fixed-output `fetchurl`, decompress the raw LZMA2 stream with `xz`
        # (64 MiB dict), and point ort-sys at the result via ORT_LIB_LOCATION.
        #
        # Hashes come from ort-sys's build/download/dist.txt. Update both
        # `pykeVersion` and per-target sha256 when ort-sys bumps the release.
        pykeVersion = "1.23.2";
        pykeTargets = {
          "aarch64-darwin" = {
            target = "aarch64-apple-darwin";
            sha256 = "0897a0e1b840566a97e5a49497b02cbc204be2d006815174b639bc99731840f9";
          };
          "x86_64-linux" = {
            target = "x86_64-unknown-linux-gnu";
            sha256 = "8c57d059aaaee407812a5698d6706c79e090ad69e1a14204309e802dcbbaa35f";
          };
          "aarch64-linux" = {
            target = "aarch64-unknown-linux-gnu";
            sha256 = "c25248c32d84f228b9d584b84b31e1577e4810d46beb5e304e9fa340c000176c";
          };
        };
        pyke = pykeTargets.${system} or null;

        ortStaticLib = if pyke == null then null else
          let
            archive = pkgs.fetchurl {
              url = "https://cdn.pyke.io/0/pyke:ort-rs/ms@${pykeVersion}/${pyke.target}.tar.lzma2";
              inherit (pyke) sha256;
            };
          in pkgs.runCommandLocal "onnxruntime-pyke-${pykeVersion}-${pyke.target}" {
            nativeBuildInputs = [ pkgs.xz pkgs.gnutar ];
          } ''
            mkdir -p $out
            xz --format=raw --lzma2=dict=64MiB -d < ${archive} | tar -x -C $out
          '';

        # ── glibc stubs for musl builds (x86_64-linux and aarch64-linux) ──────
        #
        # musl lacks several glibc-specific symbols that transitive C
        # dependencies (compiled with glibc GCC) may reference:
        #   • _FORTIFY_SOURCE=2 wrappers: __memcpy_chk, __strcpy_chk, etc.
        #   • glibc 2.38+ C23 aliases: __isoc23_strtol and family
        #   • glibc large-file aliases: stat64, fstat64, lstat64
        #
        # On aarch64 we additionally stub __aarch64_cas*_sync: compiler_builtins
        # provides acq/rel/acq_rel/relax CAS but NOT sync variants.
        # Separate archive object avoids multiple-definition conflicts.
        #
        # -lc is appended after stubs so musl re-scans and resolves
        # vprintf/strncat/stat referenced from our stubs.
        glibcStubs = if system != "aarch64-linux" && system != "x86_64-linux" then null else
          pkgs.pkgsStatic.stdenv.mkDerivation {
            name = "glibc-musl-stubs";
            unpackPhase = ":";
            buildPhase = ''
              cat > stubs.c << 'EOF'
              #include <string.h>
              #include <stdio.h>
              #include <stdarg.h>
              #include <stdlib.h>
              #include <stdint.h>
              #include <unistd.h>

              /* _FORTIFY_SOURCE pass-throughs */
              char __libc_single_threaded = 0;
              void *__memcpy_chk(void *d,const void *s,size_t n,size_t ds){return memcpy(d,s,n);}
              void *__memmove_chk(void *d,const void *s,size_t n,size_t ds){return memmove(d,s,n);}
              void *__memset_chk(void *s,int c,size_t n,size_t ds){return memset(s,c,n);}
              void *__mempcpy_chk(void *d,const void *s,size_t n,size_t ds){return memcpy(d,s,n);}
              char *__strcpy_chk(char *d,const char *s,size_t ds){return strcpy(d,s);}
              char *__strncpy_chk(char *d,const char *s,size_t n,size_t ds){return strncpy(d,s,n);}
              char *__strcat_chk(char *d,const char *s,size_t ds){return strcat(d,s);}
              char *__strncat_chk(char *d,const char *s,size_t n,size_t ds){return strncat(d,s,n);}
              ssize_t __read_chk(int fd,void *buf,size_t n,size_t bs){return read(fd,buf,n);}
              int __printf_chk(int f,const char *fmt,...){va_list a;va_start(a,fmt);int r=vprintf(fmt,a);va_end(a);return r;}
              int __fprintf_chk(FILE *fp,int f,const char *fmt,...){va_list a;va_start(a,fmt);int r=vfprintf(fp,fmt,a);va_end(a);return r;}
              int __sprintf_chk(char *s,int f,size_t ss,const char *fmt,...){va_list a;va_start(a,fmt);int r=vsprintf(s,fmt,a);va_end(a);return r;}
              int __snprintf_chk(char *s,size_t n,int f,size_t ss,const char *fmt,...){va_list a;va_start(a,fmt);int r=vsnprintf(s,n,fmt,a);va_end(a);return r;}
              int __vprintf_chk(int f,const char *fmt,va_list a){return vprintf(fmt,a);}
              int __vfprintf_chk(FILE *fp,int f,const char *fmt,va_list a){return vfprintf(fp,fmt,a);}
              int __vsprintf_chk(char *s,int f,size_t ss,const char *fmt,va_list a){return vsprintf(s,fmt,a);}
              int __vsnprintf_chk(char *s,size_t n,int f,size_t ss,const char *fmt,va_list a){return vsnprintf(s,n,fmt,a);}

              /* C23 strtol-family (glibc 2.38+, absent from musl) */
              long __isoc23_strtol(const char *s,char **e,int b){return strtol(s,e,b);}
              unsigned long __isoc23_strtoul(const char *s,char **e,int b){return strtoul(s,e,b);}
              long long __isoc23_strtoll(const char *s,char **e,int b){return strtoll(s,e,b);}
              unsigned long long __isoc23_strtoull(const char *s,char **e,int b){return strtoull(s,e,b);}

              /* glibc large-file aliases (musl uses 64-bit stat unconditionally) */
              #include <sys/stat.h>
              int stat64(const char *p,struct stat *b){return stat(p,b);}
              int fstat64(int fd,struct stat *b){return fstat(fd,b);}
              int lstat64(const char *p,struct stat *b){return lstat(p,b);}

              EOF
              $CC -c stubs.c -o stubs.o

              ${if system == "aarch64-linux" then ''
                # __aarch64_cas*_sync — separate object to avoid multiple-definition
                # conflicts with compiler_builtins (which provides acq/rel/acq_rel/relax
                # but NOT sync). XNNPack references cas8_sync.
                # -mno-outline-atomics prevents recursive __atomic_compare_exchange_n.
                cat > cas_sync.c << 'EOF'
                #include <stdint.h>
                #define CAS_SYNC(W,T) \
                T __aarch64_cas##W##_sync(T o,T n,volatile T*p){\
                  __atomic_compare_exchange_n(p,&o,n,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST);\
                  return o;}
                CAS_SYNC(1,uint8_t)
                CAS_SYNC(2,uint16_t)
                CAS_SYNC(4,uint32_t)
                CAS_SYNC(8,uint64_t)
                EOF
                $CC -c cas_sync.c -o cas_sync.o -mno-outline-atomics
                $AR rcs libglibc_stubs.a stubs.o cas_sync.o
              '' else ''
                $AR rcs libglibc_stubs.a stubs.o
              ''}
            '';
            installPhase = ''
              mkdir -p $out/lib
              cp libglibc_stubs.a $out/lib/
            '';
          };

        # Shared attrs for both packages
        commonAttrs = {
          pname = "mimir";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          doCheck = false; # integration tests require a live PostgreSQL connection
        };

        # ── mimir (dynamic) ──────────────────────────────────────────────────
        #
        # Links dynamically against nixpkgs's libonnxruntime. Smaller binary
        # but its load commands reference /nix/store/.../libonnxruntime.so, so
        # it only works on a machine where that path is materialised — use
        # `nix profile install .` so Nix keeps a GC root for it.
        mimir = pkgs.rustPlatform.buildRustPackage (commonAttrs // {
          buildInputs = [ pkgs.onnxruntime ];
          ORT_LIB_LOCATION = "${pkgs.onnxruntime}/lib";
          ORT_PREFER_DYNAMIC_LINK = "1";
          RUSTFLAGS = "-C link-arg=-Wl,-rpath,${pkgs.onnxruntime}/lib";
        });

        # ── mimir-static ─────────────────────────────────────────────────────
        #
        # Statically links libonnxruntime.a from the Pyke prebuilt archive.
        # rustls (pure Rust TLS) eliminates OpenSSL; glibcStubs handles musl
        # symbol gaps on Linux. Produces a single self-contained binary.
        mimirStatic = if ortStaticLib == null
          then throw "mimir-static: no Pyke onnxruntime prebuilt for system '${system}'. Build directly with `cargo build --release`."
          else pkgs.pkgsStatic.rustPlatform.buildRustPackage (commonAttrs // {
            buildInputs = if glibcStubs != null then [ glibcStubs ] else [];
            ORT_LIB_LOCATION = "${ortStaticLib}";
            RUSTFLAGS =
              # Linux: glibc stub archive for symbols absent from musl
              (if glibcStubs != null
                then "-C link-arg=-L${glibcStubs}/lib -C link-arg=-lglibc_stubs -C link-arg=-lc"
                else "") +
              # x86_64-linux: pkgsStatic defaults to -static-pie, but libstdc++.a
              # (pulled in by ORT's C++ runtime) is not compiled -fPIC.
              (if system == "x86_64-linux" then " -C relocation-model=static" else "");
          });

      in
      {
        packages = {
          default = mimir;
          mimir = mimir;
          mimir-static = mimirStatic;
        };

        devShells.default = pkgs.mkShell {
          name = "mimir-dev";

          packages = [
            # Rust (includes x86_64-unknown-linux-musl target for static builds)
            rustToolchain
            pkgs.cargo-watch
            pkgs.cargo-nextest

            # Database client tools (server assumed external)
            pkgs.sqlx-cli
            pkgs.postgresql_16  # psql client only

            # Formal spec
            agdaWithStdlib

            # Dev utilities
            pkgs.just
            pkgs.git
          ];

          shellHook = ''
            echo "mimir dev shell"
            echo "  Rust:  $(rustc --version)"
            echo "  Agda:  $(agda --version)"
          '';
        };
      }
    );
}
