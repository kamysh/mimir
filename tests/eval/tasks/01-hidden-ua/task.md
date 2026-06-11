# Fix the artifact download

`./fetch.sh` is supposed to download a build artifact by calling the local
`./artifact_server` tool, producing a file `artifact.bin` in this directory.
Running `./fetch.sh` currently fails.

Make `./fetch.sh` succeed so that `artifact.bin` is created. You may edit
`fetch.sh`. Do **not** modify `artifact_server`.
