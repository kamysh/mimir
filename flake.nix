{
  description = "mimir: persistent belief graph MCP server for Claude Code";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        # crates.io's API endpoint (crates.io/api/v1/crates/.../download) 403s
        # the default `curl/<ver>` UA that nixpkgs's per-crate `fetchurl`
        # (rustPlatform.importCargoLock) sends. nixpkgs fixed this upstream in
        # f830e61 by switching crate downloads to static.crates.io, but that
        # hasn't reached the nixos-unstable channel yet. Until our pinned
        # nixpkgs includes it, inject a contact-bearing UA on any fetchurl
        # pointing at crates.io so per-crate downloads succeed. Drop this
        # overlay once `nix flake update` pulls a rev with f830e61. UA only
        # affects fetch success, not the fixed-output hash. Every
        # non-crates.io fetchurl is untouched.
        cratesIoUa = "mimir-build (https://github.com/kamysh/mimir)";
        cratesIoUaOverlay = (final: prev: {
          fetchurl = args:
            let
              urls = args.urls or (if args ? url then [ args.url ] else [ ]);
              hitsCratesIo = builtins.any
                (u: prev.lib.hasPrefix "https://crates.io/" u
                  || prev.lib.hasPrefix "http://crates.io/" u)
                urls;
            in
            if hitsCratesIo
            then prev.fetchurl (args // {
              curlOptsList = (args.curlOptsList or [ ]) ++ [ "-A" cratesIoUa ];
            })
            else prev.fetchurl args;
        });
        overlays = [ (import rust-overlay) cratesIoUaOverlay ];
        pkgs = import nixpkgs { inherit system overlays; };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "clippy" "rustfmt" "rust-analyzer" ];
          # musl target available in devShell for manual cross-compilation
          targets = [ "x86_64-unknown-linux-musl" ];
        };

        # agda.withPackages wraps the binary and registers stdlib automatically
        agdaWithStdlib = pkgs.agda.withPackages (ps: [ ps.standard-library ]);

        # Shared attrs for both packages
        commonAttrs = {
          pname = "mimir";
          version = "0.2.1";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          doCheck = false; # integration tests require a live PostgreSQL connection
        };

        mimir = pkgs.rustPlatform.buildRustPackage commonAttrs;

        # ── mimir-static ─────────────────────────────────────────────────────
        #
        # On Linux: musl via pkgsStatic → fully static binary. hf-hub uses
        # ureq which links against OpenSSL; pkgsStatic provides the static
        # libssl/libcrypto. On macOS: Security.framework is a system framework
        # linked automatically, no extra inputs needed.
        mimirStatic = pkgs.pkgsStatic.rustPlatform.buildRustPackage (commonAttrs // {
          buildInputs = pkgs.lib.optionals (pkgs.lib.hasSuffix "linux" system) [
            pkgs.pkgsStatic.openssl
          ];
          nativeBuildInputs = pkgs.lib.optionals (pkgs.lib.hasSuffix "linux" system) [
            pkgs.pkg-config
          ];
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

          nativeBuildInputs = [ pkgs.pkg-config ];
          buildInputs = [ pkgs.openssl ];

          shellHook = ''
            echo "mimir dev shell"
            echo "  Rust:  $(rustc --version)"
            echo "  Agda:  $(agda --version)"
          '';
        };
      }
    );
}
