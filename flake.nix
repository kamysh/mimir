{
  description = "ai-mem: persistent belief graph MCP server for Claude Code";

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
        };

        # agda.withPackages wraps the binary and registers stdlib automatically
        agdaWithStdlib = pkgs.agda.withPackages (ps: [ ps.standard-library ]);

        ai-mem = pkgs.rustPlatform.buildRustPackage {
          pname = "ai-mem";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          nativeBuildInputs = [ pkgs.pkg-config pkgs.makeWrapper ];
          buildInputs = [ pkgs.openssl ];
        };

      in
      {
        packages = {
          default = ai-mem;
          ai-mem = ai-mem;
        };

        devShells.default = pkgs.mkShell {
          name = "ai-mem-dev";

          packages = [
            # Rust
            rustToolchain
            pkgs.cargo-watch
            pkgs.cargo-nextest

            # Database client tools (server assumed external)
            pkgs.sqlx-cli
            pkgs.postgresql_16  # psql client only

            # Formal spec
            agdaWithStdlib

            # Build deps for sqlx/openssl
            pkgs.pkg-config
            pkgs.openssl

            # Dev utilities
            pkgs.just
            pkgs.git
          ];

          shellHook = ''
            if [[ -z "''${AI_MEM_DSN:-}" ]]; then
              export AI_MEM_DSN="postgresql://ai_mem@localhost:5450/ai_mem"
            fi

            echo "ai-mem dev shell"
            echo "  Rust:  $(rustc --version)"
            echo "  Agda:  $(agda --version)"
            echo "  AI_MEM_DSN=$AI_MEM_DSN"
          '';

          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
        };
      }
    );
}