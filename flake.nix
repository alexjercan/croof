{
  description = "A basic flake for my Rust Project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }: (
    flake-utils.lib.eachDefaultSystem
    (system: let
      pkgs = import nixpkgs {
        inherit system;

        config = {
          allowUnfree = true;
        };
      };
      manifest = (pkgs.lib.importTOML ./Cargo.toml).package;
    in {
      packages.default = pkgs.rustPlatform.buildRustPackage {
        pname = manifest.name;
        version = manifest.version;
        cargoLock.lockFile = ./Cargo.lock;
        src = pkgs.lib.cleanSource ./.;
      };

      devShells.default = pkgs.mkShell rec {
        nativeBuildInputs = with pkgs; [
          cargo
          rustc
          rustfmt
          clippy
        ];

        buildInputs = with pkgs; [ ];

        LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath buildInputs;

        RUST_BACKTRACE = 1;

        RUST_SRC_PATH = "${pkgs.rust.packages.stable.rustPlatform.rustLibSrc}";
      };
    })
  );
}
