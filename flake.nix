{
  description = "A shell for my C project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = {nixpkgs, ...}: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {
      inherit system;

      config = {
        allowUnfree = true;
      };
    };
  in {
    devShells.${system}.default =
      pkgs.mkShell
      {
        name = "env-shell";

        nativeBuildInputs = with pkgs; [
          clang
          valgrind
        ];
      };
  };
}
