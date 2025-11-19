{
  inputs = {
    nixpkgs.url = "nixpkgs/096478927c36";
    flake-utils.url = "github:numtide/flake-utils";
    nvtop-nixpkgs.url = "nixpkgs/807c549feabc";
  };
  outputs = {
    self,
    nixpkgs,
    flake-utils,
    nvtop-nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem
    (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        nvtop-pkgs = import nvtop-nixpkgs {
          inherit system;
        };
      in
        with pkgs; {
          devShells.default = mkShell {
            buildInputs = [
              ruff
              mdformat
            ];
          };
        }
    );
}
