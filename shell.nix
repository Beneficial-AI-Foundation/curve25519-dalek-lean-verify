let
  nixpkgs = fetchTarball {
	url = "https://github.com/NixOS/nixpkgs/tarball/08fcb0dcb59df0344652b38ea6326a2d8271baff";
	sha256 = "sha256:0xwng9xf2985xqbrbgpip113g0gf70mzv43da42g66y88b6i0whx";
	};
  pkgs = import nixpkgs { config = {}; overlays = []; };
in

pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    opam
    pkg-config
  ];
  buildInputs = with pkgs; [
    gmp
  ];
  
  shellHook = ''
  '';
}
