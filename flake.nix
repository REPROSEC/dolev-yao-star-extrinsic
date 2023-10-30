{
  inputs = {
    fstar-flake.url = "github:FStarLang/FStar";
    nixpkgs.follows = "fstar-flake/nixpkgs";

    comparse-flake = {
      url = "github:TWal/comparse";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-flake.follows = "fstar-flake";
    };
  };

  outputs = {self, nixpkgs, fstar-flake, comparse-flake}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    fstar-dune = fstar-flake.packages.${system}.fstar-dune;
    comparse = comparse-flake.packages.${system}.comparse;
    dolev-yao-star = pkgs.callPackage ./default.nix {inherit fstar fstar-dune z3 comparse; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;};
  in {
    packages.${system} = {
      default = dolev-yao-star;
      inherit dolev-yao-star;
    };
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        fstar z3
      ] ++ (with pkgs.ocaml-ng.ocamlPackages_4_14; [
        ocaml dune_3 findlib yojson
      ])
      ++ (fstar.buildInputs);
    };
    checks.${system} = {
      dolev-yao-star-build = dolev-yao-star;
      dolev-yao-star-tests = dolev-yao-star.tests;
    };
  };
}
