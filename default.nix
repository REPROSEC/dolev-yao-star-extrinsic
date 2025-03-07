{lib, stdenv, which, fstar, z3, ocamlPackages, comparse, fetchFromGitHub}:

let
  dolev-yao-star = stdenv.mkDerivation {
    name = "dolev-yao-star";
    src =
      lib.sources.sourceByRegex ./. [
        "Makefile"
        "src(/.*)?"
        "examples(/[^/]*)?"
      ]
    ;
    enableParallelBuilding = true;
    buildInputs = [ which fstar z3 ];
    COMPARSE_HOME = comparse;
    installPhase = ''
      mkdir -p $out
      cp -r ml src cache hints $out
    '';
    passthru.tests = dolev-yao-star-tests;
  };

  dolev-yao-star-tests = stdenv.mkDerivation {
    name = "dolev-yao-star-tests";
    src =
      lib.sources.sourceByRegex ./. [
        "Makefile"
        "src(/.*)?"
        "examples(/.*)?"
      ]
    ;
    enableParallelBuilding = true;
    buildInputs =
      [ which fstar z3 ]
      ++ (with ocamlPackages; [
        ocaml dune_3 findlib
      ])
      ++ (fstar.buildInputs);
    COMPARSE_HOME = comparse;
    # pre-patch uses build output from dolev-yao-star, to avoid building things twice
    prePatch = ''
      cp -pr --no-preserve=mode ${dolev-yao-star}/cache ${dolev-yao-star}/ml .
      mkdir obj
      cp -p ml/lib/src/* obj/
    '';
    doCheck = true;
    installPhase = ''
      touch $out
    '';
  };

in
  dolev-yao-star
