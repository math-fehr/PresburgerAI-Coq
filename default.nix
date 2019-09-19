{ }:

let
  pkgs = import <nixpkgs> { };
in
  pkgs.stdenv.mkDerivation {
    name = "simplexhc-1.0.0";
    src = ./.;
    buildInputs = [ pkgs.coq_8_9 pkgs.emacs26  ];
  }
