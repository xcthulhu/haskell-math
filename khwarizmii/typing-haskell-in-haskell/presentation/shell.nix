{pkgs ? import <nixpkgs> { } }:

let
  haskellPackages = pkgs.haskellPackages;
in pkgs.stdenv.mkDerivation {
  name = "presentation";

  # The packages in the `buildInputs` list will be added to the PATH in our shell
  buildInputs = [
    haskellPackages.bimap
    haskellPackages.ghc
    haskellPackages.markdown-unlit
    haskellPackages.pandoc
    haskellPackages.pandoc-citeproc

    pkgs.librsvg
    pkgs.pdf2svg

    # Takes too long to link, just use system texlive
    #pkgs.texlive.combined.scheme-full
  ];
}
