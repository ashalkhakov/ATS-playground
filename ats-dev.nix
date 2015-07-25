# A nix file (nixos.org) to load the necessary software for doing work with
# ATS2 and ATS Contrib from their source repositories.
# NOTE: based on file of the same name by Brandon Barker

#
# To use:
# nix-shell ats-dev.nix -A ATSDevEnv
#
# Or see https://nixos.org/wiki/Howto_develop_software_on_nixos
# for explanation and alternative usage.

#
# Some of the buildInputs are strictly speaking, optional
# Feel free to tailor to your needs
#

let
  pkgs = import <nixpkgs> {};
  stdenv = pkgs.stdenv;

  packages_ats1 = pkgs.callPackage /home/artyom/proj/nix/nixpkgs/pkgs/development/compilers/ats/default.nix { };

  patshome = "$HOME/proj/ATS-Postiats";
  patshomereloc = "$HOME/proj/ATS-Postiats-contrib";
in rec {
  ATSDevEnv = stdenv.mkDerivation rec {
    name = "atsdev-env";
    buildInputs = with pkgs; [ packages_ats1 gmp ];
    shellHook = ''
      export ATSHOME=${packages_ats1}/lib/ats-anairiats-0.2.12
      export ATSHOMERELOC=ATS-0.2.12
      export PATSHOME=${patshome}
      export PATSHOMERELOC=${patshomereloc}
    '';  
  };
}

