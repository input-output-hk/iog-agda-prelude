{
  description = "IOG Prelude";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/cb9a96f23c491c081b38eab96d22fa958043c9fa";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system; };
          lib = pkgs.stdEnv.lib;
          localEmacs = (pkgs.emacs.pkgs.withPackages (epkgs: (with epkgs.melpaStablePackages; [
            epkgs.agda2-mode
          ])));
          agda-stdlib = pkgs.agdaPackages.standard-library.overrideAttrs (oldAtts: rec {
            version = "2.0";
            src = pkgs.fetchFromGitHub {
              repo = "agda-stdlib";
              owner = "agda";
              rev = "v${version}";
              sha256 = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
            };
            preConfigure = ''
              runhaskell GenerateEverything.hs
              rm EverythingSafe.agda
            '';
          });
          agda-stdlib-classes = pkgs.agdaPackages.mkDerivation {
            pname = "agda-stdlib-classes";
            version = "2.0";
            src = pkgs.fetchFromGitHub {
              repo = "agda-stdlib-classes";
              owner = "omelkonian";
              rev = "0c61d92540f0913f24951c88d3d3d4dc15347853";
              sha256 = "sha256-kTqS9p+jjv34d4JIWV9eWAI8cw9frX/K9DHuwv56AHo=";
            };
            meta = { };
            libraryFile = "agda-stdlib-classes.agda-lib";
            everythingFile = "standard-library-classes.agda";
            buildInputs = [ agda-stdlib ];
          };
          localAgda = pkgs.agda.withPackages (ps: [
            agda-stdlib agda-stdlib-classes
          ]);
          iog-prelude = pkgs.agdaPackages.mkDerivation {
            pname = "iog-prelude";
            version = "0.1";
            meta = { };
            src = pkgs.fetchFromGitHub {
              repo = "iog-agda-prelude";
              owner = "functionally";
              rev = "2b780014456447bfe2a936be04a0e06f3f1ebba8";
              sha256 = "sha256-z3Or2gPin7fZzVkIhEkRVu8+KFxjNfKh6Ik5sM7qqks=";
            };
            preConfigure = ''
              echo "module Everything where" > Everything.agda
              find src -type f | sed -e '/Dec\.agda$/d;s@^src/\(.*\)\.agda$@open import \1@;s@/@.@g' >> Everything.agda
            '';
            buildInputs = [ agda-stdlib ];
          };
        in
        {
          packages.default = iog-prelude;
          defaultPackage = iog-prelude;
          devShell = pkgs.mkShell {
            buildInputs = [
              pkgs.nixpkgs-fmt
              localAgda
              localEmacs
              pkgs.mononoki
            ];
          };
        }
      );

  nixConfig = {
    bash-prompt = "\\n\\[\\033[1;32m\\][iog-prelude:\\w]\\$\\[\\033[0m\\] ";
  };
}
