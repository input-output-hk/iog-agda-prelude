{
  description = "IOG Prelude";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    flake-utils.url = "github:numtide/flake-utils";

    agda-nix = {
      url = "github:input-output-hk/agda.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    agda-stdlib = {
      url = "github:agda/agda-stdlib/v2.4";
      flake = false;
    };

    agda-stdlib-classes = {
      url = "github:agda/agda-stdlib-classes/v2.4";
      flake = false;
    };

    agda-stdlib-meta = {
      url = "github:agda/agda-stdlib-meta/v2.4";
      flake = false;
    };
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-utils,
      ...
    }:
    let
      overlay = nixpkgs.lib.composeManyExtensions [
        inputs.agda-nix.overlays.default
        (final: prev: {
          agdaPackages = prev.agdaPackages.overrideScope (
            afinal: aprev: {
              standard-library = aprev.standard-library.overrideAttrs (_: {
                src = inputs.agda-stdlib;
              });
              standard-library-classes = aprev.standard-library-classes.overrideAttrs (_: {
                src = inputs.agda-stdlib-classes;
              });
              standard-library-meta = aprev.standard-library-meta.overrideAttrs (_: {
                src = inputs.agda-stdlib-meta;
              });
              iog-prelude = aprev.iog-prelude.overrideAttrs (_: {
                src = ./.;
              });
            }
          );
        })
      ];
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            overlay
          ];
        };
      in
      {
        packages.default = pkgs.agdaPackages.iog-prelude;
        devShells.default = pkgs.agda.shellFor pkgs.agdaPackages.iog-prelude;
        hydraJobs =
          let
            jobs = { inherit (self) packages devShells; };
          in
          jobs
          // {
            required = pkgs.releaseTools.aggregate {
              name = "${system}-required";
              constituents = with nixpkgs.lib; collect isDerivation jobs;
            };
          };
      }
    )
    // {
      overlays.default = overlay;
    };
}
