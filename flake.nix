{
  description = "IOG Prelude";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    flake-utils.url = "github:numtide/flake-utils";

    shellFor = {
      url = "github:input-output-hk/agda.nix?dir=tools/shellFor";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    standard-library-classes = {
      url = "github:input-output-hk/agda.nix?dir=libraries/standard-library-classes";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    standard-library-meta = {
      url = "github:input-output-hk/agda.nix?dir=libraries/standard-library-meta";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.standard-library-classes.follows = "standard-library-classes";
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
      overlay = final: prev: {
        agdaPackages = prev.agdaPackages.overrideScope (
          afinal: aprev: {
            iog-prelude = afinal.callPackage ./nix/iog-prelude.nix { };
          }
        );
      };
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            inputs.shellFor.overlays.default
            inputs.standard-library-classes.overlays.default
            inputs.standard-library-meta.overlays.default
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
