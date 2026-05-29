# Warning: only edit this file if you know what you're doing!
# In this case, consider using `agda.nix` directly.
{
  description = "Pagda nix template";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    flake-utils.url = "github:numtide/flake-utils";

    agda-nix = {
      url = "github:input-output-hk/agda.nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.standard-library-meta.url =
        "github:agda/agda-stdlib-meta/d10d2826db53855e5765b5a49a74e567a7ceb2ff";
    };

    pagda = {
      url = "./pagda.nix";
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
      inherit (nixpkgs) lib;
    in
      flake-utils.lib.eachDefaultSystem (
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [
              inputs.agda-nix.overlays.default
            ];
          };

          pagda = import inputs.pagda { agdaPackages = pkgs.agdaPackages; };
        in
          {
            packages = pagda // {
              agda = pkgs.agdaPackages.agda.withPackages
                (builtins.filter (p: p ? isAgdaDerivation) pagda.default.buildInputs);
            };
          }
      );
}
