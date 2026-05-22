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

          tex = pkgs.texlive.combine {
            inherit (pkgs.texlive)
              scheme-medium tikz-cd stmaryrd mathtools;
          };

          machine-category-pdf = pkgs.stdenvNoCC.mkDerivation {
            name = "machine-category.pdf";
            src = ./doc;
            nativeBuildInputs = [ tex ];
            buildPhase = ''
              export HOME=$TMPDIR
              lualatex -interaction=nonstopmode -halt-on-error machine-category.tex
              # second pass for refs / pagebreaks
              lualatex -interaction=nonstopmode -halt-on-error machine-category.tex
            '';
            installPhase = ''
              mkdir -p $out
              cp machine-category.pdf $out/
            '';
          };
        in
          {
            packages = pagda // {
              agda = pkgs.agdaPackages.agda.withPackages
                (builtins.filter (p: p ? isAgdaDerivation) pagda.default.buildInputs);
              doc = machine-category-pdf;
            };

            devShells.tex = pkgs.mkShell {
              packages = [ tex ];
            };
          }
      );
}
