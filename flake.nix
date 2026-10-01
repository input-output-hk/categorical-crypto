# Warning: only edit this file if you know what you're doing!
# To customize the build, prefer the optional pagda.nix escape hatch.
{
  description = "Pagda project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    agda-nix = {
      url = "github:input-output-hk/agda.nix";
      inputs.nixpkgs.follows = "nixpkgs";
      # The reflection frontend (Categories.Coherence.Monoidal.Tactic) needs
      # the generic solver frontend `Tactic.Solver.Core`, which is not on
      # agda-stdlib-meta's master yet.
      inputs.standard-library-meta.url = "github:agda/agda-stdlib-meta/algebraic-solvers";
    };

    pagda.url = "github:WhatisRT/pagda";
  };

  # The build logic lives in pagda (lib.mkFlake), so this file stays a thin
  # caller: bump the pagda input to pick up improvements.
  outputs = inputs: inputs.pagda.lib.mkFlake { inherit inputs; src = ./.; };
}
