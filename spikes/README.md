# spikes/ — preserved investigation artifacts (off the main build)

These standalone `--safe` modules are a ledger of the gate-performance /
completeness investigation. They are intentionally **outside `src/`**, so the
main `categorical-crypto` library (`include: src`) does not compile them.

- `GlobalPhiDirect.agda` — machine-checked NO-GO: the frame-iso `⟪s⟫ ≅ᴴ ⟪frame⟫`
  reduces to the faithfulness kernel (why proof-carrying Route-A was abandoned).
- `Leg3Recomp.agda` — `focusAtₙ-sound` / `retract-sound` (the salvageable subterm
  recomposition-soundness lemmas, if the subterm gate is ever made proof-carrying).
- `Leg1Carve.agda` — partial carve-iso machinery for the abandoned frame-iso route.
- `CruxSpike.agda`, `FrobProbe.agda` — per-edge decode + Frobenius probes.

`Leg1Carve.agda` and `Leg3Recomp.agda` are the ones whose in-repo module
references all still resolve at the current tree. To typecheck one of these
again, build it against a library that `include`s both this directory and
`../src` (e.g. a registered `categorical-crypto-spikes` lib).
