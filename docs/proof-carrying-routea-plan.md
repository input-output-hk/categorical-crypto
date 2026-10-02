# Plan: proof-carrying Route A (make `rewriteDeep` gate #1 a theorem)

Status: PLAN (2026-06-14). Supersedes the 3-leg graph-roundtrip approach in
`findiso-witness-plan.md`, which the Route B audit (`/tmp/opt3-routeb/
ROUTEB-AUDIT.md`, archived findings in memory) found to be NO-GO: its leg 2
(`⟪decode-attempt H'⟫ ≅ᴴ H'`, full on-graph decoder completeness) is the
project's hardest open problem (~thousands of LOC, 3–6 months).

## Goal

Replace the FIRST `findIso` gate of the deep-rewrite engine — currently a
guided search + `Verify.verify` run costing ~34 s/gate (new machine) — with a
PROVEN iso, so the gate becomes a cheaply-forced proof term instead of a
typecheck-time computation.

```
deepFrame-≅ᴴ : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q) n found
             → ⟪ s ⟫ ≅ᴴ ⟪ deepFrame s lᵗ lᵗ n found ⟫
```

Per call this turns 2 gates into 1 (gate #2, against the user-stated clean
term `t`, stays a search — `t` is genuinely new information). Projected: a
`rewriteDeepTo!` call drops ~68 s → ~34 s, **~50% on the engine / showcases**.

## Why this sidesteps Route B's showstopper

Route B tried to relate `⟪frame⟫` to `⟪s⟫` by proving the carved graph `H'`
decodes back to itself (`⟪decode H'⟫ ≅ᴴ H'`) — the full completeness theorem.
Route A never asks "what graph does the frame decode to." It relates the two
term translations DIRECTLY via the carve provenance edge map that
`DeepProv.agda` already computes and that empirically passes `Verify`
(ROUTEA-NOTES, 2026-06-11). The proof obligation collapses from "every
well-formed acyclic graph round-trips" to a set of PER-EDGE structural facts
about the specific frame the carve built.

## What `⟪frame⟫` is, structurally (the backbone — FREE)

`deepFrame s lᵗ lᵗ n found = post ∘ ((id {k} ⊗₁ lᵗ) ∘ pre)` where
`(k, pre, post) = fromWitness! (deepFocₙ s lᵗ n) found`.

`⟪∘⟫`/`⟪⊗⟫` are DEFINITIONAL (Translation.agda:43/45; spiked `refl`), so

```
⟪frame⟫ edges  ≡  ⟪pre⟫'s edges  ++  ⟪lᵗ⟫'s edges  ++  ⟪post⟫'s edges
```

in data-flow order, with vertices the term's wiring. So the iso `⟪s⟫ ≅ᴴ ⟪frame⟫`
must exhibit, for every `⟪s⟫`-edge `e`, that its provenance image lands in one
of these three blocks with matching label and endpoints.

## The three edge blocks, and what each needs

| block | what covers it | status |
|---|---|---|
| `⟪lᵗ⟫` edges (the substituted redex) | the verified embedding `emb : ⟪lᵗ⟫ ↪ᴴ ⟪s⟫` — its `ψ-elab`/`ψ-ein`/`ψ-eout` already prove these edges' labels & endpoints match the corresponding `⟪s⟫` edges | **REUSE** (free) |
| `⟪pre⟫` / `⟪post⟫` edges (the complement = S minus ψ-image) | **the CRUX** — see below | NEW |
| (vertices) | `assemble` keeps `nV = S.nV`, `vlab = S.vlab` (Deep.agda:160-170); vertices are never renumbered by the carve, so `φ` is essentially identity composed with the term-translation's wiring map | NEW but structural |

## THE CRUX: per-edge decode preservation (de-risk this FIRST)

The complement edges reach `⟪frame⟫` via
`⟪ retract (focus-leg-of (decode-attempt H')) ⟫`. To prove their labels and
endpoints match the originating `⟪s⟫` edges we need, NOT the full
`⟪decode H'⟫ ≅ᴴ H'`, but the weaker per-edge invariant:

> **`decode-attempt H'` emits, for each processed `H'`-edge `i`, an `Agen`
> carrying `H'.elab i`, with the edge's wires placed so that `⟪_⟫` recovers
> `H'.ein i` / `H'.eout i` under the (identity-on-vertices) carve map.**

`decode-attempt` is `process-edges (range H'.nE)` emitting exactly one `Agen`
per edge in order (ROUTEA-NOTES confirmed). The LABEL half is a clean
structural induction on the edge list (`Agen g` translates to a one-edge graph
with label `g` — a translation fact). The **ENDPOINT (vertex) half is the
genuinely fiddly part**: decode threads vertices through the term's wiring, and
`⟪_⟫` re-derives vertex identities from that wiring; proving they match `H'`'s
endpoints through `focus → retract → recompose` is vertex bookkeeping across
the round-trip. This is where LOC can balloon and where the estimate is least
certain.

### De-risking spike (do BEFORE committing the full effort) — ~1 week
State and prove ONLY the per-edge LABEL preservation for `decode-attempt` (skip
endpoints), for the Frobenius bench `H'`. If even the label half drags in
unexpected machinery, the full crux is a months problem and we should stop. If
it falls out of structural induction, prove a single complement edge's ENDPOINT
preservation next — that one edge is the true bellwether for the whole effort.

## Reused / known-absent machinery (from the audit)

- `_≅ᴴ_` (Iso.agda): plain bijection record, full refl/sym/trans — **clean, no
  σ-naturality wall**. Assembly of the final iso ≈ 50 LOC once the legs exist.
- `emb : _↪ᴴ_` (SubMatch.agda): fully verified — covers the `⟪lᵗ⟫` block.
- `DeepProv.agda`: already computes the φ/ψ provenance (label-free `BuildO`,
  `pairsO`), `--safe`, postulate-free, empirically passes `Verify`. This IS the
  witness data; the work is proving it correct.
- definitional `⟪∘⟫`/`⟪⊗⟫`: the frame expansion is free.
- **ABSENT (must be written):** `focusAtₙ` soundness (Carve.agda header says
  unverified), `retract` soundness (ExtendSig.agda header says unverified), and
  the pad layer `repadR`/`repadL` (Deep.agda:283-305) soundness — an unbudgeted
  surface of σ/α coherence wrappers (the kind `solveMor!` can shrink).

## Milestones

0. **Crux spike** (~1 wk): per-edge decode-attempt label preservation + one
   complement-edge endpoint preservation, on the Frobenius `H'`. GO/NO-GO gate.
1. **Complement edge preservation** (general): label + endpoint, by induction on
   the edge list. ~400–700 LOC. (the crux, scaled up)
2. **focus / retract soundness**: `ctx ≈ post⁺ ∘ (id ⊗ Agen hole) ∘ pre⁺` and
   `⟪retract p⟫ = ⟪p⟫` on h-free terms. ~550–850 LOC. Independent of 1.
3. **Pad-layer soundness** (`repadR`/`repadL`): ~200–400 LOC; shrink the
   coherence chases with `solveMor!`.
4. **Carve combinatorics** (leg 1): kahn-output-is-a-permutation +
   complement ∪ ψ-image = all S edges. ~700–1100 LOC. Reuse DeepProv data;
   LinearExtension.agda is precedent for the permutation induction.
5. **Assemble** `deepFrame-≅ᴴ` from 1–4 via trans/sym-≅ᴴ (~50 LOC), thread the
   existing `found` witness (do not re-decide).
6. **Wire-up**: replace gate #1 in `rewriteDeepₙ!`/`rewriteDeep!`/
   `rewriteDeepTo!` with the theorem; drop the `{cert}` implicit; keep gate #2.
   Re-run the Test suite + FrobProbe.

## Effort & risk

- Total (milestones 1–6): **~1,900–3,100 LOC, ~5–8 weeks**, IF the crux spike
  (milestone 0) confirms per-edge decode preservation is tractable.
- Highest risk: the vertex-bookkeeping half of the crux. The label half is
  low-risk; endpoints through focus/retract/recompose are the uncertain piece.
- This is strictly better than Route B (which adds the months-scale leg 2 on
  top of all of the above).

## Recommendation

Run milestone 0 (the ~1-week crux spike) before committing. It converts the
single biggest uncertainty (per-edge decode preservation incl. vertex
bookkeeping) into a measured GO/NO-GO, at ~15% of the total cost. If GO, the
~50%-per-call engine win is reachable in ~5–8 weeks. If NO-GO, we stop at
Option 2 (flat-match, landed, ~7%/call) and accept the engine cost — or revisit
once the broader decoder-completeness effort lands and makes leg 2 cheap.

## Benchmark

Frobenius `step₃` and the `FrobProbe.agda` staged probes; gate cost is
`probe-vfull`-style. Hold to: gate #1 → near-0, `rewriteDeepTo!` call ~68 s →
~34 s (new machine).
