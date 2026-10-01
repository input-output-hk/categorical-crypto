# Plan: proving the `deepFrame` iso (Route B for the rewriteDeep `findIso` gates)

Status: PLAN ONLY (2026-06-11). Route A (computational witness + `Verify`)
is being spiked separately; this records the full-theorem route for when /
if we want the gate to vanish entirely.

## Problem and payoff

Every `rewriteDeepₙ!` / `rewriteDeepTo!` call (`Solver/Interpret.agda`)
carries the typecheck-time gate

```
findIso ⟪ s ⟫ ⟪ deepFrame s lᵗ lᵗ n found ⟫
```

which re-discovers, by backtracking search (~48 s) plus `Verify` (~20 s) on
the Frobenius benchmark, an isomorphism that the carve pipeline itself
constructed the frame from. Route B replaces the gate with a proven

```
deepFrame-≅ᴴ :
  ∀ {A B P Q} (s : HomTerm A B) (lᵗ mid : HomTerm P Q) n found
  → ⟪ s ⟫ ≅ᴴ ⟪ deepFrame s lᵗ lᵗ n found ⟫
```

(note: `mid = lᵗ` only — for `mid = rᵗ` no such iso exists or is wanted; the
second gate in `rewriteDeepTo!`, against the user-stated `t`, is genuinely
new information and stays a search). Payoff: gate #1 costs 0; per-call cost
of `rewriteDeepTo!` drops ~170 s → ~75 s, and `rewriteDeep!`/`rewriteDeepₙ!`
become essentially free (only `deepFocₙ`, ~0.4 s).

## The pipeline being verified (all in `Solver/Deep.agda` unless noted)

```
emb : ⟪ lᵗ ⟫ ↪ᴴ ⟪ s ⟫            -- subMatchAll, ALREADY verified (SubMatch.verifySub)
H'  = Build.holeGraph ⟪lᵗ⟫ ⟪s⟫ emb -- keep / kahn / assemble, over sig⁺ = sig + hole h
ctx = D⁺.decode-attempt H'         -- graph → term over sig⁺, ctx mentions h once
foc = C⁺.focusAtₙ ctx (Agen⁺ hole!) 0 → (k , pre⁺ , post⁺)
pre/post = retract pre⁺ / post⁺    -- sig⁺ → sig (h does not occur)
glue: two decide-≡ substs aligning unflatten⁺ boundaries
frame = post ∘ (id {k} ⊗₁ mid) ∘ pre   -- deepFrame, Interpret.agda:75
```

## Theorem decomposition

The iso factors through the carved graph; prove the three legs and compose
with `trans-≅ᴴ` / `sym-≅ᴴ` (`Hypergraph/Iso.agda`):

1. **(Replacement leg)** `H'[h ↦ ⟪lᵗ⟫] ≅ᴴ ⟪ s ⟫`
   where `H'[h ↦ G]` is hole substitution (to be defined, or phrased as:
   the graph `assemble (keep es) + ⟪lᵗ⟫'s edges` with the embedding's vertex
   identifications). Inputs: the verified embedding `emb` (vertex/edge
   partial bijections with their laws, from `SubMatch.verifySub`) and the
   carve bookkeeping (`keep` = S-edges minus matched edges; `kahn` is a
   permutation of those plus the hole). NEW work: a permutation lemma for
   `kahn`/`assemble` (the assembled edge list is a permutation of its
   input — provable by tracking `findReady`'s removal), plus the statement
   that carving then substituting back is the identity up to that
   permutation and the embedding.

2. **(Decode leg, at `sig⁺`)** `⟪ decode-attempt H' ⟫⁺ ≅ᴴ H'` when
   `decode-attempt` succeeds. This is a decode-roundtrip statement; the
   soundness tree has the proven machinery for exactly this shape
   (`Soundness/DecodeRoundtripSafe.agda` and the decode-agreement chain) —
   the work is INSTANTIATING it at the extended signature `sig⁺` and for
   `decode-attempt` specifically (check what `D⁺` imports; if the roundtrip
   is stated for the pruned decoder, bridge via the decoder-agreement
   lemmas). Risk: the existing roundtrip may be stated against `_≅ᴴ_` up to
   specific interface conventions — audit first. This leg is where most
   reusable mass lives; budget the audit before estimating.

3. **(Recomposition leg)** `⟪ frame ⟫ ≅ᴴ ⟪ ctx ⟫⁺[h ↦ ⟪mid⟫]`
   i.e. translating `post ∘ (id ⊗ mid) ∘ pre` equals substituting `⟪mid⟫`
   for the unique `h`-occurrence in `⟪ctx⟫⁺`. Sub-pieces:
   - `focusAtₙ` correctness: `ctx ≈ post⁺ ∘ (id ⊗ Agen⁺ hole!) ∘ pre⁺` at
     the TERM level — `Solver/Carve.agda` may already have the focus/frame
     soundness (it is what `focFrame`-based `rewriteAutoₙ!` relies on);
     audit `Carve.agda` for it.
   - `retract` soundness: `⟪ retract pre⁺ ⟫⁺ = ⟪ pre⁺ ⟫⁺` modulo the
     signature inclusion (h-free terms translate identically) — small.
   - The two `decide-≡` substs are propositional equalities of OBJECTS;
     they transport along `≡`, free.
   - Hole substitution commutes with `⟪_⟫` on a single-occurrence context:
     this is a compositionality lemma for the translation
     (`Hypergraph/Translation.agda` has the `hComposeP` structure; the
     statement is `⟪ post ∘ (id ⊗ m) ∘ pre ⟫ ≅ᴴ subst-hole ⟪ctx⟫ ⟪m⟫`).
     Probably the second-largest new piece after leg 1.

Finally `deepFrame-≅ᴴ = trans-≅ᴴ (sym-≅ᴴ leg1) (trans-≅ᴴ (sym-≅ᴴ leg2') leg3')`
with leg2'/leg3' specialised to `mid = lᵗ` (substituting the SAME subgraph
that was carved out).

## Order of work / milestones

1. **Audit pass (cheap, do first):** confirm what already exists —
   `DecodeRoundtripSafe` statement shape; `Carve.agda` focus-soundness;
   `SubMatch.verifySub`'s `_↪ᴴ_` record contents; `Iso.agda` combinators.
   Output: revised effort estimate per leg. (~1 session)
2. **Leg 3** (recomposition): self-contained term/translation work,
   independently useful (it would also serve `rewriteAutoₙ!`). (~1-2 wk by
   repo precedent for translation-compositionality proofs)
3. **Leg 2** (decode roundtrip at `sig⁺`): mostly instantiation + bridging;
   unknown until the audit. (days to weeks)
4. **Leg 1** (carve replacement): the genuinely new combinatorial proof
   (kahn permutation + embedding identification). (~1-2 wk)
5. **Wire-up:** replace gate #1 in `rewriteDeepₙ!`/`rewriteDeepTo!`/
   `rewriteDeep!` with the theorem; delete the `{cert}` implicits; keep
   gate #2 (t-side) as-is. Re-run the Test suite + FrobProbe. (~1 session)

## Risks

- `kahn`'s output order depends on `findReady`'s search; the permutation
  proof must not fix a specific order, only permutation-ness. Keep the
  statement order-agnostic.
- `decode-attempt` may fail (`Maybe`); all legs are conditional on the same
  success path that `deepFocₙ`'s `found : T (is-just …)` already witnesses —
  thread the witness, don't re-decide.
- `sig⁺` retraction: `Solver/ExtendSig.agda` — check it has (or add) the
  h-free-term retraction lemma.
- If Route A's spike lands first, its provenance plumbing (edge origins in
  `Build.Edge`, decode emission order) is exactly the data leg 1 and leg 2
  quantify over — design Route A's data so it can be reused as the
  skeleton of the Route B proofs.

## Benchmarks to hold ourselves to

Frobenius `step₃` (`Test/Frobenius.agda`): 170 s now; Route A target ~95 s;
Route B target ~75 s. Probe harness: `src/FrobProbe.agda` (uncommitted
artifact; recreate from Test/Frobenius lines 1-105 + litmus probes if gone).
