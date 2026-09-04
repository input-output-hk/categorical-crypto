# Rewrite verdict: `protocol-rewrite` vs the old lineage

Comparison of `protocol-rewrite` (M1–M3, 63 files / +8095 LOC over `f71a2381`) against
the old lineage's tip (`sfunm-setoid` + `spike/pov-tower`, 59 files / +9592/−1888 over
the same base). Quality-pass addendum pending; nothing below depends on it.

## Verdict: ADOPT the rewrite as the mainline

The rewrite dominates on every axis the maintainer has pressed, and its gaps versus the
old lineage are enumerable ports, not regressions in kind.

| axis | protocol-rewrite | old lineage |
|---|---|---|
| statement honesty | POV over the state trajectory at a pinned genesis; randomized strategies native (`coin`); **no budget in any statement**; `SameTV` ancilla-parametric ⇒ **no K island**; ε-indexed `≈ₚ[ε]` replaces the (at Dₚ uninhabitable) ℚ-valued `adv`; `Reflects` in the sound quantifier order over randomized trees | budget-parametric statements needing calibration remarks; 2-module K island; deterministic `Dgr` (`Reflects` refuted once); ledger `valid` had two value-leak bugs making POV(inputConsuming) **false** |
| reach | machine category = `Traced` + **`GConstruction` verbatim, zero hypotheses** (`𝒢ₚ` closed); unbounded machines native — infinite traces with no towers, no `Stabilizes`, no `clip` | never reached `𝒢` (blocked at ro-model phase 1); infinite traces only via the tower workaround |
| example | `ChimericLedger.POV` = 190 lines, 3 layer imports, plain-Agda ledger, `Sys = ledger ∘ᵖ oracle`, pins by `refl` | same shape achieved only after three API redesign passes; rests on `System` certificate luggage |
| equalities | one hom-equality (simulation zigzag) from birth | four-relation zoo (`≈ᴹᶜ/≲/≲ᵒ/≈ˢ`) + ~780 LOC of word machinery with no counterpart in the rewrite |
| hatches / flags | 21 = baseline; zero postulates; `--without-K` everywhere incl. all of `UC.*`; `--guardedness` on 18 Dₚ-facing modules only | 21 = baseline; K island (2 modules) |
| perf | no module over ~12 s warm; machine closure ~40 s | 450 s MD remainder (slated for deletion); two conversion-wall incidents |

## What the old lineage still has (the port ledger, in harvest order)

1. **`van-bound`** — the vanishing-bound analysis: pure ℚ, ports verbatim. (~0 adaptation)
2. **The α query-bound content**: counting theorem + full `qb` calculus + closed-leg
   discharges — proved on the old branch, stated-and-priced on the new (`Counting`
   250–350, `qb-∘` 250–400, `BudgetLawsᴹ` ~180). The design re-types; the proofs adapt.
3. **The MD example**: its crypto core (`MerkleDamgard/Core`, machine-free) ports
   verbatim; the machine side becomes a `Protocol` with the free-monad `Call`
   (k calls per message) — replacing the old `_∘ᵍ_`/`stableN`/clock apparatus outright.
4. **The functor seam**: `Morphism-∘` (300–500; the ≲ direction has the state map, the
   reverse needs thought — flagged) and `PrAgree` (250–450; missing link = a general
   `Dist⊥ → Dₚ` embedding, `Dp.Coin` is the Bool case).
5. **`Monoidal (GConstruction C)`**: one compound-object σ-coherence (`⌜⌝-⊗`) gates the
   bifunctor field; embedding layer landed.
6. **The `Reflects` reifier** (~250, instance-specific) and `AgreeToAdv` (= reifier +
   `PrAgree`, no new content); `Grading 𝒫ᴵ` (record-eta cliff, medicine known);
   `UC-compose` (two `Grading` fields).

Total to parity-and-beyond: ≈1400–2300 LOC, all routine-to-medium, none research-grade.

## Honest liabilities of the rewrite

* `morphism` preserves composition but **not identities** (`wireᵖ` costs a query where
  `𝒢.id` forwards silently — the Katis–Sabadini–Walters delay at the functor seam). A
  genuine functor lands in a subcategory of `𝒢`; the UC seam must be built with that in
  mind. Recorded in `Protocol/Machine`'s header.
* `refl`-pins of *categorical* composites are measured out of reach at Dₚ (`cum n`
  explores 2ⁿ branches through junction delays); pins compute for protocol composites
  and direct machine images. The old clocked layer was better at this — it is the one
  thing it was better at, and the recorded reason it could return as an internal exact
  fragment if ever needed.
* The old branch's proved-but-unported content (item 2 above) means the rewrite is
  *currently* behind on inhabited query-bound theorems; adopt-then-port, not
  port-then-adopt, is still the right order because nothing in the port is blocked by
  the rewrite's design — while the reverse direction (fixing the old statements) was
  what this rewrite exists to avoid.

## Disposition of the old branches

`spike/pov-tower` (frozen at 75cbfb70): archive; reference for the System-API pattern
and the coherence-field refutations. `sfunm-setoid`: archive after items 1–3 are
harvested; its MD-relocation plan docs remain the map for item 3. `spike/pov-dp`,
`spike-dp`, `spike-elgot`: fully harvested, archive. The MD line inherited at
`f71a2381` stays green and untouched on this branch until item 3 replaces it; the M3
doc records the one-to-one supersession map for the deletion pass.
