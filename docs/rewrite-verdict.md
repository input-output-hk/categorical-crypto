# Rewrite verdict: `protocol-rewrite` vs the old lineage

Comparison of `protocol-rewrite` (M1–M3, 67 files / +8732 LOC over `f71a2381`) against
the old lineage's tip (`sfunm-setoid` + `spike/pov-tower`, 59 files / +9592/−1888 over
the same base). Quality-pass addendum pending; nothing below depends on it.

## Verdict: ADOPT the rewrite as the mainline

The rewrite dominates on every axis the maintainer has pressed, and its gaps versus the
old lineage are enumerable ports, not regressions in kind.

| axis | protocol-rewrite | old lineage |
|---|---|---|
| statement honesty | POV over the state trajectory at a pinned genesis; randomized strategies native (`coin`); **no budget in any statement**; `SameTV` ancilla-parametric ⇒ **no K island**; ε-indexed `≈ₚ[ε]` replaces the (at Dₚ uninhabitable) ℚ-valued `adv`; the bridge quantifies over the budgeted strategies instead of witnessing a dominating one, a context's budget is guarded against zero, and the seam is built along the embedding with a simulator-aware carry at both grades (addenda) | budget-parametric statements needing calibration remarks; 2-module K island; deterministic `Dgr` (`Reflects` refuted once); ledger `valid` had two value-leak bugs making POV(inputConsuming) **false** |
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
6. **The seam's remaining steps**: `StratIsEnv` (~80–120) and `Adequacy` (~250–350),
   after which `AgreeToAdv` and `pov-carry` are theorems (addendum 1); the trivial
   grade's `SubBlind`/`IotaBlind` (~60–90 each) and `AuditIsBounded` (~120–180), after
   which both simulator carries reach layer 1 (addendum 2); `ContextDominated`
   (~250, instance-specific); `Grading 𝒫ᴵ` (record-eta cliff, medicine known);
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

## Addendum: external theory review, findings and resolutions

Reviewed at `ebb3f2a5` (`docs/protocol-rewrite-theory-review.md`); all four findings are
resolved on this branch.

1. **Vacuous birthday target.** `AtBirthday`'s account-only genesis dead-locked the
   input-consuming ledger, so the bound held with probability zero. Genesis is now all the
   value in ONE UTxO output keyed by a genesis hash `h₀` (an `AtBirthday` parameter beside
   `ser-inj`), the bound is `ε q = (q² + q)·2⁻ˡ` — the `+ q` for fresh hashes colliding
   with `h₀` — and `ChimericLedger.Pin` pins acceptance-with-probability-1 and the state
   change by `refl`, so the vacuity cannot return unnoticed.
2. **`Reflects` quantifier order.** A finite `Strat` mentions finitely many first queries
   and so cannot reflect a `Dₚ` context that samples an unbounded-support question at
   query bound one. `UC.Bridge.Reflects` now quantifies over the compared pair *before*
   witnessing the strategy; the uniform form is priced as a `Dₚ`-valued or coinductive
   strategy language, not built.
3. **Seam direction.** `AgreeToAdv` cannot follow from `Reflects` (wrong direction).
   `UC.Seam` is rebuilt along the embedding instead: `strategyEnv` (a finite strategy as
   an environment) is constructive, `StratIsEnv` (`UC.Seam.Grounding`) and `Adequacy` are
   the two stated-and-priced steps, and `AgreeToAdv` — hence `pov-carry` — is now a
   THEOREM of those plus `PrAgree` (`UC.Seam.Carry`). Carrying a bound across `_≤UC_`
   needs the interface-observable audit form, the simulator being quantified at a graded
   codomain; recorded in the module header.
4. **κ cofinality.** `UC.Family` now takes `κ-cofinal : ∀ N → Σ[ i ] N ≤ κ i`, without
   which a bounded `κ` makes every eventual statement — hence the UC preorder — vacuous.
   `≈^ω-witness` is what it buys.

## Addendum 2: second external theory review, findings and resolutions

Reviewed at `f096c5d5`; round 1's four resolutions are confirmed there, and all three
new findings are resolved on this branch.

1. **Context budgets collapsing to zero.** `c * c′` charges a genuinely querying
   context nothing when the closure certifies at `QB 0` (an ancilla with no downward
   port). `UC.Base.ctxBudget c c′ = c * (c′ ⊔ 1)` replaces it in `UC.Bridge`, in
   `UC.Family`'s `_≈ℰ[_]_` (as `ctxQB`, still polynomial) and in `UC.Audit`; the
   port-specific bound on crossings of the distinguished hole is priced, not built.
2. **A simulator-aware carry.** `UC.Emulation.unit-grade` proves the unit-grade
   specialization (an emulation at a blind grade IS `pov-carry`'s direct premise) and
   `UC.Audit.audit-carry` proves the graded one (an interface-observable audit bound
   crosses `_≤UC_` at the emulation's slack, the simulator absorbed into the test and
   its queries charged there). Both are proved over an arbitrary base because at the
   machine instance an `≈ℰ` between composites cannot be a term's type; the instance
   modules name the residue (`SubBlind`/`IotaBlind`, `AuditIsBounded`).
3. **The existential reflection.** Gone: `UC.Bridge.ContextDominated` quantifies over
   the strategies the context's budget affords and concludes at `ε + δ` for an
   arbitrary positive δ, which is what a convexity argument over a supremum-valued
   mass delivers and what layer 1's budget-quantified theorems feed directly.
