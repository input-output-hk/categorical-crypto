# Spike: one accounting theory (option §2.3)

Branch `memo23-spike` on `6cd42b1e`: two new unwired modules, no existing file changed,
`--safe --without-K`, escape-hatch baseline unchanged at 16, warning gate empty.

| module | lines | warm check | heap |
|---|---|---|---|
| `UC.Quantitative.Spike.Constant` | 158 | 19 s | `-M3G -H1G` |
| `UC.Quantitative.Spike.ConstantEvent` | 18 | 13 s (interface current; 4 m 33 s cold with deps) | `-M8G -H2G` |

## 1. Verdict: NO-GO for §2.3 as a deletion work package

§2.3 says single-level statements should be the family theory at constant families, so
that their second proof can go. The spike finds no second proof to delete.

- **The family theory is already the levelwise single-level one.** `_≈ctxᴬ[_]_` is
  *defined* as `UC.Quantitative.Contextual._≈ᵁᵠ[_]_` at every level. Every family
  composition law is a wrapper around a single-level lemma: `≈ctx-sub` wraps `ctx-sub`,
  `≤UC[]-trans` wraps `at-trans`, `≈ctx-ext` wraps `ctx-absorb`, and `≈ctx-pre`/`-dom`
  wrap `absorb-closureᵠ`/`≈ᵃ-post`. `Boundedᶠ` is defined as `BoundedAt` at every
  level, and `Hitsᶠ` as `HitsAt`. Deriving the single-level lemmas back from the family
  ones through `Δ` works (§3), but it is **circular**: the family proof calls the lemma
  it would replace.
- **`UC.Audit` is not the family theory at `Δ`.** It is a different theory at one level.
  Its comparison is the *exact* readout equivalence `_≈ᵁ_` over *all* contexts. The
  family comparison is ε-closeness over *certified* contexts. `Δ` maps the first into
  the second in one direction only; it reflects back under `Exact` and `Total` (§2), and
  `Total` fails at the model. `AuditBound`, `absorb`, `audit-carry` have **no family twin**.

## 2. The embedding and what it reflects (`Spike.Constant`)

Parameters: `Quantitative.Family`'s plus Audit's `mass`; Audit is instantiated at
`Family.readout`, so both theories share one `_≈ᵁ_`.

```agda
Δ  : Channel → ℕ → Channel                          -- Δ X _ = X
Δʰ : A ⇒ X ⊗₀ B → Homᶠ (Δ A) (Δ X) (Δ B)
Δᶜ : L.Hom r Y X → Certified (Δ Y) (Δ X)            -- (λ _ → r) , poly-const (value r) , λ _ → ŝ
```

These are the results, all typechecked:

| theorem | statement | lines |
|---|---|---|
| `Δ-≈ᵁᵠ` | `f ≈ᵁᵠ[ ε ] g ⇔ Δʰ f ≈ctx[ (λ _ → ε) ] Δʰ g` | 1 |
| `Δ-≤UC` | `f Au.≤UC[ r ] g → (ν>0) → Δʰ f ≤UC[ Δᶜ ŝ , (λ _ _ → ν) ] Δʰ g` | 1 |
| `const-not-negligible` | `0 < ν → ¬ NegligibleBound (λ _ _ → ν)` | 6 |
| `Δ-≤UC^ωᵉ` | `Exact → f Au.≤UC[ r ] g → Δʰ f ≤UC^ωᵉ Δʰ g` | 2 |
| `Δ-≈ᵁ⁻` | `Total → Δʰ f ≈ctx[ 0 ] Δʰ g → f ≈ᵁ g` | 1 |
| `Δ-≤UC⇔` | `Exact → Total → f Au.≤UC[ r ] g ⇔ Σ ŝ. Δʰ f ≤UC[ Δᶜ ŝ , 0 ] Δʰ g` | 2 |

The two conditions are defined as follows:

- `Exact = x ∼ y → x ≈[ 0 ] y`. This says the readout is `Approx.Evaluation.qual`. The
  model's readout is `qual₊`, where `∼` is agreement at every *positive* error.
  `Quantitative.Family.≈C⇒≈ctx` records that `_≈ᵁ_` has no zero instance to hand over.
  I have not checked whether the model's `≈[_]` is closed enough to give one (UNVERIFIED).
- `Total = (u : A ⇒ B) → Σ c. Image forget c u`. This says every morphism is
  rate-certified. It is §1's totality. It is false at the machine model, because a
  machine need not be query-bounded.

So exact emulation reaches the family theory only at positive constant schedules, which
never give an `_≤UC^ωᵉ_` (`const-not-negligible`: 0 is the only negligible constant, and
reaching 0 needs `Exact`). Coming back also needs `Total`: the family relation never asks
about an uncertified context, but `_≈ᵁ_` asks about every context.

This is where a constant family stops being a special case:

- **`Poly⁺` rates against one `ℕ⁺`:** free. A constant schedule is `poly-const` (`Δᶜ`),
  and back, a family certificate projects to its level-`n` one `hom s n`, for any family.
- **Existential error:** `_≤UC^ωᵉ_` hides a negligible `ε`, and `ε 0 q` is not 0. So
  even under `Exact` and `Total`, a family `≤UC^ωᵉ` between constant families does not
  give an exact Audit `≤UC[ r ]`. Only the fixed-data form `≤UC[ Δᶜ ŝ , 0 ]` reflects.
  The simulator family would also have to be constant, and `_≤UC^ωᵉ⁺_` does not
  promise that.
- **The `Δ Gr.𝟘ᴳ ⊛ω` grading** (`Model.Family.Emulation.gradedᶠ`): the family images
  already sit at a constant grade via `Families.Δ`; free, and not new.
- **`AuditBound` ⇔ `BoundedAt`/`Boundedᶠ`:** `Spike.ConstantEvent.Δ-bounded` proves
  `Boundedᶠ (Δ f) (Δ 𝔠) (λ _ → ε) ⇔ ∀ q → BoundedAt q (ε q) f 𝔠` in one line, because
  it is definitional. `AuditBound` is a bound at an *arbitrary* base over a `Permitted`
  class of certified contexts. It uses the uncapped exact budget `c · r′`. `BoundedAt`
  is machine-only and uses a `Reader`, a cap `≤ q` and `QB` certificates. The
  `EventBounds` header says the two are not identified, and the spike does not identify
  them. Doing so would be a new bridge at the model, `Seam.Audit.Context`-shaped. It
  would not be a Δ lemma. Sketch: at `R = evaluationᵒ` and
  `𝔈 k = "k's test is 𝔠 Y E"`, `AuditBound f 𝔈 ε` should imply
  `∀ q. BoundedAt q (ε q) f 𝔠` by monotonicity of `ε` over the cap. This is not built.

## 3. Two single-level theorems through `Δ`

| derived | from | derived proof | existing proof | verbatim? |
|---|---|---|---|---|
| `ctx-subᐞ` = `Contextual.ctx-sub` | `Family.≈ctx-sub` | 4 lines | 7 lines (via `ctx-absorb`) | yes |
| `at-transᐞ` ≈ `Contextual.at-trans` | `Family.Compose.≤UC[]-trans` | 6 lines | 7 lines (via `ctx-sub`) | **no** |

- `ctx-subᐞ` is `Δ-≈ᵁᵠ` both ways plus one `ctx-resp` (`⌊ ŝ ⌋` to `s`). Shorter, but not
  a deletion: `≈ctx-sub` *is* `ctx-sub` at every level.
- `at-transᐞ` needs one extra hypothesis, `Image forget r′ t`. The family witness
  `Certified` certifies both simulators. `at-trans` never uses a certificate for the
  second one, and neither does `≤UC[]-trans` (it only builds `s ∘ᶜ t`). The family
  packaging asks for more than the proof uses, so the single-level statement *cannot*
  be recovered verbatim.

The candidates `≤UC[]⇒≤UC` (vs `≤UC^ωᵉ⇒⁺`) and `audit-carry` (vs `≈ctx-sub`) fail for
§2's reasons: exact `≤UC` is reached only under `Exact`/`Total` with a constant simulator,
and `audit-carry` has no family statement to start from.

## 4. The work package

**(a) What §2.3 would delete:**

- `Quantitative/Contextual.agda` :: `ctx-sub`, `at-trans`, `ctx-absorb`,
  `absorb-closureᵠ` (≈40 LOC). These cannot go, because the family proofs are built
  from them. Moving them into `Family` would be a move, not a deletion.
- `Machine/EventBounds.agda` :: `BoundedAt`, `Quantitative/EventLift.agda` :: `HitsAt`
  etc.: 0 LOC (single-level primaries; the family forms are one-line definitions).
  `Audit.agda` (134 LOC): 0 LOC is derivable (§2).
- The only genuine duplication found is between two *single-level* pieces, and it is
  not a Δ question:
  - `Audit.agda` :: `_∙ˢ_` and `budget-∙ˢ` (≈13 LOC) re-derive the allowance algebra
    that `Quantitative.Query.absorb-test`/`scale-comm` already have.
  - `Quantitative/Family.agda` :: `≈ctx-resp`, `≈C⇒≈ctx`, `≈ctx-refl`, `-sym`,
    `-trans`, `-≤` (≈20 LOC) restate `Contextual.ctx-*` directly at the `prefixᵒ`
    bracket, instead of going through `≈ctxᴬ`. Routing them through `≈ctxᴬ` costs about
    one conversion line each.

**(b) What would be added:** `Δ`, `Δʰ`, `Δᶜ` and `Δ-≈ᵁᵠ`, ≈10 LOC. The Audit bridge
(`Δ-≤UC`, `Δ-≤UC^ωᵉ`, `Δ-≈ᵁ⁻`, `Exact`, `Total`) is another ≈20 LOC, and it only pays
off where `Exact`/`Total` hold.

**(c) Net LOC:** positive for §2.3 as stated, since nothing is deleted and (b) is added.
The optional single-level cleanup in (a) is about −10 to −20 LOC and is independent of Δ.

**(d) Which direction is cleaner:** family as levelwise single-level. That is the
opposite direction to this spike, and the repo already takes it:

the quantitative layer definitionally (`≈ctxᴬ`, `Boundedᶠ`/`Hitsᶠ`), and the qualitative
layer through `UC/Family.ucSetup^ω`, which builds the vanishing-advantage family as *one*
`UCSetup` over the levelwise `Famᴹ` (`Categories.LocallyGraded.Family`, whose `Δ` is
`Families.Δ`), so Abstract2's whole theory is inherited for families.

`ucSetup^ω` does make this spike's Δ-direction redundant for the qualitative tier. It
says nothing ε-level, and the spike does not replace `§2.1`/`certified-homs-spike.md`
for that. The residue of §2.3 is really "Audit vs Contextual at one level": exact `≈ᵁ`
over all contexts against `≈ᵁᵠ[0]` over certified ones. That is `Exact` + `Total`,
which is §1's totality question and not an accounting-theory question.

**(e) Session estimate:** 0 for §2.3 (close it as already realized levelwise); the
optional cleanup in (a) ≈0.5 session.
