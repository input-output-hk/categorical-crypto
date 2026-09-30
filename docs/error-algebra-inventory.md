# Error-algebra inventory (WP8, before the split)

Taken at `24c48d67` (`integrate/2-qucsetup.resource`). "Uses" means the field
is named, or reached through a lemma that names it (grep over `src/`).

## Records and fields

| Record (module) | Field | Consumers that use it | Only for the collapse? |
|---|---|---|---|
| `ErrorAlgebra` (`UC.Approximate`) | `Error`, `ε₀`, `_⊕_`, `_⊑_` | every module below | no |
| | `Positive` | `Approximation._∼ᵃ_`; `Approx.Space.zero⇒positive`; `Approx.Forget.F₊`; `UC.Quantitative.Bridge` (`positive-agreement`, `Witness₊`); `UC.Quantitative.Observed.Absorbing`; `UC.Quantitative.Family.≈ᵁ⇒≈ctx` (via `reflects`) | **yes** |
| | `half` | `Approximation.∼ᵃ-isEquivalence` (transitivity) | **yes** (halving) |
| | `ε₀-least` | `∼ᵃ-isEquivalence` (reflexivity); `Approx.Space.zero⇒positive` | **yes** (positivity) |
| | `half-pos` | `∼ᵃ-isEquivalence` | **yes** (halving) |
| | `half-sum` | `∼ᵃ-isEquivalence` | **yes** (halving) |
| `Approximation Obs E` (`UC.Approximate`) | `_≈[_]_`, `≈[]-refl/sym/trans/mono` | all spaces and instances | no |
| | derived `_∼ᵃ_`, `∼ᵃ-isEquivalence` | `Approx.Space` (re-export), `Approx.Evaluation.qual₊`, `Approx.Forget`, `UC.Quantitative.Observed`, `UC.Quantitative.Family` (`reflects`), `UC.Family.Quantitative` | **yes** |
| `OrderedErrorAlgebra` (`Approx.Error`) | `errors : ErrorAlgebra` | every `Approx.*` / `UC.Quantitative*` module | carries the collapse fields in |
| | `⊑-refl` | `≈[]-resp₀`, `Approx.Controlled` (`idᶜ`, `≐-reflexive`), `Approx.Schedule`, `UC.Quantitative.Witness` | no |
| | `⊑-trans` | `≈[]-resp₀`, `Approx.Controlled` (`_∘ᶜ_`, `≈ᶜ`), `Approx.Filtered` (`≈ᶠ`), `Approx.Schedule` | no |
| | `⊕-identityˡ` (`ε₀ ⊕ ε ⊑ ε`) | `≈[]-resp₀`, `Approx.Space` (`zeroSetoid`, `≈map`, `compose-resp`), `Approx.Controlled`, `Approx.Filtered` | no |
| | `⊕-identityʳ` (`ε ⊕ ε₀ ⊑ ε`) | `≈[]-resp₀`, `UC.Quantitative.Witness` | no |
| | `⊕-mono` | `≈[]-resp₀`, `UC.Quantitative.Witness` (`at-trans`, `at-compose`) | no |
| `SmallClass ℓs` (`Approx.Small`) | `Small`, `small-ε₀`, `small-⊕` | `Approx.Small.Controlled`, `UC.Quantitative` (`underlyingSmall`), `UC.Quantitative.Bridge.Small`, `UC.Approximate.Local` (negligible) | its own existential collapse; spends only `ε₀`, `_⊕_` — no positivity, no halving |
| `Control` (`Approx.Controlled`) | `at`, `preserves-ε₀`, `preserves-⊕`, `monotone` | `Controlled`, `Filtered`, `Small.Controlled`, `Schedule.Reindexing`, `UC.Quantitative.Query` | no |
| `Allowance` (`Approx.Filtered`) | `at`, `monotone` over a `Poset` | `Filtered`, `UC.Quantitative.Query` | no |

Never used by any consumer: associativity, commutativity, the reverse unit
bounds `ε ⊑ ε₀ ⊕ ε`, and antisymmetry of `⊑`.

## Instances

| Instance | Structure | Laws true beyond the record |
|---|---|---|
| `ℚ-errors` / `ℚ-ordered` | `ℚ`, `0`, `+`, `≤`, `0 <_`, `½ *_` | an ordered commutative monoid; `≤` a total order |
| `Approx.Schedule.pointwise I V` | pointwise lift, collapse fields included | the lift of whatever `V` has; `⊑` is antisymmetric only up to pointwise `≡` (no funext) |
| `Sched` (`UC.Quantitative.Query`) = `pointwise ℕ⁺ ℚ-ordered`; `pointwise ℕ ℚ-ordered` (`UC.Approximate.Local`, `UC.Family.Negligible*`) | schedule errors | never use the collapse fields |
| `negligible` (`UC.Approximate.Local`) | `SmallClass` at `pointwise ℕ ℚ-ordered` | — |
| Filtered allowances `≤⁺-poset` | `Poset` index, not an error algebra | — |

## What the collapse spends

`∼ᵃ-isEquivalence`: reflexivity spends `ε₀-least`; transitivity spends one
refinement step (`half`, `half-pos`, `half-sum`: two positive tolerances whose
sum is below the given one). Nothing else in the finite-error layer mentions
`Positive` or `half`.

## Dependency boundary

`Approx.Error`, `Approx.Space` import `UC.Approximate` for `ErrorAlgebra`,
`ℚ-errors` and `Approximation` only. `Approx.Separating` imports
`UC.Approximate{,.Decay,.Separating}` for decay and metric facts
(`Negligible⇒→0`, `negligible-slack`, `0<inv-pow-2`, `≈ᵐ-0`, `≈ᵐ-gap`), not
for error algebra.
