# `UC.Quantitative.Family` makeover — review and spike

Base `437dca12` (`protocol-rewrite.next`), branch `family-review`. New files only:
this note and `src/CategoricalCrypto/UC/Quantitative/Spike/FamilyLean.agda` (255 lines,
unwired, `--safe --without-K`, no holes or hatches). The escape-hatch count is 16 before
and after. Warm single-module checks at `-M3G -H1G`, one `Checking` line each:
`FamilyLean` 8.7 s, current `Family` 11.0 s.

The test applied to every item: **what do we need it for, and is that need general enough?**
"Consumer" below means a code use found by `grep -rnF` over `src`. A mention in a comment is
not a consumer. The consumers of `UC.Quantitative.Family` (through
`UC.Model.Family.Contextual`) are:

- `Examples/CoinToss/Compose`, `…/Ideal/Compose` and `…/Ideal/Receiver/Compose`
- `Examples/ChimericLedger/Transfer`
- `Examples/ROCommitment/Realization/Assembly`
- `UC/Model/Family/Emulation`, and through it `UC/Machine/EventBounds/Transport` and
  `Examples/ChimericLedger/Property`, which use only `Emulation`'s own names

## Verdict

The module can drop from 600 lines to about 260 without weakening anything a consumer
uses. Three facts carry this:

1. **Only one bracket is used.** No consumer uses the `prefixᵒ` bracket. Inside the module
   it served only to prove `≈ctx-pre` and `≈ctx-dom`, and the spike proves both at the
   operational bracket at the same size. So `_≈ctx[_]_` *becomes* today's `_≈ctxᴬ[_]_`
   (`_≈ᵁᵠ[_]_` at every level). The following then go: the second relation, its four
   conversions, `splice`, `ctx-cong`, `prefixᵒ`, and with them the `Std2`/`readout`
   dependency. The module parameters become `Contextual`'s, so `∼-isEquivalence`,
   `∼-from-zero` and `reflects` go too.
2. **`Certified` is `Families._⇒^ω_`, and the model already exports it.**
   `UC.Model.Family` opens the same `Families Rg ℕ id Poly⁺ …` application publicly.
   `Certified`, `cost`, `cost-poly`, `idᶜ`, `_∘ᶜ_`, `λ⇒ᶜ` and `_⊗ᶠ_` are renamings of
   `_⇒^ω_`, `schedOf`, `schedOf-adm`, `Fam`'s identity and composite, `Famᴹ`'s left
   unitor and `_⊛ω_`. `composeSim` is `_⊗^ω_` up to a propositional equality of homs,
   at the same schedule.
3. **Half of the API has no consumer:**
   - the second witness `_≤UC^ωᵉ⁺_` and both of its conversions;
   - `≈ctx-refl`, `-sym`, `-trans`, `-≤` and `≈ᵁ⇒≈ctx`;
   - `≤UC[]-resp` and `≤UC^ωᵉ-dom`;
   - `UC-composeᵉ` and `≤UC^ωᵉ-∙` (only comments name them);
   - the general `≤UC[]-compose` (its only caller is `≤UC[]-compose′`);
   - `module Compose` as a namespace.

## 1. Per-definition table

LOC counts code plus the comment attached to the definition. "int." means the definition
is used inside `Family` only.

| name | for (consumer) | verdict | LOC |
|---|---|---|---|
| `Ap` | int.: the `Contextual` application | DELETE (becomes the parameter `Ap`) | 2 |
| `readout` | int.: `open Evaluation`/`Std2`, `≈ᵁ⇒≈ctx` | DELETE | 2 |
| `Homᶠ` | CoinToss ×3, Transfer, Assembly (16 uses) | KEEP | 2 |
| `prefixᵒ` | int.: `≈ctx` bracket only | DELETE | 5 |
| `_≈ctx[_]_` (prefix bracket) | CoinToss ×3 hypotheses (`…ᶜ`) — bracket immaterial | MERGE-INTO the `_≈ctxᴬ[_]_` definition, keeping the name `_≈ctx[_]_` | 10 |
| `_≈ctxᴬ[_]_` | Emulation (`_≈ᶠ[_]_`, bridge), Receiver (`coin-ctxᴬʰ`) | KEEP as **`_≈ctx[_]_`** | 4 |
| `≈ctx⇒agreeᵠ` | int.: `-pre`, `-dom` | DELETE (`ctx⇒agree` at every level) | 7 |
| `agreeᵠ⇒≈ctx` | int.: `-pre`, `-dom` | DELETE (`agree⇒ctx`) | 5 |
| `splice` (private) | int.: conversions, kit | DELETE | 4 |
| `≈ctx⇒≈ctxᴬ` | Emulation, Transfer: round trips only | DELETE | 11 |
| `≈ctxᴬ⇒≈ctx` | Receiver, Transfer: round trips only | DELETE | 5 |
| `ctx-cong` (private) | int.: kit | DELETE | 5 |
| `≈ctx-resp` | Receiver, Transfer, int. | KEEP (1 line: `ctx-resp` at every level) | 5 |
| `≈C⇒≈ctx` | CoinToss/Compose, Ideal/Compose | KEEP (1 line: `ctx-resp … ctx-refl`) | 6 |
| `≈ctx-refl` | none | DELETE | 2 |
| `≈ctx-sym` | none | DELETE | 2 |
| `≈ctx-trans` | int. (`compose`) | DELETE (`compose` calls `ctx-trans`) | 3 |
| `≈ctx-≤` | none | DELETE | 4 |
| `≈ᵁ⇒≈ctx` | none | DELETE (and with it the parameter `reflects`) | 4 |
| `Cᶠ` (private) | int. | KEEP as a non-public `open Families … using (…)` | 7 |
| `Certified` | CoinToss ×3, Emulation (types) | DELETE → `Y ⇒^ω X` (`UC.Model.Family`) | 2 |
| `sim` | Emulation ×4, int. | KEEP (`⌊ hom s n ⌋` is a composite, not a forwarder) | 2 |
| `cost` | int. | DELETE → `schedOf` | 2 |
| `cost-poly` | int. | DELETE → `schedOf-adm` | 2 |
| `idᶜ` | CoinToss/Compose ×1 | DELETE → `Category.id Fam` | 2 |
| `_∘ᶜ_` | Ideal/Compose, Receiver/Compose | DELETE → `Fam [ s ∘ t ]` | 3 |
| `λ⇒ᶜ` | Transfer ×1 | DELETE → `Famᴹ`'s `unitorˡ.from` | 4 |
| `subᶠ` | CoinToss ×3, Transfer, int. | KEEP | 3 |
| `≈ctx-sub` | Receiver, Transfer | KEEP (1 line: `ctx-sub` at every level) | 8 |
| `NegligibleBound-scale` | Transfer, int. ×3 | MOVE-TO `UC.Approximate` (beside `GradedBound-reindex`) | 8 |
| `_≤UC[_,_]_` | CoinToss ×3, Emulation | KEEP | 9 |
| `≤UC[]-resp` | int. (`≤UC^ωᵉ-resp`) | DELETE (inline) | 5 |
| `_≤UC^ωᵉ_` | CoinToss ×3, Assembly | KEEP | 6 |
| `≤UC^ωᵉ-resp` | Assembly | KEEP | 4 |
| `_≤UC^ωᵉ⁺_` | none | DELETE | 9 |
| `≤UC^ωᵉ⇒⁺` | none | DELETE | 15 |
| `≤UC^ωᵉ⁺⇒` | none | DELETE | 6 |
| `module Compose` | 5 consumers `open Compose` | DELETE (flatten) | 10 |
| `seqError` | int. (the statement of `≤UC[]-trans`) | KEEP | 4 |
| `seqError-negligible` | Ideal/Compose, Receiver/Compose | KEEP | 6 |
| `≤UC[]-trans` | Ideal/Compose, Receiver/Compose | KEEP (1 line: `at-trans`) | 9 |
| `≤UC^ωᵉ-trans` | Assembly | KEEP | 5 |
| `_⊗ᶠ_` | CoinToss ×3 (types) | DELETE → `_⊛ω_` (identical definition) | 4 |
| `_∙ᶠ_` | CoinToss ×3, Transfer, Assembly | KEEP | 3 |
| `≈ctx-ext` | Transfer | KEEP | 18 |
| `≈ctx-pre` | int. (`compose`) | KEEP, re-proved at the single bracket | 27 |
| `≈ctx-dom` | none (named in an Ideal/Compose comment) | MERGE-INTO `≤UC[]-dom` | 20 |
| `≤UC[]-dom` | Ideal/Compose, Receiver/Compose | KEEP, absorbing `≈ctx-dom` | 8 |
| `≤UC^ωᵉ-dom` | none | DELETE | 5 |
| `composeSim` | CoinToss/Compose (`simᶜᵗ`) | DELETE → `_⊗^ω_` | 9 |
| `composeError` | int. (statement) | KEEP | 5 |
| `composeError-negligible` | CoinToss/Compose | KEEP | 10 |
| `≤UC[]-compose` (cert. of the composite) | int. (`compose′`) | MERGE-INTO the one below *(maintainer call, see §2.5)* | 41 |
| `≤UC[]-compose′` | CoinToss/Compose | KEEP as **`≤UC[]-compose`** | 14 |
| `UC-composeᵉ` | none (comments in Assembly, CoinToss/UC, Hiding/UC) | DELETE | 16 |
| `≤UC^ωᵉ-∙` | none | DELETE | 9 |

Of the `module _`/`Compose` internals the brief names: `≤UC[]-trans`, `≤UC[]-dom`,
`≤UC[]-compose′`, `seqError` and `composeError` are content and stay.
`≤UC[]-compose` merges into `′` (§2.5).

`Contextual.agda` loses only `ctx-sym` (no consumer, −2 lines). Its comments that name
`prefixᵒ` and `Family`'s `Compose` names need rewording: lines 20–22, 84–86, 113–115,
189–191, 202–205. It stays a separate module: its single-level lemmas are what `Family`
applies at every level, and merging the two saves no lines.

## 2. The eight questions

### 2.1 One bracket

The consumers need **`_≈ᵁᵠ[_]_` at every level**, today's `_≈ctxᴬ[_]_`.

The operational bracket `W ⊗ (X ⊗ B)` is required by the following:

- `UC.Model.Dominated.dominatedᵍ`, used by Receiver's `coin-ctxᴬʰ`.
- `UC.Family._≈ℰ[_]_`, which `Emulation.≈ctxᴬ⇒≈ℰ[]` targets.
- `Seam.Audit.Context`'s `auditTest`, used by `Emulation.≈ᶠ-runs`.
- `Emulation._≈ᶠ[_]_`, consumed by Transfer, Transport and Property.

`UC.Model.Family.Ingest` does not import `Quantitative.Family` at all. It works at
`_≈ℰ[_]_`, which is also operational.

No consumer requires the prefix bracket `(W ⊗ X) ⊗ B`. Every consumer use of `_≈ctx[_]_`
either passes it through (the three CoinToss `…ᶜ` hypotheses) or is a round trip:

- `Transfer.hash-liftᵇ` goes `≈ctxᴬ⇒≈ctx`, then `-ext`, `-sub`, `-resp`, then `≈ctx⇒≈ctxᴬ`.
- `Receiver.coin-hybridʳᵇ` goes `≈ctxᴬ⇒≈ctx` and then `-sub`.
- `Emulation.≤UC[]⇒≈ℰⁿ` ends with `≈ctx⇒≈ctxᴬ`.

Inside `Family`, `-sub`, `-ext` and `-trans` already detour through `≈ctxᴬ`. Only `-pre`
and `-dom` use the prefix bracket, through `Abstract2`'s `∙-decomp`/`μT`.

The spike re-proves both at the operational bracket:

- **`≈ctx-pre`:** `absorb-closureᵠ` with the structural test map
  `id ⊗ α⇐ ∘ α⇒ : (W⊗X)⊗(P⊗C) ⇒ W⊗((X⊗P)⊗C)` at `1⁺` and the closure `α⇐ ∘ id ⊗ f` at
  `rf`. The step is `α⇒ ∘ id⊗u ∘ α⇐ ≈ id⊗(id⊗u)` (`assoc-commute-from`, `cancelʳ`). It is
  27 lines, against 27 today.
- **`≤UC[]-dom`:** `absorb-closureᵠ` at `1⁺` with `id ⊗ p`, then `ctx-mono` along
  `scale-unit`. It is 12 lines, against today's 20 + 8 for `≈ctx-dom` + `≤UC[]-dom`.

So `_≈ctxᴬ_` alone suffices. The definitional choice is to give `_≈ctx[_]_` today's
`_≈ctxᴬ[_]_` body. The other relation and all four conversions go. Because both relations
carry the same `ε` and are inter-derivable, no statement changes meaning in a weakening
direction (§4).

### 2.2 The enrichment kit

At the single bracket, every kit lemma is `λ n → ctx-x (ε n) … (h n)`.

- `≈ctx-resp` (2 consumers) and `≈C⇒≈ctx` (2 consumers) stay at one line each.
- `≈ctx-refl`, `-sym`, `-≤` and `≈ᵁ⇒≈ctx` have no consumer and are deleted.
- `≈ctx-trans` is used once, inside `compose`, which now calls `ctx-trans` directly.

A generic "levelwise lifting" lemma over `ℕ →` buys nothing. The lemmas have different
arities and argument shapes, so it would be one lifting per arity, which is no shorter
than the one-liners. If a consumer ever needs `sym`, it writes
`λ n → ctx-sym (ε n) (h n)`.

### 2.3 `Certified` and its wrappers

Open the construction and use its names. `UC.Model.Family` already exports `_⇒^ω_`,
`_⊛ω_`, `_⊗^ω_`, `Fam`, `Famᴹ`, `hom`, `schedOf` and `schedOf-adm` from the *same*
`Families` application, so the model-level consumers have them in scope. `Emulation`
already passes a `Certified` to `Canonicalᴺ.sub` (a `_⇒^ω_` argument) and checks.

In the generic module, `Families` is opened non-publicly with a `using` list. A public
re-export would clash with `UC.Model.Family`'s names in Ideal/Compose and Receiver/Compose,
which open both. That clash is the reason for the `using` list (rule 11).

Replacements:

- `Certified Y X` → `Y ⇒^ω X`
- `cost` → `schedOf`
- `cost-poly` → `schedOf-adm`
- `s ∘ᶜ t` → `Fam [ s ∘ t ]`
- `idᶜ` → `Category.id Fam`
- `λ⇒ᶜ X` → `Famᴹ`'s `unitorˡ.from`. It is definitionally `unit^ω λ _ → _ , pred-λ⇒`, at
  type `(Δ unit ⊛ω X) ⇒^ω X`, and its schedule is still `1⁺`, so Transfer's `εᴴ` is
  unchanged.
- `X ⊗ᶠ P` → `X ⊛ω P`
- `composeSim sf t` → `sf ⊗^ω t`

`sim` stays as a name. It is used at five sites and is the composite `⌊ hom s n ⌋`, not a
forwarder.

### 2.4 Two witnesses

`_≤UC^ωᵉ⁺_` is the adversary-quantified form at `Abstract2._≤UC_`'s quantifier order, and
`≤UC^ωᵉ⇒⁺`/`⁺⇒` are `dummy-complete`/`≤UC⇒dummy` with costs. It buys a *documented*
equivalence with the qualitative order's shape. No module states anything at `⁺`, and the
negligible order consumers reach goes through `Emulation.≤UC[]⇒≤UCᴺ`, which uses
`Canonicalᴺ.dummy-complete` directly. Verdict: one witness, `_≤UC^ωᵉ_`, and
`⁺` + both conversions are deleted (−30 lines).

### 2.5 The composition laws

`≤UC[]-trans` and `≤UC[]-dom` are content and stay; `trans` is now one line over
`at-trans`. The rate algebra:

- `NegligibleBound-scale` is general: it reindexes a negligible bound along `scale _ r` at
  a `Poly⁺` rate. It has a second consumer (Transfer), so it **moves to `UC.Approximate`**,
  beside `GradedBound-reindex`, at the cost of a `Data.Nat.Positive` import there.
- `seqError`, `composeError` and their `-negligible` lemmas are the published error
  formulas of these two laws, statement vocabulary with no use outside them, so they stay
  in `Family`. `Data/Nat/Positive` already has `scale-comm`/`scale-·`/`poly-scale` and
  needs nothing new.

`≤UC[]-compose′` is a second spelling of `≤UC[]-compose`. It is the general law applied to
the product-rule certificate of `sub (sim t n) ∘ v n`, which takes 4 lines.

- Only `′` has a consumer: CoinToss/Compose, and `UC-composeᵉ`, which itself has none.
- The general form is strictly sharper. It takes a certificate of the composite, and its
  header says a sharper one "is used as it stands".

Proposal: keep **one** law in the consumer's form, named `≤UC[]-compose` and taking a
certificate for `v`, with the composite certificate built inside. Its simulator is
`sf ⊗^ω t`. This deletes an unconsumed generalization. That is allowed under rules 1 and
4 because nothing is weakened to make something pass, but it is the maintainer's call.
The sharp form comes back in about 4 lines if a consumer ever certifies a composite more
tightly than the product rule.

### 2.6 Plumbing

- `Ap` and `readout`: no (they become parameters, or are deleted).
- `prefixᵒ`: no.
- `Homᶠ`: yes (16 consumer uses).
- `module Compose`: no. It is a parameterless namespace, and five consumers carry an
  `open Compose` line that goes.

The 4-line comment on `prefixᵒ` (+22 s for naming `UCSetup.prefix`) goes with it. The
`Std2.StdUC` application it worked around also goes: `ext`/`sub`/`μ`/`T₁` now come from
`Categories.Monad.Graded.FromMonad (curriedTensor M)`, the same terms `StdUC` exposes, so
consumers' definitional equalities are untouched (the spike's `≈ctx-ext`/`-sub` check
against `ctx-absorb`/`ctx-sub` unchanged).

### 2.7 Comments

The proposed header is 9 lines:

```agda
-- The ε-contextual relation on families of morphisms, `_≈ctx[_]_` —
-- `UC.Quantitative.Contextual._≈ᵁᵠ[_]_` at every level — and the emulation
-- bound over it at a named simulator family and schedule, `_≤UC[_,_]_`, with
-- its composition laws at their error formulas (`seqError`, `composeError`).
-- Simulators are `Categories.LocallyGraded.Family` homs at `Poly⁺` schedules;
-- the compared morphisms carry no rate, and a morphism a law moves into a
-- context is asked for an `Image` certificate.  `_≤UC^ωᵉ_` hides the data and
-- classifies the schedule as negligible.  Design note:
-- `docs/quantitative-family.md`.
```

Of the 156 comment lines:

- About 70 go with their deleted definitions.
- 24 of the 33 header lines go.
- What remains goes per rules 21 and 22: the per-section "with its cost" glosses, the
  `Abstract2` step-by-step narration (`Compose`'s 9-line preamble), and the "Σ and not a
  record, for a MEASURED reason" note.
  - The Σ note matters only if someone turns `_⇒^ω_` into a record. It belongs at
    `Families._⇒^ω_` if anywhere, and is not `Family`'s.

The spike has 19 comment lines, and the target about 20.

Side finding, outside the brief:

- `UC/Family.agda` has a 42-line header and a 17-line closing essay
  ("What is NOT delivered here…"). Both are design narration, and the essay names
  `UC.Model.Family.Contextual.Compose`, which this makeover removes.
- `Assembly.agda:87` says `UC-composeᵉ` builds its composite. It does not: it goes through
  `coin-from-Rcom`, i.e. `toss-over`. That comment is stale already.

### 2.8 The instance modules and `UC/Family.agda`

- **`UC/Model/Family/Contextual`** (23 lines) is `Quantitative.Family` at the seal, the
  module every consumer opens. It stays. Its arguments become
  `𝔾ᵒ gradingᵒ (QEvaluation.approx qevaluationᵒ) J Ω read read-resp₀`, and the 4-line
  "spelled exactly as `qual₊`" comment and the `AllPositive` module go, because no
  readout is a parameter any more.
  - Optional: merge it into `UC/Model/Family` (−23 lines, one import fewer in 6
    consumers). This puts `Contextual`/`Query` into the closure of every
    `UC.Model.Family` importer (`Ingest`, `Dominated`, …). Measure the closure before
    doing it. Not recommended blind.
- **`UC/Model/Family/Emulation`** (111 lines) bridges the family relation to protocol
  images (`_≈ᶠ[_]_`, `_≈ᶠᴺ_`, `≈ᶠ-runs`). It also bridges to the canonical negligible
  order (`≤UC[]⇒≈ℰⁿ`, `≤UC[]⇒≤UCᴺ` — the `Cᴺ.≤UC` bridge the brief names). It stays.
  - `≈ctxᴬ⇒≈ℰ[]` is renamed `≈ctx⇒≈ℰ[]`.
  - `≤UC[]⇒≈ℰⁿ` loses its `≈ctx⇒≈ctxᴬ`.
  - `Certified Y X` becomes `Y ⇒^ω X`.
  - The 15-line header is design narration and shrinks to about 4 lines.
- **`UC/Model/Family/Ingest`** (102 lines) is `UC.Family`'s `_≈ℰ[_]_` ingestion of a
  machine advantage bound. It does not touch `Quantitative.Family` and is out of this
  makeover.
- **`UC/Family.agda` vs `Quantitative/Family`: not two spellings.**
  - `UC.Family` is the asymptotic family `UCSetup` (`ucSetup^ω`, consumed by
    `Family.Negligible.Setup` and `Family.Quantitative`) over `Famᴹ`. Its homs are
    *certified* families, and `_≈ℰ[_]_` quantifies over *families* of contexts that carry
    one polynomial.
  - `Quantitative.Family` compares *uncertified* hom families (`Homᶠ`), with the context
    quantified *per level*.
  - The only map between them is the one-way `Emulation.≈ctxᴬ⇒≈ℰ[]`, and the
    `≈ℰ[]`/`≈ℰⁿ` consumers (Dominated, Ingest, Observed, RandomOracle*) are a different
    population. Both survive.
  - What they genuinely share is the `Families` instance. §2.3 is what makes
    `Quantitative.Family` stop re-spelling it.

## 3. Target module outline

`UC/Quantitative/Family.agda`, about 260 lines (the spike is 255, plus `sim`). Parameters
are `Contextual`'s:
`M Rg Ap 𝟙 Ω ⟦_⟧ obs-resp`.

| section | contents | LOC |
|---|---|---|
| header, imports, parameters, opens | 9-line header; `Contextual` application; `FromMonad (curriedTensor M)`; non-public `Families … using (_⇒^ω_; _⊛ω_; _⊗^ω_; Fam; hom; schedOf; schedOf-adm)` | 60 |
| the relation | `Homᶠ`, `_≈ctx[_]_`, `≈C⇒≈ctx`, `≈ctx-resp`, `sim`, `subᶠ`, `_∙ᶠ_` | 28 |
| the three plugs | `≈ctx-sub`, `≈ctx-ext`, `≈ctx-pre` | 59 |
| bounds and witness | `_≤UC[_,_]_`, `_≤UC^ωᵉ_`, `≤UC^ωᵉ-resp` | 15 |
| composition laws | `seqError(-negligible)`, `≤UC[]-trans`, `≤UC^ωᵉ-trans`, `≤UC[]-dom`, `composeError(-negligible)`, `≤UC[]-compose` | 84 |

The spike also carries `NegligibleBound-scale` (8 lines). In the implementation it moves
to `UC.Approximate`, and its `Data.Nat.Positive` import is about +2 lines there.

Net, from `git diff --stat`-style estimates:

| file | now | after | Δ |
|---|---|---|---|
| `UC/Quantitative/Family` | 600 | ~252 | −348 |
| `UC/Quantitative/Contextual` | 216 | ~205 | −11 (`ctx-sym`, comment rewording) |
| `UC/Approximate` | — | — | +10 (`NegligibleBound-scale` + import) |
| `UC/Model/Family/Contextual` | 23 | ~10 | −13 |
| `UC/Model/Family/Emulation` | 111 | ~98 | −13 (header, one conversion) |
| CoinToss ×3, Transfer, Assembly | — | — | about −10 (`open Compose` ×5, Transfer's two conversions, Receiver's one) |
| **total** | | | **≈ −385** |

## 4. Consumer statements whose text changes

None of these weakens anything.

- Every `Certified`/`⊗ᶠ` change is a renaming to the definitionally equal `Families` name.
- `composeSim sf t` → `sf ⊗^ω t` keeps the schedule `cost sf n · cost t n`, so every
  `seqError`/`composeError` reading is unchanged. The hom becomes `⌊sf⌋ ⊗₁ ⌊t⌋` instead
  of `⌊(id ⊗ t) ∙ (sf ⊗ id)⌋`; these are equal by `serialize₂₁`, and no consumer reads it.
- `_≈ctx[_]_` hypotheses keep their text and move from the prefix to the operational
  bracket at the *same* `ε`. The two are inter-derivable exactly (today's
  `≈ctx⇒≈ctxᴬ`/`≈ctxᴬ⇒≈ctx`), so no hypothesis gets stronger.

`Examples/CoinToss/Compose`:

```agda
simᶜᵗ : {Lk Adv Advᶜ : ℕ → Channel} → Certified Lk Adv → Certified (Lk ⊗ᶠ Advᶜ) (Adv ⊗ᶠ Advᶜ)
-- →
simᶜᵗ : {Lk Adv Advᶜ : ℕ → Channel} → Lk ⇒^ω Adv → (Lk ⊛ω Advᶜ) ⇒^ω (Adv ⊛ω Advᶜ)
-- body: composeSim sf idᶜ  →  sf ⊗^ω Category.id Fam

toss-overᵇ : (sf : Certified Lk Adv) …            →  toss-overᵇ : (sf : Lk ⇒^ω Adv) …
coin-toss-from-comᵇ  : (sf : Certified Lkᶠ Advᶠ) …   →  (sf : Lkᶠ ⇒^ω Advᶠ) …
coin-toss-from-comʰᵇ : (sf : Certified Lkʰᶠ Advʰᶠ) … →  (sf : Lkʰᶠ ⇒^ω Advʰᶠ) …
comSim  : Certified Lkᶠ Advᶠ    →  comSim  : Lkᶠ ⇒^ω Advᶠ
comSimʰ : Certified Lkʰᶠ Advʰᶠ  →  comSimʰ : Lkʰᶠ ⇒^ω Advʰᶠ
-- coin-toss-from-comᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ → …   (text unchanged)
```

`Examples/CoinToss/Ideal/Compose`:

```agda
simᶜᶠ : Certified Lkᶜᶠ (Lkᶠ ⊗ᶠ Advᶜᶠ)         →  simᶜᶠ : Lkᶜᶠ ⇒^ω (Lkᶠ ⊛ω Advᶜᶠ)
simᶜⁱ : Certified Lkᶠ Advᶠ → Certified Lkᶜᶠ (Advᶠ ⊗ᶠ Advᶜᶠ)
  →  simᶜⁱ : Lkᶠ ⇒^ω Advᶠ → Lkᶜᶠ ⇒^ω (Advᶠ ⊛ω Advᶜᶠ)      -- body: Fam [ simᶜᵗ sf ∘ simᶜᶠ ]
coin-toss-idealᵇ : (sf : Certified Lkᶠ Advᶠ) …  →  (sf : Lkᶠ ⇒^ω Advᶠ) …
```

`Examples/CoinToss/Ideal/Receiver/Compose`:

```agda
simᶜʰᶠ : Certified Lkᶜʰᶠ (Lkʰᶠ ⊗ᶠ Advᶜʰᶠ)  →  simᶜʰᶠ : Lkᶜʰᶠ ⇒^ω (Lkʰᶠ ⊛ω Advᶜʰᶠ)
flatᶜʰ : Certified Lk♯ᶠ (Lkʰᶠ ⊗ᶠ Advᶜʰᶠ)   →  flatᶜʰ : Lk♯ᶠ ⇒^ω (Lkʰᶠ ⊛ω Advᶜʰᶠ)
simᶜʳ : Certified Lkʰᶠ Advʰᶠ → Certified Lkᶜʰᶠ (Advʰᶠ ⊗ᶠ Advᶜʰᶠ)
  →  simᶜʳ : Lkʰᶠ ⇒^ω Advʰᶠ → Lkᶜʰᶠ ⇒^ω (Advʰᶠ ⊛ω Advᶜʰᶠ)
coin-toss-idealʳᵇ : (sf : Certified Lkʰᶠ Advʰᶠ) …  →  (sf : Lkʰᶠ ⇒^ω Advʰᶠ) …
coin-ctxᴬʰ : hybʰᶠ ≈ctxᴬ[ ηʰ ] idlʰᶠ  →  coin-ctxᴬʰ : hybʰᶠ ≈ctx[ ηʰ ] idlʰᶠ   (same relation)
-- coin-hybridʳᵇ's proof loses `≈ctxᴬ⇒≈ctx ηʰ`
```

`Examples/ChimericLedger/Transfer` (`factorᴿ` is private):

```agda
factorᴿ : … → subᶠ (λ⇒ᶜ (Δ 𝟘ᴳ)) (ledgerᶠ ∙ᶠ imgᶠ HashIf^ω hash) n ≈ …
  →  factorᴿ : … → subᶠ Fᴹ.unitorˡ.from (ledgerᶠ ∙ᶠ imgᶠ HashIf^ω hash) n ≈ …
-- with `module Fᴹ = MonoidalCategory Famᴹ`; hash-liftᵇ's proof loses both conversions
```

`UC/Model/Family/Emulation`:

```agda
_≈ᶠ[_]_ … = imgᶠ B R ≈ctxᴬ[ ε ] imgᶠ B I  →  … = imgᶠ B R ≈ctx[ ε ] imgᶠ B I   (same relation)
≈ctxᴬ⇒≈ℰ[] : … → sim f ≈ctxᴬ[ ε ] sim g → _≈ℰ[_]_ {A} {X ⊛ω B} f ε g
  →  ≈ctx⇒≈ℰ[] : … → sim f ≈ctx[ ε ] sim g → _≈ℰ[_]_ {A} {X ⊛ω B} f ε g
module _ {A X Y B : Obj^ω} (s : Certified Y X) …  →  module _ {A X Y B : Obj^ω} (s : Y ⇒^ω X) …
```

`Examples/ROCommitment/Realization/Assembly` has no statement change. It loses its
`open Compose` line and its stale `UC-composeᵉ` comment.

Generic `Family` statements that change, besides the deletions in §1:

```agda
≤UC[]-trans : … → f ≤UC[ s ∘ᶜ t , seqError s ε δ ] h
  →  … → f ≤UC[ Fam [ s ∘ t ] , seqError s ε δ ] h                         -- definitionally equal
≤UC[]-compose′ : … (sf : Certified Y X) (t : Certified Q P) (rf rv : ℕ → ℕ⁺) …
  → (u ∙ᶠ f) ≤UC[ composeSim sf t , composeError rf (λ n → rv n · cost t n) εf εu ] (v ∙ᶠ g)
  →  ≤UC[]-compose : … (sf : Y ⇒^ω X) (t : Q ⇒^ω P) (rf rv : ℕ → ℕ⁺) …
  → (u ∙ᶠ f) ≤UC[ sf ⊗^ω t , composeError rf (λ n → rv n · schedOf t n) εf εu ] (v ∙ᶠ g)
_∙ᶠ_ : Homᶠ B P C → Homᶠ A X B → Homᶠ A (X ⊗ᶠ P) C  →  … → Homᶠ A (X ⊛ω P) C
```

The module telescope changes from `(M qro Rg ∼-isEquivalence ∼-from-zero reflects)` to
`(M Rg Ap 𝟙 Ω ⟦_⟧ obs-resp)`.

## 5. Implementation and estimate

There is one new branch-2 ref on `protocol-rewrite.next`.

1. Write the new `Family` from the spike: add `sim`, move `NegligibleBound-scale`, and
   use the §2.7 header.
2. Update `Model/Family/Contextual`'s arguments.
3. Update `Emulation`, the three CoinToss modules, `Transfer` and `Assembly` per §4.
4. Reword the comment references: `Contextual` ×5, `UC/Graded` ×2, `Approx/Schedule`,
   `CoinToss/Ideal/Reach`, `CoinToss/Ideal/Compose:9`, `CoinToss/UC:4`, `Hiding/UC:4`,
   `UC/Family:269`.
5. Delete the spike.
6. Run the checks, consumers first:
   - `Family`
   - `Model/Family/{Contextual,Emulation}`
   - the CoinToss trio, `Assembly` and `Transport` at `-M8G -H2G`
   - `ChimericLedger/{Transfer,Property}` at `-M8G -H2G`
   - the root closure

Rebase hazard: another agent is editing `Family`'s imports (the `UC/Audit` retirement).
The new file replaces the import block wholesale, so the result is a trivial conflict
that keeps ours. `docs/quantitative-family.md` (about 70 mentions of removed names) is a
design note, so it gets a one-paragraph errata pointer rather than a rewrite.

**Estimate: 1 session** (about half of it for checks: the warm consumer trio plus a cold
root closure of 9–15 min).
