# Spike: certified homs as the objects of comparison (option §2.1)

**2026-09-30: modules deleted** (shelved). Recover with `git log --diff-filter=D --oneline -- src/CategoricalCrypto/UC/Quantitative/Spike`, then `git show <commit>^:<path>`.

Branch `memo21-spike`, based on `3034aa9c`. The spike adds three new modules under
`src/CategoricalCrypto/UC/Quantitative/Spike/` (433 lines in total). None of them is
wired into anything, and no existing file changed. All three are `--safe --without-K`,
the escape-hatch grep finds nothing, and the warning gate is empty.

| module | lines | warm check | heap |
|---|---|---|---|
| `Spike.AllowanceNoGo` | 85 | 15 s | `-M3G -H1G` |
| `Spike.FilteredSetup` | 168 | 25 s | `-M3G -H1G` |
| `Spike.Instance` | 180 | 19 s | `-M6G -H2G` (`-M4G` runs out of heap) |

The file is 33 lines over the 400-line budget. The overrun is `𝒞ᵇᴹ`, the monoidal rated
base, which is itself one of the missing ingredients (§5).

## 1. Question and verdict

The hypothesis under test (`simplification-options.md` §2.1) is this: make the
certified homs the ones that are compared. Then `_≤UC^ωᵉ_` and `_≈ctx[_]_` would be the
generic `_≤UC_`/`_≈ᵁ_` of a single `QUCSetup`, and `≤UC[]-compose` would be one
application of the generic composition theorem.

**The hypothesis fails as stated, for a structural reason (§2).** A `QUCSetup` compares
two *elements* of an `Approx` space. `_≈ctx[_]_`, however, reads its error at the
allowance of the *context*, and the context is no longer visible once the compared hom
has been pulled through it. `AllowanceNoGo` proves that an element-level closeness which
reads an allowance off the two elements cannot be transitive unless it ignores the
allowance. Beyond that, an exact instance would prove `QWitness.at-trans` and
`at-compose` with their *unscaled* errors `ε ⊕ δ` and `εu ⊕ εf`. Those are stronger than
`seqError` and `composeError`, and they are not the family theory's content.

**A version with the presheaf valued in `Filt` instead of `Approx` works (§3, §4).**
`FilteredSetup` is `QUCSetup` with `Q : Presheaf 𝒞 (Filt …)` and with the admitted
agreement `_≈ᵃ[_]_` as its comparison. At the rated base `Query.𝒞ᵇ`, which the spike
makes monoidal as `𝒞ᵇᴹ`, the following were proved at one security level:

- (a) `generic⇔ctx`: the generic relation is exactly `_≈ᵁᵠ[_]_` on the underlying
  morphisms. The rates of the compared homs never enter.
- (b) `trans-instance` and `compose-instance`: the generic `at-trans` and `at-compose`
  produce exactly `seqError` and `composeError`, the latter at `≤UC[]-compose′`'s product
  rule. Each schedule side condition is discharged by one ring identity on `ℕ`.

It is a win in structure, not in lines (§6). It is a no-go for the LOC motive, and a
conditional go if a single composition theory is wanted, conditional on the reach
question in §5, M3.

## 2. The obstruction, as a typing failure

Two definitions collide:

```agda
-- UC.Quantitative (QUCSetup)
f ≈ᵁ[ ε ] g = (W : ℐ.Obj) (e : Env (T₀ (W ⊗₀ X) B)) → run W f e ≈[ ε ] run W g e
run W f e   = pull (prefix W f) e

-- UC.Quantitative.Family
f ≈ctx[ ε ] g = (n : ℕ) (W : Channel) (E : …) (m : …) {c r′ : ℕ⁺}
              → Image forget c E → Image forget r′ m
              → read ((E ∘ prefixᵒ W (f n)) ∘ m) ≈[ ε n (value (c · r′)) ] read (…)
```

`ε n (value (c · r′))` needs `c`, the rate at which the **unpulled** test `E` is
certified. In the generic term, the closeness `_≈[ ε ]_` at `T₀ W A` receives only
`run W f e` and `run W g e`, which are *pulled* elements. No `Image forget c E` reaches
that space. For `c` to be visible there it would have to be a tag on the elements, and
the two sides carry different tags, `c · r_f` and `c · r_g`. `AllowanceNoGo.SetForm`
formalises this, with carrier `a × ℚ` and closeness
`(x , v) ≈⟨ ε ⟩ (y , w) = ∀ q → S x y q → ∣ v - w ∣ ≤ ε q`:

```agda
no-go : Transitive → (x y z q : a) → S x z q → S x y q × S y z q
certificate-no-go : ¬ Transitive   -- S x y q = x ≤ q × y ≤ q, the upward `Image forget` reading
```

A single pinned point `S a b = {J a b}`, such as `max` or `min`, must be constant in both
tags. That is, it reads no allowance at all. The reading "at every certificate both
sides carry" is not transitive even once, because an expensive middle element leaves the
cheap pair unconstrained. The Σ-form "equal tags × bound" does escape this, but it
requires the compared homs to have equal rates, which is the grade-stable restriction.

This is the typing failure the header of `Quantitative/Family` (~l.320) describes. A
certificate is needed at the place where the test is moved, and the generic
`QuantitativeUC.ctx-sub : f ≈ᵁ[ ε ] g → sub s ∘ f ≈ᵁ[ ε ] sub s ∘ g` gives its
conclusion at an unchanged `ε`. A `Nonexpansive` map has no control, so there is nowhere
to write the reindexing `ε ∘ scale _ (cost s)`. Two variants were also considered:

- **`Fam` from `UC/Family.agda` as the base.** Its equality `_≈^ω_` ignores rates, and
  `QEvaluation.eval₀.cong` must respect that equality. So any readout is rate-blind, and
  only allowance-free errors (`Qᴺ.QSetup`, `ℕ → ℚ`) are possible. Those imply
  `_≈ctx[ λ n _ → δ n ]_`. The converse fails: an allowance-graded bound such as
  `q·2⁻ⁿ` has no bound that is uniform in the allowance.
- **`𝒞 := L` from the brief.** It is a locally graded category, not a `Category`. Its
  total category is `Query.𝒞ᵇ`, where the rate is part of the hom's equality.

## 3. The Filt-valued setup (`Spike.FilteredSetup`)

```agda
record FQUCSetup … where
  field 𝒞 : Category o′ ℓ′ e′ ; ℐ : MonoidalCategory o ℓ e ; ℳ : GradedMonad ℐ 𝒞
        Q : Presheaf 𝒞 (Filt c ℓa ℓd)

underlying₀ = record { …; ℰ = Forget c ℓa ℓd ∘F S.Q }   -- zero-error part; all UCSetup lemmas reused

_≈ᵁᶠ[_]_ f Ε g = (W : ℐ.Obj) → run W f ≈ᵃ[ Ε ] run W g      -- admitted agreement: Ε read at the UNPULLED test's allowance

PreBound  k Ε Ε′ = (q : Ix) → Ε (⟦ Filtered.allowance (Pull k) ⟧ q) ⊑ Ε′ q          -- k moved into the test
PostBound k Ε Ε′ = (q : Ix) → Control.at (control (Pull k)) (Ε q) ⊑ Ε′ q            -- k moved into the closure
```

The module proves the following, each as a short composition of `≈ᵃ-pre` and `≈ᵃ-post`
with `UCSetup`'s `run-sub`, `∙-decomp` and `μT`:

- `ctx-trans` and `ctx-resp`.
- `ctx-sub`, with a `PreBound` at `sub (id ⊗ s)`.
- `ctx-ext`, with a `PreBound` at `sub α⇒ ∘ ext (W⊗X) k`.
- `ctx-pre`, with a `PostBound` at `prefix W f` after a `PreBound` at `sub α⇒`.
- `At s Ε f g = f ≈ᵁᶠ[ Ε ] sub s ∘ g`.
- `at-trans`, whose output is `Ε ⊕ Δ′` with `Δ′` the absorbed `Δ`.
- `at-compose`, whose output is `Δ′ ⊕ Ε′`, using the same `strict` equation as
  `QWitness.at-compose`.

Every side condition is uniform in the ancilla `W`, because the rate of the moved
morphism does not depend on `W`.

## 4. The instance at the rated base (`Spike.Instance`)

```agda
_⊗ᵇ_ : Budgeted A B → Budgeted C D → Budgeted (A ⊗₀ C) (B ⊗₀ D)
(r , f) ⊗ᵇ (s , g) = r · s , f ⊗ʰ g
𝒞ᵇᴹ : MonoidalCategory o (ℓ ⊔ qs) e           -- monoidalHelper; every law = M-law , value-injective (ring identity)
setupᵇ = record { 𝒞 = MonoidalCategory.U 𝒞ᵇᴹ ; ℐ = 𝒞ᵇᴹ ; ℳ = Curried.curriedTensor 𝒞ᵇᴹ ; Q = Qᵠ }

generic⇔ctx : (ε : ℕ → ℚ) {f g : Budgeted A (X ⊗₀ B)}
  → (f ≈ᵁᶠ[ (λ q r′ → ε (value (q · r′))) ] g) ⇔ (⌊ proj₂ f ⌋ ≈ᵁᵠ[ ε ] ⌊ proj₂ g ⌋)

trans-instance : … → At s (λ q r′ → ε (value (q · r′))) f g → At t (λ q r′ → δ (value (q · r′))) g h
  → At (s ∘ t) (λ q r′ → ε (value (q · r′)) ℚ.+ δ (scale (value (q · r′)) (proj₁ s))) f h

compose-instance : … → At s (…εf…) f g → At t (…εu…) u v
  → At ((id ⊗ t) ∘ (s ⊗ id)) (λ q r′ → εu (scale (value (q · r′)) (proj₁ f))
                                     ℚ.+ εf (scale (value (q · r′)) (proj₁ v · proj₁ t)))
       (u ∙ f) (v ∙ g)
```

The schedules at the instance, read at `q_family = value (c · r′)`, are these:

- `trans-instance` gives `seqError s ε δ n` at level `n`.
- `compose-instance` gives `composeError rf (λ n → rv n · cost t n) εf εu n`, which is
  `≤UC[]-compose′`.

The simulator `(id ⊗ t) ∘ (s ⊗ id)` in `𝒞ᵇᴹ` carries the product rate by definition, so
`composeSim` is no longer needed. The sharper `≤UC[]-compose`, which takes an arbitrary
certificate for `sub t ∘ v`, needs one more step. By `generic⇔ctx` the relation depends
only on `⌊_⌋`, so `sub t ∘ v` can be swapped for any rated hom with the same underlying
morphism. This is one instance-level lemma and was not written.

On lifting (a) to families: `_≈ctx[_]_` is levelwise, and `Family.≈ctx⇔≈ctxᴬ` together
with `generic⇔ctx` at each `n` give `f ≈ctx[ ε ] g ⇔ ∀ n → f̂ n ≈ᵁᶠ[ ε n ∘ · ] ĝ n` for
any rated lifts. Glue of about 20 lines is needed and was not written. `_≤UC^ωᵉ_` is then
the Σ of a certified simulator, a schedule, `NegligibleBound`, and `At` at every level.
The negligibility packaging and `Poly⁺` remain specific to the family layer. The generic
filtered theory has an `At` and no ∃-order, so `_≤UC^ωᵉ_` is still not literally a
generic `_≤UC_`.

Performance: spelling `setupᵇ`'s `𝒞` as `𝒞ᵇ` instead of `U 𝒞ᵇᴹ` costs 25 s against
6 s. Residency is 2 GiB either way, which is recorded in the module header.

## 5. Missing ingredients

| # | ingredient | kind | status |
|---|---|---|---|
| M1 | a monoidal structure on the rated base (`𝒞ᵇᴹ`) | structural | built, ~35 lines |
| M2 | a Filt-valued setup and its kit (`FQUCSetup`); `QUCSetup` is `Approx`-valued and cannot host it (§2) | structural | built, 168 lines |
| M3 | **reach**: `setupᵇ` compares only rated homs, so the *unmoved* compared homs (`g`, `u`, `h`) now need *some* certificate. `Family` never asks for one. The rate is irrelevant by `generic⇔ctx`, but a certificate must exist. Without that, a two-sorted setup is needed: an uncertified `𝒟 ⊇ 𝒞` acting by plain maps on the test carriers. | structural | not built, est. +60–100 lines |
| M4 | the schedule side conditions (`PreBound`/`PostBound`) | lemma (ring identity) | discharged, exact |
| M5 | family = levelwise glue (§4) | lemma | not built, ~20 lines |

No `scale`/`·` arithmetic is missing. Every substitution is exact (`ℚₚ.≤-reflexive ∘ cong`).

## 6. What `Quantitative/Family` could delete

Line counts are non-blank lines on `3034aa9c`. The file has 514 non-blank lines (600 total).

| names | lines | replaced by |
|---|---|---|
| `ctx-cong`, `≈ctx-resp`, `≈C⇒≈ctx`, `≈ctx-refl/-sym/-trans/-≤` | 23 | generic kit |
| `≈ctx⇒≈ctxᴬ`, `≈ctxᴬ⇒≈ctx` (rebracketing) | 18 | `generic⇔ctx` |
| `≈ctx-sub` | 8 | `ctx-sub` |
| `≤UC^ωᵉ⇒⁺`, `≤UC^ωᵉ⁺⇒` | 21 | generic dummy/universal (not built, ~15) |
| `seqError`, `≤UC[]-trans` | 19 | `at-trans` |
| `≈ctx-ext`, `≈ctx-pre` | 41 | `ctx-ext`, `ctx-pre` |
| `≤UC[]-compose`, `≤UC[]-compose′` (incl. `strict-final`) | 54 | `at-compose` |
| `composeSim` | 9 | composition in `𝒞ᵇᴹ` |
| **subtotal** | **193** | |
| `≈ctx-dom`, `≤UC[]-dom` | 33 | kept (would need one more generic `PostBound` lemma) |

`Contextual.agda`'s kit, lines 107–216 (99 non-blank: `ctx-*`, `absorb-testᵠ`,
`absorb-closureᵠ`, `ctx-absorb`, `ctx-sub`, `at-trans`), is also superseded; about 80 of
those lines go.

The cost side is FilteredSetup (+168) plus `𝒞ᵇᴹ` (+35), plus lift/unlift glue for each
retained `Family` theorem (+~40), plus the level glue (+~20). **Net is about −10 to +30
lines, roughly zero.** §2.1's estimate of "~1–2k LOC" is off by an order of magnitude:
the whole parallel ε-theory is about 300 lines, and the generic replacement costs about
the same.

## 7. Go / no-go

- **No-go** for the brief's form. An `Approx`-valued `QUCSetup` cannot have
  `_≈ctx[_]_` as its `_≈ᵁ[_]_`: this is proved (§2), and an exact instance would prove
  the unscaled schedules.
- **Conditional go** for the Filt-valued generalisation, but only if the goal is one
  composition theory whose error formulas are *outputs* of filtered maps, and not
  deleting lines. It is conditional on M3: either every compared machine has some
  certificate, or a two-sorted setup is built.
- **Estimate for the real change:**
  - promote `FilteredSetup` to `UC.Quantitative.Filtered`;
  - move `𝒞ᵇᴹ` into `Query`;
  - re-derive `Family.Compose` and the `Contextual` kit from them, with glue;
  - retire the duplicated proofs.

  That is 1–2 sessions, with net LOC about 0. M3 as a two-sorted setup adds one more
  session.
