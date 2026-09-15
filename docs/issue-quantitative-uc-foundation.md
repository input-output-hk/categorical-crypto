# Build quantitative UC from an Approx-valued presheaf

## Summary

Define a small category of approximate spaces and use an `Approx`-valued presheaf to build a generic quantitative UC theory. Recover ordinary `UCSetup` instances through forgetful functors.

This issue covers the resource-independent foundation and its unrestricted machine instance. Query-sensitive bounds and migration are covered by [the dependent resource-aware issue](issue-quantitative-uc-resources-and-migration.md).

## Background

The existing development has several separately presented UC relations. The goal is one qualitative metatheory, inherited from `Abstract2`, and a quantitative extension whose laws follow from categorical structure rather than additional UC axioms.

The design is specified in [the quantitative UC plan](quantitative-uc-setup-plan.typ), sections 1–6. Its source references were reviewed at `protocol-rewrite`, `92479a31`; recheck them against the implementation tip. The signatures below are schematic, not typechecked Agda.

## Scope

### Approximate spaces and nonexpansive maps

Start with rational nonnegative errors and reuse the existing `UC.Approximate.Approximation` relation and laws where possible.

```agda
record ApproxSpace : Set where
  field
    Carrier : Set
    _≈[_]_ : Carrier → ℚ≥0 → Carrier → Set
    refl  : x ≈[ 0 ] x
    sym   : x ≈[ ε ] y → y ≈[ ε ] x
    trans : x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε + δ ] z
    mono  : ε ≤ δ → x ≈[ ε ] y → x ≈[ δ ] y

record Nonexpansive (X Y : ApproxSpace) : Set where
  field
    map : X.Carrier → Y.Carrier
    preserves : X._≈[_]_ x ε y → Y._≈[_]_ (map x) ε (map y)

f ≈map g = ∀ x → Y._≈[_]_ (f.map x) 0 (g.map x)
```

Prove that ordinary identity and composition, with pointwise zero-error hom equality, form the category `Approx`. Derive respect of fixed error bounds under zero-error changes of endpoints; do not introduce a separate fine equality.

### Forgetful functors

Construct both functors to setoids:

```agda
x ∼₀ y = x ≈[ 0 ] y
x ∼₊ y = ∀ ε → 0 < ε → x ≈[ ε ] y

F₀ F₊ : Functor Approx Setoids
```

Prove the all-positive equivalence using rational halving, functoriality, and the identity-on-carriers natural transformation `F₀ ⇒ F₊`.

Do not impose closedness of error balls. The existing finite-stage comparison can distinguish immediate return from an almost-sure geometric return at zero error, while all-positive comparison identifies them. Exact quantitative bounds must not be required to respect the coarser `F₊` equality.

### Quantitative setup and metatheory

```agda
record QUCSetup : Set where
  field
    C : Category
    I : MonoidalCategory
    M : GradedKleisliTriple I C
    Q : Functor (op C) Approx

underlying₀ S = setup S.C S.I S.M (F₀ ∘F S.Q)
underlying₊ S = setup S.C S.I S.M (F₊ ∘F S.Q)

prefix W f = μ W X ∘ T₁ W f
run W f e = Nonexpansive.map (Q.₁ (prefix W f)) e

f ≈ᵁ[ ε ] g =
  ∀ W (e : Env (T₀ (W ⊗₀ X) B)) →
    run W f e ≈[ ε ] run W g e

At s ε f g = f ≈ᵁ[ ε ] (sub s ∘ g)
Witness ε f g = Σ[ s ∈ I [ Y , X ] ] At s ε f g
Witness⁺ ε f g = ∀ X′ (a : I [ X , X′ ]) →
                   Witness ε (sub a ∘ f) g
```

Derive the approximation laws for contextual comparison, ambient hom-equality transport, simulator absorption, and congruence in both arguments of graded composition. In this nonexpansive theory, those congruences preserve the error unchanged.

Prove dummy/universal equivalence and witness composition, including:

```agda
at-trans : At s ε f g → At t δ g h → At (s ∘I t) (ε + δ) f h

at-compose : At s εf f g → At t εu u v →
  At ((id_X ⊗₁ t) ∘I (s ⊗₁ id_R)) (εu + εf) (u ∙ f) (v ∙ g)
```

Here `s : Y → X`, `t : R → P`, and the compared composites have grades `X ⊗ P` and `Y ⊗ R` respectively. These are theorems derived from the presheaf and graded structure, not fields of `QUCSetup`.

Establish the precise links to inherited UC:

```agda
(f ≤UC₀ g) ↔ Witness 0 f g
(f ≤UC₊ g) ↔ Σ[ s ∈ I [ Y , X ] ]
                (∀ ε → 0 < ε → At s ε f g)
```

The second statement retains one simulator for every positive error; it must not become `∀ ε > 0. Witness ε f g`.

### Unrestricted machine instance

Construct the test presheaf from an observation approximation space `O` and a map:

```agda
Obs : C [ K , Ω ] → O.Carrier
obs-resp₀ : p ≈C q → Obs p ≈O[ 0 ] Obs q

E ≈[ ε ] F = ∀ (m : K → A) → Obs (E ∘ m) ≈O[ ε ] Obs (F ∘ m)
Q.₁ h E = E ∘ h
```

All closures are admitted. Prove nonexpansiveness and identify the `F₊` image with the current qualitative machine test presheaf. This instance is not the old budget-restricted `_≈ctx[_]_`.

## Acceptance Criteria

- [ ] `Approx`, its hom equality, and its category laws are implemented without new postulates.
- [ ] `F₀`, `F₊`, and their comparison natural transformation are proved.
- [ ] A checked example distinguishes zero-error from all-positive-error equality.
- [ ] `QUCSetup` contains the computational structure and an approximate-space-valued presheaf, not separate certificate/resource records.
- [ ] Contextual comparison retains the full prefix-grade quantification of `Abstract2._≈ᵁ_`.
- [ ] Approximation, absorption, dummy/universal, transitivity, and graded composition results are derived generically.
- [ ] Both ordinary setup instances and the fixed-simulator equivalences above are proved.
- [ ] The unrestricted machine instance is constructed and connected to the existing qualitative setup.
- [ ] New modules and affected consumers typecheck with the shared Agda toolchain; significant elaboration regressions are recorded.

## Reuse and Non-Goals

Reuse `UC.Approximate`, `UC.Environment.Presheaf`, `UC.Model.Observation.obs-resp`, `Abstract2`, and `Abstract2.Action`. Place approximate-space categories and forgetful functors in general-purpose modules; reserve `UC.Quantitative` for the setup and UC-specific theory.

Do not change `Obs`, introduce another experiment category, assume `C = I`, require `GradeStable`, or reconstruct machine trace laws. Do not retire budget-sensitive APIs in this issue or claim their errors remain unchanged under composition.
