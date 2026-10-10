# Nondeterministic choice: the scheduler in the grade

Plan, 2026-10-10; replaces the 2026-10-09 plan of the same name (image equality over `Sched → Dist⊥ Bool`,
in git history at `7d722e1f`).  Nothing here is typechecked.  Every claim about a module that does not
exist is a design claim; `[INFERENCE]` marks what was reasoned and not checked.  Line references are to
`uc-setup-landscape` at `cf7c0db0`.  Names are those of `docs/uc-models.typ` (PM, SSP, PM[wb], 𝒲, SSPᵈ,
ND_A, ND_B; §4 there, `sec:nd`, is the mathematical statement this plan implements).

## 0. Summary

(outline; filled below)

## 1. The generic construction: restriction along a monoidal functor of grades

### 1.1 The restricted setup

For a setup 𝕊 = (𝒞, ℐ, ℳ, ℰ) and a lax monoidal functor ι : 𝒥 → ℐ (structure ι_ε : I → ιI,
ι₂ : ιW ⊗ ιX → ι(W ⊗ X)), the **restriction of 𝕊 along ι** is

  𝕊|ι := (𝒞, 𝒥, ℳ ∘ ι, ℰ),

with the graded monad pulled back (`Categories/Monad/Graded/Pullback.agda:32`, `pullbackM = ∘-Monoidal ℳ ι`):
T′_X = T_{ιX}, sub′_c = sub_{ιc}, η′ = sub_{ι_ε} ∘ η, μ′_{W,X} = sub_{ι₂} ∘ μ_{ιW,ιX}.  Computations, tests
and the kernel ≈ℰ are 𝕊's; a protocol of 𝕊|ι at grade X *is* a protocol of 𝕊 at grade ιX.  Only the
adversaries, the simulators and the ancillas are cut down to ι's image.

The standard case is `Std(𝕄, ℰ)|ι` for ι : 𝕄′ → 𝕄: 𝒞 = |𝕄|, ℐ = 𝕄′, T′_X B = ιX ⊗ B, an adversary
a ∈ 𝕄′(X, X′) acts as ιa ⊗ id, and μ′ = (ι₂ ⊗ id) ∘ α⁻¹.  Typical ι: the inclusion of a monoidal
subcategory of grades, not necessarily full (ND_A; efficient simulators) nor wide (the adversary-free
setup of §1.3(e)), or a functor that names structure on grades (ND_B's designated choice factors, §2.2).

### 1.2 The inclusion morphism

`inclusion : UCSetupMorphism (𝕊|ι) 𝕊` is (F = Id, Φ = ι, κ = id, ν = `idᵛ ℰ`).  Its κ-laws are the
pullback's defining equations: κ-sub and κ-return are `pullback-sub`/`pullback-return` (`refl`,
`Pullback.agda:46-50`), κ-ext is `pullback-ext` (`:52`).  The action on protocols is G f = id ∘ f ≈ f, and
ν is Epi and Mono (`Categories/Functor/Presheaf/Morphism.agda:155-159`).

### 1.3 Theorem: what the inclusion preserves and reflects

Let f : A → T_{ιX} B and g : A → T_{ιY} B be protocols of 𝕊|ι; ≈ᵁ|ι and ≤UC|ι are 𝕊|ι's relations.

- **(a) ≈ᵁ ⊆ ≈ᵁ|ι, always.**  𝕊|ι quantifies over the ancillas ιW only, and μ′ = sub_{ι₂} ∘ μ only
  post-composes, which ≈ℰ respects (`≈ℰ-cong-post`).
- **(b) ≈ᵁ|ι ⊆ ≈ᵁ when ι is essentially surjective with split comparisons** (every ι₂ has a retraction;
  a strong ι supplies `⊗-homo.⇐`).  Cancel sub_{ι₂} by sub of the retraction, then move the ancilla
  along φ : ιW′ ≅ W:  prefix_W f = sub_{φ ⊗ id} ∘ prefix_{ιW′} f ∘ sub_{φ⁻¹}, by `sub-commute′` and
  `μ-sub-commute` (`FromMonad.agda:87-91`).  The curried-tensor instance of this conjugation is
  `Standard2/Morphism.agda:82` `conj`, used by `surjective⇒preserves-≈ᵁ` (`:97`).  "W a retract of some
  ιW′" suffices (the same computation with r ∘ s = id).  Under (b) the U-kernels coincide on 𝕊|ι's
  protocols; when ι is bijective on objects and strict (a wide monoidal subcategory) they are literally
  one relation, with no conjugation.
- **(c) Preservation under (b).**  f ≤UC|ι g ⇒ f ≤UC g: the dummy simulator s₀ ∈ 𝒥(Y, X) of the
  hypothesis gives f ≈ᵁ sub_{ιs₀} ∘ g by (b), and `dummy-complete` (`Abstract2.agda:156`) gives the
  simulator a ∘ ιs₀ for each a : ιX → X″.  No `GradeStable`, no Epi.
- **(d) Preservation for every ι when 𝕊 is grade-stable.**  𝕊|ι is then grade-stable (T′_Y = T_{ιY}), and
  f ≈ᵁ|ι g ⇒ f ≈ℰ g ⇒ f ≈ᵁ g by `bridge` (`Abstract2.agda:124`).  This is
  `Transfer.transfer inclusion idᵛ-epi gs` (`Abstract2/Morphism.agda:75`), the route the causal-boxes
  sketch takes.
- **(e) Without (b) or (d) preservation fails.**  Take ι : `Oneᴹ` → ℐ, the unit (`Oneᴹ` is
  `Categories/Monad/Graded/Trivial.agda:24`).  𝕊|ι is the adversary-free setup: one ancilla and one
  simulator, so ≈ᵁ|ι and ≤UC|ι are ≈ℰ on unit-graded protocols.  At PM the reveal pair
  r_true ≈ℰ r_false (`UC/RandomSystems/FullAbstraction.agda:186`) is ≤UC|ι, while r_true ≰UC r_false: a
  simulator I → I has the empty interface, so sub_s ∘ r_false still never sends `true`, and ≈ᵁ ⇒ ≈ᴿ
  separates the two [INFERENCE: that every s : I → I of 𝔾ᵒ is inert].
- **(f) Reflection when ι is full.**  f ≤UC g ⇒ f ≤UC|ι g: take 𝕊's dummy simulator s₀ ∈ ℐ(ιY, ιX), a
  preimage s₀′ with ιs₀′ ≈ s₀, and (a).  No grade stability, κ-mono or ν-mono:
  `Abstract2/Morphism.agda:90` `reflects-≤UC` needs all three because it rebuilds the source U-kernel
  from a ≈ℰ; here (a) gives it directly.
- **(g) Without fullness reflection fails**; ND_A → ND_B is the witness (§4).

So a full, essentially surjective, strong ι changes nothing about ≤UC (ND_B, §2.2); a wide strict non-full
ι preserves and does not reflect (ND_A ⊆ ND_B; efficient simulators); a non-essentially-surjective ι
coarsens ≈ᵁ, and preservation then needs grade stability.

### 1.4 Between two restrictions

For a second ι′ : 𝒥′ → ℐ, a monoidal j : 𝒥 → 𝒥′ and a monoidal natural iso θ : ι′ ∘ j ≅ ι
(`Categories.NaturalTransformation.NaturalIsomorphism.Monoidal`), `between j θ : 𝕊|ι → 𝕊|ι′` is
(Id, j, sub_{θ⁻¹}, `idᵛ ℰ`); its κ-laws are `pullback-∘-return`/`pullback-∘-ext` (`Pullback.agda:90-99`)
plus θ's monoidality.  The theorem carries over with "essential image of ι" in place of "all of ℐ":
the U-kernels agree when ι and ι′ have the same essential image on objects (split comparisons), and
full j reflects.  §4 needs it once, for the way back B → A.

### 1.5 The module

`src/CategoricalCrypto/Abstract2/Regrade.agda`, beside its dual `Abstract2/WideSubcategory.agda`.  It is
generic in the `UCSetup`, not in `Standard2`: ND_A restricts the non-standard ND_B, and the curried
tensor buys nothing (b) needs.  No `Standard2/Regrade.agda`: `Std(𝕄,ℰ)|ι` is the instance
`regraded (StdUC.StdSetup 𝕄 ℰ) ι`.

```agda
{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Abstract2.Regrade
  {o ℓ e o′ ℓ′ e′ cs ℓs oⱼ ℓⱼ eⱼ : Level} (𝕊 : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ} (ι : MonoidalFunctor 𝒥 (UCSetup.ℐ 𝕊)) where
open AbstractUC 𝕊
ι₂ : (W X : 𝒥.Obj) → ι.₀ W ⊗₀ ι.₀ X ℐ.⇒ ι.₀ (W 𝒥.⊗₀ X) ;  ι₂ W X = ι.⊗-homo.η (W , X)

regraded : UCSetup oⱼ ℓⱼ eⱼ o′ ℓ′ e′ cs ℓs                                 -- 𝕊|ι
regraded = record { 𝒞 = 𝒞 ; ℐ = 𝒥 ; ℳ = pullbackM ι ℳ ; ℰ = ℰ }
module R = AbstractUC regraded       -- R.T₀ X = T₀ (ι.₀ X), R.sub c = sub (ι.₁ c): refl

inclusion : UCSetupMorphism regraded 𝕊
inclusion = record { ν = idᵛ ℰ ; effect = record { F = idF ; Φ = ι ; κ = 𝒞.id
  ; isGradedKleisliMorphism = record { κ-return = 𝒞.identityˡ ; κ-sub = λ _ → id-comm-sym
                                     ; κ-ext = λ f → 𝒞.identityˡ ○ pullback-ext ι triple f ○ … } } }

≈ᵁ⇒≈ᵁ|ι : {f g : A 𝒞.⇒ T₀ (ι.₀ X) B} → f ≈ᵁ g → f R.≈ᵁ g                       -- (a)
≈ᵁ⇒≈ᵁ|ι e W = ≈ℰ-cong-post (sub (ι₂ W _)) (e (ι.₀ W))                            -- up to R.μ's spelling

restrict-≤UC : Full ι.F → f ≤UC g → f R.≤UC g                                    -- (f)
restrict-≤UC full f≤g = let s₀ , e = ≤UC⇒dummy f≤g ; s₀′ , s≈ = full s₀
                        in R.dummy-complete (s₀′ , ≈ᵁ⇒≈ᵁ|ι (≈ᵁ-trans e (≈C⇒≈ᵁ (sub-resp-≈ (ℐ.Equiv.sym s≈) ⟩∘⟨refl))))

module Preserves (r : ∀ {W X} → ι.₀ (W 𝒥.⊗₀ X) ℐ.⇒ ι.₀ W ⊗₀ ι.₀ X) (r∘ι₂ : ∀ {W X} → r ℐ.∘ ι₂ W X ℐ.≈ ℐ.id)
                 (surj : EssentiallySurjective ι.F) where                         -- (b), (c)
  ≈ᵁ|ι⇒≈ᵁ : f R.≈ᵁ g → f ≈ᵁ g
  ≈ᵁ|ι⇒≈ᵁ e W = let W′ , φ = surj W in conjugate φ (cancel r∘ι₂ (e W′))
  unrestrict-≤UC : f R.≤UC g → f ≤UC g
  unrestrict-≤UC le = let s₀ , e = R.≤UC⇒dummy le in dummy-complete (ι.₁ s₀ , ≈ᵁ|ι⇒≈ᵁ e)

regraded-gs : GradeStable → R.GradeStable                                       -- (d)
regraded-gs gs Y = gs (ι.₀ Y)
unrestrict-≤UC-gs : GradeStable → f R.≤UC g → f ≤UC g                           -- Transfer.transfer, G f = 𝒞.id ∘ f

module Between (ι′ : MonoidalFunctor 𝒥′ ℐ) (j : MonoidalFunctor 𝒥 𝒥′)
               (θ : MonoidalNaturalIsomorphism (∘-Monoidal ι′ j) ι) where      -- §1.4
  between : UCSetupMorphism regraded (Regrade.regraded 𝕊 ι′)                    -- κ = sub (θ.⇐.η _)

module Trivial where                                                             -- acceptance, §6
  open Preserves ℐ.id ℐ.identity² (λ W → W , ≅.refl)    -- at ι = idF-Monoidal ℐ
  to = restrict-≤UC (λ s → s , ℐ.Equiv.refl) ; from = unrestrict-≤UC
```

`cancel` (post-compose sub r, `sub-homomorphism`, `sub-identity`) and `conjugate` (the identity of (b))
are private.  The `refl`s of `R.T₀`/`R.sub`/`R.return` must survive `FromMonad`'s `triple`: the
causal-boxes plan flags it, and `pullback-*` are stated on `GradedMonad⇒GradedKleisliTriple`, which is
what `UCSetup.triple` is (`FromMonad.agda:36-37`).

### 1.6 Relation to `WideSubcategory`, causal boxes' `regrade`, `Oneᴹ`

| | `Abstract2/WideSubcategory` (𝒞 side) | `Abstract2/Regrade` (ℐ side) |
|---|---|---|
| restricts | computations, to a wide 𝒲 ⊆ 𝒞 closed under `return`, `μ`, `T₁`, `sub` | grades, along any monoidal ι : 𝒥 → ℐ |
| keeps | ℐ; ℳ restricted; tests ℰ′ presented by ν : ℰ′ ⇒ ℰ ∘ ιᵒᵖ | 𝒞 and ℰ; ℳ pulled back |
| inclusion | (ι, Id, id, ν) (`:118`) | (Id, ι, id, `idᵛ`) |
| has fewer | protocols | adversaries, simulators, ancillas |
| ≤UC preserved | `Preserves-≈ℰ` (`unrestrict-≤UC`, `:172`) | ι essentially surjective with split comparisons, or 𝕊 grade-stable |
| ≤UC reflected | `Reflects-≈ℰ` (`restrict-≤UC`, `:158`; free for `fine`) | ι full |
| trivial instance | `Trivial.everything` (`:192`) | ι = `idF-Monoidal ℐ` |

- **Causal boxes** (`docs/uc-setup-causal-boxes.md:417-433`): its `regrade`, planned in
  `UCSetup/Morphism.agda`, is `inclusion`; its "`Transfer.transfer` given target `GradeStable`" is
  (d), and (c) drops the hypothesis whenever ι is essentially surjective — its efficient-simulator
  grading keeps all grades, so (c) applies.  Its step 9 becomes an import of this module.
- **Regrade, then restrict computations.**  `WideSubcategory` over 𝕊|ι asks `W-sub` only at
  `sub (ι.₁ c)`.  The landscape's §3 correction (`W-sub` at every ambient adversary sinks "feasible
  machines") is lifted by first regrading to feasible adversaries.
- **`Oneᴹ`**: `Graded/Trivial.ungraded` reads a Kleisli triple as graded over `Oneᴹ`; restriction along
  the unit `Oneᴹ → ℐ` is (e)'s adversary-free setup, where UC emulation collapses to ≈ℰ.
- Only (b) and (c) use more than laxness of ι; the construction, (a), (d) and (f) are lax.


## 2. Choice factors and model B

## 3. Model A: relabellings only

## 4. The morphism A → B, and the way back

## 5. Laws of `choose`, `P ∥ Q`, SSPᵈ

## 6. Work breakdown

## 7. Sources
