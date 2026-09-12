{-# OPTIONS --safe --without-K --guardedness #-}

-- The operational reading of the inherited `_≈ᵁ_` (proposal §2).  For
-- `f, g : A → X ⊗ B` it says
--
--     ∀ Y, e : Y ⊗ (X ⊗ B) → Ω, m : 𝟘 → Y ⊗ A.
--       Obs (e ∘ (id ⊗ f) ∘ m) = Obs (e ∘ (id ⊗ g) ∘ m)
--
-- and that is a THEOREM, not a second definition: the defining prefix
-- `μ Y X ∘ T₁ Y f` is `α⇐ ∘ id ⊗₁ f` (`CurriedTensor.Properties.μT₁-α⇐`), so it
-- merely re-brackets the test's domain, and the two quantifications over tests
-- correspond under `α⇒`/`α⇐`.  Hence the ancillas of the graded context closure
-- ARE the ancillas of the displayed experiment, and `ℰ`'s bare kernel need not
-- already be stable under them — no `GradeStable`, and no claim that `_≈ᵁ_`
-- agrees with every presentation in `Abstract`.
--
-- The reasoning is spelled with the unqualified `MonoidalCategory` vocabulary
-- `StdUC` re-exports; `open 𝒞` in addition makes every `_∘_` an ambiguous
-- overloaded projection.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (μT₁-α⇐)

open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (0ℓ; suc)

open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)
open import CategoricalCrypto.UC.Model.Setup

module CategoricalCrypto.UC.Model.Reading where

open HomReasoning
open import Categories.Morphism.Reasoning ∣machines∣ using (cancelInner)

private variable A B X : Channel

infix 4 _≈ᴬ_

-- Quantified over an ancilla, a test on it and a closure of the pair.
_≈ᴬ_ : (f g : A ⇒ T₀ X B) → Set (suc 0ℓ)
_≈ᴬ_ {A} {X} {B} f g = (Y : Channel) (e : Test (Y ⊗₀ X ⊗₀ B))
                       (m : Closure (Y ⊗₀ A))
                     → Obs (e ∘ id ⊗₁ f ∘ m) ∼ᴼ Obs (e ∘ id ⊗₁ g ∘ m)

-- The bracketing shuffle, in the two orientations the equivalence needs.  Also
-- what carries a robustness statement between the two bracketings
-- (`UC.Robust.Model`), so it is not private.
shuffle⇒ : {Y : Channel} (f : A ⇒ T₀ X B) (e : Test (Y ⊗₀ X ⊗₀ B))
           (m : Closure (Y ⊗₀ A))
         → ((e ∘ α⇒) ∘ μ Y X ∘ T₁ Y f) ∘ m ≈ e ∘ id ⊗₁ f ∘ m
shuffle⇒ {Y = Y} f e m = begin
    ((e ∘ α⇒) ∘ μ Y _ ∘ T₁ Y f) ∘ m  ≈⟨ (refl⟩∘⟨ μT₁-α⇐ 𝔾ᵒ Y f) ⟩∘⟨refl ⟩
    ((e ∘ α⇒) ∘ α⇐ ∘ id ⊗₁ f) ∘ m    ≈⟨ cancelInner associator.isoʳ ⟩∘⟨refl ⟩
    (e ∘ id ⊗₁ f) ∘ m                ≈⟨ assoc ⟩
    e ∘ id ⊗₁ f ∘ m                  ∎

shuffle⇐ : {Y : Channel} (f : A ⇒ T₀ X B) (e : Test ((Y ⊗₀ X) ⊗₀ B))
           (m : Closure (Y ⊗₀ A))
         → (e ∘ μ Y X ∘ T₁ Y f) ∘ m ≈ (e ∘ α⇐) ∘ id ⊗₁ f ∘ m
shuffle⇐ {Y = Y} f e m = begin
    (e ∘ μ Y _ ∘ T₁ Y f) ∘ m  ≈⟨ (refl⟩∘⟨ μT₁-α⇐ 𝔾ᵒ Y f) ⟩∘⟨refl ⟩
    (e ∘ α⇐ ∘ id ⊗₁ f) ∘ m    ≈⟨ sym-assoc ⟩∘⟨refl ⟩
    ((e ∘ α⇐) ∘ id ⊗₁ f) ∘ m  ≈⟨ assoc ⟩
    (e ∘ α⇐) ∘ id ⊗₁ f ∘ m    ∎

≈ᵁ⇒≈ᴬ : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ᴬ g
≈ᵁ⇒≈ᴬ {f = f} {g} u Y e m =
  ∼ᴼ-resp (obs-resp (shuffle⇒ f e m)) (obs-resp (shuffle⇒ g e m))
          (KE.run∼ (u Y) {e ∘ α⇒} m)

≈ᴬ⇒≈ᵁ : {f g : A ⇒ T₀ X B} → f ≈ᴬ g → f ≈ᵁ g
≈ᴬ⇒≈ᵁ {f = f} {g} r Y = KE.mk∼ λ {e} m →
  ∼ᴼ-resp (obs-resp (⟺ (shuffle⇐ f e m))) (obs-resp (⟺ (shuffle⇐ g e m)))
          (r Y (e ∘ α⇐) m)

≈ᵁ⇔≈ᴬ : {f g : A ⇒ T₀ X B} → f ≈ᵁ g ⇔ f ≈ᴬ g
≈ᵁ⇔≈ᴬ {f = f} {g} = mk⇔ {B = f ≈ᴬ g} ≈ᵁ⇒≈ᴬ ≈ᴬ⇒≈ᵁ
