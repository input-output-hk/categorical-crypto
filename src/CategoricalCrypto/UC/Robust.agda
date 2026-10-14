{-# OPTIONS --safe --without-K #-}

-- `≤UC` is equivalent to robust hyperproperty preservation (see
-- `Universal Composability is Robust Compilation`). We don't have
-- traces in generic models, so what they call hyperproperties are
-- just regular properties for us. In models where morphisms are sets
-- of traces, this instantiates exactly to their hyperproperties.

open import categorical-crypto.Prelude using (PredS)
open import Data.Product
open import Function.Bundles

open import Level

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup

module CategoricalCrypto.UC.Robust
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level} (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open AbstractUC setup public

private variable
  A B : 𝒞.Obj
  X Y : ℐ.Obj
  p : Level
  f : A 𝒞.⇒ T₀ X B
  g : A 𝒞.⇒ T₀ Y B

------------------------------------------------------------------------
-- Robust properties
------------------------------------------------------------------------

Predᵁ : (A B : 𝒞.Obj) (p : Level) → Set (o ⊔ ℓ′ ⊔ cs ⊔ ℓs ⊔ suc p)
Predᵁ A B p = (X : ℐ.Obj) → PredS (≈ᵁ-setoid A B X) p

-- `Robust P f`: `f` robustly satisfies `P`
Robust : Predᵁ A B p → A 𝒞.⇒ T₀ X B → Set (o ⊔ ℓ ⊔ p)
Robust {X = X} P f = ∀ {X′} (a : X ℐ.⇒ X′) → P X′ ⟨$⟩ (sub a 𝒞.∘ f)

-- `Emu g` selects all morphisms that emulate `g`
Emu : A 𝒞.⇒ T₀ Y B → Predᵁ A B (o ⊔ ℓ ⊔ cs ⊔ ℓs)
Emu {Y = Y} g X′ = record
  { to = _≤UCᵈ g
  ; cong = λ u → mk⇔ (λ (s , v) → s , ≈ᵁ-trans (≈ᵁ-sym u) v) (λ (s , v) → s , ≈ᵁ-trans u v) }

RHP : ∀ {A B X Y} (f : A 𝒞.⇒ T₀ X B) (g : A 𝒞.⇒ T₀ Y B) → Set (suc o ⊔ suc ℓ ⊔ ℓ′ ⊔ suc cs ⊔ suc ℓs)
RHP f g = ∀ (P : Predᵁ _ _ (o ⊔ ℓ ⊔ cs ⊔ ℓs)) → Robust P f → Robust P g

uc-preserves : f ≤UC g → RHP g f
uc-preserves uc P rob a = let s , u = uc a in Equivalence.from (Func.cong (P _) u) (rob s)

robust⇒≤UC : RHP g f → f ≤UC g
robust⇒≤UC {g = g} rhp = rhp (Emu g) (≤UC-refl g)

≤UC⇔robust : f ≤UC g ⇔ RHP g f
≤UC⇔robust = mk⇔ uc-preserves robust⇒≤UC
