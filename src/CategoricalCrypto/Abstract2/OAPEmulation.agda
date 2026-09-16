{-# OPTIONS --safe --without-K #-}

-- UC emulation stated directly on OAP-homs: `_≤UCᴼ_` is Abstract's `_≤UC_`
-- with an arbitrary OAP-hom in place of `ι f`.  On OP-homs the two relations
-- are the same Set (`≤UC≡≤UCᴼ` holds by `refl`), so OP is not needed to
-- *state* emulation, and the metatheorems that never invert an interface
-- (refl, dummy-complete, trans) generalize verbatim.  UC-compose does not:
-- Abstract's proof slides an attack across an OP-hom via `pureAtk-transport`,
-- which inverts the hom's interface part (Coh(ℐ) is a groupoid); an arbitrary
-- OAP-hom's interface part is not invertible, so the transport step — and
-- with it the composition theorem — is exactly where OP earns its existence.

open import Level

import CategoricalCrypto.Abstract as Abstract
open import CategoricalCrypto.UCSetup

module CategoricalCrypto.Abstract2.OAPEmulation
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  where

open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as SetoidR

open Abstract.AbstractUC setup

private variable
  A B : 𝒞.Obj
  X X′ X″ Y Y′ Y″ : ℐ.Obj
  I I′ J K : ℂ.Obj

infix 4 _≤UCᴼ_

_≤UCᴼ_ : ⟨ A , X ⟩ ⇒ᴼ ⟨ B , Y ⟩ → ⟨ A , X′ ⟩ ⇒ᴼ ⟨ B , Y′ ⟩ → Set (o ⊔ ℓ ⊔ cs ⊔ ℓs)
_≤UCᴼ_ {X = X} {Y = Y} {X′ = X′} {Y′ = Y′} x y =
  ∀ {D} (a : Y ℐ.⇒ D) → Σ[ s⁺ ∈ Y′ ℐ.⇒ D ] Σ[ s⁻ ∈ X ℐ.⇒ X′ ]
    pureAtk a OAP.∘ x ≈ℰ' pureAtk s⁺ OAP.∘ y OAP.∘ pureAtk s⁻

------------------------------------------------------------------------
-- Restriction to OP: `_≤UC_` is `_≤UCᴼ_` at `ι`, definitionally
------------------------------------------------------------------------

≤UC≡≤UCᴼ : {f : ⟨ A , I ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , J ⟩ᴼᴾ} {g : ⟨ A , I′ ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , K ⟩ᴼᴾ}
         → (f ≤UC g) ≡ (ι f ≤UCᴼ ι g)
≤UC≡≤UCᴼ = refl

op⇒oap : {f : ⟨ A , I ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , J ⟩ᴼᴾ} {g : ⟨ A , I′ ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , K ⟩ᴼᴾ}
       → f ≤UC g → ι f ≤UCᴼ ι g
op⇒oap h = h

oap⇒op : {f : ⟨ A , I ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , J ⟩ᴼᴾ} {g : ⟨ A , I′ ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , K ⟩ᴼᴾ}
       → ι f ≤UCᴼ ι g → f ≤UC g
oap⇒op h = h

------------------------------------------------------------------------
-- The transport-free metatheorems, at OAP level
------------------------------------------------------------------------

≤UCᴼ-refl : {x : ⟨ A , X ⟩ ⇒ᴼ ⟨ B , Y ⟩} → x ≤UCᴼ x
≤UCᴼ-refl {x = x} w = w , ℐ.id , ≈'-congˡ (pureAtk w) (≈'-sym (atk-idʳ x))

-- Completeness of the dummy adversary.
dummy-completeᴼ : {x : ⟨ A , X ⟩ ⇒ᴼ ⟨ B , Y ⟩} {y : ⟨ A , X′ ⟩ ⇒ᴼ ⟨ B , Y′ ⟩}
                → Σ[ s ∈ Y′ ℐ.⇒ Y ] Σ[ u ∈ X ℐ.⇒ X′ ]
                    (x ≈ℰ' pureAtk s OAP.∘ y OAP.∘ pureAtk u)
                → x ≤UCᴼ y
dummy-completeᴼ {x = x} {y = y} (s , u , e) w = (w ℐ.∘ s) , u , (begin
    pureAtk w OAP.∘ x                                    ≈⟨ ≈'-congˡ (pureAtk w) e ⟩
    pureAtk w OAP.∘ pureAtk s OAP.∘ y OAP.∘ pureAtk u    ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟨
    (pureAtk w OAP.∘ pureAtk s) OAP.∘ y OAP.∘ pureAtk u  ≈⟨ ≈'-congʳ (y OAP.∘ pureAtk u) (pureAtk-∘ w s) ⟩
    pureAtk (w ℐ.∘ s) OAP.∘ y OAP.∘ pureAtk u            ∎)
  where open SetoidR (≈'-setoid _ _)

≤UCᴼ-trans : {x : ⟨ A , X ⟩ ⇒ᴼ ⟨ B , Y ⟩} {y : ⟨ A , X′ ⟩ ⇒ᴼ ⟨ B , Y′ ⟩}
             {z : ⟨ A , X″ ⟩ ⇒ᴼ ⟨ B , Y″ ⟩}
           → x ≤UCᴼ y → y ≤UCᴼ z → x ≤UCᴼ z
≤UCᴼ-trans {x = x} {y = y} {z = z} x≤y y≤z w =
  let (s₁ , u₁ , e₁) = x≤y w
      (s₂ , u₂ , e₂) = y≤z s₁
      open SetoidR (≈'-setoid _ _)
  in s₂ , (u₂ ℐ.∘ u₁) , (begin
    pureAtk w OAP.∘ x                                       ≈⟨ e₁ ⟩
    pureAtk s₁ OAP.∘ y OAP.∘ pureAtk u₁                     ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟨
    (pureAtk s₁ OAP.∘ y) OAP.∘ pureAtk u₁                   ≈⟨ ≈'-congʳ (pureAtk u₁) e₂ ⟩
    (pureAtk s₂ OAP.∘ z OAP.∘ pureAtk u₂) OAP.∘ pureAtk u₁  ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟩
    pureAtk s₂ OAP.∘ (z OAP.∘ pureAtk u₂) OAP.∘ pureAtk u₁  ≈⟨ ≈'-congˡ (pureAtk s₂) (≋⇒≈ℰ' OAP.assoc) ⟩
    pureAtk s₂ OAP.∘ z OAP.∘ pureAtk u₂ OAP.∘ pureAtk u₁    ≈⟨ ≈'-congˡ (pureAtk s₂) (≈'-congˡ z (pureAtk-∘ u₂ u₁)) ⟩
    pureAtk s₂ OAP.∘ z OAP.∘ pureAtk (u₂ ℐ.∘ u₁)            ∎)
