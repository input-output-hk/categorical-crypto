{-# OPTIONS --safe --without-K --guardedness #-}

-- The environment presheaf of the model (proposal §2): tests into the verdict
-- object, modulo closed observation.
--
--     ℰ(A) = 𝒜(A , Ω) / ≋      e ≋ e′  ⟺  ∀ m : 𝟘 → A. Obs (e ∘ m) ∼ Obs (e′ ∘ m)
--     ℰ(f)[e] = [e ∘ f]
--
-- No ancilla is part of the carrier, deliberately: the graded context closure of
-- `Abstract2` supplies the ancillary experiments, and its operational reading is
-- `UC.Model.Reading`.  This is what distinguishes the construction from
-- `VanishingTV.ℰᵗᵛ`, whose carrier is a dependent pair `(Y , test on Y ⊗ A)`.
--
-- Precomposition is well defined because a closure `m : 𝟘 → B` becomes the
-- closure `f ∘ m : 𝟘 → A`; associativity then gives the presheaf laws, and it is
-- the ONLY structure they need — every one of the three is one `≈ᵒ⇒≋`.

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Presheaf using (Presheaf)

open import Level using (0ℓ; suc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.Model.Environment where

private
  module G = MonoidalCategory 𝔾ᵒ
  module ∼ = IsEquivalence ∼ᴼ-isEquivalence

infix 4 _≋_

_≋_ : {X : G.Obj} → Test X → Test X → Set (suc 0ℓ)
_≋_ {X} e e′ = (m : Closure X) → Obs (e G.∘ m) ∼ᴼ Obs (e′ G.∘ m)

≋-isEquivalence : {X : G.Obj} → IsEquivalence (_≋_ {X})
≋-isEquivalence = record
  { refl  = λ _ → ∼.refl
  ; sym   = λ h m → ∼.sym (h m)
  ; trans = λ h k m → ∼.trans (h m) (k m)
  }

≈ᵒ⇒≋ : {X : G.Obj} {e e′ : Test X} → e G.≈ e′ → e ≋ e′
≈ᵒ⇒≋ eq m = ≈ₚ⇒∼ᴼ (obs-resp (G.∘-resp-≈ˡ eq))

ℰ₀ : G.Obj → Setoid (suc 0ℓ) (suc 0ℓ)
ℰ₀ X = record { Carrier = Test X ; _≈_ = _≋_ ; isEquivalence = ≋-isEquivalence }

ℰᵒ : Presheaf ∣𝔾ᵒ∣ (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᵒ = record
  { F₀           = ℰ₀
  ; F₁           = λ f → record
      { to   = λ e → e G.∘ f
      ; cong = λ h m → ∼ᴼ-resp (obs-resp G.sym-assoc) (obs-resp G.sym-assoc)
                               (h (f G.∘ m))
      }
  ; identity     = ≈ᵒ⇒≋ G.identityʳ
  ; homomorphism = ≈ᵒ⇒≋ G.sym-assoc
  ; F-resp-≈     = λ eq → ≈ᵒ⇒≋ (G.∘-resp-≈ʳ eq)
  }
