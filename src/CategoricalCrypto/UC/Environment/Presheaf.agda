{-# OPTIONS --safe --without-K #-}

-- The environment presheaf an observation induces: tests into the verdict
-- object, modulo closed observation.
--
--     ℰ(A) = 𝒞(A , Ω) / ≋    E₁ ≋ E₂ ⟺ ∀ m : 𝟙 ⇒ A. ⟦ E₁ ∘ m ⟧ ∼ ⟦ E₂ ∘ m ⟧
--     ℰ(f)[E] = [E ∘ f]
--
-- `UCSetup` takes `ℰ` as GIVEN; an `Observation` is the datum one is built
-- from, and this is that construction — no ancilla in the carrier.  It is the
-- one row of the supersession inventory that runs from the core to the
-- inherited layer (`docs/stduc-supersession-plan.md` §2.3), so it is proved
-- once here rather than per instance: `UC.Environment` re-exports it,
-- `UC.Core.Bridge` is what feeds it to `StdUC`, and it is what an `ℰ` at the
-- levelwise family category will be (P6).
--
-- The parameter is the OBSERVATION alone: no tensor is spent, and at the
-- machine model none may be — a conversion that meets two monoidal bundles is
-- the configuration the seal exists to avoid (`UC.Model.Seal`'s header,
-- `UC.Model.Enrichment`).
--
-- Precomposition is well defined because a closure `m : 𝟙 ⇒ B` becomes the
-- closure `f ∘ m : 𝟙 ⇒ A`; associativity then gives all three presheaf laws,
-- and it is the only structure they need — each of the three is one `≈⇒≋`.

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Presheaf using (Presheaf)

open import Level using (_⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.UC.Core using (Observation)

module CategoricalCrypto.UC.Environment.Presheaf
  {o ℓ e os ℓs} (𝒞 : Category o ℓ e) (O : Observation 𝒞 os ℓs) where

open Category 𝒞
open Observation O

private variable A : Obj

Test : Obj → Set ℓ
Test A = A ⇒ Ω

Closure : Obj → Set ℓ
Closure A = 𝟙 ⇒ A

obs : Test A → Closure A → Obs
obs E m = ⟦ E ∘ m ⟧

infix 4 _≋_

_≋_ : Test A → Test A → Set (ℓ ⊔ ℓs)
_≋_ {A} E₁ E₂ = (m : Closure A) → obs E₁ m ∼ obs E₂ m

≋-isEquivalence : IsEquivalence (_≋_ {A})
≋-isEquivalence = record
  { refl  = λ _ → ∼-refl
  ; sym   = λ h m → ∼-sym (h m)
  ; trans = λ h k m → ∼-trans (h m) (k m)
  }

≈⇒≋ : {E₁ E₂ : Test A} → E₁ ≈ E₂ → E₁ ≋ E₂
≈⇒≋ eq _ = ⟦⟧-resp-≈ (∘-resp-≈ˡ eq)

ℰ₀ : Obj → Setoid ℓ (ℓ ⊔ ℓs)
ℰ₀ A = record { Carrier = Test A ; _≈_ = _≋_ ; isEquivalence = ≋-isEquivalence }

ℰᴼ : Presheaf 𝒞 (Setoids ℓ (ℓ ⊔ ℓs))
ℰᴼ = record
  { F₀           = ℰ₀
  ; F₁           = λ f → record
      { to = _∘ f ; cong = λ h m → ∼-cast sym-assoc sym-assoc (h (f ∘ m)) }
  ; identity     = ≈⇒≋ identityʳ
  ; homomorphism = ≈⇒≋ sym-assoc
  ; F-resp-≈     = λ eq → ≈⇒≋ (∘-resp-≈ʳ eq)
  }
