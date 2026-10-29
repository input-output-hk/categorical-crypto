{-# OPTIONS --safe --without-K #-}

-- unflatten ∘ flatten holds only up to a coherence iso, not equality.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Base.Unflatten (sig : APROPSignature) where

open APROP sig

open FreeMonoidalHelper Symm X using (flatten)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal using (_⊗ᵢ_)
open import Categories.Morphism FreeMonoidal public using (_≅_; module ≅)

-- Sharing the generic definition keeps the APROP and SMC unflattens
-- definitionally equal.
open import Categories.PermuteCoherence.Unflatten asFreeMonoidalData public
  using (unflatten; unflatten-++-≅)

open Monoidal Monoidal-FreeMonoidal using (unitorʳ)

private variable
  a b c d : List X
  x : X

unflatten-flatten-≈ : ∀ (A : ObjTerm) → A ≅ unflatten (flatten A)
unflatten-flatten-≈ unit     = ≅.refl
unflatten-flatten-≈ (Var x)  = ≅.sym unitorʳ
unflatten-flatten-≈ (A ⊗₀ B) =
  ≅.trans (unflatten-flatten-≈ A ⊗ᵢ unflatten-flatten-≈ B)
          (≅.sym (unflatten-++-≅ (flatten A) (flatten B)))

bridge : ∀ {A B} → HomTerm A B → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
bridge {A} {B} f = _≅_.from (unflatten-flatten-≈ B) ∘ f ∘ _≅_.to (unflatten-flatten-≈ A)

--------------------------------------------------------------------------------
-- Transported identities
--------------------------------------------------------------------------------

subst-id-cod : c ≡ d → HomTerm (unflatten c) (unflatten d)
subst-id-cod {c} q = subst (λ z → HomTerm (unflatten c) (unflatten z)) q id

subst-id-cod-trans : (p : a ≡ b) (q : b ≡ c)
                   → subst-id-cod q ∘ subst-id-cod p ≈Term subst-id-cod (trans p q)
subst-id-cod-trans refl refl = idˡ

-- Crossing to the inverse proof costs no ≈Term step.
subst-id-dom : a ≡ b → HomTerm (unflatten b) (unflatten a)
subst-id-dom p = subst-id-cod (sym p)

-- Unlike the domain spelling, this direction needs sym (sym p) ≡ p.
cast-dc : (p : a ≡ b) → subst-id-dom (sym p) ≈Term subst-id-cod p
cast-dc refl = ≈-Term-refl

cast-cancel′ : (p : a ≡ b) → subst-id-dom p ∘ subst-id-cod p ≈Term id
cast-cancel′ refl = idˡ

cod-cancel : (p : a ≡ b) → subst-id-cod p ∘ subst-id-cod (sym p) ≈Term id
cod-cancel refl = idˡ

dom-cancel : (p : a ≡ b) → subst-id-dom (sym p) ∘ subst-id-dom p ≈Term id
dom-cancel refl = idˡ

subst-cod-cons
  : (e : a ≡ b)
  → id {Var x} ⊗₁ subst-id-cod e ≈Term subst-id-cod (cong (x ∷_) e)
subst-cod-cons refl = id⊗id≈id
