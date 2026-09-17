{-# OPTIONS --safe #-}

-- ============================================================================
-- Reassociating a three-fold `Pair`, as the monoidal associator needs:
--
--     Pair M₁ (Pair M₂ M₃)  ≅ᴹ  Pair (Pair M₁ M₂) M₃   (up to relabelling)
--
-- The proof is the same trick as `Pair-mid4`: `Pair` carries its step relation
-- at fully general indices, so `Tensor.CompRel` constructors can be matched
-- directly and every leaf step is simply re-tagged.  Unlike `mid4ᵢ`/`mid4ₒ`,
-- these maps are not involutions (source and target trees have different
-- shapes), so the backward direction gets its own matching helper, and the two
-- are tied together by the round-trip laws.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Message
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Reindex.PairAssoc where

open Channel

open _≅ᴹ_

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ

  -- ------------------------------------------------------------------------
  -- The leaves are re-tagged, the middle one moving from the right subtree to
  -- the left.
  -- ------------------------------------------------------------------------

  asc3ᵢ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
        → inType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
        → inType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ (A₃ ⊗ᵀ B₃))
  asc3ᵢ (inj₁ x)        = inj₁ (inj₁ x)
  asc3ᵢ (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
  asc3ᵢ (inj₂ (inj₂ z)) = inj₂ z

  asc3ₒ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
        → outType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
        → outType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ (A₃ ⊗ᵀ B₃))
  asc3ₒ (inj₁ x)        = inj₁ (inj₁ x)
  asc3ₒ (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
  asc3ₒ (inj₂ (inj₂ z)) = inj₂ z

  asc3ᵢ⁻ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
         → inType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ (A₃ ⊗ᵀ B₃))
         → inType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
  asc3ᵢ⁻ (inj₁ (inj₁ x)) = inj₁ x
  asc3ᵢ⁻ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  asc3ᵢ⁻ (inj₂ z)        = inj₂ (inj₂ z)

  asc3ₒ⁻ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
         → outType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ (A₃ ⊗ᵀ B₃))
         → outType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
  asc3ₒ⁻ (inj₁ (inj₁ x)) = inj₁ x
  asc3ₒ⁻ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  asc3ₒ⁻ (inj₂ z)        = inj₂ (inj₂ z)

  private
    asc3ᵢ⁻-asc3ᵢ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
                   (i : inType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃))))
                 → asc3ᵢ⁻ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃}
                     (asc3ᵢ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} i) ≡ i
    asc3ᵢ⁻-asc3ᵢ (inj₁ _)        = refl
    asc3ᵢ⁻-asc3ᵢ (inj₂ (inj₁ _)) = refl
    asc3ᵢ⁻-asc3ᵢ (inj₂ (inj₂ _)) = refl

    asc3ₒ⁻-asc3ₒ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
                   (o : outType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃))))
                 → asc3ₒ⁻ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃}
                     (asc3ₒ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} o) ≡ o
    asc3ₒ⁻-asc3ₒ (inj₁ _)        = refl
    asc3ₒ⁻-asc3ₒ (inj₂ (inj₁ _)) = refl
    asc3ₒ⁻-asc3ₒ (inj₂ (inj₂ _)) = refl

  asc3s : ∀ {S₁ S₂ S₃ : Type} → S₁ × (S₂ × S₃) → (S₁ × S₂) × S₃
  asc3s (s₁ , (s₂ , s₃)) = (s₁ , s₂) , s₃

  asc3s⁻ : ∀ {S₁ S₂ S₃ : Type} → (S₁ × S₂) × S₃ → S₁ × (S₂ × S₃)
  asc3s⁻ ((s₁ , s₂) , s₃) = s₁ , (s₂ , s₃)

  Pair-asc3-to : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
                 (M₁ : Machine A₁ B₁) (M₂ : Machine A₂ B₂) (M₃ : Machine A₃ B₃)
                 {s i o s'}
               → Tensor.CompRel M₁ (Pair M₂ M₃) s i o s'
               → Tensor.CompRel (Pair M₁ M₂) M₃
                   (asc3s s) (asc3ᵢ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} i)
                   (mapᴹ (asc3ₒ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃}) o) (asc3s s')
  Pair-asc3-to _ _ _ (Tensor.Step₁ {m' = just _}  q) = Tensor.Step₁ (Tensor.Step₁ q)
  Pair-asc3-to _ _ _ (Tensor.Step₁ {m' = nothing} q) = Tensor.Step₁ (Tensor.Step₁ q)
  Pair-asc3-to _ _ _ (Tensor.Step₂ (Tensor.Step₁ {m' = just _}  r)) = Tensor.Step₁ (Tensor.Step₂ r)
  Pair-asc3-to _ _ _ (Tensor.Step₂ (Tensor.Step₁ {m' = nothing} r)) = Tensor.Step₁ (Tensor.Step₂ r)
  Pair-asc3-to _ _ _ (Tensor.Step₂ (Tensor.Step₂ {m' = just _}  r)) = Tensor.Step₂ r
  Pair-asc3-to _ _ _ (Tensor.Step₂ (Tensor.Step₂ {m' = nothing} r)) = Tensor.Step₂ r

  Pair-asc3-from : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
                   (M₁ : Machine A₁ B₁) (M₂ : Machine A₂ B₂) (M₃ : Machine A₃ B₃)
                   {s i o s'}
                 → Tensor.CompRel (Pair M₁ M₂) M₃ s i o s'
                 → Tensor.CompRel M₁ (Pair M₂ M₃)
                     (asc3s⁻ s) (asc3ᵢ⁻ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} i)
                     (mapᴹ (asc3ₒ⁻ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃}) o) (asc3s⁻ s')
  Pair-asc3-from _ _ _ (Tensor.Step₁ (Tensor.Step₁ {m' = just _}  q)) = Tensor.Step₁ q
  Pair-asc3-from _ _ _ (Tensor.Step₁ (Tensor.Step₁ {m' = nothing} q)) = Tensor.Step₁ q
  Pair-asc3-from _ _ _ (Tensor.Step₁ (Tensor.Step₂ {m' = just _}  r)) = Tensor.Step₂ (Tensor.Step₁ r)
  Pair-asc3-from _ _ _ (Tensor.Step₁ (Tensor.Step₂ {m' = nothing} r)) = Tensor.Step₂ (Tensor.Step₁ r)
  Pair-asc3-from _ _ _ (Tensor.Step₂ {m' = just _}  r) = Tensor.Step₂ (Tensor.Step₂ r)
  Pair-asc3-from _ _ _ (Tensor.Step₂ {m' = nothing} r) = Tensor.Step₂ (Tensor.Step₂ r)

  Pair-asc3 : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
              (M₁ : Machine A₁ B₁) (M₂ : Machine A₂ B₂) (M₃ : Machine A₃ B₃)
            → Pair M₁ (Pair M₂ M₃) ≅ᴹ Reindex (Pair (Pair M₁ M₂) M₃) asc3ᵢ asc3ₒ
  Pair-asc3 {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} M₁ M₂ M₃ =
    MkIso asc3s asc3s⁻ (λ _ → refl) (λ _ → refl)
      (Pair-asc3-to M₁ M₂ M₃)
      (λ {_} {i} {o} p →
        subst₂ (λ x y → Tensor.CompRel M₁ (Pair M₂ M₃) _ x y _)
               (asc3ᵢ⁻-asc3ᵢ i)
               (trans (mapᴹ-∘ asc3ₒ⁻ asc3ₒ o)
                      (trans (mapᴹ-cong asc3ₒ⁻-asc3ₒ o) (mapᴹ-id o)))
               (Pair-asc3-from M₁ M₂ M₃ p))
