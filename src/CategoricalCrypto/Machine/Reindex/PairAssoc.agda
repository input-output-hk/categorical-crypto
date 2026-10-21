{-# OPTIONS --safe #-}

-- ============================================================================
-- Reassociating a three-fold `Pair`, as `Machine.Monoidal.Associator` needs:
--
--     Pair M₁ (Pair M₂ M₃)  ≅ᴹ  Pair (Pair M₁ M₂) M₃   (up to relabelling)
--
-- `Tensor.CompRel` constructors are matched directly, for the reason given
-- beside `Pair` in `Machine.Reindex`.  Unlike `mid4ᵢ`/`mid4ₒ`, the maps
-- `asc3ᵢ`/`asc3ₒ` are not involutions (source and target trees have different
-- shapes), so the backward direction gets its own helper, and the two are tied
-- together by the round-trip laws.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex

open import categorical-crypto.Prelude hiding (id; _∘_)
import Data.Product.Base as ×
import Data.Sum.Base as ⊎
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

  asc3ᵢ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
        → inType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
        → inType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ (A₃ ⊗ᵀ B₃))
  asc3ᵢ = ⊎.assocˡ

  asc3ₒ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
        → outType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
        → outType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ (A₃ ⊗ᵀ B₃))
  asc3ₒ = ⊎.assocˡ

  asc3ᵢ⁻ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
         → inType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ (A₃ ⊗ᵀ B₃))
         → inType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
  asc3ᵢ⁻ = ⊎.assocʳ

  asc3ₒ⁻ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
         → outType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ (A₃ ⊗ᵀ B₃))
         → outType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
  asc3ₒ⁻ = ⊎.assocʳ

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
  asc3s = ×.assocˡ′

  asc3s⁻ : ∀ {S₁ S₂ S₃ : Type} → (S₁ × S₂) × S₃ → S₁ × (S₂ × S₃)
  asc3s⁻ = ×.assocʳ′

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
               (asc3ᵢ⁻-asc3ᵢ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} i)
               (mapᴹ-invol (asc3ₒ⁻-asc3ₒ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃}) o)
               (Pair-asc3-from M₁ M₂ M₃ p))
