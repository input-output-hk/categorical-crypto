{-# OPTIONS --safe #-}

-- ============================================================================
-- Swapping the two components of a `Pair`.
--
-- The braiding's naturality needs the two-leaf cousin of `Pair-mid4`:
--
--     Pair M₁ M₂  ≅ᴹ  Pair M₂ M₁   (up to relabelling)
--
-- The proof is the same trick as there: `Pair` carries its step relation at
-- fully general indices, so `Tensor.CompRel` constructors can be matched
-- directly, and each leaf step is simply re-tagged from `Step₁` to `Step₂` and
-- back.  The relabelling `swᵢ`/`swₒ` is an involution, so the backward
-- direction is the forward one at the swapped machines, followed by the
-- involution law.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Reindex.Swap where

open _≅ᴹ_

private
  mapᴹ-∘ˢ : ∀ {X Y Z : Type} (v : Y → Z) (v' : X → Y) (o : Maybe X)
          → mapᴹ v (mapᴹ v' o) ≡ mapᴹ (λ x → v (v' x)) o
  mapᴹ-∘ˢ v v' (just x) = refl
  mapᴹ-∘ˢ v v' nothing  = refl

  mapᴹ-congˢ : ∀ {X Y : Type} {v v' : X → Y}
             → (∀ x → v x ≡ v' x) → ∀ o → mapᴹ v o ≡ mapᴹ v' o
  mapᴹ-congˢ e (just x) = cong just (e x)
  mapᴹ-congˢ e nothing  = refl

  mapᴹ-idˢ : ∀ {X : Type} (o : Maybe X) → mapᴹ (λ x → x) o ≡ o
  mapᴹ-idˢ (just _) = refl
  mapᴹ-idˢ nothing  = refl

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ

  -- ------------------------------------------------------------------------
  -- The message-level swap, at the exact channel shapes `Pair` produces.
  -- ------------------------------------------------------------------------

  swᵢ : ∀ {A B C D}
      → Channel.inType ((A ⊗ᵀ B) ⊗₀ (C ⊗ᵀ D))
      → Channel.inType ((C ⊗ᵀ D) ⊗₀ (A ⊗ᵀ B))
  swᵢ (inj₁ x) = inj₂ x
  swᵢ (inj₂ y) = inj₁ y

  swₒ : ∀ {A B C D}
      → Channel.outType ((A ⊗ᵀ B) ⊗₀ (C ⊗ᵀ D))
      → Channel.outType ((C ⊗ᵀ D) ⊗₀ (A ⊗ᵀ B))
  swₒ (inj₁ x) = inj₂ x
  swₒ (inj₂ y) = inj₁ y

  private
    swᵢ-invol : ∀ {A B C D} (i : Channel.inType ((A ⊗ᵀ B) ⊗₀ (C ⊗ᵀ D)))
              → swᵢ {C} {D} {A} {B} (swᵢ {A} {B} {C} {D} i) ≡ i
    swᵢ-invol (inj₁ _) = refl
    swᵢ-invol (inj₂ _) = refl

    swₒ-invol : ∀ {A B C D} (o : Channel.outType ((A ⊗ᵀ B) ⊗₀ (C ⊗ᵀ D)))
              → swₒ {C} {D} {A} {B} (swₒ {A} {B} {C} {D} o) ≡ o
    swₒ-invol (inj₁ _) = refl
    swₒ-invol (inj₂ _) = refl

  swₛ : ∀ {S₁ S₂ : Type} → S₁ × S₂ → S₂ × S₁
  swₛ (s₁ , s₂) = s₂ , s₁

  -- Each leaf step is re-tagged; the split on `m'` is what lets `mapᴹ swₒ`
  -- compute on the output.
  Pair-swap-to : ∀ {A B C D} (M₁ : Machine A B) (M₂ : Machine C D) {s i o s'}
               → Tensor.CompRel M₁ M₂ s i o s'
               → Tensor.CompRel M₂ M₁
                   (swₛ s) (swᵢ {A} {B} {C} {D} i)
                   (mapᴹ (swₒ {A} {B} {C} {D}) o) (swₛ s')
  Pair-swap-to _ _ (Tensor.Step₁ {m' = just _}  q) = Tensor.Step₂ q
  Pair-swap-to _ _ (Tensor.Step₁ {m' = nothing} q) = Tensor.Step₂ q
  Pair-swap-to _ _ (Tensor.Step₂ {m' = just _}  q) = Tensor.Step₁ q
  Pair-swap-to _ _ (Tensor.Step₂ {m' = nothing} q) = Tensor.Step₁ q

  Pair-swap : ∀ {A B C D} (M₁ : Machine A B) (M₂ : Machine C D)
            → Pair M₁ M₂ ≅ᴹ Reindex (Pair M₂ M₁) (swᵢ {A} {B} {C} {D}) (swₒ {A} {B} {C} {D})
  Pair-swap {A} {B} {C} {D} M₁ M₂ =
    MkIso swₛ swₛ (λ _ → refl) (λ _ → refl)
      (Pair-swap-to M₁ M₂)
      (λ {_} {i} {o} p →
        subst₂ (λ x y → Tensor.CompRel M₁ M₂ _ x y _)
               (swᵢ-invol i)
               (trans (mapᴹ-∘ˢ (swₒ {C} {D} {A} {B}) (swₒ {A} {B} {C} {D}) o)
                      (trans (mapᴹ-congˢ swₒ-invol o) (mapᴹ-idˢ o)))
               (Pair-swap-to M₂ M₁ p))
