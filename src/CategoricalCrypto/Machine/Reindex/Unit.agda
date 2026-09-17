{-# OPTIONS --safe #-}

-- ============================================================================
-- `Pair` with the identity on the unit channel.
--
-- `I = ⊥ ⇿ ⊥` carries no messages, so `CC.id {I}` never steps: every step of
-- `Pair (CC.id {I}) M` is a `Step₂`, and every step of `Pair M (CC.id {I})` a
-- `Step₁`.  Up to the relabelling that drops the empty summand, each is `M`
-- itself:
--
--     Pair (CC.id {I}) M  ≅ᴹ  Reindex M unitˡᵢ unitˡₒ
--     Pair M (CC.id {I})  ≅ᴹ  Reindex M unitʳᵢ unitʳₒ
--
-- These are what the naturality of the unitors (`Machine.Monoidal.Unitors`)
-- needs from `Pair`, in the same way that the associator's needs `Pair-asc3`.
-- The proof is the usual one for `Pair`: its step relation sits at fully
-- general indices, so `Tensor.CompRel` constructors are matched directly; the
-- constructor for the identity's column is refuted on its message.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Reindex.Unit where

open Channel

open _≅ᴹ_

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ

  private
    -- There is no message on the identity's channel pair.
    noI : ∀ {ℓ} {W : Type ℓ} → inType (I ⊗ᵀ I) → W
    noI (inj₁ ())
    noI (inj₂ ())

  -- ------------------------------------------------------------------------
  -- The identity on the left.
  -- ------------------------------------------------------------------------

  unitˡᵢ : ∀ {A B} → inType ((I ⊗₀ I ᵀ) ⊗ᵀ ((A ⊗₀ B ᵀ) ᵀ))
                   → inType (A ⊗ᵀ B)
  unitˡᵢ (inj₁ (inj₁ ()))
  unitˡᵢ (inj₁ (inj₂ ()))
  unitˡᵢ (inj₂ x) = x

  unitˡₒ : ∀ {A B} → outType ((I ⊗₀ I ᵀ) ⊗ᵀ ((A ⊗₀ B ᵀ) ᵀ))
                   → outType (A ⊗ᵀ B)
  unitˡₒ (inj₁ (inj₁ ()))
  unitˡₒ (inj₁ (inj₂ ()))
  unitˡₒ (inj₂ x) = x

  Pair-unitˡ-to : ∀ {A B} (M : Machine A B) {s i o s'}
                → Tensor.CompRel (CC.id {I}) M s i o s'
                → Machine.stepRel M (proj₂ s) (unitˡᵢ {A} {B} i)
                                    (mapᴹ (unitˡₒ {A} {B}) o) (proj₂ s')
  Pair-unitˡ-to _ (Tensor.Step₁ {m = m} _)        = noI m
  Pair-unitˡ-to _ (Tensor.Step₂ {m' = just _}  q) = q
  Pair-unitˡ-to _ (Tensor.Step₂ {m' = nothing} q) = q

  Pair-unitˡ-from : ∀ {A B} (M : Machine A B) {s s'}
                    (i : inType ((I ⊗₀ I ᵀ) ⊗ᵀ ((A ⊗₀ B ᵀ) ᵀ)))
                    (o : Maybe (outType ((I ⊗₀ I ᵀ) ⊗ᵀ ((A ⊗₀ B ᵀ) ᵀ))))
                  → Machine.stepRel M s (unitˡᵢ {A} {B} i) (mapᴹ (unitˡₒ {A} {B}) o) s'
                  → Tensor.CompRel (CC.id {I}) M (tt , s) i o (tt , s')
  Pair-unitˡ-from _ (inj₁ (inj₁ ())) _ _
  Pair-unitˡ-from _ (inj₁ (inj₂ ())) _ _
  Pair-unitˡ-from _ (inj₂ x) nothing                 q = Tensor.Step₂ {m = x} {m' = nothing} q
  Pair-unitˡ-from _ (inj₂ x) (just (inj₁ (inj₁ ()))) _
  Pair-unitˡ-from _ (inj₂ x) (just (inj₁ (inj₂ ()))) _
  Pair-unitˡ-from _ (inj₂ x) (just (inj₂ y))         q = Tensor.Step₂ {m = x} {m' = just y} q

  Pair-unitˡ : ∀ {A B} (M : Machine A B)
             → Pair (CC.id {I}) M ≅ᴹ Reindex M (unitˡᵢ {A} {B}) (unitˡₒ {A} {B})
  Pair-unitˡ M =
    MkIso proj₂ (tt ,_) (λ _ → refl) (λ _ → refl)
      (Pair-unitˡ-to M)
      (λ {_} {i} {o} q → Pair-unitˡ-from M i o q)

  -- ------------------------------------------------------------------------
  -- The identity on the right.
  -- ------------------------------------------------------------------------

  unitʳᵢ : ∀ {A B} → inType ((A ⊗₀ B ᵀ) ⊗ᵀ ((I ⊗₀ I ᵀ) ᵀ))
                   → inType (A ⊗ᵀ B)
  unitʳᵢ (inj₁ x) = x
  unitʳᵢ (inj₂ (inj₁ ()))
  unitʳᵢ (inj₂ (inj₂ ()))

  unitʳₒ : ∀ {A B} → outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((I ⊗₀ I ᵀ) ᵀ))
                   → outType (A ⊗ᵀ B)
  unitʳₒ (inj₁ x) = x
  unitʳₒ (inj₂ (inj₁ ()))
  unitʳₒ (inj₂ (inj₂ ()))

  Pair-unitʳ-to : ∀ {A B} (M : Machine A B) {s i o s'}
                → Tensor.CompRel M (CC.id {I}) s i o s'
                → Machine.stepRel M (proj₁ s) (unitʳᵢ {A} {B} i)
                                    (mapᴹ (unitʳₒ {A} {B}) o) (proj₁ s')
  Pair-unitʳ-to _ (Tensor.Step₁ {m' = just _}  q) = q
  Pair-unitʳ-to _ (Tensor.Step₁ {m' = nothing} q) = q
  Pair-unitʳ-to _ (Tensor.Step₂ {m = m} _)        = noI m

  Pair-unitʳ-from : ∀ {A B} (M : Machine A B) {s s'}
                    (i : inType ((A ⊗₀ B ᵀ) ⊗ᵀ ((I ⊗₀ I ᵀ) ᵀ)))
                    (o : Maybe (outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((I ⊗₀ I ᵀ) ᵀ))))
                  → Machine.stepRel M s (unitʳᵢ {A} {B} i) (mapᴹ (unitʳₒ {A} {B}) o) s'
                  → Tensor.CompRel M (CC.id {I}) (s , tt) i o (s' , tt)
  Pair-unitʳ-from _ (inj₁ x) nothing                 q = Tensor.Step₁ {m = x} {m' = nothing} q
  Pair-unitʳ-from _ (inj₁ x) (just (inj₁ y))         q = Tensor.Step₁ {m = x} {m' = just y} q
  Pair-unitʳ-from _ (inj₁ x) (just (inj₂ (inj₁ ()))) _
  Pair-unitʳ-from _ (inj₁ x) (just (inj₂ (inj₂ ()))) _
  Pair-unitʳ-from _ (inj₂ (inj₁ ())) _ _
  Pair-unitʳ-from _ (inj₂ (inj₂ ())) _ _

  Pair-unitʳ : ∀ {A B} (M : Machine A B)
             → Pair M (CC.id {I}) ≅ᴹ Reindex M (unitʳᵢ {A} {B}) (unitʳₒ {A} {B})
  Pair-unitʳ M =
    MkIso proj₁ (_, tt) (λ _ → refl) (λ _ → refl)
      (Pair-unitʳ-to M)
      (λ {_} {i} {o} q → Pair-unitʳ-from M i o q)
