{-# OPTIONS --safe #-}

-- ============================================================================
-- The category of machines, with hom equality the state isomorphism `_≅ᴹ_`.
--
-- Associativity is the `TriTrace` isomorphism of `Machine.Iso`.  The two
-- identity laws are instances of the relay lemmas of `Reindex.Post`:
-- composing with a crossing forwarder relabels the other machine's ports,
-- and the identity relabels nothing.
-- ============================================================================

module CategoricalCrypto.Machine.Category where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Categories.Category

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Reindex.Post

∘-identityˡ-≅ᴹ : ∀ {A B} {m : Machine A B} → (_∘_ {B = B} id m) ≅ᴹ m
∘-identityˡ-≅ᴹ {m = m} = ∘-identityˡ-Post m

∘-identityʳ-≅ᴹ : ∀ {A B} {m : Machine A B} → (_∘_ {B = A} m id) ≅ᴹ m
∘-identityʳ-≅ᴹ {m = m} = ∘-identityʳ-Post m

MachineCategory : Category _ _ _
MachineCategory = record
  { Obj       = Channel
  ; _⇒_       = Machine
  ; _≈_       = _≅ᴹ_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = ∘-assoc-≅ᴹ
  ; sym-assoc = ≅ᴹ-sym ∘-assoc-≅ᴹ
  ; identityˡ = ∘-identityˡ-≅ᴹ
  ; identityʳ = ∘-identityʳ-≅ᴹ
  ; identity² = ∘-identityˡ-≅ᴹ
  ; equiv     = ≅ᴹ-isEquivalence
  ; ∘-resp-≈  = ∘-resp-≅ᴹ
  }
