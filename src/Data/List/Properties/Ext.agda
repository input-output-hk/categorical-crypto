{-# OPTIONS --safe --without-K #-}

-- Repo extensions of `Data.List.Properties`.

module Data.List.Properties.Ext where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.List using (List)
open import Data.List.Properties using (≡-dec)
open import Relation.Binary.Definitions using (DecidableEquality; Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- UIP on lists over a type with decidable equality (Hedberg), --without-K.
≡-irrelevant : ∀ {a} {A : Set a} → DecidableEquality A → Irrelevant {A = List A} _≡_
≡-irrelevant _≟_ = Decidable⇒UIP.≡-irrelevant (≡-dec _≟_)
