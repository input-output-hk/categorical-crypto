{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Data.List.Properties`.
------------------------------------------------------------------------

module Data.List.Properties.Ext where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (≡-dec; ++-assoc)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.Definitions using (DecidableEquality; Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

≡-irrelevant : ∀ {a} {A : Set a} → DecidableEquality A → Irrelevant {A = List A} _≡_
≡-irrelevant _≟_ = Decidable⇒UIP.≡-irrelevant (≡-dec _≟_)

-- re-associate a mid-nested `++` block: (p ++ (x ++ s)) ++ r → p ++ (x ++ (s ++ r))
++-assoc-mid : ∀ {a} {A : Set a} (p x s r : List A)
             → (p ++ (x ++ s)) ++ r ≡ p ++ (x ++ (s ++ r))
++-assoc-mid p x s r = trans (++-assoc p (x ++ s) r) (cong (p ++_) (++-assoc x s r))

-- decidable prefix strip: if `p` is a prefix of `xs`, recover the remainder
-- `ys` together with a propositional witness `xs ≡ p ++ ys`.
stripPrefix : ∀ {a} {A : Set a} → DecidableEquality A
            → (p xs : List A) → Maybe (Σ[ ys ∈ List A ] xs ≡ p ++ ys)
stripPrefix _≟_ []       xs       = just (xs , refl)
stripPrefix _≟_ (_ ∷ _)  []       = nothing
stripPrefix _≟_ (x ∷ p)  (y ∷ xs) with x ≟ y
... | no  _   = nothing
... | yes x≡y = map (λ (ys , eq) → ys , cong₂ _∷_ (sym x≡y) eq)
                    (stripPrefix _≟_ p xs)
