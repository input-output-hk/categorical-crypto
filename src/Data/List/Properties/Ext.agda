{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Data.List.Properties`.
------------------------------------------------------------------------

module Data.List.Properties.Ext where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.List using (List; []; _∷_; _++_; map; head; drop)
open import Data.List.Properties using (≡-dec; ++-assoc; map-∘; map-cong; map-id)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
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

-- positional lookup as a partial function: the `n`-th element (0-based) of
-- `xs`, or `nothing` past the end.  Signature-free, so consumers inside a
-- parameterised module do not re-elaborate it per instantiation.
lookupMaybe : ∀ {a} {A : Set a} → List A → ℕ → Maybe A
lookupMaybe xs n = head (drop n xs)

-- decidable prefix strip: if `p` is a prefix of `xs`, recover the remainder
-- `ys` together with a propositional witness `xs ≡ p ++ ys`.
stripPrefix : ∀ {a} {A : Set a} → DecidableEquality A
            → (p xs : List A) → Maybe (Σ[ ys ∈ List A ] xs ≡ p ++ ys)
stripPrefix _≟_ []       xs       = just (xs , refl)
stripPrefix _≟_ (_ ∷ _)  []       = nothing
stripPrefix _≟_ (x ∷ p)  (y ∷ xs) with x ≟ y
... | no  _   = nothing
... | yes x≡y = Maybe.map (λ (ys , eq) → ys , cong₂ _∷_ (sym x≡y) eq)
                          (stripPrefix _≟_ p xs)

-- push a `map` through a composed relabelling that agrees pointwise with a
-- direct one; `map-∘-id` is the `map-id`-tail variant, for a left inverse.
map-∘-cong : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
               {f : A → B} {g : B → C} {h : A → C}
           → (∀ x → g (f x) ≡ h x)
           → (xs : List A) → map g (map f xs) ≡ map h xs
map-∘-cong p xs = trans (sym (map-∘ xs)) (map-cong p xs)

map-∘-id : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {g : B → A}
         → (∀ x → g (f x) ≡ x)
         → (xs : List A) → map g (map f xs) ≡ xs
map-∘-id p xs = trans (map-∘-cong p xs) (map-id xs)
