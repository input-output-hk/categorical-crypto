{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Data.List.Properties`.
------------------------------------------------------------------------

module Data.List.Properties.Ext where

open import Axiom.UniquenessOfIdentityProofs
open import Data.Empty
open import Data.Fin.Base
open import Data.List.Base
open import Data.List.Properties
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base
open import Data.Product.Base using (Σ-syntax; _,_)
open import Function.Base using (case_of_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Decidable.Core

≡-irrelevant : ∀ {a} {A : Set a} → DecidableEquality A → Irrelevant {A = List A} _≡_
≡-irrelevant _≟_ = Decidable⇒UIP.≡-irrelevant (≡-dec _≟_)

-- `Data.List.Effectful.MonadProperties.associative` is this at a single level.
concatMap-assoc : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                  (xs : List A) (f : A → List B) (g : B → List C)
                → concatMap g (concatMap f xs) ≡ concatMap (λ x → concatMap g (f x)) xs
concatMap-assoc []       f g = refl
concatMap-assoc (x ∷ xs) f g = trans (concatMap-++ g (f x) (concatMap f xs))
                                     (cong (concatMap g (f x) ++_) (concatMap-assoc xs f g))

++-assoc-mid : ∀ {a} {A : Set a} (p x s r : List A)
             → (p ++ (x ++ s)) ++ r ≡ p ++ (x ++ (s ++ r))
++-assoc-mid p x s r = trans (++-assoc p (x ++ s) r) (cong (p ++_) (++-assoc x s r))

lookupMaybe : ∀ {a} {A : Set a} → List A → ℕ → Maybe A
lookupMaybe xs n = head (drop n xs)

stripPrefix : ∀ {a} {A : Set a} → DecidableEquality A
            → (p xs : List A) → Maybe (Σ[ ys ∈ List A ] xs ≡ p ++ ys)
stripPrefix _≟_ []       xs       = just (xs , refl)
stripPrefix _≟_ (_ ∷ _)  []       = nothing
stripPrefix _≟_ (x ∷ p)  (y ∷ xs) = case x ≟ y of λ where
  (no  _)   → nothing
  (yes x≡y) → Maybe.map (λ (ys , eq) → ys , cong₂ _∷_ (sym x≡y) eq)
                        (stripPrefix _≟_ p xs)

map-∘-cong : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
               {f : A → B} {g : B → C} {h : A → C}
           → (∀ x → g (f x) ≡ h x)
           → (xs : List A) → map g (map f xs) ≡ map h xs
map-∘-cong p xs = trans (sym (map-∘ xs)) (map-cong p xs)

map-∘-id : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {g : B → A}
         → (∀ x → g (f x) ≡ x)
         → (xs : List A) → map g (map f xs) ≡ xs
map-∘-id p xs = trans (map-∘-cong p xs) (map-id xs)

All-lookup : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A}
           → All P xs → (i : Fin (length xs)) → P (lookup xs i)
All-lookup (p ∷ _)  zero    = p
All-lookup (_ ∷ ps) (suc i) = All-lookup ps i

lookup-injective-unique : ∀ {a} {A : Set a} {xs : List A}
                        → Unique xs
                        → ∀ (i j : Fin (length xs))
                        → lookup xs i ≡ lookup xs j
                        → i ≡ j
lookup-injective-unique (_  ∷ _ ) zero    zero    _  = refl
lookup-injective-unique (x≢ ∷ _ ) zero    (suc j) eq = ⊥-elim (All-lookup x≢ j eq)
lookup-injective-unique (x≢ ∷ _ ) (suc i) zero    eq = ⊥-elim (All-lookup x≢ i (sym eq))
lookup-injective-unique (_  ∷ uq) (suc i) (suc j) eq =
  cong suc (lookup-injective-unique uq i j eq)
