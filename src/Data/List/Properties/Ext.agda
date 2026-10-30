{-# OPTIONS --safe --without-K #-}

module Data.List.Properties.Ext where

open import Axiom.UniquenessOfIdentityProofs
open import Data.Empty
open import Data.Fin.Base hiding (_+_; pred)
open import Data.List.Base
open import Data.List.Properties
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there; index)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base
open import Data.Product.Base using (Σ-syntax; _,_; proj₁; proj₂)
open import Function.Base using (case_of_; _∘_)
open import Level using (Level)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Decidable.Core

private variable
  a b c p : Level
  A : Set a
  B : Set b
  C : Set c
  P : A → Set p
  xs : List A
  m n : ℕ

≡-irrelevant : DecidableEquality A → Irrelevant {A = List A} _≡_
≡-irrelevant _≟_ = Decidable⇒UIP.≡-irrelevant (≡-dec _≟_)

-- `Data.List.Effectful.MonadProperties.associative` is this at a single level.
concatMap-assoc : (xs : List A) (f : A → List B) (g : B → List C)
                → concatMap g (concatMap f xs) ≡ concatMap (concatMap g ∘ f) xs
concatMap-assoc []       f g = refl
concatMap-assoc (x ∷ xs) f g = trans (concatMap-++ g (f x) (concatMap f xs))
                                     (cong (concatMap g (f x) ++_) (concatMap-assoc xs f g))

++-assoc-mid : (p x s r : List A)
             → (p ++ (x ++ s)) ++ r ≡ p ++ (x ++ (s ++ r))
++-assoc-mid p x s r = trans (++-assoc p (x ++ s) r) (cong (p ++_) (++-assoc x s r))

lookupMaybe : List A → ℕ → Maybe A
lookupMaybe xs n = head (drop n xs)

stripPrefix : DecidableEquality A
            → (p xs : List A) → Maybe (Σ[ ys ∈ List A ] xs ≡ p ++ ys)
stripPrefix _≟_ []       xs       = just (xs , refl)
stripPrefix _≟_ (_ ∷ _)  []       = nothing
stripPrefix _≟_ (x ∷ p)  (y ∷ xs) = case x ≟ y of λ where
  (no  _)   → nothing
  (yes x≡y) → Maybe.map (λ (ys , eq) → ys , cong₂ _∷_ (sym x≡y) eq)
                        (stripPrefix _≟_ p xs)

map-∘-cong : {f : A → B} {g : B → C} {h : A → C}
           → (∀ x → g (f x) ≡ h x)
           → (xs : List A) → map g (map f xs) ≡ map h xs
map-∘-cong p xs = trans (sym (map-∘ xs)) (map-cong p xs)

map-∘-id : {f : A → B} {g : B → A}
         → (∀ x → g (f x) ≡ x)
         → (xs : List A) → map g (map f xs) ≡ xs
map-∘-id p xs = trans (map-∘-cong p xs) (map-id xs)

All-lookup : All P xs → (i : Fin (length xs)) → P (lookup xs i)
All-lookup (p ∷ _)  zero    = p
All-lookup (_ ∷ ps) (suc i) = All-lookup ps i

-- Eliminate the witness against the aligned list without constructing,
-- casting and then eliminating an intermediate Fin index.
lookup-along : (xs : List A) (ys : List B) → length xs ≡ length ys → Any P xs → B
lookup-along [] ys eq ()
lookup-along (_ ∷ _) [] () p
lookup-along (_ ∷ xs) (y ∷ ys) eq (here _) = y
lookup-along (_ ∷ xs) (_ ∷ ys) eq (there p) = lookup-along xs ys (cong pred eq) p

lookup-along-index : (xs : List A) (ys : List B) (eq : length xs ≡ length ys) (p : Any P xs)
                   → lookup-along xs ys eq p ≡ lookup ys (cast eq (index p))
lookup-along-index [] ys eq ()
lookup-along-index (_ ∷ _) [] () p
lookup-along-index (_ ∷ xs) (_ ∷ ys) eq (here _) = refl
lookup-along-index (_ ∷ xs) (_ ∷ ys) eq (there p) = lookup-along-index xs ys (cong pred eq) p

lookup-injective-unique : Unique xs
                        → ∀ (i j : Fin (length xs))
                        → lookup xs i ≡ lookup xs j
                        → i ≡ j
lookup-injective-unique (_  ∷ _ ) zero    zero    _  = refl
lookup-injective-unique (x≢ ∷ _ ) zero    (suc j) eq = ⊥-elim (All-lookup x≢ j eq)
lookup-injective-unique (x≢ ∷ _ ) (suc i) zero    eq = ⊥-elim (All-lookup x≢ i (sym eq))
lookup-injective-unique (_  ∷ uq) (suc i) (suc j) eq =
  cong suc (lookup-injective-unique uq i j eq)

len-match : ∀ {A B Y : Set} (f : A → Y) (g : B → Y)
            (xs : List A) (ys : List B) → map f xs ≡ map g ys
          → length xs ≡ length ys
len-match f g xs ys eq =
  trans (sym (length-map f xs))
        (trans (cong length eq) (length-map g ys))

lookup-boundary : ∀ {A B Y : Set} (f : A → Y) (g : B → Y)
                    (xs : List A) (ys : List B)
                    (eq : map f xs ≡ map g ys)
                    (i : Fin (length xs))
                  → f (lookup xs i)
                  ≡ g (lookup ys (cast (len-match f g xs ys eq) i))
lookup-boundary f g (x ∷ xs) (y ∷ ys) eq zero    = proj₁ (∷-injective eq)
lookup-boundary f g (x ∷ xs) (y ∷ ys) eq (suc i) =
  lookup-boundary f g xs ys (proj₂ (∷-injective eq)) i

deriveAtomEq
  : ∀ {V₁ V₂ X : Set} {vlab₁ : V₁ → X} {vlab₂ : V₂ → X} {φ : V₁ → V₂}
  → (∀ i → vlab₂ (φ i) ≡ vlab₁ i)
  → ∀ (xs : List V₁) {ys : List V₂} → ys ≡ map φ xs
  → map vlab₂ ys ≡ map vlab₁ xs
deriveAtomEq {vlab₂ = vlab₂} φ-lab xs p =
  trans (cong (map vlab₂) p) (map-∘-cong φ-lab xs)

tabulate-+ : ∀ {A : Set} (f : Fin (m + n) → A)
           → tabulate f
           ≡ tabulate (f ∘ (_↑ˡ n)) ++ tabulate (f ∘ (m ↑ʳ_))
tabulate-+ {m = zero}          f = refl
tabulate-+ {m = suc m} {n = n} f = cong (f zero ∷_) (tabulate-+ {m = m} {n = n} (f ∘ suc))

concat-tabulate-blocks
  : ∀ {A B C : Set}
      (fc : Fin (m + n) → List C) (fG : Fin m → List A) (fK : Fin n → List B)
      (gL : A → C) (gR : B → C)
  → (∀ e → fc (e ↑ˡ n) ≡ map gL (fG e))
  → (∀ e → fc (m ↑ʳ e) ≡ map gR (fK e))
  → concat (tabulate fc)
    ≡ map gL (concat (tabulate fG)) ++ map gR (concat (tabulate fK))
concat-tabulate-blocks {m} {n} fc fG fK gL gR redL redR =
  trans (cong concat (tabulate-+ {m = m} {n = n} fc))
  (trans (cong concat
            (cong₂ _++_ (trans (tabulate-cong redL) (sym (map-tabulate fG (map gL))))
                        (trans (tabulate-cong redR) (sym (map-tabulate fK (map gR))))))
  (trans (sym (concat-++ (map (map gL) (tabulate fG)) (map (map gR) (tabulate fK))))
         (cong₂ _++_ (concat-map (tabulate fG)) (concat-map (tabulate fK)))))

allFin-suc : ∀ n → allFin (suc n) ≡ zero ∷ map suc (allFin n)
allFin-suc n = cong (zero ∷_) (sym (map-tabulate (λ i → i) suc))

allFin-++ : ∀ n m → allFin (n + m) ≡ map (_↑ˡ m) (allFin n) ++ map (n ↑ʳ_) (allFin m)
allFin-++ n m =
  trans (tabulate-+ {m = n} {n = m} (λ i → i))
        (cong₂ _++_ (sym (map-tabulate (λ i → i) (_↑ˡ m)))
                     (sym (map-tabulate (λ i → i) (n ↑ʳ_))))

map-allFin : ∀ {a} {A : Set a} (f : Fin n → A) → map f (allFin n) ≡ tabulate f
map-allFin f = map-tabulate (λ i → i) f

map-lookup-allFin : ∀ {a} {A : Set a} (xs : List A) → map (lookup xs) (allFin (length xs)) ≡ xs
map-lookup-allFin xs = trans (map-allFin (lookup xs)) (tabulate-lookup xs)
