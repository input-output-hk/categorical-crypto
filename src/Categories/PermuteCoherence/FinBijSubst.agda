{-# OPTIONS --safe --without-K #-}

module Categories.PermuteCoherence.FinBijSubst where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; _∷_; length; map)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Level using (Level)

private
  variable
    a c : Level
    A : Set a
    C : Set c

-- J-lemmas about subst₂ on FinBij.
subst₂-FinBij-id : ∀ {n m} (e : n ≡ m) → subst₂ FinBij e e id-fb ≡ id-fb
subst₂-FinBij-id refl = refl

cons-fb-subst₂ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') (π : FinBij n m)
  → cons-fb (subst₂ FinBij a b π) ≡ subst₂ FinBij (cong suc a) (cong suc b) (cons-fb π)
cons-fb-subst₂ refl refl π = refl

swap-fb-subst₂ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') (π : FinBij n m)
  → cons-fb (cons-fb (subst₂ FinBij a b π))
    ≡ subst₂ FinBij (cong (λ z → suc (suc z)) a) (cong (λ z → suc (suc z)) b)
        (cons-fb (cons-fb π))
swap-fb-subst₂ refl refl π = refl

-- subst₂ is proof-irrelevant: it depends only on the proof's value.
-- (Needed to reconcile `length-map h (x∷xs)`'s `cong suc`-shaped proof
-- with the `sym`-shaped proof our recursion produces.)
subst₂-FinBij-irr : ∀ {n m n' m'} (a a' : n ≡ n') (b b' : m ≡ m') (π : FinBij n m)
  → a ≡ a' → b ≡ b' → subst₂ FinBij a b π ≡ subst₂ FinBij a' b' π
subst₂-FinBij-irr a a' b b' π refl refl = refl

sym-cong-suc : ∀ {n m} (e : n ≡ m) → sym (cong suc e) ≡ cong suc (sym e)
sym-cong-suc refl = refl

sym-cong-ss : ∀ {n m} (e : n ≡ m)
  → sym (cong suc (cong suc e)) ≡ cong (λ z → suc (suc z)) (sym e)
sym-cong-ss refl = refl

∘-fb-subst₂ : ∀ {n m k n' m' k'} (a : n ≡ n') (b : m ≡ m') (cc : k ≡ k')
  (g : FinBij m k) (f : FinBij n m)
  → subst₂ FinBij b cc g ∘-fb subst₂ FinBij a b f
    ≡ subst₂ FinBij a cc (g ∘-fb f)
∘-fb-subst₂ refl refl refl g f = refl

swap-gen-subst₂ : ∀ {n n'} (a : n ≡ n')
  → swap-fb n' ≡ subst₂ FinBij (cong (λ z → suc (suc z)) a) (cong (λ z → suc (suc z)) a) (swap-fb n)
swap-gen-subst₂ refl = refl

eval-map⁺ : (h : A → C) {xs ys : List A} (p : xs ↭ ys)
  → eval-↭ (PermProp.map⁺ h p)
    ≡ subst₂ FinBij (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p)
eval-map⁺ h {xs = xs} Perm.refl = sym (subst₂-FinBij-id (sym (length-map h xs)))
eval-map⁺ h {xs = x ∷ xs} {ys = .x ∷ ys} (Perm.prep x p) =
  trans (cong cons-fb (eval-map⁺ h p))
  (trans (cons-fb-subst₂ (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p))
         (subst₂-FinBij-irr
            (cong suc (sym (length-map h xs))) (sym (length-map h (x ∷ xs)))
            (cong suc (sym (length-map h ys))) (sym (length-map h (x ∷ ys)))
            (cons-fb (eval-↭ p))
            (sym (sym-cong-suc (length-map h xs)))
            (sym (sym-cong-suc (length-map h ys)))))
eval-map⁺ h {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (Perm.swap x y p) =
  trans (cong (λ z → swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb z)) (eval-map⁺ h p))
  (trans goal
         (subst₂-FinBij-irr
            (ss aa) (sym (length-map h (x ∷ x' ∷ xs)))
            (ss bb) (sym (length-map h (y ∷ y' ∷ ys)))
            (swap-fb (length ys) ∘-fb cons-fb (cons-fb (eval-↭ p)))
            (sym (sym-cong-ss (length-map h xs)))
            (sym (sym-cong-ss (length-map h ys)))))
  where
    aa = sym (length-map h xs)
    bb = sym (length-map h ys)
    ss : ∀ {n m} → n ≡ m → suc (suc n) ≡ suc (suc m)
    ss = cong (λ z → suc (suc z))
    goal : swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb (subst₂ FinBij aa bb (eval-↭ p)))
         ≡ subst₂ FinBij (ss aa) (ss bb)
             (swap-fb (length ys) ∘-fb cons-fb (cons-fb (eval-↭ p)))
    goal =
      trans (cong (swap-fb (length (map h ys)) ∘-fb_) (swap-fb-subst₂ aa bb (eval-↭ p)))
      (trans (cong (_∘-fb subst₂ FinBij (ss aa) (ss bb) (cons-fb (cons-fb (eval-↭ p))))
                   (swap-gen-subst₂ bb))
             (∘-fb-subst₂ (ss aa) (ss bb) (ss bb) (swap-fb (length ys)) (cons-fb (cons-fb (eval-↭ p)))))
eval-map⁺ h {xs = xs} {ys = zs} (Perm.trans {ys = ys} p q) =
  trans (cong₂ _∘-fb_ (eval-map⁺ h q) (eval-map⁺ h p))
        (∘-fb-subst₂ (sym (length-map h xs)) (sym (length-map h ys)) (sym (length-map h zs)) (eval-↭ q) (eval-↭ p))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

------------------------------------------------------------------------
-- More generic eval lemmas.

-- eval commutes with subst on the codomain.
eval-subst-cod : {xs : List A} {C D : List A} (eq : C ≡ D) (p : xs ↭ C)
  → eval-↭ (subst (λ z → xs ↭ z) eq p)
    ≡ subst (λ n → FinBij (length xs) n) (cong length eq) (eval-↭ p)
eval-subst-cod refl p = refl
