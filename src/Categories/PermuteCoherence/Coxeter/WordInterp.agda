{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- List interpretation of adjacent-transposition words; see `Word` for
-- the right-to-left evaluation convention.  Out-of-range swaps are identities,
-- but valid-length interpretations never use those cases.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Coxeter.WordInterp {a} {X : Set a} where

open import Categories.PermuteCoherence.Coxeter.Word
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.FinBij.Properties

open import Data.Fin.Base renaming (suc to fsuc)
open import Data.Fin.Patterns
import Data.Fin.Permutation as P
open import Data.List.Base
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.Nat.Base
open import Data.Nat.Properties renaming (≡-irrelevant to ℕ-≡-irrelevant)
open import Relation.Binary.PropositionalEquality

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Interpretation
------------------------------------------------------------------------
swapAt : Fin n → List X → List X
swapAt _        []              = []
swapAt 0F       (a ∷ [])        = a ∷ []
swapAt 0F       (a ∷ b ∷ rest)  = b ∷ a ∷ rest
swapAt (fsuc i) (a ∷ xs)        = a ∷ swapAt i xs

swapAt-↭ : (i : Fin n) (xs : List X) → xs ↭ swapAt i xs
swapAt-↭ _        []              = Perm.refl
swapAt-↭ 0F       (a ∷ [])        = Perm.refl
swapAt-↭ 0F       (a ∷ b ∷ rest)  = Perm.swap a b Perm.refl
swapAt-↭ (fsuc i) (a ∷ xs)        = Perm.prep a (swapAt-↭ i xs)

swapAt-length : (i : Fin n) (xs : List X) → length (swapAt i xs) ≡ length xs
swapAt-length _        []              = refl
swapAt-length 0F       (a ∷ [])        = refl
swapAt-length 0F       (a ∷ b ∷ rest)  = refl
swapAt-length (fsuc i) (a ∷ xs)        = cong suc (swapAt-length i xs)

applyW : Word n → List X → List X
applyW []      xs = xs
applyW (i ∷ w) xs = swapAt i (applyW w xs)

applyW-length : (w : Word n) (xs : List X) → length (applyW w xs) ≡ length xs
applyW-length []      xs = refl
applyW-length (i ∷ w) xs = trans (swapAt-length i (applyW w xs)) (applyW-length w xs)

⟦_⟧↭ : (w : Word n) (xs : List X) → xs ↭ applyW w xs
⟦ []    ⟧↭ xs = Perm.refl
⟦ i ∷ w ⟧↭ xs = Perm.trans (⟦ w ⟧↭ xs) (swapAt-↭ i (applyW w xs))

------------------------------------------------------------------------
-- Evaluation and transport
------------------------------------------------------------------------

gen-eval : (i : Fin n) (ys : List X) (len : length ys ≡ suc n)
           (cod : length (swapAt i ys) ≡ suc n)
         → castFB len cod (eval-↭ (swapAt-↭ i ys)) ≈-fb genFB i
gen-eval {suc n} 0F (a ∷ b ∷ rest) len cod k
  rewrite ℕ-≡-irrelevant cod len =
  trans (cast-push {n = suc n} len len
                   (eval-↭ (swapAt-↭ {n = suc n} 0F (a ∷ b ∷ rest))) k)
        (aux len k)
  where
    aux : {m : ℕ} (e : suc (suc (length rest)) ≡ suc (suc m)) (j : Fin (suc (suc m)))
        → subst Fin e
            (eval-↭ (Perm.swap a b (Perm.refl {xs = rest}))
             P.⟨$⟩ʳ subst Fin (sym e) j)
          ≡ swap-fb m P.⟨$⟩ʳ j
    aux refl j =
      ∘-fb-congʳ (swap-fb (length rest))
                 (cons-fb (cons-fb (id-fb {n = length rest})))
                 (id-fb {n = suc (suc (length rest))})
                 (cons²-fb-id {n = length rest}) j
-- Pointwise chaining avoids unsolved intermediate records; see `FinBij.Properties.∘-fb-congˡ`.
gen-eval {suc n} (fsuc i) (a ∷ xs) len cod k =
  trans (cons-cast {n = n} len cod (eval-↭ (swapAt-↭ i xs)) k)
        (cons-fb-cong (gen-eval i xs (suc-injective len) (suc-injective cod)) k)

eval-respect : (z : X) (zs : List X) (w : Word (length zs))
             → castFB refl (applyW-length w (z ∷ zs))
                      (eval-↭ (⟦ w ⟧↭ (z ∷ zs)))
               ≈-fb evalW w
eval-respect z zs [] = cast-id refl
eval-respect z zs (i ∷ w) k =
  trans (comp-cast {n = length zs} refl lenMid lenCod
                   (eval-↭ (swapAt-↭ i (applyW w (z ∷ zs))))
                   (eval-↭ (⟦ w ⟧↭ (z ∷ zs))) k)
        (∘-fb-cong {g = castFB lenMid lenCod
                              (eval-↭ (swapAt-↭ i (applyW w (z ∷ zs))))}
                   {g′ = genFB i}
                   {f = castFB refl lenMid (eval-↭ (⟦ w ⟧↭ (z ∷ zs)))}
                   {f′ = evalW w}
                   (gen-eval i (applyW w (z ∷ zs)) lenMid lenCod)
                   (eval-respect z zs w)
                   k)
  where
    lenMid : length (applyW w (z ∷ zs)) ≡ suc (length zs)
    lenMid = applyW-length w (z ∷ zs)
    lenCod : length (applyW (i ∷ w) (z ∷ zs)) ≡ suc (length zs)
    lenCod = applyW-length (i ∷ w) (z ∷ zs)
