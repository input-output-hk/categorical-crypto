{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Length/descent facts feeding the Insertion-Lemma endgame:
-- `inv≤length`, `reduced-head`, `len≡0→[]`.
------------------------------------------------------------------------
module Categories.PermuteCoherence.InsertProofBase where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; n≤1+n; 1+n≰n; suc-injective)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using ([]; _∷_; length)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)
import Data.Fin.Permutation as P

open import Categories.PermuteCoherence.FinBij using (_∘-fb_)
open import Categories.PermuteCoherence.Word using (Word; evalW; genFB; genFB∘genFB)
open import Categories.PermuteCoherence.Inversions using (inv)
open import Categories.PermuteCoherence.InversionsCong using (inv-resp-≈; inv-id)
open import Categories.PermuteCoherence.ExchangeBase using (Reduced; descent; inv-di)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- `inv (evalW w) ≤ length w`: each generator changes `inv` by ±1.

inv≤length : (w : Word n) → inv (evalW w) ≤ length w
inv≤length {n} []          = ≤-reflexive (inv-id {n})
inv≤length {suc n} (i ∷ w) with inv-di i (evalW w)
... | inj₁ asc = ≤-trans (≤-reflexive asc) (s≤s (inv≤length w))
... | inj₂ dsc =
  ≤-trans (≤-trans (n≤1+n _) (≤-reflexive dsc))
          (≤-trans (inv≤length w) (n≤1+n _))

------------------------------------------------------------------------
-- A reduced `i ∷ v′` has `i` a descent and `v′` reduced.

reduced-head : (i : Fin (suc n)) (v′ : Word (suc n))
             → Reduced (i ∷ v′) → descent i (evalW (i ∷ v′)) × Reduced v′
reduced-head i v′ red with inv-di i (evalW v′)
... | inj₁ asc =
      trans (cong suc (inv-resp-≈ {b = genFB i ∘-fb (genFB i ∘-fb evalW v′)} {b′ = evalW v′}
                                  (genFB∘genFB i (evalW v′)))) (sym asc)
    , suc-injective (trans red asc)
... | inj₂ dsc =
  ⊥-elim (1+n≰n (≤-trans (s≤s (n≤1+n (length v′)))
                         (≤-trans (≤-reflexive (trans (cong suc red) dsc)) (inv≤length v′))))

------------------------------------------------------------------------
-- Length-zero words are empty.

len≡0→[] : (w : Word n) → length w ≡ 0 → w ≡ []
len≡0→[] []      _ = refl
len≡0→[] (_ ∷ _) ()
