{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- The type-A EXCHANGE CONDITION at the front of a reduced word.
--   bring-to-front : (w : Word n) (i : Fin n)
--     → Reduced w → descent i (evalW w)
--     → Σ[ w′ ∈ Word n ] ((i ∷ w′) ~ʷ w) × Reduced w′
-- If `i` is a left descent of a reduced `w`, then `w` is `~ʷ`-equal to a
-- word starting with `i` whose tail is again reduced.  Insert-free: the
-- witness deletes one letter and the equality uses only c1/c2/c3.  This
-- file is the driver `btf′`; the case work lives in BringToFront{Base,
-- AdjR,AdjL,Cases}.
------------------------------------------------------------------------
module Categories.PermuteCoherence.BringToFront where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.List.Base using ([]; _∷_; length)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans)

open import Categories.PermuteCoherence.Word
  using (Word; evalW; _~ʷ_; ~refl; ∷c)
open import Categories.PermuteCoherence.InversionsCong using (inv-id)
open import Categories.PermuteCoherence.ExchangeBase
  using (Reduced; descent)
open import Categories.PermuteCoherence.BringToFrontBase
open import Categories.PermuteCoherence.BringToFrontCases

private
  variable
    n : ℕ


btf′ : (k : ℕ) (w : Word (suc n))
     → length w ≤ k → (i : Fin (suc n)) → Reduced w → descent i (evalW w) → BtfOut w i
-- `w = []` :  `descent i id-fb` is `suc _ ≡ inv id-fb ≡ 0`, impossible.
btf′ {n} _ [] _ i red dsc =
  ⊥-elim (1+n≢n′ (trans dsc (inv-id {suc n})))
  where
  1+n≢n′ : {m : ℕ} → suc m ≢ 0
  1+n≢n′ ()
btf′ {n} zero    (j ∷ rest) ()
btf′ {n} (suc k) (j ∷ rest) (s≤s lr≤k) i red dsc with i ≟ j
-- `i ≡ j` :  the head is exactly `i` already; witness `rest`.
... | yes i≡j = btfOut rest refl (∷c i≡j ~refl)
-- `i ≢ j` :  dispatch on Far / Adj using the factored case helpers.
... | no  i≢j = dispatch (decide-FA1 i j i≢j)
  where
  red-rest = Reduced-tail {j = j} {rest = rest} red
  hd       = head-descent {j = j} {rest = rest} red
  dispatch : FarAdj i j → BtfOut (j ∷ rest) i
  dispatch (is-far-ij f) = Cases.far-ij (btf′ k) lr≤k red-rest hd dsc f
  dispatch (is-far-ji f) = Cases.far-ji (btf′ k) lr≤k red-rest hd dsc f
  dispatch (is-adj-ij a) = Cases.adj-L  (btf′ k) lr≤k red-rest hd dsc a
  dispatch (is-adj-ji a) = Cases.adj-R  (btf′ k) lr≤k red-rest hd dsc a

-- Drive the fuelled recursion at exactly `length w`.
btf : (w : Word (suc n)) (i : Fin (suc n))
    → Reduced w → descent i (evalW w) → BtfOut w i
btf w i = btf′ (length w) w ≤-refl i

------------------------------------------------------------------------
-- The Exchange Condition (public form): project the one-letter-shorter
-- witness out of `btf`, recover `Reduced w′` via `reduced-of-witness`.

bring-to-front : {n : ℕ} (w : Word n) (i : Fin n)
               → Reduced w → descent i (evalW w)
               → Σ[ w′ ∈ Word n ] ((i ∷ w′) ~ʷ w) × Reduced w′
bring-to-front {zero}  w ()
bring-to-front {suc n} w i red dsc =
  w′ , rel , reduced-of-witness {w = w} {w′} {i} red dsc lenEq rel
  where
  bf : BtfOut w i
  bf    = btf w i red dsc
  w′    = BtfOut.wit bf
  lenEq = BtfOut.len bf
  rel   = BtfOut.rel bf
