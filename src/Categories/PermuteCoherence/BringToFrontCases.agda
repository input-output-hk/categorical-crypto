{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Exchange condition: `BtfOut`/`Rec` and the four Far/Adj case
-- constructions of one step (`module Cases`).  Each case is `abstract`,
-- so the driver `btf′` only ever sees their types.
------------------------------------------------------------------------
module Categories.PermuteCoherence.BringToFrontCases where

open import Data.Nat.Base using (ℕ; suc; _<_; _≤_)
open import Data.Nat.Properties
  using (≤-trans; n≤1+n)
open import Data.Fin.Base using (Fin; toℕ) renaming (suc to fsuc; zero to fz)
open import Data.List.Base using (_∷_; length)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
import Data.Fin.Permutation as P

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; _∘-fb_; id-fb; inv-fb)
open import Categories.PermuteCoherence.Word
  using (Word; evalW; genFB; _~ʷ_; ~refl; ~sym; ~trans; ∷c; c1; c2; c3; Far; far0ˡ; far0ʳ; farS; Adj; adj0; adjS; ∷-cong; genFB-involutive; ~ʷ⇒≈)
open import Categories.PermuteCoherence.Inversions using (inv)
open import Categories.PermuteCoherence.ExchangeBase
  using (Reduced; descent; descent-resp-≈; inv-di)
open import Categories.PermuteCoherence.InversionsDichotomy
  using (inj; suc-pos; toℕ-inj; toℕ-suc-pos; swapℕ; swapℕ-k; swapℕ-sk; genFB-toℕ; invS-dichotomy)
open import Categories.PermuteCoherence.BringToFrontBase
open import Categories.PermuteCoherence.BringToFrontAdjR
open import Categories.PermuteCoherence.BringToFrontAdjL

private
  variable
    n : ℕ

-- The result of one exchange step: a witness word `wit` that deletes
-- exactly one letter (`len`) and reassociates to `w` with `i` at the
-- front (`rel`).
record BtfOut {n : ℕ} (w : Word (suc n)) (i : Fin (suc n)) : Set where
  constructor btfOut
  field
    wit : Word (suc n)
    len : suc (length wit) ≡ length w
    rel : (i ∷ wit) ~ʷ w

-- The recursion callback handed to each case at fuel `k`.  The four
-- `FarAdj` branches take it as an argument so each can be its own
-- `abstract` definition rather than one large term.
Rec : (n k : ℕ) → Set
Rec n k = (w : Word (suc n)) → length w ≤ k → (i : Fin (suc n))
        → Reduced w → descent i (evalW w) → BtfOut w i

-- Common reasoning shared by the four branches, abstracted over the head
-- `j`, residual word `rest` and descent index `i` (with `b = evalW rest`).
-- `hd`/`dsc` are the head- and assumed-descents of `genFB j ∘-fb b`.
module Cases {n k : ℕ} (rec : Rec n k)
             {j i : Fin (suc n)} {rest : Word (suc n)}
             (lr≤k : length rest ≤ k)
             (red-rest : Reduced rest)
             (hd  : descent j (genFB j ∘-fb evalW rest))
             (dsc : descent i (genFB j ∘-fb evalW rest)) where

  private
    b = evalW rest

    -- Bring `i` to the front of `rest` (first recursion).
    front-i : descent i b → BtfOut rest i
    front-i d = rec rest lr≤k i red-rest d

    -- `j∷i∷j∷v ~ʷ j∷i∷u ~ʷ j∷rest`.
    chain : (u v : Word (suc n)) → (i ∷ u) ~ʷ rest → (j ∷ v) ~ʷ u
          → (j ∷ i ∷ j ∷ v) ~ʷ (j ∷ rest)
    chain u v rᵤ rᵥ = ~trans (∷-cong j (∷-cong i rᵥ)) (∷-cong j rᵤ)

    -- After bringing `i` to the front of `rest` (giving `u`), bring `j`
    -- to the front of `u` (second recursion), then leave the caller to
    -- apply the appropriate braid (`c3` / `~sym (c3 _)`) via `mk`.
    adj : descent i b → descent j (genFB i ∘-fb b)
        → ((u v : Word (suc n)) → (j ∷ i ∷ j ∷ v) ~ʷ (j ∷ rest)
             → suc (suc (length v)) ≡ length rest → BtfOut (j ∷ rest) i)
        → BtfOut (j ∷ rest) i
    adj dsc-i dscⱼ-b mk =
      let btfOut u lenEqᵤ relᵤ = front-i dsc-i
          red-u = reduced-of-witness {w = rest} {u} {i} red-rest dsc-i lenEqᵤ relᵤ
          dsc-j = descent-resp-≈ {j = j} {x = genFB i ∘-fb b} {y = evalW u}
                                 (λ p → sym (evalW-tail≈ relᵤ p)) dscⱼ-b
          u≤k   = ≤-trans (n≤1+n (length u)) (subst (_≤ k) (sym lenEqᵤ) lr≤k)
          btfOut v lenEqᵥ relᵥ = rec u u≤k j red-u dsc-j
      in  mk u v (chain u v relᵤ relᵥ)
             (trans (cong suc lenEqᵥ) lenEqᵤ)

  -- The four case constructions are `abstract`: each is large, and keeping
  -- them opaque means the dispatching `btf′` only ever sees their TYPES,
  -- so its own elaboration (and the recursive `with`-tree) stays cheap.
  abstract
    -- Far, `Far i j` :  commute the head `j` past `i` with `c2`.
    far-ij : Far i j → BtfOut (j ∷ rest) i
    far-ij f =
      let btfOut w″ lenEq rel = front-i (descent-far {i = i} {j} {b} (Far→gap f) dsc)
      in  btfOut (j ∷ w″) (cong suc lenEq) (~trans (c2 f) (∷-cong j rel))

    -- Far, `Far j i` :  same with `c2` reversed.
    far-ji : Far j i → BtfOut (j ∷ rest) i
    far-ji f =
      let btfOut w″ lenEq rel = front-i (descent-far {i = i} {j} {b} (gapˢ (Far→gap f)) dsc)
      in  btfOut (j ∷ w″) (cong suc lenEq) (~trans (~sym (c2 f)) (∷-cong j rel))
      where
      gapˢ : (suc (toℕ j) < toℕ i) ⊎ (suc (toℕ i) < toℕ j) → Gap i j
      gapˢ (inj₁ x) = inj₂ x
      gapˢ (inj₂ y) = inj₁ y

    -- Adj, `Adj i j` (head `j = i+1`) :  two recursions + braid `c3`.
    adj-L : Adj i j → BtfOut (j ∷ rest) i
    adj-L a =
      adj (AdjL.adj-descent-i {b = b} a hd dsc) (AdjL.adj-descent-j {b = b} a dsc)
          (λ u v chn lenV → btfOut (j ∷ i ∷ v) (cong suc lenV) (~trans (c3 a) chn))

    -- Adj, `Adj j i` (head `j`, descent `i = j+1`) :  two recursions + `c3`.
    adj-R : Adj j i → BtfOut (j ∷ rest) i
    adj-R a =
      adj (AdjR.adj-descent-i {b = b} a hd dsc) (AdjR.adj-descent-j {b = b} a dsc)
          (λ u v chn lenV → btfOut (j ∷ i ∷ v) (cong suc lenV) (~trans (~sym (c3 a)) chn))
