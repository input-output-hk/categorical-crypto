{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Exchange condition, braid case: descent transfer when the head
-- generator `j` is one below the descent index `i` (`Adj j i`).
------------------------------------------------------------------------
module Categories.PermuteCoherence.BringToFrontAdjR where

open import Data.Nat.Base using (ℕ; suc; _<_; _≤_)
open import Data.Nat.Properties
  using (<-trans; 1+n≢n)
open import Data.Fin.Base using (Fin; toℕ) renaming (suc to fsuc; zero to fz)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List.Base using (_∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_)
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
  using (Reduced; descent; inv-di)
open import Categories.PermuteCoherence.InversionsDichotomy
  using (inj; suc-pos; toℕ-inj; toℕ-suc-pos; swapℕ; swapℕ-k; swapℕ-sk; genFB-toℕ; invS-dichotomy)
open import Categories.PermuteCoherence.BringToFrontBase

private
  variable
    n : ℕ

module AdjR {n : ℕ} {j i : Fin (suc n)}
            {b : FinBij (suc (suc n)) (suc (suc n))}
            (adj : Adj j i) where

  private
    toℕi≡ : toℕ i ≡ suc (toℕ j)
    toℕi≡ = Adj→suc adj

    -- The backward action of `genFB j` on the four values it meets.
    -- `genFB j` swaps the values `j (=inj j)` and `j+1 (=suc-pos j=inj i)`,
    -- and fixes `j+2 (=suc-pos i)`.
    j-on-inj-j : genFB j P.⟨$⟩ˡ inj j ≡ suc-pos j
    j-on-inj-j = toℕ-injective
      (trans (genFB-ˡ-toℕ j (inj j))
             (trans (cong (swapℕ (toℕ j)) (toℕ-inj j))
                    (trans (swapℕ-k (toℕ j)) (sym (toℕ-suc-pos j)))))

    j-on-suc-j : genFB j P.⟨$⟩ˡ suc-pos j ≡ inj j
    j-on-suc-j = toℕ-injective
      (trans (genFB-ˡ-toℕ j (suc-pos j))
             (trans (cong (swapℕ (toℕ j)) (toℕ-suc-pos j))
                    (trans (swapℕ-sk (toℕ j)) (sym (toℕ-inj j)))))

    -- `inj i` has `toℕ ≡ suc (toℕ j)`, so `genFB j` sends it to `inj j`.
    j-on-inj-i : genFB j P.⟨$⟩ˡ inj i ≡ inj j
    j-on-inj-i = toℕ-injective
      (trans (genFB-ˡ-toℕ j (inj i))
             (trans (cong (swapℕ (toℕ j)) (trans (toℕ-inj i) toℕi≡))
                    (trans (swapℕ-sk (toℕ j)) (sym (toℕ-inj j)))))

    -- `suc-pos i` has `toℕ ≡ suc (suc (toℕ j))`, outside `{j, j+1}`, fixed.
    toℕsi : toℕ (suc-pos i) ≡ suc (suc (toℕ j))
    toℕsi = trans (toℕ-suc-pos i) (cong suc toℕi≡)

    j-on-suc-i : genFB j P.⟨$⟩ˡ suc-pos i ≡ suc-pos i
    j-on-suc-i = toℕ-injective
      (trans (genFB-ˡ-toℕ j (suc-pos i))
             (swapℕ-fix-val (toℕ j) (toℕ (suc-pos i))
               (λ e → 2+n≢n (toℕ j) (trans (sym toℕsi) e))
               (λ e → 1+n≢n (trans (sym toℕsi) e))))

    -- `genFB i` fixes `inj j` (toℕ j, outside `{i, i+1} = {j+1, j+2}`) and
    -- sends `suc-pos j` (toℕ j+1 = toℕ i) to `suc-pos i` (toℕ i+1).
    toℕij : toℕ (inj j) ≡ toℕ j
    toℕij = toℕ-inj j

    i-on-inj-j : genFB i P.⟨$⟩ˡ inj j ≡ inj j
    i-on-inj-j = toℕ-injective
      (trans (genFB-ˡ-toℕ i (inj j))
             (swapℕ-fix-val (toℕ i) (toℕ (inj j)) ij≢i ij≢si))
      where
      -- toℕ (inj j) = toℕ j ;  toℕ i = suc (toℕ j) ;  suc (toℕ i) = 2 + toℕ j.
      ij≢i : toℕ (inj j) ≢ toℕ i
      ij≢i e = 1+n≢n (sym (trans (sym toℕij) (trans e toℕi≡)))
      ij≢si : toℕ (inj j) ≢ suc (toℕ i)
      ij≢si e = 2+n≢n (toℕ j)
        (sym (trans (sym toℕij) (trans e (cong suc toℕi≡))))

    i-on-suc-j : genFB i P.⟨$⟩ˡ suc-pos j ≡ suc-pos i
    i-on-suc-j = toℕ-injective
      (trans (genFB-ˡ-toℕ i (suc-pos j))
             (trans (cong (swapℕ (toℕ i)) (trans (toℕ-suc-pos j) (sym toℕi≡)))
                    (trans (swapℕ-k (toℕ i)) (sym (toℕ-suc-pos i)))))

    -- `inj i` and `suc-pos j` denote the same value (`toℕ ≡ suc (toℕ j)`).
    inj-i≡suc-j : inj i ≡ suc-pos j
    inj-i≡suc-j = toℕ-injective (trans (toℕ-inj i) (trans toℕi≡ (sym (toℕ-suc-pos j))))

    -- The three relevant positions of `b`.
    pj  = toℕ (b P.⟨$⟩ˡ inj j)      -- position of value `j`
    pj1 = toℕ (b P.⟨$⟩ˡ suc-pos j)  -- position of value `j+1`
    pj2 = toℕ (b P.⟨$⟩ˡ suc-pos i)  -- position of value `j+2`

  -- `pj < pj1`  (the head `j` is a left descent of `genFB j ∘-fb b`).
  head→pos : descent j (genFB j ∘-fb b) → pj < pj1
  head→pos hd =
    subst₂ _<_
      (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) j-on-suc-j)   -- posⱼ₊₁ j (gjb) = pj
      (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) j-on-inj-j)   -- posⱼ   j (gjb) = pj1
      (descent→pos j (genFB j ∘-fb b) hd)

  -- `pj2 < pj`  (the assumed descent of `i`, read through the head `j`).
  hyp→pos : descent i (genFB j ∘-fb b) → pj2 < pj
  hyp→pos hp =
    subst₂ _<_
      (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) j-on-suc-i)   -- posᵢ₊₁ i (gjb) = pj2
      (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) j-on-inj-i)   -- posᵢ   i (gjb) = pj
      (descent→pos i (genFB j ∘-fb b) hp)

  -- Output 1:  `descent i b`  (from `pj2 < pj1`).  `abstract` keeps these
  -- large terms opaque so downstream (`btf′`) does not re-unfold them.
  abstract
    adj-descent-i : descent j (genFB j ∘-fb b) → descent i (genFB j ∘-fb b)
                  → descent i b
    adj-descent-i hd hp =
      pos→descent i b
        (subst₂ _<_ refl (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) (sym inj-i≡suc-j))
          (<-trans (hyp→pos hp) (head→pos hd)))

    -- Output 2:  `descent j (genFB i ∘-fb b)`  (from `pj2 < pj`).
    adj-descent-j : descent i (genFB j ∘-fb b) → descent j (genFB i ∘-fb b)
    adj-descent-j hp =
      pos→descent j (genFB i ∘-fb b)
        (subst₂ _<_
          (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) (sym i-on-suc-j))   -- pj2 = posⱼ₊₁ j (gib)
          (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) (sym i-on-inj-j))   -- pj  = posⱼ   j (gib)
          (hyp→pos hp))
