{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Exchange condition, braid case: descent transfer when the head
-- generator `j` is one above the descent index `i` (`Adj i j`).
------------------------------------------------------------------------
module Categories.PermuteCoherence.BringToFrontAdjL where

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

module AdjL {n : ℕ} {j i : Fin (suc n)}
            {b : FinBij (suc (suc n)) (suc (suc n))}
            (adj : Adj i j) where

  private
    -- here `toℕ j ≡ suc (toℕ i)`.
    toℕj≡ : toℕ j ≡ suc (toℕ i)
    toℕj≡ = Adj→suc adj

    -- `genFB j` swaps `inj j (=i+1)` and `suc-pos j (=i+2)`.
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

    -- `inj j` and `suc-pos i` denote the same value (`toℕ ≡ suc (toℕ i)`).
    inj-j≡suc-i : inj j ≡ suc-pos i
    inj-j≡suc-i = toℕ-injective
      (trans (toℕ-inj j) (trans toℕj≡ (sym (toℕ-suc-pos i))))

    -- `genFB j` fixes `inj i` (toℕ i, outside `{j, j+1} = {i+1, i+2}`).
    toℕii : toℕ (inj i) ≡ toℕ i
    toℕii = toℕ-inj i

    j-fix-inj-i : genFB j P.⟨$⟩ˡ inj i ≡ inj i
    j-fix-inj-i = toℕ-injective
      (trans (genFB-ˡ-toℕ j (inj i))
             (swapℕ-fix-val (toℕ j) (toℕ (inj i)) ii≢j ii≢sj))
      where
      ii≢j : toℕ (inj i) ≢ toℕ j
      ii≢j e = 1+n≢n (sym (trans (sym toℕii) (trans e toℕj≡)))
      ii≢sj : toℕ (inj i) ≢ suc (toℕ j)
      ii≢sj e = 2+n≢n (toℕ i)
        (sym (trans (sym toℕii) (trans e (cong suc toℕj≡))))

    -- `genFB j` sends `suc-pos i` (toℕ i+1 = toℕ j) to `suc-pos j` (toℕ j+1).
    j-on-suc-i : genFB j P.⟨$⟩ˡ suc-pos i ≡ suc-pos j
    j-on-suc-i = toℕ-injective
      (trans (genFB-ˡ-toℕ j (suc-pos i))
             (trans (cong (swapℕ (toℕ j)) (trans (toℕ-suc-pos i) (sym toℕj≡)))
                    (trans (swapℕ-k (toℕ j)) (sym (toℕ-suc-pos j)))))

    -- `genFB i` sends `inj j` (toℕ i+1) to `inj i` (toℕ i), and fixes
    -- `suc-pos j` (toℕ i+2, outside `{i, i+1}`).
    i-on-inj-j : genFB i P.⟨$⟩ˡ inj j ≡ inj i
    i-on-inj-j = toℕ-injective
      (trans (genFB-ˡ-toℕ i (inj j))
             (trans (cong (swapℕ (toℕ i)) (trans (toℕ-inj j) toℕj≡))
                    (trans (swapℕ-sk (toℕ i)) (sym (toℕ-inj i)))))

    toℕsj : toℕ (suc-pos j) ≡ suc (suc (toℕ i))
    toℕsj = trans (toℕ-suc-pos j) (cong suc toℕj≡)

    i-fix-suc-j : genFB i P.⟨$⟩ˡ suc-pos j ≡ suc-pos j
    i-fix-suc-j = toℕ-injective
      (trans (genFB-ˡ-toℕ i (suc-pos j))
             (swapℕ-fix-val (toℕ i) (toℕ (suc-pos j))
               (λ e → 2+n≢n (toℕ i) (trans (sym toℕsj) e))
               (λ e → 1+n≢n (trans (sym toℕsj) e))))

    -- The three relevant positions of `b`.
    pa = toℕ (b P.⟨$⟩ˡ inj i)      -- position of value `i`
    pc = toℕ (b P.⟨$⟩ˡ suc-pos i)  -- position of value `i+1`
    pd = toℕ (b P.⟨$⟩ˡ suc-pos j)  -- position of value `i+2`

  -- `pc < pd`  (head `j` is a left descent of `genFB j ∘-fb b`).
  head→pos : descent j (genFB j ∘-fb b) → pc < pd
  head→pos hd =
    subst₂ _<_
      (trans (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) j-on-suc-j)
             (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) inj-j≡suc-i))   -- posⱼ₊₁ j (gjb) = pc
      (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) j-on-inj-j)            -- posⱼ   j (gjb) = pd
      (descent→pos j (genFB j ∘-fb b) hd)

  -- `pd < pa`  (the assumed descent of `i`, read through the head `j`).
  hyp→pos : descent i (genFB j ∘-fb b) → pd < pa
  hyp→pos hp =
    subst₂ _<_
      (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) j-on-suc-i)   -- posᵢ₊₁ i (gjb) = pd
      (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) j-fix-inj-i)  -- posᵢ   i (gjb) = pa
      (descent→pos i (genFB j ∘-fb b) hp)

  -- Output 1:  `descent i b`  (from `pc < pa`).  `abstract`: keep opaque.
  abstract
    adj-descent-i : descent j (genFB j ∘-fb b) → descent i (genFB j ∘-fb b)
                  → descent i b
    adj-descent-i hd hp =
      pos→descent i b (<-trans (head→pos hd) (hyp→pos hp))

    -- Output 2:  `descent j (genFB i ∘-fb b)`  (from `pd < pa`).
    adj-descent-j : descent i (genFB j ∘-fb b) → descent j (genFB i ∘-fb b)
    adj-descent-j hp =
      pos→descent j (genFB i ∘-fb b)
        (subst₂ _<_
          (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) (sym i-fix-suc-j))  -- pd = posⱼ₊₁ j (gib)
          (cong (λ z → toℕ (b P.⟨$⟩ˡ z)) (sym i-on-inj-j))   -- pa = posⱼ   j (gib)
          (hyp→pos hp))
