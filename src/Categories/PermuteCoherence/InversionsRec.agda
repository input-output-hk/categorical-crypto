{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The sum-of-inversions `invS` satisfies the Lehmer recursion (peeling
-- value 0), hence equals the recursive `inv` (`invS≡inv`).
--
-- The crux is the Lehmer recursion #inversions(b) = #inversions(residual)
-- + #inversions involving value 0.  Value 0 sits at position `m = b ⟨$⟩ˡ
-- 0F`; the `toℕ m` earlier positions each contribute one inversion with it,
-- and ALL other inversions are exactly those of the residual.
--
-- Strategy:
--   * `sumF-punch` : pull index `m` out of a `Fin (suc N)`-sum.
--   * `invS-peel`  : if `b ⟨$⟩ʳ m ≡ 0F` then invS b ≡ toℕ m + invS (remove m b).
--   * the `inv`-residual is `≈-fb`-equal to `remove m b` (`rest≈remove-m`).
------------------------------------------------------------------------

module Categories.PermuteCoherence.InversionsRec where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Fin.Base using (Fin; toℕ; punchIn; _<_)
  renaming (suc to fsuc; zero to fz)
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Properties
  using (suc-injective; _<?_; punchIn-mono-≤; punchIn-cancel-≤)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool.Base using (_∧_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst₂)

import Data.Fin.Permutation as P
open P using (remove)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _∘-fb_; inv-fb; _≈-fb_)
open import Categories.PermuteCoherence.Word using (rotate-fb)
open import Categories.PermuteCoherence.Inversions using (inv)
open import Categories.PermuteCoherence.InversionsSum
  using (sumF; sumF-cong; sumF-+; 1if; invAt; invS)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- 0. Decidable-bracket congruence under logical equivalence.

dec-cong : {A B : Set} (a? : Dec A) (b? : Dec B)
         → (A → B) → (B → A) → ⌊ a? ⌋ ≡ ⌊ b? ⌋
dec-cong (yes _) (yes _) _ _ = refl
dec-cong (no  _) (no  _) _ _ = refl
dec-cong (yes a) (no ¬b) f _ = ⊥-elim (¬b (f a))
dec-cong (no ¬a) (yes b) _ g = ⊥-elim (¬a (g b))

------------------------------------------------------------------------
-- 1. Pull one index out of a `Fin (suc N)`-sum:
--   sumF g ≡ g m + sumF (g ∘ punchIn m)  (`punchIn m` enumerates ∖ {m}).

sumF-punch : {N : ℕ} (g : Fin (suc N) → ℕ) (m : Fin (suc N))
           → sumF g ≡ g m + sumF (λ j → g (punchIn m j))
sumF-punch {zero}  g 0F = refl
sumF-punch {suc N} g 0F = refl
sumF-punch {suc N} g (fsuc m) =
  trans (cong (g 0F +_) (sumF-punch (λ j → g (fsuc j)) m))
        (lemma (g 0F) (g (fsuc m)) (sumF (λ j → g (fsuc (punchIn m j)))))
  where
  lemma : (a c S : ℕ) → a + (c + S) ≡ c + (a + S)
  lemma a c S =
    trans (sym (+-assoc a c S))
          (trans (cong (_+ S) (+-comm a c)) (+-assoc c a S))

------------------------------------------------------------------------
-- 2. `invS` respects pointwise (`≈-fb`) equality (`invAt` uses `b ⟨$⟩ʳ` only).

invAt-resp-≈ : {n : ℕ} {b b′ : FinBij (suc n) (suc n)} → b ≈-fb b′
             → ∀ x y → invAt b x y ≡ invAt b′ x y
invAt-resp-≈ {b = b} {b′} eq x y =
  cong (λ z → 1if (⌊ x <? y ⌋ ∧ z)) brkt
  where
  brkt : ⌊ (b P.⟨$⟩ʳ y) <? (b P.⟨$⟩ʳ x) ⌋
       ≡ ⌊ (b′ P.⟨$⟩ʳ y) <? (b′ P.⟨$⟩ʳ x) ⌋
  brkt = dec-cong ((b P.⟨$⟩ʳ y) <? (b P.⟨$⟩ʳ x))
                  ((b′ P.⟨$⟩ʳ y) <? (b′ P.⟨$⟩ʳ x))
                  to from
    where
    R : Fin (suc n) → Fin (suc n) → Set
    R a c = a < c
    to : R (b P.⟨$⟩ʳ y) (b P.⟨$⟩ʳ x) → R (b′ P.⟨$⟩ʳ y) (b′ P.⟨$⟩ʳ x)
    to = subst₂ R (eq y) (eq x)
    from : R (b′ P.⟨$⟩ʳ y) (b′ P.⟨$⟩ʳ x) → R (b P.⟨$⟩ʳ y) (b P.⟨$⟩ʳ x)
    from = subst₂ R (sym (eq y)) (sym (eq x))

invS-resp-≈ : {n : ℕ} {b b′ : FinBij (suc n) (suc n)} → b ≈-fb b′ → invS b ≡ invS b′
invS-resp-≈ {b = b} {b′} eq =
  sumF-cong (λ x → sumF-cong (λ y → invAt-resp-≈ {b = b} {b′} eq x y))

------------------------------------------------------------------------
-- 3. Small arithmetic / order helpers.

sumF-const0 : {N : ℕ} → sumF {N} (λ _ → 0) ≡ 0
sumF-const0 {zero}  = refl
sumF-const0 {suc N} = sumF-const0 {N}

open import Data.Nat.Properties using (<⇒≱; ≰⇒>)
open import Data.Fin.Base using (_≤_)

-- positions: `punchIn m i < punchIn m j  ⟺  i < j`.
punchIn-<-bracket : {N : ℕ} (m : Fin (suc N)) (i j : Fin N)
                  → ⌊ punchIn m i <? punchIn m j ⌋ ≡ ⌊ i <? j ⌋
punchIn-<-bracket m i j =
  dec-cong (punchIn m i <? punchIn m j) (i <? j) to from
  where
  to : punchIn m i < punchIn m j → i < j
  to pi<pj = ≰⇒> (λ j≤i → <⇒≱ pi<pj (punchIn-mono-≤ m j i j≤i))
  from : i < j → punchIn m i < punchIn m j
  from i<j = ≰⇒> (λ pj≤pi → <⇒≱ i<j (punchIn-cancel-≤ m j i pj≤pi))

-- The punch-out bridge:  when `b ⟨$⟩ʳ m ≡ 0F`, the value of `b` at a
-- non-`m` position is `suc` of the corresponding value of `remove m b`.
-- (`punchIn-permute` + `b ⟨$⟩ʳ m = 0F` + `punchIn 0F = suc`.)
remove-bridge : {N : ℕ} (b : FinBij (suc N) (suc N)) (m : Fin (suc N))
              → b P.⟨$⟩ʳ m ≡ 0F
              → ∀ k → b P.⟨$⟩ʳ (punchIn m k) ≡ fsuc (remove m b P.⟨$⟩ʳ k)
remove-bridge b m bm≡0 k =
  trans (P.punchIn-permute b m k)
        (cong (λ z → punchIn z (remove m b P.⟨$⟩ʳ k)) bm≡0)

suc-<-bracket : {N : ℕ} (a c : Fin N) → ⌊ fsuc a <? fsuc c ⌋ ≡ ⌊ a <? c ⌋
suc-<-bracket a c = dec-cong (fsuc a <? fsuc c) (a <? c) s<s⁻¹ s<s
  where open import Data.Nat.Base using (s<s; s<s⁻¹)

-- values: `b ⟨$⟩ʳ (punchIn m j) <? b ⟨$⟩ʳ (punchIn m i)  ⟺  rmb j <? rmb i`.
remove-<-bracket : {N : ℕ} (b : FinBij (suc N) (suc N)) (m : Fin (suc N))
                 → b P.⟨$⟩ʳ m ≡ 0F → (i j : Fin N)
                 → ⌊ (b P.⟨$⟩ʳ (punchIn m j)) <? (b P.⟨$⟩ʳ (punchIn m i)) ⌋
                 ≡ ⌊ (remove m b P.⟨$⟩ʳ j) <? (remove m b P.⟨$⟩ʳ i) ⌋
remove-<-bracket b m bm≡0 i j =
  trans (cong₂ (λ p q → ⌊ p <? q ⌋) (remove-bridge b m bm≡0 j) (remove-bridge b m bm≡0 i))
        (suc-<-bracket (remove m b P.⟨$⟩ʳ j) (remove m b P.⟨$⟩ʳ i))

-- Count of non-`m` positions landing strictly below `m`: exactly `toℕ m`.
countBelow : {N : ℕ} (m : Fin (suc N))
           → sumF (λ i → 1if ⌊ punchIn m i <? m ⌋) ≡ toℕ m
countBelow {zero}  0F       = refl
countBelow {suc N} 0F       = sumF-const0 {suc N}
countBelow {suc N} (fsuc m) =
  cong₂ _+_ refl
    (trans (sumF-cong (λ i → cong 1if (suc-<-bracket (punchIn m i) m)))
           (countBelow m))

------------------------------------------------------------------------
-- 4. The value-0 peel of `invS`:
--   b ⟨$⟩ʳ m ≡ 0F  ⟹  invS b ≡ toℕ m + invS (remove m b).
--
-- Split every position pair by whether it touches `m` (`sumF-punch` at `m`,
-- once per coordinate): the `m`-row contributes 0 (value 0 is never the
-- larger), the `m`-column contributes `toℕ m` (`countBelow`), and the rest
-- reindex order-preservingly to the pairs of `remove m b`.

open import Data.Bool.Properties using (∧-zeroʳ; ∧-identityʳ)

module _ {N : ℕ} (b : FinBij (suc (suc N)) (suc (suc N))) (m : Fin (suc (suc N)))
         (bm≡0 : b P.⟨$⟩ʳ m ≡ 0F) where

  -- the `m`-row vanishes: value 0 is never strictly above another value.
  row-m : ∀ y → invAt b m y ≡ 0
  row-m y =
    trans (cong (λ z → 1if (⌊ m <? y ⌋ ∧ ⌊ (b P.⟨$⟩ʳ y) <? z ⌋))
                bm≡0)
          (cong 1if (∧-zeroʳ ⌊ m <? y ⌋))

  -- the `m`-column at position `punchIn m i`.
  col-m : ∀ i → invAt b (punchIn m i) m ≡ 1if ⌊ punchIn m i <? m ⌋
  col-m i =
    trans (cong (λ z → 1if (⌊ punchIn m i <? m ⌋ ∧ ⌊ z <? (b P.⟨$⟩ʳ (punchIn m i)) ⌋))
                bm≡0)
          (trans (cong (λ z → 1if (⌊ punchIn m i <? m ⌋ ∧ ⌊ fz {suc N} <? z ⌋))
                       (remove-bridge b m bm≡0 i))
                 (cong 1if (∧-identityʳ ⌊ punchIn m i <? m ⌋)))

  -- the remaining pairs reindex to the pairs of `remove m b`.
  inner-m : ∀ i j → invAt b (punchIn m i) (punchIn m j) ≡ invAt (remove m b) i j
  inner-m i j =
    cong₂ (λ p q → 1if (p ∧ q))
          (punchIn-<-bracket m i j)
          (remove-<-bracket b m bm≡0 i j)

  -- the `m`-row `sumF (λ y → invAt b m y)` is `0`.
  Rm≡0 : sumF (λ y → invAt b m y) ≡ 0
  Rm≡0 = trans (sumF-cong row-m) (sumF-const0 {suc (suc N)})

  invS-peel : invS b ≡ toℕ m + invS (remove m b)
  invS-peel =
    -- outer punch at m, drop the vanishing `m`-row, then `goal`.
    trans (sumF-punch (λ x → sumF (λ y → invAt b x y)) m)
          (trans (cong (_+ sumF Rrow) Rm≡0) goal)
    where
    Rrow : Fin (suc N) → ℕ
    Rrow i = sumF (λ y → invAt b (punchIn m i) y)

    Rrow-split : ∀ i → Rrow i
               ≡ invAt b (punchIn m i) m
                 + sumF (λ j → invAt b (punchIn m i) (punchIn m j))
    Rrow-split i = sumF-punch (λ y → invAt b (punchIn m i) y) m

    goal : sumF Rrow ≡ toℕ m + invS (remove m b)
    goal =
      trans (sumF-cong Rrow-split)
      (trans (sumF-+ (λ i → invAt b (punchIn m i) m)
                     (λ i → sumF (λ j → invAt b (punchIn m i) (punchIn m j))))
             (cong₂ _+_
               (trans (sumF-cong col-m) (countBelow m))
               (sumF-cong (λ i → sumF-cong (λ j → inner-m i j)))))

------------------------------------------------------------------------
-- 5. The `inv`-residual is `remove m b` (`m = b ⟨$⟩ˡ 0F`): the inverse
-- rotation sends `suc j` to `punchIn m j`, so `b ∘-fb inv-fb ρ` reads `b`
-- skipping `m`.

-- The inverse rotation, off the front, is `punchIn m`.
rotate-punchIn : {N : ℕ} (m : Fin (suc N)) (j : Fin N)
               → rotate-fb m P.⟨$⟩ˡ fsuc j ≡ punchIn m j
rotate-punchIn         0F        j        = refl
rotate-punchIn {suc N} (fsuc m)  0F       = refl
rotate-punchIn {suc N} (fsuc m)  (fsuc j) =
  cong fsuc (rotate-punchIn m j)

open import Categories.PermuteCoherence.Word using (inv-rotate-fb-0)

-- The `inv`-residual equals `remove m b` (pointwise).  `c = b ∘-fb inv-fb
-- ρ` fixes `0F`, so `lift₀-remove` + rotate-punchIn + remove-bridge give
-- `suc (rest j) ≡ suc (remove m b j)`; strip the `suc`.
rest≈remove-m
  : {n : ℕ} (b : FinBij (suc (suc n)) (suc (suc n)))
  → remove 0F (b ∘-fb inv-fb (rotate-fb (b P.⟨$⟩ˡ 0F))) ≈-fb remove (b P.⟨$⟩ˡ 0F) b
rest≈remove-m {n} b j = suc-injective suc-eq
  where
  m  = b P.⟨$⟩ˡ 0F
  ρ  = rotate-fb m
  c  = b ∘-fb inv-fb ρ

  bm≡0 : b P.⟨$⟩ʳ m ≡ 0F
  bm≡0 = P.inverseʳ b

  fix0 : c P.⟨$⟩ʳ 0F ≡ 0F
  fix0 = trans (cong (b P.⟨$⟩ʳ_) (inv-rotate-fb-0 m)) (P.inverseʳ b)

  c-suc : c P.⟨$⟩ʳ fsuc j ≡ b P.⟨$⟩ʳ (punchIn m j)
  c-suc = cong (b P.⟨$⟩ʳ_) (rotate-punchIn m j)

  suc-eq : fsuc (remove 0F c P.⟨$⟩ʳ j) ≡ fsuc (remove m b P.⟨$⟩ʳ j)
  suc-eq =
    trans (P.lift₀-remove c fix0 (fsuc j))
          (trans c-suc (remove-bridge b m bm≡0 j))

------------------------------------------------------------------------
-- 6. The Lehmer recursion of `invS`, and the bridge `invS ≡ inv`.

invS-rec : {n : ℕ} (b : FinBij (suc (suc n)) (suc (suc n)))
         → invS b
         ≡ invS (remove 0F (b ∘-fb inv-fb (rotate-fb (b P.⟨$⟩ˡ 0F))))
           + toℕ (b P.⟨$⟩ˡ 0F)
invS-rec {n} b =
  trans (invS-peel b m (P.inverseʳ b {0F}))
        (trans (+-comm (toℕ m) (invS (remove m b)))
               (cong (_+ toℕ m)
                     (sym (invS-resp-≈ {b = rest} {b′ = remove m b}
                                       (rest≈remove-m b)))))
  where
  m    = b P.⟨$⟩ˡ 0F
  rest = remove 0F (b ∘-fb inv-fb (rotate-fb m))

-- `invS` equals the recursive (Lehmer) inversion count `inv`.
opaque
  unfolding inv
  invS≡inv : {n : ℕ} (b : FinBij (suc n) (suc n)) → invS b ≡ inv b
  invS≡inv {zero}  b = refl
  invS≡inv {suc n} b =
    trans (invS-rec b)
          (cong (_+ toℕ (b P.⟨$⟩ˡ 0F))
                (invS≡inv (remove 0F (b ∘-fb inv-fb (rotate-fb (b P.⟨$⟩ˡ 0F))))))
