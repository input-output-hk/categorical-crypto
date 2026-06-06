{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The descent dichotomy for the sum-of-inversions count `invS`.
--
-- Post-composing a finite bijection `b` with an adjacent-transposition
-- generator `genFB i` (which swaps the two VALUES `i` and `i+1`) changes
-- the inversion count `invS` by EXACTLY ONE, with the sign determined by
-- whether the position holding value `i` is before or after the position
-- holding value `i+1`:
--
--   * ascent  (pos i < pos i+1):  invS (genFB i ∘-fb b) ≡ suc (invS b)
--   * descent (pos i+1 < pos i):  suc (invS (genFB i ∘-fb b)) ≡ invS b
--
-- Proof structure:
--   1. `genFB-toℕ`  — `toℕ (genFB i ⟨$⟩ʳ z) ≡ swapℕ (toℕ i) (toℕ z)`,
--      where `swapℕ k` is the ℕ-level adjacent transposition of `k,k+1`.
--      Induction on `i`, matching `genFB`'s `swap-fb`/`cons-fb` recursion.
--   2. `swapℕ-cmp-*` — the arithmetic core: `swapℕ k` flips the `<?`
--      comparison of `a,b` exactly when `{a,b} = {k, suc k}`, and leaves
--      it unchanged otherwise.  Induction on `k`.
--   3. `invAt`-agreement off the swapped position-pair, then two nested
--      `sumF-step`s (one inner, one outer) to read off the ± 1.
------------------------------------------------------------------------

module Categories.PermuteCoherence.InversionsDichotomy where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n; s<s; s≤s⁻¹)
open import Data.Nat.Properties using (1+n≰n; <⇒≤; <-cmp; <-asym)
  renaming (suc-injective to sucℕ-injective; _≟_ to _≟ℕ_; _<?_ to _<?ℕ_; ≤-refl to ≤ℕ-refl)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Function.Base using (_∘′_)
open import Data.Fin.Base using (Fin; toℕ; inject₁) renaming (suc to fsuc; zero to fz)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-injective)
  renaming (suc-injective to fsuc-injective; _<?_ to _<?F_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; isYes≗does; dec-true; dec-false)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Bool.Base using (Bool; true; false; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

import Data.Fin.Permutation as P
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _∘-fb_; swap-fb; cons-fb)
open import Categories.PermuteCoherence.Word using (genFB)
open import Categories.PermuteCoherence.InversionsSum
  using (sumF; sumF-cong; sumF-+; sumF-step; invAt; invS; 1if)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- 0.  The two values `genFB i` transposes: `i` and `i+1`.

inj : Fin (suc n) → Fin (suc (suc n))
inj i = inject₁ i

suc-pos : Fin (suc n) → Fin (suc (suc n))
suc-pos i = fsuc i

toℕ-inj : (i : Fin (suc n)) → toℕ (inj i) ≡ toℕ i
toℕ-inj i = toℕ-inject₁ i

toℕ-suc-pos : (i : Fin (suc n)) → toℕ (suc-pos i) ≡ suc (toℕ i)
toℕ-suc-pos i = refl

------------------------------------------------------------------------
-- 1.  The ℕ-level adjacent transposition and `genFB`'s action on `toℕ`.

-- `swapℕ k` swaps `k` and `suc k`, fixing all other naturals; recursion
-- arranged to mirror `genFB`'s `swap-fb`/`cons-fb` split.
swapℕ : ℕ → ℕ → ℕ
swapℕ zero    zero          = 1
swapℕ zero    (suc zero)    = 0
swapℕ zero    (suc (suc m)) = suc (suc m)
swapℕ (suc k) zero          = 0
swapℕ (suc k) (suc m)       = suc (swapℕ k m)

-- `genFB i ⟨$⟩ʳ` acts on `toℕ` exactly as `swapℕ (toℕ i)`.
genFB-toℕ : (i : Fin (suc n)) (z : Fin (suc (suc n)))
          → toℕ (genFB i P.⟨$⟩ʳ z) ≡ swapℕ (toℕ i) (toℕ z)
genFB-toℕ {n} 0F 0F             = refl
genFB-toℕ {n} 0F (fsuc 0F)      = refl
genFB-toℕ {n} 0F (fsuc (fsuc z)) = refl
genFB-toℕ {suc n} (fsuc i) 0F        = refl
genFB-toℕ {suc n} (fsuc i) (fsuc z) = cong suc (genFB-toℕ i z)

------------------------------------------------------------------------
-- 2.  The arithmetic core.
--
-- `swapℕ k` flips the `<?` comparison of `a,b` exactly when
-- `{a,b} = {k, suc k}`; otherwise the comparison is unchanged.

-- The Boolean comparison and its reflection.
cmpB : ℕ → ℕ → Bool
cmpB a b = ⌊ a <?ℕ b ⌋

cmpB-true : {a b : ℕ} → a < b → cmpB a b ≡ true
cmpB-true {a} {b} a<b = trans (isYes≗does (a <?ℕ b)) (dec-true (a <?ℕ b) a<b)

cmpB-false : {a b : ℕ} → ¬ (a < b) → cmpB a b ≡ false
cmpB-false {a} {b} ¬a<b = trans (isYes≗does (a <?ℕ b)) (dec-false (a <?ℕ b) ¬a<b)

-- A decision of `a < b` as plain data, WITHOUT exposing `cmpB`'s internal
-- `<?` term (which would entangle the goal during case analysis).
data Dec< (a b : ℕ) : Set where
  is<  : a < b → Dec< a b
  not< : ¬ (a < b) → Dec< a b

dec< : (a b : ℕ) → Dec< a b
dec< a b with <-cmp a b
... | tri< a<b _ _ = is< a<b
... | tri≈ ¬a<b _ _ = not< ¬a<b
... | tri> ¬a<b _ _ = not< ¬a<b

-- `cmpB` depends only on the underlying `<` proposition.
cmpB-iff : {a b c d : ℕ} → (a < b → c < d) → (c < d → a < b)
         → cmpB a b ≡ cmpB c d
cmpB-iff {a} {b} {c} {d} fwd bwd with dec< a b
... | is<  a<b = trans (cmpB-true a<b) (sym (cmpB-true (fwd a<b)))
... | not< ¬a<b = trans (cmpB-false ¬a<b) (sym (cmpB-false (¬a<b ∘′ bwd)))

-- Shift both arguments by one.
cmpB-suc : (a b : ℕ) → cmpB (suc a) (suc b) ≡ cmpB a b
cmpB-suc a b = cmpB-iff s≤s⁻¹ s<s

-- `swapℕ k` swaps the two adjacent values `k` and `suc k`.
swapℕ-k : (k : ℕ) → swapℕ k k ≡ suc k
swapℕ-k zero    = refl
swapℕ-k (suc k) = cong suc (swapℕ-k k)

swapℕ-sk : (k : ℕ) → swapℕ k (suc k) ≡ k
swapℕ-sk zero    = refl
swapℕ-sk (suc k) = cong suc (swapℕ-sk k)

-- The membership/swapped-pair predicate (at ℕ level).
SwapPair : ℕ → ℕ → ℕ → Set
SwapPair k a b = (a ≡ k × b ≡ suc k) ⊎ (a ≡ suc k × b ≡ k)

-- ¬ (suc k < k) and k < suc k.
¬suc<self : (k : ℕ) → ¬ (suc k < k)
¬suc<self k h = 1+n≰n (<⇒≤ h)

self<suc : (k : ℕ) → k < suc k
self<suc k = ≤ℕ-refl

-- The FLIP at the swapped pair.
swapℕ-flip : (k a b : ℕ) → SwapPair k a b
           → cmpB (swapℕ k a) (swapℕ k b) ≡ not (cmpB a b)
swapℕ-flip k .k .(suc k) (inj₁ (refl , refl)) =
  trans (cong₂ cmpB (swapℕ-k k) (swapℕ-sk k))
        (trans (cmpB-false (¬suc<self k))
               (sym (cong not (cmpB-true (self<suc k)))))
swapℕ-flip k .(suc k) .k (inj₂ (refl , refl)) =
  trans (cong₂ cmpB (swapℕ-sk k) (swapℕ-k k))
        (trans (cmpB-true (self<suc k))
               (sym (cong not (cmpB-false (¬suc<self k)))))

-- Comparison against a value outside {k, suc k} is unchanged.
swapℕ-fix : (k a b : ℕ) → a ≢ b → ¬ SwapPair k a b
          → cmpB (swapℕ k a) (swapℕ k b) ≡ cmpB a b
swapℕ-fix zero zero zero a≢b _ = ⊥-elim (a≢b refl)
swapℕ-fix zero zero (suc zero) _ ¬sp = ⊥-elim (¬sp (inj₁ (refl , refl)))
swapℕ-fix zero zero (suc (suc m)) _ _ =
  trans (cmpB-true {1} {suc (suc m)} (s<s (s≤s z≤n)))
        (sym (cmpB-true {0} {suc (suc m)} (s≤s z≤n)))
swapℕ-fix zero (suc zero) zero _ ¬sp = ⊥-elim (¬sp (inj₂ (refl , refl)))
swapℕ-fix zero (suc zero) (suc zero) a≢b _ = ⊥-elim (a≢b refl)
swapℕ-fix zero (suc zero) (suc (suc m)) _ _ =
  trans (cmpB-true {0} {suc (suc m)} (s≤s z≤n))
        (sym (cmpB-true {1} {suc (suc m)} (s<s (s≤s z≤n))))
swapℕ-fix zero (suc (suc m)) zero _ _ =
  trans (cmpB-false {suc (suc m)} {1} (λ { (s≤s ()) }))
        (sym (cmpB-false {suc (suc m)} {0} (λ ())))
swapℕ-fix zero (suc (suc m)) (suc zero) _ _ =
  trans (cmpB-false {suc (suc m)} {0} (λ ()))
        (sym (cmpB-false {suc (suc m)} {1} (λ { (s≤s ()) })))
swapℕ-fix zero (suc (suc m)) (suc (suc m′)) _ _ = refl
swapℕ-fix (suc k) zero zero a≢b _ = ⊥-elim (a≢b refl)
swapℕ-fix (suc k) zero (suc b) _ _ =
  trans (cmpB-true {0} {suc (swapℕ k b)} (s≤s z≤n))
        (sym (cmpB-true {0} {suc b} (s≤s z≤n)))
swapℕ-fix (suc k) (suc a) zero _ _ =
  trans (cmpB-false {suc (swapℕ k a)} {0} (λ ()))
        (sym (cmpB-false {suc a} {0} (λ ())))
swapℕ-fix (suc k) (suc a) (suc b) a≢b ¬sp =
  trans (cmpB-suc (swapℕ k a) (swapℕ k b))
        (trans (swapℕ-fix k a b (a≢b ∘′ cong suc) (¬sp ∘′ liftSP))
               (sym (cmpB-suc a b)))
  where
  liftSP : SwapPair k a b → SwapPair (suc k) (suc a) (suc b)
  liftSP (inj₁ (refl , refl)) = inj₁ (refl , refl)
  liftSP (inj₂ (refl , refl)) = inj₂ (refl , refl)

------------------------------------------------------------------------
-- 3.  From the arithmetic core to `invAt`.

private
  variable
    n′ : ℕ

-- Right-action injectivity (from the left-inverse law).
⟨$⟩ʳ-inj : (b : FinBij (suc (suc n)) (suc (suc n))) {x y : Fin (suc (suc n))}
         → b P.⟨$⟩ʳ x ≡ b P.⟨$⟩ʳ y → x ≡ y
⟨$⟩ʳ-inj b {x} {y} eq =
  trans (sym (P.inverseˡ b)) (trans (cong (b P.⟨$⟩ˡ_) eq) (P.inverseˡ b))

-- The second conjunct of `invAt`, isolated.
cmpInv : FinBij (suc n) (suc n) → Fin (suc n) → Fin (suc n) → Bool
cmpInv b x y = ⌊ (b P.⟨$⟩ʳ y) <?F (b P.⟨$⟩ʳ x) ⌋

-- `invAt` is `1if` of the first (`c`-independent) conjunct AND `cmpInv`.
invAt-split : (b : FinBij (suc n) (suc n)) (x y : Fin (suc n))
            → invAt b x y ≡ 1if (⌊ x <?F y ⌋ ∧ cmpInv b x y)
invAt-split b x y = refl

-- OFF the swapped value-pair (at distinct positions), `cmpInv` is
-- unchanged by post-composing with `genFB i`.
cmpInv-fix : (i : Fin (suc n′)) (b : FinBij (suc (suc n′)) (suc (suc n′)))
             {x y : Fin (suc (suc n′))} → x ≢ y
           → ¬ SwapPair (toℕ i) (toℕ (b P.⟨$⟩ʳ y)) (toℕ (b P.⟨$⟩ʳ x))
           → cmpInv (genFB i ∘-fb b) x y ≡ cmpInv b x y
cmpInv-fix i b {x} {y} x≢y ¬sp =
  trans (cong₂ cmpB (genFB-toℕ i (b P.⟨$⟩ʳ y)) (genFB-toℕ i (b P.⟨$⟩ʳ x)))
        (swapℕ-fix (toℕ i) (toℕ (b P.⟨$⟩ʳ y)) (toℕ (b P.⟨$⟩ʳ x)) a≢b ¬sp)
  where
  a≢b : toℕ (b P.⟨$⟩ʳ y) ≢ toℕ (b P.⟨$⟩ʳ x)
  a≢b e = x≢y (sym (⟨$⟩ʳ-inj b (toℕ-injective e)))

------------------------------------------------------------------------
-- 4.  `invAt`-level agreement off the swapped pair, and the flip on it.

-- Reverse bridge: a `true` comparison yields the `<` witness.
cmpB-true⁻ : {a b : ℕ} → cmpB a b ≡ true → a < b
cmpB-true⁻ {a} {b} eq with dec< a b
... | is<  a<b  = a<b
... | not< ¬a<b = ⊥-elim (true≢false (trans (sym eq) (cmpB-false ¬a<b)))
  where
  true≢false : true ≢ false
  true≢false ()

-- `1if (p ∧ _)` only depends on the second conjunct when `p ≡ true`.
1if-∧-cong : (p : Bool) {q₁ q₂ : Bool} → (p ≡ true → q₁ ≡ q₂)
           → 1if (p ∧ q₁) ≡ 1if (p ∧ q₂)
1if-∧-cong true  h = cong (λ z → 1if (true ∧ z)) (h refl)
1if-∧-cong false _ = refl

-- `invAt` is unchanged whenever the pair, *when it is an ordered pair*
-- `x < y`, is not the swapped value-pair.  (For `x ≮ y` both counts are
-- 0, so the `¬ SwapPair` hypothesis is only required under `x < y`.)
invAt-agree : (i : Fin (suc n′)) (b : FinBij (suc (suc n′)) (suc (suc n′)))
              (x y : Fin (suc (suc n′)))
            → (⌊ x <?F y ⌋ ≡ true
                → ¬ SwapPair (toℕ i) (toℕ (b P.⟨$⟩ʳ y)) (toℕ (b P.⟨$⟩ʳ x)))
            → invAt (genFB i ∘-fb b) x y ≡ invAt b x y
invAt-agree i b x y ¬sp =
  1if-∧-cong ⌊ x <?F y ⌋
    (λ x<y → cmpInv-fix i b (λ e → <⇒≢ℕ (cmpB-true⁻ x<y) (cong toℕ e)) (¬sp x<y))
  where
  <⇒≢ℕ : {a c : ℕ} → a < c → a ≢ c
  <⇒≢ℕ a<c refl = 1+n≰n a<c

------------------------------------------------------------------------
-- 5.  The double `sumF-step`.

-- Two nested `sumF-step`s: if the matrices `F`, `G` agree everywhere
-- except a single cell `(x₀, y₀)` where `F x₀ y₀ = suc (G x₀ y₀)`, then
-- their double sums differ by one.
double-step :
    {N : ℕ} (F G : Fin N → Fin N → ℕ) (x₀ y₀ : Fin N)
  → (∀ x → x ≢ x₀ → ∀ y → F x y ≡ G x y)
  → (∀ y → y ≢ y₀ → F x₀ y ≡ G x₀ y)
  → F x₀ y₀ ≡ suc (G x₀ y₀)
  → sumF (λ x → sumF (F x)) ≡ suc (sumF (λ x → sumF (G x)))
double-step F G x₀ y₀ offRow inRow atCell =
  sumF-step (λ x → sumF (F x)) (λ x → sumF (G x)) x₀
    (λ x x≢x₀ → sumF-cong (offRow x x≢x₀))
    (sumF-step (F x₀) (G x₀) y₀ inRow atCell)

------------------------------------------------------------------------
-- 6.  Locating the unique flipped pair, and the assembled dichotomy.

module _ (i : Fin (suc n′)) (b : FinBij (suc (suc n′)) (suc (suc n′))) where

  private
    c = genFB i ∘-fb b
    k = toℕ i
    pk  = b P.⟨$⟩ˡ inj i       -- position of value `i`     (toℕ ≡ k)
    psk = b P.⟨$⟩ˡ suc-pos i   -- position of value `i+1`   (toℕ ≡ suc k)

  -- The values actually sitting at `pk` / `psk`.
  bpk : toℕ (b P.⟨$⟩ʳ pk) ≡ k
  bpk = trans (cong toℕ (P.inverseʳ b)) (toℕ-inj i)

  bpsk : toℕ (b P.⟨$⟩ʳ psk) ≡ suc k
  bpsk = trans (cong toℕ (P.inverseʳ b)) (toℕ-suc-pos i)

  -- A position holding value `k` is `pk`; value `suc k` is `psk`.
  from-k : {z : Fin (suc (suc n′))} → toℕ (b P.⟨$⟩ʳ z) ≡ k → z ≡ pk
  from-k {z} e = sym (⟨$⟩ʳ-inj b (toℕ-injective (trans bpk (sym e))))

  from-sk : {z : Fin (suc (suc n′))} → toℕ (b P.⟨$⟩ʳ z) ≡ suc k → z ≡ psk
  from-sk {z} e = sym (⟨$⟩ʳ-inj b (toℕ-injective (trans bpsk (sym e))))

  -- `x < y` at an ordered pair gives `invAt` as a single `cmpB`.
  invAt-pair : (d : FinBij (suc (suc n′)) (suc (suc n′)))
               {x y : Fin (suc (suc n′))} → toℕ x < toℕ y
             → invAt d x y ≡ 1if (cmpB (toℕ (d P.⟨$⟩ʳ y)) (toℕ (d P.⟨$⟩ʳ x)))
  invAt-pair d {x} {y} x<y =
    cong (λ z → 1if (z ∧ cmpB (toℕ (d P.⟨$⟩ʳ y)) (toℕ (d P.⟨$⟩ʳ x))))
         (cmpB-true {toℕ x} {toℕ y} x<y)

  -- `k ≢ suc k`.
  k≢sk : k ≢ suc k
  k≢sk e = 1+n≰n (subst (suc k ≤_) (sym e) ≤ℕ-refl)

  ----------------------------------------------------------------------
  -- A `SwapPair` at positions `(x, y)` forces `{x, y} = {pk, psk}`.

  unique : {x y : Fin (suc (suc n′))}
         → SwapPair k (toℕ (b P.⟨$⟩ʳ y)) (toℕ (b P.⟨$⟩ʳ x))
         → (x ≡ pk × y ≡ psk) ⊎ (x ≡ psk × y ≡ pk)
  unique (inj₁ (yk , xsk)) = inj₂ (from-sk xsk , from-k yk)
  unique (inj₂ (ysk , xk)) = inj₁ (from-k xk , from-sk ysk)

  ----------------------------------------------------------------------
  -- The flipped cell, both orderings.

  -- `c`'s image-`toℕ` is `swapℕ k` of `b`'s.
  c-toℕ : (z : Fin (suc (suc n′))) → toℕ (c P.⟨$⟩ʳ z) ≡ swapℕ k (toℕ (b P.⟨$⟩ʳ z))
  c-toℕ z = genFB-toℕ i (b P.⟨$⟩ʳ z)

  invAtb-asc : toℕ pk < toℕ psk → invAt b pk psk ≡ 0
  invAtb-asc o =
    trans (invAt-pair b o)
          (cong 1if (trans (cong₂ cmpB bpsk bpk) (cmpB-false (¬suc<self k))))

  invAtc-asc : toℕ pk < toℕ psk → invAt c pk psk ≡ 1
  invAtc-asc o =
    trans (invAt-pair c o)
          (cong 1if (trans (cong₂ cmpB (trans (c-toℕ psk) (trans (cong (swapℕ k) bpsk) (swapℕ-sk k)))
                                       (trans (c-toℕ pk)  (trans (cong (swapℕ k) bpk)  (swapℕ-k k))))
                           (cmpB-true (self<suc k))))

  invAtb-desc : toℕ psk < toℕ pk → invAt b psk pk ≡ 1
  invAtb-desc o =
    trans (invAt-pair b o)
          (cong 1if (trans (cong₂ cmpB bpk bpsk) (cmpB-true (self<suc k))))

  invAtc-desc : toℕ psk < toℕ pk → invAt c psk pk ≡ 0
  invAtc-desc o =
    trans (invAt-pair c o)
          (cong 1if (trans (cong₂ cmpB (trans (c-toℕ pk)  (trans (cong (swapℕ k) bpk)  (swapℕ-k k)))
                                       (trans (c-toℕ psk) (trans (cong (swapℕ k) bpsk) (swapℕ-sk k))))
                           (cmpB-false (¬suc<self k))))

  pk≢psk : pk ≢ psk
  pk≢psk e = k≢sk (trans (sym bpk) (trans (cong (λ z → toℕ (b P.⟨$⟩ʳ z)) e) bpsk))

  ----------------------------------------------------------------------
  -- 7.  The two assembled directions.

  -- ascent: pk < psk  ⇒  invS c ≡ suc (invS b).
  invS-ascent : toℕ pk < toℕ psk → invS c ≡ suc (invS b)
  invS-ascent asc =
    double-step (invAt c) (invAt b) pk psk offRow inRow atCell
    where
    offRow : (x : Fin (suc (suc n′))) → x ≢ pk
           → (y : Fin (suc (suc n′))) → invAt c x y ≡ invAt b x y
    offRow x x≢pk y = invAt-agree i b x y λ x<y → ¬sp (cmpB-true⁻ x<y)
      where
      ¬sp : toℕ x < toℕ y → ¬ SwapPair k (toℕ (b P.⟨$⟩ʳ y)) (toℕ (b P.⟨$⟩ʳ x))
      ¬sp x<y sp with unique sp
      ... | inj₁ (x≡pk , _)     = x≢pk x≡pk
      ... | inj₂ (refl , refl)  = <-asym asc x<y
    inRow : (y : Fin (suc (suc n′))) → y ≢ psk → invAt c pk y ≡ invAt b pk y
    inRow y y≢psk = invAt-agree i b pk y λ x<y → ¬sp
      where
      ¬sp : ¬ SwapPair k (toℕ (b P.⟨$⟩ʳ y)) (toℕ (b P.⟨$⟩ʳ pk))
      ¬sp sp with unique sp
      ... | inj₁ (_ , y≡psk)    = y≢psk y≡psk
      ... | inj₂ (pk≡psk , _)   = pk≢psk pk≡psk
    atCell : invAt c pk psk ≡ suc (invAt b pk psk)
    atCell = trans (invAtc-asc asc) (cong suc (sym (invAtb-asc asc)))

  -- descent: psk < pk  ⇒  suc (invS c) ≡ invS b.
  invS-descent : toℕ psk < toℕ pk → suc (invS c) ≡ invS b
  invS-descent desc =
    sym (double-step (invAt b) (invAt c) psk pk offRow inRow atCell)
    where
    offRow : (x : Fin (suc (suc n′))) → x ≢ psk
           → (y : Fin (suc (suc n′))) → invAt b x y ≡ invAt c x y
    offRow x x≢psk y = sym (invAt-agree i b x y λ x<y → ¬sp (cmpB-true⁻ x<y))
      where
      ¬sp : toℕ x < toℕ y → ¬ SwapPair k (toℕ (b P.⟨$⟩ʳ y)) (toℕ (b P.⟨$⟩ʳ x))
      ¬sp x<y sp with unique sp
      ... | inj₁ (refl , refl)  = <-asym desc x<y
      ... | inj₂ (x≡psk , _)    = x≢psk x≡psk
    inRow : (y : Fin (suc (suc n′))) → y ≢ pk → invAt b psk y ≡ invAt c psk y
    inRow y y≢pk = sym (invAt-agree i b psk y λ x<y → ¬sp)
      where
      ¬sp : ¬ SwapPair k (toℕ (b P.⟨$⟩ʳ y)) (toℕ (b P.⟨$⟩ʳ psk))
      ¬sp sp with unique sp
      ... | inj₁ (psk≡pk , _)   = pk≢psk (sym psk≡pk)
      ... | inj₂ (_ , y≡pk)     = y≢pk y≡pk
    atCell : invAt b psk pk ≡ suc (invAt c psk pk)
    atCell = trans (invAtb-desc desc) (cong suc (sym (invAtc-desc desc)))

------------------------------------------------------------------------
-- 8.  The packaged dichotomy.  The sign is stated via `toℕ`-comparison
-- of the two positions, which is the `Fin` `_<_` by definition.

invS-dichotomy :
    (i : Fin (suc n)) (b : FinBij (suc (suc n)) (suc (suc n)))
  → (toℕ (b P.⟨$⟩ˡ inj i) < toℕ (b P.⟨$⟩ˡ suc-pos i)
        → invS (genFB i ∘-fb b) ≡ suc (invS b))
  × (toℕ (b P.⟨$⟩ˡ suc-pos i) < toℕ (b P.⟨$⟩ˡ inj i)
        → suc (invS (genFB i ∘-fb b)) ≡ invS b)
invS-dichotomy i b = invS-ascent i b , invS-descent i b
