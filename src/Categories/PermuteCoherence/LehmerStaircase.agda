{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Lehmer-peel staircase identities for `insert-thm`, in the real
-- Coxeter word relation `_~ʷ_`.
--
-- These are the two combinatorial identities the direct (Lehmer-peel)
-- proof of `insert-thm` rests on, replacing the exchange-condition /
-- Matsumoto tower (`Inversions*`, `ExchangeBase`, `BringToFront*`,
-- `InsertProof{Base,Matsumoto}`).  Both are derived from the three
-- Coxeter relations `c1`/`c2`/`c3` alone.
--
-- The identities concatenate ascending runs of DIFFERENT lengths; the
-- ambient bound `N` is held FIXED and runs are built with `fromℕ<`
-- (`runF`, whose bound argument is irrelevant).  Because a run is
-- parameterised by its base `s` directly, the base-incrementing step of
-- the induction is a plain recursive call `stairBW (suc s)` — no
-- `map suc`/`shift` bookkeeping is needed.
------------------------------------------------------------------------

module Categories.PermuteCoherence.LehmerStaircase where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; s≤s; _<_; _+_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; n≤1+n; m≤m+n; +-suc; +-monoʳ-≤)
open import Data.Fin.Base using (fromℕ<) renaming (suc to fsuc)
open import Data.Fin.Patterns using (0F)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; trans; subst)

open import Categories.PermuteCoherence.Word

private
  variable
    n N : ℕ

------------------------------------------------------------------------
-- 0. Structural glue for `_~ʷ_` (Word ships only `++c-r`).

-- Left-concatenation congruence.
++c-l : (u : Word n) {v w : Word n} → v ~ʷ w → (u ++ v) ~ʷ (u ++ w)
++c-l []      r = r
++c-l (i ∷ u) r = ∷-cong i (++c-l u r)

-- `liftW` distributes over `_++_` (definitional, stated for reuse).
liftW-++ : (v w : Word n) → liftW (v ++ w) ≡ liftW v ++ liftW w
liftW-++ []      w = refl
liftW-++ (i ∷ v) w = cong (fsuc i ∷_) (liftW-++ v w)

-- The c2 engine `comm₀`: a leading `0F` commutes right past a
-- doubly-lifted word (all letters ≥ 2), using c2 (far0ˡ) only.
comm₀ : (u : Word n) (v : Word (suc (suc n)))
      → (0F ∷ (liftW (liftW u) ++ v)) ~ʷ (liftW (liftW u) ++ (0F ∷ v))
comm₀ []      v = ~refl
comm₀ (i ∷ u) v = ~trans (c2 far0ˡ) (∷-cong (fsuc (fsuc i)) (comm₀ u v))

------------------------------------------------------------------------
-- 1. `Far`/`Adj` transfer: the numeric side-conditions of the Coxeter
-- relations, phrased on `fromℕ<`-letters.

-- `Far (fromℕ< s<N) (fromℕ< b<N)` whenever `s + 2 ≤ b`.  Bounds are
-- relevant so the impossible small-`N` cases can be discharged.
farℕ→Far : ∀ (s b : ℕ) (s<N : s < N) (b<N : b < N)
         → suc (suc s) ≤ b → Far {N} (fromℕ< s<N) (fromℕ< b<N)
farℕ→Far zero    (suc (suc b)) (s≤s _)   (s≤s (s≤s _))   (s≤s (s≤s _)) = far0ˡ
farℕ→Far (suc s) (suc b)       (s≤s s<N) (s≤s b<N)       (s≤s le)      =
  farS (farℕ→Far s b s<N b<N le)

-- `Adj (fromℕ< s<N) (fromℕ< (1+s)<N)` (the braid triple `(s , suc s)`).
adjℕ→Adj : ∀ (s : ℕ) (s<N : s < N) (ss<N : suc s < N)
         → Adj {N} (fromℕ< s<N) (fromℕ< ss<N)
adjℕ→Adj zero    (s≤s _)   (s≤s (s≤s _)) = adj0
adjℕ→Adj (suc s) (s≤s s<N) (s≤s ss<N)    = adjS (adjℕ→Adj s s<N ss<N)

------------------------------------------------------------------------
-- 2. The Fin-level ascending run `runF s ℓ = [s, s+1, …, s+ℓ−1]`, at a
-- FIXED ambient `N`.  Bounds are irrelevant, so the term does not depend
-- on which proofs are supplied.

-- Arithmetic: the head/tail bounds of a run of length `suc ℓ`.
head< : ∀ {N} (s ℓ : ℕ) → s + suc ℓ ≤ N → s < N
head< {N} s ℓ le = ≤-trans (s≤s (m≤m+n s ℓ)) (subst (λ z → z ≤ N) (+-suc s ℓ) le)

tail≤ : ∀ {N} (s ℓ : ℕ) → s + suc ℓ ≤ N → suc s + ℓ ≤ N
tail≤ {N} s ℓ le = subst (λ z → z ≤ N) (+-suc s ℓ) le

runF : (s ℓ : ℕ) → .(s + ℓ ≤ N) → Word N
runF s zero    _  = []
runF s (suc ℓ) le = fromℕ< (head< s ℓ le) ∷ runF (suc s) ℓ (tail≤ s ℓ le)

------------------------------------------------------------------------
-- 3. The c2 engine: a letter `s` commutes past a run whose base is
-- `≥ s + 2`.  Uses `c2` only.

commLW : ∀ (s b k : ℕ) (w : Word N) (s<N : s < N) (bk : b + k ≤ N)
       → suc (suc s) ≤ b
       → (fromℕ< s<N ∷ (runF b k bk ++ w)) ~ʷ (runF b k bk ++ (fromℕ< s<N ∷ w))
commLW s b zero    w s<N bk le = ~refl
commLW s b (suc k) w s<N bk le =
  ~trans (c2 (farℕ→Far s b s<N (head< b k bk) le))
         (∷-cong (fromℕ< (head< b k bk))
                 (commLW s (suc b) k w s<N (tail≤ b k bk) (≤-trans le (n≤1+n b))))

------------------------------------------------------------------------
-- 4. Bound arithmetic for the staircase statements.  All are consumed
-- only in irrelevant `runF` positions or as relevant inputs to the c2
-- engine, so their precise proofs never matter for the result type.

bnd-m : ∀ {N} (s m r : ℕ) → m ≤ r → s + suc r ≤ N → s + m ≤ N
bnd-m s m r m≤r sr = ≤-trans (+-monoʳ-≤ s (≤-trans m≤r (n≤1+n r))) sr

bnd-sm : ∀ {N} (s m r : ℕ) → m ≤ r → s + suc r ≤ N → suc s + m ≤ N
bnd-sm {N} s m r m≤r sr =
  subst (λ z → z ≤ N) (+-suc s m) (≤-trans (+-monoʳ-≤ s (s≤s m≤r)) sr)

------------------------------------------------------------------------
-- 5. STAIRCASE IDENTITY (B) (r ≥ m):
--    runF s (r+1) ++ runF s m  ~ʷ  runF (s+1) m ++ runF s (r+1)

stairBW : ∀ {N} (s m r : ℕ) (m≤r : m ≤ r) (sr : s + suc r ≤ N)
        → (runF s (suc r) sr ++ runF s m (bnd-m s m r m≤r sr))
          ~ʷ (runF (suc s) m (bnd-sm s m r m≤r sr) ++ runF s (suc r) sr)
stairBW s zero r _ sr =
  subst (λ z → z ~ʷ runF s (suc r) sr)
        (sym (++-identityʳ (runF s (suc r) sr))) ~refl
stairBW {N} s (suc m′) (suc r′) (s≤s m′≤r′) sr =
  ~trans (∷-cong S (∷-cong S1 (~sym (commLW s (suc (suc s)) r′ _ s<N cb1 ≤-refl))))
  (~trans (c3 (adjℕ→Adj s s<N ss<N))
  (~trans (∷-cong S1 (∷-cong S (stairBW (suc s) m′ r′ m′≤r′ sr′)))
          (∷-cong S1 (commLW s (suc (suc s)) m′ _ s<N cb2 ≤-refl))))
  where
  s<N : s < N
  s<N = head< s (suc r′) sr
  eq1 : s + suc (suc r′) ≡ suc (suc (s + r′))
  eq1 = trans (+-suc s (suc r′)) (cong suc (+-suc s r′))
  cb1 : suc (suc s) + r′ ≤ N
  cb1 = subst (λ z → z ≤ N) eq1 sr
  ss<N : suc s < N
  ss<N = ≤-trans (s≤s (s≤s (m≤m+n s r′))) cb1
  cb2 : suc (suc s) + m′ ≤ N
  cb2 = ≤-trans (s≤s (s≤s (+-monoʳ-≤ s m′≤r′))) cb1
  sr′ : suc s + suc r′ ≤ N
  sr′ = subst (λ z → z ≤ N) (+-suc s (suc r′)) sr
  S  = fromℕ< s<N
  S1 = fromℕ< ss<N

------------------------------------------------------------------------
-- 6. Bound arithmetic + STAIRCASE IDENTITY (A) (r ≤ m′), which
-- terminates in a `c1` cancellation:
--    runF s (r+1) ++ runF s (m′+1)  ~ʷ  runF (s+1) m′ ++ runF s r

bA-r : ∀ {N} (s m′ r : ℕ) → r ≤ m′ → s + suc m′ ≤ N → s + suc r ≤ N
bA-r s m′ r r≤m′ sm = ≤-trans (+-monoʳ-≤ s (s≤s r≤m′)) sm

bA-sm : ∀ {N} (s m′ r : ℕ) → s + suc m′ ≤ N → suc s + m′ ≤ N
bA-sm {N} s m′ r sm = subst (λ z → z ≤ N) (+-suc s m′) sm

bA-rr : ∀ {N} (s m′ r : ℕ) → r ≤ m′ → s + suc m′ ≤ N → s + r ≤ N
bA-rr s m′ r r≤m′ sm = ≤-trans (+-monoʳ-≤ s (≤-trans r≤m′ (n≤1+n m′))) sm

stairAW : ∀ {N} (s m′ r : ℕ) (r≤m′ : r ≤ m′) (sm : s + suc m′ ≤ N)
        → (runF s (suc r) (bA-r s m′ r r≤m′ sm) ++ runF s (suc m′) sm)
          ~ʷ (runF (suc s) m′ (bA-sm s m′ r sm) ++ runF s r (bA-rr s m′ r r≤m′ sm))
stairAW {N} s m′ zero _ sm =
  ~trans (c1 S)
         (subst (λ z → runF (suc s) m′ (bA-sm s m′ zero sm) ~ʷ z)
                (sym (++-identityʳ _)) ~refl)
  where
  s<N : s < N
  s<N = head< s m′ sm
  S = fromℕ< s<N
stairAW {N} s (suc m″) (suc r′) (s≤s r′≤m″) sm =
  ~trans (∷-cong S (∷-cong S1 (~sym (commLW s (suc (suc s)) r′ _ s<N cb1 ≤-refl))))
  (~trans (c3 (adjℕ→Adj s s<N ss<N))
  (~trans (∷-cong S1 (∷-cong S (stairAW (suc s) m″ r′ r′≤m″ sr′)))
          (∷-cong S1 (commLW s (suc (suc s)) m″ _ s<N cb2 ≤-refl))))
  where
  s<N : s < N
  s<N = head< s (suc m″) sm
  eqA : s + suc (suc m″) ≡ suc (suc (s + m″))
  eqA = trans (+-suc s (suc m″)) (cong suc (+-suc s m″))
  cbm : suc (suc s) + m″ ≤ N
  cbm = subst (λ z → z ≤ N) eqA sm
  cb1 : suc (suc s) + r′ ≤ N
  cb1 = ≤-trans (s≤s (s≤s (+-monoʳ-≤ s r′≤m″))) cbm
  cb2 : suc (suc s) + m″ ≤ N
  cb2 = cbm
  ss<N : suc s < N
  ss<N = ≤-trans (s≤s (s≤s (m≤m+n s m″))) cbm
  sr′ : suc s + suc m″ ≤ N
  sr′ = subst (λ z → z ≤ N) (+-suc s (suc m″)) sm
  S  = fromℕ< s<N
  S1 = fromℕ< ss<N
