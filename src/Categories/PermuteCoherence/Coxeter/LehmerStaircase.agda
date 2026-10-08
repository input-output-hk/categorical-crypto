{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Staircase identities for Lehmer insertion, derived from `c1`/`c2`/`c3`.
-- The ambient bound stays fixed while run lengths differ.  A numeric base
-- makes base-incrementing recursion direct, without lifting transports.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Coxeter.LehmerStaircase where

open import Data.Fin.Base using (fromℕ<) renaming (suc to fsuc)
open import Data.Fin.Patterns
open import Data.List.Base
open import Data.List.Properties
open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality.Core

open import Categories.PermuteCoherence.Coxeter.Word

private
  variable
    n N : ℕ

------------------------------------------------------------------------
-- Word congruence and head commutation
------------------------------------------------------------------------
++c-l : (u : Word n) {v w : Word n} → v ~ʷ w → (u ++ v) ~ʷ (u ++ w)
++c-l []      r = r
++c-l (i ∷ u) r = ∷-cong i (++c-l u r)

comm₀ : (u : Word n) (v : Word (suc (suc n)))
      → (0F ∷ (liftW (liftW u) ++ v)) ~ʷ (liftW (liftW u) ++ (0F ∷ v))
comm₀ []      v = ~refl
comm₀ (i ∷ u) v = ~trans (c2 far0ˡ) (∷-cong (fsuc (fsuc i)) (comm₀ u v))

------------------------------------------------------------------------
-- Numeric generator relations
------------------------------------------------------------------------

-- Relevant bounds discharge impossible small ambient sizes.
farℕ→Far : ∀ (s b : ℕ) (s<N : s < N) (b<N : b < N)
         → suc (suc s) ≤ b → Far {N} (fromℕ< s<N) (fromℕ< b<N)
farℕ→Far zero    (suc (suc b)) (s≤s _)   (s≤s (s≤s _))   (s≤s (s≤s _)) = far0ˡ
farℕ→Far (suc s) (suc b)       (s≤s s<N) (s≤s b<N)       (s≤s le)      =
  farS (farℕ→Far s b s<N b<N le)

adjℕ→Adj : ∀ (s : ℕ) (s<N : s < N) (ss<N : suc s < N)
         → Adj {N} (fromℕ< s<N) (fromℕ< ss<N)
adjℕ→Adj zero    (s≤s _)   (s≤s (s≤s _)) = adj0
adjℕ→Adj (suc s) (s≤s s<N) (s≤s ss<N)    = adjS (adjℕ→Adj s s<N ss<N)

------------------------------------------------------------------------
-- Ascending runs
------------------------------------------------------------------------
head< : (s ℓ : ℕ) → s + suc ℓ ≤ N → s < N
head< {N} s ℓ le = ≤-trans (s≤s (m≤m+n s ℓ)) (subst (λ z → z ≤ N) (+-suc s ℓ) le)

tail≤ : (s ℓ : ℕ) → s + suc ℓ ≤ N → suc s + ℓ ≤ N
tail≤ {N} s ℓ le = subst (λ z → z ≤ N) (+-suc s ℓ) le

runF : (s ℓ : ℕ) → .(s + ℓ ≤ N) → Word N
runF s zero    _  = []
runF s (suc ℓ) le = fromℕ< (head< s ℓ le) ∷ runF (suc s) ℓ (tail≤ s ℓ le)

commLW : ∀ (s b k : ℕ) (w : Word N) (s<N : s < N) (bk : b + k ≤ N)
       → suc (suc s) ≤ b
       → (fromℕ< s<N ∷ (runF b k bk ++ w)) ~ʷ (runF b k bk ++ (fromℕ< s<N ∷ w))
commLW s b zero    w s<N bk le = ~refl
commLW s b (suc k) w s<N bk le =
  ~trans (c2 (farℕ→Far s b s<N (head< b k bk) le))
         (∷-cong (fromℕ< (head< b k bk))
                 (commLW s (suc b) k w s<N (tail≤ b k bk) (≤-trans le (n≤1+n b))))

-- Run bounds are irrelevant; only bounds consumed by the generator
-- relations need named arithmetic proofs.

stairBW : (s m r : ℕ) (m≤r : m ≤ r) (sr : s + suc r ≤ N)
          .(bm : s + m ≤ N) .(bsm : suc s + m ≤ N)
        → (runF s (suc r) sr ++ runF s m bm)
          ~ʷ (runF (suc s) m bsm ++ runF s (suc r) sr)
stairBW s zero r _ sr _ _ =
  subst (λ z → z ~ʷ runF s (suc r) sr)
        (sym (++-identityʳ (runF s (suc r) sr))) ~refl
stairBW {N} s (suc m′) (suc r′) (s≤s m′≤r′) sr _ _ =
  ~trans (∷-cong S (∷-cong S1 (~sym (commLW s (suc (suc s)) r′ _ s<N cb1 ≤-refl))))
  (~trans (c3 (adjℕ→Adj s s<N ss<N))
  (~trans (∷-cong S1 (∷-cong S (stairBW (suc s) m′ r′ m′≤r′ sr′ _ _)))
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

stairAW : (s m′ r : ℕ) (r≤m′ : r ≤ m′) (sm : s + suc m′ ≤ N)
          .(br : s + suc r ≤ N) .(bsm : suc s + m′ ≤ N) .(brr : s + r ≤ N)
        → (runF s (suc r) br ++ runF s (suc m′) sm)
          ~ʷ (runF (suc s) m′ bsm ++ runF s r brr)
stairAW {N} s m′ zero _ sm _ bsm _ =
  ~trans (c1 S)
         (subst (λ z → runF (suc s) m′ bsm ~ʷ z) (sym (++-identityʳ _)) ~refl)
  where
  s<N : s < N
  s<N = head< s m′ sm
  S = fromℕ< s<N
stairAW {N} s (suc m″) (suc r′) (s≤s r′≤m″) sm _ _ _ =
  ~trans (∷-cong S (∷-cong S1 (~sym (commLW s (suc (suc s)) r′ _ s<N cb1 ≤-refl))))
  (~trans (c3 (adjℕ→Adj s s<N ss<N))
  (~trans (∷-cong S1 (∷-cong S (stairAW (suc s) m″ r′ r′≤m″ sr′ brA _ _)))
          (∷-cong S1 (commLW s (suc (suc s)) m″ _ s<N cbm ≤-refl))))
  where
  s<N : s < N
  s<N = head< s (suc m″) sm
  eqA : s + suc (suc m″) ≡ suc (suc (s + m″))
  eqA = trans (+-suc s (suc m″)) (cong suc (+-suc s m″))
  cbm : suc (suc s) + m″ ≤ N
  cbm = subst (λ z → z ≤ N) eqA sm
  cb1 : suc (suc s) + r′ ≤ N
  cb1 = ≤-trans (s≤s (s≤s (+-monoʳ-≤ s r′≤m″))) cbm
  ss<N : suc s < N
  ss<N = ≤-trans (s≤s (s≤s (m≤m+n s m″))) cbm
  sr′ : suc s + suc m″ ≤ N
  sr′ = subst (λ z → z ≤ N) (+-suc s (suc m″)) sm
  brA : suc s + suc r′ ≤ N
  brA = ≤-trans (+-monoʳ-≤ (suc s) (s≤s r′≤m″)) sr′
  S  = fromℕ< s<N
  S1 = fromℕ< ss<N
