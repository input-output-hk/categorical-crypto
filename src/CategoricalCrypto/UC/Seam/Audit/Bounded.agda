{-# OPTIONS --safe --without-K --guardedness #-}

-- The probability arithmetic of the audit supply, at the trivial grade: a
-- budget of a context's observation is reached by the monitor's run, `Pr≤-mono`
-- paying the difference between that budget and the one past which `prAgree`
-- reads layer 1's probability off the machine run.
--
-- Only a ZERO-SLACK domination is asked of the identification, which is what
-- lets a prefix-tolerant witness supply it (`Dp.Mass.const-bind-≼`: an
-- initialization is never seen to add mass).  `UC.Seam.Audit.Prefix` is the
-- consumer, and `UC.Seam.Audit.Context` builds the context the domination is
-- read at.

open import Data.Bool.Base using (Bool; true)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-identityʳ; ≤-reflexive; ≤-trans)

open import ProbabilisticLogic.Dp using (Dₚ)
open import ProbabilisticLogic.Dp.Advantage using (_≼ₚ[_]_; Pr≤; Pr≤-mono)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Machine.Agree using (prAgree)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat; asks≤)

module CategoricalCrypto.UC.Seam.Audit.Bounded where

supply : {B : Iface} (P : Protocol unitᴵ B)
         (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
         (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → Bounded P bad ε
       → (x : Dₚ Bool) → x ≼ₚ[ 0ℚ ] runᴹ (morphism P) (bad d)
       → (n : ℕ) → Pr≤ n x ℚ.≤ ε q
supply P bad ε q d a bnd x dom n =
  ≤-trans (≤-trans (proj₂ reach) (≤-reflexive (+-identityʳ _)))
    (≤-trans (Pr≤-mono true run (ℕP.m≤n+m (proj₁ reach) (proj₁ pa)))
             (≤-trans (≤-reflexive (reads (proj₁ reach))) (bnd q d a)))
  where
  run : Dₚ Bool
  run = runᴹ (morphism P) (bad d)

  pa = prAgree true P (bad d)
  reads = proj₂ pa

  reach = dom true n
