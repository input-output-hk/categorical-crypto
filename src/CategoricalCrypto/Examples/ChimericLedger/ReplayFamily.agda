{-# OPTIONS --safe --without-K --guardedness #-}

-- What the replay attack does to the FAMILY property, and where it stops.
--
-- `Replay.Attack.chimeric-loses-value` holds at every hash width, at a
-- constant query depth, through the very watch the monitor
-- `Property.PreservesValue` reads implements.  So the chimeric family
-- violates that property outright: `Property.preservesValue⇒saturated` hands
-- the attack's strategy back the contextual bound, and a bound
-- `εᴹ n (p n) + ν n` that is eventually below 1 cannot dominate probability
-- one, at any polynomial allowance and any negligible slack.  No single
-- security parameter is picked — the allowance is quantified first, as the
-- property quantifies it.
--
-- What this is NOT is a refutation at the positive theorem's INITIALIZATION.
-- The attack needs a funded account and nothing credits one
-- (`System.ledger-keeps-accts-[]`), so `Chimericᶠ` starts account-funded while
-- `Property.Ideal` starts at the UTxO genesis.  What the two DO share is the
-- watch, exactly: `funded-total` is the equal-total side condition that lets
-- the same watch be read on both sides.  Whether the chimeric variant
-- preserves value AT the UTxO genesis is a different question and is left
-- open — with an empty account table every accepted withdrawal is zero, so
-- there the replay charges nothing.

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Nat.Poly using (poly-const)
open import Data.Nat.Properties using (+-identityʳ) renaming (≤-refl to ≤ᴺ-refl)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (1ℚ; ½)
open import Data.Rational.Properties using (positive⁻¹; ≤-reflexive; ≤-trans)
open import Data.Rational.Properties.Ext using (1≰½)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym)
open import Relation.Nullary.Negation.Core using (¬_)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Saturated

import CategoricalCrypto.Examples.ChimericLedger.Replay as Replay

module CategoricalCrypto.Examples.ChimericLedger.ReplayFamily
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Property ser

module At (V n : ℕ) = Replay.Attack n (ser n) V

-- The attack's family at funded value `2 + V`: the chimeric variant at the
-- account-funded initialization, level by level.
Chimericᶠ : (V : ℕ) → Systems LedgerIf^ω
Chimericᶠ V n = AtLevel.Sys n chimeric (At.s₀ V n)

module _ (a V : ℕ) where

  -- The UTxO genesis the watch measures against carries the same total as the
  -- funded state the attack runs at, so one watch serves both.
  funded-total : (n : ℕ) → Ledger.total n (genesisAt a (suc (suc V)) n)
                         ≡ Ledger.total n (At.s₀ V n)
  funded-total _ = cong (λ z → suc (suc z)) (+-identityʳ (V + 0))

  chimeric-loses-value^ω : (n : ℕ)
    → Pr (Chimericᶠ V n) (auditWatch a (suc (suc V)) n (At.replay V n)) ≡ 1ℚ
  chimeric-loses-value^ω n =
    At.chimeric-loses-value V n (genesisAt a (suc (suc V)) n) (funded-total n)

  -- Three queries at every level, probability one at every level: no
  -- negligible slack over a polynomial allowance can cover that.
  chimeric-not-preserving : ¬ PreservesValue a (suc (suc V)) (Chimericᶠ V)
  chimeric-not-preserving pv =
    let ν , neg , bnd = preservesValue⇒saturated a (suc (suc V)) (Chimericᶠ V) pv
                          (λ _ → 3) (poly-const 3)
        N , small     = →0-+ (Negligible⇒→0 (εᴹ-negligible (λ _ → 3) (poly-const 3)))
                             (Negligible⇒→0 neg) ½ (positive⁻¹ ½)
    in 1≰½ (≤-trans (≤-reflexive (sym (chimeric-loses-value^ω N)))
                    (≤-trans (bnd N (At.replay V N) (At.replay-asks V N)) (small N ≤ᴺ-refl)))
