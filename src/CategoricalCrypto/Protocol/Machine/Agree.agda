{-# OPTIONS --safe --without-K --guardedness #-}

-- `PrAgree`: past a budget the machine image's cumulative mass IS layer 1's
-- verdict probability.  Two nested inductions — one on the call tree an
-- activation drives, one on the strategy — each an instance of `Stable`, so all
-- budget bookkeeping stays in `Dp.Stable` and only the junctions are exhibited
-- here: one for the machine's `point`, one per activation, one per resumption.
--
-- The test is a parameter `Q` throughout; nothing below inspects it, which is
-- what makes `PrAgree`'s "at either verdict" free (`Protocol.Machine`'s header).

open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Stable

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Protocol.Machine.Agree where

module _ {B : Iface} (P : Protocol unitᴵ B) where

  -- One activation: `drive` runs the call tree to the boundary where the
  -- machine's continuation `h` takes over, and `evalC` collapses the same tree.
  callAgree : (Q : Bool → ℚ) (T : Calls unitᴵ (St P × Pos B))
              (h : MSt P × (⊥ ⊎ Pos B) → Dₚ Bool) (F : St P × Pos B → ℚ)
            → ((s : St P) (r : Pos B) → Stable Q (h (idle s , inj₂ r)) (F (s , r)))
            → Stable Q (drive P T >>=ₚ h) (E⊥ (evalC T) F)
  callAgree Q (ret (s , r)) h F hyp =
    subst (Stable Q _) (sym (lookupᴰℚ-return (just (s , r)) (maybeℚ F)))
          (Stable-bind-return (idle s , inj₂ r) h Q (hyp s r))
  callAgree Q (call q _) h F hyp = ⊥-elim q
  callAgree Q (coin μ k) h F hyp =
    subst (Stable Q _) (sym (E-bind μ (λ c → evalC (k c)) (maybeℚ F)))
          (Stable-assoc (coinₚ μ) (λ c → drive P (k c)) h Q
            (Stable-coin μ (λ c → drive P (k c) >>=ₚ h) (λ c → E⊥ (evalC (k c)) F) Q
                         λ c → callAgree Q (k c) h F hyp))
  callAgree Q dead h F hyp =
    subst (Stable Q _) (sym (lookupᴰℚ-return nothing (maybeℚ F))) (Stable-bot-bind h Q)

  runAgree : (Q : Bool → ℚ) (s : St P) (d : Strat (Neg B) (Pos B))
           → Stable Q (runᴹFrom (morphism P) (idle s) d) (E⊥ (runFrom P s d) Q)
  runAgree Q s (out b) =
    subst (Stable Q _) (sym (lookupᴰℚ-return (just b) (maybeℚ Q))) (Stable-return b Q)
  runAgree Q s (coin μ k) =
    subst (Stable Q _) (sym (E-bind μ (λ c → runFrom P s (k c)) (maybeℚ Q)))
          (Stable-coin μ (λ c → runᴹFrom (morphism P) (idle s) (k c))
                       (λ c → E⊥ (runFrom P s (k c)) Q) Q λ c → runAgree Q s (k c))
  runAgree Q s (ask q k) =
    subst (Stable Q _)
          (sym (E⊥-bind (kernel P s q) (λ y → runFrom P (proj₁ y) (k (proj₂ y))) Q))
          (callAgree Q (step P s q) (resumeᴹ (morphism P) λ m r → runᴹFrom (morphism P) m (k r))
                     (λ y → E⊥ (runFrom P (proj₁ y) (k (proj₂ y))) Q)
                     λ s′ r → runAgree Q s′ (k r))

prAgree : PrAgree
prAgree b P d =
  Stable⇒Σ+ (Stable-bind-return (idle (init P)) (λ m → runᴹFrom (morphism P) m d) (indᵇ b)
                                (runAgree P (indᵇ b) (init P) d))
