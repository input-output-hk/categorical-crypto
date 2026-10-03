{-# OPTIONS --safe --without-K --guardedness #-}

-- The concrete resource crosses the `Dₚ`/`Dist-ℚ` boundary: every activation
-- settles (`resource-settles`, inhabiting `Machines.Run.Raw.StepSettles`
-- at a machine that samples), so `rawPr` reads its closed `Dₚ` run as a kernel
-- run, and on the oracle half that kernel is the closed game's (`resKᵀ`).  The
-- kernel is `Dist⊥`-valued because the two off-protocol cell activations are
-- `botₚ` in the machine (`docs/dp-transport.md`).

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational using (ℚ)
open import Data.Sum.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Settle

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.Machines.Run.Raw
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.ROCommitment.Transport (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Oracle k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open MC

------------------------------------------------------------------------
-- The kernel

digᵀ : RState × Dig → RState × ResA
digᵀ u = proj₁ u , digᴿ (proj₂ u)

resKᵀ : RState → Pt → Dist-ℚ (RState × ResA)
resKᵀ (t , m) x = Dmap digᵀ (fetchT (_, m) t x)

resK : RState → Neg Resᴵ → Dist⊥ (RState × Pos Resᴵ)
resK s             (hashᴿ x) = Dmap just (resKᵀ s x)
resK (t , nothing) (putᴿ b)  = return⊥ ((t , just b) , rcptᴿ)
resK (t , just _)  (putᴿ _)  = return-ℚ nothing
resK (t , just b)  getᴿ      = return⊥ ((t , just b) , outᴿ b)
resK (t , nothing) getᴿ      = return-ℚ nothing
resK (t , m)       nakᴿ      = return⊥ ((t , m) , rejᴿ)

------------------------------------------------------------------------
-- Every activation settles

private
  Ans : Set
  Ans = RState × (Pos unitᴵ ⊎ ResA)

  Test : Set
  Test = Ans → ℚ

  -- The oracle's activation, at the lookup result passed in rather than
  -- scrutinised: `with` does not abstract the copy of it inside the machine's
  -- own step, where `rewrite` at a matched `r` reduces both sides.
  hash : (t : Tbl) (m : Maybe Bool) (x : Pt) (r : Maybe Dig) → lookupPt t x ≡ r
       → Σ[ n ∈ ℕ ] Settles n (step resource ((t , m) , inj₂ (hashᴿ x)))
                              (Dmap⊥ ansᴹ (Dmap just (resKᵀ (t , m) x)))
  hash t m x (just d) eq rewrite eq =
    1 , Settlesᵀ-tag ansᴹ (Dmap digᵀ (return-ℚ ((t , m) , d)))
          (Settlesᵀ-resp (return-ℚ (ansᴹ hit)) (Dmap ansᴹ (Dmap digᵀ (return-ℚ ((t , m) , d)))) value
                 (Settlesᵀ-return (ansᴹ hit)))
    where
    hit : RState × ResA
    hit = (t , m) , digᴿ d

    value : (Q : Test) → E (return-ℚ (ansᴹ hit)) Q
                       ≡ E (Dmap ansᴹ (Dmap digᵀ (return-ℚ ((t , m) , d)))) Q
    value Q = trans (lookupᴰℚ-return (ansᴹ hit) Q)
                    (sym (trans (lookupᴰℚ-Dmap ansᴹ (Dmap digᵀ (return-ℚ ((t , m) , d))) Q)
                         (trans (lookupᴰℚ-Dmap digᵀ (return-ℚ ((t , m) , d)) (λ p → Q (ansᴹ p)))
                                (lookupᴰℚ-return ((t , m) , d) λ p → Q (ansᴹ (digᵀ p))))))
  hash t m x nothing eq rewrite eq =
    draw .proj₁
    , Settlesᵀ-tag ansᴹ (Dmap digᵀ (Dmap sample (uniform-Vec k)))
        (Settlesᵀ-resp (uniform-Vec k >>=ᴹ λ h → return-ℚ (ansᴹ (ent h)))
               (Dmap ansᴹ (Dmap digᵀ (Dmap sample (uniform-Vec k)))) value (draw .proj₂))
    where
    sample : Dig → RState × Dig
    sample h = ((x , h) ∷ t , m) , h

    ent : Dig → RState × ResA
    ent h = ((x , h) ∷ t , m) , digᴿ h

    draw : Σ[ n ∈ ℕ ] Settlesᵀ n (uniformₚ k >>=ₚ λ h → returnₚ (ansᴹ (ent h)))
                                 (uniform-Vec k >>=ᴹ λ h → return-ℚ (ansᴹ (ent h)))
    draw = Settlesᵀ-bind⋆ (uniformₚ-settles k .proj₁) (uniformₚ k)
             (λ h → returnₚ (ansᴹ (ent h))) (uniform-Vec k) (λ h → return-ℚ (ansᴹ (ent h)))
             (uniformₚ-settles k .proj₂) λ h → 1 , Settlesᵀ-return (ansᴹ (ent h))

    value : (Q : Test) → E (uniform-Vec k >>=ᴹ λ h → return-ℚ (ansᴹ (ent h))) Q
                       ≡ E (Dmap ansᴹ (Dmap digᵀ (Dmap sample (uniform-Vec k)))) Q
    value Q = trans (lookupᴰℚ-Dmap (λ h → ansᴹ (ent h)) (uniform-Vec k) Q)
      (sym (trans (lookupᴰℚ-Dmap ansᴹ (Dmap digᵀ (Dmap sample (uniform-Vec k))) Q)
           (trans (lookupᴰℚ-Dmap digᵀ (Dmap sample (uniform-Vec k)) (λ p → Q (ansᴹ p)))
                  (lookupᴰℚ-Dmap sample (uniform-Vec k) (λ p → Q (ansᴹ (digᵀ p)))))))

resource-settles : StepSettles resource resK
resource-settles (t , m) (hashᴿ x) = hash t m x (lookupPt t x) refl
resource-settles (t , nothing) (putᴿ b) = 1 , Settles-map-return ansᴹ ((t , just b) , rcptᴿ)
resource-settles (t , just _) (putᴿ _) = 0 , Settles-map-bot ansᴹ
resource-settles (t , just b) getᴿ = 1 , Settles-map-return ansᴹ ((t , just b) , outᴿ b)
resource-settles (t , nothing) getᴿ = 0 , Settles-map-bot ansᴹ
resource-settles (t , m) nakᴿ = 1 , Settles-map-return ansᴹ ((t , m) , rejᴿ)
