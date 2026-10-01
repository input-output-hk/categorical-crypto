{-# OPTIONS --safe --without-K --guardedness #-}

-- The concrete resource crosses the `Dₚ`/`Dist-ℚ` boundary: every activation
-- settles (`resource-settles`, inhabiting `Protocol.Machine.Raw.StepSettles`
-- at a machine that samples), so its closed `Dₚ` run is a kernel run, and on
-- the oracle half that kernel is the closed game's (`resKᵀ`).  The
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
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Raw
open import CategoricalCrypto.Strategy

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.ROCommitment.Transport (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Oracle k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Core (𝒱ₚ 0ℓ)

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

  map-return : (y : RState × ResA) (Q : Test)
             → E⊥ (return⊥ (ansᴹ y)) Q ≡ E⊥ (Dmap⊥ ansᴹ (return⊥ y)) Q
  map-return y Q = trans (E⊥-return (ansᴹ y) Q)
                         (sym (trans (E⊥-map ansᴹ (return⊥ y) Q)
                                     (E⊥-return y λ p → Q (ansᴹ p))))

  map-bot : (Q : Test) → E⊥ (return-ℚ nothing) Q ≡ E⊥ (Dmap⊥ ansᴹ (return-ℚ nothing)) Q
  map-bot Q = trans (lookupᴰℚ-return nothing (maybeℚ Q))
                    (sym (trans (E⊥-map ansᴹ (return-ℚ nothing) Q)
                                (lookupᴰℚ-return nothing (maybeℚ λ p → Q (ansᴹ p)))))

  respᵀ : (μ ν : Dist-ℚ Ans) → ((Q : Test) → E μ Q ≡ E ν Q)
        → {n : ℕ} {d : Dₚ Ans} → Settlesᵀ n d μ → Settlesᵀ n d ν
  respᵀ μ ν h = Settles-resp (Dmap just μ) (Dmap just ν)
                             λ Q → trans (Eⱼ μ Q) (trans (h Q) (sym (Eⱼ ν Q)))

  -- A relabelled value and a relabelled sink: `Dmap⊥` is a bind, so neither is
  -- definitionally what `Settles-return`/`Settles-bot` produces.
  respᴿ : (y : RState × ResA) → Settles 1 (returnₚ (ansᴹ y)) (Dmap⊥ ansᴹ (return⊥ y))
  respᴿ y = Settles-resp (return⊥ (ansᴹ y)) (Dmap⊥ ansᴹ (return⊥ y))
                         (map-return y) (Settles-return (ansᴹ y))

  respᴮ : Settles 0 botₚ (Dmap⊥ ansᴹ (return-ℚ nothing))
  respᴮ = Settles-resp (return-ℚ nothing) (Dmap⊥ ansᴹ (return-ℚ nothing)) map-bot Settles-bot

  -- The oracle's activation, at the lookup result passed in rather than
  -- scrutinised: `with` does not abstract the copy of it inside the machine's
  -- own step, where `rewrite` at a matched `r` reduces both sides.
  hash : (t : Tbl) (m : Maybe Bool) (x : Pt) (r : Maybe Dig) → lookupPt t x ≡ r
       → Σ[ n ∈ ℕ ] Settles n (step resource ((t , m) , inj₂ (hashᴿ x)))
                              (Dmap⊥ ansᴹ (Dmap just (resKᵀ (t , m) x)))
  hash t m x (just d) eq rewrite eq =
    1 , Settlesᵀ-tag ansᴹ (Dmap digᵀ (return-ℚ ((t , m) , d)))
          (respᵀ (return-ℚ (ansᴹ hit)) (Dmap ansᴹ (Dmap digᵀ (return-ℚ ((t , m) , d)))) value
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
        (respᵀ (uniform-Vec k >>=ᴹ λ h → return-ℚ (ansᴹ (ent h)))
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
resource-settles (t , nothing) (putᴿ b) = 1 , respᴿ ((t , just b) , rcptᴿ)
resource-settles (t , just _) (putᴿ _) = 0 , respᴮ
resource-settles (t , just b) getᴿ = 1 , respᴿ ((t , just b) , outᴿ b)
resource-settles (t , nothing) getᴿ = 0 , respᴮ
resource-settles (t , m) nakᴿ = 1 , respᴿ ((t , m) , rejᴿ)

-- The closed `Dₚ` run of the resource is the kernel's run:
-- `Protocol.Machine.Agree.prAgree`'s conclusion without protocol images
-- (`docs/dp-transport.md`).
resource-run : (b : Bool) (d : Strat (Neg Resᴵ) (Pos Resᴵ))
             → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n + i) (runᴹ resource d) (indᵇ b)
                                    ≡ E⊥ (runWith⊥ resK ([] , nothing) d) (indᵇ b))
resource-run b d = run .proj₁ , λ i → trans (run .proj₂ i) collapse
  where
  σ₀ : Dist⊥ RState
  σ₀ = return⊥ ([] , nothing)

  run = rawPr resource resK resource-settles σ₀ 1 (Settles-return ([] , nothing)) b d

  collapse : E⊥ (σ₀ >>=⊥ λ s → runWith⊥ resK s d) (indᵇ b)
           ≡ E⊥ (runWith⊥ resK ([] , nothing) d) (indᵇ b)
  collapse = >>=⊥-identityˡ ([] , nothing) (λ s → runWith⊥ resK s d) (maybeℚ (indᵇ b))
