{-# OPTIONS --safe --without-K --guardedness #-}

-- The concrete resource crosses the `Dₚ`/`Dist-ℚ` boundary: every activation of
-- `Examples.ROCommitment.Resource.resource` settles, so its closed `Dₚ` run IS
-- a kernel run, and on the oracle half that kernel is the closed game's own
-- (`resKᵀ-fetchT`).
--
-- This is what inhabits `Protocol.Machine.Raw.StepSettles` at a machine that
-- really samples — the lazily sampled table draws `uniformₚ k`, whose cascade
-- settles by `Dp.Settle.Uniform.uniformₚ-settles` — so the raw transport is not
-- vacuous.  The kernel is `Dist⊥`-valued because two activations of the CELL are
-- off-protocol (a second `putᴿ`, a `getᴿ` before one) and the machine's image of
-- those is `botₚ`, where the game's `respR` answers `idleR`;
-- `docs/dp-transport.md` records what that costs.

open import Data.Bool.Base using (Bool)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (_⊎_; inj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; uniform-Vec)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Settle
open import ProbabilisticLogic.Dp.Settle.Uniform using (uniformₚ-settles)
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction using (runWith⊥)
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Protocol.Machine.Raw using (StepSettles; ansᴹ; rawPr)
open import CategoricalCrypto.Strategy using (Strat)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.ROCommitment.Transport (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Game k using (fetchT)
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- The kernel

-- The oracle's branch, written the way the MACHINE branches — on the table
-- lookup — so that each half is a settled distribution outright.
fetchᴰ : Tbl → Maybe Bool → Pt → Maybe Dig → Dist-ℚ (RState × ResA)
fetchᴰ t m x (just d) = return-ℚ ((t , m) , digᴿ d)
fetchᴰ t m x nothing  = uniform-Vec k >>=ᴹ λ h → return-ℚ (((x , h) ∷ t , m) , digᴿ h)

resKᵀ : RState → Pt → Dist-ℚ (RState × ResA)
resKᵀ (t , m) x = fetchᴰ t m x (lookupPt t x)

resK : RState → Neg Resᴵ → Dist⊥ (RState × Pos Resᴵ)
resK s             (hashᴿ x) = Dmap just (resKᵀ s x)
resK (t , nothing) (putᴿ b)  = return⊥ ((t , just b) , rcptᴿ)
resK (t , just _)  (putᴿ _)  = return-ℚ nothing
resK (t , just b)  getᴿ      = return⊥ ((t , just b) , outᴿ b)
resK (t , nothing) getᴿ      = return-ℚ nothing
resK (t , m)       nakᴿ      = return⊥ ((t , m) , rejᴿ)

private
  up : RState × Dig → Dist-ℚ (RState × ResA)
  up u = return-ℚ (proj₁ u , digᴿ (proj₂ u))

-- …and it IS the closed game's oracle, relabelled onto `Resᴵ`.
resKᵀ-fetchT : (s : RState) (x : Pt)
             → resKᵀ s x ≈Mℚ (fetchT s x >>=ᴹ λ u → return-ℚ (proj₁ u , digᴿ (proj₂ u)))
resKᵀ-fetchT (t , m) x with lookupPt t x
... | just d  = Mℚ.sym {x = return-ℚ ((t , m) , d) >>=ᴹ up} {y = return-ℚ ((t , m) , digᴿ d)}
                       (>>=ᴹ-identityˡ ((t , m) , d) up)
... | nothing = Mℚ.sym {x = (uniform-Vec k >>=ᴹ sample) >>=ᴹ up} {y = uniform-Vec k >>=ᴹ tag}
                  (Mℚ.trans {i = (uniform-Vec k >>=ᴹ sample) >>=ᴹ up}
                            {j = uniform-Vec k >>=ᴹ λ h → sample h >>=ᴹ up}
                            {k = uniform-Vec k >>=ᴹ tag}
                    (>>=ᴹ-assoc (uniform-Vec k) sample up)
                    (>>=ᴹ-congˡ (uniform-Vec k) (λ h → sample h >>=ᴹ up) tag
                                λ h → >>=ᴹ-identityˡ (((x , h) ∷ t , m) , h) up))
  where
  sample : Dig → Dist-ℚ (RState × Dig)
  sample h = return-ℚ (((x , h) ∷ t , m) , h)

  tag : Dig → Dist-ℚ (RState × ResA)
  tag h = return-ℚ (((x , h) ∷ t , m) , digᴿ h)

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

  -- Two total values agreeing on every test agree as settled values.
  respᵀ : (μ ν : Dist-ℚ Ans) → ((Q : Test) → E μ Q ≡ E ν Q)
        → {n : ℕ} {d : Dₚ Ans} → Settlesᵀ n d μ → Settlesᵀ n d ν
  respᵀ μ ν h = Settles-resp (Dmap just μ) (Dmap just ν)
                             λ Q → trans (Eⱼ μ Q) (trans (h Q) (sym (Eⱼ ν Q)))

  -- A relabelled value and a relabelled sink: `Dmap⊥` is a bind, so neither is
  -- definitionally what `Settles-return`/`Settles-bot` produces.
  respᴿ : (y : RState × ResA) → Settles 1 (returnₚ (ansᴹ y)) (Dmap⊥ ansᴹ (return⊥ y))
  respᴿ y = Settles-resp (return⊥ (ansᴹ y)) (Dmap⊥ ansᴹ (return⊥ y))
                         (map-return y) (Settles-return (ansᴹ y))

  respᴮ : Settles 0 (botₚ {A = Ans}) (Dmap⊥ (ansᴹ {RState} {ResA}) (return-ℚ nothing))
  respᴮ = Settles-resp (return-ℚ nothing) (Dmap⊥ ansᴹ (return-ℚ nothing)) map-bot Settles-bot

  -- The oracle's activation, at the lookup result passed in rather than
  -- scrutinised: `with` does not abstract the copy of it inside the machine's
  -- own step, where `rewrite` at a matched `r` reduces both sides.
  hash : (t : Tbl) (m : Maybe Bool) (x : Pt) (r : Maybe Dig) → lookupPt t x ≡ r
       → Σ[ n ∈ ℕ ] Settles n (step resource ((t , m) , inj₂ (hashᴿ x)))
                              (Dmap⊥ ansᴹ (Dmap just (fetchᴰ t m x r)))
  hash t m x (just d) eq rewrite eq =
    1 , Settlesᵀ-tag ansᴹ (return-ℚ hit)
          (respᵀ (return-ℚ (ansᴹ hit)) (Dmap ansᴹ (return-ℚ hit)) value
                 (Settlesᵀ-return (ansᴹ hit)))
    where
    hit : RState × ResA
    hit = (t , m) , digᴿ d

    value : (Q : Test) → E (return-ℚ (ansᴹ hit)) Q ≡ E (Dmap ansᴹ (return-ℚ hit)) Q
    value Q = trans (lookupᴰℚ-return (ansᴹ hit) Q)
                    (sym (trans (lookupᴰℚ-Dmap ansᴹ (return-ℚ hit) Q)
                                (lookupᴰℚ-return hit λ p → Q (ansᴹ p))))
  hash t m x nothing eq rewrite eq =
    draw .proj₁
    , Settlesᵀ-tag ansᴹ (uniform-Vec k >>=ᴹ λ h → return-ℚ (ent h))
        (respᵀ (uniform-Vec k >>=ᴹ λ h → return-ℚ (ansᴹ (ent h)))
               (Dmap ansᴹ (uniform-Vec k >>=ᴹ λ h → return-ℚ (ent h))) value (draw .proj₂))
    where
    ent : Dig → RState × ResA
    ent h = ((x , h) ∷ t , m) , digᴿ h

    draw : Σ[ n ∈ ℕ ] Settlesᵀ n (uniformₚ k >>=ₚ λ h → returnₚ (ansᴹ (ent h)))
                                 (uniform-Vec k >>=ᴹ λ h → return-ℚ (ansᴹ (ent h)))
    draw = Settlesᵀ-bind⋆ (uniformₚ-settles k .proj₁) (uniformₚ k)
             (λ h → returnₚ (ansᴹ (ent h))) (uniform-Vec k) (λ h → return-ℚ (ansᴹ (ent h)))
             (uniformₚ-settles k .proj₂) λ h → 1 , Settlesᵀ-return (ansᴹ (ent h))

    value : (Q : Test) → E (uniform-Vec k >>=ᴹ λ h → return-ℚ (ansᴹ (ent h))) Q
                       ≡ E (Dmap ansᴹ (uniform-Vec k >>=ᴹ λ h → return-ℚ (ent h))) Q
    value Q =
      trans (E-bind (uniform-Vec k) (λ h → return-ℚ (ansᴹ (ent h))) Q)
      (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
               λ h → lookupᴰℚ-return (ansᴹ (ent h)) Q)
      (sym (trans (lookupᴰℚ-Dmap ansᴹ (uniform-Vec k >>=ᴹ λ h → return-ℚ (ent h)) Q)
           (trans (E-bind (uniform-Vec k) (λ h → return-ℚ (ent h)) λ p → Q (ansᴹ p))
                  (lookupᴰℚ-cong-P (entries (uniform-Vec k))
                    λ h → lookupᴰℚ-return (ent h) λ p → Q (ansᴹ p))))))

-- `Protocol.Machine.Raw`'s hypothesis, inhabited at a machine that samples.
resource-settles : StepSettles resource resK
resource-settles (t , m) (hashᴿ x) = hash t m x (lookupPt t x) refl
resource-settles (t , nothing) (putᴿ b) =
  1 , respᴿ ((t , just b) , rcptᴿ)
resource-settles (t , just _) (putᴿ _) = 0 , respᴮ
resource-settles (t , just b) getᴿ =
  1 , respᴿ ((t , just b) , outᴿ b)
resource-settles (t , nothing) getᴿ = 0 , respᴮ
resource-settles (t , m) nakᴿ =
  1 , respᴿ ((t , m) , rejᴿ)

------------------------------------------------------------------------
-- …so the closed `Dₚ` run of the resource IS the kernel's run

-- At either verdict, past a budget of its own, and with no protocol image
-- anywhere: `Protocol.Machine.Agree.prAgree`'s conclusion off protocol images
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
  collapse = trans (E⊥-bind σ₀ (λ s → runWith⊥ resK s d) (indᵇ b))
                   (E⊥-return ([] , nothing) λ s → E⊥ (runWith⊥ resK s d) (indᵇ b))
