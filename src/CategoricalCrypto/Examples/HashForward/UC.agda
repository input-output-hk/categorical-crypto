{-# OPTIONS --safe --without-K --guardedness #-}

-- The toy at the UC model: emulation at a nontrivial grade, what the
-- simulator spends, and the emulation as a machine-level event bound.
--
-- The grade is `ifaceᵒ Advᴵ`, inhabited by `peekᴬ`, and the simulator
-- `procᵒ simulator` is not a scalar.  The emulation is exact: `emulᵍ` of
-- `real-factors`, no error term.
--
-- The spend is stated at two weightings of one ledger (`UC.QueryBound.Exact`):
-- `simExactHash` counts oracle queries, `simExactAll` all downward outputs, so
-- "one hash query per `peekᴬ`" and "two queries per `peekᴬ`" are equations,
-- not ceilings.  `simCert` (`exact⇒certified` of `simExactAll`) is the upper
-- bound `hf-bounded` consumes.

open import Categories.Category

open import Data.List.Base
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational using (ℚ)
open import Data.Sum.Base hiding (map₂)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Run
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Graded
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Exact

module CategoricalCrypto.Examples.HashForward.UC (Msg Dig : Set) where

open import CategoricalCrypto.Examples.HashForward Msg Dig

------------------------------------------------------------------------
-- The emulation

realᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)
realᵒ = gradedᵒ real

idealᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Lkᴵ) (ifaceᵒ Honᴵ)
idealᵒ = gradedᵒ ideal

simᵒ : ifaceᵒ Lkᴵ ⇒ ifaceᵒ Advᴵ
simᵒ = procᵒ simulator

real-agrees : realᵒ ≈ᵁ sub simᵒ ∘ idealᵒ
real-agrees = emulᵍ real-factors

real-≤UC : realᵒ ≤UC idealᵒ
real-≤UC = ≤UCᵍ real-factors

------------------------------------------------------------------------
-- What the simulator spends

-- Amortisation potential: the queries the simulator still owes the pending
-- `peekᴬ`; the same Φ balances both ledgers below.
Φˢ : SSt → ℕ
Φˢ idleˢ  = 0
Φˢ awaitL = 1
Φˢ awaitD = 0

hashes : Neg Lkᴵ ⊎ Pos Advᴵ → ℕ
hashes (inj₁ leakˢ)     = 0
hashes (inj₁ (hashˢ _)) = 1
hashes (inj₂ _)         = 0

peeks : Pos Lkᴵ ⊎ Neg Advᴵ → ℕ
peeks (inj₁ _)     = 0
peeks (inj₂ peekᴬ) = 1

twoPerPeek : Pos Lkᴵ ⊎ Neg Advᴵ → ℕ
twoPerPeek (inj₁ _)     = 0
twoPerPeek (inj₂ peekᴬ) = 2

module EH = Ledger {Lkᴵ} {Advᴵ} SSt (returnₚ idleˢ) simStep hashes peeks
module EA = Ledger {Lkᴵ} {Advᴵ} SSt (returnₚ idleˢ) simStep downward twoPerPeek

private
  stepᵂ : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ)
        → Dₚ (Σ[ p ∈ SSt × (Neg Lkᴵ ⊎ Pos Advᴵ) ]
               (hashes (proj₂ p) + Φˢ (proj₁ p) ≡ Φˢ s + peeks x)
               × (downward (proj₂ p) + Φˢ (proj₁ p) ≡ Φˢ s + twoPerPeek x))
  stepᵂ idleˢ  (inj₂ peekᴬ)    = returnₚ ((awaitL , inj₁ leakˢ)     , refl , refl)
  stepᵂ awaitL (inj₁ (lkˢ m))  = returnₚ ((awaitD , inj₁ (hashˢ m)) , refl , refl)
  stepᵂ awaitD (inj₁ (digˢ d)) = returnₚ ((idleˢ  , inj₂ (wireᴬ d)) , refl , refl)
  stepᵂ _ _                    = botₚ

  cohᵂ : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ) → mapₚ proj₁ (stepᵂ s x) ≈ₚ simStep (s , x)
  cohᵂ idleˢ  (inj₂ peekᴬ)    = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᵂ awaitL (inj₁ (lkˢ m))  = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᵂ awaitD (inj₁ (digˢ d)) = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᵂ idleˢ  (inj₁ (lkˢ _))  = bot-bind-≈ₚ _
  cohᵂ idleˢ  (inj₁ (digˢ _)) = bot-bind-≈ₚ _
  cohᵂ awaitL (inj₂ peekᴬ)    = bot-bind-≈ₚ _
  cohᵂ awaitL (inj₁ (digˢ _)) = bot-bind-≈ₚ _
  cohᵂ awaitD (inj₂ peekᴬ)    = bot-bind-≈ₚ _
  cohᵂ awaitD (inj₁ (lkˢ _))  = bot-bind-≈ₚ _

simExactHash : EH.QEᵢ
simExactHash = record
  { Λ = Φˢ ; pointᴱ = returnₚ (idleˢ , refl)
  ; coh₀ = >>=ₚ-identityˡ (idleˢ , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ = λ s x → mapₚ (map₂ proj₁) (stepᵂ s x)
  ; cohᴱ = λ s x → map-map (stepᵂ s x) (map₂ proj₁) proj₁ ⟨≈⟩ cohᵂ s x }

simExactAll : EA.QEᵢ
simExactAll = record
  { Λ = Φˢ ; pointᴱ = returnₚ (idleˢ , refl)
  ; coh₀ = >>=ₚ-identityˡ (idleˢ , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ = λ s x → mapₚ (map₂ proj₂) (stepᵂ s x)
  ; cohᴱ = λ s x → map-map (stepᵂ s x) (map₂ proj₂) proj₁ ⟨≈⟩ cohᵂ s x }

simCert : Certified 2 simulator
simCert = exact⇒certified simExactAll (λ _ → refl) λ where
  peekᴬ → ≤-refl

simQB : QB 2 simulator
simQB = certified⇒QB simCert

sim-hash-count : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
               → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                      EH.Balanced Φˢ (weight peeks w) p)
sim-hash-count = EH.exactᴱ simExactHash

sim-query-count : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
                → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                       EA.Balanced Φˢ (weight twoPerPeek w) p)
sim-query-count = EA.exactᴱ simExactAll

sim-hash-count-settled : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
                       → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                              (Φˢ (proj₁ p) ≡ 0
                               → weight hashes (proj₂ p) ≡ weight peeks w))
sim-hash-count-settled w = mapₚ (λ (p , b) → p , λ nil →
    trans (sym (+-identityʳ _)) (trans (cong (weight hashes (proj₂ p) +_) (sym nil)) b))
  (sim-hash-count w)

-- One live round of each side, on the word one `peekᴬ` drives.
round : Msg → Dig → List (Pos Lkᴵ ⊎ Neg Advᴵ)
round m d = inj₂ peekᴬ ∷ inj₁ (lkˢ m) ∷ inj₁ (digˢ d) ∷ []

sim-round : (m : Msg) (d : Dig)
          → behᴾ simulator (round m d)
            ≈ₚ returnₚ (inj₁ leakˢ ∷ inj₁ (hashˢ m) ∷ inj₂ (wireᴬ d) ∷ [])
sim-round m d =
    >>=ₚ-identityˡ idleˢ _
  ⟨≈⟩ >>=ₚ-identityˡ (awaitL , inj₁ leakˢ) _
  ⟨≈⟩ map-arg _ afterLeak
  ⟨≈⟩ >>=ₚ-identityˡ _ _
  where
  afterDigest : traceᵍ SSt (returnₚ idleˢ) simStep awaitD (inj₁ (digˢ d) ∷ [])
                ≈ₚ returnₚ (inj₂ (wireᴬ d) ∷ [])
  afterDigest = >>=ₚ-identityˡ (idleˢ , inj₂ (wireᴬ d)) _ ⟨≈⟩ >>=ₚ-identityˡ [] _

  afterLeak : traceᵍ SSt (returnₚ idleˢ) simStep awaitL
                (inj₁ (lkˢ m) ∷ inj₁ (digˢ d) ∷ [])
              ≈ₚ returnₚ (inj₁ (hashˢ m) ∷ inj₂ (wireᴬ d) ∷ [])
  afterLeak = >>=ₚ-identityˡ (awaitD , inj₁ (hashˢ m)) _
            ⟨≈⟩ map-arg _ afterDigest ⟨≈⟩ >>=ₚ-identityˡ _ _

real-round : (m : Msg) (d : Dig)
           → behᴾ real (inj₂ (inj₁ peekᴬ) ∷ inj₁ (lkᴿ m) ∷ inj₁ (digᴿ d) ∷ [])
             ≈ₚ returnₚ (inj₁ leakᴿ ∷ inj₁ (hashᴿ m) ∷ inj₂ (inj₁ (wireᴬ d)) ∷ [])
real-round m d =
    >>=ₚ-identityˡ idleˢ _
  ⟨≈⟩ >>=ₚ-identityˡ (awaitL , inj₁ leakᴿ) _
  ⟨≈⟩ map-arg _ afterLeak
  ⟨≈⟩ >>=ₚ-identityˡ _ _
  where
  afterDigest : traceᵍ SSt (returnₚ idleˢ) realStep awaitD (inj₁ (digᴿ d) ∷ [])
                ≈ₚ returnₚ (inj₂ (inj₁ (wireᴬ d)) ∷ [])
  afterDigest = >>=ₚ-identityˡ (idleˢ , inj₂ (inj₁ (wireᴬ d))) _ ⟨≈⟩ >>=ₚ-identityˡ [] _

  afterLeak : traceᵍ SSt (returnₚ idleˢ) realStep awaitL
                (inj₁ (lkᴿ m) ∷ inj₁ (digᴿ d) ∷ [])
              ≈ₚ returnₚ (inj₁ (hashᴿ m) ∷ inj₂ (inj₁ (wireᴬ d)) ∷ [])
  afterLeak = >>=ₚ-identityˡ (awaitD , inj₁ (hashᴿ m)) _
            ⟨≈⟩ map-arg _ afterDigest ⟨≈⟩ >>=ₚ-identityˡ _ _

------------------------------------------------------------------------
-- The emulation as an event bound at the machine

-- The simulator is absorbed into the adversary (`UC.Machine.EventBounds.bounded-absorb`),
-- and its two queries per `peekᴬ` (`simQB`) double the adversary's rate.
-- `real-factors` is an exact machine equality, so any bound on the ideal run
-- carries to the real one with no slack.

private
  module 𝒫 = Category 𝒫ᴵ
  open 𝒫.HomReasoning

  variable
    k q : ℕ
    r : ℚ

hf-bounded : AdvBoundedAt (k * 2) q r ideal → AdvBoundedAt k q r real
hf-bounded = bounded-absorb real-factors simQB

hf-exact : (d : Strat (Neg Honᴵ) (Pos Honᴵ)) (a : Proc Advᴵ 𝟭ᴵ) (w : Proc unitᴵ Resᴵ)
         → runᴹ ((plugᴹ a 𝒫.∘ real) 𝒫.∘ w) d ≈ₚ runᴹ ((plugᴹ (a 𝒫.∘ simulator) 𝒫.∘ ideal) 𝒫.∘ w) d
hf-exact d a w = runᴹ-resp-≈ᴹ ((𝒫.∘-resp-≈ʳ real-factors ○ plug-absorb a simulator ideal) ⟩∘⟨refl) d

hf-pr-bound : (d : Strat (Neg Honᴵ) (Pos Honᴵ)) (a : Proc Advᴵ 𝟭ᴵ) (w : Proc unitᴵ Resᴵ)
            → Upper (runᴹ ((plugᴹ (a 𝒫.∘ simulator) 𝒫.∘ ideal) 𝒫.∘ w) d) r
            → Upper (runᴹ ((plugᴹ a 𝒫.∘ real) 𝒫.∘ w) d) r
hf-pr-bound d a w = upper-≈ (hf-exact d a w)
