{-# OPTIONS --safe --without-K --guardedness #-}

-- The toy at the UC model: emulation at a nontrivial grade, and what the
-- simulator spends.
--
-- The grade is `ifaceᵒ Advᴵ`, inhabited by the adversary's `peekᴬ`, and the
-- simulator is `procᵒ simulator : ifaceᵒ Lkᴵ ⇒ ifaceᵒ Advᴵ` — not a scalar, so
-- nothing here is in reach of `UC.Seam.Grounded.subBlind`.  The emulation is
-- exact: `UC.Graded.emulᵍ` turns `real-factors` into it with no error term.
--
-- What the simulator spends is stated twice, at two weightings of the same
-- ledger (`UC.QueryBound.Exact`): `simExactHash` counts ORACLE queries and
-- `simExactAll` counts downward outputs of any kind, so "one hash query per
-- `peekᴬ`" and "two queries per `peekᴬ`" are both equations, not ceilings.
-- `simCert` is the matching upper bound, which is what `UC.Budget` asks for.

open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Graded using (emulᵍ; ≤UCᵍ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using (Certified; QB; certified⇒QB; forget)
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

-- The amortised bound: a `peekᴬ` deposits two units and the simulator's two
-- queries withdraw them, so `Φ` is the number still owed.
Φˢ : SSt → ℕ
Φˢ idleˢ  = 0
Φˢ awaitL = 1
Φˢ awaitD = 0

simCert : Certified 2 simulator
simCert = record
  { Φ      = Φˢ
  ; pointᵍ = returnₚ (idleˢ , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (idleˢ , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  onL : (s : SSt) (a : Pos Lkᴵ) → Dₚ _
  onL awaitL (lkˢ m)  = returnₚ (inj₁ ((awaitD , s≤s z≤n) , hashˢ m))
  onL awaitD (digˢ d) = returnₚ (inj₂ ((idleˢ , z≤n) , wireᴬ d))
  onL idleˢ  _        = botₚ
  onL awaitL (digˢ _) = botₚ
  onL awaitD (lkˢ _)  = botₚ

  onR : (s : SSt) (b : Neg Advᴵ) → Dₚ _
  onR idleˢ  peekᴬ = returnₚ (inj₁ ((awaitL , s≤s (s≤s z≤n)) , leakˢ))
  onR awaitL peekᴬ = botₚ
  onR awaitD peekᴬ = botₚ

  cohL : (s : SSt) (a : Pos Lkᴵ) → mapₚ forget (onL s a) ≈ₚ simStep (s , inj₁ a)
  cohL awaitL (lkˢ m)  = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL awaitD (digˢ d) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL idleˢ  (lkˢ _)  = bot-bind-≈ₚ _
  cohL idleˢ  (digˢ _) = bot-bind-≈ₚ _
  cohL awaitL (digˢ _) = bot-bind-≈ₚ _
  cohL awaitD (lkˢ _)  = bot-bind-≈ₚ _

  cohR : (s : SSt) (b : Neg Advᴵ) → mapₚ forget (onR s b) ≈ₚ simStep (s , inj₂ b)
  cohR idleˢ  peekᴬ = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR awaitL peekᴬ = bot-bind-≈ₚ _
  cohR awaitD peekᴬ = bot-bind-≈ₚ _

simQB : QB 2 simulator
simQB = certified⇒QB simCert

------------------------------------------------------------------------
-- …exactly

-- The ledger is the same for both weightings: `awaitL` is a `peekᴬ` in flight.
Λˢ : SSt → ℕ
Λˢ idleˢ  = 0
Λˢ awaitL = 1
Λˢ awaitD = 0

-- One ORACLE query per `peekᴬ`.
hashes : Neg Lkᴵ ⊎ Pos Advᴵ → ℕ
hashes (inj₁ leakˢ)     = 0
hashes (inj₁ (hashˢ _)) = 1
hashes (inj₂ _)         = 0

peeks : Pos Lkᴵ ⊎ Neg Advᴵ → ℕ
peeks (inj₁ _)     = 0
peeks (inj₂ peekᴬ) = 1

-- …and two queries of ANY kind per `peekᴬ`.
twoPerPeek : Pos Lkᴵ ⊎ Neg Advᴵ → ℕ
twoPerPeek (inj₁ _)     = 0
twoPerPeek (inj₂ peekᴬ) = 2

module EH = Ledger {Lkᴵ} {Advᴵ} SSt (returnₚ idleˢ) simStep hashes peeks
module EA = Ledger {Lkᴵ} {Advᴵ} SSt (returnₚ idleˢ) simStep downward twoPerPeek

private
  -- The three live transitions and the off-protocol rest, shared by the two
  -- certificates: only the arithmetic witness differs, and it is `refl` at both.
  stepᴴ : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ)
        → Dₚ (Σ[ p ∈ SSt × (Neg Lkᴵ ⊎ Pos Advᴵ) ]
               Λˢ s + peeks x ≡ hashes (proj₂ p) + Λˢ (proj₁ p))
  stepᴴ idleˢ  (inj₂ peekᴬ)    = returnₚ ((awaitL , inj₁ leakˢ)      , refl)
  stepᴴ awaitL (inj₁ (lkˢ m))  = returnₚ ((awaitD , inj₁ (hashˢ m))  , refl)
  stepᴴ awaitD (inj₁ (digˢ d)) = returnₚ ((idleˢ  , inj₂ (wireᴬ d))  , refl)
  stepᴴ idleˢ  (inj₁ _)        = botₚ
  stepᴴ awaitL (inj₂ peekᴬ)    = botₚ
  stepᴴ awaitL (inj₁ (digˢ _)) = botₚ
  stepᴴ awaitD (inj₂ peekᴬ)    = botₚ
  stepᴴ awaitD (inj₁ (lkˢ _))  = botₚ

  cohᴴ : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ)
       → mapₚ proj₁ (stepᴴ s x) ≈ₚ simStep (s , x)
  cohᴴ idleˢ  (inj₂ peekᴬ)    = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᴴ awaitL (inj₁ (lkˢ m))  = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᴴ awaitD (inj₁ (digˢ d)) = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᴴ idleˢ  (inj₁ (lkˢ _))  = bot-bind-≈ₚ _
  cohᴴ idleˢ  (inj₁ (digˢ _)) = bot-bind-≈ₚ _
  cohᴴ awaitL (inj₂ peekᴬ)    = bot-bind-≈ₚ _
  cohᴴ awaitL (inj₁ (digˢ _)) = bot-bind-≈ₚ _
  cohᴴ awaitD (inj₂ peekᴬ)    = bot-bind-≈ₚ _
  cohᴴ awaitD (inj₁ (lkˢ _))  = bot-bind-≈ₚ _

simExactHash : EH.QEᵢ
simExactHash = record
  { Λ = Λˢ ; pointᴱ = returnₚ (idleˢ , refl)
  ; coh₀ = >>=ₚ-identityˡ (idleˢ , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ = stepᴴ ; cohᴱ = cohᴴ }

simExactAll : EA.QEᵢ
simExactAll = record
  { Λ = Λˢ ; pointᴱ = returnₚ (idleˢ , refl)
  ; coh₀ = >>=ₚ-identityˡ (idleˢ , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ = stepᴬ ; cohᴱ = cohᴬ }
  where
  stepᴬ : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ)
        → Dₚ (Σ[ p ∈ SSt × (Neg Lkᴵ ⊎ Pos Advᴵ) ]
               Λˢ s + twoPerPeek x ≡ downward (proj₂ p) + Λˢ (proj₁ p))
  stepᴬ idleˢ  (inj₂ peekᴬ)    = returnₚ ((awaitL , inj₁ leakˢ)     , refl)
  stepᴬ awaitL (inj₁ (lkˢ m))  = returnₚ ((awaitD , inj₁ (hashˢ m)) , refl)
  stepᴬ awaitD (inj₁ (digˢ d)) = returnₚ ((idleˢ  , inj₂ (wireᴬ d)) , refl)
  stepᴬ idleˢ  (inj₁ _)        = botₚ
  stepᴬ awaitL (inj₂ peekᴬ)    = botₚ
  stepᴬ awaitL (inj₁ (digˢ _)) = botₚ
  stepᴬ awaitD (inj₂ peekᴬ)    = botₚ
  stepᴬ awaitD (inj₁ (lkˢ _))  = botₚ

  cohᴬ : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ)
       → mapₚ proj₁ (stepᴬ s x) ≈ₚ simStep (s , x)
  cohᴬ idleˢ  (inj₂ peekᴬ)    = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᴬ awaitL (inj₁ (lkˢ m))  = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᴬ awaitD (inj₁ (digˢ d)) = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  cohᴬ idleˢ  (inj₁ (lkˢ _))  = bot-bind-≈ₚ _
  cohᴬ idleˢ  (inj₁ (digˢ _)) = bot-bind-≈ₚ _
  cohᴬ awaitL (inj₂ peekᴬ)    = bot-bind-≈ₚ _
  cohᴬ awaitL (inj₁ (digˢ _)) = bot-bind-≈ₚ _
  cohᴬ awaitD (inj₂ peekᴬ)    = bot-bind-≈ₚ _
  cohᴬ awaitD (inj₁ (lkˢ _))  = bot-bind-≈ₚ _

-- The occurrence statement: on EVERY branch of the simulator's run over an
-- activation word, the number of `hashˢ` queries plus the ledger of the state
-- it ends in is the number of `peekᴬ`s the word asked for.  `runᴱ-erases` says
-- the refined run is the run.
sim-hash-count : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
               → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                      EH.Balanced Λˢ (weight peeks w) p)
sim-hash-count = EH.exactᴱ simExactHash

sim-query-count : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
                → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                       EA.Balanced Λˢ (weight twoPerPeek w) p)
sim-query-count = EA.exactᴱ simExactAll

-- …and when the run ends between transactions the ledger is zero, so the
-- count is exact on the nose.
sim-hash-count-settled : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
                       → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                              (Λˢ (proj₁ p) ≡ 0
                               → weight hashes (proj₂ p) ≡ weight peeks w))
sim-hash-count-settled w = mapₚ settle (sim-hash-count w)
  where
  settle : Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ] EH.Balanced Λˢ (weight peeks w) p
         → Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
             (Λˢ (proj₁ p) ≡ 0 → weight hashes (proj₂ p) ≡ weight peeks w)
  settle z = proj₁ z , λ nil →
    trans (sym (+-identityʳ _))
          (trans (cong (weight hashes (proj₂ (proj₁ z)) +_) (sym nil)) (proj₂ z))
