{-# OPTIONS --safe --without-K --guardedness #-}

-- Monitor agreement at embedded strategies: `docs/event-bounds-in-setup.md`
-- §2 obligation 4.
--
-- `stratTest` is the test an ordinary finite strategy embeds to, and `Read`
-- collapses the flag reader over a test into one machine.  `flag-agree` runs
-- the accumulator's flag wire (`UC.Machine.Monitor.accᴹ`) at `flagStrat d`:
-- it IS the run of the process under the watch, as `_≈ₚ_`, because the flag
-- equals the accumulator along the run.

open import Categories.Category using (Category)

open import Data.Bool.Base
open import Data.Bool.Properties.Ext
open import Data.Empty
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; subst; trans)

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.StateEvent
open import CategoricalCrypto.UC.Machine.StateEvent.Read
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Compose.Laws
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Budget

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Monitor.Agree where

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- A strategy embedded as a test

-- `UC.Seam.strategyEnv` read on the compiler's own domain: the ancilla is
-- trivial, so the empty summand is eliminated.
outᵁ : (B : Iface) → Neg B ⊎ Bool → (Pos unitᴵ ⊎ Neg B) ⊎ Bool
outᵁ B (inj₁ q) = inj₁ (inj₂ q)
outᵁ B (inj₂ v) = inj₂ v

stepᵁ : (B : Iface) → EnvSt B × ((Pos unitᴵ ⊎ Pos B) ⊎ ⊤)
      → Dₚ (EnvSt B × ((Neg unitᴵ ⊎ Neg B) ⊎ Bool))
stepᵁ B (se , inj₁ (inj₁ ()))
stepᵁ B (se , inj₁ (inj₂ p)) = mapₚ (λ z → proj₁ z , outᵁ B (proj₂ z)) (stepˢ B (se , inj₁ p))
stepᵁ B (se , inj₂ _)        = mapₚ (λ z → proj₁ z , outᵁ B (proj₂ z)) (stepˢ B (se , inj₂ tt))

stratTest : (B : Iface) → Strat (Neg B) (Pos B) → Proc (unitᴵ ⊗ᴵ B) Ωᴵ
stratTest B d = mk (stateˢ B d) (stepᵁ B)

stratTest-embeds : (B : Iface) (d : Strat (Neg B) (Pos B))
                 → 𝒫._≈_ {unitᴵ ⊗ᴵ B} {Ωᴵ} (stratTest B d) (strategyEnv B d 𝒫.∘ λᴵ⇒)
stratTest-embeds B d =
  ⟺ᴹ (∘-wireᴹ [ ⊥-elim , id ] inj₂ (strategyEnv B d) ○ᴹ ≲⇒≈ᴹ (mk-cong pt))
  where
  pt : (z : _) → _
  pt (se , inj₁ (inj₁ ()))
  pt (se , inj₁ (inj₂ p)) =
    map-eq (stepˢ B (se , inj₁ p)) _ _ λ where (_ , inj₁ _) → refl
                                               (_ , inj₂ _) → refl
  pt (se , inj₂ _) =
    map-eq (stepˢ B (se , inj₂ tt)) _ _ λ where (_ , inj₁ _) → refl
                                                (_ , inj₂ _) → refl

qb-stratTest : (B : Iface) {q : ℕ} (d : Strat (Neg B) (Pos B)) → asks≤ q d
             → QB q (stratTest B d)
qb-stratTest B {q} d a =
  qb-resp-≈ (𝒫.Equiv.sym (stratTest-embeds B d))
    (subst (λ k → QB k (strategyEnv B d 𝒫.∘ λᴵ⇒)) (ℕP.*-identityʳ q)
      (qb-∘-category (unitᴵ ⊗ᴵ B) B Ωᴵ (strategyEnv B d) λᴵ⇒
        (qb-strategyEnv B q d a) qb-λᴵ⇒))

m₀ : Proc unitᴵ (unitᴵ ⊗ᴵ unitᴵ)
m₀ = λᴵ⇐

------------------------------------------------------------------------
-- The test with the flag reader over it, as one machine

-- `flagReadᴹ ∘ subᴵ E` collapsed: the loop between the two runs at most two
-- passes, so the composite's step is the test's own, post-processed by where
-- the flag reader is in its cycle.
module Read (D : Iface) (E : Proc D Ωᴵ) where

  efOut : FlagSt → St E × (Neg D ⊎ Bool) → Dₚ ((FlagSt × St E) × ((Neg D ⊎ ⊤) ⊎ Bool))
  efOut fs    (se , inj₁ q) = returnₚ ((fs    , se) , inj₁ (inj₁ q))
  efOut waitE (se , inj₂ _) = returnₚ ((waitF , se) , inj₁ (inj₂ tt))
  efOut idle  (se , inj₂ _) = botₚ
  efOut waitF (se , inj₂ _) = botₚ

  readStep : (FlagSt × St E) × ((Pos D ⊎ Bool) ⊎ ⊤)
           → Dₚ ((FlagSt × St E) × ((Neg D ⊎ ⊤) ⊎ Bool))
  readStep ((fs    , se) , inj₁ (inj₁ p)) = step E (se , inj₁ p) >>=ₚ efOut fs
  readStep ((idle  , se) , inj₁ (inj₂ _)) = botₚ
  readStep ((waitE , se) , inj₁ (inj₂ _)) = botₚ
  readStep ((waitF , se) , inj₁ (inj₂ b)) = returnₚ ((idle , se) , inj₂ b)
  readStep ((idle  , se) , inj₂ _)        = step E (se , inj₂ tt) >>=ₚ efOut waitE
  readStep ((waitE , se) , inj₂ _)        = botₚ
  readStep ((waitF , se) , inj₂ _)        = botₚ

  readᴹ : Proc (D ⊗ᴵ Ωᴵ) Ωᴵ
  readᴹ = mk (Col.Sᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                     flagReadᴹ (subᴵ E))
             readStep

  private
    Sᴿ : State
    Sᴿ = Col.Sᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                flagReadᴹ (subᴵ E)

    kᴿ : obj Sᴿ × (((Pos D ⊎ Bool) ⊎ ⊤) ⊎ ((⊤ ⊎ ⊤) ⊎ (Bool ⊎ Bool)))
       → Dₚ (obj Sᴿ × (((Neg D ⊎ ⊤) ⊎ Bool) ⊎ ((⊤ ⊎ ⊤) ⊎ (Bool ⊎ Bool))))
    kᴿ = Col.kᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                flagReadᴹ (subᴵ E)

  open Col.Loop ((Pos D ⊎ Bool) ⊎ ⊤) ((Neg D ⊎ ⊤) ⊎ Bool) ((⊤ ⊎ ⊤) ⊎ (Bool ⊎ Bool)) Sᴿ kᴿ

  private
    relayᴰ : FlagSt → St E × (Neg D ⊎ Bool)
           → Dₚ ((FlagSt × St E) × (((Neg D ⊎ ⊤) ⊎ Bool) ⊎ ((⊤ ⊎ ⊤) ⊎ (Bool ⊎ Bool))))
    relayᴰ fs (se , inj₁ q) = returnₚ ((fs , se) , inj₁ (inj₁ (inj₁ q)))
    relayᴰ fs (se , inj₂ v) = returnₚ ((fs , se) , inj₂ (inj₂ (inj₁ v)))

    verdict-pass : (fs : FlagSt) (se : St E) (v : Bool)
                 → iterₚ body ((fs , se) , inj₂ (inj₁ v)) ≈ₚ efOut fs (se , inj₂ v)
    verdict-pass idle  se v = loop-bot (idle  , se) (inj₂ (inj₁ v)) (bot-bind-≈ₚ _)
    verdict-pass waitF se v = loop-bot (waitF , se) (inj₂ (inj₁ v)) (bot-bind-≈ₚ _)
    verdict-pass waitE se v =
        loop-pass (waitE , se) (inj₂ (inj₁ v)) (waitF , se) (inj₂ (inj₁ (inj₂ tt)))
                  (>>=ₚ-identityˡ (waitF , inj₁ (inj₂ tt)) _)
      ⟨≈⟩ loop-pass (waitF , se) (inj₁ (inj₂ tt)) (waitF , se) (inj₁ (inj₁ (inj₂ tt)))
                    (>>=ₚ-identityˡ (se , inj₁ (inj₂ tt)) _)

    pump : (fs : FlagSt) (dE : Dₚ (St E × (Neg D ⊎ Bool)))
         → ((dE >>=ₚ relayᴰ fs) >>=ₚ contᵢ body) ≈ₚ (dE >>=ₚ efOut fs)
    pump fs dE = >>=ₚ-assoc dE (relayᴰ fs) (contᵢ body) ⟨≈⟩ bindᶠ out-case
      where
      out-case : (z : St E × (Neg D ⊎ Bool))
               → (relayᴰ fs z >>=ₚ contᵢ body) ≈ₚ efOut fs z
      out-case (se , inj₁ q) = >>=ₚ-identityˡ ((fs , se) , inj₁ (inj₁ (inj₁ q))) _
      out-case (se , inj₂ v) = >>=ₚ-identityˡ ((fs , se) , inj₂ (inj₂ (inj₁ v))) _
                         ⟨≈⟩ verdict-pass fs se v

    relay-red : (fs : FlagSt) (se : St E) (x : Pos D ⊎ ⊤)
              → (step (subᴵ E) (se , Sum.map inj₁ inj₁ x) >>=ₚ
                 λ r → returnₚ ((fs , proj₁ r) , Col.outᶠ (proj₂ r)))
                ≈ₚ (step E (se , x) >>=ₚ relayᴰ fs)
    relay-red fs se (inj₁ p) = bind-map (step E (se , inj₁ p)) _ _
                         ⟨≈⟩ bindᶠ λ where (_ , inj₁ _) → ≈refl
                                           (_ , inj₂ _) → ≈refl
    relay-red fs se (inj₂ _) = bind-map (step E (se , inj₂ tt)) _ _
                         ⟨≈⟩ bindᶠ λ where (_ , inj₁ _) → ≈refl
                                           (_ , inj₂ _) → ≈refl

    read-step : (z : obj Sᴿ × ((Pos D ⊎ Bool) ⊎ ⊤)) → step tracedᴹ z ≈ₚ readStep z
    read-step ((fs , se) , inj₁ (inj₁ p)) =
        step-red (fs , se) (inj₁ (inj₁ p))
      ⟨≈⟩ bindˣ (relay-red fs se (inj₁ p)) ⟨≈⟩ pump fs (step E (se , inj₁ p))
    read-step ((idle  , se) , inj₁ (inj₂ b)) =
        step-red (idle , se) (inj₁ (inj₂ b))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (se , inj₂ (inj₂ b)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((idle , se) , inj₂ (inj₂ (inj₂ b))) _
      ⟨≈⟩ loop-bot (idle , se) (inj₂ (inj₂ b)) (bot-bind-≈ₚ _)
    read-step ((waitE , se) , inj₁ (inj₂ b)) =
        step-red (waitE , se) (inj₁ (inj₂ b))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (se , inj₂ (inj₂ b)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((waitE , se) , inj₂ (inj₂ (inj₂ b))) _
      ⟨≈⟩ loop-bot (waitE , se) (inj₂ (inj₂ b)) (bot-bind-≈ₚ _)
    read-step ((waitF , se) , inj₁ (inj₂ b)) =
        step-red (waitF , se) (inj₁ (inj₂ b))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (se , inj₂ (inj₂ b)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((waitF , se) , inj₂ (inj₂ (inj₂ b))) _
      ⟨≈⟩ loop-pass (waitF , se) (inj₂ (inj₂ b)) (idle , se) (inj₁ (inj₂ b))
                    (>>=ₚ-identityˡ (idle , inj₂ b) _)
    read-step ((idle , se) , inj₂ _) =
        step-red (idle , se) (inj₂ tt)
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (waitE , inj₁ (inj₁ tt)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((waitE , se) , inj₂ (inj₁ (inj₁ tt))) _
      ⟨≈⟩ loop-fix (waitE , se) (inj₁ (inj₁ tt))
      ⟨≈⟩ bindˣ (relay-red waitE se (inj₂ tt))
      ⟨≈⟩ pump waitE (step E (se , inj₂ tt))
    read-step ((waitE , se) , inj₂ _) =
        step-red (waitE , se) (inj₂ tt) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _
    read-step ((waitF , se) , inj₂ _) =
        step-red (waitF , se) (inj₂ tt) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _

  read-collapse : 𝒫._≈_ {D ⊗ᴵ Ωᴵ} {Ωᴵ} (flagReadᴹ 𝒫.∘ subᴵ E) readᴹ
  read-collapse =
       ⟺ᴹ (Col.compose-raw≈∘ᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                              flagReadᴹ (subᴵ E))
    ○ᴹ Col.collapseᵀ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                     flagReadᴹ (subᴵ E)
    ○ᴹ ≲⇒≈ᴹ (mk-cong read-step)

------------------------------------------------------------------------
-- Agreement

module _ {B : Iface} (report : Neg B → Pos B → Bool) (u : Proc unitᴵ B) where

  private
    w = accᴹ report u ▷ reported report u

    run-flag : (s : MC.St u) (a : Bool) (p : Maybe (Neg B)) (f : Bool) → f ≡ a
             → (d : Strat (Neg B) (Pos B))
             → runᴹFrom w ((s , (a , p)) , f) (flagStrat d) ≈ₚ runᴹFrom u s (watchFrom report a d)
    run-flag s a p f refl (out _)    = >>=ₚ-identityˡ _ _
    run-flag s a p f eq   (coin μ k) = bindᶠ λ c → run-flag s a p f eq (k c)
    run-flag s a p f eq   (ask q k)  =
          bind-map (MC.step u (s , inj₂ q) >>=ₚ settle report u (a , just q)) _ _
      ⟨≈⟩ >>=ₚ-assoc (MC.step u (s , inj₂ q)) _ _
      ⟨≈⟩ bindᶠ λ where
            (_  , inj₁ ())
            (s′ , inj₂ b) →
                  >>=ₚ-identityˡ _ _
              ⟨≈⟩ run-flag s′ (a ∨ report q b) nothing _
                    (trans (cong (_∨ (a ∨ report q b)) eq) (∨-idemˡ a (report q b)))
                    (k b)

  flag-agree : (d : Strat (Neg B) (Pos B))
             → runᴹ (accᴹ report u ▷ reported report u) (flagStrat d) ≈ₚ runᴹ u (watchFrom report false d)
  flag-agree d = bind-map (mapₚ _ (MC.point (MC.state u) ttᵛ)) _ _
             ⟨≈⟩ bind-map (MC.point (MC.state u) ttᵛ) _ _
             ⟨≈⟩ bindᶠ (λ s → run-flag s false nothing false refl d)
