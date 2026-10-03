{-# OPTIONS --safe --without-K --guardedness #-}

-- Reading a state event in an ordinary experiment: the experiment `E , m` at
-- `B` is run against `M ▷ P`, and `flagReader` puts `flagReadᴹ` ABOVE the test:
-- it waits for the verdict, discards it and answers the flag.  No state is
-- projected out of a composite; the flag is an interface message, and a test
-- never sees the flag port, so it cannot forge the bit that replaces its
-- verdict.
--
-- The completed-run convention is `flagReadᴹ`'s: a test that diverges leaves
-- the reader in `waitE`, so a flag raised before a divergence is not reported.
-- At an embedded strategy the reading is `flagStrat`
-- (`UC.Machine.StateEvent.Agree`); at a protocol image it is
-- `Protocol.Observe.PrHit` (`UC.Machine.StateEvent.Adequacy`).

open import Categories.Category using (Category)

open import Data.Bool.Base
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ)
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Function.Base

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Protocol.Machine.Run
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Machine.StateEvent

import CategoricalCrypto.Machines.Collapse as Col

module CategoricalCrypto.UC.Machine.StateEvent.Read where

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- Reading the flag when the test finishes

data FlagSt : Set where
  idle waitE waitF : FlagSt

flagReadStep : FlagSt × ((Bool ⊎ Bool) ⊎ ⊤) → Dₚ (FlagSt × ((⊤ ⊎ ⊤) ⊎ Bool))
flagReadStep (idle  , inj₂ _)        = returnₚ (waitE , inj₁ (inj₁ tt))
flagReadStep (waitE , inj₁ (inj₁ _)) = returnₚ (waitF , inj₁ (inj₂ tt))
flagReadStep (waitF , inj₁ (inj₂ b)) = returnₚ (idle  , inj₂ b)
flagReadStep _                       = botₚ

flagReadᴹ : Proc (Ωᴵ ⊗ᴵ Ωᴵ) Ωᴵ
flagReadᴹ = MC.mk (initˢ FlagSt idle) flagReadStep

flagReader : (B : Iface) → Reader B (B ⊗ᴵ Ωᴵ)
flagReader B Y E = flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ a⇐ᴵ)

------------------------------------------------------------------------
-- The test with the flag reader over it, as one machine

-- `flagReadᴹ ∘ subᴵ E` collapsed: the loop between the two runs at most two
-- passes, so the composite's step is the test's own, post-processed by where
-- the flag reader is in its cycle.
module Collapsed (D : Iface) (E : Proc D Ωᴵ) where
  open MC
  open S

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

  private
    Sᴿ : State
    Sᴿ = Col.Sᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                flagReadᴹ (subᴵ E)

  readᴹ : Proc (D ⊗ᴵ Ωᴵ) Ωᴵ
  readᴹ = mk Sᴿ readStep

  private
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
      ⟨≈⟩ iterₚ-fix body ((waitE , se) , inj₁ (inj₁ tt))
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
-- The reading

stateRead : {A B : Iface} (Y : Iface) (M : Proc A B) → StateTest M
          → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool
stateRead {B = B} Y M P = readRun Y (M ▷ P) (flagReader B)

-- The strategy-level closing experiment: play `d`, ignore its verdict, ask
-- the flag.  An answer off the protocol scores `false`.
flagStrat : {Q R : Set} → Strat Q R → Strat (Q ⊎ ⊤) (R ⊎ Bool)
flagStrat (out _)    = ask (inj₂ tt) [ (λ _ → out false) , out ]
flagStrat (ask q k)  = ask (inj₁ q) [ flagStrat ∘ k , (λ _ → out false) ]
flagStrat (coin μ k) = coin μ (flagStrat ∘ k)

------------------------------------------------------------------------
-- The bound, as an instance of `UC.Machine.EventBounds`

StateBoundedAt : {A B : Iface} → ℕ → ℚ → (M : Proc A B) → StateTest M → Set₁
StateBoundedAt {B = B} q r M P = BoundedAt q r (M ▷ P) (flagReader B)

module _ {A B : ℕ → Iface} (M : (n : ℕ) → Proc (A n) (B n))
         (P : (n : ℕ) → StateTest (M n)) where

  StateBoundedᶠ : (ℕ → ℕ → ℚ) → Set₁
  StateBoundedᶠ = Boundedᶠ (λ n → M n ▷ P n) (λ n → flagReader (B n))

  StateBoundedᴺ : (ℕ → ℕ → ℚ) → Set₁
  StateBoundedᴺ = Boundedᴺ (λ n → M n ▷ P n) (λ n → flagReader (B n))

------------------------------------------------------------------------
-- Invariance

-- Exact, at any `A`.
transportᵉ : {A B : Iface} {q : ℕ} {r : ℚ} {R I : Proc A B} {P : StateTest R} {Q : StateTest I}
           → EventSim (R , P) (I , Q) → StateBoundedAt q r I Q → StateBoundedAt q r R P
transportᵉ {B = B} e h Y E m qE qm le =
  upper-≈ (readRun-resp-≈ Y (S.≲⇒≈ᴹ (▷-≲ e)) (flagReader B) E m) (h Y E m qE qm le)
