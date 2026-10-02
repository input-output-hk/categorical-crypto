{-# OPTIONS --safe --without-K --guardedness #-}

-- A watch as a process, and the reader that turns a test into its event.
--
-- `monitorᴹ` relays the honest leg and accumulates the report.  A relay alone
-- cannot detect completion, so `flagReader` puts `flagReadᴹ` ABOVE the test:
-- it waits for the verdict, discards it and answers with the flag; a
-- monitored experiment is `flagReader B` read over `monitorᴹ report ∘ u`.  A
-- test never sees the flag port and cannot forge the bit that replaces its
-- verdict; a test that diverges leaves `flagReadᴹ` in `waitE`, so a flag
-- raised before a divergence is not reported.
--
-- On the process side the monitor collapses with the process it watches into
-- `accᴹ`, whose state carries the accumulator, and the composite IS that
-- accumulator's flag wire (`monitor-flag`): `▷` samples `f ∨ acc′` with
-- `f = acc` and `acc′ = acc ∨ report q b`.  A monitored event is therefore a
-- state event (`UC.Machine.StateEvent`).  Agreement with the strategy-level
-- watch is `UC.Quantitative.EventLift.agree`.

open import Categories.Category

open import Data.Bool.Base
open import Data.Bool.Properties.Ext
open import Data.Maybe.Base
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Machine.StateEvent
open import CategoricalCrypto.UC.QueryBound

import CategoricalCrypto.Machines.Collapse as Col

module CategoricalCrypto.UC.Machine.Monitor where

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The monitor

-- The pending query is state because `report` reads the (query, answer) PAIR
-- and no single message carries it.
MonSt : Iface → Set
MonSt B = Bool × Maybe (Neg B)

monitorStep : {B : Iface} → (Neg B → Pos B → Bool)
            → MonSt B × (Pos B ⊎ (Neg B ⊎ ⊤))
            → Dₚ (MonSt B × (Neg B ⊎ (Pos B ⊎ Bool)))
monitorStep report ((acc , _)     , inj₂ (inj₁ q)) = returnₚ ((acc , just q) , inj₁ q)
monitorStep report ((acc , p)     , inj₂ (inj₂ _)) = returnₚ ((acc , p) , inj₂ (inj₂ acc))
monitorStep report ((acc , just q) , inj₁ a) =
  returnₚ ((acc ∨ report q a , nothing) , inj₂ (inj₁ a))
monitorStep report ((_ , nothing) , inj₁ _) = botₚ

-- The watch as a PROCESS: `Strategy.watchFrom` with its accumulator in a
-- machine state and its verdict on a port.
monitorᴹ : {B : Iface} → (Neg B → Pos B → Bool) → Proc B (B ⊗ᴵ Ωᴵ)
monitorᴹ {B} report = MC.mk (initˢ (MonSt B) (false , nothing)) (monitorStep report)

-- The monitor is query-transparent: every query from above is passed down
-- once, at rate 1 and constant potential.
qbᵢ-monitor : (B : Iface) (report : Neg B → Pos B → Bool)
            → Certified 1 (monitorᴹ report)
qbᵢ-monitor B report = record
  { Φ      = Φ
  ; pointᵍ = returnₚ ((false , nothing) , z≤n)
  ; coh₀   = >>=ₚ-identityˡ ((false , nothing) , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  Φ : MonSt B → ℕ
  Φ _ = 0

  onL : (s : MonSt B) (a : Pos B) → Dₚ (Ans Φ (Neg B) (Pos B ⊎ Bool) (Φ s))
  onL (acc , just q)  a = returnₚ (inj₂ (((acc ∨ report q a , nothing) , z≤n) , inj₁ a))
  onL (_   , nothing) _ = botₚ

  onR : (s : MonSt B) (b : Neg B ⊎ ⊤) → Dₚ (Ans Φ (Neg B) (Pos B ⊎ Bool) (Φ s ℕ.+ 1))
  onR (acc , _) (inj₁ q) = returnₚ (inj₁ (((acc , just q) , s≤s z≤n) , q))
  onR (acc , p) (inj₂ _) = returnₚ (inj₂ (((acc , p) , z≤n) , inj₂ acc))

  cohL : (s : MonSt B) (a : Pos B)
       → mapₚ forget (onL s a) ≈ₚ monitorStep report (s , inj₁ a)
  cohL (_ , just _)  _ = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (_ , nothing) _ = bot-bind-≈ₚ (returnₚ ∘′ forget)

  cohR : (s : MonSt B) (b : Neg B ⊎ ⊤)
       → mapₚ forget (onR s b) ≈ₚ monitorStep report (s , inj₂ b)
  cohR (_ , _) (inj₁ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (_ , _) (inj₂ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)

------------------------------------------------------------------------
-- The monitored process, collapsed

module _ {A B : Iface} (report : Neg B → Pos B → Bool) (u : Proc A B) where

  -- `monitorᴹ`'s bookkeeping on the process's own boundary.
  settle : MonSt B → MC.St u × (Neg A ⊎ Pos B) → Dₚ ((MC.St u × MonSt B) × (Neg A ⊎ Pos B))
  settle mq             (s , inj₁ a) = returnₚ ((s , mq) , inj₁ a)
  settle (acc , just q) (s , inj₂ b) = returnₚ ((s , (acc ∨ report q b , nothing)) , inj₂ b)
  settle (_ , nothing)  (_ , inj₂ _) = botₚ

  accStep : (MC.St u × MonSt B) × (Pos A ⊎ Neg B) → Dₚ ((MC.St u × MonSt B) × (Neg A ⊎ Pos B))
  accStep ((s , mq)      , inj₁ a) = MC.step u (s , inj₁ a) >>=ₚ settle mq
  accStep ((s , (acc , _)) , inj₂ q) = MC.step u (s , inj₂ q) >>=ₚ settle (acc , just q)

  accᴹ : Proc A B
  accᴹ = MC.mk (record { obj = MC.St u × MonSt B
                       ; point = λ x → mapₚ (_, (false , nothing)) (MC.point (MC.state u) x) })
               accStep

  reported : StateTest accᴹ
  reported = proj₁ ∘ proj₂

  private
    Sᴹ : MC.State
    Sᴹ = Col.Sᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos B ⊎ Bool} {Neg B ⊎ ⊤} (monitorᴹ report) u

    kᴹ = Col.kᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos B ⊎ Bool} {Neg B ⊎ ⊤} (monitorᴹ report) u

  open Col.Loop (Pos A ⊎ (Neg B ⊎ ⊤)) (Neg A ⊎ (Pos B ⊎ Bool)) (Neg B ⊎ Pos B) Sᴹ kᴹ

  private
    Out : Set
    Out = (MonSt B × MC.St u) × (Neg A ⊎ (Pos B ⊎ Bool))

    pass : MonSt B → MC.St u × (Neg A ⊎ Pos B) → Dₚ Out
    pass mq             (s , inj₁ a) = returnₚ ((mq , s) , inj₁ a)
    pass (acc , just q) (s , inj₂ b) = returnₚ (((acc ∨ report q b , nothing) , s) , inj₂ (inj₁ b))
    pass (_ , nothing)  (_ , inj₂ _) = botₚ

    colStep : (MonSt B × MC.St u) × (Pos A ⊎ (Neg B ⊎ ⊤)) → Dₚ Out
    colStep ((mq , s)        , inj₁ a)        = MC.step u (s , inj₁ a) >>=ₚ pass mq
    colStep (((acc , _) , s) , inj₂ (inj₁ q)) = MC.step u (s , inj₂ q) >>=ₚ pass (acc , just q)
    colStep (((acc , p) , s) , inj₂ (inj₂ _)) = returnₚ (((acc , p) , s) , inj₂ (inj₂ acc))

    upass : (mq : MonSt B) (r : MC.St u × (Neg A ⊎ Pos B))
          → (returnₚ ((mq , proj₁ r) , Col.outᶠ (proj₂ r)) >>=ₚ contᵢ body) ≈ₚ pass mq r
    upass mq             (s , inj₁ a) = >>=ₚ-identityˡ _ _
    upass (acc , just q) (s , inj₂ b) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ loop-pass ((acc , just q) , s) (inj₂ b) ((acc ∨ report q b , nothing) , s) (inj₁ (inj₂ (inj₁ b)))
                    (>>=ₚ-identityˡ _ _)
    upass (acc , nothing) (s , inj₂ b) =
      >>=ₚ-identityˡ _ _ ⟨≈⟩ loop-bot ((acc , nothing) , s) (inj₂ b) (bot-bind-≈ₚ _)

    upump : (mq : MonSt B) (d : Dₚ (MC.St u × (Neg A ⊎ Pos B)))
          → ((d >>=ₚ λ r → returnₚ ((mq , proj₁ r) , Col.outᶠ (proj₂ r))) >>=ₚ contᵢ body)
            ≈ₚ (d >>=ₚ pass mq)
    upump mq d = >>=ₚ-assoc d _ _ ⟨≈⟩ bindᶠ (upass mq)

    col-step : (z : MC.obj Sᴹ × (Pos A ⊎ (Neg B ⊎ ⊤))) → MC.step tracedᴹ z ≈ₚ colStep z
    col-step ((mq , s) , inj₁ a) = step-red (mq , s) (inj₁ a) ⟨≈⟩ upump mq (MC.step u (s , inj₁ a))
    col-step (((acc , p) , s) , inj₂ (inj₁ q)) =
          step-red ((acc , p) , s) (inj₂ (inj₁ q))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ ((acc , just q) , inj₁ q) _)
      ⟨≈⟩ >>=ₚ-identityˡ (((acc , just q) , s) , inj₂ (inj₁ q)) _
      ⟨≈⟩ iterₚ-fix body (((acc , just q) , s) , inj₁ q)
      ⟨≈⟩ upump (acc , just q) (MC.step u (s , inj₂ q))
    col-step (((acc , p) , s) , inj₂ (inj₂ _)) =
          step-red ((acc , p) , s) (inj₂ (inj₂ tt))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ ((acc , p) , inj₂ (inj₂ acc)) _)
      ⟨≈⟩ >>=ₚ-identityˡ (((acc , p) , s) , inj₁ (inj₂ (inj₂ acc))) _

    ψ : MonSt B × MC.St u → (MC.St u × MonSt B) × Bool
    ψ (mq , s) = (s , mq) , proj₁ mq

    -- The flag `▷` samples at a completed answer is the accumulator already.
    sampled : (mq : MonSt B) (r : MC.St u × (Neg A ⊎ Pos B))
            → (pass mq r >>=ₚ λ o → returnₚ (ψ (proj₁ o) , proj₂ o))
              ≈ₚ mapₚ (sample accᴹ reported (proj₁ mq)) (settle mq r)
    sampled mq (s , inj₁ a) = >>=ₚ-identityˡ _ _ ⟨≈⟩ ≈sym (>>=ₚ-identityˡ _ _)
    sampled (acc , just q) (s , inj₂ b) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ ret≡ (cong (λ z → ((s , (acc ∨ report q b , nothing)) , z) , inj₂ (inj₁ b))
                     (sym (∨-idemˡ acc (report q b))))
      ⟨≈⟩ ≈sym (>>=ₚ-identityˡ _ _)
    sampled (acc , nothing) (s , inj₂ b) = bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)

    via : (mq : MonSt B) (d : Dₚ (MC.St u × (Neg A ⊎ Pos B)))
        → ((d >>=ₚ pass mq) >>=ₚ λ o → returnₚ (ψ (proj₁ o) , proj₂ o))
          ≈ₚ mapₚ (sample accᴹ reported (proj₁ mq)) (d >>=ₚ settle mq)
    via mq d = >>=ₚ-assoc d _ _ ⟨≈⟩ bindᶠ (sampled mq) ⟨≈⟩ ≈sym (>>=ₚ-assoc d _ _)

    col≲flag : MC.mk Sᴹ colStep S.≲ (accᴹ ▷ reported)
    col≲flag = simFn ψ pt st
      where
      pt : (x : _) → (MC.point Sᴹ x >>=ₚ λ s → returnₚ (ψ s)) ≈ₚ MC.point (▷state accᴹ reported) x
      pt x = bindˣ (point-⊛ (MC.state (monitorᴹ report)) (MC.state u) x)
         ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (false , nothing) _)
         ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state u) x) _ _
         ⟨≈⟩ bindᶠ (λ s → >>=ₚ-identityˡ ((false , nothing) , s) _)
         ⟨≈⟩ ≈sym (bind-map (MC.point (MC.state u) x) _ _)

      st : (p : _) → _
      st ((mq , s) , inj₁ a)              = via mq (MC.step u (s , inj₁ a))
      st (((acc , p) , s) , inj₂ (inj₁ q)) = via (acc , just q) (MC.step u (s , inj₂ q))
      st (((acc , p) , s) , inj₂ (inj₂ _)) = >>=ₚ-identityˡ _ _

  -- The crux: the monitor over the process is the accumulator's flag wire.
  monitor-flag : 𝒫._≈_ (monitorᴹ report 𝒫.∘ u) (accᴹ ▷ reported)
  monitor-flag =
         S.⟺ᴹ (Col.compose-raw≈∘ᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos B ⊎ Bool} {Neg B ⊎ ⊤}
                                  (monitorᴹ report) u)
    S.○ᴹ Col.collapseᵀ {Pos A} {Neg A} {Pos B} {Neg B} {Pos B ⊎ Bool} {Neg B ⊎ ⊤} (monitorᴹ report) u
    S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong col-step)
    S.○ᴹ S.≲⇒≈ᴹ col≲flag

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
module Read (D : Iface) (E : Proc D Ωᴵ) where
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
