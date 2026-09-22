{-# OPTIONS --safe --without-K --guardedness #-}

-- Compiling a watch into a machine test: the monitor relay, the completion
-- reader above the test, and the allowance the composite is certified at.
--
-- A relay alone cannot detect completion, so the compiled test is a sandwich:
-- `monitorᴹ` on the honest leg accumulates the report, the original test runs
-- through it, and `flagReadᴹ` sits ABOVE the test, waits for its verdict,
-- discards it and answers with the flag.  A test never sees the flag port and
-- cannot forge the bit that replaces its verdict; a test that diverges leaves
-- `flagReadᴹ` in `waitE`, so a flag raised before a divergence is not
-- reported.
--
-- What this module does NOT establish is semantic agreement with the
-- strategy-level watch it implements; the behaviour pins below are checks, not
-- that theorem (`docs/event-bounds-in-setup.md`, work package A).
--
-- `κμ` is the COARSE certificate of the compiled test — the resource a
-- quantitative comparison is instantiated at.  It is neither the
-- environment's own query count nor the queries spent retrieving the flag,
-- and `κμ 0 = 2` is not a claim that monitoring doubles honest queries:
-- `ctxBudget` cannot tell a flag-port query from one on the honest interface
-- (`UC.Budget`'s header prices the port-specific bound that could).

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; _∨_; false)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base as ℕ using (ℕ; s≤s; z≤n)
open import Data.Nat.Poly using (Poly; poly-*; poly-const; poly-⊔)
open import Data.Nat.Properties using (*-identityʳ; ≤-reflexive)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)

open import ProbabilisticLogic.Dp
  using (Dₚ; botₚ; bot-bind-≈ₚ; mapₚ; returnₚ; _≈ₚ_; >>=ₚ-identityˡ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; T₁ᴵ; a⇒ᴵ; subᴵ)
open import CategoricalCrypto.UC.Machine.Grading using (qb-subᴵ)
open import CategoricalCrypto.UC.QueryBound
  using (Ans; Certified; QB; certified⇒QB; forget; qb-mono; qbᵢ-T₁; qbᵢ-wire)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Machine.Monitor where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The flag port and the monitor

-- A one-bit query port: ticked, answering a Boolean.  It is `Ωᴵ`'s shape for
-- `Ωᴵ`'s reason — a machine is reactive, so the bit has to be asked for.
Flagᴵ : Iface
Flagᴵ = Bool ⇿ ⊤

-- The monitor's state: the accumulated report, and the query an answer is
-- still owed to.  The pending query is state because `report` reads the
-- (query, answer) PAIR and no single message carries it.
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

-- The watch as a PROCESS: `Examples.ChimericLedger.Observable.auditWatchFrom`
-- with its accumulator in a machine state and its verdict on a port.
monitorᴹ : {B : Iface} → (Neg B → Pos B → Bool) → Proc B (B ⊗ᴵ Flagᴵ)
monitorᴹ {B} report = MC.mk stateᴹ (monitorStep report)
  where
  stateᴹ : MC.State
  stateᴹ = record
    { obj = MonSt B ; point = λ _ → returnₚ (false , nothing)
    ; discard = λ _ → returnₚ ttᵛ }

------------------------------------------------------------------------
-- Reading the flag when the test finishes

data FlagSt : Set where
  idle waitE waitF : FlagSt

flagReadStep : FlagSt × ((Bool ⊎ Bool) ⊎ ⊤) → Dₚ (FlagSt × ((⊤ ⊎ ⊤) ⊎ Bool))
flagReadStep (idle  , inj₂ _)        = returnₚ (waitE , inj₁ (inj₁ tt))
flagReadStep (waitE , inj₁ (inj₁ _)) = returnₚ (waitF , inj₁ (inj₂ tt))
flagReadStep (waitF , inj₁ (inj₂ b)) = returnₚ (idle  , inj₂ b)
flagReadStep _                       = botₚ

flagReadᴹ : Proc (Ωᴵ ⊗ᴵ Flagᴵ) Ωᴵ
flagReadᴹ = MC.mk stateᴹ flagReadStep
  where
  stateᴹ : MC.State
  stateᴹ = record
    { obj = FlagSt ; point = λ _ → returnₚ idle ; discard = λ _ → returnₚ ttᵛ }

compileᴹ : (Y B : Iface) → Proc B (B ⊗ᴵ Flagᴵ) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B) Ωᴵ
compileᴹ Y B μ E = flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ (a⇒ᴵ 𝒫.∘ T₁ᴵ Y μ))

------------------------------------------------------------------------
-- The certificates

qbᵢ-monitor : (B : Iface) (report : Neg B → Pos B → Bool)
            → Certified 1 (monitorᴹ report)
qbᵢ-monitor B report = record
  { Φ      = λ _ → 0
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

  onL : (s : MonSt B) (a : Pos B)
      → Dₚ (Ans Φ (Neg B) (Pos B ⊎ Bool) (Φ s))
  onL (acc , just q)  a = returnₚ (inj₂ (((acc ∨ report q a , nothing) , z≤n) , inj₁ a))
  onL (_   , nothing) _ = botₚ

  onR : (s : MonSt B) (b : Neg B ⊎ ⊤)
      → Dₚ (Ans Φ (Neg B) (Pos B ⊎ Bool) (Φ s ℕ.+ 1))
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

-- Reading the flag is a SECOND downward activation of the compiled test's own,
-- so the flag reader is 2-bounded and not 1-bounded, and no potential makes it
-- 1: at `waitE` one unit is already owed.
Φᶠ : FlagSt → ℕ
Φᶠ idle  = 0
Φᶠ waitE = 1
Φᶠ waitF = 0

qbᵢ-flagRead : Certified 2 flagReadᴹ
qbᵢ-flagRead = record
  { Φ      = Φᶠ
  ; pointᵍ = returnₚ (idle , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (idle , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  onL : (s : FlagSt) (a : Bool ⊎ Bool) → Dₚ (Ans Φᶠ (⊤ ⊎ ⊤) Bool (Φᶠ s))
  onL idle  _        = botₚ
  onL waitE (inj₁ _) = returnₚ (inj₁ ((waitF , s≤s z≤n) , inj₂ tt))
  onL waitE (inj₂ _) = botₚ
  onL waitF (inj₁ _) = botₚ
  onL waitF (inj₂ b) = returnₚ (inj₂ ((idle , z≤n) , b))

  onR : (s : FlagSt) (b : ⊤) → Dₚ (Ans Φᶠ (⊤ ⊎ ⊤) Bool (Φᶠ s ℕ.+ 2))
  onR idle  _ = returnₚ (inj₁ ((waitE , s≤s (s≤s z≤n)) , inj₁ tt))
  onR waitE _ = botₚ
  onR waitF _ = botₚ

  cohL : (s : FlagSt) (a : Bool ⊎ Bool)
       → mapₚ forget (onL s a) ≈ₚ flagReadStep (s , inj₁ a)
  cohL idle  _        = bot-bind-≈ₚ (returnₚ ∘′ forget)
  cohL waitE (inj₁ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL waitE (inj₂ _) = bot-bind-≈ₚ (returnₚ ∘′ forget)
  cohL waitF (inj₁ _) = bot-bind-≈ₚ (returnₚ ∘′ forget)
  cohL waitF (inj₂ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)

  cohR : (s : FlagSt) (b : ⊤) → mapₚ forget (onR s b) ≈ₚ flagReadStep (s , inj₂ b)
  cohR idle  _ = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR waitE _ = bot-bind-≈ₚ (returnₚ ∘′ forget)
  cohR waitF _ = bot-bind-≈ₚ (returnₚ ∘′ forget)

-- The relay costs nothing, the flag read doubles.
κμ : ℕ → ℕ
κμ c = 2 ℕ.* (c ℕ.⊔ 1)

qb-compileᴹ : (Y B : Iface) (report : Neg B → Pos B → Bool) {c : ℕ}
              (E : Proc (Y ⊗ᴵ B) Ωᴵ) → QB c E
            → QB (κμ c) (compileᴹ Y B (monitorᴹ report) E)
qb-compileᴹ Y B report {c} E qE =
  qb-mono (≤-reflexive (cong (2 ℕ.*_) (*-identityʳ (c ℕ.⊔ 1))))
    (qb-∘-category (Y ⊗ᴵ B) (Ωᴵ ⊗ᴵ Flagᴵ) Ωᴵ flagReadᴹ _
      (certified⇒QB qbᵢ-flagRead)
      (qb-∘-category (Y ⊗ᴵ B) ((Y ⊗ᴵ B) ⊗ᴵ Flagᴵ) (Ωᴵ ⊗ᴵ Flagᴵ) (subᴵ E) _
        (qb-subᴵ (Y ⊗ᴵ B) Ωᴵ Flagᴵ E qE)
        (qb-∘-category (Y ⊗ᴵ B) (Y ⊗ᴵ (B ⊗ᴵ Flagᴵ)) ((Y ⊗ᴵ B) ⊗ᴵ Flagᴵ) a⇒ᴵ _
          (certified⇒QB (qbᵢ-wire ⊎assocˡ ⊎assocʳ))
          (certified⇒QB (qbᵢ-T₁ Y B (B ⊗ᴵ Flagᴵ) (monitorᴹ report)
                                (qbᵢ-monitor B report))))))

poly-κμ : (p : ℕ → ℕ) → Poly p → Poly (λ n → κμ (p n))
poly-κμ _ Pp = poly-* (poly-const 2) (poly-⊔ Pp (poly-const 1))

------------------------------------------------------------------------
-- The three behaviours the compiler is accepted on, at the steps deciding them

module _ {B : Iface} (report : Neg B → Pos B → Bool) (acc : Bool) where

  -- Traffic agreement: the query goes down unchanged and is remembered, the
  -- answer comes up unchanged, and the report is read off the PAIR.
  monitor-query : (p : Maybe (Neg B)) (q : Neg B)
                → monitorStep report ((acc , p) , inj₂ (inj₁ q))
                  ≡ returnₚ ((acc , just q) , inj₁ q)
  monitor-query _ _ = refl

  monitor-answer : (q : Neg B) (a : Pos B)
                 → monitorStep report ((acc , just q) , inj₁ a)
                   ≡ returnₚ ((acc ∨ report q a , nothing) , inj₂ (inj₁ a))
  monitor-answer _ _ = refl

  monitor-flag : (p : Maybe (Neg B))
               → monitorStep report ((acc , p) , inj₂ (inj₂ tt))
                 ≡ returnₚ ((acc , p) , inj₂ (inj₂ acc))
  monitor-flag _ = refl

-- Completion is the test's own verdict emission, seen from above; the verdict
-- is DISCARDED and the flag asked in its place.
flagRead-start : flagReadStep (idle , inj₂ tt) ≡ returnₚ (waitE , inj₁ (inj₁ tt))
flagRead-start = refl

flagRead-complete : (v : Bool)
                  → flagReadStep (waitE , inj₁ (inj₁ v)) ≡ returnₚ (waitF , inj₁ (inj₂ tt))
flagRead-complete _ = refl

flagRead-report : (b : Bool) → flagReadStep (waitF , inj₁ (inj₂ b)) ≡ returnₚ (idle , inj₂ b)
flagRead-report _ = refl

-- …and the only way out of `waitE` is that verdict, so a test that diverges
-- leaves the experiment with no verdict rather than with the raised flag.
flagRead-diverges : flagReadStep (waitE , inj₂ tt) ≡ botₚ
flagRead-diverges = refl
