{-# OPTIONS --safe --without-K --guardedness #-}

-- SPIKE (`docs/event-bounds-in-setup.md` steps 1-3).  Not a landing site: see
-- the spike report for where each block belongs.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; _∨_; false; true)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base as ℕ using (ℕ; s≤s; z≤n)
open import Data.Nat.Poly using (Poly)
open import Data.Nat.Properties using (*-identityʳ; m≤n+m; ≤-reflexive)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
  using (+-monoˡ-≤; ≤-trans) renaming (≤-reflexive to ≤-reflexiveℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (cong)

open import ProbabilisticLogic.Dp
  using (Dₚ; _≼ₚ_; _≈ₚ_; botₚ; bot-bind-≈ₚ; mapₚ; returnₚ; >>=ₚ-identityˡ)
open import ProbabilisticLogic.Dp.Advantage
  using (Pr≤; Pr≤-mono; _≼ₚ[_]_; _≈ₚ[_]_; indᵇ-nn)

open import CategoricalCrypto.Examples.ChimericLedger using (module Ledger)
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Machine.Agree using (prAgree)
open import CategoricalCrypto.Protocol.Observe using (Bounded; Pr)
open import CategoricalCrypto.Strategy using (Strat; asks≤; asks≤-mono; ask; coin; out)
open import CategoricalCrypto.UC.Approximate using (Negligible)
open import CategoricalCrypto.UC.Budget using (ctxBudget)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; T₁ᴵ; a⇒ᴵ; subᴵ)
open import CategoricalCrypto.UC.QueryBound
  using ( Ans; Certified; QB; certified⇒QB; forget; qb-mono; qbᵢ-T₁; qbᵢ-sub
        ; qb-resp-≈; qbᵢ-wire )
open import CategoricalCrypto.UC.Machine.Bridge using (ctxRun)
open import CategoricalCrypto.UC.Machine.Dictionary using (sub-⊗₁)
open import CategoricalCrypto.UC.Machine.Grading using (qb-subᴳ)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)

import CategoricalCrypto.Examples.ChimericLedger.Observable as Observable
import CategoricalCrypto.Examples.ChimericLedger.System as System
import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Quantitative.Hits where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- Finite-depth upper bounds

-- The layer never forms `Dₚ`'s limiting probability, so an event bound is a
-- bound on every finite approximant (`Dp.Advantage`'s header).
Upper : Dₚ Bool → ℚ → Set
Upper d r = (k : ℕ) → Pr≤ k d ℚ.≤ r

-- The transport, one-sided: the comparison supplies a depth of `e` at each
-- depth of `d`, and no positive slack is spent doing it.
upper-≼[] : {d e : Dₚ Bool} {r ε : ℚ} → d ≼ₚ[ ε ] e → Upper e r → Upper d (r ℚ.+ ε)
upper-≼[] {ε = ε} le up k =
  let m , bd = le true k in ≤-trans bd (+-monoˡ-≤ ε (up m))

upper-≈[] : {d e : Dₚ Bool} {r ε : ℚ} → d ≈ₚ[ ε ] e → Upper e r → Upper d (r ℚ.+ ε)
upper-≈[] (le , _) = upper-≼[] le

-- …and along an exact agreement, which is what crossing the seal costs
-- (`UC.Model.Dominated.ctxRunᵒ`).
upper-≼ : {d e : Dₚ Bool} {r : ℚ} → d ≼ₚ e → Upper e r → Upper d r
upper-≼ le up k = let m , bd = le _ (indᵇ-nn true) k in ≤-trans bd (up m)

upper-≈ : {d e : Dₚ Bool} {r : ℚ} → d ≈ₚ e → Upper e r → Upper d r
upper-≈ (le , _) = upper-≼ le

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

-- Completion is not detected by the relay: it is the test's own verdict
-- emission, seen from ABOVE.  `flagReadᴹ` sits over the test, discards that
-- verdict, ticks the flag and answers with it — so a test that never emits
-- never produces one either, and a flag raised before a divergence is not
-- reported.
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

------------------------------------------------------------------------
-- The compiled test

-- The monitor on the honest leg, the test run through it, and the flag read
-- when the test's verdict comes back.  `E` is an ARBITRARY test: it never sees
-- the flag port, and cannot forge the bit it is replaced by.
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

qb-subᴵ : (X Y A : Iface) {c : ℕ} (s : Proc X Y) → QB c s → QB (c ℕ.⊔ 1) (subᴵ s {A})
qb-subᴵ X Y A s q = qb-resp-≈ (𝒫.Equiv.sym (sub-⊗₁ s)) (qb-subᴳ X Y A s q)

-- The allowance the compiled test spends: the relay costs nothing, the flag
-- read doubles.  `κμ 0 = 2`, so a test certified at rate 0 still compiles to a
-- querying one — the flag port IS a query, and `ctxBudget` cannot tell it from
-- a query on the honest interface (`UC.Budget`'s header: the principled form
-- is a PORT-specific bound, and it is not built).
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

------------------------------------------------------------------------
-- The strategy-level watch the monitor is meant to implement

-- `Examples.ChimericLedger.Observable.auditWatchFrom` with its report a
-- parameter; the ledger's watch is this at `reportsLoss s₀`, on the nose.
watchFrom : {B : Iface} → (Neg B → Pos B → Bool) → Bool
          → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)
watchFrom report acc (out _)    = out acc
watchFrom report acc (ask q k)  = ask q λ a → watchFrom report (acc ∨ report q a) (k a)
watchFrom report acc (coin μ k) = coin μ λ b → watchFrom report acc (k b)

watchOf : {B : Iface} → (Neg B → Pos B → Bool)
        → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)
watchOf report = watchFrom report false

asks≤-watchFrom : {B : Iface} {n : ℕ} (report : Neg B → Pos B → Bool) (acc : Bool)
                  (d : Strat (Neg B) (Pos B)) → asks≤ n d → asks≤ n (watchFrom report acc d)
asks≤-watchFrom             _      _   (out _)    _ = tt
asks≤-watchFrom {n = ℕ.suc _} report acc (ask _ k)  a =
  λ r → asks≤-watchFrom report _ (k r) (a r)
asks≤-watchFrom             report acc (coin _ k) a =
  λ b → asks≤-watchFrom report acc (k b) (a b)

-- Layer 1's verdict probability bounds EVERY finite approximant of the machine
-- image's run: `prAgree` reads it off past one budget and `Pr≤` is monotone.
upper-run : {B : Iface} (P : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B)) {r : ℚ}
          → Pr P d ℚ.≤ r → Upper (runᴹ (morphism P) d) r
upper-run P d bnd k =
  let n , h = prAgree true P d
  in ≤-trans (≤-trans (Pr≤-mono true (runᴹ (morphism P) d) (m≤n+m k n))
                      (≤-reflexiveℚ (h k)))
             bnd

------------------------------------------------------------------------
-- The event bound

eventRun : {A B : Iface} (Y : Iface) → Proc A B → Proc B (B ⊗ᴵ Flagᴵ)
         → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool
eventRun {B = B} Y f μ E m = ctxRun Y (compileᴹ Y B μ E) m f

-- The allowance is CAPPED and the bound read at a constant: the schedule is
-- not known to be monotone, so it cannot be read at the budget a context
-- happens to carry (`docs/event-bounds-in-setup.md` §3).
HitsAt : {A B : Iface} → ℕ → ℚ → Proc A B → Proc B (B ⊗ᴵ Flagᴵ) → Set₁
HitsAt {A} {B} q r f μ =
    (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m → ctxBudget c c′ ℕ.≤ q → Upper (eventRun Y f μ E m) r

Hitsᶠ : {A B : ℕ → Iface} → (ℕ → ℕ → ℚ) → ((n : ℕ) → Proc (A n) (B n))
      → ((n : ℕ) → Proc (B n) (B n ⊗ᴵ Flagᴵ)) → Set₁
Hitsᶠ ε f μ = (n q : ℕ) → HitsAt q (ε n q) (f n) (μ n)

Hitsᴺ : {A B : ℕ → Iface} → ((n : ℕ) → Proc (A n) (B n))
      → ((n : ℕ) → Proc (B n) (B n ⊗ᴵ Flagᴵ)) → (ℕ → ℕ → ℚ) → Set₁
Hitsᴺ f μ ε = (p : ℕ → ℕ) → Poly p
            → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν
            × ((n : ℕ) → HitsAt (p n) (ε n (p n) ℚ.+ ν n) (f n) (μ n))

-- Transport at one monitored context, off a comparison of the two COMPILED
-- experiments: the whole of `docs/event-bounds-in-setup.md` §4's steps 1 and 4.
hits-transport : {A B : Iface} {q : ℕ} {r ε : ℚ} (f g : Proc A B)
                 (μ : Proc B (B ⊗ᴵ Flagᴵ))
               → ((Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
                  → QB c E → QB c′ m → ctxBudget c c′ ℕ.≤ q
                  → eventRun Y f μ E m ≈ₚ[ ε ] eventRun Y g μ E m)
               → HitsAt q r g μ → HitsAt q (r ℚ.+ ε) f μ
hits-transport f g μ near h Y E m qE qm le =
  upper-≈[] (near Y E m qE qm le) (h Y E m qE qm le)

-- …and what a comparison stated at UNCOMPILED contexts actually pays when it
-- is instantiated at a compiled one: the schedule is read at
-- `ctxBudget (κμ c) c′`, never at the environment's own `ctxBudget c c′`.
hits-transport-ctx :
    (Y B : Iface) (report : Neg B → Pos B → Bool) {A : Iface} {ε : ℕ → ℚ} {r : ℚ}
    (f g : Proc A B)
  → ((E′ : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
     → QB c E′ → QB c′ m → ctxRun Y E′ m f ≈ₚ[ ε (ctxBudget c c′) ] ctxRun Y E′ m g)
  → (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m
  → Upper (eventRun Y g (monitorᴹ report) E m) r
  → Upper (eventRun Y f (monitorᴹ report) E m) (r ℚ.+ ε (ctxBudget (κμ c) c′))
hits-transport-ctx Y B report f g near E m qE qm =
  upper-≈[] (near (compileᴹ Y B (monitorᴹ report) E) m (qb-compileᴹ Y B report E qE) qm)
