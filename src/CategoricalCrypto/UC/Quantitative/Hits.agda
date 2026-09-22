{-# OPTIONS --safe --without-K --guardedness #-}

-- The compiled-monitor instance of the event-bound layer, the strategy-level
-- watch it is meant to implement, and the ledger at one level.
--
-- `UC.Model.EventBounds` proves the transport with no reference to any
-- particular way of reading an event, and `UC.Machine.Monitor` builds one;
-- this module is where the two meet — `HitsAt` is `BoundedAt` at the
-- compiled readout, and `hits-carry` is `carry-boundedBy` at `κμ` with the
-- closure recertified.
--
-- Two things are NOT established: semantic agreement of the compiled
-- experiment with the strategy-level watch, and the event-sensitive
-- contextual lift.  `EventDominated` is the second, stated and consumed and
-- nowhere inhabited, and `ledger-hits` is the ledger's single-level bound
-- modulo exactly it (`docs/event-bounds-in-setup.md`, work packages A and C).

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; _∨_; false; true)
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-*; poly-const; poly-⊔)
open import Data.Nat.Properties
  using ( *-monoʳ-≤; *-monoˡ-≤; ⊔-monoˡ-≤; m≤n+m; n≤0⇒n≡0; ≤-reflexive; ≤-trans )
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
  using (+-mono-≤) renaming (≤-reflexive to ≤-reflexiveℚ; ≤-trans to ≤-transℚ)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; subst; sym)

open import ProbabilisticLogic.Distribution.RationalDist using (Dist-ℚ)
open import ProbabilisticLogic.Dp using (Dₚ)

open import CategoricalCrypto.Examples.ChimericLedger using (Variant; module Ledger)
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Machine.Agree using (prAgree)
open import CategoricalCrypto.Protocol.Observe using (Bounded; Pr)
open import CategoricalCrypto.Strategy using (Strat; asks≤; asks≤-mono; ask; coin; out)
open import CategoricalCrypto.UC.Approximate
  using ( GradedBound-+[_]; GradedBound-reindex; Negligible; Negligible-+
        ; NegligibleBound )
open import CategoricalCrypto.UC.Budget
  using (ctxBudget; ctxBudget-closed; q≤simCost; simCost)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ)
open import CategoricalCrypto.UC.Machine.Bridge using (ctxRun)
open import CategoricalCrypto.UC.QueryBound using (QB; qb-closed)

import CategoricalCrypto.Examples.ChimericLedger.Observable as Observable
import CategoricalCrypto.Examples.ChimericLedger.System as System

module CategoricalCrypto.UC.Quantitative.Hits where

-- TEMPORARY SHIM: the spike's blocks have landed in these three modules, and
-- the re-export keeps its importers working until they are repointed.
open import ProbabilisticLogic.Dp.Advantage public
open import CategoricalCrypto.UC.Machine.Grading public using (qb-T₁ᴵ; qb-subᴵ)
open import CategoricalCrypto.UC.Machine.Monitor public
open import CategoricalCrypto.UC.Model.EventBounds public

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The compiled readout

readoutᴹ : (B : Iface) → Proc B (B ⊗ᴵ Flagᴵ) → Readout B
readoutᴹ B μ Y = compileᴹ Y B μ

chargeᴹ : (B : Iface) (report : Neg B → Pos B → Bool)
        → Charge (readoutᴹ B (monitorᴹ report)) κμ
chargeᴹ B report Y E = qb-compileᴹ Y B report E

eventRun : {A B : Iface} (Y : Iface) → Proc A B → Proc B (B ⊗ᴵ Flagᴵ)
         → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool
eventRun {B = B} Y f μ = readRun Y f (readoutᴹ B μ)

HitsAt : {A B : Iface} → ℕ → ℚ → Proc A B → Proc B (B ⊗ᴵ Flagᴵ) → Set₁
HitsAt {B = B} q r f μ = BoundedAt q r f (readoutᴹ B μ)

Hitsᶠ : {A B : ℕ → Iface} → (ℕ → ℕ → ℚ) → ((n : ℕ) → Proc (A n) (B n))
      → ((n : ℕ) → Proc (B n) (B n ⊗ᴵ Flagᴵ)) → Set₁
Hitsᶠ {B = B} ε f μ = Boundedᶠ f (λ n → readoutᴹ (B n) (μ n)) ε

Hitsᴺ : {A B : ℕ → Iface} → ((n : ℕ) → Proc (A n) (B n))
      → ((n : ℕ) → Proc (B n) (B n ⊗ᴵ Flagᴵ)) → (ℕ → ℕ → ℚ) → Set₁
Hitsᴺ {B = B} f μ ε = Boundedᴺ f (λ n → readoutᴹ (B n) (μ n)) ε

------------------------------------------------------------------------
-- The closure recertification

-- The closure of a context is a CLOSED process, so the model recertifies it
-- at `QB 0` (`UC.QueryBound.qb-closed`) whatever certificate it arrived with.
-- That changes a certificate, not the closure and not the admitted
-- experiment, and no `UC.Budget.Budget` law gives it: it reads the empty
-- `Neg unitᴵ` off the model's own closure type.
--
-- It is what makes the compiled allowance a function of the ORIGINAL one at
-- all.  At the recertified closure it is `ctxBudget (κμ c) 0 = κμ c`, hence
-- at most `κμ q` for every context the cap `q` admits; at the closure's own
-- certificate it is `2 · (c ⊔ 1) · (c′ ⊔ 1)`, which no function of
-- `q = c · (c′ ⊔ 1)` bounds — at `c = 0` the original allowance is 0 whatever
-- the closure does.
κμ-cap : {c c′ q : ℕ} → ctxBudget c c′ ℕ.≤ q → ctxBudget (κμ c) 0 ℕ.≤ κμ q
κμ-cap {c} {c′} le =
  ≤-trans (≤-reflexive (ctxBudget-closed (κμ c)))
          (*-monoʳ-≤ 2 (⊔-monoˡ-≤ 1 (≤-trans (q≤simCost c c′) le)))

-- Zero allowance, explicitly.  `ctxBudget`'s second leg is guarded, so a
-- context admitted at `q = 0` has `c = 0` whatever its closure does — and it
-- still compiles to a test that spends 2.  `κμ 0 = 2` is the cap above, so
-- the bound is tight there rather than vacuous.
κμ-cap-zero : {c c′ : ℕ} → ctxBudget c c′ ℕ.≤ 0 → ctxBudget (κμ c) 0 ≡ 2
κμ-cap-zero {c} {c′} le =
  cong (λ z → ctxBudget (κμ z) 0) (n≤0⇒n≡0 (≤-trans (q≤simCost c c′) le))

------------------------------------------------------------------------
-- Transport at the compiled readout

-- Off a comparison of the two COMPILED experiments.
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

-- The explicit-error carry at the compiled readout, with the closure
-- recertified: `UC.Model.EventBounds.carry-boundedBy` at `κ = κμ`, applied
-- with `qb-closed m` in place of the closure's own certificate.  Both
-- allowances are EXACT before the cap is taken — `simCost c cs` for the ideal
-- bound, `κμ c` for the comparison — and the two schedule monotonicities are
-- spent only on the last step, from the carried allowance to the cap.
hits-carry :
    (B C : Iface) (μ : Proc B (B ⊗ᴵ Flagᴵ)) (ν : Proc C (C ⊗ᴵ Flagᴵ)) {A : Iface}
    (f : Proc A B) (x : Proc A C) (s : Proc C B) {cs : ℕ} → QB cs s
  → Charge (readoutᴹ B μ) κμ → Absorbsᵣ s (readoutᴹ B μ) (readoutᴹ C ν)
  → (ε δ : ℕ → ℚ) → Monotone ε → Monotone δ
  → ((Y : Iface) (E′ : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
     → QB c E′ → QB c′ m
     → ctxRun Y E′ m f ≈ₚ[ ε (ctxBudget c c′) ] ctxRun Y E′ m (s 𝒫.∘ x))
  → BoundedBy δ x (readoutᴹ C ν)
  → (q : ℕ) → HitsAt q (δ (simCost q cs) ℚ.+ ε (κμ q)) f μ
hits-carry B C μ ν f x s {cs} qs chg abs ε δ mε mδ near bnd q Y E m {c} {c′} qE qm le =
  upper-mono cap
    (carry-boundedBy f x s qs (readoutᴹ B μ) (readoutᴹ C ν) κμ chg abs ε δ near bnd
                     Y E m qE (qb-closed m))
  where
  ideal≤ : simCost (ctxBudget c 0) cs ℕ.≤ simCost q cs
  ideal≤ = ≤-trans (≤-reflexive (cong (λ z → simCost z cs) (ctxBudget-closed c)))
                   (*-monoˡ-≤ (cs ℕ.⊔ 1) (≤-trans (q≤simCost c c′) le))

  cap : δ (simCost (ctxBudget c 0) cs) ℚ.+ ε (ctxBudget (κμ c) 0)
      ℚ.≤ δ (simCost q cs) ℚ.+ ε (κμ q)
  cap = +-mono-≤ (mδ ideal≤) (mε (κμ-cap {c} {c′} le))

-- …at every level.  Nothing is uniform across levels but the shape: each
-- level carries its own comparison, ideal bound and simulator.
-- `UC.Model.EventBounds.boundedᶠ⇒boundedᴺ` turns the result into a `Hitsᴺ`,
-- at zero slack.
hits-carryᶠ :
    {A B C : ℕ → Iface}
    (f : (n : ℕ) → Proc (A n) (B n)) (x : (n : ℕ) → Proc (A n) (C n))
    (μ : (n : ℕ) → Proc (B n) (B n ⊗ᴵ Flagᴵ)) (ν : (n : ℕ) → Proc (C n) (C n ⊗ᴵ Flagᴵ))
    (s : (n : ℕ) → Proc (C n) (B n)) (cs : ℕ → ℕ) → ((n : ℕ) → QB (cs n) (s n))
  → ((n : ℕ) → Charge (readoutᴹ (B n) (μ n)) κμ)
  → ((n : ℕ) → Absorbsᵣ (s n) (readoutᴹ (B n) (μ n)) (readoutᴹ (C n) (ν n)))
  → (ε δ : ℕ → ℕ → ℚ) → ((n : ℕ) → Monotone (ε n)) → ((n : ℕ) → Monotone (δ n))
  → ((n : ℕ) (Y : Iface) (E′ : Proc (Y ⊗ᴵ B n) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A n)) {c c′ : ℕ}
     → QB c E′ → QB c′ m
     → ctxRun Y E′ m (f n) ≈ₚ[ ε n (ctxBudget c c′) ] ctxRun Y E′ m (s n 𝒫.∘ x n))
  → ((n : ℕ) → BoundedBy (δ n) (x n) (readoutᴹ (C n) (ν n)))
  → Hitsᶠ (λ n q → δ n (simCost q (cs n)) ℚ.+ ε n (κμ q)) f μ
hits-carryᶠ f x μ ν s cs qs chg abs ε δ mε mδ near bnd n =
  hits-carry _ _ (μ n) (ν n) (f n) (x n) (s n) (qs n) (chg n) (abs n)
             (ε n) (δ n) (mε n) (mδ n) (near n) (bnd n)

-- …and the schedule it produces is negligible whenever the comparison's and
-- the ideal bound's are.  Both reindexings preserve polynomials — `poly-κμ`
-- for the readout's charge, `simCost`'s guard for the absorption — and that
-- is all a `GradedBound` ever asks of a substitution.
NegligibleBound-carry : (cs : ℕ → ℕ) → Poly cs → (ε δ : ℕ → ℕ → ℚ)
                      → NegligibleBound ε → NegligibleBound δ
                      → NegligibleBound (λ n q → δ n (simCost q (cs n)) ℚ.+ ε n (κμ q))
NegligibleBound-carry cs Pcs ε δ nε nδ =
  GradedBound-+[ Negligible ] Negligible-+
    (λ n q → δ n (simCost q (cs n))) (λ n q → ε n (κμ q))
    (GradedBound-reindex Negligible (λ n q → simCost q (cs n))
       (λ _ Pp → poly-* Pp (poly-⊔ Pcs (poly-const 1))) δ nδ)
    (NegligibleBound-charge κμ poly-κμ ε nε)

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

-- What ties a strategy transformer to a monitor's report.  Stated as three
-- equations rather than as `watchFrom` itself: a transformer defined
-- elsewhere — `Examples.ChimericLedger.Observable.auditWatchFrom` — satisfies
-- them by `refl`, where identifying the two definitions would want funext.
IsWatch : {B : Iface} → (Neg B → Pos B → Bool)
        → (Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → Set
IsWatch {B} report w =
    ((acc b : Bool) → w acc (out b) ≡ out acc)
  × ( ((acc : Bool) (q : Neg B) (k : Pos B → Strat (Neg B) (Pos B))
       → w acc (ask q k) ≡ ask q λ a → w (acc ∨ report q a) (k a))
    × ((acc : Bool) (ν : Dist-ℚ Bool) (k : Bool → Strat (Neg B) (Pos B))
       → w acc (coin ν k) ≡ coin ν λ b → w acc (k b)))

watchFrom-IsWatch : {B : Iface} (report : Neg B → Pos B → Bool)
                  → IsWatch report (watchFrom report)
watchFrom-IsWatch _ = (λ _ _ → refl) , (λ _ _ _ → refl) , (λ _ _ _ → refl)

-- A watch buys no queries: it plays inside the allowance it is handed.
asks≤-watch : {B : Iface} (report : Neg B → Pos B → Bool)
              (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
            → IsWatch report w → {n : ℕ} (acc : Bool) (d : Strat (Neg B) (Pos B))
            → asks≤ n d → asks≤ n (w acc d)
asks≤-watch report w iw@(eo , _ , _) {n} acc (out b) _ =
  subst (asks≤ n) (sym (eo acc b)) tt
asks≤-watch report w iw@(_ , ea , _) {ℕ.suc n} acc (ask q k) a =
  subst (asks≤ (ℕ.suc n)) (sym (ea acc q k))
        λ r → asks≤-watch report w iw _ (k r) (a r)
asks≤-watch report w iw@(_ , _ , ec) {n} acc (coin ν k) a =
  subst (asks≤ n) (sym (ec acc ν k)) λ b → asks≤-watch report w iw acc (k b) (a b)

-- Layer 1's verdict probability bounds EVERY finite approximant of the machine
-- image's run: `prAgree` reads it off past one budget and `Pr≤` is monotone.
upper-run : {B : Iface} (P : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B)) {r : ℚ}
          → Pr P d ℚ.≤ r → Upper (runᴹ (morphism P) d) r
upper-run P d bnd k =
  let n , h = prAgree true P d
  in ≤-transℚ (≤-transℚ (Pr≤-mono true (runᴹ (morphism P) d) (m≤n+m k n))
                        (≤-reflexiveℚ (h k)))
              bnd

------------------------------------------------------------------------
-- The event-sensitive one-sided lift, and what it would buy

-- NOT PROVED HERE, and NOT an axiom: nothing below inhabits it, and the only
-- consumer takes it as a hypothesis.  `docs/event-bounds-in-setup.md` §5 is
-- the statement; the spike report says exactly where the existing domination
-- machinery stops short of it.
EventDominated : Set₁
EventDominated =
    {B : Iface} (report : Neg B → Pos B → Bool)
    (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
  → (u : Proc unitᴵ B) (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ)
    (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) {c c′ : ℕ} → QB c E → QB c′ m
  → (r η : ℚ) → 0ℚ ℚ.< η
  → ((d : Strat (Neg B) (Pos B)) → asks≤ (ctxBudget c c′) d
     → Upper (runᴹ u (w false d)) r)
  → Upper (eventRun Y u (monitorᴹ report) E m) (r ℚ.+ η)

------------------------------------------------------------------------
-- The ledger, at one level

module _ (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) (s₀ : Ledger.LState ℓ) where

  private
    module Sy = System ℓ ser
    module Ob = Observable ℓ ser

  auditMonitor : Proc Sy.LedgerIf (Sy.LedgerIf ⊗ᴵ Flagᴵ)
  auditMonitor = monitorᴹ (Ob.reportsLoss s₀)

  -- The compiler's strategy-level target IS the ledger's own watch.
  auditWatch-IsWatch : IsWatch (Ob.reportsLoss s₀) (Ob.auditWatchFrom s₀)
  auditWatch-IsWatch = (λ _ _ → refl) , (λ _ _ _ → refl) , (λ _ _ _ → refl)

  -- `Observable.auditWatch-bounded`'s conclusion, crossed to the machine
  -- observation and read at every admitted context: the single-level content
  -- of `Property.ideal-preserves-value`, modulo the one unproved lift.
  ledger-hits : EventDominated → (vr : Variant) {ε : ℕ → ℚ}
              → Bounded (Sy.Sys vr s₀) (Ob.auditWatch s₀) ε
              → (q : ℕ) (η : ℚ) → 0ℚ ℚ.< η
              → HitsAt q (ε q ℚ.+ η) (morphism (Sy.Sys vr s₀)) auditMonitor
  ledger-hits ev vr {ε} bnd q η 0<η Y E m qE qm le =
    ev (Ob.reportsLoss s₀) (Ob.auditWatchFrom s₀) auditWatch-IsWatch
       (morphism (Sy.Sys vr s₀)) Y E m qE qm (ε q) η 0<η
       λ d a → upper-run (Sy.Sys vr s₀) (Ob.auditWatch s₀ d)
                         (bnd q d (asks≤-mono le d a))
