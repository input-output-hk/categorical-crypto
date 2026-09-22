{-# OPTIONS --safe --without-K --guardedness #-}

-- The strategy-to-contexts lift for the compiled monitor
-- (`docs/event-bounds-in-setup.md` §5), down to its one remaining premise.
--
-- `UC.Machine.Dominated.eventSkeleton` bounds a closed context's verdict mass
-- by a bound on the watched event of the strategies its certificate extracts
-- to, given the accumulator invariant.  What is added here is the passage from
-- `UC.Quantitative.Hits.eventRun` to that closed context — `ctxRun-conj` then
-- `ctxRun-slide`.
--
-- The certificate of that closed context is QUANTIFIED rather than named: the
-- ones `UC.Quantitative.EventLift.Budget` builds are `qb-∘` composites, and
-- `CovCtx` reads a certificate's potential and emissions, so naming one in a
-- type makes the elaborator normalize the whole tower.
--
-- Two allowances stay apart, as §B asks.  The CLOSURE is recertified at rate
-- zero (`qb-closed`, `m` being a closed process), so the compiled context's
-- allowance is a function of the test's own rate `c` and not of
-- `ctxBudget c c′`, which at `c = 0` is `0` whatever the closure does.  The
-- honest-query allowance is then `c + 1`, NOT `c`: the extra unit is the
-- monitor's accumulator, which `CovCtx` forces a certificate to give
-- potential to (`UC.Quantitative.EventLift.Cov`), and `ctxBudget` cannot tell
-- a flag-port query from an honest one (`UC.Budget`'s header).  That
-- rescaling is exposed below and is why these are not
-- `UC.Quantitative.Hits.EventDominated`, whose hypothesis is read at the
-- original `ctxBudget c c′`.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties
open import Data.Sum.Base using ([_,_]; inj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Dp using (_≈ₚ_; ≈ₚ-sym)
open import ProbabilisticLogic.Dp.Advantage using (Upper; upper-≈)
open import ProbabilisticLogic.Dp.Reasoning using (_⟨≈⟩_)

open import CategoricalCrypto.Examples.ChimericLedger using (Variant; module Ledger)
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Observe using (Bounded; Pr)
open import CategoricalCrypto.Strategy using (Strat; IsWatch; asks≤; asks≤-mono)
open import CategoricalCrypto.UC.Budget using (c≤ctxBudget; ctxBudget; ctxBudget-closed)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; T₁ᴵ; ⟦_⟧ᴼ)
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇒)
open import CategoricalCrypto.UC.Machine.Dominated using (CovCtx; eventSkeleton)
open import CategoricalCrypto.UC.Machine.Monitor using (compileᴹ; monitorᴹ; κμ)
open import CategoricalCrypto.UC.Machine.Monitor.Agree
  using (agree; m₀; stratTest; stratTest-embeds)
open import CategoricalCrypto.UC.Machine.Slide using (Kctx; ctxRun-conj; ctxRun-slide)
open import CategoricalCrypto.UC.QueryBound
  using (QB; certified⇒QB; qb-closed; qb-resp-≈; qbᵢ-wire)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)
open import CategoricalCrypto.UC.Quantitative.EventLift.Cov using (covCtx)
open import CategoricalCrypto.UC.Quantitative.Hits
open import CategoricalCrypto.UC.Seam using (strategyEnv)
open import CategoricalCrypto.UC.Seam.Budget using (qb-strategyEnv)

import CategoricalCrypto.Examples.ChimericLedger.Observable as Observable
import CategoricalCrypto.Examples.ChimericLedger.System as System

module CategoricalCrypto.UC.Quantitative.EventLift where

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The compiled context, closed

-- The compiled test with the hole `ctxRun` closes over reopened, which is the
-- shape `Kctx` slides the closure into.
openedᴹ : (Y B : Iface) → (Neg B → Pos B → Bool) → Proc (Y ⊗ᴵ B) Ωᴵ
        → Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ
openedᴹ Y B report E = compileᴹ Y B (monitorᴹ report) E 𝒫.∘ T₁ᴵ Y λᴵ⇒

-- The monitored experiment IS that closed context's observation.
eventRun-closed : (Y B : Iface) (report : Neg B → Pos B → Bool)
                  (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
                  (u : Proc unitᴵ B)
                → eventRun Y u (monitorᴹ report) E m
                  ≈ₚ ⟦ Kctx (openedᴹ Y B report E) m 𝒫.∘ u ⟧ᴼ
eventRun-closed Y B report E m u =
  ctxRun-conj (compileᴹ Y B (monitorᴹ report) E) m u
    ⟨≈⟩ ctxRun-slide (openedᴹ Y B report E) m u

------------------------------------------------------------------------
-- The lift

-- `UC.Quantitative.Hits.EventDominated` with the header's two changes: the
-- strategy allowance is the compiled context's own, and the accumulator
-- invariant is a premise.  No positive slack is spent — the extraction is
-- chosen once the observation's budget is known — so `EventDominated`'s `η`
-- is free for a consumer to add.
EventDominatedᶜ : Set₁
EventDominatedᶜ =
    {B : Iface} (report : Neg B → Pos B → Bool)
    (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
  → (u : Proc unitᴵ B) (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ)
    (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) (k : ℕ)
    (kb : QB k (Kctx (openedᴹ Y B report E) m)) → CovCtx B k report kb
  → (r : ℚ)
  → ((d : Strat (Neg B) (Pos B)) → asks≤ k d → Upper (runᴹ u (w false d)) r)
  → Upper (eventRun Y u (monitorᴹ report) E m) r

eventDominatedᶜ : EventDominatedᶜ
eventDominatedᶜ {B} report w (wo , wa , wc) u Y E m k kb cov r h =
  upper-≈ (eventRun-closed Y B report E m u)
          (eventSkeleton B (Kctx (openedᴹ Y B report E) m) report w wo wa wc kb cov u r h)

-- …and what separates that from `EventDominated` itself: ONE premise, a
-- certificate of the compiled closed context at the ORIGINAL allowance `c`
-- satisfying the accumulator invariant.  Its `QB` half is available —
-- `UC.Quantitative.EventLift.Budget.qb-compiled′`, off the tight compiled
-- certificate — but its `CovCtx` half is FALSE at that rate: see
-- `eventDominatedᵘ` below, which is the same lift at `c + 1`.
eventDominated :
    ((Y B : Iface) (report : Neg B → Pos B → Bool) {c : ℕ}
     (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) → QB c E
     → Σ[ kb ∈ QB c (Kctx (openedᴹ Y B report E) m) ] CovCtx B c report kb)
  → EventDominated
eventDominated prem {B} report w iw u Y E m {c} {c′} qE qm r η 0<η h k =
  ≤-trans (eventDominatedᶜ report w iw u Y E m c (proj₁ pm) (proj₂ pm) r
             (λ d a → h d (asks≤-mono (c≤ctxBudget c c′) d a)) k)
          (≤-trans (≤-reflexive (sym (+-identityʳ r))) (+-monoʳ-≤ r (<⇒≤ 0<η)))
  where
  pm = prem Y B report E m qE

-- …and the lift with that premise discharged, at the one rate it can be:
-- `UC.Quantitative.EventLift.Cov.covCtx` pays one unit of allowance for the
-- accumulator's potential and no slack.  At the test's own rate `c` the
-- premise is not merely unproved but false — `CovCtx` is read at EVERY
-- zero-potential state, and a context that spends its whole allowance before
-- its answer reports leaves the accumulator raised with no potential left,
-- so the next activation's verdict is a `true` with nothing covering it.
eventDominatedᵘ :
    {B : Iface} (report : Neg B → Pos B → Bool)
    (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
  → (u : Proc unitᴵ B) (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ)
    (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) {c : ℕ} → QB c E → (r : ℚ)
  → ((d : Strat (Neg B) (Pos B)) → asks≤ (c ℕ.+ 1) d → Upper (runᴹ u (w false d)) r)
  → Upper (eventRun Y u (monitorᴹ report) E m) r
eventDominatedᵘ {B} report w iw u Y E m {c} qE r h =
  eventDominatedᶜ report w iw u Y E m (c ℕ.+ 1) (proj₁ pm) (proj₂ pm) r h
  where
  pm = covCtx Y B report E m qE

-- …as an event bound at a CAPPED allowance, which is the public shape
-- (`UC.Model.EventBounds`'s two presentations).  The strategy hypothesis is
-- read at the cap plus the accumulator's one unit, `c ≤ ctxBudget c c′ ≤ q`
-- being what rescales the test's own rate to the cap.
hitsᵘ : {B : Iface} (report : Neg B → Pos B → Bool)
        (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
      → (u : Proc unitᴵ B) (q : ℕ) {r : ℚ}
      → ((d : Strat (Neg B) (Pos B)) → asks≤ (q ℕ.+ 1) d → Upper (runᴹ u (w false d)) r)
      → HitsAt q r u (monitorᴹ report)
hitsᵘ report w iw u q h Y E m {c} {c′} qE qm le =
  eventDominatedᵘ report w iw u Y E m qE _
    λ d a → h d (asks≤-mono (ℕP.+-monoˡ-≤ 1 (ℕP.≤-trans (c≤ctxBudget c c′) le)) d a)

------------------------------------------------------------------------
-- …and back to the strategy level

-- The strategy context `UC.Machine.Monitor.Agree.agree` is stated at, with the
-- certificate the strategy's own ask-depth gives it: `stratTest-embeds` reads
-- the test as the strategy environment behind one wire, and `qb-∘` multiplies
-- by that wire's rate of 1.
qb-stratTest : (B : Iface) {q : ℕ} (d : Strat (Neg B) (Pos B)) → asks≤ q d
             → QB q (stratTest B d)
qb-stratTest B {q} d a =
  qb-resp-≈ (𝒫.Equiv.sym (stratTest-embeds B d))
    (subst (λ k → QB k (strategyEnv B d 𝒫.∘ λᴵ⇒)) (ℕP.*-identityʳ q)
      (qb-∘-category (unitᴵ ⊗ᴵ B) B Ωᴵ (strategyEnv B d) λᴵ⇒
        (qb-strategyEnv B q d a) (certified⇒QB (qbᵢ-wire [ ⊥-elim , id ] inj₂))))

-- …so a contextual event bound, read at that context, IS the strategy-level
-- watched bound at the same allowance: the closure is closed, so
-- `ctxBudget q 0 = q` and the strategy keeps the whole cap.  Nothing is spent
-- coming back — the one extra query `hitsᵘ` charges is charged going out.
hits⇒bounded :
    {B : Iface} (report : Neg B → Pos B → Bool)
    (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
  → (P : Protocol unitᴵ B) (q : ℕ) {r : ℚ}
  → HitsAt q r (morphism P) (monitorᴹ report)
  → (d : Strat (Neg B) (Pos B)) → asks≤ q d → Pr P (w false d) ℚ.≤ r
hits⇒bounded {B} report w iw P q h d a =
  run-upper P (w false d)
    (upper-≈ (≈ₚ-sym _ _ (agree B report w iw (morphism P) d))
             (h unitᴵ (stratTest B d) m₀ (qb-stratTest B d a) (qb-closed m₀)
                (ℕP.≤-reflexive (ctxBudget-closed q))))

------------------------------------------------------------------------
-- The ledger, at one level

module _ (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) (s₀ : Ledger.LState ℓ) where

  private
    module Sy = System ℓ ser
    module Ob = Observable ℓ ser

  -- `UC.Quantitative.Hits.ledger-hits` with the lift discharged: what is left
  -- is a certificate of the compiled context at the compiled allowance
  -- (`UC.Quantitative.EventLift.Budget.qb-compiled` builds one at `κμ c`)
  -- satisfying the accumulator invariant.  The schedule is then read at the
  -- rescaled allowance `κμ q`, the cap still being the environment's own —
  -- `c ≤ ctxBudget c c′ ≤ q` is what rescales it.
  ledger-hitsᶜ : (vr : Variant) {ε : ℕ → ℚ}
               → Bounded (Sy.Sys vr s₀) (Ob.auditWatch s₀) ε → (q : ℕ)
               → ((Y : Iface) (E : Proc (Y ⊗ᴵ Sy.LedgerIf) Ωᴵ)
                   (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) (c : ℕ)
                  → Σ[ kb ∈ QB (κμ c)
                              (Kctx (openedᴹ Y Sy.LedgerIf (Ob.reportsLoss s₀) E) m) ]
                      CovCtx Sy.LedgerIf (κμ c) (Ob.reportsLoss s₀) kb)
               → HitsAt q (ε (κμ q)) (morphism (Sy.Sys vr s₀)) (auditMonitor ℓ ser s₀)
  ledger-hitsᶜ vr {ε} bnd q cov Y E m {c} {c′} qE qm le =
    eventDominatedᶜ (Ob.reportsLoss s₀) (Ob.auditWatchFrom s₀)
      (auditWatch-IsWatch ℓ ser s₀) (morphism (Sy.Sys vr s₀)) Y E m (κμ c)
      (proj₁ (cov Y E m c)) (proj₂ (cov Y E m c)) (ε (κμ q))
      λ d a → upper-run (Sy.Sys vr s₀) (Ob.auditWatch s₀ d)
                        (bnd (κμ q) d (asks≤-mono κμ-le d a))
    where
    c≤q : c ℕ.≤ q
    c≤q = ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-reflexive (sym (ℕP.*-identityʳ c)))
                                 (ℕP.*-monoʳ-≤ c (ℕP.m≤n⊔m c′ 1)))
                     le

    κμ-le : κμ c ℕ.≤ κμ q
    κμ-le = ℕP.*-monoʳ-≤ 2 (ℕP.⊔-mono-≤ c≤q ℕP.≤-refl)

  -- …and the same with the invariant discharged: unconditional, with the
  -- schedule read one query past the environment's own cap.
  ledger-hitsᵘ : (vr : Variant) {ε : ℕ → ℚ}
               → Bounded (Sy.Sys vr s₀) (Ob.auditWatch s₀) ε → (q : ℕ)
               → HitsAt q (ε (q ℕ.+ 1)) (morphism (Sy.Sys vr s₀))
                          (auditMonitor ℓ ser s₀)
  ledger-hitsᵘ vr bnd q =
    hitsᵘ (Ob.reportsLoss s₀) (Ob.auditWatchFrom s₀) (auditWatch-IsWatch ℓ ser s₀)
          (morphism (Sy.Sys vr s₀)) q
          λ d a → upper-run (Sy.Sys vr s₀) (Ob.auditWatch s₀ d) (bnd (q ℕ.+ 1) d a)
