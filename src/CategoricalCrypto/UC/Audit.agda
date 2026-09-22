{-# OPTIONS --safe --without-K #-}

-- Carrying an audit-form bound across an emulation: the graded half of the
-- seam's carry.
--
-- At a degenerate grade an emulation collapses to agreement between two CLOSED
-- processes (`UC.Seam.Grounded.subBlind`).  An emulation in general is not
-- that: `f ≤UC g` compares processes
-- carrying adversary interfaces and the simulator lives at that grade, so
-- `audit-carry` is the carry that keeps it — an ideal-side bound on the audit
-- event becomes a real-side bound at the emulation's slack, the simulator
-- absorbed into the environment leg, where the simulator slides off the
-- process and onto the test and the test's own budget pays for its queries.
--
-- The event carried has to be INTERFACE-OBSERVABLE, and that is the content of
-- the restriction rather than a convenience: what a test reads is what an
-- emulation preserves.  A state trajectory is not such an event — the
-- simulator's state is not the ideal process's — which is why the ledger
-- example carries a WATCH's bound, and recovers the trajectory only under an
-- extra truthfulness hypothesis (`Examples.ChimericLedger.Observable`).
--
-- WHICH event is carried is DATA (`AuditEvent`): the contexts permitted to read
-- it.  Quantifying over every budgeted test instead — which is what this module
-- did before `docs/protocol-implementation-review.md` §1 — bounds the mass of a
-- constant-`true` verdict too, so at a trivial-grade protocol image the premise
-- forces `1 ≤ ε q` and no ideal theorem can supply it.  That statement is this
-- one at the total event class; the repair is that a SMALL class is now
-- expressible, and `UC.Seam.Audit`'s is supplied by an ordinary ideal bound on
-- a monitor whose truthfulness is the instance's own theorem.
--
-- Everything here is generic in the base, and deliberately so: at the intended
-- instance a term whose type is an `≈ℰ` between machine composites η-expands the
-- observation record and with it the machine equality (`UC.Seam.Grounding`'s
-- header measures it), so the arithmetic runs once here rather than never there.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-monoˡ-≤; module ≤-Reasoning)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import CategoricalCrypto.UC.Approximate using (Mass)
open import CategoricalCrypto.UC.Budget using (Budget; ctxBudget; ctxBudget-absorb)
open import CategoricalCrypto.UC.Core using (Observation)

module CategoricalCrypto.UC.Audit
  {o ℓ e os ℓs qs : Level} (M : MonoidalCategory o ℓ e)
  (O : Observation (MonoidalCategory.U M) os ℓs)
  (bud : Budget M qs) (mass : Mass O) where

open import CategoricalCrypto.UC.Environment M O

open Budget bud
open Mass mass

-- What the simulator costs the context absorbing it, and the arithmetic of
-- that rescaling: `UC.Budget`, where every absorption's allowance substitution
-- is proved once.
open import CategoricalCrypto.UC.Budget using (q≤simCost; simCost) public

private variable A B′ X Y : Obj
                 w w′ : Level

infix 4 _≤UC[_]_

-- An emulation whose simulator carries a query budget.  A carry needs it: the
-- simulator ends up inside the environment leg, and a budget-indexed bound
-- charges its queries there.  Dropping it is dropping the standard notion's
-- polynomially bounded simulator, after which no budget-indexed bound survives.
record _≤UC[_]_ {A B′ X Y : Obj} (f : A ⇒ X ⊗₀ B′) (cs : ℕ) (g : A ⇒ Y ⊗₀ B′)
              : Set (o ⊔ ℓ ⊔ ℓs ⊔ qs) where
  field
    sim     : Y ⇒ X
    sim-qb  : QB cs sim
    emulate : f ≈ℰ (sim ⊗₁ id ∘ g)

open _≤UC[_]_ public

-- The designated audit event of a process with domain `A` and grade `X`: which
-- contexts around it — ancilla, test and closure — are trusted to read the
-- event, and at which budget.  A context is a test plus the closure it is taken
-- at, so both are indexed here; absorbing a simulator moves only the test.
AuditEvent : (w : Level) (A X B′ : Obj) → Set (o ⊔ ℓ ⊔ suc w)
AuditEvent w A X B′ =
  (Y : Obj) → Test (Y ⊗₀ (X ⊗₀ B′)) → Closure (Y ⊗₀ A) → ℕ → Set w

-- The audit-form bound: no PERMITTED context of budget `q` makes the watched
-- event's mass exceed `ε q`.  This is layer 1's `Bounded` shape — one
-- budget-indexed `ε`, quantified over the contexts of that budget the event
-- designates.
AuditBound : {A B′ X : Obj} → A ⇒ X ⊗₀ B′ → AuditEvent w A X B′ → (ℕ → ℚ)
           → Set (o ⊔ ℓ ⊔ qs ⊔ w)
AuditBound {A = A} {B′ = B′} {X = X} f 𝔈 ε =
  (Y : Obj) (Et : Test (Y ⊗₀ (X ⊗₀ B′))) (m : Closure (Y ⊗₀ A)) {c c′ : ℕ}
  → QB c Et → QB c′ m → 𝔈 Y Et m (ctxBudget c c′)
  → (n : ℕ) → at n (obs (tv₁ Y f Et) m) ℚ.≤ ε (ctxBudget c c′)

-- An event class PINNED to a designated observation: a context reads it when
-- what it observes is the one the designation names for its budget.  Layer 1's
-- monitor run is abstracted away here, so this is available at ANY grade;
-- `Examples.HashForward.Audit` is the application at one that is not trivial.
pinned : {A B′ X : Obj} → A ⇒ X ⊗₀ B′ → (ℕ → Obs) → AuditEvent ℓs A X B′
pinned f μ Y Et m q = obs (tv₁ Y f Et) m ∼ μ q

-- …and its bound, off a bound on the designated observations alone.  The slack
-- is the `Mass`-level price of reading an equivalence as a numeric comparison:
-- `dominate` is what a general observation offers, and it is one-sided only up
-- to a positive `δ`.
pinned-bound : {A B′ X : Obj} (f : A ⇒ X ⊗₀ B′) (μ : ℕ → Obs) (ε : ℕ → ℚ)
               (δ : ℚ) → 0ℚ ℚ.< δ → ((q n : ℕ) → at n (μ q) ℚ.≤ ε q)
             → AuditBound f (pinned f μ) (λ q → ε q ℚ.+ δ)
pinned-bound f μ ε δ δ>0 bnd Y Et m {c} {c′} qEt qm ev n = begin
    at n (obs (tv₁ Y f Et) m)                 ≤⟨ proj₂ reach ⟩
    at (proj₁ reach) (μ (ctxBudget c c′)) ℚ.+ δ
      ≤⟨ +-monoˡ-≤ δ (bnd (ctxBudget c c′) (proj₁ reach)) ⟩
    ε (ctxBudget c c′) ℚ.+ δ                  ∎
  where
  open ≤-Reasoning
  reach = dominate ev δ δ>0 n

-- Absorbing a simulator of cost `cs` into a context: the ancilla and the
-- closure stay, the simulator goes in front of the test, the budget is rescaled
-- by what the simulator costs the context that now runs it.
absorb : (s : Y ⇒ X) (cs : ℕ) → AuditEvent w A Y B′ → AuditEvent w A X B′
absorb s cs 𝔈 W Et m q = 𝔈 W (Et ∘ id ⊗₁ (s ⊗₁ id)) m (simCost q cs)

-- Closure of the permitted contexts under that absorption: every context the
-- real side permits the ideal side permits with the simulator in front of it.
-- This is what the carry needs of the two event data and the whole of it.
Absorbs : {A B′ X Y : Obj} (s : Y ⇒ X) (cs : ℕ)
        → AuditEvent w A X B′ → AuditEvent w′ A Y B′ → Set (o ⊔ ℓ ⊔ w ⊔ w′)
Absorbs {A = A} {B′ = B′} {X = X} s cs 𝔈 𝔉 =
  (W : Obj) (Et : Test (W ⊗₀ (X ⊗₀ B′))) (m : Closure (W ⊗₀ A)) (q : ℕ)
  → 𝔈 W Et m q → absorb s cs 𝔉 W Et m q

-- `absorb s cs 𝔉` is the largest class closed into `𝔉`, so an emulation always
-- has one to carry to: a real-side event need only be designated INSIDE it.
absorb-absorbs : {s : Y ⇒ X} {cs : ℕ} {𝔉 : AuditEvent w A Y B′}
               → Absorbs s cs (absorb s cs 𝔉) 𝔉
absorb-absorbs _ _ _ _ ev = ev

-- The carry's whole structural content, with no event class and no budget on
-- it: what a context observes of the real process is dominated, at the
-- emulation's own slack, by what the SAME context with the simulator in front
-- of it observes of the ideal one.  Everything `AuditBound` adds to this is the
-- designation and the allowance arithmetic, which is why the plan's §4.2 asks
-- for the property-specific statement to be made here rather than through a
-- second action.
carry-obs : (f : A ⇒ X ⊗₀ B′) (g : A ⇒ Y ⊗₀ B′) (s : Y ⇒ X) → f ≈ℰ (s ⊗₁ id ∘ g)
          → (W : Obj) (Et : Test (W ⊗₀ (X ⊗₀ B′))) (m : Closure (W ⊗₀ A))
            (δ : ℚ) → 0ℚ ℚ.< δ → (n : ℕ)
          → Σ[ k ∈ ℕ ] at n (obs (tv₁ W f Et) m)
                       ℚ.≤ at k (obs (tv₁ W g (tv₁ W (s ⊗₁ id) Et)) m) ℚ.+ δ
carry-obs f g s em W Et m δ δ>0 =
  dominate (∼-trans (em W Et m) (⟦⟧-resp-≈ (∘-resp-≈ˡ (tv₁-∘ W (s ⊗₁ id) g Et)))) δ δ>0

-- The whole of the carry that is not the comparison: the ideal side is tested
-- through `Et ∘ id ⊗₁ (s ⊗₁ id)` — the same context with the simulator in
-- front of it — so the ideal bound applies at a budget the test pays for and
-- at an event the absorption keeps permitted, and the comparison's own error
-- is what separates the two masses.
--
-- The comparison is a SCHEDULE read at the allowance the real context carries,
-- because an explicit-error consumer (`UC.Quantitative.Family._≈ctx[_]_`) has
-- one and an arbitrary positive slack cannot stand in for it at a fixed
-- security parameter.  The two allowances are different and both are visible:
-- `ε` is read at the real context's `ctxBudget c c′`, `δ` at the absorbed
-- context's, which `ctxBudget-absorb` identifies with `simCost _ cs`.
audit-carryᵉ : (f : A ⇒ X ⊗₀ B′) (g : A ⇒ Y ⊗₀ B′) (s : Y ⇒ X) {cs : ℕ} → QB cs s
             → {𝔈 : AuditEvent w A X B′} {𝔉 : AuditEvent w′ A Y B′}
             → Absorbs s cs 𝔈 𝔉 → (ε δ : ℕ → ℚ)
             → ((W : Obj) (Et : Test (W ⊗₀ (X ⊗₀ B′))) (m : Closure (W ⊗₀ A))
                {c c′ : ℕ} → QB c Et → QB c′ m → (n : ℕ)
                → Σ[ k ∈ ℕ ] at n (obs (tv₁ W f Et) m)
                             ℚ.≤ at k (obs (tv₁ W g (tv₁ W (s ⊗₁ id) Et)) m)
                                 ℚ.+ ε (ctxBudget c c′))
             → AuditBound g 𝔉 δ → AuditBound f 𝔈 (λ q → δ (simCost q cs) ℚ.+ ε q)
audit-carryᵉ {B′ = B′} {Y = Y} f g s {cs} qs {𝔉 = 𝔉} cl ε δ near
             bnd W Et m {c} {c′} qEt qm ev n =
  subst (λ k → at n x ℚ.≤ δ k ℚ.+ ε (ctxBudget c c′)) (ctxBudget-absorb c c′ cs) bound
  where
  Et′ : Test (W ⊗₀ (Y ⊗₀ B′))
  Et′ = Et ∘ id ⊗₁ (s ⊗₁ id)

  x = obs (tv₁ W f Et) m
  z = obs (tv₁ W g Et′) m

  qEt′ : QB (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) Et′
  qEt′ = qb-∘ qEt (qb-T₁ (qb-sub qs))

  ev′ : 𝔉 W Et′ m (ctxBudget (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) c′)
  ev′ = subst (𝔉 W Et′ m) (sym (ctxBudget-absorb c c′ cs)) (cl W Et m (ctxBudget c c′) ev)

  bound : at n x ℚ.≤ δ (ctxBudget (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) c′) ℚ.+ ε (ctxBudget c c′)
  bound = let k , le = near W Et m qEt qm n in begin
    at n x                        ≤⟨ le ⟩
    at k z ℚ.+ ε (ctxBudget c c′)
      ≤⟨ +-monoˡ-≤ (ε (ctxBudget c c′)) (bnd W Et′ m qEt′ qm ev′ k) ⟩
    δ _ ℚ.+ ε (ctxBudget c c′)    ∎
    where open ≤-Reasoning

-- The graded carry: the same, at the comparison a QUALITATIVE emulation
-- supplies — `carry-obs`, whose error is the constant `δ` the domination is
-- read at.
audit-carry : (f : A ⇒ X ⊗₀ B′) (g : A ⇒ Y ⊗₀ B′) {cs : ℕ} (em : f ≤UC[ cs ] g)
              {𝔈 : AuditEvent w A X B′} {𝔉 : AuditEvent w′ A Y B′}
            → Absorbs (sim em) cs 𝔈 𝔉
            → (ε : ℕ → ℚ) (δ : ℚ) → 0ℚ ℚ.< δ
            → AuditBound g 𝔉 ε → AuditBound f 𝔈 (λ q → ε (simCost q cs) ℚ.+ δ)
audit-carry f g em {𝔈} {𝔉} cl ε δ δ>0 =
  audit-carryᵉ f g (sim em) (sim-qb em) {𝔈} {𝔉} cl (λ _ → δ) ε
    λ W Et m _ _ → carry-obs f g (sim em) (emulate em) W Et m δ δ>0
