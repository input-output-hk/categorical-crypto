{-# OPTIONS --safe --without-K #-}

-- Carrying an audit-form bound across an emulation: the graded half of the
-- seam's carry.
--
-- `UC.Seam.pov-carry` consumes agreement between two CLOSED processes, which is
-- what `UC.Seam.Grounded.unitGrade` reads off an emulation at a degenerate
-- grade.  An emulation in general is not that: `f ≤UC g` compares processes
-- carrying adversary interfaces and the simulator lives at that grade, so
-- `audit-carry` is the carry that keeps it — an ideal-side bound on the audit
-- event becomes a real-side bound at the emulation's slack, the simulator
-- absorbed into the environment leg, where `sub s` slides off the process and
-- onto the test and the test's own budget pays for the simulator's queries.
--
-- The event carried has to be INTERFACE-OBSERVABLE, and that is the content of
-- the restriction rather than a convenience: what a test reads is what an
-- emulation preserves.  A state trajectory is not such an event — the
-- simulator's state is not the ideal process's — which is why layer 1 states the
-- trajectory bound (`POV`) but carries a MONITOR's bound, the two tied by
-- `Examples.ChimericLedger.Trajectory`.
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

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Properties using (*-assoc; *-comm; ⊔-assoc; ⊔-idem)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-monoˡ-≤; module ≤-Reasoning)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst; sym; trans; module ≡-Reasoning)

open import CategoricalCrypto.UC.Approximate using (Mass)
open import CategoricalCrypto.UC.Budget using (Budget; ctxBudget)
open import CategoricalCrypto.UC.Core using (UCBase)

module CategoricalCrypto.UC.Audit
  {o ℓ e os ℓs qs : Level} (base : UCBase o ℓ e os ℓs)
  (bud : Budget (UCBase.𝒞 base) (UCBase.grading base) qs)
  (mass : Mass (UCBase.observation base)) where

open import CategoricalCrypto.UC.Emulation base

open Budget bud
open Mass mass

private variable A B′ X Y : Obj
                 w w′ : Level

infix 4 _≤UC[_]_

-- An emulation whose simulator carries a query budget.  A carry needs it: the
-- simulator ends up inside the environment leg, and a budget-indexed bound
-- charges its queries there.  Dropping it is dropping the standard notion's
-- polynomially bounded simulator, after which no budget-indexed bound survives.
record _≤UC[_]_ {A B′ X Y : Obj} (f : A ⇒ X ⊛ B′) (cs : ℕ) (g : A ⇒ Y ⊛ B′)
              : Set (o ⊔ ℓ ⊔ ℓs ⊔ qs) where
  field
    sim     : Y ⇒ X
    sim-qb  : QB cs sim
    emulate : f ≈ℰ (sub sim ∘ g)

open _≤UC[_]_ public

≤UC[]⇒≤UC : {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′} {cs : ℕ} → f ≤UC[ cs ] g → f ≤UC g
≤UC[]⇒≤UC e = sim e , emulate e

-- What the simulator costs the context absorbing it: the context's budget
-- rescaled by the simulator's, guarded exactly as `ctxBudget` guards its own.
simCost : ℕ → ℕ → ℕ
simCost q cs = q ℕ.* (cs ℕ.⊔ 1)

-- The designated audit event of a process with domain `A` and grade `X`: which
-- contexts around it — ancilla, test and closure — are trusted to read the
-- event, and at which budget.  A context is a test plus the closure it is taken
-- at, so both are indexed here; absorbing a simulator moves only the test.
AuditEvent : (w : Level) (A X B′ : Obj) → Set (o ⊔ ℓ ⊔ suc w)
AuditEvent w A X B′ =
  (Y : Obj) → Test (Y ⊛ (X ⊛ B′)) → Closure (Y ⊛ A) → ℕ → Set w

-- The audit-form bound: no PERMITTED context of budget `q` makes the watched
-- event's mass exceed `ε q`.  This is layer 1's `Bounded` shape — one
-- budget-indexed `ε`, quantified over the contexts of that budget the event
-- designates.
AuditBound : {A B′ X : Obj} → A ⇒ X ⊛ B′ → AuditEvent w A X B′ → (ℕ → ℚ)
           → Set (o ⊔ ℓ ⊔ qs ⊔ w)
AuditBound {A = A} {B′ = B′} {X = X} f 𝔈 ε =
  (Y : Obj) (Et : Test (Y ⊛ (X ⊛ B′))) (m : Closure (Y ⊛ A)) {c c′ : ℕ}
  → QB c Et → QB c′ m → 𝔈 Y Et m (ctxBudget c c′)
  → (n : ℕ) → at n (obs (tv₁ Y f Et) m) ℚ.≤ ε (ctxBudget c c′)

-- Absorbing a simulator of cost `cs` into a context: the ancilla and the
-- closure stay, the simulator goes in front of the test, the budget is rescaled
-- by what the simulator costs the context that now runs it.
absorb : (s : Y ⇒ X) (cs : ℕ) → AuditEvent w A Y B′ → AuditEvent w A X B′
absorb s cs 𝔈 W Et m q = 𝔈 W (Et ∘ T₁ W (sub s)) m (simCost q cs)

-- Closure of the permitted contexts under that absorption: every context the
-- real side permits the ideal side permits with the simulator in front of it.
-- This is what the carry needs of the two event data and the whole of it.
Absorbs : {A B′ X Y : Obj} (s : Y ⇒ X) (cs : ℕ)
        → AuditEvent w A X B′ → AuditEvent w′ A Y B′ → Set (o ⊔ ℓ ⊔ w ⊔ w′)
Absorbs {A = A} {B′ = B′} {X = X} s cs 𝔈 𝔉 =
  (W : Obj) (Et : Test (W ⊛ (X ⊛ B′))) (m : Closure (W ⊛ A)) (q : ℕ)
  → 𝔈 W Et m q → absorb s cs 𝔉 W Et m q

-- `absorb s cs 𝔉` is the largest class closed into `𝔉`, so an emulation always
-- has one to carry to: a real-side event need only be designated INSIDE it.
absorb-absorbs : {s : Y ⇒ X} {cs : ℕ} {𝔉 : AuditEvent w A Y B′}
               → Absorbs s cs (absorb s cs 𝔉) 𝔉
absorb-absorbs _ _ _ _ ev = ev

private
  -- Absorbing the simulator into the test rescales the context's budget by the
  -- simulator's own, and it does not matter which leg is charged.
  shuffle : (c c′ cs : ℕ)
          → ctxBudget (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) c′ ≡ simCost (ctxBudget c c′) cs
  shuffle c c′ cs = begin
    (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) ℕ.* (c′ ℕ.⊔ 1)  ≡⟨ cong (λ k → (c ℕ.* k) ℕ.* (c′ ℕ.⊔ 1)) (idem cs) ⟩
    (c ℕ.* (cs ℕ.⊔ 1)) ℕ.* (c′ ℕ.⊔ 1)          ≡⟨ *-assoc c (cs ℕ.⊔ 1) (c′ ℕ.⊔ 1) ⟩
    c ℕ.* ((cs ℕ.⊔ 1) ℕ.* (c′ ℕ.⊔ 1))          ≡⟨ cong (c ℕ.*_) (*-comm (cs ℕ.⊔ 1) (c′ ℕ.⊔ 1)) ⟩
    c ℕ.* ((c′ ℕ.⊔ 1) ℕ.* (cs ℕ.⊔ 1))          ≡⟨ *-assoc c (c′ ℕ.⊔ 1) (cs ℕ.⊔ 1) ⟨
    (c ℕ.* (c′ ℕ.⊔ 1)) ℕ.* (cs ℕ.⊔ 1)          ∎
    where
    open ≡-Reasoning

    idem : (k : ℕ) → (k ℕ.⊔ 1) ℕ.⊔ 1 ≡ k ℕ.⊔ 1
    idem k = trans (⊔-assoc k 1 1) (cong (k ℕ.⊔_) (⊔-idem 1))

-- The graded carry.  The ideal side is tested through `Et ∘ T₁ W (sub s)` — the
-- same context with the simulator in front of it — so the hypothesis applies at
-- a budget the test pays for and at an event the absorption keeps permitted,
-- and the emulation's slack `δ` is what separates the two masses.
audit-carry : (f : A ⇒ X ⊛ B′) (g : A ⇒ Y ⊛ B′) {cs : ℕ} (em : f ≤UC[ cs ] g)
              {𝔈 : AuditEvent w A X B′} {𝔉 : AuditEvent w′ A Y B′}
            → Absorbs (sim em) cs 𝔈 𝔉
            → (ε : ℕ → ℚ) (δ : ℚ) → 0ℚ ℚ.< δ
            → AuditBound g 𝔉 ε → AuditBound f 𝔈 (λ q → ε (simCost q cs) ℚ.+ δ)
audit-carry {B′ = B′} {Y = Y} f g {cs} em {𝔉 = 𝔉} cl ε δ δ>0
            bnd W Et m {c} {c′} qEt qm ev n =
  subst (λ k → at n x ℚ.≤ ε k ℚ.+ δ) (shuffle c c′ cs) bound
  where
  s = sim em

  Et′ : Test (W ⊛ (Y ⊛ B′))
  Et′ = Et ∘ T₁ W (sub s)

  x = obs (tv₁ W f Et) m
  z = obs (tv₁ W g Et′) m

  qEt′ : QB (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) Et′
  qEt′ = qb-∘ qEt (qb-T₁ (qb-sub (sim-qb em)))

  ev′ : 𝔉 W Et′ m (ctxBudget (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) c′)
  ev′ = subst (𝔉 W Et′ m) (sym (shuffle c c′ cs)) (cl W Et m (ctxBudget c c′) ev)

  -- The simulator slides off the process and onto the test.
  slide : (Et ∘ T₁ W (sub s ∘ g)) ∘ m ≈ (Et′ ∘ T₁ W g) ∘ m
  slide = ∘-resp-≈ˡ (Equiv.trans (∘-resp-≈ʳ T₁-∘) sym-assoc)

  near : x ∼ z
  near = ∼-trans (emulate em W Et m) (⟦⟧-resp-≈ slide)

  bound : at n x ℚ.≤ ε (ctxBudget (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) c′) ℚ.+ δ
  bound = let k , le = dominate near δ δ>0 n in begin
    at n x        ≤⟨ le ⟩
    at k z ℚ.+ δ  ≤⟨ +-monoˡ-≤ δ (bnd W Et′ m qEt′ qm ev′ k) ⟩
    ε _ ℚ.+ δ     ∎
    where open ≤-Reasoning
