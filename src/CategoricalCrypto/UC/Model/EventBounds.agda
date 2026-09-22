{-# OPTIONS --safe --without-K --guardedness #-}

-- Event bounds at the machine, and their explicit-error transport.
--
-- An event bound is a one-sided bound (`ProbabilisticLogic.Dp.Advantage.Upper`)
-- on what a certified context observes.  What makes a context read an EVENT
-- rather than an arbitrary verdict is a `Readout` — a way of building the test
-- the environment is run inside — and nothing below knows how one is built:
-- `UC.Machine.Monitor.compileᴹ` is the construction this layer exists for, and
-- `UC.Audit` makes the same restriction at an arbitrary base as a CLASS of
-- permitted contexts instead.  `UC.Audit.audit-carryᵉ` is this module's carry
-- over there; the two are not identified — bridging them is the sealed model's
-- job (`docs/event-bounds-in-setup.md`, "Architectural clarification").
--
-- Three resources stay distinct, and only the last of them appears here: the
-- environment's own queries to the process, whatever a readout spends
-- retrieving the event, and the coarse certificate `κ` of the test the two
-- together make, which is the one a quantitative comparison is instantiated
-- at.  `Charge` names the third and says nothing about the first two.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-identityʳ; ≤-reflexive)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ProbabilisticLogic.Dp using (Dₚ; _≈ₚ_; ≈ₚ-trans)
open import ProbabilisticLogic.Dp.Advantage
  using (Upper; _≈ₚ[_]_; upper-mono; upper-≈; upper-≈[])

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Approximate
  using (GradedBound-reindex; Negligible; Negligible-0; NegligibleBound)
open import CategoricalCrypto.UC.Budget
  using (ctxBudget; ctxBudget-simCost; simCost)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; T₁ᴵ)
open import CategoricalCrypto.UC.Machine.Bridge using (ctxRun)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-∘)
open import CategoricalCrypto.UC.Machine.Grading using (qb-T₁ᴵ)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.QueryBound using (QB)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)

module CategoricalCrypto.UC.Model.EventBounds where

private
  module 𝒫 = Category 𝒫ᴵ

  variable A B C : Iface
           c c′ cs : ℕ
           ε δ : ℕ → ℚ
           r r′ : ℚ

------------------------------------------------------------------------
-- Reading an event off a context

-- A way of turning a budgeted test into one whose verdict IS the event.  A
-- bound quantified over ALL tests would bound the mass of a constant-`true`
-- verdict too (`UC.Audit`'s header); restricting the tests is what makes an
-- event bound a statement about an event.
Readout : Iface → Set₁
Readout B = (Y : Iface) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B) Ωᴵ

Charge : Readout B → (ℕ → ℕ) → Set₁
Charge {B} 𝔠 κ = (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) {c : ℕ}
               → QB c E → QB (κ c) (𝔠 Y E)

readRun : (Y : Iface) → Proc A B → Readout B → Proc (Y ⊗ᴵ B) Ωᴵ
        → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool
readRun Y f 𝔠 E m = ctxRun Y (𝔠 Y E) m f

------------------------------------------------------------------------
-- The two allowance presentations

-- Capped, for a public statement: no certified context of allowance at most
-- `q` makes the event's mass exceed `r`.  The cap is on the ORIGINAL
-- environment's allowance, and it is essential — at `q = 0` a bound over
-- every context with the schedule read at a constant would bound arbitrarily
-- large ones.
BoundedAt : ℕ → ℚ → Proc A B → Readout B → Set₁
BoundedAt {A = A} {B = B} q r f 𝔠 =
    (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m → ctxBudget c c′ ℕ.≤ q → Upper (readRun Y f 𝔠 E m) r

-- Carried, for the proofs: the schedule read at the allowance the context's
-- two legs actually carry, `UC.Audit.AuditBound`'s shape.  Transport works
-- here because every absorption substitutes EXACTLY in a carried allowance,
-- where reading a schedule along an INEQUALITY would cost its monotonicity.
BoundedBy : (ℕ → ℚ) → Proc A B → Readout B → Set₁
BoundedBy {A = A} {B = B} ε f 𝔠 =
    (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m → Upper (readRun Y f 𝔠 E m) (ε (ctxBudget c c′))

-- Monotonicity in the allowance is what passing from the carried presentation
-- to the capped one costs, and the only thing it costs.
Monotone : (ℕ → ℚ) → Set
Monotone ε = {a b : ℕ} → a ℕ.≤ b → ε a ℚ.≤ ε b

carried⇒capped : {f : Proc A B} {𝔠 : Readout B} → Monotone ε
               → BoundedBy ε f 𝔠 → (q : ℕ) → BoundedAt q (ε q) f 𝔠
carried⇒capped mono h q Y E m qE qm le = upper-mono (mono le) (h Y E m qE qm)

-- …and back, at each context's own cap, which needs nothing of the schedule.
capped⇒carried : {f : Proc A B} {𝔠 : Readout B}
               → ((q : ℕ) → BoundedAt q (ε q) f 𝔠) → BoundedBy ε f 𝔠
capped⇒carried h Y E m qE qm = h _ Y E m qE qm ≤-refl

------------------------------------------------------------------------
-- Families, and where the slack's quantifier sits

module _ {A B : ℕ → Iface} (f : (n : ℕ) → Proc (A n) (B n))
         (𝔠 : (n : ℕ) → Readout (B n)) where

  Boundedᶠ : (ℕ → ℕ → ℚ) → Set₁
  Boundedᶠ ε = (n q : ℕ) → BoundedAt q (ε n q) (f n) (𝔠 n)

  -- The slack is chosen after the polynomial allowance and before the level,
  -- and is uniform over every context that allowance admits.
  Boundedᴺ : (ℕ → ℕ → ℚ) → Set₁
  Boundedᴺ ε = (p : ℕ → ℕ) → Poly p
             → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν
             × ((n : ℕ) → BoundedAt (p n) (ε n (p n) ℚ.+ ν n) (f n) (𝔠 n))

  carriedᶠ⇒boundedᶠ : (ε : ℕ → ℕ → ℚ) → ((n : ℕ) → Monotone (ε n))
                    → ((n : ℕ) → BoundedBy (ε n) (f n) (𝔠 n)) → Boundedᶠ ε
  carriedᶠ⇒boundedᶠ _ mono h n = carried⇒capped (mono n) (h n)

  -- What the two adapters give at the family level, and what they do NOT.
  -- A capped family bound is already a saturated one, at zero slack: its
  -- schedule `ε n (p n)` is uniform over the contexts `p n` admits.  Nothing
  -- goes the other way — `capped⇒carried` specializes a cap, it does not
  -- export a witness — so a carried bound whose slack is chosen INSIDE the
  -- context quantifier yields no `Boundedᴺ`.  That is why the carry below
  -- takes its error before the context, as `UC.Audit.audit-carryᵉ` does.
  boundedᶠ⇒boundedᴺ : (ε : ℕ → ℕ → ℚ) → Boundedᶠ ε → Boundedᴺ ε
  boundedᶠ⇒boundedᴺ _ h _ _ =
      (λ _ → 0ℚ) , Negligible-0
    , λ n Y E m qE qm le →
        upper-mono (≤-reflexive (sym (+-identityʳ _))) (h n _ Y E m qE qm le)

------------------------------------------------------------------------
-- Absorbing a morphism into the context

-- The relay is functorial, so a morphism in front of the process is the same
-- experiment as that morphism in front of the test.  `UC.Audit.absorb` is
-- this move at an arbitrary base, as a map on event classes rather than as an
-- equation between two observations.
ctxRun-∘ : (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A))
           (s : Proc C B) (x : Proc A C)
         → ctxRun Y E m (s 𝒫.∘ x) ≈ₚ ctxRun Y (E 𝒫.∘ T₁ᴵ Y s) m x
ctxRun-∘ Y E m s x =
  runᴹ-resp-≈ᴹ {Ωᴵ}
    (𝒫.∘-resp-≈ˡ (𝒫.Equiv.trans (𝒫.∘-resp-≈ʳ (T₁-∘ s x)) 𝒫.sym-assoc)) (ask tt out)

-- …and what it costs the test: `qb-T₁ᴵ`'s guard at `⊔ 1` under `qb-∘`'s
-- product, which is the product `UC.Budget.ctxBudget-simCost` turns into
-- `simCost` exactly.  One action and not two — `s` is the whole morphism
-- absorbed, where `UC.Audit.audit-carryᵉ` absorbs a grade morphism through
-- `sub` and then `T₁` and pays `⊔ 1` twice.
qb-absorb : (Y A′ B′ : Iface) (E : Proc (Y ⊗ᴵ B′) Ωᴵ) (s : Proc A′ B′)
          → QB c E → QB cs s → QB (c ℕ.* (cs ℕ.⊔ 1)) (E 𝒫.∘ T₁ᴵ Y s)
qb-absorb Y A′ B′ E s qE qs =
  qb-∘-category (Y ⊗ᴵ A′) (Y ⊗ᴵ B′) Ωᴵ E _ qE (qb-T₁ᴵ Y A′ B′ s qs)

-- What absorption asks of the two readouts: the simulator in front of the
-- REAL side's read test is the IDEAL side's read test with the simulator in
-- front of the ordinary one.  `UC.Audit.Absorbs` is the same requirement
-- between two event classes; where the classes are total, as they are here,
-- this equation is what is left of it.
Absorbsᵣ : (s : Proc C B) → Readout B → Readout C → Set₁
Absorbsᵣ {B = B} s 𝔠 𝔡 =
    (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ)
  → 𝒫._≈_ (𝔠 Y E 𝒫.∘ T₁ᴵ Y s) (𝔡 Y (E 𝒫.∘ T₁ᴵ Y s))

------------------------------------------------------------------------
-- The explicit-error carry

-- At ONE context: the comparison's error and the ideal side's bound, added.
-- The absorption is what makes the second one an ideal-side experiment at
-- all — without it there is no context for the ideal bound to be read at.
carry-upper : (f : Proc A B) (x : Proc A C) (s : Proc C B)
              (𝔠 : Readout B) (𝔡 : Readout C) → Absorbsᵣ s 𝔠 𝔡
            → (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A))
            → ctxRun Y (𝔠 Y E) m f ≈ₚ[ r′ ] ctxRun Y (𝔠 Y E) m (s 𝒫.∘ x)
            → Upper (readRun Y x 𝔡 (E 𝒫.∘ T₁ᴵ Y s) m) r
            → Upper (readRun Y f 𝔠 E m) (r ℚ.+ r′)
carry-upper f x s 𝔠 𝔡 abs Y E m near ideal = upper-≈[] near (upper-≈ slide ideal)
  where
  slide : ctxRun Y (𝔠 Y E) m (s 𝒫.∘ x) ≈ₚ readRun Y x 𝔡 (E 𝒫.∘ T₁ᴵ Y s) m
  slide = ≈ₚ-trans _ _ _ (ctxRun-∘ Y (𝔠 Y E) m s x)
            (runᴹ-resp-≈ᴹ {Ωᴵ} (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ˡ (abs Y E))) (ask tt out))

-- …and over every certified context, with both allowances named and exact.
--
--   `rμ` — where the COMPARISON is read.  The environment hands the readout a
--          test of rate `c`; what the comparison is instantiated at is the
--          read test, of rate `κ c`, so `rμ c c′ = ctxBudget (κ c) c′` and
--          never the environment's own `ctxBudget c c′`.
--   `rI` — where the IDEAL bound is read.  The absorbed test costs the
--          context `simCost _ cs`, `ctxBudget-simCost` exactly.
--
-- At the identity readout (`κ = id`, `𝔠 = 𝔡 = λ _ E → E`) the two collapse to
-- the intended `δ (simCost q cs) + ε q`; `UC.Machine.Monitor` is the instance
-- where `κ` is not the identity and the difference is visible.
carry-boundedBy :
    (f : Proc A B) (x : Proc A C) (s : Proc C B) → QB cs s
  → (𝔠 : Readout B) (𝔡 : Readout C) (κ : ℕ → ℕ) → Charge 𝔠 κ → Absorbsᵣ s 𝔠 𝔡
  → (ε δ : ℕ → ℚ)
  → ((Y : Iface) (E′ : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
     → QB c E′ → QB c′ m
     → ctxRun Y E′ m f ≈ₚ[ ε (ctxBudget c c′) ] ctxRun Y E′ m (s 𝒫.∘ x))
  → BoundedBy δ x 𝔡
  → (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m
  → Upper (readRun Y f 𝔠 E m)
          (δ (simCost (ctxBudget c c′) cs) ℚ.+ ε (ctxBudget (κ c) c′))
carry-boundedBy {cs = cs} f x s qs 𝔠 𝔡 κ chg abs ε δ near bnd
                Y E m {c} {c′} qE qm =
  carry-upper f x s 𝔠 𝔡 abs Y E m (near Y (𝔠 Y E) m (chg Y E qE) qm) ideal
  where
  ideal : Upper (readRun Y x 𝔡 (E 𝒫.∘ T₁ᴵ Y s) m) (δ (simCost (ctxBudget c c′) cs))
  ideal = subst (λ k → Upper (readRun Y x 𝔡 (E 𝒫.∘ T₁ᴵ Y s) m) (δ k))
                (ctxBudget-simCost c c′ cs)
                (bnd Y (E 𝒫.∘ T₁ᴵ Y s) m (qb-absorb Y _ _ E s qE qs) qm)

-- The reindexing a readout's charge performs is polynomial whenever the charge
-- is, so a negligible schedule read at `κ` stays negligible.  The `simCost`
-- half is `UC.Quantitative.Family.NegligibleBound-simCost`, the same
-- `GradedBound-reindex` at the other substitution.
NegligibleBound-charge : (κ : ℕ → ℕ) → ((p : ℕ → ℕ) → Poly p → Poly (λ n → κ (p n)))
                       → (ε : ℕ → ℕ → ℚ) → NegligibleBound ε
                       → NegligibleBound (λ n q → ε n (κ q))
NegligibleBound-charge κ = GradedBound-reindex Negligible (λ _ → κ)
