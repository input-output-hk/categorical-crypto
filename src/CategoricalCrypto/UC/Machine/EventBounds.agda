{-# OPTIONS --safe --without-K --guardedness #-}

-- Event bounds at the machine: the capped-allowance presentation, and the
-- absorption of a morphism into the context.
--
-- An event bound is a one-sided bound (`ProbabilisticLogic.Dp.Advantage.Upper`)
-- on what a certified context observes.  What makes a context read an EVENT
-- rather than an arbitrary verdict is a `Reader` — a way of building the test
-- the environment is run inside — and nothing below knows how one is built.
-- `UC.Machine.Monitor.flagReader` is one; `UC.Audit` makes the same
-- restriction at an arbitrary base as a CLASS of permitted contexts, and the
-- two are not identified (`docs/event-bounds-in-setup.md`, "What already
-- exists: `UC.Audit`").
--
-- Three resources stay distinct, and only the last of them is measured here:
-- the environment's own queries to the process, whatever a readout spends
-- retrieving the event, and the certificate of the test the two together
-- make, which is the one a quantitative comparison is instantiated at.

open import Categories.Category

open import Data.Bool.Base
open import Data.Nat.Base as ℕ
open import Data.Nat.Positive
open import Data.Nat.Poly
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Unit.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.Machine.EventBounds where

private
  module 𝒫 = Category 𝒫ᴵ

  variable A B B′ C : Iface

------------------------------------------------------------------------
-- Reading an event off a context

-- A way of turning a budgeted test into one whose verdict IS the event.  A
-- bound quantified over ALL tests would bound the mass of a constant-`true`
-- verdict too; restricting the tests is what makes an event bound a statement
-- about an event.
-- The readout may sit at a wider interface `B′` than the test's `B`: a
-- process that exposes its event on a port of its own
-- (`UC.Machine.StateEvent._▷_`) is read at `B ⊗ᴵ Ωᴵ`.
Reader : Iface → Iface → Set₁
Reader B B′ = (Y : Iface) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B′) Ωᴵ

readRun : (Y : Iface) → Proc A B′ → Reader B B′ → Proc (Y ⊗ᴵ B) Ωᴵ
        → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool
readRun Y f 𝔠 E m = ctxRun Y (𝔠 Y E) m f

readRun-resp-≈ : (Y : Iface) {f g : Proc A B′} → 𝒫._≈_ f g → (𝔠 : Reader B B′)
                 (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A))
               → readRun Y f 𝔠 E m ≈ₚ readRun Y g 𝔠 E m
readRun-resp-≈ Y e 𝔠 E m = runᴹ-resp-≈ᴹ (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ʳ (T₁-resp-≈ e))) (ask tt out)

-- The relay is functorial, so a morphism in front of the process is the same
-- experiment as that morphism in front of the test.  `UC.Audit.absorb` is
-- this move at an arbitrary base, as a map on event classes.
ctxRun-∘ : (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A))
           (s : Proc C B) (x : Proc A C)
         → ctxRun Y E m (s 𝒫.∘ x) ≈ₚ ctxRun Y (E 𝒫.∘ T₁ᴵ Y s) m x
ctxRun-∘ Y E m s x =
  runᴹ-resp-≈ᴹ
    (𝒫.∘-resp-≈ˡ (𝒫.Equiv.trans (𝒫.∘-resp-≈ʳ (T₁-∘ s x)) 𝒫.sym-assoc)) (ask tt out)

-- No certified context of allowance at most `q` makes the event's mass exceed
-- `r`.  The cap is on the ORIGINAL environment's allowance, and it is
-- essential — at `q = 0` a bound over every context with the schedule read at
-- a constant would bound arbitrarily large ones.
BoundedAt : ℕ → ℚ → Proc A B′ → Reader B B′ → Set₁
BoundedAt {A = A} {B = B} q r f 𝔠 =
    (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m → scale c (positive c′) ℕ.≤ q → Upper (readRun Y f 𝔠 E m) r

------------------------------------------------------------------------
-- Families, and where the slack's quantifier sits

-- One negligible slack per polynomial cap, chosen before the security
-- parameter.  Belongs beside `UC.Approximate.GradedBound` once that file is open.
Saturated : {ℓ : Level} → (ℕ → ℕ → ℚ → Set ℓ) → (ℕ → ℕ → ℚ) → Set ℓ
Saturated X ε = (p : ℕ → ℕ) → Poly p
              → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν × ((n : ℕ) → X n (p n) (ε n (p n) ℚ.+ ν n))

saturated-map : {ℓ ℓ′ : Level} {X : ℕ → ℕ → ℚ → Set ℓ} {Y : ℕ → ℕ → ℚ → Set ℓ′} {ε : ℕ → ℕ → ℚ}
              → ((n q : ℕ) {r : ℚ} → X n q r → Y n q r) → Saturated X ε → Saturated Y ε
saturated-map g h p Pp = let ν , neg , b = h p Pp in ν , neg , λ n → g n (p n) (b n)

module _ {A B B′ : ℕ → Iface} (f : (n : ℕ) → Proc (A n) (B′ n))
         (𝔠 : (n : ℕ) → Reader (B n) (B′ n)) where

  Boundedᶠ : (ℕ → ℕ → ℚ) → Set₁
  Boundedᶠ ε = (n q : ℕ) → BoundedAt q (ε n q) (f n) (𝔠 n)

  Boundedᴺ : (ℕ → ℕ → ℚ) → Set₁
  Boundedᴺ = Saturated λ n q r → BoundedAt q r (f n) (𝔠 n)

  -- A capped family bound is already a saturated one, at zero slack: its
  -- schedule `ε n (p n)` is uniform over the contexts `p n` admits.  A bound
  -- whose slack is chosen INSIDE the context quantifier yields no `Boundedᴺ`,
  -- which is why the carry takes its error before the context, as
  -- `UC.Audit.audit-carry` does.
  boundedᶠ⇒boundedᴺ : (ε : ℕ → ℕ → ℚ) → Boundedᶠ ε → Boundedᴺ ε
  -- A schedule read at a larger cap is still a bound: the contexts a cap
  -- admits only grow with it.
  boundedᴺ-reindex : (ε : ℕ → ℕ → ℚ) (cap : ℕ → ℕ) → ((q : ℕ) → q ℕ.≤ cap q)
                   → ({p : ℕ → ℕ} → Poly p → Poly (λ n → cap (p n)))
                   → Boundedᴺ ε → Boundedᴺ (λ n q → ε n (cap q))
  boundedᴺ-reindex _ cap le pc h p pp = let ν , nν , b = h (λ n → cap (p n)) (pc pp) in
    ν , nν , λ n Y E m qE qm le′ → b n Y E m qE qm (ℕP.≤-trans le′ (le (p n)))

  boundedᶠ⇒boundedᴺ _ h _ _ =
      (λ _ → 0ℚ) , Negligible-0
    , λ n Y E m qE qm le →
        upper-mono (≤-reflexive (sym (+-identityʳ _))) (h n _ Y E m qE qm le)
