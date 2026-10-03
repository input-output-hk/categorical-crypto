{-# OPTIONS --safe --without-K --guardedness #-}

-- Event bounds at the machine: the capped-allowance presentation, and the
-- absorption of a morphism into the context.
--
-- An event bound is a one-sided bound (`ProbabilisticLogic.Dp.Advantage.Upper`)
-- on what a certified context observes.  What makes a context read an EVENT
-- rather than an arbitrary verdict is a `Reader` — a way of building the test
-- the environment is run inside — and nothing below knows how one is built.
-- `UC.Machine.StateEvent.Read.flagReader` is one; `advReader` is another, an adversary
-- between the test and the process, and absorbing a simulator into the
-- process is absorbing it into that adversary (`readRun-absorb`).
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
open import Level
open import Relation.Binary.PropositionalEquality

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Distribution.Uniform.Decay
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.Machines.Run.Sim
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Compose.Laws

module CategoricalCrypto.UC.Machine.EventBounds where

private
  module 𝒫 = Category 𝒫ᴵ
  open 𝒫.HomReasoning

  variable
    A B B′ C X Z : Iface
    k q t : ℕ
    r : ℚ

------------------------------------------------------------------------
-- Reading an event off a context

conjᴵ : Proc unitᴵ B → Proc unitᴵ (unitᴵ ⊗ᴵ B)
conjᴵ u = λᴵ⇐ 𝒫.∘ u

-- What a budgeted ancilla context observes when a process is plugged into it:
-- exactly the closed run `_≈ℰ_` compares.
ctxRun : (Y : Iface) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Proc A B → Dₚ Bool
ctxRun Y E m f = ⟦ (E 𝒫.∘ T₁ᴵ Y f) 𝒫.∘ m ⟧ᴼ

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
-- experiment as that morphism in front of the test.
ctxRun-∘ : (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A))
           (s : Proc C B) (x : Proc A C)
         → ctxRun Y E m (s 𝒫.∘ x) ≈ₚ ctxRun Y (E 𝒫.∘ T₁ᴵ Y s) m x
ctxRun-∘ Y E m s x =
  runᴹ-resp-≈ᴹ
    (𝒫.∘-resp-≈ˡ (𝒫.Equiv.trans (𝒫.∘-resp-≈ʳ (T₁-∘ s x)) 𝒫.sym-assoc)) (ask tt out)

advReader : Proc X 𝟭ᴵ → Reader B (X ⊗ᴵ B)
advReader a Y E = E 𝒫.∘ T₁ᴵ Y (plugᴹ a)

plug-absorb : (a : Proc X 𝟭ᴵ) (s : Proc Z X) (g : Proc A (Z ⊗ᴵ B))
            → plugᴹ a 𝒫.∘ (subᴵ s 𝒫.∘ g) 𝒫.≈ plugᴹ (a 𝒫.∘ s) 𝒫.∘ g
plug-absorb a s g = 𝒫.assoc ○ (refl⟩∘⟨ (𝒫.sym-assoc ○ (⟺ (sub-∘ a s) ⟩∘⟨refl))) ○ 𝒫.sym-assoc

readRun-absorb : (a : Proc X 𝟭ᴵ) {f : Proc A (X ⊗ᴵ B)} {s : Proc Z X} {g : Proc A (Z ⊗ᴵ B)}
               → f 𝒫.≈ subᴵ s 𝒫.∘ g → (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A))
               → readRun Y f (advReader a) E m ≈ₚ readRun Y g (advReader (a 𝒫.∘ s)) E m
readRun-absorb a {f} {s} {g} e Y E m =
      ≈sym (ctxRun-∘ Y E m (plugᴹ a) f)
  ⟨≈⟩ readRun-resp-≈ Y (𝒫.∘-resp-≈ʳ e ○ plug-absorb a s g) (λ _ E → E) E m
  ⟨≈⟩ ctxRun-∘ Y E m (plugᴹ (a 𝒫.∘ s)) g

-- No certified context of allowance at most `q` makes the event's mass exceed
-- `r`.  The cap is on the ORIGINAL environment's allowance, and it is
-- essential — at `q = 0` a bound over every context with the schedule read at
-- a constant would bound arbitrarily large ones.
BoundedAt : ℕ → ℚ → Proc A B′ → Reader B B′ → Set₁
BoundedAt {A = A} {B = B} q r f 𝔠 =
    (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m → scale c (positive c′) ℕ.≤ q → Upper (readRun Y f 𝔠 E m) r

-- Every adversary of rate `k`, at every context of cap `q`.
AdvBoundedAt : ℕ → ℕ → ℚ → Proc A (X ⊗ᴵ B) → Set₁
AdvBoundedAt {X = X} k q r f = (a : Proc X 𝟭ᴵ) → QB k a → BoundedAt q r f (advReader a)

-- The simulator's rate multiplies the ADVERSARY's allowance; the context cap is
-- untouched, and an exact factoring costs no slack.
bounded-absorb : {f : Proc A (X ⊗ᴵ B)} {s : Proc Z X} {g : Proc A (Z ⊗ᴵ B)}
               → f 𝒫.≈ subᴵ s 𝒫.∘ g → QB t s → AdvBoundedAt (k ℕ.* t) q r g → AdvBoundedAt k q r f
bounded-absorb {X = X} {Z = Z} {s = s} e qs h a qa Y E m qE qm le =
  upper-≈ (readRun-absorb a e Y E m) (h (a 𝒫.∘ s) (qb-∘-category Z X 𝟭ᴵ a s qa qs) Y E m qE qm le)

------------------------------------------------------------------------
-- Families, and where the slack's quantifier sits

module _ {A B B′ : ℕ → Iface} (f : (n : ℕ) → Proc (A n) (B′ n))
         (𝔠 : (n : ℕ) → Reader (B n) (B′ n)) where

  Boundedᶠ : (ℕ → ℕ → ℚ) → Set₁
  Boundedᶠ ε = (n q : ℕ) → BoundedAt q (ε n q) (f n) (𝔠 n)

  Boundedᴺ : (ℕ → ℕ → ℚ) → Set₁
  Boundedᴺ = Saturated λ n q r → BoundedAt q r (f n) (𝔠 n)

  -- A capped family bound is already a saturated one, at zero slack: its
  -- schedule `ε n (p n)` is uniform over the contexts `p n` admits.  A bound
  -- whose slack is chosen INSIDE the context quantifier yields no `Boundedᴺ`.
  boundedᶠ⇒boundedᴺ : (ε : ℕ → ℕ → ℚ) → Boundedᶠ ε → Boundedᴺ ε
  boundedᶠ⇒boundedᴺ _ h _ _ =
      (λ _ → 0ℚ) , Negligible-0
    , λ n Y E m qE qm le →
        upper-mono (≤-reflexive (sym (+-identityʳ _))) (h n _ Y E m qE qm le)
