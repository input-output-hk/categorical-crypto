{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- The probabilistic machine layer as a model of the UC metatheory.
--
-- `CategoricalCrypto.MachineAxioms` axiomatizes one security level of a
-- machine layer; this module builds that model out of a `Machines` structure.
-- Three things happen here.
--
-- 1. Machines form a monoidal category whose hom-equality is OBSERVATIONAL
--    (`f ≈ₚ g = ⟦ f ⟧ ≈ᵉ ⟦ g ⟧`).  `Machines` supplies `_⊚_` with no laws, so
--    the laws and the tensor are the hypotheses `MachineCategory` /
--    `MonoidalMachines`.
-- 2. A closed experiment is a machine `unit ⇒ Ω` at the verdict channel
--    `Ω = Bool ⇿ ⊤`: it receives one trigger and answers with a bit.  This is
--    where the theory's BINARY advantage meets the concrete TERNARY one
--    (`adv f g d`, carrying an adaptive distinguisher): the distinguisher is
--    absorbed into the morphism, and reappears as the CONTEXT a machine is
--    plugged into (`UC.Machine.Bridge`, `UC.Seam`).  Everything on this side is
--    proven — `Obs`, `adv⊥` and its three laws come from `Pr₁⊥` and
--    ℚ-absolute-value facts.
-- 3. Counting: `QueryBudget` is the instrument `MachineAxioms.QB` asks for —
--    "one codomain-side activation of `h` causes at most `c` completed
--    domain-side events" — again a hypothesis, being a property of the trace.
--
-- `MachineModel` bundles the hypotheses and derives `axioms`.
--------------------------------------------------------------------------------

open import CategoricalCrypto.Machine.Probabilistic using (Machines)

module CategoricalCrypto.Machine.Probabilistic.Model (PM : Machines) where

open import Data.Bool.Base using (Bool)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat as ℕ using (ℕ)
open import Data.Rational using (ℚ; 0ℚ)
  renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (+-inverseʳ; ∣-p∣≡∣p∣; ∣p+q∣≤∣p∣+∣q∣)
open import Data.Rational.Properties.Ext using (neg-sub; telescope)
open import Data.Unit.Base using (⊤; tt)
open import Level using (0ℓ; suc)
open import Relation.Binary using (IsEquivalence; Setoid)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal using (Monoidal; MonoidalCategory)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import CategoricalCrypto.Channel.Core using (Channel; _⇿_; I)
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.MachineAxioms using (MachineAxioms)
open import CategoricalCrypto.SFunM using (_≈ᵉ_; ≈ᵉ-isEquivalence)
open import CategoricalCrypto.SFunPartial
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist using (_≈Mℚ_)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Pr₁⊥; mb)
open import ProbabilisticLogic.Distribution.RationalDist.Partial using (Dist⊥)
open import ProbabilisticLogic.Distribution.RationalDist.Setoid using (Mℚ-setoid)

open Machines PM public

private variable A B C : Channel

------------------------------------------------------------------------
-- Machines up to observation

-- Closed semantics: a machine with no subroutine (input channel `I = ⊥ ⇿ ⊥`) has
-- a plain kernel `outType C → inType C` — the empty `⊥` interface is dropped.
⟦_⟧cl : PMachine I C → SFun⊥ (Channel.outType C) (Channel.inType C)
⟦ m ⟧cl = strip⊥ ⟦ m ⟧

-- Every equational fact about machines goes through `⟦_⟧` into the trace setoid
-- of `SFun⊥`, so that is the machine category's hom-equality.
infix 4 _≈ₚ_

_≈ₚ_ : PMachine A B → PMachine A B → Set
f ≈ₚ g = (_≈ᵉ_ {M = Dist⊥}) ⟦ f ⟧ ⟦ g ⟧

≈ₚ-isEquivalence : IsEquivalence (_≈ₚ_ {A} {B})
≈ₚ-isEquivalence = On.isEquivalence ⟦_⟧ (≈ᵉ-isEquivalence {M = Dist⊥})

-- Concrete security, output-only: no distinguisher issuing at most `n` queries
-- separates the two closed machines by more than `ε n`.
infix 4 _≈adv[_]_

_≈adv[_]_ : PMachine I C → (ℕ → ℚ) → PMachine I C → Set
f ≈adv[ ε ] g = ∀ n d → asks≤ n d → adv ⟦ f ⟧cl ⟦ g ⟧cl d ≤ℚ ε n

------------------------------------------------------------------------
-- The verdict channel, and the advantage pseudometric on observations
--
-- `Ω` receives one trigger (`⊤`) and answers with a verdict bit, so a machine
-- `unit ⇒ Ω` is a complete closed experiment and `askOnce` merely reads the bit
-- off.  `Interaction.adv f g d` is `adv⊥ (run⊥ f d) (run⊥ g d)` on the nose.

Ω : Channel
Ω = Bool ⇿ ⊤

askOnce : Strat ⊤ Bool
askOnce = ask tt out

Obs : Setoid 0ℓ 0ℓ
Obs = Mℚ-setoid (Maybe Bool)

adv⊥ : Dist⊥ Bool → Dist⊥ Bool → ℚ
adv⊥ μ ν = ∣ Pr₁⊥ μ -ℚ Pr₁⊥ ν ∣ℚ

adv⊥-sym : ∀ μ ν → adv⊥ μ ν ≡ adv⊥ ν μ
adv⊥-sym μ ν = trans (cong ∣_∣ℚ (neg-sub (Pr₁⊥ μ) (Pr₁⊥ ν))) (∣-p∣≡∣p∣ _)

adv⊥-triangle : ∀ μ ν ρ → adv⊥ μ ρ ≤ℚ adv⊥ μ ν +ℚ adv⊥ ν ρ
adv⊥-triangle μ ν ρ =
  subst (λ z → ∣ z ∣ℚ ≤ℚ adv⊥ μ ν +ℚ adv⊥ ν ρ)
        (telescope (Pr₁⊥ μ) (Pr₁⊥ ν) (Pr₁⊥ ρ))
        (∣p+q∣≤∣p∣+∣q∣ (Pr₁⊥ μ -ℚ Pr₁⊥ ν) (Pr₁⊥ ν -ℚ Pr₁⊥ ρ))

adv⊥-≈⇒0 : {μ ν : Dist⊥ Bool} → μ ≈Mℚ ν → adv⊥ μ ν ≡ 0ℚ
adv⊥-≈⇒0 {μ} = λ e → trans (cong (λ z → ∣ Pr₁⊥ μ -ℚ z ∣ℚ) (sym (e mb)))
                           (cong ∣_∣ℚ (+-inverseʳ (Pr₁⊥ μ)))

------------------------------------------------------------------------
-- The machine layer's outstanding structure, as hypotheses

-- `Machines` gives `_⊚_` with no laws at all; the trace they hold of is
-- `Machines.Base.Tracedₚ`.
record MachineCategory : Set (suc (suc 0ℓ)) where
  field
    ⊚-assoc     : ∀ {A B C D} {f : PMachine A B} {g : PMachine B C} {h : PMachine C D}
                → ((h ⊚ g) ⊚ f) ≈ₚ (h ⊚ (g ⊚ f))
    ⊚-identityˡ : ∀ {A B} {f : PMachine A B} → (pid ⊚ f) ≈ₚ f
    ⊚-identityʳ : ∀ {A B} {f : PMachine A B} → (f ⊚ pid) ≈ₚ f
    ⊚-resp-≈    : ∀ {A B C} {g i : PMachine B C} {f h : PMachine A B}
                → g ≈ₚ i → f ≈ₚ h → (g ⊚ f) ≈ₚ (i ⊚ h)

machines : MachineCategory → Category (suc 0ℓ) (suc 0ℓ) 0ℓ
machines mc = categoryHelper record
  { Obj = Channel ; _⇒_ = PMachine ; _≈_ = _≈ₚ_ ; id = pid ; _∘_ = _⊚_
  ; assoc = ⊚-assoc ; identityˡ = ⊚-identityˡ ; identityʳ = ⊚-identityʳ
  ; equiv = ≈ₚ-isEquivalence ; ∘-resp-≈ = ⊚-resp-≈ }
  where open MachineCategory mc

record MonoidalMachines : Set (suc (suc 0ℓ)) where
  field
    cat : MachineCategory
    -- The channel-level tensor and unit are already concrete; outstanding are
    -- the machine-level structural morphisms and all the laws, with the unit
    -- pinned to the empty channel `I`.
    mono   : Monoidal (machines cat)
    unit≡I : Monoidal.unit mono ≡ I

  open MachineCategory cat public

  𝕄 : MonoidalCategory (suc 0ℓ) (suc 0ℓ) 0ℓ
  𝕄 = record { U = machines cat ; monoidal = mono }

  module M = MonoidalCategory 𝕄

-- `QB c h` reads "one codomain-side activation of `h` causes at most `c`
-- completed domain-side events".
record QueryBudget (mm : MonoidalMachines) : Set (suc (suc 0ℓ)) where
  open MonoidalMachines mm
  open MonoidalUtilities.Shorthands mono

  field
    QB        : ℕ → ∀ {A B} → PMachine A B → Set
    qb-id     : ∀ {A} → QB 1 (pid {A})
    qb-∘      : ∀ {A B C c c′} {g : PMachine B C} {f : PMachine A B}
              → QB c g → QB c′ f → QB (c ℕ.* c′) (g ⊚ f)
    qb-⊗      : ∀ {A B C D c c′} {f : PMachine A B} {h : PMachine C D}
              → QB c f → QB c′ h → QB (c ℕ.⊔ c′) (f M.⊗₁ h)
    qb-resp-≈ : ∀ {A B c} {f g : PMachine A B} → f ≈ₚ g → QB c f → QB c g
    qb-mono   : ∀ {A B c c′} {f : PMachine A B} → c ℕ.≤ c′ → QB c f → QB c′ f
    qb-α⇒     : ∀ {A B C} → QB 1 (α⇒ {A} {B} {C})
    qb-α⇐     : ∀ {A B C} → QB 1 (α⇐ {A} {B} {C})
    qb-λ⇒     : ∀ {A} → QB 1 (λ⇒ {A})
    qb-λ⇐     : ∀ {A} → QB 1 (λ⇐ {A})
    qb-ρ⇒     : ∀ {A} → QB 1 (ρ⇒ {A})
    qb-ρ⇐     : ∀ {A} → QB 1 (ρ⇐ {A})

------------------------------------------------------------------------
-- The model

record MachineModel : Set (suc (suc (suc 0ℓ))) where
  field
    structure : MonoidalMachines
    budget    : QueryBudget structure

  open MonoidalMachines structure public
  open QueryBudget budget public

  -- The interaction layer's assumption: needed to read a machine equality as
  -- an equality of adaptive runs.
  field trace-run : TraceDeterminesRun

  -- The transport along `unit≡I` is what lets a `unit ⇒ Ω` machine be read as
  -- the subroutine-free `PMachine I Ω` whose closed semantics `⟦_⟧cl` computes,
  -- and `fromI` is the same transport the other way round.
  toI : PMachine M.unit C → PMachine I C
  toI {C} = subst (λ U → PMachine U C) unit≡I

  fromI : PMachine I C → PMachine M.unit C
  fromI {C} = subst (λ U → PMachine U C) (sym unit≡I)

  obs : PMachine M.unit Ω → Dist⊥ Bool
  obs u = run⊥ ⟦ toI u ⟧cl askOnce

  obs-cong : {u u′ : PMachine M.unit Ω} → u ≈ₚ u′ → obs u ≈Mℚ obs u′
  obs-cong = go unit≡I
    where
    go : ∀ {U} (p : U ≡ I) {u u′ : PMachine U Ω} → u ≈ₚ u′
       → run⊥ ⟦ subst (λ V → PMachine V Ω) p u  ⟧cl askOnce
     ≈Mℚ run⊥ ⟦ subst (λ V → PMachine V Ω) p u′ ⟧cl askOnce
    go refl e = trace-run (strip⊥-cong e) askOnce

  axioms : MachineAxioms (suc 0ℓ) (suc 0ℓ) 0ℓ 0ℓ 0ℓ 0ℓ
  axioms = record
    { 𝕄 = 𝕄 ; Ω = Ω ; Obs = Obs ; ⟦_⟧ = obs ; adv = adv⊥ ; QB = QB
    ; ⟦⟧-resp-≈ = λ {f} {g} → obs-cong {f} {g}
    ; adv-sym = adv⊥-sym ; adv-triangle = adv⊥-triangle
    ; adv-≈⇒0 = λ {x} {y} → adv⊥-≈⇒0 {x} {y}
    ; qb-id = qb-id ; qb-∘ = qb-∘ ; qb-⊗ = qb-⊗ ; qb-resp-≈ = qb-resp-≈
    ; qb-mono = qb-mono
    ; qb-α⇒ = qb-α⇒ ; qb-α⇐ = qb-α⇐ ; qb-λ⇒ = qb-λ⇒ ; qb-λ⇐ = qb-λ⇐
    ; qb-ρ⇒ = qb-ρ⇒ ; qb-ρ⇐ = qb-ρ⇐
    }
