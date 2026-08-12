{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- From output-only concrete security to UC realization.
--
-- A `Realization` is the shape a hand-written cryptographic theorem has: a
-- protocol machine on top of a resource is indistinguishable from an ideal
-- machine, with an explicit bound on the advantage of any ≤ q-query
-- distinguisher.  Nothing in it mentions an adversary interface — that is what
-- OUTPUT-ONLY means, and it is what a theorem like `Examples.MerkleDamgard`
-- proves.
--
-- This module lifts a family of them into the UC metatheory, in the three steps
-- the theory prescribes:
--
--   1. INGESTION — read the concrete `≈adv[ bound ]` statement as ℰᵗᵛ's
--      `_≈ℰ[_]_`, whose distinguisher is an ancilla CONTEXT rather than a `Dgr`.
--      This is the one step with content, and it is exactly what `Reflects`
--      buys: a budgeted context is realized by a single adaptive distinguisher.
--   2. ABSORPTION — a vanishing bound collapses `≈ℰ[ bound ]` to the kernel
--      equality `≈ℰ` of the environment presheaf (`VanishingTV.absorb`).
--   3. THE PAYOFF — at the DEGENERATE grade `𝟙^ω` (no adversary interface, so
--      the simulator is the identity and the ideal bridge is the graded unit
--      law) the dummy-adversary theorem turns that into `≤UC`.
--
-- The degenerate grade is honest but weak: it lifts an output-only theorem into
-- the UC formulation at the price of the no-adversary-interface case.  A real
-- indifferentiability simulator replaces exactly three definitions of `Payoff`
-- (`Ideal`, `simulator`, `ideal-bridge`) at a non-degenerate grade.
--------------------------------------------------------------------------------

open import CategoricalCrypto.Machine.Probabilistic using (Machines)
import CategoricalCrypto.Machine.Probabilistic.Model as Machine

module CategoricalCrypto.OutputOnly (PM : Machines) (MM : Machine.MachineModel PM) where

open import Data.Bool.Base using (Bool)
open import Data.Nat using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Level using (0ℓ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category.Monoidal using (MonoidalCategory)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import CategoricalCrypto.Channel.Core using (Channel; I)
import CategoricalCrypto.FamilyCategory
open import CategoricalCrypto.Interaction
import CategoricalCrypto.StandardTV
import CategoricalCrypto.VanishingTV
open import ProbabilisticLogic.Distribution.RationalDist using (_≈Mℚ_)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Pr₁⊥; Pr₁⊥-cong)
open import ProbabilisticLogic.Distribution.RationalDist.Partial using (Dist⊥)

open Machine PM
open MachineModel MM
open MonoidalUtilities.Shorthands mono

------------------------------------------------------------------------
-- The artifact

-- A protocol realizing an ideal machine from a resource, with a concrete bound
-- against adaptive query-counting distinguishers and NO adversary interface.
record Realization : Set (suc 0ℓ) where
  field
    Res-If Ideal-If : Channel
    resource : PMachine I Res-If
    protocol : PMachine Res-If Ideal-If
    ideal    : PMachine I Ideal-If
    bound    : ℕ → ℚ
    secure   : ideal ≈adv[ bound ] (protocol ⊚ resource)

------------------------------------------------------------------------
-- The family, and the context that plays the distinguisher's role

module Ingest (art : ℕ → Realization) where

  module A (j : ℕ) = Realization (art j)
  module FC = CategoricalCrypto.FamilyCategory axioms
  module VT = CategoricalCrypto.VanishingTV axioms
  module ST = CategoricalCrypto.StandardTV axioms hom-triv
  module Cω = MonoidalCategory FC.𝒞^ω

  ResIf IdealIf : FC.Obj^ω
  ResIf   = A.Res-If
  IdealIf = A.Ideal-If

  -- The protocol domain is closed on the input side; the codomain carries the
  -- degenerate adversary grade, so `Bo` is `T₀ 𝟙^ω IdealIf` under the
  -- curried-tensor triple.
  Ao Bo : FC.Obj^ω
  Ao = Cω.unit Cω.⊗₀ Cω.unit
  Bo = FC.𝟙^ω Cω.⊗₀ IdealIf

  private
    _⊗ω_ : FC.Obj^ω → FC.Obj^ω → FC.Obj^ω
    (Y ⊗ω B) j = Y j M.⊗₀ B j

  -- The unitor conjugation of a subroutine-free machine into the degenerate grade.
  conj : ∀ {C} → PMachine I C → PMachine (M.unit M.⊗₀ M.unit) (M.unit M.⊗₀ C)
  conj u = λ⇐ ⊚ (fromI u ⊚ λ⇒)

  private
    subst-⊚ : ∀ {U B C} (p : I ≡ U) (g : PMachine B C) (f : PMachine I B)
            → subst (λ V → PMachine V C) p (g ⊚ f) ≡ g ⊚ subst (λ V → PMachine V B) p f
    subst-⊚ refl g f = refl

    -- The composite of the two conjugated legs IS the conjugated composite.
    conj-∘ : ∀ {B C} (g : PMachine B C) (f : PMachine I B)
           → ((λ⇐ ⊚ g) ⊚ (fromI f ⊚ λ⇒)) ≈ₚ conj (g ⊚ f)
    conj-∘ g f = M.Equiv.trans M.assoc (M.∘-resp-≈ʳ inner)
      where
      inner : (g ⊚ (fromI f ⊚ λ⇒)) ≈ₚ (fromI (g ⊚ f) ⊚ λ⇒)
      inner = M.Equiv.trans M.sym-assoc
                (M.Equiv.reflexive (cong (λ z → z ⊚ λ⇒) (sym (subst-⊚ (sym unit≡I) g f))))

  -- The closed run of a machine plugged into a budgeted ancilla context.  This
  -- is `VanishingTV.run` of the context composite, spelled level by level.
  ctxRun : (Y : FC.Obj^ω) → FC.Test^ω (Y ⊗ω Bo) → FC.Closure^ω (Y ⊗ω Ao)
         → ∀ j → PMachine (Ao j) (Bo j) → Dist⊥ Bool
  ctxRun Y E m j f = obs (proj₁ E j ⊚ ((M.id M.⊗₁ f) ⊚ proj₁ m j))

  private
    ctxRun-cong : ∀ Y E m j {f g} → f ≈ₚ g → ctxRun Y E m j f ≈Mℚ ctxRun Y E m j g
    ctxRun-cong Y E m j e =
      obs-cong (M.∘-resp-≈ʳ (M.∘-resp-≈ˡ (M.⊗.F-resp-≈ (M.Equiv.refl , e))))

  -- Every budgeted ancilla context around a subroutine-free machine is realized
  -- by ONE adaptive distinguisher, whose query count is bounded by the context's
  -- polynomial budget.  This is what `QB` MEANS at the machine layer, and the
  -- reason `MachineAxioms.QB` can stay an abstract instrument: it is the
  -- obligation that lets a `∀ d`-quantified concrete theorem be read as an
  -- ℰᵗᵛ-statement.  Not provable while `⟦_⟧`/`_⊚_` carry no laws.
  Reflects : Set (suc 0ℓ)
  Reflects = ∀ (Y : FC.Obj^ω) (E : FC.Test^ω (Y ⊗ω Bo)) (m : FC.Closure^ω (Y ⊗ω Ao))
           → Σ[ p ∈ (ℕ → ℕ) ] Poly p ×
             (∀ j → Σ[ d ∈ Dgr (Channel.outType (IdealIf j)) (Channel.inType (IdealIf j)) ]
                      asks≤ (p j) d ×
                      (∀ (u : PMachine I (IdealIf j)) →
                         ctxRun Y E m j (conj u) ≈Mℚ run⊥ ⟦ u ⟧cl d))

  -- The three legs as morphism FAMILIES; their polynomial query budgets are
  -- hypotheses of `Payoff`, since discharging them needs a concrete `QB`.
  resFam : ∀ j → PMachine (Ao j) (ResIf j)
  resFam j = fromI (A.resource j) ⊚ λ⇒

  protoFam : ∀ j → PMachine (ResIf j) (Bo j)
  protoFam j = λ⇐ ⊚ A.protocol j

  idealFam : ∀ j → PMachine (Ao j) (Bo j)
  idealFam j = conj (A.ideal j)

  ------------------------------------------------------------------------
  -- The payoff

  module Payoff
    (qbRes   : FC.PolyQB resFam)
    (qbProto : FC.PolyQB protoFam)
    (qbIdeal : FC.PolyQB idealFam)
    (reflects : Reflects)
    (van : VT.VanishingBound A.bound)
    where

    Resource : FC._⇒^ω_ Ao ResIf
    Resource = resFam , qbRes

    Protocol : FC._⇒^ω_ ResIf Bo
    Protocol = protoFam , qbProto

    -- Ascribed at the graded type, since that is where `sub`'s grade and object
    -- implicits are read off in `ideal-bridge`.
    Ideal : Ao FC.⇒^ω ST.T₀ FC.𝟙^ω IdealIf
    Ideal = idealFam , qbIdeal

    -- The real protocol is the composite itself — a bare machine morphism at
    -- grade 𝟙^ω, since `T₀ 𝟙^ω ·` reduces to `𝟙^ω ⊗ ·` under the curried-tensor
    -- triple.
    real : Ao FC.⇒^ω ST.T₀ FC.𝟙^ω IdealIf
    real = Protocol Cω.∘ Resource

    private
      advEq : ∀ Y E m j d → (∀ u → ctxRun Y E m j (conj u) ≈Mℚ run⊥ ⟦ u ⟧cl d)
            → adv⊥ (ctxRun Y E m j (proj₁ Ideal j)) (ctxRun Y E m j (proj₁ real j))
            ≡ adv ⟦ A.ideal j ⟧cl ⟦ A.protocol j ⊚ A.resource j ⟧cl d
      -- Every implicit here is pinned by an ascribed statement: `_≈Mℚ_` mentions
      -- only `entries`, so an inferred distribution strands `mass-1` as a meta.
      advEq Y E m j d eq = cong₂ (λ a b → ∣ a -ℚ b ∣ℚ) idealSide realSide
        where
        idealSide : Pr₁⊥ (ctxRun Y E m j (proj₁ Ideal j)) ≡ Pr₁⊥ (run⊥ ⟦ A.ideal j ⟧cl d)
        idealSide = Pr₁⊥-cong (ctxRun Y E m j (conj (A.ideal j)))
                              (run⊥ ⟦ A.ideal j ⟧cl d) (eq (A.ideal j))

        realSide : Pr₁⊥ (ctxRun Y E m j (proj₁ real j))
                 ≡ Pr₁⊥ (run⊥ ⟦ A.protocol j ⊚ A.resource j ⟧cl d)
        realSide = trans (Pr₁⊥-cong (ctxRun Y E m j (protoFam j ⊚ resFam j))
                                    (ctxRun Y E m j (conj (A.protocol j ⊚ A.resource j)))
                                    (ctxRun-cong Y E m j (conj-∘ (A.protocol j) (A.resource j))))
                         (Pr₁⊥-cong (ctxRun Y E m j (conj (A.protocol j ⊚ A.resource j)))
                                    (run⊥ ⟦ A.protocol j ⊚ A.resource j ⟧cl d)
                                    (eq (A.protocol j ⊚ A.resource j)))

    -- STEP 1: the concrete theorem, read against ℰᵗᵛ's ancilla contexts.
    ingest : Ideal VT.≈ℰ[ A.bound ] real
    ingest Y E m =
      let (p , Pp , h) = reflects Y E m
      in p , Pp , λ j → let (d , le , eq) = h j in
         subst (λ z → z ≤ℚ A.bound j (p j)) (sym (advEq Y E m j d eq))
               (A.secure j (p j) d le)

    -- STEP 3: at the degenerate grade the simulator is the identity and the
    -- ideal bridge is the graded unit law.
    simulator : FC.𝟙^ω FC.⇒^ω FC.𝟙^ω
    simulator = Cω.id

    ideal-bridge : (ST.sub simulator Cω.∘ Ideal) ST.≈ℰ Ideal
    ideal-bridge = ST.≈C⇒≈ℰ (ST.sub-identityˡ Ideal)

    -- STEP 2 + the bridge.  `ε` must be pinned: it occurs applied (`ε n (p n)`)
    -- inside `≈ℰ[_]`, so inferring it strands a non-pattern constraint.
    emulate : real ST.≈ℰ (ST.sub simulator Cω.∘ Ideal)
    emulate = begin
        real                          ≈⟨ VT.absorb {ε = A.bound} ingest van ⟨
        Ideal                         ≈⟨ ideal-bridge ⟨
        ST.sub simulator Cω.∘ Ideal   ∎
      where open SetoidR (ST.≈ℰ-setoid Ao Bo)

    realizes : real ST.≤UC Ideal
    realizes = ST.dummy-complete (simulator , ST.bridge ST.grade-stableᵗᵛ emulate)
