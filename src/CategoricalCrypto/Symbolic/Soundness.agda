{-# OPTIONS --safe --without-K --guardedness #-}

-- A shared symbolic experiment with protocol-dependent approximation errors
-- suffices for feasible indistinguishability. `Backtranslation` remains an
-- operational prerequisite, not an IND-CPA/INT-CTXT reduction. See
-- docs/uc-setup-symbolic.md §4.3 for its quantifier order and eligibility limits.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Soundness (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal
open import Categories.LocallyGraded.SubCategory
open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.Product
open import Data.Unit
open import Function.Bundles
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Symbolic.Computational.Run 𝔖
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖 using (GroundGuarded; verdict)
open import CategoricalCrypto.Symbolic.Semantics 𝔖 E using (eval)
open import CategoricalCrypto.Symbolic.Setup 𝔖 E
open import CategoricalCrypto.Symbolic.Soundness.Errors
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family hiding (Closure; Test; observe)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

private
  module G = MonoidalCategory 𝔾ᵒ
  module Fm = MonoidalCategory Famᴹ
  variable A B X Y : ObjTerm

GroundGuardedC : HomTerm A B → Set
GroundGuardedC (var (_ , _ , p)) = GroundGuarded p
GroundGuardedC (g ∘ f) = GroundGuardedC g × GroundGuardedC f
GroundGuardedC (f ⊗₁ g) = GroundGuardedC f × GroundGuardedC g
GroundGuardedC _ = ⊤

maybe-ext : {a b : Maybe Bool} → (∀ x → a ≡ just x ⇔ b ≡ just x) → a ≡ b
maybe-ext {nothing} {nothing} _ = refl
maybe-ext {nothing} {just b} h with Equivalence.from (h b) refl
... | ()
maybe-ext {just a} h = sym (Equivalence.to (h a) refl)

-- A neutral bundle keeps record positivity from normalizing the family grading.
module FeasibleContexts {o ℓ e} (M : MonoidalCategory o ℓ e)
  (J Ω : MonoidalCategory.Obj M)
  (Feasible : ∀ {A B : MonoidalCategory.Obj M} → MonoidalCategory._⇒_ M A B → Set) where
  private module C = MonoidalCategory M
  record Context (A B : C.Obj) : Set (o ⊔ ℓ) where
    field
      ancilla : C.Obj
      test : (ancilla C.⊗₀ B) C.⇒ Ω
      closure : J C.⇒ (ancilla C.⊗₀ A)
      feasible-test : Feasible {A = ancilla C.⊗₀ B} {B = Ω} test
      feasible-closure : Feasible {A = J} {B = ancilla C.⊗₀ A} closure

module OperationalPrerequisite {ℓ} (Requirement : Set ℓ) where
  record Backtranslation : Set (Level.suc ℓ) where
    field extract : Requirement

module DummyEvidence {X Y : ObjTerm} (Agreement : HomTerm Y X → Set₁) where
  record DummyWitness : Set₁ where
    field
      simulator : HomTerm Y X
      agreement : Agreement simulator

module FeasibleComparison (sch : Scheme)
  (Feasible : ∀ {A B : Obj^ω} → A ⇒^ω B → Set) where
  private module ByteRun = Execution sch
  open GradedSubCat gradingᵒ

  Objᶜ : ObjTerm → Obj^ω
  Objᶜ A η = StrongMonoidalFunctor.F₀ (ByteRun.Fᶜ η) A

  interpret : HomTerm A B → (η : ℕ) → Objᶜ A η G.⇒ Objᶜ B η
  interpret f η = StrongMonoidalFunctor.F₁ (ByteRun.Fᶜ η) f

  Raw : Obj^ω → Obj^ω → Set₁
  Raw A B = (η : ℕ) → A η G.⇒ B η

  open FeasibleContexts Famᴹ (Δ 𝟘ᵒ) (Δ Ωᵒ) Feasible public

  observeᶠ : ∀ {A B} → Context A B → Raw A B → ℕ → Dₚ Bool
  observeᶠ c f η = Obs ((⌊ hom (Context.test c) η ⌋ G.∘ (G.id {Context.ancilla c η} G.⊗₁ f η))
    G.∘ ⌊ hom (Context.closure c) η ⌋)

  infix 4 _≈ᶠ_
  _≈ᶠ_ : ∀ {A B} → Raw A B → Raw A B → Set₁
  _≈ᶠ_ {A} {B} f g = (c : Context A B) → observeᶠ c f ∼ᴺ observeᶠ c g

  -- The sampling distribution and symbolic contexts are chosen BEFORE an
  -- honest system. Divergence is `nothing`; both verdict masses are preserved.
  record Extraction {A B} (W : Obj^ω) (c : Context (W ⊛ω Objᶜ A) (W ⊛ω Objᶜ B)) : Set₁ where
    field
      Sample : ℕ → Set
      samples : (η : ℕ) → Dₚ (Sample η)
      symbolic-ancilla : (η : ℕ) → Sample η → ObjTerm
      symbolic-test : (η : ℕ) (a : Sample η) → HomTerm (symbolic-ancilla η a ⊗₀ B) (Var verdict)
      symbolic-closure : (η : ℕ) (a : Sample η) → Closure (symbolic-ancilla η a ⊗₀ A)
      result : HomTerm A B → (η : ℕ) → Sample η → Maybe Bool
      classifies : (f : HomTerm A B) → GroundGuardedC f → (η : ℕ) (a : Sample η) (b : Bool)
        → eval ((symbolic-test η a ∘ (id ⊗₁ f)) ∘ symbolic-closure η a) b ⇔ result f η a ≡ just b
      approximation : ProtocolError (HomTerm A B) GroundGuardedC
        (λ f η → observeᶠ c (λ η → G.id {W η} G.⊗₁ interpret f η) η)
        (λ f η → samples η >>=ₚ λ a → detₚ (result f η a))

  open OperationalPrerequisite
    (∀ {A B} (W : Obj^ω) (c : Context (W ⊛ω Objᶜ A) (W ⊛ω Objᶜ B)) → Extraction {A} {B} W c) public

  module Derived (hyp : Backtranslation) where
    open Backtranslation hyp

    sound⁺ : {f g : HomTerm A B} → GroundGuardedC f → GroundGuardedC g → f Sym.≈ℰ g
           → (W : Obj^ω) → _≈ᶠ_ {W ⊛ω Objᶜ A} {W ⊛ω Objᶜ B}
             (λ η → G.id {W η} G.⊗₁ interpret f η) (λ η → G.id {W η} G.⊗₁ interpret g η)
    sound⁺ {A = A} {B = B} {f = f} {g} sf sg e W c =
      Comparison.compare approximation f g sf sg mixtures-agree
      where
      open Extraction (extract {A} {B} W c)

      results-agree : (η : ℕ) (a : Sample η) → result f η a ≡ result g η a
      results-agree η a = maybe-ext λ b → mk⇔
        (λ h → Equivalence.to (classifies g sg η a b)
          (Equivalence.to (same⁻¹ (lower (Sym.KE.run∼ e {lift (symbolic-ancilla η a , symbolic-test η a)})) (symbolic-closure η a) b)
            (Equivalence.from (classifies f sf η a b) h)))
        (λ h → Equivalence.to (classifies f sf η a b)
          (Equivalence.from (same⁻¹ (lower (Sym.KE.run∼ e {lift (symbolic-ancilla η a , symbolic-test η a)})) (symbolic-closure η a) b)
            (Equivalence.from (classifies g sg η a b) h)))

      mixtures-agree : (η : ℕ)
        → (samples η >>=ₚ λ a → detₚ (result f η a)) ≈ₚ (samples η >>=ₚ λ a → detₚ (result g η a))
      mixtures-agree η = bindᶠ λ a → ≡⇒≈ₚ (cong detₚ (results-agree η a))

    -- An explicit symbolic dummy simulator is retained. This is NOT the
    -- target's adversary-quantified canonical UC order: feasibility has no
    -- closure law that would absorb every computational adversary into a test.
    module _ (f : HomTerm A (X ⊗₀ B)) (g : HomTerm A (Y ⊗₀ B)) where
      open DummyEvidence {X} {Y} (λ simulator → (W : Obj^ω)
        → _≈ᶠ_ {W ⊛ω Objᶜ A} {W ⊛ω Objᶜ (X ⊗₀ B)}
            (λ η → G.id {W η} G.⊗₁ interpret f η)
            (λ η → G.id {W η} G.⊗₁ ((interpret simulator η G.⊗₁ G.id {Objᶜ B η}) G.∘ interpret g η))) public

    sound-≤UC : {f : HomTerm A (X ⊗₀ B)} {g : HomTerm A (Y ⊗₀ B)}
              → (le : f Sym.≤UC g) → GroundGuardedC f → GroundGuardedC g
              → GroundGuardedC (proj₁ (Sym.≤UC⇒dummy le)) → DummyWitness f g
    sound-≤UC {f = f} {g} le sf sg ss = record
      { simulator = proj₁ (Sym.≤UC⇒dummy le)
      ; agreement = sound⁺ sf ((ss , tt) , sg) (Sym.≈ᵁ⇒≈ℰ (proj₂ (Sym.≤UC⇒dummy le))) }
