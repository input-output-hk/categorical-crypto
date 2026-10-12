{-# OPTIONS --safe --guardedness #-}

-- Public consumers of the relational and certified computational
-- interpretations, conditional E₀ soundness, and independently proved
-- protocol-size-dependent nonce-guessing errors.
module CategoricalCrypto.Symbolic.InterpretationTests where

open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; z≤n)
open import Data.Nat.Positive using (1⁺)
open import Data.Product using (_,_)
open import Data.Rational as ℚ using (ℚ)
open import Data.Sum.Base using (inj₂)
open import Data.Unit using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Role Σ₀ as R
open import CategoricalCrypto.UC.Approximate using (Negligible)
open import CategoricalCrypto.UC.QueryBound using (Certified; qbᵢ-upward)
open import CategoricalCrypto.UC.Model.Family using (Obj^ω; _⇒^ω_; _⊛ω_; schedOf; ucSetupᴺ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.Machine.UC as Iso
import CategoricalCrypto.Machines.Base as Base
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Symbolic.Computational Σ₀ as Comp
import CategoricalCrypto.Symbolic.Computational.Obstruction Σ₀ as Obstruction
import CategoricalCrypto.Symbolic.Fine Σ₀ as Fine
import CategoricalCrypto.Symbolic.Machine Σ₀ E₀ as Rel
import CategoricalCrypto.Symbolic.Setup Σ₀ E₀ as Setup
import CategoricalCrypto.Symbolic.Soundness Σ₀ E₀ as Sound
import CategoricalCrypto.Symbolic.Soundness.Deterministic as Det
import CategoricalCrypto.Symbolic.Soundness.ErrorTests as Errors

private module MC = Core (Base.𝒱ₚ 0ℓ)

open Terms Σ₀
open Run E₀
open Fine using (ObjTerm; Var)

wire : ObjTerm
wire = Var (port tt tt)

relational-consumer : UCSetupMorphism Fine.Sym≅.StdSetup Iso.StdSetup
relational-consumer = Rel.sym≅→iso

-- Unlike a backwards bounce, forwarding a domain activation upwards is
-- admissible at potential zero. The reverse direction spends the budget
-- supplied by the activation from above.
forward : Role wire wire
forward = record
  { n = 1 ; Γ = λ _ → [] ; start = zero ; fresh = refl
  ; react = λ where
      zero (here refl) _ → emit zero [] (there (here refl)) (var (here refl))
      zero (there (here refl)) _ → emit zero [] (here refl) (var (here refl)) }

module CertifiedForward (sch : Comp.Scheme) where
  module ByteRun = Comp.Execution sch
  module Source = Comp.CertifiedSource sch
  module F = StrongMonoidalFunctor Source.Fᶜ

  forward-certified : (η : ℕ) → Certified 1 (ByteRun.runᶜ η forward)
  forward-certified η = qbᵢ-upward _ (returnₚ (ByteRun.initᶜ forward)) (MC.step (ByteRun.runᶜ η forward))
    (λ { (ByteRun.configᶜ zero []) b → returnₚ (inj₂ ((ByteRun.configᶜ zero [] , z≤n) , b)) })
    (λ { (ByteRun.configᶜ zero []) _ → >>=ₚ-identityˡ _ _ ⟨≈⟩ ≈sym (>>=ₚ-identityˡ _ _) })

  generator : Source.Generator wire wire
  generator = Source.certified tt tt forward 1⁺ forward-certified

  compiled : F.₀ wire ⇒^ω F.₀ wire
  compiled = F.₁ (Source.Src.var generator)

  carried-rate : (η : ℕ) → schedOf compiled η ≡ 1⁺
  carried-rate _ = refl

  computational-consumer : UCSetupMorphism Source.Sym≅ᶜ.StdSetup ucSetupᴺ
  computational-consumer = Source.fine→comp

  backward-obstruction : (b : Comp.Scheme.Bits sch) (c : ℕ)
    → Certified c (ByteRun.runᶜ 0 (Obstruction.backwards tt)) → ⊥
  backward-obstruction = Obstruction.no-backwards-certificate sch tt

-- E₀ identifies x with π₁(pair(x,x)); the spare control point satisfies only
-- the ground-guard predicate, not the absorbing terminal specialization.
echo : Role (Var void) wire
echo = record
  { n = 2 ; Γ = λ _ → [] ; start = zero ; fresh = refl
  ; react = λ where
      zero (here refl) _ → emit zero [] (here refl) (var (here refl))
      zero (there ()) _
      (suc zero) (here refl) _ → emit (suc zero) [] (here refl) (app (cst 0) [])
      (suc zero) (there ()) _ }

echo-π₁ : Reactions echo
echo-π₁ zero (here refl) _ = emit zero [] (here refl) (π₁ ⟪ var (here refl) , var (here refl) ⟫)
echo-π₁ zero (there ()) _
echo-π₁ (suc zero) (here refl) _ = emit (suc zero) [] (here refl) (app (cst 0) [])
echo-π₁ (suc zero) (there ()) _

projected : Role (Var void) wire
projected = record echo { react = echo-π₁ }

echo-ground-guarded : GroundGuarded echo
echo-ground-guarded = record
  { ground-control = suc zero
  ; ground-at-control = λ { (here refl) _ → ground-jump tt ; (there ()) _ }
  ; ground-guards = λ { zero (here refl) _ → emit ; zero (there ()) _
                ; (suc zero) (here refl) _ → emit ; (suc zero) (there ()) _ } }

projected-ground-guarded : GroundGuarded projected
projected-ground-guarded = record
  { ground-control = suc zero
  ; ground-at-control = λ { (here refl) _ → ground-jump tt ; (there ()) _ }
  ; ground-guards = λ { zero (here refl) _ → emit ; zero (there ()) _
                ; (suc zero) (here refl) _ → emit ; (suc zero) (there ()) _ } }

normalized-kernel : Fine.var (tt , tt , echo) Setup.Sym.≈ℰ Fine.var (tt , tt , projected)
normalized-kernel = Setup.emit-≈E echo λ where
  zero (here refl) _ → emit (λ _ → []) (λ _ → refl)
  zero (there ()) _
  (suc zero) (here refl) _ → emit (λ _ → []) (λ _ → refl)
  (suc zero) (there ()) _

echo-system projected-system : Fine.HomTerm (Var void) (wire Fine.⊗₀ Fine.unit)
echo-system = Fine.ρ⇐ Fine.∘ Fine.var (tt , tt , echo)
projected-system = Fine.ρ⇐ Fine.∘ Fine.var (tt , tt , projected)

normalized-UC : echo-system Setup.Sym.≤UC projected-system
normalized-UC = Setup.Sym.≈ᵁ⇒≤UC (Setup.Sym.bridge Setup.grade-stable
  (Setup.Sym.≈ℰ-cong-post Fine.ρ⇐ normalized-kernel))

module ConditionalConsumer (sch : Comp.Scheme)
  (Feasible : ∀ {A B : Obj^ω} → A ⇒^ω B → Set) where
  module C = Sound.FeasibleComparison sch Feasible

  module _ (hyp : C.Backtranslation) where
    module D = C.Derived hyp
    private module G = MonoidalCategory 𝔾ᵒ

    normalized-output : (W : Obj^ω)
      → C._≈ᶠ_ {W ⊛ω C.Objᶜ (Var void)} {W ⊛ω C.Objᶜ wire}
          (λ η → G.id {W η} G.⊗₁ C.interpret (Fine.var (tt , tt , echo)) η)
          (λ η → G.id {W η} G.⊗₁ C.interpret (Fine.var (tt , tt , projected)) η)
    normalized-output = D.sound⁺ echo-ground-guarded projected-ground-guarded normalized-kernel

    normalized-dummy : D.DummyWitness echo-system projected-system
    normalized-dummy = D.sound-≤UC normalized-UC (tt , echo-ground-guarded) (tt , projected-ground-guarded) (tt , tt)

nonce-guessing-comparison : (η : ℕ)
  → Errors.observe 1 η ≈ₚ[ Errors.error 1 η ℚ.+ Errors.error 2 η ] Errors.observe 2 η
nonce-guessing-comparison = Errors.comparison-at 1 2

uniform-nonce-error-obstruction : (shared : ℕ → Dₚ Bool) (ε : ℕ → ℚ) → Negligible ε
  → ((N η : ℕ) → Errors.observe N η ≈ₚ[ ε η ] shared η) → ⊥
uniform-nonce-error-obstruction = Errors.no-uniform-factorization

-- The exact labeled trace lemma also has an actual symbolic-role consumer.
-- It says nothing about applied-π static-equivalent labels.
module ExactEcho (κ : ℕ) where
  module SymbolicRun = R.Run E₀

  echo-determinate : ∀ {q r}
    → Det.TraceEqual (SymbolicRun.step κ echo) (SymbolicRun.step κ echo) q r
    → Det.Bisimulation (SymbolicRun.step κ echo) (SymbolicRun.step κ echo) q r
  echo-determinate = Det.trace⇒bisim (SymbolicRun.step κ echo) (SymbolicRun.step κ echo)
