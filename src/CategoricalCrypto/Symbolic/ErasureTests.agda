{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Symbolic.ErasureTests where

open import Data.Bool.Base
import Data.Bool.Properties as Bool
open import Data.Fin.Base using (zero)
open import Data.List.Base using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; z≤n)
open import Data.Nat.Positive
open import Data.Product
open import Data.Sum.Base using (inj₂)
open import Data.Unit
open import Function.Bundles
open import Level using (0ℓ; lift; lower)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Role Σ₀
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.Machines.Base as Base
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Symbolic.Computational Σ₀ as Comp
import CategoricalCrypto.Symbolic.Erasure Σ₀ as Erase
import CategoricalCrypto.Symbolic.Fine Σ₀ as Fine

scheme : Comp.Scheme
scheme = record
  { Bits = Bool ; impl = λ _ _ _ → true ; nonce = λ _ → returnₚ false
  ; _≟ᵇ_ = Bool._≟_ ; tag = λ _ b → b }

module E = Erase.Erasure scheme
module Source = Comp.CertifiedSource scheme
module S = Source.Src
module ByteRun = Comp.Execution scheme
module Arrow = UCSetupMorphism E.certified→fine
private module MC = Core (Base.𝒱ₚ 0ℓ)

verdict-wire : Fine.ObjTerm
verdict-wire = Fine.Var verdict

verdict-forward : Role verdict-wire verdict-wire
verdict-forward = record
  { n = 1 ; Γ = λ _ → [] ; start = zero ; fresh = refl
  ; react = λ where
      zero (here refl) b → emit zero [] (there (here refl)) b
      zero (there (here refl)) _ → emit zero [] (here refl) tt }

verdict-activation : ByteRun.stepᶜ 0 verdict-forward (ByteRun.initᶜ verdict-forward)
    (here refl ByteRun.↦ᶜ true)
  ≡ returnₚ (ByteRun.configᶜ zero [] , there (here refl) ByteRun.↦ᶜ true)
verdict-activation = refl

-- The rate-one forwarding proof follows InterpretationTests.CertifiedForward,
-- specialized to the verdict alphabet so it can also close a syntactic test.
verdict-certified : (η : ℕ) → Certified 1 (ByteRun.runᶜ η verdict-forward)
verdict-certified η = qbᵢ-upward _ (returnₚ (ByteRun.initᶜ verdict-forward))
  (MC.step (ByteRun.runᶜ η verdict-forward))
  (λ { (ByteRun.configᶜ zero []) b → returnₚ (inj₂ ((ByteRun.configᶜ zero [] , z≤n) , b)) })
  (λ { (ByteRun.configᶜ zero []) _ → >>=ₚ-identityˡ _ _ ⟨≈⟩ ≈sym (>>=ₚ-identityˡ _ _) })

verdict-generator : Source.Generator verdict-wire verdict-wire
verdict-generator = Source.certified tt tt verdict-forward 1⁺ verdict-certified

forward-erases : Arrow.F.₁ (S.var verdict-generator) ≡ Fine.var (tt , tt , verdict-forward)
forward-erases = refl

composition-erases : Arrow.F.₁ (S.var verdict-generator S.∘ S.var verdict-generator)
  ≡ Fine.var (tt , tt , verdict-forward) Fine.∘ Fine.var (tt , tt , verdict-forward)
composition-erases = refl

tensor-erases : Arrow.F.₁ (S.var verdict-generator S.⊗₁ S.var verdict-generator)
  ≡ Fine.var (tt , tt , verdict-forward) Fine.⊗₁ Fine.var (tt , tt , verdict-forward)
tensor-erases = refl

consumer : Source.Test verdict-wire
consumer = S.unit , S.var verdict-generator S.∘ S.λ⇒

ordinary-consumer : Fine.Test verdict-wire
ordinary-consumer = Fine.unit , Fine.var (tt , tt , verdict-forward) Fine.∘ Fine.λ⇒

consumer-erases : lower (Arrow.ν.η verdict-wire ⟨$⟩ lift consumer) ≡ ordinary-consumer
consumer-erases = refl

pull-erases : lower (Arrow.ν.η verdict-wire ⟨$⟩
    lift (Source.pull (S.var verdict-generator) consumer))
  ≡ (Fine.unit , (Fine.var (tt , tt , verdict-forward) Fine.∘ Fine.λ⇒)
      Fine.∘ (Fine.id Fine.⊗₁ Fine.var (tt , tt , verdict-forward)))
pull-erases = refl

pull-natural : Fine.SameTerm
  (lower (Arrow.ν.η verdict-wire ⟨$⟩ lift (Source.pull (S.var verdict-generator) consumer)))
  (Fine.pullᵗ (Arrow.F.₁ (S.var verdict-generator)) ordinary-consumer)
pull-natural = lower (Arrow.ν.commute (S.var verdict-generator) {lift consumer})

consumer-congruence : Fine.SameTerm
  (lower (Arrow.ν.η verdict-wire ⟨$⟩
    lift (S.unit , S.id S.∘ (S.var verdict-generator S.∘ S.λ⇒))))
  ordinary-consumer
consumer-congruence = lower (Func.cong (Arrow.ν.η verdict-wire)
  {x = lift (S.unit , S.id S.∘ (S.var verdict-generator S.∘ S.λ⇒))}
  {y = lift consumer} (lift (Source.same S.idˡ)))
