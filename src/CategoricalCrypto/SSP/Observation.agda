{-# OPTIONS --safe --without-K #-}

-- What a closed protocol shows (`docs/uc-setup-ssp.md` §3.5).  Tests at `A`
-- are distinguishers `A ⇒ Ωᴵ` and closures `unitᴵ ⇒ A` are games, so `≈ℰ` is
-- perfect indistinguishability in every game context (brzuska2018 Def. 8 at
-- ε = 0).  The adversary's whole interaction is ONE activation of the closed
-- composite, and call trees are finite, so the readout needs no fuel.
--
-- Closeness compares BOTH verdict masses (`Protocol.Observe._≈adv[_]_`), so
-- `dead` is not identified with answering `false`; SSProve compares
-- `Pr[true]` only (ssprove2023 §3.2), which agrees when nothing aborts.  The
-- quantitative readout is primary and the qualitative one is its `qual₊`, as
-- in `UC.Model.Observation`.

open import Data.Bool.Base using (Bool)
open import Data.Maybe.Base using (nothing)
open import Data.Product.Base using (map₁; proj₂)
open import Data.Rational
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext using (∣x-x∣≡0)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Advantage
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category
open import CategoricalCrypto.UC.Core

module CategoricalCrypto.SSP.Observation where

private variable X : Set

evalC : Calls unitᴵ X → Dist⊥ X
evalC (ret x)       = return⊥ x
evalC (call () _ _)
evalC (coin μ k)    = μ >>=ᴹ λ b → evalC (k b)
evalC dead          = return-ℚ nothing

evalC-cong : {t t′ : Calls unitᴵ X} → t ≈ᶜ t′ → evalC t ≈Mℚ evalC t′
evalC-cong (ret refl)            = λ _ → refl
evalC-cong (call {c = ()} _)
evalC-cong (coin {μ} {k} {k′} h) = >>=ᴹ-congˡ μ (evalC ∘ k) (evalC ∘ k′) λ b → evalC-cong (h b)
evalC-cong dead                  = λ _ → refl

runᵖ : Protocol unitᴵ Ωᴵ → Dist⊥ Bool
runᵖ W = evalC (mapᶜ proj₂ (step W (init W) tt tt))

runᵖ-sim : {W W′ : Protocol unitᴵ Ωᴵ} → W ≲ᵖ W′ → runᵖ W ≈Mℚ runᵖ W′
runᵖ-sim {W} {W′} s = evalC-cong (≈ᶜ-trans (≈ᶜ-sym (mapᶜ-∘ proj₂ (map₁ (θ s)) t))
  (subst (λ s′ → mapᶜ proj₂ (mapᶜ (map₁ (θ s)) t) ≈ᶜ mapᶜ proj₂ (step W′ s′ tt tt))
         (θ-init s) (mapᶜ-cong proj₂ (θ-step s (init W) tt tt))))
  where t = step W (init W) tt tt

runᵖ-resp : {W W′ : Protocol unitᴵ Ωᴵ} → W ≈ᵖ W′ → runᵖ W ≈Mℚ runᵖ W′
runᵖ-resp = EqC.gfold ≈Mℚ-isEquivalence runᵖ runᵖ-sim

Approximation⊥ : Approximation (Dist⊥ Bool) ℚ-ordered 0ℓ
Approximation⊥ = record
  { _≈[_]_    = λ μ ε ν → (b : Bool) → advᵇ⊥ b μ ν ≤ ε
  ; ≈[]-refl  = λ {μ} b → ≤-reflexive (∣x-x∣≡0 (Prᵇ⊥ b μ))
  ; ≈[]-sym   = λ {μ} {ν} h b → ≤-trans (≤-reflexive (advᵇ⊥-sym b ν μ)) (h b)
  ; ≈[]-trans = λ {μ} {ν} {ρ} h k b → ≤-trans (advᵇ⊥-triangle b μ ν ρ) (+-mono-≤ (h b) (k b))
  ; ≈[]-mono  = λ le h b → ≤-trans (h b) le
  }

≈Mℚ⇒≈[0] : {μ ν : Dist⊥ Bool} → μ ≈Mℚ ν → Approximation._≈[_]_ Approximation⊥ μ 0ℚ ν
≈Mℚ⇒≈[0] {μ} e b = ≤-reflexive
  (trans (cong (λ z → ∣ Prᵇ⊥ b μ - z ∣) (sym (e (maybeℚ (indᵇ b))))) (∣x-x∣≡0 (Prᵇ⊥ b μ)))

qevaluationᵖ : QEvaluation Prot 0ℓ 0ℓ
qevaluationᵖ = record
  { J = unitᴵ ; Ω = Ωᴵ ; X = record { Carrier = Dist⊥ Bool ; approx = Approximation⊥ }
  ; eval₀ = record { to = runᵖ ; cong = λ {W} {W′} e → ≈Mℚ⇒≈[0] {runᵖ W} {runᵖ W′} (runᵖ-resp e) }
  }

evaluationᵖ : Evaluation Prot 0ℓ 0ℓ
evaluationᵖ = qual₊ ℚ-refinement qevaluationᵖ
