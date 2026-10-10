{-# OPTIONS --safe --without-K --guardedness #-}

-- PM[wb] (`docs/uc-setup-ssp.md` §4.2): the well-bracketed tests on `𝒲ᴹ`
-- (`ℰᵂ`), `𝒲ᴹ` quotiented by their two-sided ancilla kernel
-- (`Standard2.UKernel`), and the tests descended to the quotient.
--
--     ℰᵂ(A) = 𝒲(A , Ωᴵ) / ≋    t ≋ t′ ⟺ ∀ m : 𝒲(unitᴵ , A). Obsᵂ (t ∘ m) ∼ᵃ Obsᵂ (t′ ∘ m)
--
-- `Obsᵂ` is the model's readout `Obs` through two wires respelling SSP's
-- closed and verdict interfaces as the model's, so a well-bracketed test and
-- closure are observed exactly as protocol-rewrite observes them.

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor
open import Categories.Functor.Presheaf

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UC.Bracket.Monoidal
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Machine hiding (Ωᴵ)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.Iface as Flat
import CategoricalCrypto.Standard2 as Std2
import CategoricalCrypto.Standard2.UKernel as UKernel

module CategoricalCrypto.UC.Bracket.Setup where

private
  module G = MonoidalCategory 𝔾ᵒ

------------------------------------------------------------------------
-- Well-bracketed tests

υʷ : Proc Flat.unitᴵ (flat unitᴵ)
υʷ = wireᴹ (λ ()) λ { (() , _) }

ωʷ : Proc (flat Ωᴵ) (Bool Flat.⇿ ⊤)
ωʷ = wireᴹ proj₂ λ _ → tt , tt

Obsᵂ : MonoidalCategory.U 𝒲ᴹ [ unitᴵ , Ωᴵ ] → Dₚ Bool
Obsᵂ (h , _) = Obs (procᵒ ωʷ G.∘ h G.∘ procᵒ υʷ)

qevaluationᵂ : QEvaluation (MonoidalCategory.U 𝒲ᴹ) 0ℓ 0ℓ
qevaluationᵂ = record
  { J = unitᴵ ; Ω = Ωᴵ ; X = spaceᴹ
  ; eval₀ = record { to = Obsᵂ ; cong = λ e → ≈ₚ⇒≈ₚ[0] (obs-resp (G.∘-resp-≈ʳ (G.∘-resp-≈ˡ e))) }
  }

evaluationᵂ : Evaluation (MonoidalCategory.U 𝒲ᴹ) 0ℓ 0ℓ
evaluationᵂ = qual₊ ℚ-refinement qevaluationᵂ

ℰᵂ : Presheaf (MonoidalCategory.U 𝒲ᴹ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᵂ = Observable.ℰᴼ (Evaluation.observable evaluationᵂ)

-- 𝒲[ℰᵂ]: well-bracketed machines under well-bracketed tests.
module 𝒲ᵂ = Std2.StdUC 𝒲ᴹ ℰᵂ

------------------------------------------------------------------------
-- PM[wb]

private module K = UKernel 𝒲ᴹ ℰᵂ

-- `K.uKernel` at one spelling of its level: its own, `suc 0ℓ ⊔ suc 0ℓ ⊔ suc 0ℓ`,
-- is not syntactically `suc 0ℓ`, and two spellings of one quotient are compared
-- by eta-expanding both records down to their law proofs (`q` exhausts 3 GiB).
uKernelᵂ : MonoidalCongruence 𝒲ᴹ (suc 0ℓ)
uKernelᵂ = K.uKernel

PM[wb]ᴹ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
PM[wb]ᴹ = quotient 𝒲ᴹ uKernelᵂ

-- Every use binds its implicit arguments: left to inference, they are solved by
-- unfolding `K._∼_` down to `ℰᵂ`'s tests (`q` past 90 s).
∼⇒≋ᵂ : {A B : Iface} {f g : MonoidalCategory.U 𝒲ᴹ [ A , B ]} → f K.∼ g
     → Setoids (suc 0ℓ) (suc 0ℓ) [ Functor.₁ ℰᵂ f ≈ Functor.₁ ℰᵂ g ]
∼⇒≋ᵂ {A} {B} {f} {g} e {t} = 𝒲ᵂ.KE.run∼ (K.∼⇒≈ℰ {A} {B} {f} {g} e) {t}

ℰ[wb] : Presheaf (MonoidalCategory.U PM[wb]ᴹ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰ[wb] = descend 𝒲ᴹ uKernelᵂ ℰᵂ λ {A} {B} {f} {g} → ∼⇒≋ᵂ {A} {B} {f} {g}

open Std2.StdUC PM[wb]ᴹ ℰ[wb] public

q : UCSetupMorphism 𝒲ᵂ.StdSetup StdSetup
q = StdUCMorphism 𝒲ᴹ PM[wb]ᴹ ℰᵂ ℰ[wb] (quotientF 𝒲ᴹ uKernelᵂ)
      (descendᵛ 𝒲ᴹ uKernelᵂ ℰᵂ λ {A} {B} {f} {g} → ∼⇒≋ᵂ {A} {B} {f} {g})
