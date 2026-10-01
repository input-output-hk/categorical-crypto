{-# OPTIONS --safe --without-K --guardedness #-}

-- The two enrichment data `UC.Audit` asks of a base, at the sealed model: a
-- graded subcategory for its rates and a mass for its readout.
--
-- `massᵒ` needs no coercion — it mentions only the readout's setoid, which
-- `evaluationᵒ` shares with `Evaluationᴹ` on the nose.  `gradingᵒ` does:
-- `GradedSubCat` is stated over a monoidal bundle, so `GradedSubCat _ 𝔾ᵒ _` is
-- not `GradedSubCat _ (𝒢ₚᴹ 0ℓ) _` outside the block where `𝔾ᵒ` reduces, so it
-- is transported along `UC.Model.Seal.sealᵒ` (see there for why not retyped).
--
-- Nothing here may open `StdUC`: `unfolding` the seal in a module that does is
-- the 12 GiB configuration `docs/stduc-supersession-plan.md` finding F5 records.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory

open import Data.Bool.Base
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational.LowerReal using (LowerReal)
open import Function.Bundles
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Grading
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.QueryBound using (QB)
open import CategoricalCrypto.UC.QueryBound.Object

module CategoricalCrypto.UC.Model.Enrichment where

private
  module Rates = SymmetricMonoidalCategory Rates
  module G = MonoidalCategory 𝔾ᵒ

gradingᵒ : GradedSubCat Rates.monoidalCategory 𝔾ᵒ (suc 0ℓ)
gradingᵒ = subst (λ M → GradedSubCat Rates.monoidalCategory M (suc 0ℓ)) (sym sealᵒ) gradingᴹ

open GradedSubCat gradingᵒ

opaque
  unfolding sealᵒ

  -- The certificates that grading accepts, at the machine-layer spelling
  -- (`UC.Seam.Budget`); under `unfolding sealᵒ` the transport above is `refl`.
  qbᵒ : {A B : Iface} {r : ℕ⁺} {f : Proc A B} → QB (value r) f → Pred r (procᵒ f)
  qbᵒ {A} {B} = qb-to-image A B

  -- …and at the graded spelling of the codomain, as the family layer's hom data
  -- asks for it.
  qb-gradedᵒ : {A P B : Iface} {r : ℕ⁺} {f : Proc A (P ⊗ᴵ B)}
             → QB (value r) f → Pred r (gradedᵒ f)
  qb-gradedᵒ {A} {P} {B} = qb-to-image A (P ⊗ᴵ B)

  -- An adversary machine filling a grade: its codomain is the bundle's own
  -- unit, which `UC.Machine.Dictionary.𝟭ᴵ` names on the machine side and the
  -- seal hides, so `procᵒ` does not serve and this is a coercion of its own.
  -- It sits here rather than beside the graded shapes it serves because its
  -- certificate does, and the two cannot be separated: `qbᵘ`'s body needs
  -- `procᵘ` transparent, which only the block declaring it is.
  procᵘ : {X : Iface} → Proc X 𝟭ᴵ → ifaceᵒ X G.⇒ G.unit
  procᵘ a = a

  qbᵘ : {X : Iface} {r : ℕ⁺} {a : Proc X 𝟭ᴵ} → QB (value r) a → Pred r (procᵘ a)
  qbᵘ {X} = qb-to-image X 𝟭ᴵ

imageᵒ : {A B : G.Obj} {r : ℕ⁺} {f : A G.⇒ B} → Pred r f → Image forget r f
imageᵒ {f = f} p = (f , p) , G.Equiv.refl

-- The reading `Evaluation` deliberately lacks: the `true`-mass, a lower real
-- presented by its approximants.  An audit bound is a probability of an event,
-- so the mass is one-sided, and its equality is the `true` half of `_≈ₚ[_]_`
-- in both directions, at every slack the agreement is asked at.
massᵒ : Func (Evaluation.S evaluationᵒ) LowerReal
massᵒ = record { to = λ d n → Pr≤ n d ; cong = λ h δ δ>0 → proj₁ (h δ δ>0) true , proj₂ (h δ δ>0) true }
