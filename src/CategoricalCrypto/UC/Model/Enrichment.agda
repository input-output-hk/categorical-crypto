{-# OPTIONS --safe --without-K --guardedness #-}

-- The rate grading at the sealed model, and the seal coercions that certify
-- into it.
--
-- `GradedSubCat` is stated over a monoidal bundle, so `GradedSubCat _ 𝔾ᵒ _` is
-- not `GradedSubCat _ (𝒢ₚᴹ 0ℓ) _` outside the block where `𝔾ᵒ` reduces, so
-- `gradingᵒ` is transported along `UC.Model.Seal.sealᵒ` (see there for why not
-- retyped).
--
-- Nothing here may open `StdUC`: `unfolding` the seal in a module that does
-- needs 12 GiB (measured).

open import Categories.Category.Instance.Rates
open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Positive
open import Data.Product.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Grading
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.QueryBound using (QB)
open import CategoricalCrypto.UC.QueryBound.Object

module CategoricalCrypto.UC.Model.Enrichment where

gradingᵒ : GradedSubCat Rates.monoidalCategory 𝔾ᵒ (suc 0ℓ)
gradingᵒ = subst (λ M → GradedSubCat Rates.monoidalCategory M (suc 0ℓ)) (sym sealᵒ) gradingᴹ

open GradedSubCat gradingᵒ

opaque
  unfolding sealᵒ

  -- The certificates that grading accepts, at the machine-layer spelling
  -- (`UC.QueryBound.QB`); under `unfolding sealᵒ` the transport above is `refl`.
  qbᵒ : {A B : Iface} {r : ℕ⁺} {f : Proc A B} → QB (value r) f → Pred r (procᵒ f)
  qbᵒ {A} {B} = qb-to-image A B

  -- …and at the graded spelling of the codomain, as the family layer's hom data
  -- asks for it.
  qb-gradedᵒ : {A P B : Iface} {r : ℕ⁺} {f : Proc A (P ⊗ᴵ B)}
             → QB (value r) f → Pred r (gradedᵒ f)
  qb-gradedᵒ {A} {P} {B} = qb-to-image A (P ⊗ᴵ B)
