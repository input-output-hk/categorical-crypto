{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The pruned `⊗` shape residual `decodeP-⊗-shape`:
--
--     decodeP (f ⊗₁ g)
--       ≈Term to (unflatten-++-≅ …) ∘ (decodeP f ⊗₁ decodeP g) ∘ from (…)
--
-- Tensor is NOT pruned (`⟪ f ⊗₁ g ⟫ₚ = hTensor ⟪f⟫ₚ ⟪g⟫ₚ`, the same
-- `hTensor` as the unpruned side), so the entire tensor-block machinery of
-- `DecodeTensorShape` (`DecodeShapeGeneric`) is generic in the two
-- sub-hypergraphs and is reused here, instantiated at `⟪f⟫ₚ` / `⟪g⟫ₚ`.
-- Parameterised by `objUIP` + `Kf : FaithfulnessResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.DecodeTensorPruned
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.APROP.Hypergraph.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)

open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP; ⟪⟫-LinearP)

-- The generic decoder-agnostic ⊗ assembly.
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.DecodeTensorShape sig _≟X_
  using (module DecodeShapeGeneric)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst₂)

private
  decodeP : ∀ {A B} (f : HomTerm A B)
          → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  decodeP {A} {B} f =
    subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL f)) (cong unflatten (⟪⟫ₚ-codL f))
           (proj₁ (decode-attempt-LinearP f))

--------------------------------------------------------------------------------
-- `decodeP-⊗-shape`: the pruned ⊗ assembly, via `DecodeShapeGeneric.goal`.

module _
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  where

  decodeP-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodeP (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decodeP f ⊗₁ decodeP g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
  decodeP-⊗-shape {A} {B} {C₀} {D} f g =
    DecodeShapeGeneric.goal objUIP Kf {A} {B} {C₀} {D} ⟪ f ⟫ₚ ⟪ g ⟫ₚ
      (decodeP f) (decodeP g) (decodeP (f ⊗₁ g))
      (⟪⟫-LinearP f) (⟪⟫-LinearP g) (⟪⟫-LinearP (f ⊗₁ g))
      (decode-attempt-LinearP f) (decode-attempt-LinearP g) (decode-attempt-LinearP (f ⊗₁ g))
      (⟪⟫ₚ-domL f) (⟪⟫ₚ-codL f) (⟪⟫ₚ-domL g) (⟪⟫ₚ-codL g)
      (⟪⟫ₚ-domL (f ⊗₁ g)) (⟪⟫ₚ-codL (f ⊗₁ g))
      refl refl refl
