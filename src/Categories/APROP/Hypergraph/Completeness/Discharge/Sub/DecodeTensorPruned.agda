{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- The PRUNED `⊗` shape residual `decodeP-⊗-shape`, PROVEN by mirroring
-- `Sub.DecodeTensorShape.decode-⊗-shape-inner` with the UNPRUNED decoder
-- `decode` / translation `⟪_⟫` replaced by the PRUNED `decodeP` / `⟪_⟫ₚ`:
--
--     decodeP (f ⊗₁ g)
--       ≈Term to (unflatten-++-≅ …) ∘ (decodeP f ⊗₁ decodeP g) ∘ from (…)
--
-- TENSOR IS NOT PRUNED: `⟪ f ⊗₁ g ⟫ₚ = hTensor ⟪f⟫ₚ ⟪g⟫ₚ` uses the SAME
-- `hTensor` as the unpruned side, and `decode-attempt-LinearP (f ⊗₁ g) =
-- decode-attempt-hTensor ⟪f⟫ₚ ⟪g⟫ₚ …` uses the SAME `decode-attempt-hTensor`
-- function the unpruned proof uses.  Consequently the ENTIRE tensor-block
-- machinery of `DecodeTensorShape` — `EmbedData`, `BlockFactor`,
-- `BlockTensor` — is generic in the two sub-hypergraphs and is REUSED here
-- verbatim, instantiated at `⟪f⟫ₚ` / `⟪g⟫ₚ`.  Only the top-level binding of
-- the sub-decoders (`G = ⟪f⟫ₚ`, `lin-G = ⟪⟫-LinearP f`, the
-- `decode-attempt-extract` extraction on `decode-attempt-LinearP`, and the
-- `decodeP`-folding `Gpart`/`Kpart`) differs.
--
-- This is the structural fact recorded in `ProcessEdgesTermShape`'s
-- `decodeP-⊗-shape` doc: the pruned `⊗` shape is the `decodeP` mirror of
-- `decode-⊗-shape-inner`.  Since the latter is PROVEN postulate-free over
-- `objUIP` + `K`, so is this — NO `nf-bracket` / `swap-atom-aligned` kernel
-- is consumed (the kernel is the interchange side's, not the decode-`⊗`
-- side's; the block reordering here is the proven `N`+`M` `BlockNFBraid`
-- framing inside `BlockFactor`).
--
-- Parameterised by `objUIP` + `K : FaithfulnessResidual`.  No postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorPruned
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.APROP.Hypergraph.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)

-- Pruned totality.
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP; ⟪⟫-LinearP)

-- The generic decoder-agnostic ⊗ assembly (proved once in `DecodeTensorShape`).
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorShape sig
  using (module DecodeShapeGeneric)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst₂)

private
  -- The pruned decoder `decodeP`.
  decodeP : ∀ {A B} (f : HomTerm A B)
          → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  decodeP {A} {B} f =
    subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL f)) (cong unflatten (⟪⟫ₚ-codL f))
           (proj₁ (decode-attempt-LinearP f))

--------------------------------------------------------------------------------
-- ## The FINAL pruned ⊗ assembly — `decodeP-⊗-shape`.
--
-- Verbatim mirror of `DecodeTensorShape.decode-⊗-shape-inner`, with
-- `decode`/`decode-attempt-Linear`/`Lin.⟪⟫-Linear`/`⟪_⟫`/`⟪⟫-{dom,cod}L`
-- → `decodeP`/`decode-attempt-LinearP`/`⟪⟫-LinearP`/`⟪_⟫ₚ`/`⟪⟫ₚ-{dom,cod}L`.

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
