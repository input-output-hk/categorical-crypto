{-# OPTIONS --safe --without-K #-}

-- Permutation morphisms between `Unique` stacks form a thin groupoid:
-- `rigid-≈̂` identifies derivations, while relabelling is functorial.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc
  (sig : APROPSignature)
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)

import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes sig as DSh
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig

import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm sig as BSC
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermRelabel sig as PVV

open import Data.Fin using (Fin)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ)

module Kit (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H

  open Restrict (Fin H.nV) vl

  open DSh.Scr (Fin H.nV) H.vlab using (bswap)

  ⟦absorbˡ⟧
    : ∀ {xs ys zs : List (Fin H.nV)} {p : xs Perm.↭ ys} (eq : ys ≡ zs)
    → permuteˢ (Perm.trans p (Perm.↭-reflexive eq)) ≈̂ permuteˢ p
  ⟦absorbˡ⟧ refl = ≈ˢ⇒≈̂ idˡ

  ⟦absorbʳ⟧
    : ∀ {xs ys zs : List (Fin H.nV)} (eq : xs ≡ ys) {p : ys Perm.↭ zs}
    → permuteˢ (Perm.trans (Perm.↭-reflexive eq) p) ≈̂ permuteˢ p
  ⟦absorbʳ⟧ refl = ≈ˢ⇒≈̂ idʳ

  ⟦bswap⟧ᵛ
    : ∀ (L R Rl : List (Fin H.nV))
    → permuteᵛ (PermProp.++⁺ʳ Rl (bswap L R)) ≈ᵛ σᵛ L R ⊗ᵛ idᵛ {Rl}
  ⟦bswap⟧ᵛ = BSC.swap-block (Fin H.nV) H.vlab

  rigid-≈̂
    : ∀ {xs ys : List (Fin H.nV)} → Unique ys
    → (p q : xs Perm.↭ ys) → permuteˢ p ≈̂ permuteˢ q
  rigid-≈̂ u p q = ≈ˢ⇒≈̂ (rigidˢ u p q)

  -- The source derivation is unrelated to `D`: rigidity identifies it with
  -- the φ-lift, after which the endpoint reindexings are absorbed.
  module _ {nK : ℕ} (vlK : Fin nK → X) (φ : Fin nK → Fin H.nV)
           (φ-lab : ∀ i → vl (φ i) ≡ vlK i) where

    ⟦relabel-rigid⟧
      : ∀ {xs ys : List (Fin nK)} {as bs : List (Fin H.nV)}
          (u : Unique bs) (e₁ : as ≡ map φ xs) (e₂ : map φ ys ≡ bs)
          (D : as Perm.↭ bs) (p : xs Perm.↭ ys)
      → permuteˢ D ≈̂ Perm′.permuteˢ (Fin nK) vlK p
    ⟦relabel-rigid⟧ {xs} {ys} {as} {bs} u e₁ e₂ D p =
      ≈̂-trans (rigid-≈̂ u D φ-lift)
      (≈̂-trans (⟦absorbʳ⟧ e₁)
      (≈̂-trans (⟦absorbˡ⟧ e₂)
               (PVV.pvv-≈̂ φ vl vlK φ-lab p)))
      where
        φ-lift : as Perm.↭ bs
        φ-lift = Perm.trans (Perm.↭-reflexive e₁)
                   (Perm.trans (PermProp.map⁺ φ p) (Perm.↭-reflexive e₂))
