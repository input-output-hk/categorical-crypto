{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict `EdgeStepRˢ` step relation, factored ONCE.
--
-- Supplies the strict fired layer and the inductive graph of the strict
-- decoder's `edge-stepˢ`, per hypergraph:
--
--   * `fire-termˢ` — the strict fired layer, matching `edge-stepˢ`'s FIRE
--     branch on the nose (so `EdgeStepRˢ`'s `fireRˢ` index is DEFINITIONALLY
--     `proj₂ (edge-stepˢ s e)`).
--   * `EdgeStepRˢ` — the inductive graph of `edge-stepˢ`; matching its
--     `skipRˢ`/`fireRˢ` constructors refines the otherwise-stuck
--     `edge-stepˢ` redex (dodges green-slime).
--   * `edge-stepˢ-graph` — the function realises the relation.
--
-- Shared by `Interchange.SwapCore` (which re-exports it under its `(H)`
-- telescope) and `Interchange.StackEquiv`'s `EquivStep`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.EdgeStepRel
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_

open import Data.Fin using (Fin)
open import Data.List using (List; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

module EdgeStepView (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H

  -- `fire-termˢ` (`edge-stepˢ`'s FIRE branch, on the nose) comes from
  -- `StrictDecoder` above, so `fireRˢ`'s morphism index below is
  -- DEFINITIONALLY `proj₂ (edge-stepˢ s e)`.

  data EdgeStepRˢ (s : List (Fin H.nV)) (e : Fin H.nE)
       : (s' : List (Fin H.nV)) → HomS (map vl s) (map vl s') → Set where
    skipRˢ : extract-prefix (H.ein e) s ≡ nothing → EdgeStepRˢ s e s idˢ
    fireRˢ : ∀ (rest : List (Fin H.nV)) (perm : s Perm.↭ H.ein e ++ rest)
           → extract-prefix (H.ein e) s ≡ just (rest , perm)
           → EdgeStepRˢ s e (H.eout e ++ rest) (fire-termˢ e s rest perm)

  -- The two `process-edgesˢ` projections (shared abbreviations).
  pe-stackˢ : List (Fin H.nE) → List (Fin H.nV) → List (Fin H.nV)
  pe-stackˢ o s = proj₁ (process-edgesˢ o s)

  pe-termˢ : (o : List (Fin H.nE)) (s : List (Fin H.nV))
           → HomS (map vl s) (map vl (pe-stackˢ o s))
  pe-termˢ o s = proj₂ (process-edgesˢ o s)

  -- `process-edgesˢ` factors over an order split.  The ONE kernel lives with
  -- the decoder (`StrictDecoder.pe-stack-++ˢ`); this view exports it under
  -- the `pe-stackˢ`-spelled name its consumers use.
  ++-stackˢ = pe-stack-++ˢ

  -- The function realises the relation.
  edge-stepˢ-graph
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
    → EdgeStepRˢ s e (proj₁ (edge-stepˢ s e)) (proj₂ (edge-stepˢ s e))
  edge-stepˢ-graph s e with extract-prefix (H.ein e) s in eq
  ... | nothing            = skipRˢ eq
  ... | just (rest , perm) = fireRˢ rest perm eq
