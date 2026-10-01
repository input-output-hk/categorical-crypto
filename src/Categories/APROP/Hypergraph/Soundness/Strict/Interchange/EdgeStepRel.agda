{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict `EdgeStepRˢ` step relation, factored ONCE.
--
-- Supplies the inductive graph of the strict decoder's `edge-stepˢ`, per
-- hypergraph (`fire-termˢ`, the strict fired layer whose shape `fireRˢ`'s
-- morphism index matches DEFINITIONALLY, is READ from `StrictDecoder`, not
-- exported here):
--
--   * `EdgeStepRˢ` — the inductive graph of `edge-stepˢ`; matching its
--     `skipRˢ`/`fireRˢ` constructors refines the otherwise-stuck
--     `edge-stepˢ` redex (dodges green-slime).
--   * `edge-stepˢ-graph` — the function realises the relation.
--   * `pe-stackˢ`/`pe-termˢ` — the two `process-edgesˢ` projection
--     abbreviations every consumer of this view reads.
--
-- Shared by `Interchange.SwapCore` (which re-exports it under its `(H)`
-- telescope) and `Interchange.StackEquiv`'s `EquivStep`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.EdgeStepRel
  (sig : APROPSignature)
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig

open import Data.Fin using (Fin)
open import Data.Maybe using (just; nothing)

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

  -- The function realises the relation.
  edge-stepˢ-graph
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
    → EdgeStepRˢ s e (proj₁ (edge-stepˢ s e)) (proj₂ (edge-stepˢ s e))
  edge-stepˢ-graph s e with extract-prefix (H.ein e) s in eq
  ... | nothing            = skipRˢ eq
  ... | just (rest , perm) = fireRˢ rest perm eq
