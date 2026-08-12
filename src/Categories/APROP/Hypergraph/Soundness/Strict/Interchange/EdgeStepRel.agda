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
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

module EdgeStepView (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H

  -- The framed box of an edge `e` on the residual `rest`, with the input
  -- locating permute `perm`.  This is EXACTLY `proj₂ (edge-stepˢ s e)` on
  -- the FIRE branch (`extract-prefix (H.ein e) s ≡ just (rest , perm)`).
  fire-termˢ
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
    → s Perm.↭ H.ein e ++ rest
    → HomS (map vl s) (map vl (H.eout e ++ rest))
  fire-termˢ e s rest perm =
    castˢ refl (sym (map-++ vl (H.eout e) rest))
      ((genˢ (H.elab e) ⊗ˢ idˢ {map vl rest})
        ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ perm))

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

  -- `process-edgesˢ` factors over an order split: the run recurses on the
  -- prefix, so this is a direct induction (no `stacks-agree` detour).
  ++-stackˢ
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → pe-stackˢ (ps ++ rest) s ≡ pe-stackˢ rest (pe-stackˢ ps s)
  ++-stackˢ []       rest s = refl
  ++-stackˢ (e ∷ ps) rest s = ++-stackˢ ps rest (proj₁ (edge-stepˢ s e))

  -- The function realises the relation.
  edge-stepˢ-graph
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
    → EdgeStepRˢ s e (proj₁ (edge-stepˢ s e)) (proj₂ (edge-stepˢ s e))
  edge-stepˢ-graph s e with extract-prefix (H.ein e) s in eq
  ... | nothing            = skipRˢ eq
  ... | just (rest , perm) = fireRˢ rest perm eq
