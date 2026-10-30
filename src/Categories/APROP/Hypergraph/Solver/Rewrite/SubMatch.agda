{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Sub-hypergraph matching (TensorRocq §4.2, DPO rewriting).
-- The raw embedding is certified downstream by the final isomorphism gate.
-- Vertices untouched by edge matching remain unbound, so totalisation fails.
-- In particular a wire-only LHS with vertices is unsupported here; the
-- empty zero-wire graph has no vertices to bind and is not excluded.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Rewrite.SubMatch (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.Evaluate
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Solver.Match.PBij
open import Categories.APROP.Hypergraph.Solver.Match.Search sig

open import Data.Fin
open import Data.List.Base
open import Data.Maybe.Base using (Maybe; just; _>>=_)
open import Data.Product using (_,_)

module _ {X : Set} {Gen : List X → List X → Set} where

  infix 4 _↪ᴴ_

  record _↪ᴴ_ (L S : Hypergraph Gen) : Set where
    private
      module L = Hypergraph L
      module S = Hypergraph S
    field φ : Fin L.nV → Fin S.nV
          ψ⁻¹ : Fin S.nE → Maybe (Fin L.nE)

    boundary-dom : List (Fin S.nV)
    boundary-dom = map φ L.dom

    boundary-cod : List (Fin S.nV)
    boundary-cod = map φ L.cod

verifySub : (L S : Hypergraph FlatGen)
          → PBij (Hypergraph.nV L) (Hypergraph.nV S)
          → PBij (Hypergraph.nE L) (Hypergraph.nE S)
          → Maybe (L ↪ᴴ S)
verifySub L S φB ψB =
  totalise (forward φB) >>= λ φ → just record { φ = φ ; ψ⁻¹ = backward ψB }

-- Enumerate embeddings so a non-convex first match cannot mask later ones.

subMatchAll : (L S : Hypergraph FlatGen) → List (L ↪ᴴ S)
subMatchAll L S =
  forceCounts (λ L → forceCounts (λ S →
    mapMaybe (λ { (φB , ψB) → verifySub L S φB ψB })
             (searchAll L S emptyBij emptyBij)) S) L

subMatch : (L S : Hypergraph FlatGen) → Maybe (L ↪ᴴ S)
subMatch L S = head (subMatchAll L S)
