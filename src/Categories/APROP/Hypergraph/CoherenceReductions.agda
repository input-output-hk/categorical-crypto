{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- The original CoherenceReductions.agda packaged subst₂-wrapped peel
-- helpers (`hCompose-hId-R-iso-substed`, `reduce-via-hId-R`,
-- `reduce-via-hId-L`).  Under de-indexing, the subst₂s on
-- `Hypergraph FlatGen` are gone, so these helpers need reformulating.
-- For now we stub the API as postulates so the soundness chain
-- (Triangle, Pentagon, AlphaCommSound, ρ/σ-nat) can build.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.CoherenceReductions (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; flatten; hId)
open import Categories.APROP.Hypergraph.PrunedCompose sig using (hComposeP)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  -- Right-side and left-side hId peels.  In the indexed world these
  -- went through `subst₂ (Hypergraph FlatGen) refl eq …`; in the
  -- de-indexed world the boundary equation lives as a runtime arg to
  -- `hComposeP`.  Reformulating these constructively is mechanical
  -- follow-up.
  reduce-via-hId-R
    : ∀ (A : ObjTerm) (G : Hypergraph FlatGen)
        (bdy : codL G ≡ flatten A)
        {T : Hypergraph FlatGen}
        (T-bdy : codL T ≡ flatten A)
    → T ≅ᴴ G

  reduce-via-hId-L
    : ∀ (A : ObjTerm) (G : Hypergraph FlatGen)
        (bdy : domL G ≡ flatten A)
    → Unique (Hypergraph.dom G)
    → {T : Hypergraph FlatGen}
    → T ≅ᴴ G

  hCompose-hId-R-iso-substed
    : ∀ (A : ObjTerm) (G : Hypergraph FlatGen)
        (bdy : codL G ≡ flatten A)
        (full-bdy : codL G ≡ domL (hId A))
    → hComposeP G (hId A) full-bdy ≅ᴴ G
