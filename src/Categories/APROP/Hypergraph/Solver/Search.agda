{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Backtracking depth-first search (TensorRocq §4.2).
--
-- Picks edges in natural order, tries each candidate extension via
-- `matchEdge`, recurses, and backtracks on failure.  Terminates via a
-- `fuel` argument (bounded by `H.nE × J.nE`).  Emits the first complete
-- match, not a best one.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Search (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Solver.PBij
  using (PBij; forward)
open import Categories.APROP.Hypergraph.Solver.Match sig-dec
  using (matchEdge; VertexBij; EdgeBij)

open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_)

--------------------------------------------------------------------------------
-- The first unmatched H-edge (`forward ψ e ≡ nothing`), or `nothing` when
-- all edges are matched (the search exit condition).

firstUnmatched
  : ∀ {nEH nEJ}
  → PBij nEH nEJ
  → Maybe (Fin nEH)
firstUnmatched {nEH} ψ = go nEH (λ i → i)
  where
    go : (count : ℕ) → (Fin count → Fin nEH) → Maybe (Fin nEH)
    go ℕ.zero    _   = nothing
    go (ℕ.suc n) inj with forward ψ (inj zero)
    ... | nothing = just (inj zero)
    ... | just _  = go n (λ i → inj (suc i))

module _
         (H J : Hypergraph FlatGen) where

  private
    nVH = Hypergraph.nV H
    nVJ = Hypergraph.nV J
    nEH = Hypergraph.nE H
    nEJ = Hypergraph.nE J

  searchIso
    : (fuel : ℕ)
    → VertexBij H J → EdgeBij H J
    → Maybe (VertexBij H J × EdgeBij H J)
  -- Succeed if all edges are already matched, even at zero fuel.
  searchIso ℕ.zero    φ ψ with firstUnmatched ψ
  ... | nothing = just (φ , ψ)
  ... | just _  = nothing
  searchIso (ℕ.suc k) φ ψ with firstUnmatched ψ
  ... | nothing = just (φ , ψ)
  ... | just e  = tryAll (matchEdge H J φ ψ e)
    where
      tryAll : List (VertexBij H J × EdgeBij H J)
             → Maybe (VertexBij H J × EdgeBij H J)
      tryAll []              = nothing
      tryAll ((φ' , ψ') ∷ xs) with searchIso k φ' ψ'
      ... | just res = just res
      ... | nothing  = tryAll xs

  -- Fuel bounded by the search-tree upper bound.
  searchIso-default : VertexBij H J → EdgeBij H J
                    → Maybe (VertexBij H J × EdgeBij H J)
  searchIso-default = searchIso (nEH * nEJ)
