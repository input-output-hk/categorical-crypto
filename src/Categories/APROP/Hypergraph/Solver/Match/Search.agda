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

module Categories.APROP.Hypergraph.Solver.Match.Search (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Solver.Match.PBij using (PBij; forward)
open import Categories.APROP.Hypergraph.Solver.Match.Match sig-dec
  using (matchEdge; VertexBij; EdgeBij)

open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; head)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_)

--------------------------------------------------------------------------------
-- The first unmatched H-edge (`forward ψ e ≡ nothing`), or `nothing` when
-- all edges are matched (the search exit condition).

firstUnmatched : ∀ {nEH nEJ} → PBij nEH nEJ → Maybe (Fin nEH)
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
    nEH = Hypergraph.nE H
    nEJ = Hypergraph.nE J

  -- Enumerate ALL complete matches, in DFS order.  Consumers whose acceptance
  -- criterion is stricter than the search's (e.g. the rewrite carve, which
  -- additionally requires the matched occurrence to be convex) retry down this
  -- list; `searchIso` is its `head`.  Succeeds if all edges are already
  -- matched, even at zero fuel.
  searchAll
    : (fuel : ℕ)
    → VertexBij H J → EdgeBij H J
    → List (VertexBij H J × EdgeBij H J)
  searchAll ℕ.zero    φ ψ with firstUnmatched ψ
  ... | nothing = (φ , ψ) ∷ []
  ... | just _  = []
  searchAll (ℕ.suc k) φ ψ with firstUnmatched ψ
  ... | nothing = (φ , ψ) ∷ []
  ... | just e  = tryAll (matchEdge H J φ ψ e)
    where
      tryAll : List (VertexBij H J × EdgeBij H J) → List (VertexBij H J × EdgeBij H J)
      tryAll []               = []
      tryAll ((φ' , ψ') ∷ xs) = searchAll k φ' ψ' ++ tryAll xs

  -- `_++_` is lazy in its second argument, so taking the `head` forces exactly
  -- the failing subtrees a first-match-only recursion would have forced.
  searchIso
    : (fuel : ℕ)
    → VertexBij H J → EdgeBij H J
    → Maybe (VertexBij H J × EdgeBij H J)
  searchIso fuel φ ψ = head (searchAll fuel φ ψ)

  -- Fuel bounded by the search-tree upper bound.
  searchAll-default : VertexBij H J → EdgeBij H J → List (VertexBij H J × EdgeBij H J)
  searchAll-default = searchAll (nEH * nEJ)

  searchIso-default : VertexBij H J → EdgeBij H J → Maybe (VertexBij H J × EdgeBij H J)
  searchIso-default = searchIso (nEH * nEJ)
