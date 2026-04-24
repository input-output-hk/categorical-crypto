{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 4a.4: Backtracking search (TensorRocq §4.2).
--
-- Depth-first search over `matchEdge` results. Picks edges in natural
-- order (`Fin.zero` first), tries each candidate extension, recurses.
-- On exhaustion without a complete match, backtracks to the next
-- candidate. Terminates via a `fuel` argument (set by callers to
-- `H.nE × J.nE`, a bound on the search-tree size).
--
-- No heuristics. The plan (§4a.4) chooses simplicity over speed —
-- we emit the *first* complete match, not the best one.
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
-- Find the first unmatched H-edge (the first `e : Fin nEH` with
-- `forward ψ e ≡ nothing`). Returns `nothing` when all edges are
-- matched — the exit condition of the search.

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

--------------------------------------------------------------------------------
-- Backtracking depth-first search. Iterates over `matchEdge` results,
-- recurses with `fuel - 1`. On fuel exhaustion, returns `nothing`.

module _ {As Bs : List X}
         (H J : Hypergraph FlatGen As Bs) where

  private
    nVH = Hypergraph.nV H
    nVJ = Hypergraph.nV J
    nEH = Hypergraph.nE H
    nEJ = Hypergraph.nE J

  searchIso
    : (fuel : ℕ)
    → VertexBij H J → EdgeBij H J
    → Maybe (VertexBij H J × EdgeBij H J)
  -- Even when fuel is exhausted, succeed if all edges are already
  -- matched — `firstUnmatched` is the only termination signal that
  -- matters.
  searchIso ℕ.zero    φ ψ with firstUnmatched ψ
  ... | nothing = just (φ , ψ)
  ... | just _  = nothing
  searchIso (ℕ.suc k) φ ψ with firstUnmatched ψ
  ... | nothing = just (φ , ψ)          -- all edges matched — done
  ... | just e  = tryAll (matchEdge H J φ ψ e)
    where
      tryAll : List (VertexBij H J × EdgeBij H J)
             → Maybe (VertexBij H J × EdgeBij H J)
      tryAll []              = nothing
      tryAll ((φ' , ψ') ∷ xs) with searchIso k φ' ψ'
      ... | just res = just res
      ... | nothing  = tryAll xs

  -- Convenience: bound fuel by the search-tree upper bound.
  searchIso-default : VertexBij H J → EdgeBij H J
                    → Maybe (VertexBij H J × EdgeBij H J)
  searchIso-default = searchIso (nEH * nEJ)
