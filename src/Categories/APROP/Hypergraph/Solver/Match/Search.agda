{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Edge matching + backtracking depth-first search (TensorRocq §4.2).
--
-- `matchEdge` enumerates, for an unmatched H-edge `e` and partial bijections
-- `(φ, ψ)`, the J-edges whose shape is compatible with `e` together with the
-- extended `(φ', ψ')`.  `searchAll` is the back-tracker that consumes those
-- lists: it picks edges in natural order, tries each candidate extension,
-- recurses, and backtracks on failure.  Terminates via a `fuel` argument
-- (bounded by `H.nE × J.nE`); `searchIso` emits the first complete match,
-- not a best one.
--
-- Propagation is implicit: pairing up `H.ein e [i] ↔ J.ein e' [i]` adds new
-- vertex constraints to `φ`, pruning future choices via `extend-bij`'s
-- conflict check.
--
-- Candidates are culled by arity/atom-list shape AND by edge label: the
-- shape check produces exactly the atom-list equalities needed to transport
-- the J-label to the H-index, where `flat-match-subst` (the same conservative
-- comparison the final verification uses) decides label equality.  Without
-- the label cull, a signature with many same-shaped generators lets the
-- search lock onto a label-mismatched (but connectivity-consistent) match,
-- which the verification stage then rejects — and since verification
-- failures do not re-enter the search, the whole query fails spuriously.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Match.Search (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Solver.Match.PBij
  using (PBij; forward; extend-bij; pairUp)
open import Categories.APROP.Hypergraph.Solver.Match.Verify sig-dec using (flat-match-subst)

open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; head; map; mapMaybe)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Decidable list equality at the atom alphabet `X`.  `tryEdge` uses it to
-- check arity/atom-list shape, keeping the `yes`-branch proofs to feed
-- `flat-match-subst`.

_≟L_ : (xs ys : List X) → _
_≟L_ = ≡-dec _≟X_

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
    nVH = Hypergraph.nV H
    nVJ = Hypergraph.nV J
    nEH = Hypergraph.nE H
    nEJ = Hypergraph.nE J

  VertexBij : Set
  VertexBij = PBij nVH nVJ

  EdgeBij : Set
  EdgeBij = PBij nEH nEJ

  ------------------------------------------------------------------------
  -- Try to match edge `e` against edge `e'`: pair up their source lists,
  -- then their target lists; finally pair `e` with `e'` in the edge PBij.
  -- Returns `just (φ', ψ')` on success, or `nothing` on any conflict.

  tryEdge : VertexBij → EdgeBij → Fin nEH → Fin nEJ → Maybe (VertexBij × EdgeBij)
  tryEdge φ ψ e e'
    with map (Hypergraph.vlab H) (Hypergraph.ein  H e)
           ≟L map (Hypergraph.vlab J) (Hypergraph.ein  J e')
       | map (Hypergraph.vlab H) (Hypergraph.eout H e)
           ≟L map (Hypergraph.vlab J) (Hypergraph.eout J e')
  ... | no _  | _     = nothing
  ... | _     | no _  = nothing
  ... | yes p | yes q
    -- Shape agrees; transport J's label to H's index and compare.
    with flat-match-subst (sym p) (sym q) (Hypergraph.elab J e')
                          (Hypergraph.elab H e)
  ... | nothing = nothing
  ... | just _  =
        pairUp φ  (Hypergraph.ein  H e) (Hypergraph.ein  J e') >>= λ φ'  →
        pairUp φ' (Hypergraph.eout H e) (Hypergraph.eout J e') >>= λ φ'' →
        extend-bij ψ e e'                                      >>= λ ψ'  →
        just (φ'' , ψ')

  -- Enumerate all matches of `e` against J-edges.
  matchEdge : VertexBij → EdgeBij → Fin nEH → List (VertexBij × EdgeBij)
  matchEdge φ ψ e = mapMaybe (tryEdge φ ψ e) (range nEJ)

  ------------------------------------------------------------------------
  -- Enumerate ALL complete matches, in DFS order.  Consumers whose acceptance
  -- criterion is stricter than the search's (e.g. the rewrite carve, which
  -- additionally requires the matched occurrence to be convex) retry down this
  -- list; `searchIso` is its `head`.  Succeeds if all edges are already
  -- matched, even at zero fuel.
  searchAll : (fuel : ℕ) → VertexBij → EdgeBij → List (VertexBij × EdgeBij)
  searchAll ℕ.zero    φ ψ with firstUnmatched ψ
  ... | nothing = (φ , ψ) ∷ []
  ... | just _  = []
  searchAll (ℕ.suc k) φ ψ with firstUnmatched ψ
  ... | nothing = (φ , ψ) ∷ []
  ... | just e  = tryAll (matchEdge φ ψ e)
    where
      tryAll : List (VertexBij × EdgeBij) → List (VertexBij × EdgeBij)
      tryAll []               = []
      tryAll ((φ' , ψ') ∷ xs) = searchAll k φ' ψ' ++ tryAll xs

  -- `_++_` is lazy in its second argument, so taking the `head` forces exactly
  -- the failing subtrees a first-match-only recursion would have forced.
  searchIso : (fuel : ℕ) → VertexBij → EdgeBij → Maybe (VertexBij × EdgeBij)
  searchIso fuel φ ψ = head (searchAll fuel φ ψ)

  -- Fuel bounded by the search-tree upper bound.
  searchAll-default : VertexBij → EdgeBij → List (VertexBij × EdgeBij)
  searchAll-default = searchAll (nEH * nEJ)

  searchIso-default : VertexBij → EdgeBij → Maybe (VertexBij × EdgeBij)
  searchIso-default = searchIso (nEH * nEJ)
