{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Backtracking edge matching (TensorRocq §4.2).
--
-- Cull labels before committing to a connectivity match: final verification
-- failures do not re-enter the search, so a wrong same-shaped generator could
-- otherwise mask a valid match.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Match.Search (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Solver.Match.PBij
open import Categories.APROP.Hypergraph.Solver.Match.Verify sig

open import Data.Bool.Base
open import Data.Fin
open import Data.List.Base
open import Data.List.Properties
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; _>>=_)
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open APROPSignature sig

_≟L_ : (xs ys : List X) → _
_≟L_ = ≡-dec _≟X_

firstUnmatched : ∀ {nEH nEJ} → PBij nEH nEJ → Maybe (Fin nEH)
firstUnmatched {nEH} ψ = findᵇ (λ e → not (is-just (forward ψ e))) (allFin nEH)

module _ (H J : Hypergraph FlatGen) where

  private
    nVH = Hypergraph.nV H
    nVJ = Hypergraph.nV J
    nEH = Hypergraph.nE H
    nEJ = Hypergraph.nE J

  VertexBij : Set
  VertexBij = PBij nVH nVJ

  EdgeBij : Set
  EdgeBij = PBij nEH nEJ

  tryEdge : VertexBij → EdgeBij → Fin nEH → Fin nEJ → Maybe (VertexBij × EdgeBij)
  tryEdge φ ψ e e'
    with map (Hypergraph.vlab H) (Hypergraph.ein  H e)
           ≟L map (Hypergraph.vlab J) (Hypergraph.ein  J e')
       | map (Hypergraph.vlab H) (Hypergraph.eout H e)
           ≟L map (Hypergraph.vlab J) (Hypergraph.eout J e')
  ... | no _  | _     = nothing
  ... | _     | no _  = nothing
  ... | yes p | yes q =
        flat-match-subst (sym p) (sym q) (Hypergraph.elab J e')
                         (Hypergraph.elab H e)                 >>= λ _   →
        pairUp φ  (Hypergraph.ein  H e) (Hypergraph.ein  J e') >>= λ φ'  →
        pairUp φ' (Hypergraph.eout H e) (Hypergraph.eout J e') >>= λ φ'' →
        extend-bij ψ e e'                                      >>= λ ψ'  →
        just (φ'' , ψ')

  matchEdge : VertexBij → EdgeBij → Fin nEH → List (VertexBij × EdgeBij)
  matchEdge φ ψ e = mapMaybe (tryEdge φ ψ e) (allFin nEJ)

  -- Enumerate rather than commit: carving may reject a non-convex match
  -- and need a later candidate.
  searchAll : VertexBij → EdgeBij → List (VertexBij × EdgeBij)
  searchAll = go (nEH * nEJ)
    where
      go : ℕ → VertexBij → EdgeBij → List (VertexBij × EdgeBij)
      go ℕ.zero    φ ψ with firstUnmatched ψ
      ... | nothing = (φ , ψ) ∷ []
      ... | just _  = []
      go (ℕ.suc k) φ ψ with firstUnmatched ψ
      ... | nothing = (φ , ψ) ∷ []
      ... | just e  = tryAll (matchEdge φ ψ e)
        where
          tryAll : List (VertexBij × EdgeBij) → List (VertexBij × EdgeBij)
          tryAll []               = []
          tryAll ((φ' , ψ') ∷ xs) = go k φ' ψ' ++ tryAll xs

  -- `_++_` is lazy in its second argument, so taking the `head` forces exactly
  -- the failing subtrees a first-match-only recursion would have forced.
  searchIso : VertexBij → EdgeBij → Maybe (VertexBij × EdgeBij)
  searchIso φ ψ = head (searchAll φ ψ)
