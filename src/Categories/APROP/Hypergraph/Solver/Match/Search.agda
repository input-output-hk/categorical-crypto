{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Backtracking edge matching (TensorRocq §4.2).
--
-- Reject incompatible connectivity before inspecting labels, but check payloads
-- before returning a candidate: final verification does not re-enter search.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Match.Search (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Solver.Match.Incidence
open import Categories.APROP.Hypergraph.Solver.Match.PBij

open import Data.Bool.Base
open import Data.Fin
open import Data.List.Base
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; _>>=_)
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open APROPSignature sig

-- Equal typed payloads imply equal flattened boundaries via FlatGen.okA/okB.
-- Search need not recompute those boundaries or construct their transports;
-- Verify still checks every vertex, port and label on the chosen candidate.
samePayload : ∀ {As Bs Cs Ds} → FlatGen As Bs → FlatGen Cs Ds → Bool
samePayload (flat-rec {A} {B} _ _ f) (flat-rec {C} {D} _ _ g)
  with A ≟-ObjTerm C | B ≟-ObjTerm D
... | yes refl | yes refl with f ≟-mor g
...   | yes _ = true
...   | no _ = false
samePayload _ _ | _ | _ = false

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
  tryEdge φ ψ e e' =
    extend-bij ψ e e' >>= λ ψ' →
    pairUp φ (Hypergraph.ein H e) (Hypergraph.ein J e') >>= λ φ' →
    pairUp φ' (Hypergraph.eout H e) (Hypergraph.eout J e') >>= λ φ'' →
    accept φ'' ψ'
    where
      accept : VertexBij → EdgeBij → Maybe (VertexBij × EdgeBij)
      accept φ' ψ' with samePayload (Hypergraph.elab J e') (Hypergraph.elab H e)
      ... | true = just (φ' , ψ')
      ... | false = nothing

  candidateEdges : Buckets nVJ nEJ → Buckets nVJ nEJ → VertexBij → Fin nEH → List (Fin nEJ)
  candidateEdges inputs outputs φ e with constrained (forward φ) inputs 0 (Hypergraph.ein H e)
  ... | just es = es
  ... | nothing with constrained (forward φ) outputs 0 (Hypergraph.eout H e)
  ...   | just es = es
  ...   | nothing = allFin nEJ

  matchEdgeFrom : Buckets nVJ nEJ → Buckets nVJ nEJ
                → VertexBij → EdgeBij → Fin nEH → List (VertexBij × EdgeBij)
  matchEdgeFrom inputs outputs φ ψ e = mapMaybe (tryEdge φ ψ e) (candidateEdges inputs outputs φ e)

  matchEdge : VertexBij → EdgeBij → Fin nEH → List (VertexBij × EdgeBij)
  matchEdge φ ψ e = mapMaybe (tryEdge φ ψ e) (allFin nEJ)

  -- Enumerate rather than commit: carving may reject a non-convex match
  -- and need a later candidate.
  searchAllIndexed : VertexBij → EdgeBij → List (VertexBij × EdgeBij)
  searchAllIndexed = go (incidence (Hypergraph.ein J)) (incidence (Hypergraph.eout J)) (nEH * nEJ)
    where
      go : Buckets nVJ nEJ → Buckets nVJ nEJ → ℕ → VertexBij → EdgeBij → List (VertexBij × EdgeBij)
      go inputs outputs ℕ.zero φ ψ with firstUnmatched ψ
      ... | nothing = (φ , ψ) ∷ []
      ... | just _  = []
      go inputs outputs (ℕ.suc k) φ ψ with firstUnmatched ψ
      ... | nothing = (φ , ψ) ∷ []
      ... | just e  = tryAll (matchEdgeFrom inputs outputs φ ψ e)
        where
          tryAll : List (VertexBij × EdgeBij) → List (VertexBij × EdgeBij)
          tryAll []               = []
          tryAll ((φ' , ψ') ∷ xs) = go inputs outputs k φ' ψ' ++ tryAll xs

  searchAllScan : VertexBij → EdgeBij → List (VertexBij × EdgeBij)
  searchAllScan = go (nEH * nEJ)
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

  -- Dispatch once, outside both recursive loops. Scalars have no incidence
  -- constraint, and a small pattern cannot amortize building the host index.
  -- The 32-edge cutoff is heuristic: unconstrained ports cannot narrow a scan.
  searchAll : VertexBij → EdgeBij → List (VertexBij × EdgeBij)
  searchAll with nEH Data.Nat.<ᵇ 32
  ... | true = searchAllScan
  ... | false with nEJ Data.Nat.<ᵇ 32
  ...   | true = searchAllScan
  ...   | false with nVJ Data.Nat.≡ᵇ 0
  ...     | true = searchAllScan
  ...     | false = searchAllIndexed

  -- `_++_` is lazy in its second argument, so taking the `head` forces exactly
  -- the failing subtrees a first-match-only recursion would have forced.
  searchIso : VertexBij → EdgeBij → Maybe (VertexBij × EdgeBij)
  searchIso φ ψ = head (searchAll φ ψ)
