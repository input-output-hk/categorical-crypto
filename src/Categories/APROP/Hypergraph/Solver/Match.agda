{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 4a.3: Edge matching + propagation (TensorRocq §4.2).
--
-- Core of the search. Given partial vertex and edge bijections `(φ, ψ)`
-- and an unmatched H-edge `e`, enumerate the J-edges `e'` whose shape
-- is compatible with `e` and, for each, return the extended
-- `(φ', ψ')`. Returns a `List` of successful extensions; the
-- back-tracker (Phase 4a.4) consumes this list.
--
-- Propagation is implicit: pairing up `H.ein e [i] ↔ J.ein e' [i]` adds new
-- vertex constraints to `φ`, pruning future choices via `extend-bij`'s
-- conflict check.
--
-- Candidates are culled by arity/atom-list shape AND by edge label: the
-- shape check produces exactly the atom-list equalities needed to transport
-- the J-label to the H-index, where `flat-match` (the same conservative
-- comparison the final verification uses) decides label equality.  Without
-- the label cull, a signature with many same-shaped generators lets the
-- search lock onto a label-mismatched (but connectivity-consistent) match,
-- which the verification stage then rejects — and since verification
-- failures do not re-enter the search, the whole query fails spuriously.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Match (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Solver.PBij
  using (PBij; extend-bij; pairUp)
open import Categories.APROP.Hypergraph.Solver.Verify sig-dec using (flat-match)

open import Data.Bool.Base using (Bool; false; true; _∧_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; subst₂)
open import Relation.Nullary using (does; yes; no)

--------------------------------------------------------------------------------
-- Shape compatibility — arity and atom lists agree.  Cheap pre-filter
-- before attempting `pairUp`.

_≟L_ : (xs ys : List X) → _
_≟L_ = ≡-dec _≟X_

shape-ok?
  : ∀
    (H J : Hypergraph FlatGen)
  → (e : Fin (Hypergraph.nE H)) (e' : Fin (Hypergraph.nE J))
  → Bool
shape-ok? H J e e' =
  does (map (Hypergraph.vlab H) (Hypergraph.ein  H e)
         ≟L map (Hypergraph.vlab J) (Hypergraph.ein  J e'))
    ∧
  does (map (Hypergraph.vlab H) (Hypergraph.eout H e)
         ≟L map (Hypergraph.vlab J) (Hypergraph.eout J e'))

--------------------------------------------------------------------------------
-- Try to match edge `e` against edge `e'`: pair up their source lists,
-- then their target lists; finally pair `e` with `e'` in the edge PBij.
-- Returns `just (φ', ψ')` on success, or `nothing` on any conflict.

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

  tryEdge
    : VertexBij → EdgeBij
    → Fin nEH → Fin nEJ
    → Maybe (VertexBij × EdgeBij)
  tryEdge φ ψ e e'
    with map (Hypergraph.vlab H) (Hypergraph.ein  H e)
           ≟L map (Hypergraph.vlab J) (Hypergraph.ein  J e')
       | map (Hypergraph.vlab H) (Hypergraph.eout H e)
           ≟L map (Hypergraph.vlab J) (Hypergraph.eout J e')
  ... | no _  | _     = nothing
  ... | _     | no _  = nothing
  ... | yes p | yes q
    -- Shape agrees; transport J's label to H's index and compare.
    with flat-match (subst₂ FlatGen (sym p) (sym q) (Hypergraph.elab J e'))
                    (Hypergraph.elab H e)
  ... | nothing = nothing
  ... | just _  = viaEin (pairUp φ (Hypergraph.ein H e) (Hypergraph.ein J e'))
    where
      viaEout : VertexBij → Maybe (VertexBij × EdgeBij)
      viaEout φ' with pairUp φ' (Hypergraph.eout H e) (Hypergraph.eout J e')
      ... | nothing   = nothing
      ... | just φ'' with extend-bij ψ e e'
      ...              | nothing   = nothing
      ...              | just ψ'   = just (φ'' , ψ')

      viaEin : Maybe VertexBij → Maybe (VertexBij × EdgeBij)
      viaEin nothing    = nothing
      viaEin (just φ')  = viaEout φ'

  --------------------------------------------------------------------------
  -- Enumerate all matches of `e` against J-edges.

  matchEdge : VertexBij → EdgeBij → Fin nEH → List (VertexBij × EdgeBij)
  matchEdge φ ψ e = go nEJ (λ i → i)
    where
      go : (count : ℕ) → (Fin count → Fin nEJ) → List (VertexBij × EdgeBij)
      go ℕ.zero    _   = []
      go (ℕ.suc n) inj = cons (tryEdge φ ψ e (inj zero))
        where
          cons : Maybe (VertexBij × EdgeBij) → List (VertexBij × EdgeBij)
          cons nothing  = go n (λ i → inj (suc i))
          cons (just x) = x ∷ go n (λ i → inj (suc i))
