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
-- *Propagation* is implicit: pairing up `H.ein e [i] ↔ J.ein e' [i]`
-- adds `length (ein e) + length (eout e)` new vertex constraints to
-- `φ`, which prune future edge-match choices via `extend-bij`'s
-- conflict check.
--
-- **No label equality check at the `FlatGen` level is done here.**
-- Labels live in `FlatGen (map vlab (ein e)) (map vlab (eout e))`,
-- and comparing them requires transport along atom-list equalities
-- that the search hasn't constructed yet. The final verification
-- (Phase 4a.5) pattern-matches both labels as `flat f / flat g`
-- and checks `f ≟-mor g` — at that point both sides have fully
-- determined types. Here we only cull candidates by arity and
-- atom-list shape, which is cheap and decidable.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Match (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Solver.PBij
  using (PBij; extend-bij; pairUp)

open import Data.Bool.Base using (Bool; false; true; _∧_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does)

--------------------------------------------------------------------------------
-- Shape compatibility — arity and atom lists agree between H-edge `e`
-- and J-edge `e'`. Cheap pre-filter before attempting to pairUp.

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
  tryEdge φ ψ e e' with shape-ok? H J e e'
  ... | false = nothing
  ... | true  = viaEin (pairUp φ (Hypergraph.ein H e) (Hypergraph.ein J e'))
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
  -- Enumerate all matches of `e` against J-edges. Walks Fin positions
  -- of `nEJ` from zero up and collects successful extensions.

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
