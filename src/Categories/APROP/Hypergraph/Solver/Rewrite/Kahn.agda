{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Kahn topological ordering of edges over a `Fin n` vertex set.
--
-- `decode` consumes edges in `Fin` order, each needing its inputs already on
-- the stack; emitting edges in dependency order guarantees that.  Greedy
-- choice suffices on a DAG; if no edge is ready the carve was non-convex
-- (a path leaves and re-enters the redex through the hole) and we fail.
--
-- Parameterised by the edge type `E` and its endpoint accessors `ins`/`outs`;
-- `kahn` only ever inspects edge endpoints, never labels.  The labelled carve
-- (`Deep.Build`, `E = Edge`) instantiates it.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Rewrite.Kahn where

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Base as Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

module _ {n : ℕ} where

  -- Remove the first occurrence of `v` from the availability stack.
  remove1 : Fin n → List (Fin n) → Maybe (List (Fin n))
  remove1 v []       = nothing
  remove1 v (w ∷ ws) with v ≟F w
  ... | yes _ = just ws
  ... | no  _ = Maybe.map (w ∷_) (remove1 v ws)

  -- Consume an edge's whole input list from the availability stack.
  consume : List (Fin n) → List (Fin n) → Maybe (List (Fin n))
  consume []       avail = just avail
  consume (v ∷ vs) avail = remove1 v avail >>= consume vs

  module _ {E : Set} (ins outs : E → List (Fin n)) where

    -- First pending edge whose inputs are all available; returns the new
    -- availability and the remaining pending list (order preserved).
    findReady : List (Fin n) → List E
              → Maybe (E × List (Fin n) × List E)
    findReady avail []       = nothing
    findReady avail (e ∷ es) with consume (ins e) avail
    ... | just avail' = just (e , avail' , es)
    ... | nothing     =
          Maybe.map (λ { (r , av , rest) → (r , av , e ∷ rest) })
                    (findReady avail es)

    kahn : ℕ → List (Fin n) → List E → Maybe (List E)
    kahn _          _     []      = just []
    kahn zero       _     _       = nothing
    kahn (suc fuel) avail pending with findReady avail pending
    ... | nothing                  = nothing
    ... | just (e , avail' , rest) =
          Maybe.map (e ∷_) (kahn fuel (avail' ++ outs e) rest)
