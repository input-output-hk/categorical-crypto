{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Kahn topological ordering of edges over a `Fin n` vertex set.
--
-- `decode` consumes edges in `Fin` order, each needing its inputs already on
-- the stack; emitting edges in dependency order guarantees that.  Greedy
-- choice suffices on a DAG whose vertices each have at most one consumer
-- (translated graphs, and `Deep`'s split scheduling views): firing a ready
-- edge never disables another.  If no edge is ready the carve was non-convex
-- (a path leaves and re-enters the redex through the hole) and we fail.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Rewrite.Kahn where

open import Data.Fin
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Relation.Nullary

module _ {n : ℕ} where

  remove1 : Fin n → List (Fin n) → Maybe (List (Fin n))
  remove1 v []       = nothing
  remove1 v (w ∷ ws) with v ≟F w
  ... | yes _ = just ws
  ... | no  _ = Maybe.map (w ∷_) (remove1 v ws)

  consume : List (Fin n) → List (Fin n) → Maybe (List (Fin n))
  consume []       avail = just avail
  consume (v ∷ vs) avail = remove1 v avail >>= consume vs

  module _ {E : Set} (ins outs : E → List (Fin n)) where

    findReady : List (Fin n) → List E → Maybe (E × List (Fin n) × List E)
    findReady avail []       = nothing
    findReady avail (e ∷ es) with consume (ins e) avail
    ... | just avail' = just (e , avail' , es)
    ... | nothing     =
          Maybe.map (λ { (r , av , rest) → (r , av , e ∷ rest) })
                    (findReady avail es)

    -- Each step emits one pending edge, so the pending list is its own fuel.
    kahn : List (Fin n) → List E → Maybe (List E)
    kahn avail pending = go pending avail pending
      where
        go : List E → List (Fin n) → List E → Maybe (List E)
        go _        _     []      = just []
        go []       _     _       = nothing
        go (_ ∷ fs) avail pending with findReady avail pending
        ... | nothing                  = nothing
        ... | just (e , avail' , rest) =
              Maybe.map (e ∷_) (go fs (avail' ++ outs e) rest)
