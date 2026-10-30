{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Port-position incidence buckets. Right-fold insertion preserves ascending
-- edge order; recording positions prevents repeated vertices duplicating edges.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Match.Incidence where

open import Data.Bool.Base
open import Data.Fin using (Fin)
open import Data.List.Base
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat
open import Data.Product using (_×_; _,_)
import Data.Vec.Base as Vec

private
  variable
    nH nV nE : ℕ

Buckets : ℕ → ℕ → Set
Buckets nV nE = Vec.Vec (List (ℕ × Fin nE)) nV

insertPorts : Fin nE → ℕ → List (Fin nV) → Buckets nV nE → Buckets nV nE
insertPorts e p [] buckets = buckets
insertPorts e p (v ∷ vs) buckets =
  Vec.updateAt (insertPorts e (suc p) vs buckets) v ((p , e) ∷_)

incidence : (Fin nE → List (Fin nV)) → Buckets nV nE
incidence {nE = nE} ports = foldr (λ e → insertPorts e 0 (ports e)) (Vec.replicate _ []) (allFin nE)

atPort : Buckets nV nE → ℕ → Fin nV → List (Fin nE)
atPort buckets p v = mapMaybe select (Vec.lookup buckets v)
  where
    select : ℕ × Fin _ → Maybe (Fin _)
    select (q , e) = if p ≡ᵇ q then just e else nothing

-- One known ordered port is a necessary condition; tryEdge checks all the rest.
-- Nothing means no constraint, whereas just [] must not fall back to all edges.
constrained : (Fin nH → Maybe (Fin nV)) → Buckets nV nE
            → ℕ → List (Fin nH) → Maybe (List (Fin nE))
constrained φ buckets p [] = nothing
constrained φ buckets p (v ∷ vs) with φ v
... | just w = just (atPort buckets p w)
... | nothing = constrained φ buckets (suc p) vs
