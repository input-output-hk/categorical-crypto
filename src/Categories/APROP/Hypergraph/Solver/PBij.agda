{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 4a.1: Partial vertex/edge maps (TensorRocq §4.2).
--
-- Pure-function representation of a partial map `Fin n → Maybe (Fin m)`.
-- Extending with a new `(i ↦ j)` binding checks for conflicts in both
-- the domain (has `i` already been bound?) and range (`j` mentioned
-- elsewhere? — handled by the symmetric PBij wrapper). Returns `nothing`
-- on any conflict.
--
-- `PBij n m` carries forward *and* backward partial maps; extending
-- atomically updates both. The operational invariants (agreement
-- between forward and backward) are enforced by `extend-bij`; the
-- bijection laws (`φ-left`, `φ-rght`) are reconstructed at
-- extraction time in `total?`.
--
-- No heuristics, no optimisations — the plan calls for the simplest
-- possible data structures (Phase 4a Risks section).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.PBij where

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Partial map.

PartialMap : ℕ → ℕ → Set
PartialMap n m = Fin n → Maybe (Fin m)

empty : ∀ {n m} → PartialMap n m
empty _ = nothing

-- Update a binding at `i` to `j` if consistent with what's already
-- stored. Returns `nothing` when `i` is already bound to a different
-- value. `p i ≡ just j` — no update needed.
extend : ∀ {n m} → PartialMap n m → Fin n → Fin m
       → Maybe (PartialMap n m)
extend {n} {m} p i j with p i
... | nothing = just (λ k → case-≟ k i j (p k))
  where
    case-≟ : Fin n → Fin n → Fin m → Maybe (Fin m) → Maybe (Fin m)
    case-≟ k i' j' pk with k ≟F i'
    ... | yes _ = just j'
    ... | no _  = pk
... | just j' with j ≟F j'
...   | yes _ = just p
...   | no _  = nothing

-- Lookup with default.
lookup? : ∀ {n m} → PartialMap n m → Fin n → Maybe (Fin m)
lookup? p i = p i

--------------------------------------------------------------------------------
-- Symmetric partial bijection. Forward and backward are kept in sync
-- by `extend-bij`, which refuses extensions that would violate the
-- operational bijection invariant (each `j` appears in at most one
-- mapping, and `forward` / `backward` agree).

record PBij (n m : ℕ) : Set where
  field
    forward  : PartialMap n m
    backward : PartialMap m n

open PBij public

emptyBij : ∀ {n m} → PBij n m
emptyBij = record { forward = empty ; backward = empty }

-- Extend a partial bijection with `i ↔ j`. Fails if either direction
-- conflicts. Both directions are updated atomically.
extend-bij : ∀ {n m} → PBij n m → Fin n → Fin m → Maybe (PBij n m)
extend-bij b i j with extend (forward b) i j
... | nothing = nothing
... | just f' with extend (backward b) j i
...   | nothing = nothing
...   | just g' = just (record { forward = f' ; backward = g' })

--------------------------------------------------------------------------------
-- Pointwise pairing of two lists into a partial bijection. Used at
-- interface-seeding time (Phase 4a.2) to pair H.dom with J.dom and
-- H.cod with J.cod.

open import Data.List.Base using (List; []; _∷_)

pairUp : ∀ {n m} → PBij n m → List (Fin n) → List (Fin m) → Maybe (PBij n m)
pairUp b [] []             = just b
pairUp b (_ ∷ _) []        = nothing   -- length mismatch
pairUp b [] (_ ∷ _)        = nothing   -- length mismatch
pairUp b (i ∷ is) (j ∷ js) with extend-bij b i j
... | nothing = nothing
... | just b' = pairUp b' is js
