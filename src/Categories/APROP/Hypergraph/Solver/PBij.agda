{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Partial vertex/edge maps (TensorRocq §4.2).
--
-- A partial map is a pure function `Fin n → Maybe (Fin m)`.  `PBij n m`
-- carries forward *and* backward partial maps; `extend-bij` updates both
-- atomically and refuses conflicting extensions.  The bijection laws
-- (`φ-left`, `φ-rght`) are reconstructed at extraction time in `total?`.
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

-- Update a binding at `i` to `j` if consistent; `nothing` when `i` is
-- already bound to a different value.
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

lookup? : ∀ {n m} → PartialMap n m → Fin n → Maybe (Fin m)
lookup? p i = p i

--------------------------------------------------------------------------------
-- Symmetric partial bijection (forward/backward kept in sync by `extend-bij`).

record PBij (n m : ℕ) : Set where
  field
    forward  : PartialMap n m
    backward : PartialMap m n

open PBij public

emptyBij : ∀ {n m} → PBij n m
emptyBij = record { forward = empty ; backward = empty }

-- Extend with `i ↔ j`, updating both directions atomically; fails on conflict.
extend-bij : ∀ {n m} → PBij n m → Fin n → Fin m → Maybe (PBij n m)
extend-bij b i j with extend (forward b) i j
... | nothing = nothing
... | just f' with extend (backward b) j i
...   | nothing = nothing
...   | just g' = just (record { forward = f' ; backward = g' })

--------------------------------------------------------------------------------
-- Pairing two lists into a partial bijection (used at interface-seeding
-- time to pair H.dom with J.dom and H.cod with J.cod).

open import Data.List.Base using (List; []; _∷_)

pairUp : ∀ {n m} → PBij n m → List (Fin n) → List (Fin m) → Maybe (PBij n m)
pairUp b [] []             = just b
pairUp b (_ ∷ _) []        = nothing   -- length mismatch
pairUp b [] (_ ∷ _)        = nothing   -- length mismatch
pairUp b (i ∷ is) (j ∷ js) with extend-bij b i j
... | nothing = nothing
... | just b' = pairUp b' is js
