{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `LinearityCombinatorial` — the pure-combinatorial residual atom
-- (formerly `SwapAtomResidual.swap-already-fires` in
-- `Discharge/Sub/SwapAtomAssumptionDischarge.agda:152`).
--
-- This atom is "topological soundness for AllFire swap": under
-- `Linear H`, having an AllFire witness for `e₁ ∷ e₂ ∷ xs` implies an
-- AllFire witness for the swapped 2-prefix `e₂ ∷ e₁ ∷ []`.  It is not
-- implied by `Linear` alone (per `EdgeReorder.agda`'s counter-example
-- to the unrestricted swap), so it is exposed as a residual.
--
-- The atom has NO SMC content (no `HomTerm`, no `_≈Term_`).  Its
-- statement only mentions `Hypergraph`, `Linear`, `AllFire` — all
-- combinatorial.  This module strips the APROP wrapper from
-- `Linear`/`AllFire` (both whose APROP definitions only use the
-- generic `Hypergraph` fields `dom`/`cod`/`ein`/`eout`/`nV`/`nE`), so
-- the trust surface field is stated over arbitrary `Hypergraph Gen`.
--------------------------------------------------------------------------------

module Categories.Hypergraph.LinearityCombinatorial where

open import Categories.APROP.Hypergraph.Core using (Hypergraph)

open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.List using (List; []; _∷_; _++_; tabulate; concat)
open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ℕ_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (yes; no)

--------------------------------------------------------------------------------
-- Section 1: Generic `count`, `producedList`, `consumedList`, `Linear`.
--
-- Definitions are verbatim copies of `Categories.APROP.Hypergraph.
-- Completeness.Linearity.{count,producedList,consumedList,Linear}` (which
-- only use generic Hypergraph fields).  We re-expose them here so the
-- trust-surface record has no APROP imports.

-- `count` does NOT depend on `Gen`/`X`; lives outside the parameterised
-- block so callers don't need to supply `{X}`/`{Gen}` implicits.
count : ∀ {n} → Fin n → List (Fin n) → ℕ
count v []       = 0
count v (x ∷ xs) with v ≟ x
... | yes _ = suc (count v xs)
... | no  _ = count v xs

module _ {X : Set} {Gen : List X → List X → Set} where

  producedList : (H : Hypergraph Gen) → List (Fin (Hypergraph.nV H))
  producedList H = Hypergraph.dom H ++ concat (tabulate (Hypergraph.eout H))

  consumedList : (H : Hypergraph Gen) → List (Fin (Hypergraph.nV H))
  consumedList H = Hypergraph.cod H ++ concat (tabulate (Hypergraph.ein H))

  Linear : Hypergraph Gen → Set
  Linear H = (∀ v → count v (producedList H) ≡ count v (consumedList H))
           × (∀ v → count v (producedList H) ≤ℕ 1)

  --------------------------------------------------------------------
  -- Section 2: Generic `AllFire`.
  --
  -- Same body as the APROP `Sub/ProcessTermAligned.AllFire`, MINUS
  -- the `extract-prefix … ≡ just (rest , p)` evidence field.  In
  -- Sense-1 / generic form the permutation `p : s ↭ ein ++ rest` is
  -- itself the locating witness; recovering `extract-prefix` evidence
  -- is a separate operation that needs a decoder context (i.e.
  -- happens in the APROP bridge module, not here).

  AllFire : (H : Hypergraph Gen)
          → List (Fin (Hypergraph.nE H))
          → List (Fin (Hypergraph.nV H))
          → Set
  AllFire H []       _ = ⊤
  AllFire H (e ∷ es) s =
    Σ[ rest ∈ List (Fin (Hypergraph.nV H)) ]
    Σ[ p ∈ s Perm.↭ Hypergraph.ein H e ++ rest ]
      AllFire H es (Hypergraph.eout H e ++ rest)

--------------------------------------------------------------------------------
-- The record.

record LinearityCombinatorial
  {X : Set} {Gen : List X → List X → Set} : Set where
  field
    -- Under `Linear H`, AllFire on `e₁ ∷ e₂ ∷ xs` produces AllFire on
    -- the swapped 2-prefix `e₂ ∷ e₁ ∷ []`.
    --
    -- Mathematically true (topological soundness) but not implied by
    -- `Linear` alone — `EdgeReorder.agda`'s counter-example shows
    -- unrestricted swap can fail without this premise.

    swap-already-fires
      : ∀ (H : Hypergraph Gen)
          (e₁ e₂ : Fin (Hypergraph.nE H))
          (xs : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
      → Linear H
      → AllFire H (e₁ ∷ e₂ ∷ xs) s
      → AllFire H (e₂ ∷ e₁ ∷ []) s
