{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 4a.2: Interface seeding (TensorRocq §4.2).
--
-- Given `H, J : Hypergraph FlatGen`, seed a partial vertex
-- bijection `φ₀` from the interfaces by pointwise pairing
-- `H.dom ↔ J.dom` and `H.cod ↔ J.cod`. This pins the boundary
-- of the isomorphism before any edge matching begins.
--
-- Returns `nothing` when interfaces have inconsistent length
-- (never happens if the hypergraphs share `As, Bs`) or when
-- a paired vertex's `vlab` disagrees between H and J, which is a
-- genuine isomorphism obstruction the search cannot recover from.
--
-- The vertex-label preservation check is done *optionally* here —
-- strictly it follows from the boundaries agreeing with `As / Bs`
-- (via `dom-ok / cod-ok`), but running it early gives a cheap
-- failure path for malformed inputs and simplifies the
-- label-preservation invariant maintenance in `Match.agda`.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Seed (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Solver.PBij
  using (PBij; emptyBij; pairUp; forward)

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Optional vertex-label consistency check over a forward partial
-- map. Walks `Fin H.nV`; at each position `i` bound to some `j`,
-- verifies `J.vlab j ≡ H.vlab i`. Unbound positions are left for the
-- edge-matching phase to resolve.

check-vlab
  : ∀
    (H J : Hypergraph FlatGen)
  → (Fin (Hypergraph.nV H) → Maybe (Fin (Hypergraph.nV J)))
  → Maybe ⊤
check-vlab H J p = go (Hypergraph.nV H) λ i → i
  where
    -- `count` tracks how many positions are left to examine;
    -- `inj` injects a `Fin count` back into `Fin H.nV`. Each
    -- recursive call shrinks `count` and post-composes `inj` with
    -- `suc` to skip the head.
    go : (count : ℕ) → (Fin count → Fin (Hypergraph.nV H)) → Maybe ⊤
    go zero      _   = just tt
    go (suc n) inj = step (p (inj zero))
      where
        step : Maybe (Fin (Hypergraph.nV J)) → Maybe ⊤
        step nothing  = go n (λ i → inj (suc i))
        step (just j) with Hypergraph.vlab J j ≟X Hypergraph.vlab H (inj zero)
        ...             | yes _ = go n (λ i → inj (suc i))
        ...             | no _  = nothing

--------------------------------------------------------------------------------
-- Seed a partial vertex bijection from the interface lists.

seedFromInterfaces
  : ∀
    (H J : Hypergraph FlatGen)
  → Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
seedFromInterfaces H J =
  step₁ (pairUp emptyBij (Hypergraph.dom H) (Hypergraph.dom J))
  where
    step₃ : Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
          → Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
    step₃ nothing = nothing
    step₃ (just b) with check-vlab H J (forward b)
    ... | nothing = nothing
    ... | just _  = just b

    step₂ : PBij (Hypergraph.nV H) (Hypergraph.nV J)
          → Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
    step₂ b = step₃ (pairUp b (Hypergraph.cod H) (Hypergraph.cod J))

    step₁ : Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
          → Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
    step₁ nothing  = nothing
    step₁ (just b) = step₂ b
