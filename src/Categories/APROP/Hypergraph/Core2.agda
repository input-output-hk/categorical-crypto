{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Experiment: a *de-indexed* Hypergraph type, where the boundary atom
-- lists `As`, `Bs` are NOT in the type.  Instead they're recovered as
-- *computed properties* `domL`/`codL` from the underlying field data.
--
-- Consequences:
--   * `dom-ok` and `cod-ok` are gone — they were the only fields that
--     depended on the indices.
--   * `subst₂ (Hypergraph FlatGen) eq₁ eq₂ H` evaporates: the type does
--     not depend on As, Bs, so there is no transport to perform.
--     `Linear-subst₂`, `decode-attempt-subst₂`, and the entire
--     `decode-attempt-resp-subst₂` chain disappear.
--   * Composition / tensor smart constructors that need a boundary
--     equation now take it as a *propositional argument*, not as part
--     of the type.  This is where any residual `subst` lives — at
--     a single, concentrated point per constructor.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Core2 where

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.Nat using (ℕ)

record Hypergraph {X : Set} (Gen : List X → List X → Set) : Set where
  field
    nV : ℕ
    vlab : Fin nV → X
    nE : ℕ
    ein : Fin nE → List (Fin nV)
    eout : Fin nE → List (Fin nV)
    elab : (e : Fin nE)
         → Gen (map vlab (ein e))
               (map vlab (eout e))
    dom : List (Fin nV)
    cod : List (Fin nV)

module _ {X : Set} {Gen : List X → List X → Set} where
  open Hypergraph

  domL : Hypergraph Gen → List X
  domL H = map (vlab H) (dom H)

  codL : Hypergraph Gen → List X
  codL H = map (vlab H) (cod H)
