{-# OPTIONS --safe --without-K #-}

module Categories.APROP.Hypergraph.Model.Evaluate where

open import Categories.APROP.Hypergraph.Model.Core

open import Data.Fin
open import Data.List.Base
open import Data.Nat.Base
open import Function.Strict
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

module _ {X : Set} {Gen : List X → List X → Set} where

  private
    build : (nV nE : ℕ) (vlab : Fin nV → X)
          → (ein eout : Fin nE → List (Fin nV))
          → ((e : Fin nE) → Gen (map vlab (ein e)) (map vlab (eout e)))
          → List (Fin nV) → List (Fin nV) → Hypergraph Gen
    build nV nE vlab ein eout elab dom cod = record
      { nV = nV ; nE = nE ; vlab = vlab ; ein = ein ; eout = eout
      ; elab = elab ; dom = dom ; cod = cod }

  module _ {b : Level} {B : Hypergraph Gen → Set b}
    (k : (H : Hypergraph Gen) → B H) where

    private
      run : (nV nE : ℕ) (vlab : Fin nV → X)
          → (ein eout : Fin nE → List (Fin nV))
          → (elab : (e : Fin nE) → Gen (map vlab (ein e)) (map vlab (eout e)))
          → (dom cod : List (Fin nV)) → B (build nV nE vlab ein eout elab dom cod)
      run nV nE vlab ein eout elab dom cod = k (build nV nE vlab ein eout elab dom cod)

    -- The continuation generalizes both counts and every Fin-indexed field.
    -- Primitive force evaluates a count to WHNF, not an entire graph.
    forceCounts : (H : Hypergraph Gen) → B H
    forceCounts H =
      force H.nV (λ nV → force H.nE (run nV))
        H.vlab H.ein H.eout H.elab H.dom H.cod
      where module H = Hypergraph H

    forceCounts-≡ : (H : Hypergraph Gen) → forceCounts H ≡ k H
    forceCounts-≡ H = trans
      (cong (λ f → f H.vlab H.ein H.eout H.elab H.dom H.cod)
        (force-≡ H.nV (λ nV → force H.nE (run nV))))
      (cong (λ f → f H.vlab H.ein H.eout H.elab H.dom H.cod)
        (force-≡ H.nE (run H.nV)))
      where module H = Hypergraph H
