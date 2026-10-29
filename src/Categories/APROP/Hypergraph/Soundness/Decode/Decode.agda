{-# OPTIONS --safe --without-K #-}

-- Failed extractions skip edges; the final match is only a boundary postcondition.
-- It admits cyclic and nonlinear raw graphs (see FinOrderNoInv). Translated-term
-- totality relies on the separate linearity/order proofs in DecodeAttemptLinearP.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Decode.Decode (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig

open import Categories.Combinatorics.ExtractPrefix

open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Function using (case_of_)

module _ (H : Hypergraph FlatGen) where

  private
    module H = Hypergraph H

  edge-step : (s : List (Fin H.nV)) (e : Fin H.nE) → List (Fin H.nV)
  edge-step s e = case extract-prefix (H.ein e) s of λ where
    nothing → s
    (just (rest , _)) → H.eout e ++ rest

  -- Reducing over abstract H avoids normalising large computed hypergraphs
  -- at hTensor/hComposeP call sites.
  edge-step-just
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
        {rest : List (Fin H.nV)} {perm}
    → extract-prefix (H.ein e) s ≡ just (rest , perm)
    → edge-step s e ≡ H.eout e ++ rest
  edge-step-just s e eq rewrite eq = refl

  edge-step-nothing
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
    → extract-prefix (H.ein e) s ≡ nothing
    → edge-step s e ≡ s
  edge-step-nothing s e eq rewrite eq = refl

  process-edges : List (Fin H.nE) → (s : List (Fin H.nV)) → List (Fin H.nV)
  process-edges []       s = s
  process-edges (e ∷ es) s = process-edges es (edge-step s e)

  process-all-edges : (s : List (Fin H.nV)) → List (Fin H.nV)
  process-all-edges = process-edges (allFin H.nE)

  process-edges-++
    : ∀ (xs ys : List (Fin H.nE)) (s : List (Fin H.nV))
    → process-edges (xs ++ ys) s ≡ process-edges ys (process-edges xs s)
  process-edges-++ []       ys s = refl
  process-edges-++ (e ∷ xs) ys s = process-edges-++ xs ys (edge-step s e)
