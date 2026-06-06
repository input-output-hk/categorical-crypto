{-# OPTIONS --safe --with-K #-}

------------------------------------------------------------------------
-- Proving the WIDE Kelly faithfulness residual from the NARROW ones.
--
-- `Categories.PermuteCoherence.Faithfulness` exposes the wide residual
-- `FaithfulnessResidual` (the full coherence obligation: any two
-- derivations with equal evaluated bijection give `≈Term`-equal
-- `permute` terms) and the strictly-narrower `TransSelfLoopResidual`
-- (the trans-self-loop fragment), together with the EASY implication
--
--     wide⇒narrow : FaithfulnessResidual → TransSelfLoopResidual.
--
-- This module supplies the GENUINELY MISSING reverse implication
--
--     narrow⇒wide : TransSelfLoopResidual → FaithfulnessResidual
--
-- proved CONSTRUCTIVELY by a groupoid argument that consumes the
-- constructive σ-block inverse lemmas of `FaithfulnessK`
-- (`permute-inverse-right!`).  Together with `wide⇒narrow` this shows
-- the wide and narrow residuals are EQUIVALENT, so the wide
-- `FaithfulnessResidual` postulate (the `K-faithfulness` /
-- `Kelly-faithfulness` axioms threaded through the completeness chain)
-- is no stronger than the narrow one.
--
-- We then compose with `FaithfulnessK.constructive-trans-self-loop`
-- (the constructive `PermuteRespSymResidual → TransSelfLoopResidual`
-- reduction) to obtain
--
--     faithfulness-from-resp-sym
--       : PermuteRespSymResidual → FaithfulnessResidual
--
-- i.e. the wide Kelly residual reduces to the single strictly-narrower
-- `PermuteRespSymResidual` (which scopes only to pairs
-- `(q, ↭-sym p)`, with the eval-hypothesis stated post
-- `eval-↭-sym`-normalisation).  EVERYTHING in this module is
-- postulate-free and `--safe`; the residual itself is supplied by the
-- consumer.
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.FaithfulnessProof
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.List.Base using (List)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

import Data.Fin.Permutation as P
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Soundness using (eval-↭-sym)
open import Categories.PermuteCoherence.Faithfulness d
  using (permute; FaithfulnessResidual; TransSelfLoopResidual; wide⇒narrow)
open import Categories.PermuteCoherence.FaithfulnessK d
  using ( permute-inverse-right!
        ; PermuteRespSymResidual
        ; constructive-trans-self-loop
        )

------------------------------------------------------------------------
-- 1. The narrow residual implies the wide one.
--
-- Given `R : TransSelfLoopResidual` and two derivations `p q : xs ↭ ys`
-- with `eval-↭ p ≈-fb eval-↭ q` (= `p ≅↭ q`), we want
-- `permute p ≈Term permute q`.
--
-- The bijection-level self-loop `eval-↭ (↭-sym q) ∘-fb eval-↭ p ≈ id`
-- holds (it sends `i ↦ flip(eval q)(eval p i) = flip(eval q)(eval q i)
-- = i`), so `R` collapses `permute (↭-sym q) ∘ permute p` to `id`.
-- Cancelling `permute (↭-sym q)` on the right of `permute q` (via the
-- constructive `permute-inverse-right! q`) then turns `permute p` into
-- `permute q`:
--
--     permute p
--   ≈ id ∘ permute p
--   ≈ (permute q ∘ permute (↭-sym q)) ∘ permute p   [permute-inverse-right! q]
--   ≈ permute q ∘ (permute (↭-sym q) ∘ permute p)   [assoc]
--   ≈ permute q ∘ id                                 [R, on the self-loop]
--   ≈ permute q.

narrow⇒wide : TransSelfLoopResidual → FaithfulnessResidual
narrow⇒wide R = record
  { permute-resp-≅↭ = λ {xs} {ys} p q p≅q →
      let
        -- The self-loop hypothesis at the bijection level.
        self-loop : eval-↭ (Perm.↭-sym q) ∘-fb eval-↭ p ≈-fb id-fb
        self-loop i =
          trans (eval-↭-sym q (eval-↭ p P.⟨$⟩ʳ i))
                (trans (cong (P.flip (eval-↭ q) P.⟨$⟩ʳ_) (p≅q i))
                       (P.inverseˡ (eval-↭ q)))

        -- The narrow residual collapses the self-loop term to `id`.
        loop : permute (Perm.↭-sym q) ∘ permute p ≈Term id
        loop = TransSelfLoopResidual.permute-trans-self-loop-id
                 R p (Perm.↭-sym q) self-loop
      in
        ≈-Term-trans (≈-Term-sym idˡ)
       (≈-Term-trans (∘-resp-≈ (≈-Term-sym (permute-inverse-right! q)) ≈-Term-refl)
       (≈-Term-trans assoc
       (≈-Term-trans (∘-resp-≈ ≈-Term-refl loop)
                      idʳ)))
  }

------------------------------------------------------------------------
-- 2. Equivalence of the wide and narrow residuals.
--
-- `wide⇒narrow` (from `Faithfulness`) is the easy direction; together
-- with `narrow⇒wide` it witnesses that the two residuals carry exactly
-- the same content.

wide⇔narrow-forward : FaithfulnessResidual → TransSelfLoopResidual
wide⇔narrow-forward = wide⇒narrow

wide⇔narrow-backward : TransSelfLoopResidual → FaithfulnessResidual
wide⇔narrow-backward = narrow⇒wide

------------------------------------------------------------------------
-- 3. The wide residual from `PermuteRespSymResidual`.
--
-- Composing `narrow⇒wide` with `FaithfulnessK.constructive-trans-self-loop`
-- reduces the wide Kelly residual to the single strictly-narrower
-- `PermuteRespSymResidual`.  This is the form consumed by the APROP
-- completeness chain: supplying ONE `PermuteRespSymResidual` value
-- discharges the `K-faithfulness : FaithfulnessResidual` postulate.

faithfulness-from-resp-sym : PermuteRespSymResidual → FaithfulnessResidual
faithfulness-from-resp-sym R = narrow⇒wide (constructive-trans-self-loop R)
