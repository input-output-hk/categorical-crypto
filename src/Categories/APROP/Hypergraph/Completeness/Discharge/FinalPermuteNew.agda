{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge module for the **NEW (RESHAPED)** `final-permute-absorb`
-- field of `Hypergraph.Completeness.DecodeRespIso.CompletenessAssumptions`.
--
-- ## The new (d) signature (as of the current refactor)
--
--   final-permute-absorb
--     : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--         (perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
--                   Perm.↭ Hypergraph.cod ⟪ f ⟫F)
--         (perm-g : proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))
--                   Perm.↭ Hypergraph.cod ⟪ g ⟫F)
--     → let stack-↭ = process-edges-resp-iso-stack f g iso
--           F-vlab = Hypergraph.vlab ⟪ f ⟫F
--           G-vlab = Hypergraph.vlab ⟪ g ⟫F
--       in subst₂ HomTerm
--            refl
--            (cong unflatten (full-cod-eq f g))
--            (permute-via-vlab G-vlab perm-g)
--          ∘ permute stack-↭
--          ≈Term
--          permute-via-vlab F-vlab perm-f
--
-- ## What changed compared to the OLD `final-permute-absorb`
--
-- The OLD signature used `subst₂ HomTerm (cong unflatten (sym stack-eq)) ...`
-- to align the domain of `permute-via-vlab G-vlab perm-g` with the domain
-- of `permute-via-vlab F-vlab perm-f`.  The `stack-eq` was the
-- (impossible-to-prove) list equality between the two vlab-mapped final
-- stacks (since they are only `Perm.↭` per `process-edges-resp-iso-stack`).
--
-- The NEW signature uses `∘ permute stack-↭` instead: explicit composition
-- with the `permute` morphism realising the (correctly-typed `Perm.↭`)
-- stack permutation.  This eliminates the impossible domain equality.
--
-- ## Discharge strategy
--
-- We follow the same pattern as `Discharge/FinalPermute.agda` (which
-- handled the OLD signature):
--
--   1. J-eliminate the cod-equation `full-cod-eq f g` (a single
--      propositional equality between X-level lists).
--   2. After J-elim, the goal collapses to
--          permute (PermProp.map⁺ G-vlab perm-g) ∘ permute stack-↭
--          ≈Term permute (PermProp.map⁺ F-vlab perm-f).
--   3. By definition of `permute` on `Perm.trans`, the LHS equals
--          permute (Perm.trans stack-↭ (PermProp.map⁺ G-vlab perm-g)).
--   4. The remaining claim — that two parallel `permute`-derivations
--      of the same X-level pair of lists are `≈Term`-equal — is exactly
--      Kelly's coherence theorem on the σ-structural fragment,
--      exposed as the narrow `PermuteCoherence` record field.
--
-- ## NARROWING vs. the original (d) field
--
-- The narrow obligation `permute-≈Term-coherence` is *strictly* narrower
-- than the original (d) field:
--
--   * NO mention of `f, g, iso, ⟪_⟫F`, the Translation iso, the
--     decoder, or `process-all-edges`.
--   * NO `subst₂` plumbing — pure `≈Term`-statement between two
--     `permute`-built HomTerms over identical X-level boundaries.
--   * NO `permute` bridge in the conclusion — pure equality.
--
-- ## Connection to `permute-inverse-right/left` and
--    `Fin-permute-self-loop-id`
--
-- The conclusion can be FURTHER reduced (via the
-- `PermuteCoherenceFin.WithSelfLoop` route) to a strictly narrower
-- *self-loop* postulate at the X level:
--
--   * `permute-inverse-right p : permute p ∘ permute (↭-sym p) ≈Term id`
--     (CONSTRUCTIVE — fully discharged in
--      `Discharge/Sub/PermuteCoherenceFin.agda`).
--
--   * Combined with a self-loop postulate
--     `permute r ≈Term id` for `r : xs ↭ xs` at the X level, one
--     derives `permute p ≈Term permute q` for any two parallel
--     derivations.
--
--   * The Fin-level analogue `Fin-permute-self-loop-id` is the
--     narrowest known obligation; converting an X-level `r` to a
--     Fin-level `r` requires additional infrastructure (lifting
--     X-level `↭` through `map⁺ vlab` when the underlying Fin lists
--     are `Unique`).
--
-- We expose the X-level `PermuteCoherence` postulate here for direct
-- use; the connection to `Fin-permute-self-loop-id` is documented
-- below in `module ReductionToSelfLoop` (sketch only, since the lift
-- step is not yet implemented).
--
-- ## Constraints
--
-- * `--safe --with-K`.
-- * No new `postulate` declarations; all residual obligations exposed
--   as record fields.
-- * Module parameter: `sig-dec : APROPSignatureDec`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.FinalPermuteNew
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)

open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (_≈-fb_)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Local helper: full-cod-eq.  Inlined here from DecodeRespIso to keep
-- this discharge module minimal-dependency.  Constructive (no K needed,
-- just trans+sym).

private
  full-cod-eq : ∀ {A B} (f g : HomTerm A B)
              → codL ⟪ g ⟫F ≡ codL ⟪ f ⟫F
  full-cod-eq f g = trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f))

--------------------------------------------------------------------------------
-- ## Section 1: The narrowed sub-assumption.
--
-- `PermuteCoherence` is a single-field record carrying the narrow
-- assumption.  See header for the discharge strategy and the
-- connection to `Fin-permute-self-loop-id`.

record PermuteCoherence : Set where
  field
    -- Kelly's symmetric-monoidal coherence theorem on the `permute`
    -- fragment, in its TRUE `≅↭`-CONDITIONED form (Kelly 1964): two
    -- `permute` derivations between the same boundary that evaluate to
    -- the SAME finite bijection (`eval-↭ p ≈-fb eval-↭ q`) are
    -- `≈Term`-equal.  This is exactly `FaithfulnessResidual` of
    -- `Categories.PermuteCoherence.Faithfulness` (APROP's `permute` is
    -- definitionally that module's `permute`).
    --
    -- ⚠ The OLD field dropped the `eval-↭ p ≈-fb eval-↭ q` hypothesis,
    -- making it FALSE in general (duplicate X-level lists: `permute σ ≢
    -- id`).  The hypothesis is what makes it true; the consumer
    -- discharges it constructively from the `Unique`-ness of the
    -- decoder stacks (see `Categories.PermuteCoherence.Rigid.eval-rigid`).
    permute-≈Term-coherence
      : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
      → eval-↭ p ≈-fb eval-↭ q
      → permute p ≈Term permute q

--------------------------------------------------------------------------------
-- ## Section 2: The constructive discharge, parameterised by the
-- coherence witness.

module WithCoherence (coh : PermuteCoherence) where
  open PermuteCoherence coh

  ------------------------------------------------------------------------
  -- ### Generic compose-style discharge.
  --
  -- The key constructive step: after J-eliminating the cod-equation,
  -- the LHS becomes `permute q ∘ permute s` for some derivations.
  -- By definition of `permute` on `Perm.trans`, this equals
  -- `permute (Perm.trans s q)`; combined with `permute-≈Term-coherence`
  -- (fed the `≅↭` evidence `ev`) it gives the goal.
  --
  -- The helper is generic over the boundary lists, so the eventual
  -- specialisation to `process-all-edges` lists is mechanical.  The
  -- `ev` argument carries the `≅↭` (equal-evaluated-bijection)
  -- evidence; under `cs≡ds = refl` its type collapses to
  -- `eval-↭ (Perm.trans s q) ≈-fb eval-↭ p`.

  generic-permute-compose-absorb
    : ∀ {as bs cs ds : List X}
        (cs≡ds : cs ≡ ds)
        (s : as Perm.↭ bs)
        (q : bs Perm.↭ cs)
        (p : as Perm.↭ ds)
        (ev : eval-↭ (Perm.trans s q)
              ≈-fb eval-↭ (subst (λ z → as Perm.↭ z) (sym cs≡ds) p))
    → subst₂ HomTerm
        refl
        (cong unflatten cs≡ds)
        (permute q)
      ∘ permute s
      ≈Term permute p
  generic-permute-compose-absorb refl s q p ev =
    -- subst₂ refl refl (permute q) = permute q  definitionally.
    -- So the LHS is `permute q ∘ permute s`.
    -- By definition of permute on Perm.trans:
    --   permute (Perm.trans s q) = permute q ∘ permute s
    -- Hence LHS ≡ permute (Perm.trans s q).
    -- Then `permute-≈Term-coherence (Perm.trans s q) p ev` closes the
    -- goal (ev : (Perm.trans s q) ≅↭ p).
    permute-≈Term-coherence (Perm.trans s q) p ev

  ------------------------------------------------------------------------
  -- ### Step 3: The constructive discharge of the NEW
  --              `final-permute-absorb`.
  --
  -- Takes the (b) stack-permutation `stack-↭` and the two final
  -- permutations as parameters.  The discharge specialises the
  -- generic helper to the boundaries arising from the decoder.

  final-permute-absorb-discharge
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (stack-↭ :
            map (Hypergraph.vlab ⟪ f ⟫F)
                (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
          Perm.↭
            map (Hypergraph.vlab ⟪ g ⟫F)
                (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
        (perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
                  Perm.↭ Hypergraph.cod ⟪ f ⟫F)
        (perm-g : proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))
                  Perm.↭ Hypergraph.cod ⟪ g ⟫F)
        -- The `≅↭` evidence: the composite `stack-↭` then `perm-g`
        -- evaluates to the same finite bijection as `perm-f` (after the
        -- cod-equation transport).  Discharged constructively from the
        -- `Unique`-ness of the decoder stacks.
        (ev : eval-↭ (Perm.trans stack-↭ (PermProp.map⁺ (Hypergraph.vlab ⟪ g ⟫F) perm-g))
              ≈-fb eval-↭ (subst (λ z →
                       map (Hypergraph.vlab ⟪ f ⟫F)
                           (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
                       Perm.↭ z)
                     (sym (full-cod-eq f g))
                     (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫F) perm-f)))
    → let F-vlab = Hypergraph.vlab ⟪ f ⟫F
          G-vlab = Hypergraph.vlab ⟪ g ⟫F
      in subst₂ HomTerm
           refl
           (cong unflatten (full-cod-eq f g))
           (permute-via-vlab G-vlab perm-g)
         ∘ permute stack-↭
         ≈Term
         permute-via-vlab F-vlab perm-f
  final-permute-absorb-discharge {A} {B} f g iso stack-↭ perm-f perm-g ev =
    let F-vlab = Hypergraph.vlab ⟪ f ⟫F
        G-vlab = Hypergraph.vlab ⟪ g ⟫F
        mapped-perm-f = PermProp.map⁺ F-vlab perm-f
        mapped-perm-g = PermProp.map⁺ G-vlab perm-g
        cod-eq = full-cod-eq f g
    in generic-permute-compose-absorb cod-eq stack-↭ mapped-perm-g mapped-perm-f ev

--------------------------------------------------------------------------------
-- ## Trust-surface summary.
--
-- `final-permute-absorb-discharge` is fully constructive GIVEN the
-- `≅↭` evidence `ev` (that the composite stack/perm derivation
-- evaluates to the same finite bijection as `perm-f`) and the
-- `PermuteCoherence` witness (the TRUE Kelly faithfulness residual).
--
-- The OLD `ReductionToSelfLoop`/`XSelfLoop` apparatus has been removed:
-- it derived the binary coherence from the UNCONDITIONAL X-level
-- self-loop `permute r ≈Term id`, which is FALSE in general (duplicate
-- X-level lists).  The `≅↭`-conditioned `permute-≈Term-coherence` is
-- the honest replacement; its hypothesis is discharged constructively
-- by the consumer via `Categories.PermuteCoherence.Rigid.eval-rigid`
-- on the `Unique` decoder stacks.
--------------------------------------------------------------------------------
