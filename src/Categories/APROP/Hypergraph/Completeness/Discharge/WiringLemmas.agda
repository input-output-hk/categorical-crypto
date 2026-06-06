-- Standalone proofs of the six "small-moderate" wiring lemmas of the
-- completeness program.  This module imports the existing chain
-- read-only; it edits no existing file.  Where a lemma matches the type
-- of an existing postulate in `IsoInvarianceWiring` / `DecodeRelRespIsoWired`
-- it is stated so it can later replace that postulate; where the existing
-- postulate's type is FALSE in general (the arbitrary-`H` `Dep-irrefl` and
-- `fin-order-NoInv`), the TRANSLATION-SPECIFIC `⟪f⟫`-version is stated and
-- flagged instead (these need `PerHG` restructured to consume them).
--
-- STATUS SUMMARY (see the per-lemma comments):
--   1. swap-validity              — TODO postulate (multiset bookkeeping)
--   2. dep-irrefl-⟪⟫              — TODO postulate (translation-specific)
--   3. fin-order-NoInv-⟪⟫         — TODO postulate (translation-specific)
--   4. NoInv-τ                    — REAL PROOF (AllPairs transport)
--   5. iso-transport              — TODO postulate (hardest; process-edges-resp-φ)
--   6. decodeOrd-boundary-resp-≈  — TODO postulate "given K" (StackEval template)
--
-- NOT `--safe`: contains clearly-marked `-- TODO:` postulates.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.WiringLemmas
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig using (process-edges)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep; ≺⇒ψ≺; ψ≺⇒≺)

import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Completeness.Discharge.DepIrrefl sig as DI

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.List using (List; map)
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.AllPairs as AP
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties as APProp using ()
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

------------------------------------------------------------------------
-- LEMMA 1.  swap-validity  (matches `IW.PerHG.swap-validity` drop-in.)
--
-- `∀ {o₁ o₂} → o₁ ↝ o₂ → Valid o₁ → Valid o₂`, where
--   `Valid o = proj₁ (process-edges H o H.dom) ↭ H.cod`.
--
-- TRUE bookkeeping: a `↝` step swaps two adjacent `Dep`-incomparable
-- edges (the `Incomp` witness inside the `swap-step`); the live-wire
-- multiset / final stack of `process-edges` is order-independent for such
-- a swap, so `finalStack o₁ ↭ cod` transports to `finalStack o₂ ↭ cod`.
--
-- The real content is `finalStack o₁ ↭ finalStack o₂` for one adjacent
-- incomparable swap.  Sketch of the route (NOT carried out here):
--   * `process-edges H (ps ++ x ∷ y ∷ qs) dom`
--       = process-edges H qs (edge-step (edge-step sₚ x) y)  where
--         sₚ = finalStack of the `ps`-prefix, run from dom;
--   * for `Dep`-incomparable adjacent `x , y`, the two single edge-steps
--     `edge-step _ x` then `edge-step _ y` produce a final stack that is a
--     permutation of running `y` then `x` (neither edge's `eout` feeds the
--     other's `ein`, by `Incomp`), so the two two-step residuals are `↭`;
--   * `process-edges` of a fixed suffix is `↭`-monotone in its input stack
--     (its final stack respects `↭` of the start — provable by the same
--     `extract-prefix-↭-residual` used pervasively in `AllFireNatural`);
--   * compose to `finalStack o₁ ↭ finalStack o₂`, then `↭`-trans with the
--     `Valid o₁ : finalStack o₁ ↭ cod` witness.
-- This is several hundred LOC of multiset/edge-step algebra; left as TODO.

-- (Lemma 1 `swap-validity` is now PROVEN in `Discharge.SwapValidity`;
-- the former TODO postulate here is REMOVED.)

------------------------------------------------------------------------
-- LEMMA 2.  dep-irrefl-⟪⟫   (TRANSLATION-SPECIFIC.)
--
-- The arbitrary-`H` `IW.PerHG.Dep-irrefl : ∀ {e} → ¬ Dep H e e` is FALSE
-- in general (a generic hypergraph can have a self-feeding edge / loop).
-- It is TRUE for translated graphs `⟪f⟫`, because a generator box's input
-- and output vertices are disjoint, so no edge depends on itself.
--
-- We state the honest `⟪f⟫`-version.  NOTE: this does NOT match the
-- postulate type drop-in — `PerHG` is parameterised over an arbitrary `H`
-- and instantiates `LinExt … (Dep H) Dep-irrefl` eagerly, so to consume
-- this lemma `PerHG` must be RESTRUCTURED to take the irreflexivity proof
-- as a module parameter (then `decode-ord-resp-iso` would feed
-- `dep-irrefl-⟪⟫ f` at `H = ⟪f⟫`).
--
-- TODO: structural induction on `f` over the translation's edge
-- construction (`hGen`/`hComposeP`/`hTensor`/…), reading off `ein`/`eout`
-- disjointness for each edge.  For `hGen` the single box has `ein`/`eout`
-- drawn from disjoint fresh-vertex blocks; for the compositional cases the
-- per-edge `ein`/`eout` are injective images (`_↑ˡ_`/`_↑ʳ_`/`remap`) of a
-- sub-graph edge, so self-dependence reflects to the sub-graph and the IH
-- applies.  Requires the per-edge endpoint-disjointness facts from
-- `Translation`/`Linearity`.

-- (Lemma 2 `dep-irrefl-⟪⟫` is now PROVEN in `Discharge.DepIrrefl`; the
-- former TODO postulate here is REMOVED.)

------------------------------------------------------------------------
-- LEMMA 3.  fin-order-NoInv-⟪⟫   (TRANSLATION-SPECIFIC.)
--
-- The arbitrary-`H` `IW.PerHG.fin-order-NoInv : NoInv (range H.nE)` is
-- FALSE for a generic `H` (the natural Fin order need not be inversion-
-- free).  It is TRUE for `⟪f⟫`, where the proven `AllFire-natural-range`
-- (`Discharge/Sub/AllFireNatural.agda`, for the unpruned `⟪_⟫F`) witnesses
-- that the edges are laid out in a topological order.
--
-- We state the honest `⟪f⟫`-version.  Like Lemma 2 this needs `PerHG`
-- restructured to consume it (the `NoInv` here lives in `IW.PerHG ⟪f⟫`,
-- whose `Dep-irrefl` instance is itself the arbitrary-`H` postulate).
--
-- TODO: bridge `AllFire ⟪f⟫F (range nE) dom` ⇒ `NoInv (range nE)` in the
-- `Dep`-order sense.  `NoInv (range nE) = AllPairs (λ a b → ¬ Dep b a)`,
-- i.e. for all i<j in the list, edge j does not feed edge i.  This is the
-- "topological" content of `AllFire-natural-range`: the inductive layout
-- (`_↑ˡ_` G-block before `_↑ʳ_`/`remap` K-block) puts a producer strictly
-- before any consumer.  It transfers from `⟪_⟫F` to `⟪_⟫` (same edges /
-- same Fin order; pruning removes only isolated wires, not edges).
-- Requires an `AllFire ⇒ NoInv(Dep)` lemma which, while morally implied,
-- is a fresh structural development; left as TODO.

-- (Lemma 3 `fin-order-NoInv-⟪⟫` is now PROVEN in `Discharge.FinOrderNoInv`;
-- the former TODO postulate here is REMOVED.)

------------------------------------------------------------------------
-- LEMMA 4.  NoInv-τ   (matches `IW.NoInv-τ` drop-in, modulo taking J's
-- `NoInv (range J.nE)` as an explicit hypothesis instead of the
-- `PerHG J`-internal `fin-order-NoInv` postulate).
--
-- REAL PROOF.  `τ = map ψ⁻¹ (range J.nE)`.  `NoInv` is
-- `AllPairs (λ a b → ¬ Dep · b a)`.  We transport J's no-inversion across
-- the edge-bijection `ψ⁻¹`:
--   * `AllPairs.map`        — turn `AllPairs Below_J (range J)` into
--                             `AllPairs (Below_H on ψ⁻¹) (range J)`, using
--                             the pointwise dependency *reflection*
--                             (Lemma A forward `≺⇒ψ≺` + `ψ-rght`);
--   * `AllPairs.Properties.map⁺` — push the `on ψ⁻¹` through `map ψ⁻¹`,
--                             giving `AllPairs Below_H (map ψ⁻¹ (range J))`
--                             = `NoInv_H τ`.
------------------------------------------------------------------------

module Lemma4 {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J)
              (dihH : ∀ {e} → ¬ (Dep H e e))
              (dihJ : ∀ {e} → ¬ (Dep J e e)) where
  private
    module PH = IW.PerHG H dihH
    module PJ = IW.PerHG J dihJ
  open _≅ᴴ_ Φ using (ψ; ψ⁻¹; ψ-rght)

  -- Dependency reflection along ψ⁻¹: if H has the dependency
  -- `ψ⁻¹ b ≺ ψ⁻¹ a`, then J has `b ≺ a`.  (Lemma A forward, with the
  -- `ψ ∘ ψ⁻¹ = id` cancellations.)
  dep-reflect : ∀ {a b}
              → Dep H (ψ⁻¹ b) (ψ⁻¹ a)
              → Dep J b a
  dep-reflect {a} {b} d =
    subst₂ (Dep J) (ψ-rght b) (ψ-rght a) (≺⇒ψ≺ Φ d)

  -- Pointwise: J's `Below` implies H's `Below` pulled back along ψ⁻¹.
  --   Below_J a b = ¬ Dep J b a
  --   (Below_H on ψ⁻¹) a b = ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)
  below-pull : ∀ {a b}
             → (¬ Dep J b a)
             → ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)
  below-pull ndJ dH = ndJ (dep-reflect dH)

  -- The `map`-of-relation step (over the FIXED list `range J.nE`).
  step-on : AllPairs (λ a b → ¬ Dep J b a) (range (Hypergraph.nE J))
          → AllPairs (λ a b → ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)) (range (Hypergraph.nE J))
  step-on = AP.map below-pull

  -- The `map ψ⁻¹` step.  `AllPairs.Properties.map⁺` at
  --   R = Below_H = (λ a b → ¬ Dep H b a),  f = ψ⁻¹
  -- has type  `AllPairs (Below_H on ψ⁻¹) xs → AllPairs Below_H (map ψ⁻¹ xs)`,
  -- and `(Below_H on ψ⁻¹) a b = ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)` definitionally.
  NoInv-τ : PJ.NoInv (range (Hypergraph.nE J))
          → PH.NoInv (map ψ⁻¹ (range (Hypergraph.nE J)))
  NoInv-τ noJ = APProp.map⁺ (step-on noJ)

------------------------------------------------------------------------
-- LEMMA 5.  iso-transport   (matches `IW.iso-transport` drop-in.)
--
-- THE HARDEST.  "Vertex relabelling is free + ψ re-indexing": decoding J
-- in its natural order equals decoding H in the pulled-back order τ, after
-- the boundary `subst₂`.  Precisely (the `IW.iso-transport` type):
--
--   (vJ : PJ.Valid (range J.nE))
--   → Σ[ vτ ∈ PH.Valid τ ]
--       ( subst₂ HomTerm (cong unflatten (IW.domL-iso Φ))
--                        (cong unflatten (IW.codL-iso Φ))
--                (PJ.decodeOrd (range J.nE) vJ)
--         ≈Term PH.decodeOrd τ vτ )
--
-- TODO.  This needs a `process-edges-respects-φ` lemma of the shape:
--   running `process-edges J (range J.nE)` from `J.dom` and running
--   `process-edges H τ` from `H.dom` (τ = ψ⁻¹-image of J's order) yield
--   final stacks related by `map φ`, and the two emitted `HomTerm`s agree
--   up to ≈Term after relabelling vertices by `φ` (free: `decode` factors
--   through `vlab`, and `φ-lab` says `J.vlab ∘ φ = H.vlab`) and reindexing
--   edges by `ψ` (free: `ψ-elab` says the edge generators agree under the
--   boundary `subst₂`).  Concretely one would prove, by induction on the
--   edge list, that `edge-step`/`process-edges` commute with the iso's
--   relabelling — a fixed-point/naturality statement in the spirit of
--   `StackPerm.process-edges-resp-iso-stack` but at the TERM (not just
--   stack-↭) level.  The validity witness `vτ` is then obtained by
--   transporting `vJ` along that stack relation.  Large; left as TODO.

-- (Lemma 5 `iso-transport` is now PROVEN in `Discharge.IsoTransport`
-- (modulo `process-edges-respects-φ`/`permute-relabel-free`); the former
-- TODO postulate here is REMOVED.)

------------------------------------------------------------------------
-- LEMMA 6.  decodeOrd-boundary-resp-≈   (matches the
-- `DecodeRelRespIsoWired.decodeOrd-boundary-resp-≈` postulate, stated
-- "given K".)
--
-- This is the TRUE Kelly-faithfulness residual that gates the final
-- permute throughout the development.  It relates the two decodings of
-- ⟪f⟫ in its natural order under DIFFERENT validity witnesses, then
-- transports the boundary `subst₂` from the wiring's iso-boundary
-- (`IW.domL-iso`/`IW.codL-iso`) to the user-facing one
-- (`⟪⟫-domL`/`⟪⟫-codL`).  The two validity witnesses are proofs of the
-- SAME `↭`, so their `permute-via-vlab` final-permutes agree up to ≈Term
-- — which is exactly K (`PermuteCoherence.Faithfulness.FaithfulnessResidual`,
-- discharged on the `Unique` vertex-level `cod` of `⟪f⟫`).
--
-- TODO ("given K").  The route is exactly the `StackEvalCoherence`
-- template (`stack-eval-coherence`):
--   * expose both final permutes via `eval-↭` and the rigid form
--     `eval-rigid` (`PermuteCoherence.Rigid`) on the `Unique` boundary
--     (`⟪_⟫-cod-unique` / `FromAPROPCodUnique`);
--   * push the `map`-of-permute through `eval-map⁺` (`PermuteCoherence.Map`);
--   * apply K (`permute-≈Term-coherence`) to collapse the two same-`↭`
--     permutes to ≈Term;
--   * `subst₂`-transport the boundary equalities (pure `subst-cod-*`
--     algebra, as in `rhs-reduced` of the template).
-- We expose it as a function of an explicit K-hypothesis so that, once K
-- is imported/instantiated, this lemma is dischargeable by adapting the
-- template.  The K-hypothesis `Kelly` below abstracts "two same-`↭`
-- final-permutes are ≈Term"; the body is left as TODO.

-- The `DecodeRelRespIsoWired.decodeOrd-boundary-resp-≈` postulate fixes
-- the two `Valid` witnesses to the `vrange`-derived ones; here we state a
-- STANDALONE version that universally quantifies over the three `Valid`
-- witnesses (`vf`, `vg` for the two user-facing decodings, and `vH` for
-- the wiring side), which is drop-in once `vrange f`/`vrange g` are
-- instantiated for `vf`/`vg`.
-- (Lemma 6 `decodeOrd-boundary-resp-≈` is now PROVEN GIVEN K in
-- `Discharge.DecodeOrdBoundary`; the former TODO postulate here is REMOVED.)
