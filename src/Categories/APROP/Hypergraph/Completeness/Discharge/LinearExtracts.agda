{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge module for `decode-attempt-Linear-extracts` from
-- `Completeness/DecodeRespIso.agda`.
--
-- ## Goal
--
-- Show: ∀ {A B} (f : HomTerm A B)
--       → ∃[ perm-f ] proj₁ (decode-attempt-Linear f)
--                     ≡ permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) perm-f
--                       ∘ proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
--
-- ## Strategy
--
-- The field expresses an EXISTENTIAL.  The path:
--
--   1. Run the cospan algorithm via `decode-attempt-perm-from-just` on
--      the `decode-attempt-Linear` witness, recovering
--      `(s_final, t', eq-proc, perm-↭)` where
--      `eq-proc : process-all-edges H H.dom ≡ (s_final, t')`.
--   2. Use `extract-prefix-from-↭ s_final H.cod perm-↭` to obtain
--      `(q, eq-prefix)` with `extract-prefix H.cod s_final ≡ just ([], q)`.
--   3. A local `decode-attempt-shape` lemma uses `rewrite eq-proc | eq-prefix`
--      to expose `decode-attempt H ≡ just (permute-via-vlab vlab perm ∘ t')`
--      for some perm.  The shape lemma's conclusion talks about `s_final`
--      and `t'`.
--   4. Combine with `decode-attempt-Linear f`'s `≡ just _` via
--      `just-injective`.
--   5. Transport along `eq-proc` to align with the field's
--      `proj₁`/`proj₂ (process-all-edges …)` form, via subst on a
--      Σ-valued type family parameterised by the algorithm output pair.
--
-- ## Status
--
-- FULL CONSTRUCTIVE DISCHARGE.  No new postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.LinearExtracts
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen)
  renaming (⟪_⟫ to ⟪_⟫F)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (decode-attempt; process-all-edges; extract-prefix; ++-[]-↭)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode-attempt-Linear; decode-attempt-perm-from-just)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-from-↭)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

--------------------------------------------------------------------------------
-- ## Shape lemma for `decode-attempt`.
--
-- Existential form: given concrete proofs that
--   (a) `process-all-edges H H.dom ≡ (s_final, t')`, and
--   (b) `extract-prefix H.cod s_final ≡ just ([], q)`,
-- there EXISTS a perm `perm : s_final ↭ H.cod` such that
-- `decode-attempt H ≡ just (permute-via-vlab H.vlab perm ∘ t')`.
--
-- We don't specify the perm — Agda's `extract-exact` internally
-- constructs it; we just extract it via `Σ`.

decode-attempt-shape
  : (H : Hypergraph FlatGen)
    (s_final : List (Fin (Hypergraph.nV H)))
    (t' : HomTerm (unflatten (map (Hypergraph.vlab H) (Hypergraph.dom H)))
                  (unflatten (map (Hypergraph.vlab H) s_final)))
    (q : s_final Perm.↭ Hypergraph.cod H ++ [])
  → process-all-edges H (Hypergraph.dom H) ≡ (s_final , t')
  → extract-prefix (Hypergraph.cod H) s_final ≡ just ([] , q)
  → decode-attempt H
    ≡ just (permute-via-vlab (Hypergraph.vlab H)
                              (Perm.trans q (++-[]-↭ (Hypergraph.cod H)))
            ∘ t')
decode-attempt-shape H s_final t' q eq-proc eq-prefix
  rewrite eq-proc | eq-prefix = refl

--------------------------------------------------------------------------------
-- ## Discharge of the field.
--
-- After deriving everything in `(s_final, t')`-coordinates, we use a
-- single `subst` along `eq-proc` to convert the existential into the
-- expected `proj₁`/`proj₂ (process-all-edges …)`-form.

decode-attempt-Linear-extracts-discharge
  : ∀ {A B} (f : HomTerm A B)
  → ∃[ perm-f ] proj₁ (decode-attempt-Linear f)
                ≡ permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) perm-f
                  ∘ proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
decode-attempt-Linear-extracts-discharge {A} {B} f =
    subst Goal (sym eq-proc) goal-at-s-final
  where
    H : Hypergraph FlatGen
    H = ⟪ f ⟫F

    -- Algorithm-output type, used as the index for the dependent
    -- transport.
    AlgPair : Set
    AlgPair = Σ[ s ∈ List (Fin (Hypergraph.nV H)) ]
                  HomTerm (unflatten (map (Hypergraph.vlab H) (Hypergraph.dom H)))
                          (unflatten (map (Hypergraph.vlab H) s))

    -- The dependent statement we want, parameterised by the algorithm
    -- output pair.  `Goal (proc-all-edges H H.dom)` is exactly the
    -- field's stated conclusion.
    Goal : AlgPair → Set
    Goal (s , t) = ∃[ perm ] proj₁ (decode-attempt-Linear f)
                            ≡ permute-via-vlab (Hypergraph.vlab H) perm ∘ t

    perm-data = decode-attempt-perm-from-just H (decode-attempt-Linear f)
    s_final = proj₁ perm-data
    t'      = proj₁ (proj₂ perm-data)
    eq-proc : process-all-edges H (Hypergraph.dom H) ≡ (s_final , t')
    eq-proc = proj₁ (proj₂ (proj₂ perm-data))
    perm-↭ : s_final Perm.↭ Hypergraph.cod H
    perm-↭ = proj₂ (proj₂ (proj₂ perm-data))

    prefix-data = extract-prefix-from-↭ s_final (Hypergraph.cod H) perm-↭
    q-prefix : s_final Perm.↭ Hypergraph.cod H ++ []
    q-prefix = proj₁ prefix-data
    eq-prefix : extract-prefix (Hypergraph.cod H) s_final ≡ just ([] , q-prefix)
    eq-prefix = proj₂ prefix-data

    perm-shape : s_final Perm.↭ Hypergraph.cod H
    perm-shape = Perm.trans q-prefix (++-[]-↭ (Hypergraph.cod H))

    eq-shape : decode-attempt H ≡ just (permute-via-vlab (Hypergraph.vlab H) perm-shape ∘ t')
    eq-shape = decode-attempt-shape H s_final t' q-prefix eq-proc eq-prefix

    eq-just : decode-attempt H ≡ just (proj₁ (decode-attempt-Linear f))
    eq-just = proj₂ (decode-attempt-Linear f)

    t-Lin-eq : proj₁ (decode-attempt-Linear f)
             ≡ permute-via-vlab (Hypergraph.vlab H) perm-shape ∘ t'
    t-Lin-eq = just-injective (trans (sym eq-just) eq-shape)

    -- The existential at the `(s_final, t')` coordinates.
    goal-at-s-final : Goal (s_final , t')
    goal-at-s-final = perm-shape , t-Lin-eq
