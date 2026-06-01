{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- The permute-coherence *bridge* keystone, parameterised by a
-- `FaithfulnessResidual` value.
--
-- ## What this module proves
--
-- The single one-liner that turns Kelly's `FaithfulnessResidual`
-- obligation (`permute-resp-≅↭`) into a *useful* coherence statement on
-- `Unique` codomains, by feeding it the rigidity witness `eval-rigid`:
--
--   permute-≈Term-coherence-K
--     : (K : FaithfulnessResidual) {xs ys : List X}
--     → Unique ys → (p q : xs ↭ ys)
--     → permute p ≈Term permute q
--   permute-≈Term-coherence-K K uniq p q =
--     FaithfulnessResidual.permute-resp-≅↭ K p q (eval-rigid uniq p q)
--
-- The key alignment: `_≅↭_` is *definitionally* `eval-↭ p ≈-fb eval-↭ q`
-- (Canonical.agda:198-199), and `eval-rigid uniq p q` has *exactly* that
-- type (Rigid.agda:91-95).  So the result of `eval-rigid` is directly the
-- `p ≅↭ q` argument expected by `permute-resp-≅↭`
-- (Faithfulness.agda:108-114) — no glue needed at the X-level.
--
-- ## Why `Unique ys` (not `Unique xs`)
--
-- `eval-rigid` requires the *codomain* list `ys` to be duplicate-free
-- (it uses injectivity of `lookup ys`).  That is exactly the hypothesis
-- under which two `↭` derivations are forced to realise the same
-- position bijection, hence the coherence is genuinely TRUE here (this
-- is the `Unique`-guarded restriction of Kelly's coherence theorem; the
-- unrestricted X-level statement is FALSE — see the counter-example in
-- `Discharge/Sub/PermuteCoherence.agda`).
--
-- ## The downstream `permute-via-vlab` form
--
-- The actual completeness call sites permute *Fin-index* stacks that are
-- `Unique` at the Fin level, but apply `vlab : Fin n → X` afterwards (so
-- `map vlab ys` may have DUPLICATES — `vlab` need not be injective).  We
-- therefore cannot apply `eval-rigid` at the X-level after the map.
-- Instead the `permute-via-vlab-≈Term-coherence-K` corollary applies
-- `eval-rigid` at the *Fin* level (where `Unique` holds), then transports
-- the resulting `≈-fb` through `eval-map⁺` to obtain
-- `map⁺ vlab p ≅↭ map⁺ vlab q`, finally feeding `permute-resp-≅↭`.
--
-- ## Trust surface
--
-- This module introduces NO `postulate`.  It is parameterised over a
-- `FaithfulnessResidual` value `K`; all the residual categorical content
-- lives in `K`.  Everything else (`eval-rigid`, `eval-map⁺`,
-- `subst₂-FinBij-≈`) is constructively proven upstream.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceK
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality using (sym)

-- The generic `permute` / `permute-via-vlab` builders, the
-- `FaithfulnessResidual` record, and `_≅↭_`.
open import Categories.PermuteCoherence.Faithfulness d
  using (permute; FaithfulnessResidual)
open import Categories.FreeSMC.Steps d using (permute-via-vlab)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Rigid using (eval-rigid)
open import Categories.PermuteCoherence.Map
  using (eval-map⁺; subst₂-FinBij-≈; ≈-fb-resp-≡)

--------------------------------------------------------------------------------
-- 1. The X-level keystone bridge lemma (exactly as posed).
--
-- `eval-rigid uniq p q : eval-↭ p ≈-fb eval-↭ q`, which is `p ≅↭ q` by
-- definition of `_≅↭_`.  Feed it straight into the residual.

permute-≈Term-coherence-K
  : (K : FaithfulnessResidual)
    {xs ys : List X}
  → Unique ys → (p q : xs Perm.↭ ys)
  → permute p ≈Term permute q
permute-≈Term-coherence-K K uniq p q =
  FaithfulnessResidual.permute-resp-≅↭ K p q (eval-rigid uniq p q)

--------------------------------------------------------------------------------
-- 2. The downstream `permute-via-vlab` corollary.
--
-- `Unique` lives at the Fin-index level (so we apply `eval-rigid` there);
-- `vlab` is applied afterwards via `map⁺`, and `eval-map⁺` lets us
-- transport the Fin-level `≈-fb` to the X-level `≅↭` of the mapped
-- derivations.
--
--   permute-via-vlab vlab p = permute (map⁺ vlab p)
--
-- so the goal reduces to `permute (map⁺ vlab p) ≈Term permute (map⁺ vlab q)`,
-- which is `permute-resp-≅↭ K` applied to `map⁺ vlab p ≅↭ map⁺ vlab q`.

private
  -- `map⁺ vlab p ≅↭ map⁺ vlab q` from Fin-level rigidity.
  --
  -- `eval-rigid uniq p q : eval-↭ p ≈-fb eval-↭ q`.  Transport along the
  -- `length-map` casts (`subst₂-FinBij-≈`), then rewrite both sides back
  -- to `eval-↭ (map⁺ vlab _)` via `eval-map⁺`.
  map⁺-≅↭
    : ∀ {n} {xs ys : List (Fin n)}
        (vlab : Fin n → X)
    → Unique ys → (p q : xs Perm.↭ ys)
    → PermProp.map⁺ vlab p ≅↭ PermProp.map⁺ vlab q
  map⁺-≅↭ {xs = xs} {ys = ys} vlab uniq p q =
    ≈-fb-resp-≡
      (sym (eval-map⁺ vlab p))
      (sym (eval-map⁺ vlab q))
      (subst₂-FinBij-≈
        (sym (length-map vlab xs))
        (sym (length-map vlab ys))
        (eval-rigid uniq p q))

permute-via-vlab-≈Term-coherence-K
  : (K : FaithfulnessResidual)
    {n : _} {xs ys : List (Fin n)}
    (vlab : Fin n → X)
  → Unique ys → (p q : xs Perm.↭ ys)
  → permute-via-vlab vlab p ≈Term permute-via-vlab vlab q
permute-via-vlab-≈Term-coherence-K K vlab uniq p q =
  FaithfulnessResidual.permute-resp-≅↭ K
    (PermProp.map⁺ vlab p) (PermProp.map⁺ vlab q)
    (map⁺-≅↭ vlab uniq p q)
