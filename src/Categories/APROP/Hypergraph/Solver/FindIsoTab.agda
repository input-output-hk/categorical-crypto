{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Tabulated (literalized) iso finder.
--
-- `findIso H J` is slow because the hypergraph fields are functions and
-- every access re-walks the `hComposeP` tower (re-evaluation without
-- sharing; docs/smc-solver-performance.md).  `findIsoᵀ` runs the same
-- search on the tabulated graphs `tabH H`/`tabH J` — whose fields read
-- shared, memoizing vectors, so each original field value is computed at
-- most once — and transports the found iso back along the postulate-free
-- `tab-≅ᴴ : tabH H ≅ᴴ H`.
--
-- The transport composition is lazy: consumers (e.g. `solveH!ᵀ`) force
-- only `is-just`, never the iso fields, so the `trans-≅ᴴ`/`sym-≅ᴴ`
-- plumbing costs nothing at the use site.
--
-- Measured on generator chains gᴺ (--profile=definitions, same-run):
-- `findIsoᵀ` ≈ 2.4× / 3.2× / 4.2× faster than `findIso` at N = 8 / 16 / 32
-- (781→332ms, 8.6→2.7s, 117→28s), the multiplier growing with size.  The
-- residual over the force-once floor is the literal-data search + Verify's
-- Dec construction + the per-access `elab` transport.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.FindIsoTab (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ; trans-≅ᴴ)
open import Categories.APROP.Hypergraph.Tabulate using (tabH; tab-≅ᴴ)
open import Categories.APROP.Hypergraph.Solver.FindIso sig-dec using (findIso)

open import Data.Maybe.Base using (Maybe)
import Data.Maybe.Base as Maybe

findIsoᵀ : (H J : Hypergraph FlatGen) → Maybe (H ≅ᴴ J)
findIsoᵀ H J =
  Maybe.map
    (λ iso → trans-≅ᴴ (sym-≅ᴴ (tab-≅ᴴ H)) (trans-≅ᴴ iso (tab-≅ᴴ J)))
    (findIso (tabH H) (tabH J))
