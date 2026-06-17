{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict SMC instance the strictified soundness pipeline works in:
-- `FreeStrictSMC.Build` over the flat graph generators `FlatGen`.  Kept
-- light (no boundary imports) so the decoder side depends on it alone;
-- the embedding back into the free SMC lives in `Strict.Boundary`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Core
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.FreeStrictSMC using (module Build)

open Build X _≟X_ FlatGen public
