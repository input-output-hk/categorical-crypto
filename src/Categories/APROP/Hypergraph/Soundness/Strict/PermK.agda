{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict Kelly residual `permˢ-K`, FULLY DISCHARGED (axiom-free) at the
-- pipeline's `FlatGen` instance.
--
-- `PermDischarge` reduces `permˢ-K` to the single closed coherence
-- `StrictBraid`; `Braid.Generic` proves `StrictBraid` for every generator
-- family.  Wiring them together (at `mor := FlatGen`) gives the constructed
-- residual the decoder shape lemmas and the part-(II)ˢ chain consume — with
-- no remaining postulate or parameter.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.PermK
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_
  using (module Support)

import Categories.APROP.Hypergraph.Soundness.Strict.PermDischarge X _≟X_ as PD
import Categories.APROP.Hypergraph.Soundness.Strict.Braid sig _≟X_ as BR

open import Data.List using (List)

--------------------------------------------------------------------------------
-- For any vertex set `V` with a labelling, the constructed residual.

module _ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) where

  private
    module D = PD.Discharge V _≟V_ vlab FlatGen
    -- `StrictBraid` at `FlatGen` is proven by `Braid.Generic FlatGen`.
    module M = D.Main (BR.Generic.strict-braid FlatGen)

  permˢ-K : Support.PermK V vlab
  permˢ-K = M.permˢ-K
