{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Audit`'s graded carry at the intended instance: the generic theory
-- applied to the sealed model.
--
-- `UC.Audit` proves the carry over a base plus the two enrichment data.  All
-- three are supplied here rather than assumed: the base is
-- `UC.Model.Setup.baseᵗ`, and the budget and the mass are
-- `UC.Model.Enrichment`.  Nothing it exports is a parameter, and this is the
-- only place that application is written — `UC.Seam.Audit.Context`, `.Bounded`,
-- `.Prefix`, `UC.Asymptotic.Audit` and `Examples.HashForward.Audit` all read
-- the model's audit theory from here.

open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; massᵒ)
open import CategoricalCrypto.UC.Model.Setup using (baseᵗ)

import CategoricalCrypto.UC.Audit as Aud

module CategoricalCrypto.UC.Seam.Audit where

private module A = Aud baseᵗ budgetᵒ massᵒ

open A public
  using (_≤UC[_]_; sim; sim-qb; emulate; simCost; q≤simCost; AuditEvent; AuditBound;
         pinned; pinned-bound; absorb; Absorbs; absorb-absorbs; carry-obs; audit-carry)
