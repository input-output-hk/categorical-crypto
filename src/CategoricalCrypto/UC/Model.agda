{-# OPTIONS --safe --without-K --guardedness #-}

-- The probabilistic machine model of categorical UC: the root of the cone that
-- instantiates the INHERITED abstract theory — `UCSetup` and `Abstract2` via
-- `Standard2.StdUC` — at this branch's machine layer.  Semantic target:
-- `docs/kb/frontier/15-probabilistic-uc-model.typ`, §§1–2.
--
--   `Model.Seal`         the machine bundle behind an `opaque` seal, and the
--                        coercions across it — the measured recipe without
--                        which the setup does not typecheck at all
--   `Model.Observation`  the ticked verdict object `Ωᵒ`, `Obs` as the one-ask
--                        closed run, the two-sided identification `_∼ᴼ_`, and
--                        the `Observation`/`ApproximateObservation` pair they
--                        induce (`observationᵒ`, `approximateᵒ`)
--   `Model.Setup`        `UC.Core.Bridge` at the two, hence the whole
--                        metatheory, the core's `_≈ℰᶜ_` and its agreement with
--                        `_≈ᵁ_`, and `ℰᵒ` — tests into `Ωᵒ` modulo closed
--                        observation — as the setup's own presheaf
--   `Model.Pin`          the metatheory's application sites, priced
--   `Model.Unit`         why the choice of empty object for the closures is
--                        immaterial: the metatheory never sees it
--   `Model.Bridge`       what the model adds to that identification: the two
--                        orders, and `_≈ᴳ_` — the identification at ungraded
--                        homs, where `_≈ᵁ_` is not stated
--   `Model.Enrichment`   the budget and the mass `UC.Audit` asks of a base,
--                        supplied here rather than assumed
--   `Model.Dominated`    `UC.Machine.Bridge.ContextDominated` at SEAL objects
--                        — `ifaceᵒ` is onto — which is the ancilla quantifier
--                        an ℰ-agreement has
--   `Model.Family`       `UC.Family.Monoidal` at the seal: the setup, and the
--                        inherited metatheory, asymptotically — and
--                        `UC.Family.Vanishing` on the same ingredients, which
--                        reads the agreement in the INHERITED `_≈ᵁ_`, so
--                        `UC-compose` applies to a concrete family
--   `Model.Family.Ingest`  a per-level advantage bound read as that family's
--                        `_≈ℰ[_]_`, `_≈ℰ_`, `_≈ℰⁿ_` and `_≤UC_`
--   `Model.Family.Negligible`  the local negligible tier (`UC.Family.Negligible`)
--                        inhabited at the machine family
--   `Model.Quantitative` `ℰᵒ` with the slack still visible: the same tests
--                        valued in `Approx`, whose `F₊` image is `ℰᵒ` again
--
-- The model obligations the proposal lists are then: the monoidal structure
-- (`Machines.G`, a theorem on this branch), and the presheaf together with the
-- observational identification (`Model.Setup`) — not another proof of
-- the UC metatheory.  `UC.Machine.Dictionary` records how the direct relays of
-- the parallel `UC.*` stack sit inside this one.

module CategoricalCrypto.UC.Model where

import CategoricalCrypto.UC.Model.Bridge
import CategoricalCrypto.UC.Model.Dominated
import CategoricalCrypto.UC.Model.Enrichment
import CategoricalCrypto.UC.Model.Family
import CategoricalCrypto.UC.Model.Family.Ingest
import CategoricalCrypto.UC.Model.Family.Negligible
import CategoricalCrypto.UC.Model.Observation
import CategoricalCrypto.UC.Model.Pin
import CategoricalCrypto.UC.Model.Quantitative
import CategoricalCrypto.UC.Model.Seal
import CategoricalCrypto.UC.Model.Setup
import CategoricalCrypto.UC.Model.Unit
