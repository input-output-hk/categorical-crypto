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
--                        closed run, and the two-sided identification `_∼ᴼ_`
--   `Model.Environment`  `ℰᵒ`: tests into `Ωᵒ` modulo closed observation, a
--                        setoid quotient with its presheaf laws proved
--   `Model.Setup`        `StdUC` at the two, hence the whole metatheory
--   `Model.Pin`          the metatheory's application sites, priced
--   `Model.Reading`      `_≈ᵁ_` is the ∀-ancilla/test/closure experiment
--   `Model.Unit`         why the choice of empty object for the closures is
--                        immaterial: the metatheory never sees it
--   `Model.Bridge`       the hand-rolled qualitative core (`UC.Core` and below)
--                        identified with this metatheory, both directions
--
-- The model obligations the proposal lists are then: the monoidal structure
-- (`Machines.G`, a theorem on this branch), the presheaf (`Model.Environment`)
-- and the observational identification (`Model.Reading`) — not another proof of
-- the UC metatheory.  `UC.Machine.Dictionary` records how the direct relays of
-- the parallel `UC.*` stack sit inside this one.

module CategoricalCrypto.UC.Model where

import CategoricalCrypto.UC.Model.Bridge
import CategoricalCrypto.UC.Model.Environment
import CategoricalCrypto.UC.Model.Observation
import CategoricalCrypto.UC.Model.Pin
import CategoricalCrypto.UC.Model.Reading
import CategoricalCrypto.UC.Model.Seal
import CategoricalCrypto.UC.Model.Setup
import CategoricalCrypto.UC.Model.Unit
