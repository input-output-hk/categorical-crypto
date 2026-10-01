{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Root of the library: checking this module checks the channel/machine layer,
-- the protocol layer, the UC cone and the examples that exercise it.
--
-- The `public` re-exports are the channel/machine layer proper.  Everything
-- else is build closure, not API — its names belong to their own roots:
-- `Strategy`, `Protocol` and below (layer 1 and its machine images), and the UC
-- layer (`docs/uc-module-inventory.md`), whose lines below are its leaves the
-- examples do not reach.  At the model, the parameterized UC modules are fed
-- `𝒢ₚᴹ 0ℓ`, `UC.Machine.Grading.gradingᴹ` and `UC.Machine.Evaluationᴹ`.
--
-- Example leaves: `Examples.HashForward.Audit` (the nontrivial-grade toy),
-- `Examples.ROCommitment.*` (a commitment that carries an error: UC images,
-- extraction and hiding games, transport, and the resource-installed
-- realization — `docs/fcom-extraction.md`, `docs/fcom-hiding.md`,
-- `docs/rcom-icom-b1.md`) and `Examples.CoinToss.*` (Blum coin-tossing over it,
-- both corruptions, to an ideal coin — `docs/coin-toss.md`).  Tests:
-- `GamePlaying.Test`, `Protocol.Machine.Pin`, `SFunM.Test.Possibility`,
-- `UC.Machine.MonitorTests`, `UC.Machine.StateEvent.HitTests`.
-- Outside, checked per file through their leaves: `Examples.ChimericLedger`
-- (`Transfer`, `Serialize`), `Examples.MerkleDamgard` (`Pin`, `QueryBound`,
-- which imports the protocol and so cannot be wired into it) and the
-- inherited abstract theories (`UCSetup`, `Standard`).
--
-- `--guardedness` is here because it is INFECTIVE and the `Dₚ` cone below uses
-- it; nothing in this module is coinductive.
------------------------------------------------------------------------

module CategoricalCrypto where

-- Open problems

-- We want to conveniently specify a machine that, on an input, sends
-- messages to other machines, waits for replies and then continues
-- execution.

-- Can we write constructors more monadically?

-- Improve syntax generally

open import CategoricalCrypto.Channel.Category public
open import CategoricalCrypto.Channel.Core public
open import CategoricalCrypto.Channel.Selection public
open import CategoricalCrypto.Machine.Constraints public
open import CategoricalCrypto.Machine.Core public
open import CategoricalCrypto.SFunM public
open import CategoricalCrypto.SFunM.Test.Possibility
open import CategoricalCrypto.SFunPartial public
open import CategoricalCrypto.SFunPossibility
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Average
open import CategoricalCrypto.GamePlaying.Defer
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.GamePlaying.Potential
open import CategoricalCrypto.GamePlaying.Test
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Machine.Compose
open import CategoricalCrypto.Protocol.Machine.Pin
open import CategoricalCrypto.Protocol.Machine.Raw
open import CategoricalCrypto.Protocol.Machine.Trace.Compose
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Protocol.Safety
open import CategoricalCrypto.Approx.FilteredTests
open import CategoricalCrypto.Approx.Separating
open import CategoricalCrypto.Approx.Small.Controlled
open import CategoricalCrypto.UC.Approximate.LocalTests
open import CategoricalCrypto.UC.Family.Negligible.Quantitative
open import CategoricalCrypto.UC.Family.Quantitative
open import CategoricalCrypto.UC.Machine.EventBounds.Transport
open import CategoricalCrypto.UC.Machine.MonitorTests
open import CategoricalCrypto.UC.Machine.Run.Lax
open import CategoricalCrypto.UC.Machine.StateEvent.HitTests
open import CategoricalCrypto.UC.Model.Family.Ingest
open import CategoricalCrypto.UC.Model.Quantitative
open import CategoricalCrypto.UC.Quantitative.EventLift
open import CategoricalCrypto.UC.QueryBound.Counting
open import CategoricalCrypto.UC.Robust.Model
open import CategoricalCrypto.Examples.Basic
open import CategoricalCrypto.Examples.Commitment
open import CategoricalCrypto.Examples.Signatures
open import CategoricalCrypto.Examples.RandomOracle
open import CategoricalCrypto.Examples.HashForward.Audit
open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Compose
open import CategoricalCrypto.Examples.CoinToss.Test
open import CategoricalCrypto.Examples.ROCommitment.Asymptotic
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Defer
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Test
open import CategoricalCrypto.Examples.ROCommitment.Hiding.UC
open import CategoricalCrypto.Examples.ROCommitment.Realization.Assembly
open import CategoricalCrypto.Examples.ROCommitment.Realization.Bisim
open import CategoricalCrypto.Examples.ROCommitment.Realization.Bound
open import CategoricalCrypto.Examples.ROCommitment.Realization.Machine
open import CategoricalCrypto.Examples.ROCommitment.Resource
open import CategoricalCrypto.Examples.ROCommitment.Test
open import CategoricalCrypto.Examples.ROCommitment.Transport
open import CategoricalCrypto.Examples.ROCommitment.UC

open import ProbabilisticLogic

import Categories.Category.Construction.Kleisli.Distributive
import Categories.Category.Distributive.Monoidal
import Categories.Category.Monoidal.Distributive.Instance.Rels
