{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Root of the library: checking this module checks the channel/machine
-- layer, the protocol layer and the UC cone.
--
-- The `public` re-exports are the channel/machine layer proper, which a
-- consumer of this module gets by name.  The rest are plain imports — build
-- closure, not API: their names belong to their own roots.  Those are
-- `Strategy` and `OutputOnly`; `Protocol` and below (layer 1: protocols,
-- their machine images, the agreement and totality readings, safety and the
-- trajectory observable); and the UC layer's two roots, `UC` and `UC.Model`,
-- whose split `UC.agda`'s inventory explains.  `UC.Robust.Model` is reached
-- here rather than from either: it runs a `UC`-side theorem at the `UC.Model`
-- side's emulation, so neither root sees it.
--
-- `Examples.HashForward.Audit` is the leaf of the nontrivial-grade toy and
-- reaches the other two modules of it; it is here rather than at a root of its
-- own because it is three small modules, not a development.
--
-- `Examples.ROCommitment.*` is the nontrivial-grade application that DOES
-- carry an error: the UC images and the exact query accounting (`.UC`), the
-- closed extraction game and its bound (`.Asymptotic`, reaching `.Game`) and
-- the acceptance instance (`.Test`).  Three leaves because the game layer and
-- the machine layer do not meet yet — `docs/fcom-extraction.md` says where.
-- `Examples.ROCommitment.Hiding.*` is the other half, the corrupted receiver,
-- with the same three leaves (`docs/fcom-hiding.md`); its deferred-sampling
-- engine is `GamePlaying.Defer`.
--
-- Outside still, each with its own root: the protocol-layer examples
-- (`Examples.ChimericLedger`, `Examples.MerkleDamgard`) and the inherited
-- abstract theories (`UCSetup`, `Standard`, `StandardTV`, `VanishingTV`).
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
open import CategoricalCrypto.Machine.Probabilistic public
open import CategoricalCrypto.SFunM public
open import CategoricalCrypto.SFunPartial public
open import CategoricalCrypto.SFunPossibility
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Defer
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.GamePlaying.Potential
open import CategoricalCrypto.GamePlaying.Test
open import CategoricalCrypto.OutputOnly
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Machine.Compose
open import CategoricalCrypto.Protocol.Machine.Total
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Protocol.Safety
open import CategoricalCrypto.UC
open import CategoricalCrypto.UC.Model
open import CategoricalCrypto.UC.Robust.Model
open import CategoricalCrypto.Examples.Basic
open import CategoricalCrypto.Examples.Commitment
open import CategoricalCrypto.Examples.Possibilistic
open import CategoricalCrypto.Examples.Signatures
open import CategoricalCrypto.Examples.RandomOracle
open import CategoricalCrypto.Examples.HashForward.Audit
open import CategoricalCrypto.Examples.HashForward.Resource
open import CategoricalCrypto.Examples.ROCommitment.Asymptotic
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Test
open import CategoricalCrypto.Examples.ROCommitment.Hiding.UC
open import CategoricalCrypto.Examples.ROCommitment.Resource
open import CategoricalCrypto.Examples.ROCommitment.Test
open import CategoricalCrypto.Examples.ROCommitment.UC

open import ProbabilisticLogic
