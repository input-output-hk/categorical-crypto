{-# OPTIONS --safe --guardedness #-}

-- `--guardedness` is here because it is INFECTIVE and the `Dₚ` cone below uses
-- it; nothing in this module is coinductive.

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
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Protocol.Safety
open import CategoricalCrypto.Examples.Basic
open import CategoricalCrypto.Examples.Commitment
open import CategoricalCrypto.Examples.Signatures

open import ProbabilisticLogic

import Categories.Category.Construction.Kleisli.Distributive
import Categories.Category.Distributive.Monoidal
import Categories.Category.Monoidal.Distributive.Instance.Rels
