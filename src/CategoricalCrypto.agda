{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Root of the categorical-cryptography development: channels, machines,
-- and example protocols.  This subtree (`CategoricalCrypto/**` plus
-- `Class.Monad.Ext`, 11 modules) is the OTHER development in this
-- source tree — it does not depend on the string-diagram solver or the
-- APROP soundness/completeness stack, and nothing outside it imports it.
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
open import CategoricalCrypto.Examples.Basic
open import CategoricalCrypto.Examples.Commitment
open import CategoricalCrypto.Examples.Signatures
