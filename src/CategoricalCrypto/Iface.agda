{-# OPTIONS --safe --without-K #-}

-- Interfaces: a pair of message types, named by direction of travel.
-- `Pos` travels rightwards (out of a protocol towards its caller), `Neg`
-- leftwards (queries into it).

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

module CategoricalCrypto.Iface where

record Iface : Set₁ where
  constructor _⇿_
  field Pos Neg : Set
open Iface public

unitᴵ : Iface
unitᴵ = ⊥ ⇿ ⊥

_⊗ᴵ_ : Iface → Iface → Iface
A ⊗ᴵ B = (Pos A ⊎ Pos B) ⇿ (Neg A ⊎ Neg B)
