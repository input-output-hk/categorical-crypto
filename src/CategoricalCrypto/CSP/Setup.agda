{-# OPTIONS --safe --without-K --guardedness #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import CategoricalCrypto.CSP.Interface

module CategoricalCrypto.CSP.Setup (Sort : Set) (Payload : Sort → Set)
  (Sort-≟ : DecidableEquality Sort) (Ω : Interface Sort Payload) where

open import CategoricalCrypto.CSP.Monoidal Sort Payload
open import CategoricalCrypto.CSP.Testing Sort Payload Sort-≟ Ω
import CategoricalCrypto.Standard2 as Standard

open Standard.StdUC OpenCSPᴹ ℰᶜˢᵖ public
