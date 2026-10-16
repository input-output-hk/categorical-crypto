{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Setup where

open import Categories.Category.Instance.Setoids
open import Categories.Functor.Presheaf
open import Level

open import CategoricalCrypto.Machine.Relational.Model
open import CategoricalCrypto.Machine.Relational.Observation
open import CategoricalCrypto.UC.Core
import CategoricalCrypto.Standard2 as Standard

module E = Evaluation evaluation

-- Observable quantifies every Initialized J A preparation, not merely arrows
-- arising from probabilistic presentations or finite scripts.
ℰᴿ : Presheaf 𝔾ᴿ (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᴿ = Observable.ℰᴼ E.observable

open Standard.StdUC 𝔾ᴿᵐ ℰᴿ public
