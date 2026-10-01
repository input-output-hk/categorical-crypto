{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC setup of the model: `StdUC` at the sealed machine bundle and the test
-- presheaf of the model's readout.
--
--     ℰᵒ(A) = 𝒜(A , Ωᵒ) / ≋    e ≋ e′ ⟺ ∀ m : 𝟘ᵒ → A. Obs (e ∘ m) ∼ᵃ Obs (e′ ∘ m)
--
-- `ℰᵒ` is the readout's OWN presheaf, re-exported rather than rebuilt.  A
-- second construction of it at the same data is a distinct copy that matches
-- nothing by head, so every conversion between the two eta-expands the
-- functor: `StdSetup` against the copy checks by `refl` in 80 s where
-- `StdSetup` against this one is at the 9 s startup floor.

open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.UC.Model.Setup where

open Evaluation evaluationᵒ public
open Observable observable public using (Test; _≋_; ≋-isEquivalence; ℰ₀)
  renaming (≈⇒≋ to ≈ᵒ⇒≋; ℰᴼ to ℰᵒ)
open Std2.StdUC 𝔾ᵒ ℰᵒ public
