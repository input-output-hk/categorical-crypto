{-# OPTIONS --safe --without-K #-}

-- The SSP setup: `StdUC` at `Protᴹ` and the test presheaf of the readout
-- (`docs/uc-setup-ssp.md` §3.6).
--
--     ℰᵖ(A) = Prot(A , Ωᴵ) / ≋    D ≋ D′ ⟺ ∀ G : unitᴵ → A. runᵖ (D ∘ᵖ G) ∼ᵃ runᵖ (D′ ∘ᵖ G)
--
-- `ℰᵖ` is the readout's own presheaf, re-exported rather than rebuilt (see
-- `UC.Model.Setup`).  In the grade reading `T₀ X B = X ⊗ᴵ B` is a protocol that
-- also exports adversary oracles `X`; `sub` puts a simulator protocol on them,
-- so `≤UC` reads "for every adversary-side protocol there is a simulator".

open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol.Monoidal
open import CategoricalCrypto.UC.Core

import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.SSP.Setup where

open Evaluation evaluationᵖ public
open Observable observable public using (Test; _≋_; ℰ₀) renaming (≈⇒≋ to ≈ᵖ⇒≋; ℰᴼ to ℰᵖ)
open Std2.StdUC Protᴹ ℰᵖ public
