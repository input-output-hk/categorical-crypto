{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC setup of the model: `Standard2.StdUC` at the sealed machine bundle and
-- the test presheaf, hence `UCSetup` and the whole of `Abstract2` — `_≈ᵁ_`,
-- `_≤UC_`, `≤UC-refl`, `dummy-complete`, `≤UC-trans`, `UC-compose`, `≈ᵁ⇒≈ℰ` —
-- inherited and already proved.  There is no second UC definition anywhere in
-- this cone.
--
-- The module does nothing but `open`, which is the spike's third discipline: the
-- seal in one module, `open StdUC` in a second, statements in a third.  Its
-- consumers are `UC.Model.Pin` (the application sites) and `UC.Model.Reading`
-- (the operational reading of `_≈ᵁ_`).

open import CategoricalCrypto.Standard2 using (module StdUC)
open import CategoricalCrypto.UC.Model.Environment using (ℰᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)

module CategoricalCrypto.UC.Model.Setup where

open StdUC 𝔾ᵒ ℰᵒ public
