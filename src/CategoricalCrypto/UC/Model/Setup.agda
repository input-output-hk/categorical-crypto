{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC setup of the model: `UC.Core.Bridge` at the sealed machine bundle and
-- the model's observation.  One module application, and it carries `UCSetup`
-- and the whole of `Abstract2` — `_≈ᵁ_`, `_≤UC_`, `≤UC-refl`,
-- `dummy-complete`, `≤UC-trans`, `UC-compose`, `≈ᵁ⇒≈ℰ` — together with the
-- hand-rolled core's `_≈ℰᶜ_` and its two-way agreement with `_≈ᵁ_`, all
-- inherited and already proved.  There is no second UC definition anywhere in
-- this cone.
--
--     ℰᵒ(A) = 𝒜(A , Ωᵒ) / ≋    e ≋ e′ ⟺ ∀ m : 𝟘ᵒ → A. Obs (e ∘ m) ∼ᴼ Obs (e′ ∘ m)
--
-- `ℰᵒ` is the setup's OWN presheaf, re-exported rather than rebuilt.  A second
-- application of `UC.Environment.Presheaf` at the same data is a distinct copy
-- that matches nothing by head, so every conversion between the two
-- eta-expands the functor: `StdSetup` against the copy checks by `refl` in
-- 80 s where `StdSetup` against this one is at the 9 s startup floor.  The
-- `using` list keeps `Test`, `Closure` and `obs` out; they are
-- `UC.Model.Observation`'s own names at this instance, and re-exporting them
-- would make them ambiguous for a consumer that opens both.

open import CategoricalCrypto.UC.Model.Observation using (observationᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)

module CategoricalCrypto.UC.Model.Setup where

open import CategoricalCrypto.UC.Core.Bridge 𝔾ᵒ observationᵒ public

open C public using (_≋_; ≋-isEquivalence; ℰ₀) renaming (≈⇒≋ to ≈ᵒ⇒≋; ℰᴼ to ℰᵒ)
