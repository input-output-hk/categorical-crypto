{-# OPTIONS --safe --without-K --guardedness #-}

-- The environment presheaf of the model (proposal §2): `UC.Environment.Presheaf`
-- at the seal's category and the model's own observation, hence
--
--     ℰᵒ(A) = 𝒜(A , Ωᵒ) / ≋    e ≋ e′ ⟺ ∀ m : 𝟘ᵒ → A. Obs (e ∘ m) ∼ᴼ Obs (e′ ∘ m)
--     ℰᵒ(f)[e] = [e ∘ f]
--
-- No ancilla is part of the carrier, deliberately: the graded context closure of
-- `Abstract2` supplies the ancillary experiments, and its operational reading is
-- `UC.Model.Reading`.  This is what distinguishes the construction from
-- `VanishingTV.ℰᵗᵛ`, whose carrier is a dependent pair `(Y , test on Y ⊗ A)`.
--
-- The presheaf may be concrete without breaking the seal (`UC.Model.Seal`'s
-- fourth discipline), and the construction it comes from spends no grading, so
-- nothing here brings a `Grading` into the closure.

open import CategoricalCrypto.UC.Model.Observation using (observationᵒ)
open import CategoricalCrypto.UC.Model.Seal using (∣𝔾ᵒ∣)

module CategoricalCrypto.UC.Model.Environment where

-- `Test`, `Closure` and `obs` are left behind: they are `UC.Model.Observation`'s
-- own names at this instance, and re-exporting them would make them ambiguous
-- for a consumer that opens both.
open import CategoricalCrypto.UC.Environment.Presheaf ∣𝔾ᵒ∣ observationᵒ public
  using (_≋_; ≋-isEquivalence; ℰ₀) renaming (≈⇒≋ to ≈ᵒ⇒≋; ℰᴼ to ℰᵒ)
