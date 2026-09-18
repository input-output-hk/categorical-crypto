{-# OPTIONS --safe --without-K #-}

-- What the UC layer asks of its ambient category, QUALITATIVELY: a closed run
-- and an equivalence on what two closed runs show.
--
-- The ancilla action the UC layer needs beside it — an ancilla bypassing a
-- process, a simulator acting on one, and the reassociator between two nested
-- ancillas — is the ambient MONOIDAL structure's own, so the layers that want
-- it take a `MonoidalCategory` (`UC.Environment`, `UC.Budget`) rather than a
-- record of their own.
--
-- The observation is an EQUIVALENCE and nothing more.  A general UC setup need
-- not support quantitative observations: rational advantage, security
-- parameters and negligible functions belong to a model, so the ε-indexed
-- relation and the ε/2 argument live in
-- `CategoricalCrypto.UC.Approximate`, which also constructs an `Observation`
-- out of one (`Induced.observation`) — that construction is how the intended
-- `Dₚ` model and the asymptotic family both arrive.  Query budgets are the
-- same kind of model datum and live in `CategoricalCrypto.UC.Budget`.

open import Categories.Category.Core using (Category)

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Structures using (IsEquivalence)

module CategoricalCrypto.UC.Core where

record Observation {o ℓ e} (𝒞 : Category o ℓ e) (os ℓs : Level)
                 : Set (o ⊔ ℓ ⊔ e ⊔ suc os ⊔ suc ℓs) where
  open Category 𝒞

  infix 4 _∼_

  field
    𝟙 Ω : Obj
    Obs : Set os
    ⟦_⟧ : 𝟙 ⇒ Ω → Obs

    _∼_             : Obs → Obs → Set ℓs
    ∼-isEquivalence : IsEquivalence _∼_
    ⟦⟧-resp-≈       : {u v : 𝟙 ⇒ Ω} → u ≈ v → ⟦ u ⟧ ∼ ⟦ v ⟧

  open IsEquivalence ∼-isEquivalence public
    using () renaming (refl to ∼-refl; sym to ∼-sym; trans to ∼-trans)

  ∼-cast : {u u′ v v′ : 𝟙 ⇒ Ω} → u ≈ u′ → v ≈ v′ → ⟦ u ⟧ ∼ ⟦ v ⟧ → ⟦ u′ ⟧ ∼ ⟦ v′ ⟧
  ∼-cast eu ev h = ∼-trans (∼-sym (⟦⟧-resp-≈ eu)) (∼-trans h (⟦⟧-resp-≈ ev))
