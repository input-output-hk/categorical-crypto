{-# OPTIONS --safe --without-K #-}

-- The standard grading: a monoidal category acting on itself.
--
-- This is where the qualitative core meets the INHERITED layer.
-- `CategoricalCrypto.Standard` instantiates `CategoricalCrypto.UCSetup` at
-- `𝒞 = ℐ = machines` with `ℳ = curriedTensor`, so `T₀ X A = X ⊗ A`, and
-- `gradingᵗ` is exactly that action read in the core's vocabulary: `_⊛_` is
-- `⊗`, `T₁`/`sub` are the bifunctor's two one-sided actions, `a⇒` is the
-- triple's `μ` and `a⇐` the retraction `θ` that
-- `UCSetup.GradeStableFromTests` asks for (`a-isoˡ` being its `θ-μ`), and
-- `a-nat` is `μ`'s naturality.  So `Grading` is a WEAKENING of the inherited
-- graded Kleisli triple, not a third parallel abstraction.
--
-- What it drops is what the intended model cannot supply: the unitors,
-- `return`/`ext`, and — decisively — that the grades form a monoidal category
-- at all.  `Monoidal (GConstruction …)` is still open (`docs/protocol-rewrite.md`,
-- M2 task 3), so `UCSetup` is uninhabited at `𝒫ᴵ` while `Grading 𝒫ᴵ` is not.
-- The same document has the supersession map for the rest of the vocabulary.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
import Categories.Category.Monoidal.Reasoning as MonR

open import Level using (Level)

open import CategoricalCrypto.UC.Core using (Grading)

module CategoricalCrypto.UC.Core.Standard {o ℓ e : Level} (M : MonoidalCategory o ℓ e) where

open MonoidalCategory M
open MonR monoidal

gradingᵗ : Grading U
gradingᵗ = record
  { _⊛_ = _⊗₀_
  ; T₁  = λ _ f → id ⊗₁ f
  ; sub = λ s → s ⊗₁ id
  ; a⇒  = associator.to
  ; a⇐  = associator.from

  ; T₁-resp-≈  = refl⟩⊗⟨_
  ; T₁-id      = ⊗.identity
  ; T₁-∘       = split₂ʳ
  ; sub-resp-≈ = _⟩⊗⟨refl
  ; sub-id     = ⊗.identity
  ; sub-∘      = split₁ʳ
  ; a-isoˡ     = associator.isoʳ
  ; a-nat      = assoc-commute-to ○ (⊗.identity ⟩⊗⟨refl ⟩∘⟨refl)
  }
