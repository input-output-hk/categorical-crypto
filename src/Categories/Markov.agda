{-# OPTIONS --safe --without-K #-}

-- A Markov category is a symmetric monoidal category (𝒞, ⊗, 𝟙)
-- equipped with a commutative comonoid (`copy`, `del`) on every
-- object, satisfying:
--
--   1. Comonoid laws (counit, coassociativity, cocommutativity).
--   2. **Comonoidality of `copy`**: `copy_{X⊗Y}` agrees with the
--      "shuffle" of `copy_X ⊗ copy_Y`, i.e. `copy` is a monoidal
--      natural transformation.
--   3. The **Markov axiom**: every morphism preserves discarding,
--      i.e. `del ∘ f ≈ del` for all `f`.

module Categories.Markov where

open import Level

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module _ {o ℓ e} {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞}
         (symmetric : Symmetric monoidal) where

  open Category 𝒞
  open Symmetric symmetric

  private variable X Y : Obj

  shuffle : ((X ⊗₀ X) ⊗₀ (Y ⊗₀ Y)) ⇒ ((X ⊗₀ Y) ⊗₀ (X ⊗₀ Y))
  shuffle =
    associator.to
      ∘ (id ⊗₁ (associator.from ∘ ((braiding.⇒.η _) ⊗₁ id) ∘ associator.to))
      ∘ associator.from

  record MarkovCategory : Set (o ⊔ ℓ ⊔ e) where
    field
      copy : X ⇒ X ⊗₀ X
      del  : X ⇒ unit

      counit-l : unitorˡ.from ∘ ((del ⊗₁ id) ∘ copy) ≈ id {X}
      counit-r : unitorʳ.from ∘ ((id ⊗₁ del) ∘ copy) ≈ id {X}
      coassoc  : associator.from ∘ ((copy ⊗₁ id) ∘ copy) ≈ (id ⊗₁ copy) ∘ copy {X}
      cocomm   : braiding.⇒.η _ ∘ copy ≈ copy {X}

      copy-⊗ : copy {X ⊗₀ Y} ≈ shuffle ∘ (copy ⊗₁ copy)
      del-⊗  : unitorˡ.from ∘ (del ⊗₁ del) ≈ del {X ⊗₀ Y}
      del-𝟙   : del ≈ id
      copy-𝟙  : unitorˡ.from ∘ copy ≈ id

      -- The Markov axiom: every morphism preserves discarding.
      discard-natural : (f : X ⇒ Y) → del ∘ f ≈ del
