{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The symmetry of the G construction: the braiding is the base swap
-- embedded on both polarities, `σᴳ = ⌜ σ⇒ , σ⇒ ⌝` (the Int construction
-- of a traced symmetric category is symmetric, jsv1996).  `absorbˡ` and
-- `absorbʳ` reduce naturality to the swap conjugating the middle-four
-- interchange (`σ-mid`, `mid-σ⊗`); `⌜⌝-∘`, `⌜⌝-⊗ˡ` and `⌜⌝-⊗ʳ` reduce each
-- hexagon to one base hexagon on the positive polarity and the other on
-- the negative one, which composes backwards.
------------------------------------------------------------------------

module Categories.GConstructionSymmetric where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE
open import Categories.GConstruction
open import Categories.GConstructionEmbedding
open import Categories.GConstructionMonoidal
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Tactic.Category using (solve)

open import Data.Product using (_,_)

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionTrace as GT

module _ {a b c} (C : Category a b c) (M : Monoidal C) (T : Traced M) where

  private
    module C where
      open Category C public
      open Traced T public
      open U.Shorthands M public
      open import Categories.Category.Monoidal.Reasoning M public using (⊗-distrib-over-∘; _⟩⊗⟨_)
      open import Categories.Morphism.Reasoning C public using (pullˡ; pullʳ; cancelˡ; cancelʳ)
      open BProps.Shorthands braided public

    module E₀ = Embed C M T

  open C.HomReasoning
  open E₀ using (⌜_,_⌝; ⌜⌝-resp-≈)
  open GT C M T using (mid; mid-involutive; mid-braiding; mid-σ)

  σᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} → (A⁺ C.⊗₀ B⁺) C.⊗₀ (B⁻ C.⊗₀ A⁻) C.⇒ (A⁻ C.⊗₀ B⁻) C.⊗₀ (B⁺ C.⊗₀ A⁺)
  σᴳ = ⌜ C.σ⇒ , C.σ⇒ ⌝

  private
    variable O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : C.Obj

    -- Bracketings, generic so that `solve` meets variables, not the composites.
    pair-shape : {v : O₀ C.⇒ O₁} {w : O₁ C.⇒ O₂} {z : O₂ C.⇒ O₃} {y : O₃ C.⇒ O₄} {x : O₄ C.⇒ O₅}
               → x C.∘ (y C.∘ z C.∘ w) C.∘ v C.≈ (x C.∘ y) C.∘ z C.∘ (w C.∘ v)
    pair-shape = solve C

    triple-shape : {d : O₀ C.⇒ O₁} {b′ : O₁ C.⇒ O₂} {c′ : O₂ C.⇒ O₃} {x : O₃ C.⇒ O₄} {c : O₄ C.⇒ O₅}
                   {b : O₅ C.⇒ O₆} {a : O₆ C.⇒ O₇}
                 → (a C.∘ b C.∘ c) C.∘ x C.∘ (c′ C.∘ b′ C.∘ d) C.≈ a C.∘ (b C.∘ (c C.∘ x C.∘ c′) C.∘ b′) C.∘ d
    triple-shape = solve C

    -- The swap conjugates `mid` into the swap of its two halves…
    mid-σ⇒ : ∀ {P Q R S} → mid {R} {S} {P} {Q} C.∘ C.σ⇒ C.≈ C.σ⇒ C.⊗₁ C.σ⇒ C.∘ mid {P} {Q} {R} {S}
    mid-σ⇒ = (refl⟩∘⟨ ⟺ mid-braiding) ○ C.cancelˡ mid-involutive

    -- …so a swap on either side of `mid` is a swap of one inner pair.
    σ-mid : ∀ {P Q R S} → C.σ⇒ C.⊗₁ C.id C.∘ mid {R} {S} {P} {Q} C.∘ C.σ⇒ C.≈ C.id C.⊗₁ C.σ⇒ C.∘ mid {P} {Q} {R} {S}
    σ-mid = (refl⟩∘⟨ mid-σ⇒) ○ C.pullˡ (⟺ C.⊗-distrib-over-∘ ○ (C.commutative C.⟩⊗⟨ C.identityˡ))

    mid-σ⊗ : ∀ {P Q R S} → C.σ⇒ C.∘ mid {Q} {P} {R} {S} C.∘ C.σ⇒ C.⊗₁ C.id C.≈ mid {P} {Q} {S} {R} C.∘ C.id C.⊗₁ C.σ⇒
    mid-σ⊗ = C.pullˡ (⟺ mid-σ) ○ C.pullʳ (⟺ C.⊗-distrib-over-∘ ○ (C.commutative C.⟩⊗⟨ C.identityʳ))

    swap-conj : ∀ {A B D E} {f : A C.⇒ B} {g : D C.⇒ E} → g C.⊗₁ f C.≈ C.σ⇒ C.∘ f C.⊗₁ g C.∘ C.σ⇒
    swap-conj {f = f} {g} = ⟺ (C.pullˡ (C.braiding.⇒.commute (f , g)) ○ C.cancelʳ C.commutative)

  module _ (L : TE.Laws T) where

    private
      G' : Category a b c
      G' = GConstruction C M T L
      module G = Category G'

    open E₀.WithTrace L

    σᴳ-commutative : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj}
                   → G._∘_ {A⁺ C.⊗₀ B⁺ , A⁻ C.⊗₀ B⁻} (σᴳ {B⁺} {B⁻} {A⁺} {A⁻}) (σᴳ {A⁺} {A⁻} {B⁺} {B⁻}) C.≈ G.id
    σᴳ-commutative = ⌜⌝-∘ ○ ⌜⌝-resp-≈ C.commutative C.commutative ○ ⌜⌝-id

    opaque
      unfolding _⊗₁ᴳ_
      σᴳ-natural : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj}
                     {f : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺} {g : D⁺ C.⊗₀ E⁻ C.⇒ D⁻ C.⊗₀ E⁺}
                 → G._∘_ {A⁺ C.⊗₀ D⁺ , A⁻ C.⊗₀ D⁻} {B⁺ C.⊗₀ E⁺ , B⁻ C.⊗₀ E⁻} σᴳ (_⊗₁ᴳ_ C M T f g)
                   C.≈ G._∘_ {A⁺ C.⊗₀ D⁺ , A⁻ C.⊗₀ D⁻} {D⁺ C.⊗₀ A⁺ , D⁻ C.⊗₀ A⁻} (_⊗₁ᴳ_ C M T g f) σᴳ
      σᴳ-natural {f = f} {g} = absorbˡ ○ (begin
        C.id C.⊗₁ C.σ⇒ C.∘ (mid C.∘ f C.⊗₁ g C.∘ mid) C.∘ C.id C.⊗₁ C.σ⇒
          ≈⟨ pair-shape ⟩
        (C.id C.⊗₁ C.σ⇒ C.∘ mid) C.∘ f C.⊗₁ g C.∘ (mid C.∘ C.id C.⊗₁ C.σ⇒)
          ≈˘⟨ σ-mid ⟩∘⟨ refl⟩∘⟨ mid-σ⊗ ⟩
        (C.σ⇒ C.⊗₁ C.id C.∘ mid C.∘ C.σ⇒) C.∘ f C.⊗₁ g C.∘ (C.σ⇒ C.∘ mid C.∘ C.σ⇒ C.⊗₁ C.id)
          ≈⟨ triple-shape ⟩
        C.σ⇒ C.⊗₁ C.id C.∘ (mid C.∘ (C.σ⇒ C.∘ f C.⊗₁ g C.∘ C.σ⇒) C.∘ mid) C.∘ C.σ⇒ C.⊗₁ C.id
          ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ swap-conj ⟩∘⟨refl) ⟩∘⟨refl ⟩
        C.σ⇒ C.⊗₁ C.id C.∘ (mid C.∘ g C.⊗₁ f C.∘ mid) C.∘ C.σ⇒ C.⊗₁ C.id ∎) ○ ⟺ absorbʳ

    GConstructionBraided : Braided (GConstructionMonoidal C M T L)
    GConstructionBraided = record
      { braiding = niHelper record
        { η       = λ _ → σᴳ
        ; η⁻¹     = λ _ → σᴳ
        ; commute = λ _ → σᴳ-natural
        ; iso     = λ _ → record { isoˡ = σᴳ-commutative ; isoʳ = σᴳ-commutative }
        }
      ; hexagon₁ = G.∘-resp-≈ (⌜⌝-⊗ˡ C M T L) (G.∘-resp-≈ʳ (⌜⌝-⊗ʳ C M T L) ○ ⌜⌝-∘) ○ ⌜⌝-∘
                 ○ ⌜⌝-resp-≈ C.hexagon₁ C.hexagon₂
                 ○ ⟺ (G.∘-resp-≈ʳ ⌜⌝-∘ ○ ⌜⌝-∘)
      ; hexagon₂ = G.∘-resp-≈ (G.∘-resp-≈ˡ (⌜⌝-⊗ʳ C M T L) ○ ⌜⌝-∘) (⌜⌝-⊗ˡ C M T L) ○ ⌜⌝-∘
                 ○ ⌜⌝-resp-≈ C.hexagon₂ C.hexagon₁
                 ○ ⟺ (G.∘-resp-≈ˡ ⌜⌝-∘ ○ ⌜⌝-∘)
      }

    GConstructionSymmetric : Symmetric (GConstructionMonoidal C M T L)
    GConstructionSymmetric = record { braided = GConstructionBraided ; commutative = σᴳ-commutative }

    -- The bundle, projected from one application as `GConstructionMonoidalCategory` is.
    GConstructionSymmetricMonoidalCategory : SymmetricMonoidalCategory a b c
    GConstructionSymmetricMonoidalCategory = record
      { U = G' ; monoidal = GConstructionMonoidal C M T L ; symmetric = GConstructionSymmetric }
