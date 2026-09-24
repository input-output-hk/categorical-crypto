{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- For a graded Kleisli triple ℳ over ℐ in 𝒞, the free actegory ∮ on
-- its locally graded presentation (GKOS / McDermott–Uustalu) is the
-- graded Kleisli category of Fujii/FKM.
--------------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Monad.Graded

module Categories.LocallyGraded.FreeActegory.Kleisli
  {o ℓ e o′ ℓ′ e′} (𝒞 : Category o′ ℓ′ e′) (ℐ : MonoidalCategory o ℓ e)
  (ℳ : GradedKleisliTriple ℐ 𝒞) where

open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor
open import Categories.Functor.Equivalence
open import Categories.GradedKleisli
open import Categories.LocallyGraded.FreeActegory using (∮)
open import Categories.LocallyGraded.Kleisli
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Product
open import Relation.Binary.Construct.Closure.Equivalence as EqC using ()
open import Relation.Binary.PropositionalEquality

private
  module 𝒞 where
    open Category 𝒞 public
    open HomReasoning public
    open MR 𝒞 public
  module ℐ = MonoidalCategory ℐ
  module ℐᵁ where
    open Category ℐ.U public
    open HomReasoning public
    open MR ℐ.U public

open ℐ using (_⊗-)
open Functor
open GradedKleisliTriple ℳ

private
  K∮ = ∮ (naiveKleisli ℳ)
  K  = GradedKleisli 𝒞 ℐ ℳ
  module K∮ where
    open Category K∮ public
    open MR K∮ public
  module K where
    open Category K public
    open MR K public

------------------------------------------------------------------------
-- The two categories agree on the nose, except for the presentation of
-- hom equality
------------------------------------------------------------------------

Obj-≡ : K∮.Obj ≡ K.Obj
Obj-≡ = refl

Hom-≡ : ∀ {X Y} → (X K∮.⇒ Y) ≡ (X K.⇒ Y)
Hom-≡ = refl

id-≡ : ∀ {X} → K∮.id {X} ≡ K.id {X}
id-≡ = refl

∘-≡ : ∀ {X Y Z} {g : Y K∮.⇒ Z} {f : X K∮.⇒ Y} → (K∮ [ g ∘ f ]) ≡ (K [ g ∘ f ])
∘-≡ = refl

-- Hom equality both ways: the equivalence closures of the coend's
-- dinaturality Step and of GradedKleisli's Slide are interconvertible
-- generator-for-generator (Slide's witness is the coend's sliding morphism,
-- applied to the witness (f₀ , β₀)).
private
  toStep : ∀ {ai bj c d} {x y : (ai , c) K.⇒ (bj , d)} → K [ x ≈ y ] → K∮ [ x ≈ y ]
  toStep {ai} = EqC.map λ where
    {X , f₀ , α₀} {Y , g₀ , β₀} (φ , p , q) →
      φ , (f₀ , β₀) , (𝒞.elimˡ sub-identity , q) , (p , ℐᵁ.elimʳ (identity (ai ⊗-)))

  toSlide : ∀ {ai bj c d} {x y : (ai , c) K∮.⇒ (bj , d)} → K∮ [ x ≈ y ] → K [ x ≈ y ]
  toSlide {ai} = EqC.map λ where
    {X , f₀ , α₀} {Y , g₀ , β₀} (φ , (w₁ , w₂) , (e₁ , e₂) , (e₃ , e₄)) →
        φ
      , (let open 𝒞 in begin
          sub φ ∘ f₀                        ≈˘⟨ refl⟩∘⟨ e₁ ⟩
          sub φ ∘ (sub ℐ.id ∘ w₁)           ≈⟨ refl⟩∘⟨ elimˡ sub-identity ⟩
          sub φ ∘ w₁                        ≈⟨ e₃ ⟩
          g₀                                ∎)
      , (let open ℐᵁ in begin
          β₀ ∘ ₁ (ai ⊗-) φ                  ≈˘⟨ e₄ ⟩∘⟨refl ⟩
          (w₂ ∘ ₁ (ai ⊗-) ℐ.id) ∘ ₁ (ai ⊗-) φ  ≈⟨ elimʳ (identity (ai ⊗-)) ⟩∘⟨refl ⟩
          w₂ ∘ ₁ (ai ⊗-) φ                  ≈⟨ e₂ ⟩
          α₀                                ∎)

toFreeActegory : Functor K K∮
toFreeActegory = record
  { F₀           = λ X → X
  ; F₁           = λ f → f
  ; identity     = K∮.Equiv.refl
  ; homomorphism = K∮.Equiv.refl
  ; F-resp-≈     = toStep
  }

fromFreeActegory : Functor K∮ K
fromFreeActegory = record
  { F₀           = λ X → X
  ; F₁           = λ f → f
  ; identity     = K.Equiv.refl
  ; homomorphism = K.Equiv.refl
  ; F-resp-≈     = toSlide
  }

bridge : StrongEquivalence K∮ K
bridge = record
  { F            = fromFreeActegory
  ; G            = toFreeActegory
  ; weak-inverse = record
    { F∘G≈id = niHelper record
      { η       = λ _ → K.id
      ; η⁻¹     = λ _ → K.id
      ; commute = λ _ → K.id-comm-sym
      ; iso     = λ _ → record { isoˡ = K.identity² ; isoʳ = K.identity² } }
    ; G∘F≈id = niHelper record
      { η       = λ _ → K∮.id
      ; η⁻¹     = λ _ → K∮.id
      ; commute = λ _ → K∮.id-comm-sym
      ; iso     = λ _ → record { isoˡ = K∮.identity² ; isoʳ = K∮.identity² } }
    }
  }

------------------------------------------------------------------------
-- The flattened forgetful factorization
------------------------------------------------------------------------

ev∮ : Functor K∮ 𝒞
ev∮ = record
  { F₀           = λ (i , A) → T₀ i A
  ; F₁           = λ where {i , _} (k , f , α) → sub α 𝒞.∘ ext i f
  ; identity     = ext-identityˡ
  ; homomorphism = λ {_} {_} {_} {f} {g} → U-∘ 𝒞 ℐ ℳ g f
  ; F-resp-≈     = λ e → U-resp 𝒞 ℐ ℳ (toSlide e)
  }

ev∮-factors : ev∮ ≡F (U-functor 𝒞 ℐ ℳ ∘F fromFreeActegory)
ev∮-factors = record { eq₀ = λ _ → refl ; eq₁ = λ _ → 𝒞.id-comm-sym }
