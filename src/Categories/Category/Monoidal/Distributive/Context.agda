{-# OPTIONS --safe --without-K #-}

-- Reindexing objects by S ⊗ - keeps every ambient arrow between them.
-- Distributivity makes this induced category cocartesian.

open import Categories.Category.Cocartesian
open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.SubCategory as Sub

module Categories.Category.Monoidal.Distributive.Context {o ℓ e}
  (𝒱 : SymmetricMonoidalCategory o ℓ e) (dist : MD.MonoidalDistributive 𝒱)
  (S : SymmetricMonoidalCategory.Obj 𝒱) where

open SymmetricMonoidalCategory 𝒱
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open CE U cocartesian
open Equiv
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U
open import Categories.Morphism.Reasoning.Ext U

private variable A B C D E F : Obj

Context : Category o ℓ e
Context = Sub.FullSubCategory U (S ⊗₀_)

context-cocartesian : Cocartesian Context
context-cocartesian = record
  { initial = record
    { ⊥ = ⊥
    ; ⊥-is-initial = record { ¡ = id ⊗₁ ¡ ; ¡-unique = λ _ → ⊥-unique }
    }
  ; coproducts = record { coproduct = record
    { A+B = _ + _
    ; i₁ = id ⊗₁ i₁
    ; i₂ = id ⊗₁ i₂
    ; [_,_] = λ f g → [ f , g ] ∘ δ⇐
    ; inject₁ = pullʳ δ⇐-i₁ ○ inject₁
    ; inject₂ = pullʳ δ⇐-i₂ ○ inject₂
    ; unique = λ e₁ e₂ → δ-unique (pullʳ δ⇐-i₁ ○ inject₁ ○ ⟺ e₁)
                                  (pullʳ δ⇐-i₂ ○ inject₂ ○ ⟺ e₂)
    } }
  }

module Context = Cocartesian context-cocartesian
module Context+ = CE Context context-cocartesian

context-+₁ : (f : S ⊗₀ A ⇒ S ⊗₀ B) (g : S ⊗₀ C ⇒ S ⊗₀ D)
            → f Context.+₁ g ≈ tstep f g
context-+₁ _ _ = ⟺ []∘+₁ ⟩∘⟨refl ○ assoc

context-α⇒ : id {S} ⊗₁ +-assocˡ {A} {B} {C} ≈ Context.+-assocˡ
context-α⇒ = ⊗-[] [ i₁ , i₂ ∘ i₁ ] (i₂ ∘ i₂)
  ○ []-cong₂ (⊗-[] i₁ (i₂ ∘ i₁) ○ []-cong₂ refl split₂ˡ ⟩∘⟨refl) split₂ˡ ⟩∘⟨refl

context-α⇐ : id {S} ⊗₁ +-assocʳ {A} {B} {C} ≈ Context.+-assocʳ
context-α⇐ = inv-resp (⊗-cancel identity² ⊕.associator.isoˡ) Context+.⊕.associator.isoʳ context-α⇒

tstep-α : {k₁ : S ⊗₀ A ⇒ S ⊗₀ B} {k₂ : S ⊗₀ C ⇒ S ⊗₀ D} {k₃ : S ⊗₀ E ⇒ S ⊗₀ F}
        → id ⊗₁ +-assocˡ ∘ tstep (tstep k₁ k₂) k₃ ≈ tstep k₁ (tstep k₂ k₃) ∘ id ⊗₁ +-assocˡ
tstep-α {k₁ = k₁} {k₂} {k₃} =
  context-α⇒ ⟩∘⟨ (tstep-cong (⟺ (context-+₁ k₁ k₂)) refl ○ ⟺ (context-+₁ (k₁ Context.+₁ k₂) k₃))
  ○ Context+.⊕.assoc-commute-from
  ○ (context-+₁ k₁ (k₂ Context.+₁ k₃) ○ tstep-cong refl (context-+₁ k₂ k₃)) ⟩∘⟨ ⟺ context-α⇒
