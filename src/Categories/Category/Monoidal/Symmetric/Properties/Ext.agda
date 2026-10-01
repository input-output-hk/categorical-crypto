{-# OPTIONS --safe --without-K #-}

-- `β` swaps the outer two factors of a triple tensor; with it, the braiding
-- facts the machine layer's state shuffles and the G construction's trace run on.

open import Categories.Category
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Product.Base using (_,_)

module Categories.Category.Monoidal.Symmetric.Properties.Ext
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (S : Symmetric M) where

open Category C
open Symmetric S
open BraidedProps.Shorthands braided
open MonoidalUtilities.Shorthands M

open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Properties.Ext M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning C
open BraidedProps braided
open MonoidalUtilities M

private variable A B K₁ K₂ L P Q R X Y Z : Obj

β : (P ⊗₀ Q) ⊗₀ R ⇒ (P ⊗₀ R) ⊗₀ Q
β = α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒

β-β : β ∘ β ≈ id {(P ⊗₀ Q) ⊗₀ X}
β-β = center (cancelʳ associator.isoʳ) ○ refl⟩∘⟨ cancelˡ (pad-inv commutative)
    ○ associator.isoˡ

σ⊗-inv : σ⇒ ⊗₁ id {A} ∘ σ⇒ {Q} {P} ⊗₁ id ≈ id
σ⊗-inv = merge₁ˡ ○ (commutative ⟩⊗⟨refl) ○ ⊗.identity

pad-braid : (L : Obj) (h : K₁ ⇒ K₂) → id {L} ⊗₁ h ≈ σ⇒ ∘ h ⊗₁ id ∘ σ⇒
pad-braid L h = insertˡ commutative ○ (refl⟩∘⟨ braiding.⇒.commute (id , h))

unbraid : (h : K₁ ⇒ K₂) {i : A ⇒ L ⊗₀ K₁} {o : L ⊗₀ K₂ ⇒ B}
        → o ∘ id ⊗₁ h ∘ i ≈ (o ∘ σ⇒) ∘ h ⊗₁ id ∘ (σ⇒ ∘ i)
unbraid {L = L} h = (refl⟩∘⟨ pad-braid L h ⟩∘⟨refl) ○ (refl⟩∘⟨ assoc) ○ sym-assoc
                  ○ (refl⟩∘⟨ assoc)

σ-splitˡ : σ⇒ {P} {Q ⊗₀ X} ≈ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐
σ-splitˡ {P} {Q} {X} = insertʳ associator.isoʳ
                     ○ (⟺ (cancelˡ associator.isoˡ) ⟩∘⟨refl)
                     ○ ((refl⟩∘⟨ ⟺ (hexagon₁ {P} {Q})) ⟩∘⟨refl)

σ-splitʳ : σ⇒ {P ⊗₀ Q} {X} ≈ α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)
σ-splitʳ {P} {Q} {X} = insertˡ associator.isoʳ
                     ○ (refl⟩∘⟨ insertʳ associator.isoˡ)
                     ○ (refl⟩∘⟨ (⟺ (hexagon₂ {P} {Q}) ⟩∘⟨refl))

-- `β` is natural in all three factors.
β-nat : (u : P ⇒ R) (v : Q ⇒ Z) (t : X ⇒ Y) → (u ⊗₁ t) ⊗₁ v ∘ β ≈ β ∘ (u ⊗₁ v) ⊗₁ t
β-nat u v t = begin
  (u ⊗₁ t) ⊗₁ v ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ○ assoc ⟩
  α⇐ ∘ (u ⊗₁ (t ⊗₁ v) ∘ (id ⊗₁ σ⇒ ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm (⟺ (braiding.⇒.commute (v , t)))) ⟩
  α⇐ ∘ ((id ⊗₁ σ⇒ ∘ u ⊗₁ (v ⊗₁ t)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (u ⊗₁ (v ⊗₁ t) ∘ α⇒))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ (u ⊗₁ v) ⊗₁ t))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ (u ⊗₁ v) ⊗₁ t  ∎

β-natural : (g : X ⇒ Y) → β {P} {Q} ∘ id ⊗₁ g ≈ (id ⊗₁ g) ⊗₁ id ∘ β
β-natural g = (refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ ⟺ (β-nat id id g)

β-natural′ : (g : X ⇒ Y) → β {P} {Y} {Q} ∘ (id ⊗₁ g) ⊗₁ id ≈ id ⊗₁ g ∘ β
β-natural′ g = ⟺ (β-nat id g id) ○ ((⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl)

σ-unit : σ⇒ ≈ id
σ-unit = insertˡ unitorˡ.isoˡ ○ (refl⟩∘⟨ (braiding-coherence ○ ⟺ coherence₃))
       ○ unitorˡ.isoˡ

ρ-β : ρ⇒ {P} ⊗₁ id {A} ∘ β ≈ ρ⇒
ρ-β = pullˡ ρα-λ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ braiding-coherence) ○ coherence₂
