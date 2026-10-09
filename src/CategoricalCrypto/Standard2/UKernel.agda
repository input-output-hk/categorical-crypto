{-# OPTIONS --safe --without-K #-}

-- The two-sided ancilla kernel of a `StdUC` test presheaf
-- (`docs/uc-setup-ssp.md` §4.2): `f ∼ g` when every padding `(Y ⊗ f) ⊗ Z` is
-- `≈ℰ`-equal.  It is a monoidal congruence: composition is padded factorwise,
-- and in a tensor the other factor is absorbed into an ancilla up to `α`, so
-- no braiding is needed.  It lies between the hom equality and `≈ᵁ`, so the
-- presheaf descends to `Quotient.quotient 𝕄 uKernel` (`∼⇒≈ℰ`).

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor.Presheaf

open import Level
open import Relation.Binary.Structures using (IsEquivalence)

import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.Standard2.UKernel
  {o ℓ e cs ℓs} (𝕄 : MonoidalCategory o ℓ e) (ℰ : Presheaf (MonoidalCategory.U 𝕄) (Setoids cs ℓs))
  where

open Std2.StdUC 𝕄 ℰ
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning ∣machines∣

private variable
  A B C D X : Channel
  f g h i : A ⇒ B

infix 4 _∼_

_∼_ : (f g : A ⇒ B) → Set (o ⊔ cs ⊔ ℓs)
f ∼ g = ∀ Y Z → (id {Y} ⊗₁ f) ⊗₁ id {Z} ≈ℰ (id {Y} ⊗₁ g) ⊗₁ id {Z}

∼-equiv : IsEquivalence (_∼_ {A} {B})
∼-equiv = record
  { refl  = λ _ _ → ≈ℰ-refl
  ; sym   = λ e Y Z → ≈ℰ-sym (e Y Z)
  ; trans = λ e e′ Y Z → ≈ℰ-trans (e Y Z) (e′ Y Z)
  }

≈⇒∼ : f ≈ g → f ∼ g
≈⇒∼ e _ _ = ≈C⇒≈ℰ ((refl⟩⊗⟨ e) ⟩⊗⟨refl)

private
  ≈ℰ-∘ : {f f′ : B ⇒ C} {g g′ : A ⇒ B} → f ≈ℰ f′ → g ≈ℰ g′ → f ∘ g ≈ℰ f′ ∘ g′
  ≈ℰ-∘ {f′ = f′} {g = g} e e′ = ≈ℰ-trans (≈ℰ-cong-pre g e) (≈ℰ-cong-post f′ e′)

  -- An `≈ℰ`-step across a structural equation on each side.
  across : {u u′ v v′ : A ⇒ B} → u ≈ u′ → v ≈ v′ → u′ ≈ℰ v′ → u ≈ℰ v
  across p q r = ≈ℰ-trans (≈C⇒≈ℰ p) (≈ℰ-trans r (≈ℰ-sym (≈C⇒≈ℰ q)))

  split-∘ : {Y Z : Channel} → (id {Y} ⊗₁ (f ∘ g)) ⊗₁ id {Z} ≈ (id ⊗₁ f) ⊗₁ id ∘ (id ⊗₁ g) ⊗₁ id
  split-∘ = (split₂ˡ ⟩⊗⟨refl) ○ split₁ˡ

  unpadʳ : {k : A ⇒ B} {k⁻ : B ⇒ A} → k ∘ k⁻ ≈ id → k ⊗₁ id {X} ∘ k⁻ ⊗₁ id ≈ id
  unpadʳ e = merge₁ˡ ○ (e ⟩⊗⟨refl) ○ ⊗.identity

∘-resp-∼ : f ∼ h → g ∼ i → (f ∘ g) ∼ (h ∘ i)
∘-resp-∼ e e′ Y Z = across split-∘ split-∘ (≈ℰ-∘ (e Y Z) (e′ Y Z))

⊗-resp-∼ : {A B C D : Channel} {f h : A ⇒ B} {g i : C ⇒ D} → f ∼ h → g ∼ i → (f ⊗₁ g) ∼ (h ⊗₁ i)
⊗-resp-∼ {A} {B} {C} {D} e e′ Y Z =
  across split split
    (≈ℰ-∘ (across left left (≈ℰ-cong-post (α⇒ ⊗₁ id ∘ α⇐) (≈ℰ-cong-pre (α⇒ ∘ α⇐ ⊗₁ id) (e Y (D ⊗₀ Z)))))
          (across right right (≈ℰ-cong-post (α⇒ ⊗₁ id) (≈ℰ-cong-pre (α⇐ ⊗₁ id) (e′ (Y ⊗₀ A) Z)))))
  where
  split : {f : A ⇒ B} {g : C ⇒ D}
        → (id {Y} ⊗₁ (f ⊗₁ g)) ⊗₁ id {Z} ≈ (id ⊗₁ (f ⊗₁ id)) ⊗₁ id ∘ (id ⊗₁ (id ⊗₁ g)) ⊗₁ id
  split = ((refl⟩⊗⟨ serialize₁₂) ⟩⊗⟨refl) ○ split-∘

  -- The other factor's object joins the right ancilla…
  left : {f : A ⇒ B}
       → (id {Y} ⊗₁ (f ⊗₁ id {D})) ⊗₁ id {Z} ≈ (α⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ f) ⊗₁ id ∘ (α⇒ ∘ α⇐ ⊗₁ id)
  left {f} = ⟺ (begin
    (α⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ f) ⊗₁ id ∘ (α⇒ ∘ α⇐ ⊗₁ id)       ≈⟨ assoc ○ (refl⟩∘⟨ sym-assoc) ⟩
    α⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ f) ⊗₁ id) ∘ (α⇒ ∘ α⇐ ⊗₁ id)       ≈⟨ refl⟩∘⟨ (slide ⟩∘⟨refl) ⟩
    α⇒ ⊗₁ id ∘ (((id ⊗₁ f) ⊗₁ id) ⊗₁ id ∘ α⇐) ∘ (α⇒ ∘ α⇐ ⊗₁ id) ≈⟨ refl⟩∘⟨ cancelInner associator.isoˡ ⟩
    α⇒ ⊗₁ id ∘ ((id ⊗₁ f) ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id              ≈⟨ pullˡ (merge₁ˡ ○ (assoc-commute-from ⟩⊗⟨refl) ○ split₁ˡ) ⟩
    ((id ⊗₁ (f ⊗₁ id)) ⊗₁ id ∘ α⇒ ⊗₁ id) ∘ α⇐ ⊗₁ id            ≈⟨ cancelʳ (unpadʳ associator.isoʳ) ⟩
    (id ⊗₁ (f ⊗₁ id)) ⊗₁ id                                    ∎)
    where slide = (refl⟩∘⟨ refl⟩⊗⟨ ⟺ ⊗.identity) ○ assoc-commute-to

  -- …and the first factor's object the left one.
  right : {g : C ⇒ D}
        → (id {Y} ⊗₁ (id {A} ⊗₁ g)) ⊗₁ id {Z} ≈ α⇒ ⊗₁ id ∘ (id ⊗₁ g) ⊗₁ id ∘ α⇐ ⊗₁ id
  right {g} = ⟺ (begin
    α⇒ ⊗₁ id ∘ (id ⊗₁ g) ⊗₁ id ∘ α⇐ ⊗₁ id        ≈⟨ (refl⟩∘⟨ merge₁ˡ) ○ merge₁ˡ ⟩
    (α⇒ ∘ (id ⊗₁ g) ∘ α⇐) ⊗₁ id                  ≈⟨ inner ⟩⊗⟨refl ⟩
    (id ⊗₁ (id ⊗₁ g)) ⊗₁ id                      ∎)
    where
    inner : α⇒ ∘ (id ⊗₁ g) ∘ α⇐ ≈ id ⊗₁ (id ⊗₁ g)
    inner = begin
      α⇒ ∘ (id ⊗₁ g) ∘ α⇐                ≈⟨ refl⟩∘⟨ (⟺ ⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      α⇒ ∘ ((id ⊗₁ id) ⊗₁ g) ∘ α⇐        ≈⟨ pullˡ assoc-commute-from ⟩
      (id ⊗₁ (id ⊗₁ g) ∘ α⇒) ∘ α⇐        ≈⟨ cancelʳ associator.isoʳ ⟩
      id ⊗₁ (id ⊗₁ g)                    ∎

uKernel : MonoidalCongruence 𝕄 (o ⊔ cs ⊔ ℓs)
uKernel = record
  { _∼_ = _∼_ ; ∼-equiv = ∼-equiv ; ≈⇒∼ = ≈⇒∼ ; ∘-resp-∼ = ∘-resp-∼ ; ⊗-resp-∼ = ⊗-resp-∼ }

-- Both ancillas the unit.
∼⇒≈ℰ : f ∼ g → f ≈ℰ g
∼⇒≈ℰ e = across pad pad (≈ℰ-cong-post (λ⇒ ∘ ρ⇒) (≈ℰ-cong-pre (ρ⇐ ∘ λ⇐) (e unit unit)))
  where
  pad : {f : A ⇒ B} → f ≈ (λ⇒ ∘ ρ⇒) ∘ (id ⊗₁ f) ⊗₁ id ∘ (ρ⇐ ∘ λ⇐)
  pad {f = f} = ⟺ (begin
    (λ⇒ ∘ ρ⇒) ∘ (id ⊗₁ f) ⊗₁ id ∘ (ρ⇐ ∘ λ⇐)   ≈⟨ assoc ○ (refl⟩∘⟨ pullˡ unitorʳ-commute-from) ⟩
    λ⇒ ∘ (id ⊗₁ f ∘ ρ⇒) ∘ (ρ⇐ ∘ λ⇐)           ≈⟨ refl⟩∘⟨ cancelInner unitorʳ.isoʳ ⟩
    λ⇒ ∘ id ⊗₁ f ∘ λ⇐                         ≈⟨ pullˡ unitorˡ-commute-from ⟩
    (f ∘ λ⇒) ∘ λ⇐                             ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
    f                                         ∎)

-- The right ancilla the unit; the left one is `≈ᵁ`'s.
∼⇒≈ᵁ : {f g : A ⇒ T₀ X B} → f ∼ g → f ≈ᵁ g
∼⇒≈ᵁ e Y = across pad pad (≈ℰ-cong-post (α⇐ ∘ ρ⇒) (≈ℰ-cong-pre ρ⇐ (e Y unit)))
  where
  pad : {f : A ⇒ X ⊗₀ B} → α⇐ ∘ id {Y} ⊗₁ f ≈ (α⇐ ∘ ρ⇒) ∘ (id ⊗₁ f) ⊗₁ id ∘ ρ⇐
  pad {f = f} = ⟺ (begin
    (α⇐ ∘ ρ⇒) ∘ (id ⊗₁ f) ⊗₁ id ∘ ρ⇐   ≈⟨ assoc ○ (refl⟩∘⟨ pullˡ unitorʳ-commute-from) ⟩
    α⇐ ∘ (id ⊗₁ f ∘ ρ⇒) ∘ ρ⇐           ≈⟨ refl⟩∘⟨ cancelʳ unitorʳ.isoʳ ⟩
    α⇐ ∘ id ⊗₁ f                       ∎)
