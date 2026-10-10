{-# OPTIONS --safe --without-K #-}

-- Grades with designated choice factors, and model B
-- (`docs/uc-setup-nondeterministic.md` §2.2).  A grade (X , S⃗) reads as
-- ⌊ X , S⃗ ⌋ = X ⊗ C⟦ S⃗ ⟧, one choice factor C S per site, and grades tensor
-- by concatenating their site lists.  𝒢B is 𝕄 transported along ⌊_⌋ at the
-- class of all maps (`Construction.Transport`); its comparison φ is the
-- middle-four interchange, whose one braiding component is σ_{C⟦S⃗⟧,Y},
-- followed by the regrouping C⟦ S⃗ ⟧ ⊗ C⟦ T⃗ ⟧ ≅ C⟦ S⃗ ++ T⃗ ⟧ (`C++`).  ιB is
-- full, essentially surjective (at S⃗ = []) and strong, so ND_B, Std(𝕄)
-- restricted along ιB, has Std(𝕄)'s ≤UC (`≤UC-B⇔≤UC`, §1.3 (b), (c), (f)).
-- C⟦_⟧ is a `foldr`, as `ND.SSP.Choice.Cᴵ⟦_⟧` is, so that at (Protˢ, Cᴵ)
-- the two agree definitionally.

open import Categories.Category.Monoidal.Bundle

module CategoricalCrypto.ND.Grade {o ℓ e} (𝕄 : SymmetricMonoidalCategory o ℓ e)
  (C : Set → SymmetricMonoidalCategory.Obj 𝕄) where

open import Data.List.Base using (List; []; _∷_; _++_; foldr)
open import Data.Product
open import Data.Unit.Base
open import Function.Bundles using (_⇔_; mk⇔)
open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Interchange.Braided (SymmetricMonoidalCategory.braided 𝕄)
import Categories.Category.Monoidal.Construction.Transport as Transport
open import Categories.Category.Monoidal.Utilities (SymmetricMonoidalCategory.monoidal 𝕄)
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Functor.Properties
open import Categories.Morphism (SymmetricMonoidalCategory.U 𝕄)

open import CategoricalCrypto.Standard2
import CategoricalCrypto.Abstract2.Regrade as Regrade
open import CategoricalCrypto.UCSetup

open SymmetricMonoidalCategory 𝕄

C⟦_⟧ : List Set → Obj
C⟦_⟧ = foldr (λ S → C S ⊗₀_) unit

Grade : Set (o ⊔ suc 0ℓ)
Grade = Obj × List Set

⌊_⌋ : Grade → Obj
⌊ X , S⃗ ⌋ = X ⊗₀ C⟦ S⃗ ⟧

infixr 10 _⊕_
_⊕_ : Grade → Grade → Grade
(X , S⃗) ⊕ (Y , T⃗) = X ⊗₀ Y , S⃗ ++ T⃗

𝟙 : Grade
𝟙 = unit , []

C++ : (S⃗ T⃗ : List Set) → C⟦ S⃗ ⟧ ⊗₀ C⟦ T⃗ ⟧ ≅ C⟦ S⃗ ++ T⃗ ⟧
C++ []      T⃗ = unitorˡ
C++ (S ∷ S⃗) T⃗ = ≅.trans associator (≅.refl ⊗ᵢ C++ S⃗ T⃗)

module C++ S⃗ T⃗ = _≅_ (C++ S⃗ T⃗)

φ : ∀ {a b} → ⌊ a ⌋ ⊗₀ ⌊ b ⌋ ≅ ⌊ a ⊕ b ⌋
φ {X , S⃗} {Y , T⃗} = ≅.trans swapInner (≅.refl ⊗ᵢ C++ S⃗ T⃗)

υ : unit ≅ ⌊ 𝟙 ⌋
υ = ≅.sym unitorˡ

private module φ {a b} = _≅_ (φ {a} {b})

module 𝒯 = Transport monoidalCategory ⌊_⌋ _⊕_ 𝟙 (λ {a} {b} → φ {a} {b}) υ

closedB : 𝒯.Closed (λ _ → ⊤)
closedB = record
  { R-id = tt ; R-∘ = λ _ _ → tt ; R-⊗ = λ _ _ → tt ; R-λ⇒ = tt ; R-λ⇐ = tt ; R-ρ⇒ = tt ; R-ρ⇐ = tt
  ; R-α⇒ = tt ; R-α⇐ = tt }

private module 𝒢 = 𝒯.Restriction (λ _ → ⊤) closedB

𝒢B : MonoidalCategory (o ⊔ suc 0ℓ) ℓ e
𝒢B = 𝒢.transport

ιB : StrongMonoidalFunctor 𝒢B monoidalCategory
ιB = 𝒢.transportF

private module ιB = StrongMonoidalFunctor ιB

ιB-full : Full ιB.F
ιB-full f = (f , tt) , Equiv.refl

ιB-surj : EssentiallySurjective ιB.F
ιB-surj X = (X , []) , unitorʳ

module _ {cs ℓs : Level} (ℰ : Presheaf U (Setoids cs ℓs)) where
  private
    module Std = StdUC monoidalCategory ℰ
    module NB = Regrade Std.StdSetup ιB.monoidalFunctor

  NDB : UCSetup (o ⊔ suc 0ℓ) ℓ e o ℓ e cs ℓs
  NDB = NB.regraded

  ≤UC-B⇔≤UC : {A B : Obj} {a b : Grade} {f : A ⇒ ⌊ a ⌋ ⊗₀ B} {g : A ⇒ ⌊ b ⌋ ⊗₀ B}
            → NB.R._≤UC_ {X = a} {Y = b} f g ⇔ f Std.≤UC g
  ≤UC-B⇔≤UC {a = a} {b} = mk⇔
    (NB.Preserves.unrestrict-≤UC (λ {a} {b} → φ.to {a} {b}) (λ {a} {b} → φ.isoˡ {a} {b}) ιB-surj {X = a} {Y = b})
    (NB.restrict-≤UC {X = a} {Y = b} (λ {a} {b} → ιB-full {a} {b}))
