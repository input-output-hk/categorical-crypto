{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- States and processes over a traced symmetric monoidal category
------------------------------------------------------------------------

module Categories.GConstruction where

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
open import Categories.Category.Product
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.GConstruction.Core
open import Data.Product

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstruction.CoreProofs as P
import Categories.Morphism as Mor

module _ {a b c} (C : Category a b c) (M : Monoidal C) (T : Traced M) where

  open Construction C M T public

  private
    module C where
      open Category C public
      open Traced T public
      open U.Shorthands M public
      open BProps.Shorthands braided public
      open Mor C public

  GConstruction : Category a b c
  GConstruction = categoryHelper record
    { Obj       = C.Obj × C.Obj
    ; _⇒_       = _⇒ᴳ_
    ; _≈_       = C._≈_
    ; id        = C.σ⇒
    ; _∘_       = composeᴳ
    ; assoc     = P.assoc' C M T
    ; identityˡ = P.identityˡ' C M T
    ; identityʳ = P.identityʳ' C M T
    ; equiv     = C.equiv
    ; ∘-resp-≈  = P.compose-resp-≈ C M T
    }

  private module MG = Mor GConstruction

  embed : Functor (Product C C.op) GConstruction
  embed = record
    { F₀           = λ A → A
    ; F₁           = λ (u , v) → ⌜ u , v ⌝
    ; identity     = P.⌜⌝-id C M T
    ; homomorphism = C.Equiv.sym (P.⌜⌝-∘ C M T)
    ; F-resp-≈     = λ (e₁ , e₂) → P.⌜⌝-resp-≈ C M T e₁ e₂
    }

  ⌜⌝-≅ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} → A⁺ C.≅ B⁺ → B⁻ C.≅ A⁻ → (A⁺ , A⁻) MG.≅ (B⁺ , B⁻)
  ⌜⌝-≅ u v = [ embed ]-resp-≅ record
    { from = u.from , v.from ; to = u.to , v.to
    ; iso = record { isoˡ = u.isoˡ , v.isoʳ ; isoʳ = u.isoʳ , v.isoˡ } }
    where module u = C._≅_ u
          module v = C._≅_ v

  GConstructionMonoidal : Monoidal GConstruction
  GConstructionMonoidal = monoidalHelper GConstruction record
    { ⊗ = record
      { F₀           = λ (X , Y) → X ⊗₀ᴳ Y
      ; F₁           = λ (f , g) → f ⊗₁ᴳ g
      ; identity     = P.identityᴳ C M T
      ; homomorphism = P.homomorphismᴳ C M T
      ; F-resp-≈     = λ (p , q) → P.⊗₁ᴳ-resp-≈ C M T p q
      }
    ; unit            = unitᴳ
    ; unitorˡ         = ⌜⌝-≅ C.unitorˡ (C.≅.sym C.unitorˡ)
    ; unitorʳ         = ⌜⌝-≅ C.unitorʳ (C.≅.sym C.unitorʳ)
    ; associator      = ⌜⌝-≅ C.associator (C.≅.sym C.associator)
    ; unitorˡ-commute = P.unitorˡ-commuteᴳ C M T
    ; unitorʳ-commute = P.unitorʳ-commuteᴳ C M T
    ; assoc-commute   = P.assoc-commuteᴳ C M T
    ; triangle        = P.triangleᴳ C M T
    ; pentagon        = P.pentagonᴳ C M T
    }

  GConstructionMonoidalCategory : MonoidalCategory a b c
  GConstructionMonoidalCategory = record { U = GConstruction ; monoidal = GConstructionMonoidal }
