{-# OPTIONS --safe --without-K --guardedness #-}

-- Random systems (maurer2002 Defs 3, 9, 10): `𝔾ᵒ` with simulation coarsened to
-- behavioural equality, and `ℰᵒ`'s tests, which cannot tell behaviourally equal
-- machines apart, descended to it.  See docs/uc-setup-random-systems.md.

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor
open import Categories.Functor.Presheaf
open import Level

open import CategoricalCrypto.UC.Model.Seal
-- `using`: `UC.Model.Setup` re-exports `StdUC 𝔾ᵒ ℰᵒ`, which the open below would clash with
open import CategoricalCrypto.UC.Model.Setup using (ℰᵒ)
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.UC.RandomSystems.Setup where

private
  module G = MonoidalCategory 𝔾ᵒ
  module Q = MonoidalCongruence congᴿ

𝔾ᴿ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) 0ℓ
𝔾ᴿ = quotient 𝔾ᵒ congᴿ

∼ᴿ⇒≋ : {A B : G.Obj} {f g : A G.⇒ B} → f Q.∼ g
     → Setoids (suc 0ℓ) (suc 0ℓ) [ Functor.₁ ℰᵒ f ≈ Functor.₁ ℰᵒ g ]
∼ᴿ⇒≋ {f = f} {g} e {t} m =
  ∼ᴿ⇒Obs {(t G.∘ f) G.∘ m} {(t G.∘ g) G.∘ m} (Q.∘-resp-∼ (Q.∘-resp-∼ Q.∼.refl e) Q.∼.refl)

ℰᴿ : Presheaf (MonoidalCategory.U 𝔾ᴿ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᴿ = descend 𝔾ᵒ congᴿ ℰᵒ ∼ᴿ⇒≋

open Std2.StdUC 𝔾ᴿ ℰᴿ public
