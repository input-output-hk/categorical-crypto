{-# OPTIONS --safe --without-K --guardedness #-}

-- protocol-rewrite → random systems: the identity on objects, machines and
-- tests, strong monoidal on the nose.  There is no morphism back (a functor would
-- need `∼ᴿ ⇒ ≈ᴹ`, false for lazy against eager sampling); a behavioural equality
-- reaches protocol-rewrite as a U-equivalence instead.  See
-- docs/uc-setup-random-systems.md §4.1.

open import Data.Product.Base

open import Categories.Category.Monoidal.Construction.Quotient

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Seal
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.UC.Model.Setup as Sᵒ
import CategoricalCrypto.UC.RandomSystems.Setup as Sᴿ

module CategoricalCrypto.UC.RandomSystems.Morphism where

private
  module Q = MonoidalCongruence congᴿ
  variable
    A B : Sᵒ.Channel
    X Y : Sᵒ.ℐ.Obj

rewrite⇒RS : UCSetupMorphism Sᵒ.StdSetup Sᴿ.StdSetup
rewrite⇒RS = StdUCMorphism 𝔾ᵒ Sᴿ.𝔾ᴿ Sᵒ.ℰᵒ Sᴿ.ℰᴿ (quotientF 𝔾ᵒ congᴿ) (descendᵛ 𝔾ᵒ congᴿ Sᵒ.ℰᵒ Sᴿ.∼ᴿ⇒≋)

-- A behavioural equality is a U-equivalence: the target sees it as a hom
-- equality, and `ν` is mono.
≈ᴿ⇒≈ᵁ : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → f Q.∼ g → f Sᵒ.≈ᵁ g
≈ᴿ⇒≈ᵁ e Y = Transfer.mono⇒reflects-≈ℰ rewrite⇒RS (descendᵛ-mono 𝔾ᵒ congᴿ Sᵒ.ℰᵒ Sᴿ.∼ᴿ⇒≋) (Sᴿ.≈C⇒≈ᵁ e Y)

≤UC-resp-≈ᴿ : {f f′ : A Sᵒ.⇒ Sᵒ.T₀ X B} {g g′ : A Sᵒ.⇒ Sᵒ.T₀ Y B}
            → f Q.∼ f′ → g Q.∼ g′ → f Sᵒ.≤UC g → f′ Sᵒ.≤UC g′
≤UC-resp-≈ᴿ ef eg le a =
  let s , e = le a
  in s , Sᵒ.≈ᵁ-trans (≈ᴿ⇒≈ᵁ (Q.∘-resp-∼ Q.∼.refl (Q.∼.sym ef)))
                     (Sᵒ.≈ᵁ-trans e (≈ᴿ⇒≈ᵁ (Q.∘-resp-∼ Q.∼.refl eg)))
