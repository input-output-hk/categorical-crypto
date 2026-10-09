{-# OPTIONS --safe --without-K --guardedness #-}

-- The ITM setup `StdUC 𝕋ᴹ ℰᵀ` and the morphism `itm⇒prot` into
-- protocol-rewrite (`docs/uc-setup-itm.md` §3.6, §4.1).  A test on ports `A`
-- is a test of the model on `Fᴾ A`, so `_≈ℰ_` is the model's, read through
-- `Fᴾ` (`≈ℰ⇔`); hom-equality is the free congruence and enters only there.

module CategoricalCrypto.ITM.Setup where

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Functor
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation

open import Data.Product.Base
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.ITM.Functor
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup using (ℰᵒ)
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.UC.Model.Setup as Prot

private module Fᴾ = StrongMonoidalFunctor Fᴾ

ℰᵀ : Presheaf (MonoidalCategory.U 𝕋ᴹ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᵀ = ℰᵒ ∘F Functor.op Fᴾ.F

open StdUC 𝕋ᴹ ℰᵀ public

-- `pullbackᵛ`, written out: its type spells `ℰᵒ ∘F Functor.op F`, and
-- matching that against the definition `ℰᵀ` compares the composites' law
-- fields (35 s, against 64 ms here; `docs/uc-setup-itm.md` §6 step 0).
νᵀ : PresheafMorphism Fᴾ.F ℰᵀ ℰᵒ
νᵀ = record { ν = ntHelper record
  { η = λ _ → record { to = λ x → x ; cong = λ e → e } ; commute = λ _ → Setoid.refl (Functor.₀ ℰᵒ _) } }

νᵀ-epi : PresheafMorphism.Epi νᵀ
νᵀ-epi y = y , Setoid.refl (Functor.₀ ℰᵒ _)

νᵀ-mono : PresheafMorphism.Mono νᵀ
νᵀ-mono e = e

itm⇒prot : UCSetupMorphism StdSetup Prot.StdSetup
itm⇒prot = StdUCMorphism 𝕋ᴹ 𝔾ᵒ ℰᵀ ℰᵒ Fᴾ νᵀ

≈ℰ⇔ : ∀ {A B} {f g : A ⇒ B} → f ≈ℰ g ⇔ Fᴾ.₁ f Prot.≈ℰ Fᴾ.₁ g
≈ℰ⇔ = mk⇔ (epi⇒preserves-≈ℰ λ {A} → νᵀ-epi {A}) (mono⇒reflects-≈ℰ λ {A} → νᵀ-mono {A})
  where open Transfer itm⇒prot
