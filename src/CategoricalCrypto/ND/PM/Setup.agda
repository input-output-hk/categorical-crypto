{-# OPTIONS --safe --without-K --guardedness #-}

-- ND_B at PM (`docs/uc-setup-nondeterministic.md` §2.2): `ND.Grade` at the
-- sealed symmetric bundle `𝔾ˢ` with the choice factors ⊤ ⇿ S of
-- `ND.PM.Factor` and the model's tests.  B-emulation is PM's ≤UC
-- (`≤UC-B⇔≤UC`).  The telescope is bound explicitly, as `ND.SSP.Setup`'s is.

open import Categories.Category.Monoidal.Bundle
open import Function.Bundles using (_⇔_)
open import Level using (suc; 0ℓ)

open import CategoricalCrypto.Abstract2
import CategoricalCrypto.ND.Grade as Grade
open import CategoricalCrypto.ND.PM.Factor using (C)
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup using (ℰᵒ; _≤UC_)
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UCSetup

module CategoricalCrypto.ND.PM.Setup where

private
  module G = MonoidalCategory 𝔾ᵒ
  module 𝔹 = Grade 𝔾ˢ C

open 𝔹 using (Grade; ⌊_⌋)

NDB : UCSetup (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) _ _
NDB = 𝔹.NDB ℰᵒ

module _ {A B : G.Obj} {a b : Grade} {f : A G.⇒ ⌊ a ⌋ G.⊗₀ B} {g : A G.⇒ ⌊ b ⌋ G.⊗₀ B} where

  ≤UC-B⇔≤UC : AbstractUC._≤UC_ NDB {X = a} {Y = b} f g ⇔ f ≤UC g
  ≤UC-B⇔≤UC = 𝔹.≤UC-B⇔≤UC ℰᵒ {a = a} {b = b}
