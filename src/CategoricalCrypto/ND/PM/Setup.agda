{-# OPTIONS --safe --without-K --guardedness #-}

-- Both designated-choice setups use PM's tests. Relabelling simulators are
-- sealed partial wires; arbitrary B-simulators may answer requests online.

open import Categories.Category.Monoidal.Bundle
open import Data.Product.Base using (Σ-syntax; _×_)
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; Equivalence)
open import Level using (suc; 0ℓ)

open import CategoricalCrypto.Abstract2
import CategoricalCrypto.ND.A as A
import CategoricalCrypto.ND.Grade as Grade
open import CategoricalCrypto.ND.PM.Factor using (C)
open import CategoricalCrypto.ND.PM.Relabel
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup using (ℰᵒ; _≤UC_; _≈ᵁ_)
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UCSetup

module CategoricalCrypto.ND.PM.Setup where

private
  module G = MonoidalCategory 𝔾ᵒ
  module 𝔹 = Grade 𝔾ˢ C
  module 𝔸 = A 𝔾ˢ C

open 𝔹 using (Grade; ⌊_⌋)

NDB : UCSetup (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) _ _
NDB = 𝔹.NDB ℰᵒ

NDA : UCSetup (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) _ _
NDA = 𝔸.NDA relabelling ℰᵒ

module _ {A B : G.Obj} {a b : Grade} {f : A G.⇒ ⌊ a ⌋ G.⊗₀ B} {g : A G.⇒ ⌊ b ⌋ G.⊗₀ B} where

  ≤UC-B⇔≤UC : AbstractUC._≤UC_ NDB {A = A} {X = a} {B = B} {Y = b} f g ⇔ _≤UC_ {A = A} {X = ⌊ a ⌋} {B = B} {Y = ⌊ b ⌋} f g
  ≤UC-B⇔≤UC = 𝔹.≤UC-B⇔≤UC ℰᵒ {A = A} {B = B} {a = a} {b = b}

  A⇒B : AbstractUC._≤UC_ NDA {A = A} {X = a} {B = B} {Y = b} f g
      → AbstractUC._≤UC_ NDB {A = A} {X = a} {B = B} {Y = b} f g
  A⇒B = 𝔸.A⇒B relabelling ℰᵒ {A = A} {B = B} {a = a} {b = b}

  A⇒PM : AbstractUC._≤UC_ NDA {A = A} {X = a} {B = B} {Y = b} f g
       → _≤UC_ {A = A} {X = ⌊ a ⌋} {B = B} {Y = ⌊ b ⌋} f g
  A⇒PM = Equivalence.to ≤UC-B⇔≤UC ∘ A⇒B

  relabel-≤UC : (s : ⌊ b ⌋ G.⇒ ⌊ a ⌋) → 𝔸.Relabels relabelling {b} {a} s
              → _≈ᵁ_ {A = A} {X = ⌊ a ⌋} {B = B} f ((s G.⊗₁ G.id) G.∘ g)
              → AbstractUC._≤UC_ NDA {A = A} {X = a} {B = B} {Y = b} f g
  relabel-≤UC = 𝔸.relabel-≤UC relabelling ℰᵒ {A = A} {B = B} {a = a} {b = b} {f = f} {g = g}

  ≤UC⇒relabel : AbstractUC._≤UC_ NDA {A = A} {X = a} {B = B} {Y = b} f g
              → Σ[ s ∈ ⌊ b ⌋ G.⇒ ⌊ a ⌋ ] 𝔸.Relabels relabelling {b} {a} s
                × _≈ᵁ_ {A = A} {X = ⌊ a ⌋} {B = B} f ((s G.⊗₁ G.id) G.∘ g)
  ≤UC⇒relabel = 𝔸.≤UC⇒relabel relabelling ℰᵒ {A = A} {B = B} {a = a} {b = b} {f = f} {g = g}
