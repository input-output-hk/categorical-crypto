{-# OPTIONS --safe --without-K #-}

-- SPIKE: the category of Mealy machines over a symmetric monoidal `𝒱`.
--
-- `Spike.SlotFrame` supplies the interchange identities and all the coherence
-- bookkeeping they are glued with.  The crux here is `run-∘`: unrolling a
-- composite `n` steps is the same as composing the two unrollings, which is
-- `CategoricalCrypto.SFunM.Kleisli`'s `trace-∘` written point-free.  `eval-∘` then
-- closes the paired state off one factor at a time, and `Mealy-Category` reads
-- the category laws off `eval-∘` and `eval-id` exactly as `SFunM.Laws` does.

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Nat.Base using (ℕ; zero; suc)

import CategoricalCrypto.SFunM.Spike.Mealy as Mealy
import CategoricalCrypto.SFunM.Spike.SlotFrame as SlotFrame

module CategoricalCrypto.SFunM.Spike.Laws {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open MonoidalUtilities.Shorthands monoidal
open Mealy 𝒱
open SlotFrame 𝒱

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B C D : Obj

------------------------------------------------------------------------
-- Unrolling
------------------------------------------------------------------------

-- The point-free `trace-∘`: pairing states commutes with pairing interfaces.
run-∘ : (g : Machine B C) (f : Machine A B) (n : ℕ)
      → run (g ∘ᴹ f) n ≈ compK (run g n) (run f n)
run-∘ g f zero    = ⟺ compK-id
run-∘ g f (suc n) = (slot₂ᵍ-cong (run-∘ g f n) ⟩∘⟨refl) ○ compK-slot

run-id : (n : ℕ) → run (idᴹ {A}) n ≈ id
run-id zero    = Equiv.refl
run-id (suc n) = (slot₂ᵍ-cong (run-id n) ⟩∘⟨ slot₁-id) ○ identityʳ ○ slot₂-id

eval-id : (n : ℕ) → eval (idᴹ {A}) n ≈ id
eval-id n = begin
  λ⇒ ∘ (id ⊗₁ id ∘ (run idᴹ n ∘ (id ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
  λ⇒ ∘ (run idᴹ n ∘ (id ⊗₁ id ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ run-id n ⟩∘⟨refl ⟩
  λ⇒ ∘ (id ∘ (id ⊗₁ id ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ identityˡ ⟩
  λ⇒ ∘ (id ⊗₁ id ∘ λ⇐)
    ≈⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
  λ⇒ ∘ λ⇐
    ≈⟨ unitorˡ.isoʳ ⟩
  id  ∎

------------------------------------------------------------------------
-- The Mealy category
------------------------------------------------------------------------

eval-∘ : (g : Machine B C) (f : Machine A B) (n : ℕ)
       → eval (g ∘ᴹ f) n ≈ eval g n ∘ eval f n
eval-∘ g f n =
    cl-cong (run-∘ g f n)
  ○ cl-resp (discard-pair _ _) (point-pair _ _)
  ○ cl-factor
  ○ cl-cong ((refl⟩∘⟨ assoc) ○ pullˡ discard-onL ○ assoc ○ (refl⟩∘⟨ discard-onR))
  ○ cl-∘ʳ

assoc-∘ᴹ : {f : Machine A B} {g : Machine B C} {h : Machine C D}
         → ((h ∘ᴹ g) ∘ᴹ f) ≈ᵉ (h ∘ᴹ (g ∘ᴹ f))
assoc-∘ᴹ {f = f} {g} {h} n = begin
  eval ((h ∘ᴹ g) ∘ᴹ f) n            ≈⟨ eval-∘ (h ∘ᴹ g) f n ⟩
  eval (h ∘ᴹ g) n ∘ eval f n        ≈⟨ eval-∘ h g n ⟩∘⟨refl ⟩
  (eval h n ∘ eval g n) ∘ eval f n  ≈⟨ assoc ⟩
  eval h n ∘ (eval g n ∘ eval f n)  ≈˘⟨ refl⟩∘⟨ eval-∘ g f n ⟩
  eval h n ∘ eval (g ∘ᴹ f) n        ≈˘⟨ eval-∘ h (g ∘ᴹ f) n ⟩
  eval (h ∘ᴹ (g ∘ᴹ f)) n            ∎

identityˡ-∘ᴹ : {f : Machine A B} → (idᴹ ∘ᴹ f) ≈ᵉ f
identityˡ-∘ᴹ {f = f} n = eval-∘ idᴹ f n ○ (eval-id n ⟩∘⟨refl) ○ identityˡ

identityʳ-∘ᴹ : {f : Machine A B} → (f ∘ᴹ idᴹ) ≈ᵉ f
identityʳ-∘ᴹ {f = f} n = eval-∘ f idᴹ n ○ (refl⟩∘⟨ eval-id n) ○ identityʳ

∘ᴹ-resp-≈ᵉ : {f h : Machine B C} {g i : Machine A B}
           → f ≈ᵉ h → g ≈ᵉ i → (f ∘ᴹ g) ≈ᵉ (h ∘ᴹ i)
∘ᴹ-resp-≈ᵉ {f = f} {h} {g} {i} e₁ e₂ n =
  eval-∘ f g n ○ (e₁ n ⟩∘⟨ e₂ n) ○ ⟺ (eval-∘ h i n)

Mealy-Category : Category _ _ _
Mealy-Category = categoryHelper record
  { Obj       = Obj
  ; _⇒_       = Machine
  ; _≈_       = _≈ᵉ_
  ; id        = idᴹ
  ; _∘_       = _∘ᴹ_
  ; assoc     = assoc-∘ᴹ
  ; identityˡ = identityˡ-∘ᴹ
  ; identityʳ = identityʳ-∘ᴹ
  ; equiv     = ≈ᵉ-isEquivalence
  ; ∘-resp-≈  = ∘ᴹ-resp-≈ᵉ
  }
