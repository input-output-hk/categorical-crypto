{-# OPTIONS --safe --without-K #-}

-- SPIKE: the category of Mealy machines over a symmetric monoidal `𝒱`.
--
-- `Spike.Interchange` supplies the three interchange identities; everything
-- here is bookkeeping on top of them.  The crux is `run-∘`: unrolling a
-- composite `n` steps is the same as composing the two unrollings, which is
-- `CategoricalCrypto.SFunM`'s `trace-∘` written point-free.  `eval-∘` then
-- closes the paired state off one factor at a time, and `Mealy-Category` reads
-- the category laws off `eval-∘` and `eval-id` exactly as `SFunM.Laws` does.

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Nat.Base using (ℕ; zero; suc)

import CategoricalCrypto.SFunM.Spike.Interchange as Interchange
import CategoricalCrypto.SFunM.Spike.Mealy as Mealy

module CategoricalCrypto.SFunM.Spike.Laws {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Mealy 𝒱
open Interchange 𝒱

open import Categories.Category.Monoidal.Properties monoidal
  using (coherence₁; coherence₂; coherence₃; coherence-inv₁; coherence-inv₃)
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U
open BraidedProps braided using (braiding-coherence)
open MonoidalUtilities monoidal using (triangle-inv)

private variable A A′ B B′ C C′ D P Q : Obj

------------------------------------------------------------------------
-- The composite step
------------------------------------------------------------------------

-- `Machine.step (g ∘ᴹ f)` is `compK (step g) (step f)`.
compK : (P ⊗₀ B ⇒ P ⊗₀ C) → (Q ⊗₀ A ⇒ Q ⊗₀ B) → (P ⊗₀ Q) ⊗₀ A ⇒ (P ⊗₀ Q) ⊗₀ C
compK g f = onL g ∘ onR f

onL-id : onL {Q = Q} (id {P ⊗₀ A}) ≈ id
onL-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ swp-swp

onR-id : onR {P = P} (id {Q ⊗₀ A}) ≈ id
onR-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoˡ

compK-id : compK (id {P ⊗₀ A}) (id {Q ⊗₀ A}) ≈ id
compK-id = (onL-id ⟩∘⟨ onR-id) ○ identity²

------------------------------------------------------------------------
-- The two state factors act on complementary interface slots
------------------------------------------------------------------------

-- Both sides are the `Ω`-conjugate of `g ⊗₁ f`; only the order in which the
-- two disjoint boxes fire differs.
slot-comm : {g : P ⊗₀ B ⇒ P ⊗₀ C} {f : Q ⊗₀ A′ ⇒ Q ⊗₀ B′}
          → slot₂ {Z = C} (onR {P = P} f) ∘ slot₁ {Z = A′} (onL {Q = Q} g)
          ≈ slot₁ {Z = B′} (onL {Q = Q} g) ∘ slot₂ {Z = B} (onR {P = P} f)
slot-comm {P = P} {B} {C} {Q} {A′} {B′} {g} {f} = begin
  slot₂ (onR f) ∘ slot₁ (onL g)
    ≈⟨ Gᶠ.slot₂-onR-Ω ⟩∘⟨ Gᵍ.slot₁-onL ⟩
  (Ω ∘ (id ⊗₁ f ∘ Ω)) ∘ (Ω ∘ (g ⊗₁ id ∘ Ω))
    ≈⟨ center (cancelʳ Ω-involutive) ⟩
  Ω ∘ (id ⊗₁ f ∘ (g ⊗₁ id ∘ Ω))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ serialize₂₁ ○ serialize₁₂) ⟩
  Ω ∘ ((g ⊗₁ id ∘ id ⊗₁ f) ∘ Ω)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  Ω ∘ (g ⊗₁ id ∘ (id ⊗₁ f ∘ Ω))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ Ω-involutive ⟩
  Ω ∘ (g ⊗₁ id ∘ (Ω ∘ (Ω ∘ (id ⊗₁ f ∘ Ω))))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  Ω ∘ ((g ⊗₁ id ∘ Ω) ∘ (Ω ∘ (id ⊗₁ f ∘ Ω)))
    ≈⟨ sym-assoc ⟩
  (Ω ∘ (g ⊗₁ id ∘ Ω)) ∘ (Ω ∘ (id ⊗₁ f ∘ Ω))
    ≈˘⟨ Gᵍ′.slot₁-onL ⟩∘⟨ Gᶠ′.slot₂-onR-Ω ⟩
  slot₁ (onL g) ∘ slot₂ (onR f)  ∎
  where
    module Gᵍ  = OneGen  P Q B C A′ g
    module Gᵍ′ = OneGen  P Q B C B′ g
    module Gᶠ  = OneGenʳ P Q A′ B′ C f
    module Gᶠ′ = OneGenʳ P Q A′ B′ B f

-- Slotting a composite step: this is the whole content of `run-∘`.
compK-slot : {g₁ : P ⊗₀ B ⇒ P ⊗₀ C} {f₁ : Q ⊗₀ A ⇒ Q ⊗₀ B}
             {g₂ : P ⊗₀ B′ ⇒ P ⊗₀ C′} {f₂ : Q ⊗₀ A′ ⇒ Q ⊗₀ B′}
           → slot₂ {Z = C} (compK g₂ f₂) ∘ slot₁ {Z = A′} (compK g₁ f₁)
           ≈ compK (slot₂ g₂ ∘ slot₁ g₁) (slot₂ f₂ ∘ slot₁ f₁)
compK-slot {P = P} {B} {C} {Q} {A} {B′} {C′} {A′} {g₁} {f₁} {g₂} {f₂} = begin
  slot₂ (onL g₂ ∘ onR f₂) ∘ slot₁ (onL g₁ ∘ onR f₁)
    ≈⟨ slot₂ᵍ-∘ ⟩∘⟨ slot₁ᵍ-∘ ⟩
  (slot₂ (onL g₂) ∘ slot₂ (onR f₂)) ∘ (slot₁ (onL g₁) ∘ slot₁ (onR f₁))
    ≈⟨ assoc ⟩
  slot₂ (onL g₂) ∘ (slot₂ (onR f₂) ∘ (slot₁ (onL g₁) ∘ slot₁ (onR f₁)))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  slot₂ (onL g₂) ∘ ((slot₂ (onR f₂) ∘ slot₁ (onL g₁)) ∘ slot₁ (onR f₁))
    ≈⟨ refl⟩∘⟨ slot-comm ⟩∘⟨refl ⟩
  slot₂ (onL g₂) ∘ ((slot₁ (onL g₁) ∘ slot₂ (onR f₂)) ∘ slot₁ (onR f₁))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  slot₂ (onL g₂) ∘ (slot₁ (onL g₁) ∘ (slot₂ (onR f₂) ∘ slot₁ (onR f₁)))
    ≈⟨ sym-assoc ⟩
  (slot₂ (onL g₂) ∘ slot₁ (onL g₁)) ∘ (slot₂ (onR f₂) ∘ slot₁ (onR f₁))
    ≈⟨ (Hᵍ.slot₂-onL-comm ⟩∘⟨ Hᵍ′.slot₁-onL-comm) ⟩∘⟨ (Hᶠ.slot₂-onR ⟩∘⟨ Hᶠ′.slot₁-onR) ⟩
  (onL (slot₂ g₂) ∘ onL (slot₁ g₁)) ∘ (onR (slot₂ f₂) ∘ onR (slot₁ f₁))
    ≈˘⟨ onL-∘ ⟩∘⟨ onRᵍ-∘ ⟩
  onL (slot₂ g₂ ∘ slot₁ g₁) ∘ onR (slot₂ f₂ ∘ slot₁ f₁)  ∎
  where
    module Hᵍ  = OneGen  P Q B′ C′ C g₂
    module Hᵍ′ = OneGen  P Q B  C  B′ g₁
    module Hᶠ  = OneGenʳ P Q A′ B′ B f₂
    module Hᶠ′ = OneGenʳ P Q A  B  A′ f₁

------------------------------------------------------------------------
-- Unrolling
------------------------------------------------------------------------

slot₁-id : ∀ {X Z} → slot₁ {P} {X} {X} {Z} id ≈ id
slot₁-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoʳ

slot₂-id : ∀ {X Z} → slot₂ {P} {X} {X} {Z} id ≈ id
slot₂-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ untuck-tuck

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
-- Closing off the state
------------------------------------------------------------------------

-- Discarding / pointing the second factor of a paired state.
dsc : (Q ⇒ unit) → P ⊗₀ Q ⇒ P
dsc d = ρ⇒ ∘ id ⊗₁ d

psc : (unit ⇒ Q) → P ⇒ P ⊗₀ Q
psc p = id ⊗₁ p ∘ ρ⇐

cl-cong : {d : P ⇒ unit} {p : unit ⇒ P} {R R′ : P ⊗₀ A ⇒ P ⊗₀ B}
        → R ≈ R′ → cl d p R ≈ cl d p R′
cl-cong e = refl⟩∘⟨ refl⟩∘⟨ e ⟩∘⟨refl

cl-resp : {d d′ : P ⇒ unit} {p p′ : unit ⇒ P} {R : P ⊗₀ A ⇒ P ⊗₀ B}
        → d ≈ d′ → p ≈ p′ → cl d p R ≈ cl d′ p′ R
cl-resp e₁ e₂ = refl⟩∘⟨ ((e₁ ⟩⊗⟨refl) ⟩∘⟨ (refl⟩∘⟨ ((e₂ ⟩⊗⟨refl) ⟩∘⟨refl)))

-- An action on the interface alone comes out of the closure.
cl-∘ʳ : {d : P ⇒ unit} {p : unit ⇒ P} {R : P ⊗₀ A ⇒ P ⊗₀ B} {h : C ⇒ A}
      → cl d p (R ∘ id ⊗₁ h) ≈ cl d p R ∘ h
cl-∘ʳ {d = d} {p} {R} {h} = begin
  λ⇒ ∘ (d ⊗₁ id ∘ ((R ∘ id ⊗₁ h) ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (id ⊗₁ h ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (pad-transport p h) ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ ((p ⊗₁ id ∘ id ⊗₁ h) ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ (id ⊗₁ h ∘ λ⇐))))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ (λ⇐ ∘ h))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ ((p ⊗₁ id ∘ λ⇐) ∘ h)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ ((R ∘ (p ⊗₁ id ∘ λ⇐)) ∘ h))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ ((d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))) ∘ h)
    ≈⟨ sym-assoc ⟩
  (λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))) ∘ h  ∎

-- …and so does an action on the interface alone on the other side.
cl-∘ˡ : {d : P ⇒ unit} {p : unit ⇒ P} {R : P ⊗₀ A ⇒ P ⊗₀ B} {h : B ⇒ C}
      → cl d p (id ⊗₁ h ∘ R) ≈ h ∘ cl d p R
cl-∘ˡ {d = d} {p} {R} {h} = begin
  λ⇒ ∘ (d ⊗₁ id ∘ ((id ⊗₁ h ∘ R) ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (id ⊗₁ h ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ (pad-transport d h)) ⟩
  λ⇒ ∘ ((id ⊗₁ h ∘ d ⊗₁ id) ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (id ⊗₁ h ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ pullˡ unitorˡ-commute-from ○ assoc ⟩
  h ∘ (λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))  ∎

-- Slotting into the first interface factor comes out of the closure untouched:
-- this is what turns a word's `A`-subrun back into `eval f`.
cl-slot₁ : {d : P ⇒ unit} {p : unit ⇒ P} {R : P ⊗₀ A ⇒ P ⊗₀ B}
         → cl d p (slot₁ {Z = C} R) ≈ cl d p R ⊗₁ id
cl-slot₁ {d = d} {p} {R} = begin
  λ⇒ ∘ (d ⊗₁ id ∘ ((α⇒ ∘ (R ⊗₁ id ∘ α⇐)) ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ assoc)) ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (α⇒ ∘ (R ⊗₁ id ∘ (α⇐ ∘ (p ⊗₁ id ∘ λ⇐)))))
    ≈⟨ refl⟩∘⟨ pullˡ (pad-α⇒ d) ⟩
  λ⇒ ∘ ((α⇒ ∘ (d ⊗₁ id) ⊗₁ id) ∘ (R ⊗₁ id ∘ (α⇐ ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ pullˡ (pullˡ coherence₁) ⟩
  (λ⇒ ⊗₁ id ∘ (d ⊗₁ id) ⊗₁ id) ∘ (R ⊗₁ id ∘ (α⇐ ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (pad-α⇐ p) ⟩
  (λ⇒ ⊗₁ id ∘ (d ⊗₁ id) ⊗₁ id) ∘ (R ⊗₁ id ∘ (((p ⊗₁ id) ⊗₁ id ∘ α⇐) ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ coherence-inv₁)) ⟩
  (λ⇒ ⊗₁ id ∘ (d ⊗₁ id) ⊗₁ id) ∘ (R ⊗₁ id ∘ ((p ⊗₁ id) ⊗₁ id ∘ λ⇐ ⊗₁ id))
    ≈⟨ merge₁ˡ ⟩∘⟨ ((refl⟩∘⟨ merge₁ˡ) ○ merge₁ˡ) ⟩
  (λ⇒ ∘ d ⊗₁ id) ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)) ⊗₁ id
    ≈⟨ merge₁ˡ ○ (assoc ⟩⊗⟨refl) ⟩
  (λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))) ⊗₁ id  ∎

-- A state map that conjugates the two runs identifies their closures; `sim` is
-- this at every unrolling.
cl-sim : {d : P ⇒ unit} {p : unit ⇒ P} {d′ : Q ⇒ unit} {p′ : unit ⇒ Q}
         {R : P ⊗₀ A ⇒ P ⊗₀ B} {R′ : Q ⊗₀ A ⇒ Q ⊗₀ B} (u : P ⇒ Q)
       → d′ ∘ u ≈ d → u ∘ p ≈ p′ → u ⊗₁ id ∘ R ≈ R′ ∘ u ⊗₁ id
       → cl d p R ≈ cl d′ p′ R′
cl-sim {d = d} {p} {d′} {p′} {R} {R′} u ed ep e = begin
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈˘⟨ refl⟩∘⟨ ed ⟩⊗⟨refl ⟩∘⟨refl ⟩
  λ⇒ ∘ ((d′ ∘ u) ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ○ (refl⟩∘⟨ assoc) ⟩
  λ⇒ ∘ (d′ ⊗₁ id ∘ (u ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ e ⟩
  λ⇒ ∘ (d′ ⊗₁ id ∘ ((R′ ∘ u ⊗₁ id) ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d′ ⊗₁ id ∘ (R′ ∘ (u ⊗₁ id ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (merge₁ˡ ○ ep ⟩⊗⟨refl) ⟩
  λ⇒ ∘ (d′ ⊗₁ id ∘ (R′ ∘ (p′ ⊗₁ id ∘ λ⇐)))  ∎

-- A factorization of the point and the discard factors out of the closure.
cl-factor : {d : P ⇒ unit} {p : unit ⇒ P} {u : Q ⇒ P} {v : P ⇒ Q}
            {R : Q ⊗₀ A ⇒ Q ⊗₀ B}
          → cl (d ∘ u) (v ∘ p) R ≈ cl d p (u ⊗₁ id ∘ (R ∘ v ⊗₁ id))
cl-factor {d = d} {p} {u} {v} {R} = begin
  λ⇒ ∘ ((d ∘ u) ⊗₁ id ∘ (R ∘ ((v ∘ p) ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ (split₁ˡ ⟩∘⟨ (refl⟩∘⟨ (split₁ˡ ⟩∘⟨refl))) ⟩
  λ⇒ ∘ ((d ⊗₁ id ∘ u ⊗₁ id) ∘ (R ∘ ((v ⊗₁ id ∘ p ⊗₁ id) ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (u ⊗₁ id ∘ (R ∘ ((v ⊗₁ id ∘ p ⊗₁ id) ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (u ⊗₁ id ∘ (R ∘ (v ⊗₁ id ∘ (p ⊗₁ id ∘ λ⇐)))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (u ⊗₁ id ∘ ((R ∘ v ⊗₁ id) ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ ((u ⊗₁ id ∘ (R ∘ v ⊗₁ id)) ∘ (p ⊗₁ id ∘ λ⇐)))  ∎

-- `_⊛_`'s discard and point factor as "discard/point the second factor, then
-- the first".
discard-pair : (dp : P ⇒ unit) (dq : Q ⇒ unit) → λ⇒ ∘ dp ⊗₁ dq ≈ dp ∘ dsc dq
discard-pair dp dq = begin
  λ⇒ ∘ dp ⊗₁ dq                ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
  λ⇒ ∘ (dp ⊗₁ id ∘ id ⊗₁ dq)   ≈⟨ sym-assoc ⟩
  (λ⇒ ∘ dp ⊗₁ id) ∘ id ⊗₁ dq   ≈⟨ (coherence₃ ⟩∘⟨refl) ⟩∘⟨refl ⟩
  (ρ⇒ ∘ dp ⊗₁ id) ∘ id ⊗₁ dq   ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
  (dp ∘ ρ⇒) ∘ id ⊗₁ dq         ≈⟨ assoc ⟩
  dp ∘ (ρ⇒ ∘ id ⊗₁ dq)         ∎

point-pair : (pp : unit ⇒ P) (pq : unit ⇒ Q) → pp ⊗₁ pq ∘ λ⇐ ≈ psc pq ∘ pp
point-pair pp pq = begin
  pp ⊗₁ pq ∘ λ⇐                ≈⟨ serialize₂₁ ⟩∘⟨refl ⟩
  (id ⊗₁ pq ∘ pp ⊗₁ id) ∘ λ⇐   ≈⟨ assoc ⟩
  id ⊗₁ pq ∘ (pp ⊗₁ id ∘ λ⇐)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
  id ⊗₁ pq ∘ (pp ⊗₁ id ∘ ρ⇐)   ≈˘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
  id ⊗₁ pq ∘ (ρ⇐ ∘ pp)         ≈⟨ sym-assoc ⟩
  (id ⊗₁ pq ∘ ρ⇐) ∘ pp         ∎

------------------------------------------------------------------------
-- Closing the second state factor of a composite step
------------------------------------------------------------------------

ρα-λ : ρ⇒ {P} ⊗₁ id {A} ∘ α⇐ ≈ id ⊗₁ λ⇒
ρα-λ = ((⟺ triangle) ⟩∘⟨refl) ○ cancelʳ associator.isoʳ

αρ-λ : α⇒ ∘ ρ⇐ {P} ⊗₁ id {A} ≈ id ⊗₁ λ⇐
αρ-λ = (refl⟩∘⟨ (⟺ triangle-inv)) ○ cancelˡ associator.isoʳ

ρ-swp : ρ⇒ {P} ⊗₁ id {A} ∘ swp ≈ ρ⇒
ρ-swp = pullˡ ρα-λ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ braiding-coherence) ○ coherence₂

dsc-swp : {d : Q ⇒ unit} → dsc {P = P} d ⊗₁ id {A} ∘ swp ≈ ρ⇒ ∘ id ⊗₁ d
dsc-swp {d = d} = begin
  (ρ⇒ ∘ id ⊗₁ d) ⊗₁ id ∘ swp            ≈⟨ split₁ˡ ⟩∘⟨refl ⟩
  (ρ⇒ ⊗₁ id ∘ (id ⊗₁ d) ⊗₁ id) ∘ swp    ≈⟨ assoc ⟩
  ρ⇒ ⊗₁ id ∘ ((id ⊗₁ d) ⊗₁ id ∘ swp)    ≈˘⟨ refl⟩∘⟨ swp-natural d ⟩
  ρ⇒ ⊗₁ id ∘ (swp ∘ id ⊗₁ d)            ≈⟨ pullˡ ρ-swp ⟩
  ρ⇒ ∘ id ⊗₁ d                          ∎

-- `onL` does not see the second state factor, so closing it passes through.
discard-onL : {d : Q ⇒ unit} {R : P ⊗₀ A ⇒ P ⊗₀ B}
            → dsc d ⊗₁ id {B} ∘ onL R ≈ R ∘ dsc d ⊗₁ id {A}
discard-onL {d = d} {R} = begin
  dsc d ⊗₁ id ∘ (swp ∘ (R ⊗₁ id ∘ swp))
    ≈⟨ pullˡ dsc-swp ⟩
  (ρ⇒ ∘ id ⊗₁ d) ∘ (R ⊗₁ id ∘ swp)
    ≈⟨ assoc ⟩
  ρ⇒ ∘ (id ⊗₁ d ∘ (R ⊗₁ id ∘ swp))
    ≈⟨ refl⟩∘⟨ pullˡ (pad-transport R d) ⟩
  ρ⇒ ∘ ((R ⊗₁ id ∘ id ⊗₁ d) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ∘ (R ⊗₁ id ∘ (id ⊗₁ d ∘ swp))
    ≈⟨ pullˡ unitorʳ-commute-from ⟩
  (R ∘ ρ⇒) ∘ (id ⊗₁ d ∘ swp)
    ≈⟨ assoc ⟩
  R ∘ (ρ⇒ ∘ (id ⊗₁ d ∘ swp))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  R ∘ ((ρ⇒ ∘ id ⊗₁ d) ∘ swp)
    ≈˘⟨ refl⟩∘⟨ dsc-swp ⟩∘⟨refl ⟩
  R ∘ ((dsc d ⊗₁ id ∘ swp) ∘ swp)
    ≈⟨ refl⟩∘⟨ cancelʳ swp-swp ⟩
  R ∘ dsc d ⊗₁ id  ∎

-- …and closing it around `onR` is exactly `eval` of the second factor.
discard-onR : {d : Q ⇒ unit} {p : unit ⇒ Q} {R : Q ⊗₀ A ⇒ Q ⊗₀ B}
            → dsc d ⊗₁ id {B} ∘ (onR {P = P} R ∘ psc p ⊗₁ id {A})
            ≈ id {P} ⊗₁ cl d p R
discard-onR {d = d} {p} {R} = begin
  dsc d ⊗₁ id ∘ (onR R ∘ psc p ⊗₁ id)
    ≈⟨ split₁ˡ ⟩∘⟨ (refl⟩∘⟨ split₁ˡ) ⟩
  (ρ⇒ ⊗₁ id ∘ (id ⊗₁ d) ⊗₁ id) ∘ (onR R ∘ ((id ⊗₁ p) ⊗₁ id ∘ ρ⇐ ⊗₁ id))
    ≈⟨ assoc ⟩
  ρ⇒ ⊗₁ id ∘ ((id ⊗₁ d) ⊗₁ id ∘ (onR R ∘ ((id ⊗₁ p) ⊗₁ id ∘ ρ⇐ ⊗₁ id)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  ρ⇒ ⊗₁ id ∘ ((id ⊗₁ d) ⊗₁ id ∘ ((onR R ∘ (id ⊗₁ p) ⊗₁ id) ∘ ρ⇐ ⊗₁ id))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  ρ⇒ ⊗₁ id ∘ (((id ⊗₁ d) ⊗₁ id ∘ (onR R ∘ (id ⊗₁ p) ⊗₁ id)) ∘ ρ⇐ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ (onRᵍ-⊗id d ⟩∘⟨ (refl⟩∘⟨ onRᵍ-⊗id p)) ⟩∘⟨refl ⟩
  ρ⇒ ⊗₁ id ∘ ((onRᵍ (d ⊗₁ id) ∘ (onRᵍ R ∘ onRᵍ (p ⊗₁ id))) ∘ ρ⇐ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ (onRᵍ-∘ ○ (refl⟩∘⟨ onRᵍ-∘)) ⟩∘⟨refl ⟩
  ρ⇒ ⊗₁ id ∘ (onRᵍ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ ρ⇐ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ⊗₁ id ∘ (α⇐ ∘ ((id ⊗₁ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ α⇒) ∘ ρ⇐ ⊗₁ id))
    ≈⟨ pullˡ ρα-λ ⟩
  id ⊗₁ λ⇒ ∘ ((id ⊗₁ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ α⇒) ∘ ρ⇐ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  id ⊗₁ λ⇒ ∘ (id ⊗₁ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ (α⇒ ∘ ρ⇐ ⊗₁ id))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ αρ-λ ⟩
  id ⊗₁ λ⇒ ∘ (id ⊗₁ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ id ⊗₁ λ⇐)
    ≈⟨ refl⟩∘⟨ merge₂ʳ ⟩
  id ⊗₁ λ⇒ ∘ id ⊗₁ ((d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ λ⇐)
    ≈⟨ merge₂ʳ ⟩
  id ⊗₁ (λ⇒ ∘ ((d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ λ⇐))
    ≈⟨ refl⟩⊗⟨ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ assoc))) ⟩
  id ⊗₁ (λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))  ∎

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
