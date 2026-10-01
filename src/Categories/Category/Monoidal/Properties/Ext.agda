{-# OPTIONS --safe --without-K #-}

-- Sliding a closed morphism out of a one-hole context (`Hole.slide`), and the
-- centrality of scalars.
--
-- `J` and `ℓ⇐` are parameters rather than the monoidal unit and its unitor
-- because at the intended instance they are NOT that: the machine layer's closed
-- interface and the G construction's tensor unit are the empty interface spelled
-- with two different empty types, and identifying them is a measured 150 s
-- (`docs/stduc-supersession-plan.md` §1.1).  The two facts the slide actually
-- spends — naturality of the wire, and the slide at the hole `J` itself — are
-- cheap at the instance, so they are what the module asks for.

open import Categories.Category
open import Categories.Category.Monoidal.Core

module Categories.Category.Monoidal.Properties.Ext
  {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Morphism.Reasoning C

open Category C
open Monoidal M
open Shorthands

-- Kelly–Laplaza: scalars are central, so a pair of them merges into their
-- composite across `λ⇐`.
scalar-λ⇐ : (σ τ : unit ⇒ unit) → σ ⊗₁ τ ∘ λ⇐ ≈ λ⇐ ∘ (σ ∘ τ)
scalar-λ⇐ σ τ = begin
  σ ⊗₁ τ ∘ λ⇐              ≈⟨ serialize₁₂ ⟩∘⟨refl ⟩
  (σ ⊗₁ id ∘ id ⊗₁ τ) ∘ λ⇐ ≈⟨ assoc ⟩
  σ ⊗₁ id ∘ (id ⊗₁ τ ∘ λ⇐) ≈˘⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
  σ ⊗₁ id ∘ (λ⇐ ∘ τ)       ≈⟨ refl⟩∘⟨ (coherence-inv₃ ⟩∘⟨refl) ⟩
  σ ⊗₁ id ∘ (ρ⇐ ∘ τ)       ≈⟨ sym-assoc ⟩
  (σ ⊗₁ id ∘ ρ⇐) ∘ τ       ≈˘⟨ unitorʳ-commute-to ⟩∘⟨refl ⟩
  (ρ⇐ ∘ σ) ∘ τ             ≈⟨ assoc ⟩
  ρ⇐ ∘ (σ ∘ τ)             ≈˘⟨ coherence-inv₃ ⟩∘⟨refl ⟩
  λ⇐ ∘ (σ ∘ τ)             ∎

private variable A K₁ K₂ L P W W′ X Y : Obj

pad-inv : {h : X ⇒ Y} {h⁻ : Y ⇒ X} → h ∘ h⁻ ≈ id → id {L} ⊗₁ h ∘ id ⊗₁ h⁻ ≈ id
pad-inv e = merge₂ˡ ○ refl⟩⊗⟨ e ○ ⊗.identity

pad-transport : (h : K₁ ⇒ K₂) (s : W ⇒ W′) → id ⊗₁ s ∘ h ⊗₁ id ≈ h ⊗₁ id ∘ id ⊗₁ s
pad-transport _ _ = parallel id-comm-sym id-comm

ρα-λ : ρ⇒ {P} ⊗₁ id {A} ∘ α⇐ ≈ id ⊗₁ λ⇒
ρα-λ = ((⟺ triangle) ⟩∘⟨refl) ○ cancelʳ associator.isoʳ

αρ-λ : α⇒ ∘ ρ⇐ {P} ⊗₁ id {A} ≈ id ⊗₁ λ⇐
αρ-λ = (refl⟩∘⟨ (⟺ triangle-inv)) ○ cancelˡ associator.isoʳ

module Hole {J : Obj} (ℓ⇐ : {B : Obj} → B ⇒ J ⊗₀ B)
            (ℓ-nat : {A B : Obj} (f : A ⇒ B) → ℓ⇐ ∘ f ≈ (id ⊗₁ f) ∘ ℓ⇐)
            (ℓ-slide : {Y : Obj} (m : J ⇒ Y ⊗₀ J)
                     → (id ⊗₁ ℓ⇐ {J}) ∘ m ≈ α⇒ ∘ ((m ⊗₁ id) ∘ ℓ⇐ {J}))
            where

  slide : {Y B : Obj} (m : J ⇒ Y ⊗₀ J) (x : J ⇒ B)
        → (id ⊗₁ (ℓ⇐ ∘ x)) ∘ m ≈ (α⇒ ∘ ((m ⊗₁ id) ∘ ℓ⇐)) ∘ x
  slide m x = begin
    (id ⊗₁ (ℓ⇐ ∘ x)) ∘ m
      ≈⟨ (refl⟩⊗⟨ ℓ-nat x) ⟩∘⟨refl ⟩
    (id ⊗₁ ((id ⊗₁ x) ∘ ℓ⇐)) ∘ m
      ≈⟨ split₂ˡ ⟩∘⟨refl ⟩
    ((id ⊗₁ (id ⊗₁ x)) ∘ (id ⊗₁ ℓ⇐)) ∘ m
      ≈⟨ assoc ⟩
    (id ⊗₁ (id ⊗₁ x)) ∘ ((id ⊗₁ ℓ⇐) ∘ m)
      ≈⟨ refl⟩∘⟨ ℓ-slide m ⟩
    (id ⊗₁ (id ⊗₁ x)) ∘ (α⇒ ∘ ((m ⊗₁ id) ∘ ℓ⇐))
      ≈⟨ sym-assoc ⟩
    ((id ⊗₁ (id ⊗₁ x)) ∘ α⇒) ∘ ((m ⊗₁ id) ∘ ℓ⇐)
      ≈⟨ ⟺ assoc-commute-from ⟩∘⟨refl ⟩
    (α⇒ ∘ ((id ⊗₁ id) ⊗₁ x)) ∘ ((m ⊗₁ id) ∘ ℓ⇐)
      ≈⟨ (refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl)) ⟩∘⟨refl ⟩
    (α⇒ ∘ (id ⊗₁ x)) ∘ ((m ⊗₁ id) ∘ ℓ⇐)
      ≈⟨ assoc ⟩
    α⇒ ∘ ((id ⊗₁ x) ∘ ((m ⊗₁ id) ∘ ℓ⇐))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ ∘ (((id ⊗₁ x) ∘ (m ⊗₁ id)) ∘ ℓ⇐)
      ≈⟨ refl⟩∘⟨ (⟺ serialize₂₁ ⟩∘⟨refl) ⟩
    α⇒ ∘ ((m ⊗₁ x) ∘ ℓ⇐)
      ≈⟨ refl⟩∘⟨ (serialize₁₂ ⟩∘⟨refl) ⟩
    α⇒ ∘ (((m ⊗₁ id) ∘ (id ⊗₁ x)) ∘ ℓ⇐)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    α⇒ ∘ ((m ⊗₁ id) ∘ ((id ⊗₁ x) ∘ ℓ⇐))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⟺ (ℓ-nat x)) ⟩
    α⇒ ∘ ((m ⊗₁ id) ∘ (ℓ⇐ ∘ x))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ ∘ (((m ⊗₁ id) ∘ ℓ⇐) ∘ x)
      ≈⟨ sym-assoc ⟩
    (α⇒ ∘ ((m ⊗₁ id) ∘ ℓ⇐)) ∘ x ∎
