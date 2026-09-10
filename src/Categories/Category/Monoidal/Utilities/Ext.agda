{-# OPTIONS --safe --without-K #-}

-- Sliding a closed morphism out of a one-hole context.
--
-- A closed diagram `(id ⊗₁ (ℓ⇐ ∘ x)) ∘ m` — an ancilla produced by the closure
-- `m`, the hole filled by `x` — is the same as `x` followed by a context that no
-- longer mentions it.  Whatever quantifies over closed contexts with a hole at
-- `B` therefore quantifies over morphisms out of `B`.
--
-- `J` is the "closed" object and `ℓ⇐` the wire that opens a hole beside it.
-- They are parameters rather than the monoidal unit and its unitor because at
-- the intended instance they are NOT that: the machine layer's closed interface
-- and the G construction's tensor unit are the empty interface spelled with two
-- different empty types, and identifying them is a measured 150 s
-- (`docs/stduc-supersession-plan.md` §1.1).  The two facts the slide actually
-- spends — naturality of the wire, and the slide at the hole `J` itself — are
-- cheap at the instance, so they are what the module asks for.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

module Categories.Category.Monoidal.Utilities.Ext
  {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)

open Category C
open Monoidal M
open Shorthands

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
