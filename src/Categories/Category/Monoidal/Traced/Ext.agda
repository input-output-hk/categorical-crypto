{-# OPTIONS --safe --without-K #-}

-- Laws of a traced symmetric monoidal category (Joyal–Street–Verity) that
-- agda-categories' `Traced` omits although its own header cites a *natural*
-- family: congruence, naturality on both sides, and Fubini (exchange of two
-- nested traces).  Dinaturality (sliding) is not a field: it follows
-- (`trace-slide`).

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U

open import Level

module Categories.Category.Monoidal.Traced.Ext
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (T : Traced M) where

open Category C
open Traced T
open U.Shorthands M
open BProps.Shorthands braided

open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric public using (β)

record Laws : Set (o ⊔ ℓ ⊔ e) where
  field
    trace-resp-≈ : ∀ {X A B} {f g : A ⊗₀ X ⇒ B ⊗₀ X} → f ≈ g → trace f ≈ trace g
    trace-∘ˡ : ∀ {X A B B′} {g : B ⇒ B′} {f : A ⊗₀ X ⇒ B ⊗₀ X} → g ∘ trace f ≈ trace (g ⊗₁ id ∘ f)
    trace-∘ʳ : ∀ {X A A′ B} {f : A ⊗₀ X ⇒ B ⊗₀ X} {h : A′ ⇒ A} → trace f ∘ h ≈ trace (f ∘ h ⊗₁ id)
    trace-comm : ∀ {X Y A B} {f : (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y}
               → trace (trace f) ≈ trace (trace (β ∘ f ∘ β))

module _ (L : Laws) where

  open Laws L

  -- Dinaturality (sliding), derived: yanking writes `g` as a trace, superposing
  -- and `trace-∘ˡ` merge it into the loop, `trace-comm` swaps the two loops, and
  -- yanking takes the second one away again.
  trace-slide : ∀ {X Y A B} {h : A ⊗₀ X ⇒ B ⊗₀ Y} {g : Y ⇒ X} →
                trace (id ⊗₁ g ∘ h) ≈ trace (h ∘ id ⊗₁ g)
  trace-slide {X} {Y} {A} {B} {h} {g} = ⟺ (begin
    trace (h ∘ id ⊗₁ g)
      ≈⟨ trace-resp-≈ (refl⟩∘⟨ (refl⟩⊗⟨ g-trace)) ⟩
    trace (h ∘ id ⊗₁ trace (σ⇒ ∘ g ⊗₁ id))
      ≈⟨ trace-resp-≈ (refl⟩∘⟨ ⟺ superposing) ⟩
    trace (h ∘ trace (α⇐ ∘ id ⊗₁ (σ⇒ ∘ g ⊗₁ id) ∘ α⇒))
      ≈⟨ trace-resp-≈ trace-∘ˡ ⟩
    trace (trace (h ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ∘ g ⊗₁ id) ∘ α⇒))
      ≈⟨ trace-comm ⟩
    trace (trace (β ∘ (h ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ∘ g ⊗₁ id) ∘ α⇒) ∘ β))
      ≈⟨ trace-resp-≈ (trace-resp-≈ ((refl⟩∘⟨ (wires ○ serialize₂₁)) ○ sym-assoc)) ⟩
    trace (trace ((β ∘ id ⊗₁ g) ∘ h ⊗₁ id))
      ≈˘⟨ trace-resp-≈ trace-∘ʳ ⟩
    trace (trace (β ∘ id ⊗₁ g) ∘ h)
      ≈⟨ trace-resp-≈ (unloop ⟩∘⟨refl) ⟩
    trace (id ⊗₁ g ∘ h) ∎)
    where
    open HomReasoning
    open import Categories.Category.Monoidal.Reasoning M
      using (⊗-distrib-over-∘; _⟩⊗⟨_; _⟩⊗⟨refl; refl⟩⊗⟨_; serialize₂₁)
    open import Categories.Morphism.Reasoning C using (cancelˡ; elimʳ; pullˡ)
    open import Data.Product using (_,_)

    g-trace : g ≈ trace (σ⇒ ∘ g ⊗₁ id)
    g-trace = ⟺ identityˡ ○ (⟺ yanking ⟩∘⟨refl) ○ trace-∘ʳ

    unloop : trace (β ∘ id ⊗₁ g) ≈ id {B} ⊗₁ g
    unloop = trace-resp-≈ (assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (⟺ ⊗.identity ⟩⊗⟨refl))
                          ○ (refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from)
                          ○ (refl⟩∘⟨ pullˡ (⟺ ⊗-distrib-over-∘ ○ (identityˡ ⟩⊗⟨ Equiv.refl))))
           ○ superposing
           ○ (refl⟩⊗⟨ (trace-resp-≈ (braiding.⇒.commute (id , g)) ○ ⟺ trace-∘ˡ ○ elimʳ yanking))

    wires : (h ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ∘ g ⊗₁ id) ∘ α⇒) ∘ β ≈ h ⊗₁ g
    wires = begin
      (h ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ∘ g ⊗₁ id) ∘ α⇒) ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒
        ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ) ⟩
      h ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ∘ g ⊗₁ id) ∘ id ⊗₁ σ⇒ ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (⟺ ⊗-distrib-over-∘ ○ (identityˡ ⟩⊗⟨ (assoc ○ swap-g))) ⟩
      h ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ g) ∘ α⇒
        ≈⟨ (refl⟩∘⟨ pullˡ assoc-commute-to) ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ associator.isoˡ) ⟩
      h ⊗₁ id ∘ (id ⊗₁ id) ⊗₁ g ∘ id
        ≈⟨ (refl⟩∘⟨ identityʳ) ○ (refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl)) ○ ⟺ ⊗-distrib-over-∘ ○ (identityʳ ⟩⊗⟨ identityˡ) ⟩
      h ⊗₁ g ∎
      where
      swap-g : σ⇒ ∘ g ⊗₁ id ∘ σ⇒ ≈ id {X} ⊗₁ g
      swap-g = (refl⟩∘⟨ ⟺ (braiding.⇒.commute (id , g))) ○ cancelˡ commutative
