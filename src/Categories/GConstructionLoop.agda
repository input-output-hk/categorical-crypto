{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Re-bracketing a trace's loop object along the middle-four interchange
-- `mid`: sliding (`Traced.Ext.trace-slide`) and `mid`'s involution.
------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE

module Categories.GConstructionLoop
  {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionTrace as GT

open GT C Monoidal Traced using (mid; mid-involutive)

private
  module C where
    open Category C public
    open Traced Traced public
    open U.Shorthands Monoidal public
    open import Categories.Category.Monoidal.Reasoning Monoidal public
      using (⊗-distrib-over-∘; _⟩⊗⟨_)
    open import Categories.Morphism.Reasoning C public using (cancelʳ)

open C
open HomReasoning

module WithTrace (L : TE.Laws Traced) where

  open TE.Laws L
  open TE Traced

  trace-conj : ∀ {X A A' B B'} {t : A ⊗₀ X ⇒ B ⊗₀ X}
                 {h : A' ⇒ A} {k : B ⇒ B'} →
               k ∘ trace t ∘ h ≈ trace (k ⊗₁ id ∘ t ∘ h ⊗₁ id)
  trace-conj = (refl⟩∘⟨ trace-∘ʳ) ○ trace-∘ˡ

  trace-mid : ∀ {A B P Q R S : Obj}
                {f : A ⊗₀ ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S)) ⇒
                     B ⊗₀ ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))} →
              trace f ≈
              trace (id ⊗₁ mid {P} {R} {Q} {S} ∘ f ∘ id ⊗₁ mid {P} {Q} {R} {S})
  trace-mid = ⟺ (trace-slide L ○ trace-resp-≈ (cancelʳ
    (⟺ ⊗-distrib-over-∘ ○ (identityˡ ⟩⊗⟨ mid-involutive) ○ ⊗.identity)))
