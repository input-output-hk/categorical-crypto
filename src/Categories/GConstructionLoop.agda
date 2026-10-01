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

open C.HomReasoning

module WithTrace (L : TE.Laws Traced) where

  open TE.Laws L
  open TE Traced using (trace-slide)

  trace-conj : ∀ {X A A' B B'} {t : A C.⊗₀ X C.⇒ B C.⊗₀ X}
                 {h : A' C.⇒ A} {k : B C.⇒ B'} →
               k C.∘ C.trace t C.∘ h C.≈ C.trace (k C.⊗₁ C.id C.∘ t C.∘ h C.⊗₁ C.id)
  trace-conj = (refl⟩∘⟨ trace-∘ʳ) ○ trace-∘ˡ

  trace-mid : ∀ {A B P Q R S : C.Obj}
                {f : A C.⊗₀ ((P C.⊗₀ R) C.⊗₀ (Q C.⊗₀ S)) C.⇒
                     B C.⊗₀ ((P C.⊗₀ R) C.⊗₀ (Q C.⊗₀ S))} →
              C.trace f C.≈
              C.trace (C.id C.⊗₁ mid {P} {R} {Q} {S} C.∘ f C.∘ C.id C.⊗₁ mid {P} {Q} {R} {S})
  trace-mid = ⟺ (trace-slide L ○ trace-resp-≈ (C.cancelʳ
    (⟺ C.⊗-distrib-over-∘ ○ (C.identityˡ C.⟩⊗⟨ mid-involutive) ○ C.⊗.identity)))
