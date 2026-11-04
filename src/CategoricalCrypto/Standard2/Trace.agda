{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.Standard2.Trace where

open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Reassociation as Reassociation
open import Categories.Category.Monoidal.Traced
import Categories.Functor.Monoidal.CurriedTensor.Properties as TensorProperties
open import Categories.Functor.Presheaf

open import CategoricalCrypto.Abstract2.Trace
open import CategoricalCrypto.Standard2

module _
  {o ℓ e cs ℓs : Level}
  (machines : MonoidalCategory o ℓ e)
  (ℰ-standard : Presheaf (MonoidalCategory.U machines) (Setoids cs ℓs))
  (traced : Traced (MonoidalCategory.monoidal machines))
  where

  open StdUC machines ℰ-standard
  open MonoidalReasoning monoidal
  open Reassociation monoidal
  open TensorProperties machines
  private
    module Base = Traced traced
    module Generic = TraceUC StdSetup monoidal

  module Trace where

    private variable
      A B Z X Y : Channel

    trace : A ⊗₀ Z ⇒ T₀ X (B ⊗₀ Z) → A ⇒ T₀ X B
    trace f = Base.trace (associator.to ∘ f)

    trace-sub : (s : Y ⇒ X) (f : A ⊗₀ Z ⇒ T₀ Y (B ⊗₀ Z))
              → trace (sub s ∘ f) ≈ sub s ∘ trace f
    trace-sub s f = begin
        Base.trace (associator.to ∘ sub s ∘ f)
          ≈⟨ Base.trace-resp-≈ (refl⟩∘⟨ (sub-⊗ s ⟩∘⟨refl)) ⟩
        Base.trace (associator.to ∘ (s ⊗₁ id) ∘ f)
          ≈⟨ Base.trace-resp-≈ (sym-assoc ○ (α⇐-⊗id-commute ⟩∘⟨refl) ○ assoc) ⟩
        Base.trace (((s ⊗₁ id) ⊗₁ id) ∘ associator.to ∘ f)
          ≈⟨ Base.tightenₗ ⟩
        (s ⊗₁ id) ∘ Base.trace (associator.to ∘ f)
          ≈⟨ (⟺ (sub-⊗ s)) ⟩∘⟨refl ⟩
        sub s ∘ trace f ∎

    traceEffect : Generic.TraceEffect
    traceEffect = record { trace = trace ; trace-sub = trace-sub }

    open Generic.TraceEffect traceEffect public using (TraceStable; UC-trace)
