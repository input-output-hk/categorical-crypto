{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Cocartesian.Monoidal
open import Categories.Category.Cocartesian.SymmetricMonoidal
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
open import Categories.Category.Monoidal.Traced
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.CoproductTrace as CT
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Context as MDC
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Reasoning as MR
import Categories.Category.Monoidal.Traced.Ext as TE
import Categories.Category.Monoidal.Utilities as MU

module Categories.Category.Monoidal.CoproductTrace.Context {o ℓ e}
  (𝒱 : SymmetricMonoidalCategory o ℓ e) (dist : MD.MonoidalDistributive 𝒱)
  (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) (E : CT.CoproductTrace 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open CT.CoproductTrace E
open TE coproduct-traced
module Ambient = Traced coproduct-traced
module Sum = CE U cocartesian
module SumReasoning = MR (CocartesianMonoidal.+-monoidal cocartesian)
open WideSymmetricMonoidalSubcategory 𝒫
open MU.Shorthands monoidal
open Equiv
open import Categories.Category.Monoidal.Reassociation monoidal
open MR monoidal
open import Categories.Morphism.Reasoning U
open import Categories.Morphism.Reasoning.Ext U

private variable A B C D X Y P S T : Obj

trace-transfer : (f : A + X ⇒ B + X) (g : C + Y ⇒ D + Y)
                 (a : A ⇒ C) (b : B ⇒ D) (κ : X ⇒ Y) → Selected κ
               → g ∘ (a +₁ κ) ≈ (b +₁ κ) ∘ f
               → Ambient.trace g ∘ a ≈ b ∘ Ambient.trace f
trace-transfer f g a b κ selected-κ hyp = ⟺ Ambient.tightenᵣ
  ○ trace-uniform κ selected-κ
    (pullʳ (+₁∘+₁ ○ +₁-cong₂ identityʳ identityˡ) ○ hyp
      ○ ⟺ (pullˡ (+₁∘+₁ ○ +₁-cong₂ identityˡ identityʳ)))
  ○ Ambient.tightenₗ

-- In a cocartesian category every scalar is the identity, so a detached
-- feedback wire contributes nothing (normality of a coproduct trace).
trace-id : Ambient.trace (id {A + X}) ≈ id
trace-id {A} {X} = ⟺ (Ambient.trace-resp-≈
    (elim-center refl ○ +₁∘+₁ ○ +₁-cong₂ inject₁ identity² ○ id+₁id))
  ○ trace-map (id {(A + ⊥) + X}) i₁ [ id , ¡ ]
  ○ (refl⟩∘⟨ elimˡ at-unit) ○ inject₁
  where
  at-unit : Ambient.trace (id {(A + ⊥) + X}) ≈ id
  at-unit = ⟺ (Ambient.trace-resp-≈
      ((refl⟩∘⟨ elimˡ id+₁id) ○ Sum.⊕.associator.isoˡ))
    ○ Ambient.superposing
    ○ +₁-cong₂ refl (¡-unique₂ _ _) ○ id+₁id

trace-sum : (f : A ⇒ B) → Ambient.trace {X = X} (f +₁ id) ≈ f
trace-sum f = ⟺ (Ambient.trace-resp-≈ identityˡ) ○ Ambient.tightenᵣ
  ○ elimˡ trace-id

present : (S ⊗₀ (A + X) ⇒ S ⊗₀ (B + Y)) → (S ⊗₀ A) + (S ⊗₀ X) ⇒ (S ⊗₀ B) + (S ⊗₀ Y)
present k = δ⇐ ∘ k ∘ distributeˡ

private
  module Direct (S : Obj) where
    module C = MDC 𝒱 dist S

    trace : (S ⊗₀ (A + X) ⇒ S ⊗₀ (B + X)) → S ⊗₀ A ⇒ S ⊗₀ B
    trace k = Ambient.trace (present k)

    present-∘ : (f : S ⊗₀ (B + Y) ⇒ S ⊗₀ (C + D)) (g : S ⊗₀ (A + X) ⇒ S ⊗₀ (B + Y))
              → present (f ∘ g) ≈ present f ∘ present g
    present-∘ f g = refl⟩∘⟨ (assoc ○ insertInner distributeˡ.isoʳ) ○ sym-assoc

    present-sum : (f : S ⊗₀ A ⇒ S ⊗₀ B) (g : S ⊗₀ X ⇒ S ⊗₀ Y)
                  → present (f C.Context.+₁ g) ≈ f +₁ g
    present-sum f g = pullˡ (refl⟩∘⟨ C.context-+₁ f g ○ cancelˡ distributeˡ.isoˡ) ○ cancelʳ distributeˡ.isoˡ

    left-coherence : (δ⇐ +₁ id) ∘ δ⇐ ∘ C.Context.+-assocʳ {A} {X} {Y} ≈ +-assocʳ ∘ (id +₁ δ⇐) ∘ δ⇐
    left-coherence = δ-unique
      (assoc ○ refl⟩∘⟨ pullʳ C.Context+.α+⇐-i₁ ○ refl⟩∘⟨ pullˡ δ⇐-i₁ ○ pullˡ +₁∘i₁ ○ pullʳ δ⇐-i₁
        ○ ⟺ (assoc ○ refl⟩∘⟨ pullʳ δ⇐-i₁ ○ refl⟩∘⟨ (+₁∘i₁ ○ identityʳ) ○ Sum.α+⇐-i₁))
      (assoc ○ refl⟩∘⟨ (pullʳ C.Context+.α+⇐-i₂
          ○ refl⟩∘⟨ C.context-+₁ _ id ○ cancelˡ distributeˡ.isoˡ)
        ○ pullˡ (+₁∘+₁ ○ +₁-cong₂ δ⇐-i₂ identity²)
        ○ ⟺ (assoc ○ refl⟩∘⟨ pullʳ δ⇐-i₂ ○ refl⟩∘⟨ +₁∘i₂ ○ pullˡ Sum.α+⇐-i₂))

    right-coherence : C.Context.+-assocˡ {A} {X} {Y} ∘ distributeˡ ∘ (distributeˡ +₁ id)
                      ≈ distributeˡ ∘ (id +₁ distributeˡ) ∘ +-assocˡ
    right-coherence = inv-resp
      (pullʳ (pullʳ (cancelˡ (SumReasoning.⊗-cancel distributeˡ.isoʳ identity²))
        ○ cancelˡ distributeˡ.isoʳ) ○ C.Context+.⊕.associator.isoʳ)
      (pullʳ (pullʳ (cancelˡ distributeˡ.isoˡ)
        ○ cancelˡ (SumReasoning.⊗-cancel identity² distributeˡ.isoˡ)) ○ Sum.⊕.associator.isoˡ)
      left-coherence

    reassociate : (k : S ⊗₀ (A + (X + Y)) ⇒ S ⊗₀ (B + (C + Y)))
      → (δ⇐ +₁ id) ∘ present (C.Context.+-assocʳ ∘ k ∘ C.Context.+-assocˡ) ∘ (distributeˡ +₁ id)
      ≈ +-assocʳ ∘ ((id +₁ δ⇐) ∘ present k ∘ (id +₁ distributeˡ)) ∘ +-assocˡ
    reassociate k =
      refl⟩∘⟨ (assoc ○ refl⟩∘⟨ (assoc ○ assoc ○ refl⟩∘⟨ assoc))
      ○ assoc²εβ ○ left-coherence ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ right-coherence
      ○ ⟺ (refl⟩∘⟨ (assoc ○ refl⟩∘⟨ (assoc ○ assoc ○ refl⟩∘⟨ assoc)))

    vanish₂ : (k : S ⊗₀ (A + (X + Y)) ⇒ S ⊗₀ (B + (X + Y)))
              → trace (trace (C.Context.+-assocʳ ∘ k ∘ C.Context.+-assocˡ)) ≈ trace k
    vanish₂ k =
      Ambient.trace-resp-≈ (⟺ (trace-map (present (C.Context.+-assocʳ ∘ k ∘ C.Context.+-assocˡ)) distributeˡ δ⇐))
      ○ Ambient.trace-resp-≈ (Ambient.trace-resp-≈ (reassociate k))
      ○ Ambient.vanishing₂
      ○ trace-loop (present k) δ⇐ distributeˡ distributeˡ.isoʳ

    yank : trace (C.Context.+-swap {X} {X}) ≈ id
    yank = Ambient.trace-resp-≈ ((refl⟩∘⟨ cancelʳ distributeˡ.isoˡ)
      ○ ∘-distribˡ-[] ○ []-cong₂ δ⇐-i₂ δ⇐-i₁
      ○ ⟺ (Sum.braiding-swap Ambient.symmetric)) ○ Ambient.yanking

    unpresent : (k : (S ⊗₀ (A + C)) + Y ⇒ (S ⊗₀ (B + D)) + Y)
                → Ambient.trace k ≈ distributeˡ ∘ Ambient.trace ((δ⇐ +₁ id) ∘ k ∘ (distributeˡ +₁ id)) ∘ δ⇐
    unpresent k = ⟺ (refl⟩∘⟨ (trace-map k distributeˡ δ⇐ ⟩∘⟨refl)
      ○ refl⟩∘⟨ assoc ○ cancelˡ distributeˡ.isoʳ ○ cancelʳ distributeˡ.isoʳ)

    superpose : (k : S ⊗₀ (A + X) ⇒ S ⊗₀ (B + X))
                → trace (C.Context.+-assocʳ ∘ (id {S ⊗₀ P} C.Context.+₁ k) ∘ C.Context.+-assocˡ)
                ≈ id C.Context.+₁ trace k
    superpose k = unpresent (present (C.Context.+-assocʳ ∘ (id C.Context.+₁ k) ∘ C.Context.+-assocˡ))
      ○ refl⟩∘⟨ (Ambient.trace-resp-≈ (reassociate (id C.Context.+₁ k)
        ○ (refl⟩∘⟨ (refl⟩∘⟨ present-sum id k ⟩∘⟨refl ○ SumReasoning.merge₂³) ⟩∘⟨refl))
        ○ Ambient.superposing) ⟩∘⟨refl
      ○ ⟺ (C.context-+₁ id (trace k))

context-traced : (S : Obj) → Traced (CocartesianMonoidal.+-monoidal (MDC.context-cocartesian 𝒱 dist S))
context-traced S = record
  { symmetric    = CocartesianSymmetricMonoidal.+-symmetric
      (MDC.Context 𝒱 dist S) (MDC.context-cocartesian 𝒱 dist S)
  ; trace        = trace
  ; trace-resp-≈ = λ eq → Ambient.trace-resp-≈ (refl⟩∘⟨ eq ⟩∘⟨refl)
  ; slide        = Ambient.trace-resp-≈ (present-∘ _ _ ○ refl⟩∘⟨ present-sum id _) ○ Ambient.slide
      ○ Ambient.trace-resp-≈ (⟺ (present-∘ _ _ ○ present-sum id _ ⟩∘⟨refl))
  ; tightenₗ     = Ambient.trace-resp-≈ (present-∘ _ _ ○ present-sum _ id ⟩∘⟨refl) ○ Ambient.tightenₗ
  ; tightenᵣ     = Ambient.trace-resp-≈ (present-∘ _ _ ○ refl⟩∘⟨ present-sum _ id) ○ Ambient.tightenᵣ
  ; vanishing₁   = Ambient.trace-resp-≈ (present-sum _ id) ○ trace-sum _
  ; vanishing₂   = vanish₂ _
  ; superposing  = superpose _
  ; yanking      = yank
  }
  where open Direct S

module At (S : Obj) = Traced (context-traced S)

vanish-step : (S : Obj) (k : S ⊗₀ (A + (X + Y)) ⇒ S ⊗₀ (B + (X + Y)))
            → At.trace S (At.trace S (id ⊗₁ +-assocʳ ∘ (k ∘ id ⊗₁ +-assocˡ))) ≈ At.trace S k
vanish-step S k = trace-resp-≈ (trace-resp-≈ (C.context-α⇐ ⟩∘⟨ refl⟩∘⟨ C.context-α⇒)) ○ vanishing₂
  where module C = MDC 𝒱 dist S; open At S

super-step : (S : Obj) (g : S ⊗₀ (A + X) ⇒ S ⊗₀ (B + X))
           → At.trace S (id ⊗₁ +-assocʳ ∘ (tstep id g ∘ id ⊗₁ +-assocˡ)) ≈ tstep (id {S ⊗₀ P}) (At.trace S g)
super-step S g = trace-resp-≈ (C.context-α⇐ ⟩∘⟨ ⟺ (C.context-+₁ id g) ⟩∘⟨ C.context-α⇒)
  ○ superposing ○ C.context-+₁ id (trace g)
  where module C = MDC 𝒱 dist S; open At S

trace-state : (θ : S ⇒ T) → Selected θ
             → {k : S ⊗₀ (A + X) ⇒ S ⊗₀ (B + X)} {k′ : T ⊗₀ (A + X) ⇒ T ⊗₀ (B + X)}
             → θ ⊗₁ id ∘ k ≈ k′ ∘ θ ⊗₁ id
             → θ ⊗₁ id ∘ At.trace S k ≈ At.trace T k′ ∘ θ ⊗₁ id
trace-state θ selected-θ {k} {k′} eq = ⟺ (trace-transfer
  (present k) (present k′) (θ ⊗₁ id) (θ ⊗₁ id) (θ ⊗₁ id)
  (selected-⊗₁ selected-θ selected-id)
  (assoc ○ (refl⟩∘⟨ (pullʳ (distributeˡ-natural θ)
    ○ pullˡ (⟺ eq) ○ assoc)) ○ pullˡ (δ⇐-natural θ) ○ assoc))

private
  frame-to : α⇒ {P} {S} {A + B} ∘ distributeˡ
            ≈ id ⊗₁ distributeˡ ∘ distributeˡ ∘ (α⇒ +₁ α⇒)
  frame-to = insertˡ (⊗-cancel identity² distributeˡ.isoʳ)
    ○ (refl⟩∘⟨ (insertˡ distributeˡ.isoʳ
      ○ (refl⟩∘⟨ (assoc²εβ ○ (⟺ δ⇐-assoc⇒ ⟩∘⟨refl) ○ cancelʳ distributeˡ.isoˡ))))

  frame-from : (α⇒ {P} {S} {A} +₁ α⇒ {P} {S} {B}) ∘ δ⇐ ∘ α⇐
              ≈ δ⇐ ∘ id ⊗₁ δ⇐
  frame-from = pullˡ δ⇐-assoc⇒ ○ assoc ○ (refl⟩∘⟨ cancelʳ associator.isoʳ)

  frame-present : (k : S ⊗₀ (A + X) ⇒ S ⊗₀ (B + X))
    → (α⇒ {P} +₁ α⇒) ∘ present (α⇐ ∘ id ⊗₁ k ∘ α⇒)
    ≈ (δ⇐ ∘ id ⊗₁ present k ∘ distributeˡ) ∘ (α⇒ +₁ α⇒)
  frame-present k =
    (refl⟩∘⟨ refl⟩∘⟨ assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc) ○ assoc²εβ
    ○ (frame-from ⟩∘⟨refl) ○ assoc
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ frame-to)
    ○ (refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ)
    ○ (refl⟩∘⟨ pullˡ merge₂ˡ) ○ assoc²εβ

trace-frame : (P S : Obj) (k : S ⊗₀ (A + X) ⇒ S ⊗₀ (B + X))
            → At.trace (P ⊗₀ S) (α⇐ ∘ id ⊗₁ k ∘ α⇒) ≈ α⇐ ∘ id ⊗₁ At.trace S k ∘ α⇒
trace-frame P S k = introˡ associator.isoˡ ○ assoc
  ○ refl⟩∘⟨ ⟺ (trace-transfer (present (α⇐ ∘ id ⊗₁ k ∘ α⇒)) (δ⇐ ∘ id ⊗₁ present k ∘ distributeˡ)
                               α⇒ α⇒ α⇒ selected-α⇒ (⟺ (frame-present k)))
  ○ refl⟩∘⟨ tensor-strength (present k) ⟩∘⟨refl
