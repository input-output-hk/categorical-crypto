{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.Wiring where

open import Data.Empty
open import Data.Maybe.Base
open import Data.Maybe.Properties using (just-injective)
open import Data.Product.Base
open import Function.Base using (case_of_)
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Reindex as Re
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
import CategoricalCrypto.Machine.Relational.Wiring as W

private variable A B C D : Channel

reindex : {R : Initialized A B}
          (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
          (q : Channel.outType (A M.⊗ᵀ B) → Channel.outType (C M.⊗ᵀ D))
        → (∀ o → app (p {Out}) (q o) ≡ o) → (∀ o → q (app (p {Out}) o) ≡ o)
        → Presentation R → Presentation (W.modify p R)
reindex {R = R} p q pq qp P = record
  { initialₚ = initialₚ P
  ; stepₚ = λ s i → mapₚ (λ r → proj₁ r , q (proj₂ r)) (stepₚ P s (app (p {In}) i))
  ; initial-sound = initial-sound P
  ; initial-complete = initial-complete P
  ; step-sound = λ { {s} {i} {o} {s′} path →
      let (t , b) , inner , eq = map-unpath (λ r → proj₁ r , q (proj₂ r)) path
      in subst₂ (λ t b → M.Machine.stepRel (machine R) s (app (p {In}) i) (just b) t)
        (cong proj₁ eq) (trans (sym (pq b)) (cong (λ r → app (p {Out}) (proj₂ r)) eq)) (step-sound P inner) }
  ; step-complete = λ { {s} {i} {o} {s′} path →
      subst (λ b → Positive (mapₚ (λ r → proj₁ r , q (proj₂ r)) (stepₚ P s (app (p {In}) i))) (s′ , b))
        (qp o) (map-path (λ r → proj₁ r , q (proj₂ r)) (step-complete P path)) }
  ; no-refusal = no-refusal P
  }

pair : Initialized A B → Initialized C D → Initialized (A ⊗₀ B ᵀ) ((C ⊗₀ D ᵀ) ᵀ)
pair R S = initialize (Re.Pair (machine R) (machine S)) λ s → initial R (proj₁ s) × initial S (proj₂ s)

module _ {R : Initialized A B} {S : Initialized C D} (P : Presentation R) (Q : Presentation S) where
  open M.Machine (machine R) renaming (State to RS)
  open M.Machine (machine S) renaming (State to SS)

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
              ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine

    pair-step : RS × SS → Channel.inType ((A ⊗₀ B ᵀ) M.⊗ᵀ ((C ⊗₀ D ᵀ) ᵀ))
              → Dₚ ((RS × SS) × Channel.outType ((A ⊗₀ B ᵀ) M.⊗ᵀ ((C ⊗₀ D ᵀ) ᵀ)))
    pair-step (s , t) (inj₁ i) = mapₚ (λ r → (proj₁ r , t) , inj₁ (proj₂ r)) (stepₚ P s i)
    pair-step (s , t) (inj₂ i) = mapₚ (λ r → (s , proj₁ r) , inj₂ (proj₂ r)) (stepₚ Q t i)

    pair-sound : ∀ {s i o s′} → Positive (pair-step s i) (s′ , o)
               → M.Tensor.CompRel (machine R) (machine S) s i (just o) s′
    pair-sound {s = s , t} {i = inj₁ i} path =
      let (s′ , o) , inner , eq = map-unpath (λ r → (proj₁ r , t) , inj₁ (proj₂ r)) path
      in subst₂ (λ s′ o → M.Tensor.CompRel (machine R) (machine S) (s , t) (inj₁ i) (just o) s′)
        (cong proj₁ eq) (cong proj₂ eq) (M.Tensor.Step₁ (step-sound P inner))
    pair-sound {s = s , t} {i = inj₂ i} path =
      let (t′ , o) , inner , eq = map-unpath (λ r → (s , proj₁ r) , inj₂ (proj₂ r)) path
      in subst₂ (λ s′ o → M.Tensor.CompRel (machine R) (machine S) (s , t) (inj₂ i) (just o) s′)
        (cong proj₁ eq) (cong proj₂ eq) (M.Tensor.Step₂ (step-sound Q inner))

    pair-support : ∀ {s i o s′} → M.Tensor.CompRel (machine R) (machine S) s i o s′
                 → ∃ λ b → (o ≡ just b) × Positive (pair-step s i) (s′ , b)
    pair-support (M.Tensor.Step₁ {m' = just o} path) =
      inj₁ o , refl , map-path _ (step-complete P path)
    pair-support (M.Tensor.Step₁ {m' = nothing} path) = ⊥-elim (no-refusal P path)
    pair-support (M.Tensor.Step₂ {m' = just o} path) =
      inj₂ o , refl , map-path _ (step-complete Q path)
    pair-support (M.Tensor.Step₂ {m' = nothing} path) = ⊥-elim (no-refusal Q path)

    pair-presentation : Presentation (pair R S)
    pair-presentation = record
      { initialₚ = initialₚ P >>=ₚ λ s → mapₚ (s ,_) (initialₚ Q)
      ; stepₚ = pair-step
      ; initial-sound = λ path →
          let s , outer , inner = bind-unpath path
              t , right , eq = map-unpath (s ,_) inner
          in subst (λ r → initial R (proj₁ r) × initial S (proj₂ r)) eq (initial-sound P outer , initial-sound Q right)
      ; initial-complete = λ { (p , q) → bind-path (initial-complete P p) (map-path _ (initial-complete Q q)) }
      ; step-sound = pair-sound
      ; step-complete = λ { {s} {i} {o} {s′} path →
          let b , eq , pos = pair-support path
          in subst (λ b → Positive (pair-step s i) (s′ , b)) (sym (just-injective eq)) pos }
      ; no-refusal = λ path → case pair-support path of λ { (b , () , pos) }
      }

    tensor-presentation : Presentation (R W.⊗₁ S)
    tensor-presentation = reindex (M.⊗σ {A} {B} {C} {D}) rearrange left right pair-presentation
      where
      rearrange : (Channel.outType A ⊎ Channel.inType B) ⊎ (Channel.outType C ⊎ Channel.inType D)
                → (Channel.outType A ⊎ Channel.outType C) ⊎ (Channel.inType B ⊎ Channel.inType D)
      rearrange (inj₁ (inj₁ a)) = inj₁ (inj₁ a)
      rearrange (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
      rearrange (inj₂ (inj₁ c)) = inj₁ (inj₂ c)
      rearrange (inj₂ (inj₂ d)) = inj₂ (inj₂ d)
      left : ∀ o → app (M.⊗σ {A} {B} {C} {D} {Out}) (rearrange o) ≡ o
      left (inj₁ (inj₁ a)) = refl
      left (inj₁ (inj₂ b)) = refl
      left (inj₂ (inj₁ c)) = refl
      left (inj₂ (inj₂ d)) = refl
      right : ∀ o → rearrange (app (M.⊗σ {A} {B} {C} {D} {Out}) o) ≡ o
      right (inj₁ (inj₁ a)) = refl
      right (inj₁ (inj₂ c)) = refl
      right (inj₂ (inj₁ b)) = refl
      right (inj₂ (inj₂ d)) = refl
