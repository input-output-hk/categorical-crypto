{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.Trace where

open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition
import ProbabilisticLogic.Dp.Positive.Loop as Loop

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
import CategoricalCrypto.Machine.Relational.Wiring as W

private variable A B C : Channel

module _ {R : Initialized (A ⊗₀ C) (B ⊗₀ C)} (P : Presentation R) where
  open M.Machine (machine R) renaming (State to S)
  private
    Input Output ExternalIn ExternalOut : Set
    Input = Channel.inType ((A ⊗₀ C) M.⊗ᵀ (B ⊗₀ C))
    Output = Channel.outType ((A ⊗₀ C) M.⊗ᵀ (B ⊗₀ C))
    ExternalIn = Channel.inType (A M.⊗ᵀ B)
    ExternalOut = Channel.outType (A M.⊗ᵀ B)

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
              ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine

    input : ExternalIn → Input
    input (inj₁ a) = inj₁ (inj₁ a)
    input (inj₂ b) = inj₂ (inj₁ b)

    output : ExternalOut → Output
    output (inj₁ a) = inj₁ (inj₁ a)
    output (inj₂ b) = inj₂ (inj₁ b)

    dispatch : S × Output → S × (ExternalOut ⊎ Input)
    dispatch (s , inj₁ (inj₁ a)) = s , inj₁ (inj₁ a)
    dispatch (s , inj₁ (inj₂ c)) = s , inj₂ (inj₂ (inj₂ c))
    dispatch (s , inj₂ (inj₁ b)) = s , inj₁ (inj₂ b)
    dispatch (s , inj₂ (inj₂ c)) = s , inj₂ (inj₁ (inj₂ c))

    body : Body S Input ExternalOut
    body (s , i) = mapₚ dispatch (stepₚ P s i)

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
              ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
              input output dispatch body

    dispatch-output : ∀ s o → dispatch (s , output o) ≡ (s , inj₁ o)
    dispatch-output s (inj₁ a) = refl
    dispatch-output s (inj₂ b) = refl

    run-sound : ∀ {s : S} {i : Input} {s′ : S} {o : ExternalOut}
              → Loop.Run body (body (s , i)) (s′ , o)
              → M.TraceRel (machine R) s i (just (output o)) s′
    run-sound {s} {i} (Loop.finish path refl) with
      map-unpath {A = S × Output} {B = S × (ExternalOut ⊎ Input)} dispatch {d = stepₚ P s i} path
    ... | (s , inj₁ (inj₁ a)) , inner , refl = M.Trace[ step-sound P inner ]
    ... | (s , inj₁ (inj₂ c)) , inner , ()
    ... | (s , inj₂ (inj₁ b)) , inner , refl = M.Trace[ step-sound P inner ]
    ... | (s , inj₂ (inj₂ c)) , inner , ()
    run-sound {s} {i} (Loop.again path rest) with
      map-unpath {A = S × Output} {B = S × (ExternalOut ⊎ Input)} dispatch {d = stepₚ P s i} path
    ... | (s , inj₁ (inj₁ a)) , inner , ()
    ... | (s , inj₁ (inj₂ c)) , inner , refl = step-sound P inner M.Trace∷ₒ run-sound rest
    ... | (s , inj₂ (inj₁ b)) , inner , ()
    ... | (s , inj₂ (inj₂ c)) , inner , refl = step-sound P inner M.Trace∷ᵢ run-sound rest

    run-complete : ∀ {s : S} {i : Input} {s′ : S} {o : ExternalOut}
                 → M.TraceRel (machine R) s i (just (output o)) s′
                 → Loop.Run body (body (s , i)) (s′ , o)
    run-complete {s} {i} {s′} {o} M.Trace[ path ] =
      Loop.finish (subst (λ r → Positive (body (s , i)) r) (dispatch-output s′ o)
        (map-path dispatch (step-complete P path))) refl
    run-complete (path M.Trace∷ₒ rest) = Loop.again (map-path dispatch (step-complete P path)) (run-complete rest)
    run-complete (path M.Trace∷ᵢ rest) = Loop.again (map-path dispatch (step-complete P path)) (run-complete rest)

    trace-no-refusal : ∀ {s : S} {i : Input} {s′ : S} → M.TraceRel (machine R) s i nothing s′ → ⊥
    trace-no-refusal M.Trace[ path ] = no-refusal P path
    trace-no-refusal (path M.Trace∷ₒ rest) = trace-no-refusal rest
    trace-no-refusal (path M.Trace∷ᵢ rest) = trace-no-refusal rest

    input-core : (i : ExternalIn) →
      app (M.∣ˡσ {A} {C} {B ⊗₀ C} {In}) (app (M.∣^ˡσ {A} {B} {C} {In}) i) ≡ input i
    input-core (inj₁ a) = refl
    input-core (inj₂ b) = refl

    output-core : (o : ExternalOut) →
      app (M.∣ˡσ {A} {C} {B ⊗₀ C} {Out}) (app (M.∣^ˡσ {A} {B} {C} {Out}) o) ≡ output o
    output-core (inj₁ a) = refl
    output-core (inj₂ b) = refl

    trace-presentation : Presentation (W.trace R)
    trace-presentation = record
      { initialₚ = initialₚ P
      ; stepₚ = λ s i → iterₚ body (s , input i)
      ; initial-sound = initial-sound P
      ; initial-complete = initial-complete P
      ; step-sound = λ { {s} {i} {o} {s′} path →
          subst₂ (λ i o → M.TraceRel (machine R) s i (just o) s′)
            (sym (input-core i)) (sym (output-core o))
            (run-sound (Loop.from-positive body (body (s , input i)) path)) }
      ; step-complete = λ { {s} {i} {o} {s′} path →
          Loop.to-positive (run-complete (subst₂ (λ i o → M.TraceRel (machine R) s i (just o) s′)
            (input-core i) (output-core o) path)) }
      ; no-refusal = trace-no-refusal
      }
