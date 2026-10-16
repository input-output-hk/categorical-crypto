{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalExtraction where

open import Axiom.ExcludedMiddle
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalScript as Script

module _ (lem : ExcludedMiddle 0ℓ) {A B C : Channel}
  (P : Initialized A B) (Q : Initialized B C) where
  private
    module S = Script.At {A} {B}
    PS = M.Machine.State (machine P)
    QS = M.Machine.State (machine Q)
    scripted = S.native lem []
    pre = W.modify M.∘σ (P W.⊗₁ Q)
    pre-script = W.modify M.∘σ (scripted W.⊗₁ Q)

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
              ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine

    tensor-step : ∀ {s t s′ t′ i o}
      → M.Tensor.CompRel (machine P) (machine Q) (s , t) i (just o) (s′ , t′)
      → (xs : S.Script) → S.Follows P s′ xs
      → ∃ λ ys → S.Follows P s ys ×
          M.Tensor.CompRel (machine scripted) (machine Q) (ys , t) i (just o) (xs , t′)
    tensor-step p xs rest with M.comp-view p
    ... | inj₁ (i , just o , refl , refl , refl , q) =
      (i , o) ∷ xs , S.next q rest , M.Tensor.Step₁ (S.step-hit lem i o xs)
    ... | inj₁ (i , nothing , eq , () , same , q)
    ... | inj₂ (i , just o , refl , refl , refl , q) = xs , rest , M.Tensor.Step₂ q
    ... | inj₂ (i , nothing , eq , () , same , q)

    pre-step : ∀ {s t s′ t′ i o}
      → M.Machine.stepRel (machine pre) (s , t) i (just o) (s′ , t′)
      → (xs : S.Script) → S.Follows P s′ xs
      → ∃ λ ys → S.Follows P s ys ×
          M.Machine.stepRel (machine pre-script) (ys , t) i (just o) (xs , t′)
    pre-step p xs rest = tensor-step p xs rest

    trace-step : ∀ {s t s′ t′ i o}
      → M.TraceRel (machine pre) (s , t) i (just o) (s′ , t′)
      → ∃ λ xs → S.Follows P s xs × M.TraceRel (machine pre-script) (xs , t) i (just o) ([] , t′)
    trace-step {i = i} {o} M.Trace[ p ] =
      let xs , follows , p′ = pre-step {i = i} {o} p [] S.stop
      in xs , follows , M.Trace[ p′ ]
    trace-step {i = i} (M._Trace∷ₒ_ {outC = b} p rest) =
      let ys , follows , rest′ = trace-step rest
          xs , follows′ , p′ = pre-step {i = i} {o = inj₁ (inj₂ b)} p ys follows
      in xs , follows′ , p′ M.Trace∷ₒ rest′
    trace-step {i = i} (M._Trace∷ᵢ_ {inC = b} p rest) =
      let ys , follows , rest′ = trace-step rest
          xs , follows′ , p′ = pre-step {i = i} {o = inj₂ (inj₂ b)} p ys follows
      in xs , follows′ , p′ M.Trace∷ᵢ rest′

    extract : ∀ {s t s′ t′ i o}
      → M.Machine.stepRel (machine (Q W.∘ P)) (s , t) i (just o) (s′ , t′)
      → ∃ λ xs → S.Follows P s xs ×
          M.Machine.stepRel (machine (Q W.∘ S.native lem xs)) (xs , t) i (just o) ([] , t′)
    extract p = trace-step p
