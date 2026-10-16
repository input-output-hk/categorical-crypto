{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalScript where

open import Axiom.ExcludedMiddle
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation.Canonical
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
open import CategoricalCrypto.Machine.Relational.Simulation using (_≲ᴿ_)

module At {A B : Channel} where
  Input = Channel.inType (A M.⊗ᵀ B)
  Output = Channel.outType (A M.⊗ᵀ B)
  Script = List (Input × Output)

  data Follows (P : Initialized A B) : M.Machine.State (machine P) → Script → Set where
    stop : ∀ {s} → Follows P s []
    next : ∀ {s s′ i o xs} → M.Machine.stepRel (machine P) s i (just o) s′
      → Follows P s′ xs → Follows P s ((i , o) ∷ xs)

  module _ (lem : ExcludedMiddle 0ℓ) where
    step : Script → Input → Dₚ (Script × Output)
    step [] i = botₚ
    step ((j , o) ∷ xs) i with lem {j ≡ i}
    ... | yes _ = returnₚ (xs , o)
    ... | no _ = botₚ

    step-hit : ∀ i o xs → Positive (step ((i , o) ∷ xs) i) (xs , o)
    step-hit i o xs with lem {i ≡ i}
    ... | yes _ = positive-return (xs , o)
    ... | no neq = ⊥-elim (neq refl)

    step-invert : ∀ {xs i o ys} → Positive (step xs i) (ys , o) → xs ≡ (i , o) ∷ ys
    step-invert {xs = []} p = ⊥-elim (positive-bot p)
    step-invert {xs = (j , b) ∷ xs} {i} p with lem {j ≡ i}
    ... | yes refl with positive-return-reflect p
    ... | refl = refl
    step-invert {xs = (j , b) ∷ xs} {i} p | no _ = ⊥-elim (positive-bot p)

    native : Script → Initialized A B
    native xs = fromₚ (returnₚ xs) step

    process : Script → EP.Proc A B
    process xs = EP.toPositive (presentₚ (returnₚ xs) step)

    replay : ∀ {P : Initialized A B} {s xs} → initial P s → Follows P s xs → native xs ≲ᴿ P
    replay {P} {s} {xs} init follows = record
      { Related = λ ys t → Follows P t ys
      ; initial-to = λ p → s , init , subst (Follows P s) (positive-return-reflect p) follows
      ; step-to = replay-step
      }
      where
      replay-step : ∀ {ys t i o zs} → Follows P t ys → M.Machine.stepRel (machine (native xs)) ys i o zs
        → ∃ λ t′ → M.Machine.stepRel (machine P) t i o t′ × Follows P t′ zs
      replay-step {o = nothing} follows ()
      replay-step {ys} {i = i} {o = just o} {zs} follows p with step-invert {xs = ys} {i} {o} {ys = zs} p
      ... | refl with follows
      ... | next q rest = _ , q , rest
