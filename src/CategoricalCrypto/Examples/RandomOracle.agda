{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.Examples.RandomOracle where

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_)

open import Data.Fin using (Fin)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Properties using (just-injective)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Vec hiding (length; map)
open import Function.Base
import Relation.Binary.Reasoning.Setoid as RS

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Calls; Protocol; coin; ret; uniformVec)
open import CategoricalCrypto.Protocol.Observe

open import ProbabilisticLogic.Distribution.RationalDist renaming (_>>=ᴹ_ to _>>=_)
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform

module RandomOracle (p : ℕ) (In : Type) ⦃ _ : DecEq In ⦄ (outN : ℕ) where

  open import ProbabilisticLogic.Distribution.Uniform.Collision outN

  Out : Type
  Out = Vec Bool outN

  uniform-Out : Dist-ℚ Out
  uniform-Out = uniform-Vec outN

  Input  = Fin p × In
  Output = Fin p × Out
  Table  = List (In × Out)

  lookup-bs : Table → In → Maybe Out
  lookup-bs []             _ = nothing
  lookup-bs ((k , v) ∷ xs) q = case q ≟ k of λ where
    (yes _) → just v
    (no  _) → lookup-bs xs q

  lookup-bs-here : ∀ s q h → lookup-bs ((q , h) ∷ s) q ≡ just h
  lookup-bs-here s q h with q ≟ q
  ... | yes _  = refl
  ... | no ¬eq = ⊥-elim (¬eq refl)

  lookup-bs-there : ∀ s q h q′ → q′ ≢ q → lookup-bs ((q , h) ∷ s) q′ ≡ lookup-bs s q′
  lookup-bs-there s q h q′ ne with q′ ≟ q
  ... | yes p = ⊥-elim (ne p)
  ... | no  _ = refl

  lookup-bs-∈ : ∀ s q h → lookup-bs s q ≡ just h → (q , h) ∈ˡ s
  lookup-bs-∈ ((k , v) ∷ xs) q h eq with q ≟ k | eq
  ... | yes refl | eq′ = here (cong (q ,_) (just-injective (sym eq′)))
  ... | no  _    | eq′ = there (lookup-bs-∈ xs q h eq′)

  step : Table × Input → Dist-ℚ (Table × Output)
  step (s , i , q) = case lookup-bs s q of λ where
    (just h)  → return-ℚ (s , i , h)
    (nothing) → do h ← uniform-Out; return-ℚ ((q , h) ∷ s , i , h)

  step-hit : ∀ s i q h → lookup-bs s q ≡ just h → step (s , i , q) ≡ return-ℚ (s , i , h)
  step-hit s i q h eq rewrite eq = refl

  step-miss : ∀ s i q → lookup-bs s q ≡ nothing
            → step (s , i , q) ≡ (uniform-Out >>= λ h → return-ℚ ((q , h) ∷ s , i , h))
  step-miss s i q eq rewrite eq = refl

  --------------------------------------------------------------------
  -- The lazily sampled oracle as a call tree

  module Lazy where

    -- The lookup result is an ARGUMENT, so that `answer-eval` can case on it
    -- without reaching the scrutinee through the record projection.
    answer : Table → Input → Maybe Out → Calls unitᴵ (Table × Output)
    answer s (i , _) (just h) = ret (s , (i , h))
    answer s (i , q) nothing  = uniformVec outN λ h → ret ((q , h) ∷ s , (i , h))

    oracle : Protocol unitᴵ (Output ⇿ Input)
    oracle = record { St = Table ; init = [] ; step = λ s q → answer s q (lookup-bs s (proj₂ q)) }

    -- The `with` reaches the scrutinee inside `step` because the statement
    -- names it.
    answer-eval : {Z : Type} (⟦_⟧ : Calls unitᴵ (Table × Output) → Dist-ℚ Z)
                → (∀ μ g → ⟦ coin μ g ⟧ ≈Mℚ (μ >>= λ b → ⟦ g b ⟧))
                → (Go : Table × Output → Dist-ℚ Z) → (∀ o → ⟦ ret o ⟧ ≈Mℚ Go o)
                → ∀ s i q → ⟦ answer s (i , q) (lookup-bs s q) ⟧ ≈Mℚ (step (s , i , q) >>= Go)
    answer-eval ⟦_⟧ hom Go ret-eq s i q with lookup-bs s q
    ... | just h  = Mℚ.trans {i = ⟦ ret (s , i , h) ⟧} {j = Go (s , i , h)}
                      {k = return-ℚ (s , i , h) >>= Go}
                      (ret-eq (s , i , h))
                      (Mℚ.sym {x = return-ℚ (s , i , h) >>= Go} {y = Go (s , i , h)}
                              (>>=ᴹ-identityˡ (s , i , h) Go))
    ... | nothing = begin
      ⟦ uniformVec outN F ⟧
        ≈⟨ uniformVec-bind ⟦_⟧ hom outN F ⟩
      (uniform-Out >>= λ h → ⟦ F h ⟧)
        ≈⟨ >>=ᴹ-congˡ uniform-Out (λ h → ⟦ F h ⟧) (λ h → Rt h >>= Go)
             (λ h → Mℚ.trans {i = ⟦ F h ⟧} {j = Go ((q , h) ∷ s , i , h)} {k = Rt h >>= Go}
                      (ret-eq _)
                      (Mℚ.sym {x = Rt h >>= Go} {y = Go ((q , h) ∷ s , i , h)}
                              (>>=ᴹ-identityˡ ((q , h) ∷ s , i , h) Go))) ⟩
      (uniform-Out >>= λ h → Rt h >>= Go)
        ≈˘⟨ >>=ᴹ-assoc uniform-Out Rt Go ⟩
      ((uniform-Out >>= Rt) >>= Go)
        ∎
      where
        F  = λ h → ret ((q , h) ∷ s , (i , h))
        Rt = λ h → return-ℚ ((q , h) ∷ s , i , h)
        open RS (Mℚ-setoid _)

  --------------------------------------------------------------------
  -- Collision counting

  count-matches : Table → Out → ℚ
  count-matches s = countMatch (map proj₂ s)

  E-collisions : ∀ s
               → lookupᴰℚ (entries uniform-Out) (count-matches s)
               ≡ (fromℕ (length s)) * inv-pow-2 outN
  E-collisions s =
    trans (E-countMatch (map proj₂ s)) (cong (λ l → fromℕ l * inv-pow-2 outN) (length-map proj₂ s))

  triangle : ℕ → ℚ
  triangle zero    = 0ℚ
  triangle (suc k) = fromℕ k + triangle k

  state-collisions : Table → ℚ
  state-collisions []             = 0ℚ
  state-collisions ((_ , h) ∷ ps) = count-matches ps h + state-collisions ps
