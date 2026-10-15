{-# OPTIONS --safe --without-K --guardedness #-}

module ProbabilisticLogic.Dp.Positive.Observation where

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no)

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Paths
open import ProbabilisticLogic.Dp.Positive.Monad

half-strict : {q : ℚ} → 0ℚ ℚ.< q → ½ ℚ.* q ℚ.< q
half-strict {q} pos = subst₂ ℚ._<_ (+-identityˡ (½ ℚ.* q)) (½*+½* q)
  (+-mono-<-≤ (0<½* pos) ≤-refl)

slack-positive : {A : Set} {d e : Dₚ A} (P : A → ℚ) → NNF P
               → (∀ ε → 0ℚ ℚ.< ε → Dom P ε d e)
               → PositiveTest d P → PositiveTest e P
slack-positive {d = d} {e} P nn h (n , pos) = result
  where
  q = cum n d P
  δ = ½ ℚ.* q
  witness = h δ (0<½* pos) n
  m = proj₁ witness
  bound = proj₂ witness
  result : PositiveTest e P
  result with 0ℚ ℚ.<? cum m e P
  ... | yes p = m , p
  ... | no neg = ⊥-elim (<-irrefl refl (<-≤-trans (half-strict pos)
    (subst (q ℚ.≤_) (trans (cong (ℚ._+ δ) (nonpositive-zero (cum-nn m e P nn) neg)) (+-identityˡ δ)) bound)))

ind-self-positive : ∀ b → 0ℚ ℚ.< indᵇ b b
ind-self-positive true = 0<1ℚ
ind-self-positive false = 0<1ℚ

ind-positive-reflect : ∀ b c → 0ℚ ℚ.< indᵇ b c → c ≡ b
ind-positive-reflect true true pos = refl
ind-positive-reflect false false pos = refl
ind-positive-reflect true false pos = ⊥-elim (<-irrefl refl pos)
ind-positive-reflect false true pos = ⊥-elim (<-irrefl refl pos)

slack-may-to : {d e : Dₚ Bool} → (∀ ε → 0ℚ ℚ.< ε → d ≼ₚ[ ε ] e) → d ≼₊ e
slack-may-to {d} {e} h P nn (n , pos) =
  let b , path , pb = positive-extract n d P nn pos
      source = positive-witness (indᵇ b) (indᵇ-nn b) path (ind-self-positive b)
      m , mass = slack-positive (indᵇ b) (indᵇ-nn b) (λ ε p → h ε p b) source
      c , target , pc = positive-extract m e (indᵇ b) (indᵇ-nn b) mass
  in positive-witness P nn target (subst (λ b → 0ℚ ℚ.< P b) (sym (ind-positive-reflect b c pc)) pb)

all-slacks⇒may : {d e : Dₚ Bool} → (∀ ε → 0ℚ ℚ.< ε → d ≈ₚ[ ε ] e) → d ≈₊ e
all-slacks⇒may h = slack-may-to (λ ε p → proj₁ (h ε p)) , slack-may-to (λ ε p → proj₂ (h ε p))
