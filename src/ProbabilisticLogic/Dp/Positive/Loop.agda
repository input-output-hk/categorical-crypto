{-# OPTIONS --safe --without-K --guardedness #-}

module ProbabilisticLogic.Dp.Positive.Loop where

open import Data.Product.Base
open import Data.Sum.Base
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Rational as ℚ using (0ℚ)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Positive

private variable
  a : Level
  S A B : Set a

-- This is finite successful relay, not an infinite-path/divergence semantics.
data Run {a : Level} {S A B : Set a} (u : Body S A B)
  (d : Dₚ (S × (B ⊎ A))) (sb : S × B) : Set a where
  finish : {s : S} {b : B} → Positive d (s , inj₁ b) → (s , b) ≡ sb → Run u d sb
  again : {s : S} {a : A} → Positive d (s , inj₂ a) → Run u (u (s , a)) sb → Run u d sb

prepend-delay : {u : Body S A B} {d e : Dₚ (S × (B ⊎ A))} {sb : S × B}
               (c : _) → 0ℚ ℚ.< wt d c → br d c ≡ inj₂ e → Run u e sb → Run u d sb
prepend-delay c pw eq (finish path endpoint) = finish (delay c _ pw eq path) endpoint
prepend-delay c pw eq (again path rest) = again (delay c _ pw eq path) rest

from-positive : (u : Body S A B) (d : Dₚ (S × (B ⊎ A))) {sb : S × B}
              → Positive (stepᵢ u d) sb → Run u d sb
from-positive u d (hit c pw eq) with br d c in branch
... | inj₁ (s , inj₁ b) = finish (hit c pw branch) (inj₁-injective eq)
... | inj₁ (s , inj₂ a) with eq
... | ()
from-positive u d (hit c pw eq) | inj₂ e with eq
... | ()
from-positive u d (delay c e pw eq path) with br d c in branch
... | inj₁ (s , inj₁ b) with eq
... | ()
from-positive u d (delay c e pw eq path) | inj₁ (s , inj₂ a) with inj₂-injective eq
... | refl = again (hit c pw branch) (from-positive u (u (s , a)) path)
from-positive u d (delay c e pw eq path) | inj₂ d′ with inj₂-injective eq
... | refl = prepend-delay c pw branch (from-positive u d′ path)

finish-path : (u : Body S A B) {d : Dₚ (S × (B ⊎ A))} {s : S} {b : B}
            → Positive d (s , inj₁ b) → Positive (stepᵢ u d) (s , b)
finish-path u (hit c pw eq) = hit c pw (cong (tagᵢ u) eq)
finish-path u (delay c e pw eq path) = delay c _ pw (cong (tagᵢ u) eq) (finish-path u path)

again-path : (u : Body S A B) {d : Dₚ (S × (B ⊎ A))} {s : S} {a : A} {sb : S × B}
           → Positive d (s , inj₂ a) → Positive (iterₚ u (s , a)) sb → Positive (stepᵢ u d) sb
again-path u (hit c pw eq) inner = delay c _ pw (cong (tagᵢ u) eq) inner
again-path u (delay c e pw eq path) inner = delay c _ pw (cong (tagᵢ u) eq) (again-path u path inner)

to-positive : {u : Body S A B} {d : Dₚ (S × (B ⊎ A))} {sb : S × B}
            → Run u d sb → Positive (stepᵢ u d) sb
to-positive (finish path refl) = finish-path _ path
to-positive (again path rest) = again-path _ path (to-positive rest)
