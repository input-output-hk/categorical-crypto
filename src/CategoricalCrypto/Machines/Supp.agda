{-# OPTIONS --safe --without-K --guardedness #-}

-- Depth-`n` support (`Dp.Supp`) through the machine layer's Kleisli plumbing:
-- the pairing `id ⊗ pure _` a pre-trace step is entered by, and a traced
-- machine's step, bounded by what its entry and every pass of its loop reach.

open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter.Supp

open import CategoricalCrypto.Machines.Base

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Machines.Supp where

private
  module MC = Core (𝒱ₚ 0ℓ)

private variable A B D L X Y : Set

-- The Kleisli pairing `id ⊗ pure _` at a point, then `k`.
Supp-pair : (Φ : D → Set) (s : A) (z : B) (k : A × B → Dₚ D) → (∀ i → Supp i (k (s , z)) Φ)
          → ∀ n → Supp n ((returnₚ s >>=ₚ λ a → returnₚ z >>=ₚ λ b → returnₚ (a , b)) >>=ₚ k) Φ
Supp-pair Φ s z k h n =
  Supp-bind Φ n _ k (Supp-bind _ n _ _ (Supp-return _ _ (λ i →
    Supp-bind _ i _ _ (Supp-return _ _ (Supp-return _ _ h) i)) n))

module _ {S : MC.State} {k : MC.obj S × (X ⊎ L) → Dₚ (MC.obj S × (Y ⊎ L))}
         {J : MC.obj S × L → Set} {Ψ : MC.obj S × Y → Set}
         (loop : ∀ {sl} → J sl → ∀ n → Supp n (k (proj₁ sl , inj₂ (proj₂ sl))) (Turn J Ψ)) where

  private
    solve-Supp : ∀ p → Turn J Ψ p → ∀ j → Supp j (Col.MT.solve S X Y L k p) Ψ
    solve-Supp (_ , inj₁ _) ψ  j = Supp-bind Ψ j _ _ (Supp-return _ _ (Supp-return Ψ _ ψ) j)
    solve-Supp (_ , inj₂ _) jl j = Supp-bind Ψ j _ _ (Supp-return _ _ (Supp-iterₚ {u = Col.MT.loopBody S X Y L k}
      (λ {sl} jl′ → Supp-pair _ (proj₁ sl) (inj₂ (proj₂ sl)) k (loop jl′)) jl) j)

  Supp-traced : ∀ {s y} → (∀ n → Supp n (k (s , inj₁ y)) (Turn J Ψ))
              → ∀ n → Supp n (MC.step (Col.MT.traceᴹ X Y L (MC.mk S k)) (s , y)) Ψ
  Supp-traced {s} {y} entry n =
    Supp-bind Ψ n _ _ (Supp-pair _ s (inj₁ y) k (λ i → Supp-map _ _ solve-Supp i _ (entry i)) n)
