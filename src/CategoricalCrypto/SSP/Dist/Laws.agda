{-# OPTIONS --safe --without-K #-}

-- The laws of `_≈ᵈ_` (`docs/uc-setup-ssp-dist.md` §3): `_≈ᵏ_` laws of call
-- trees within an activation, which `stepwise` lifts to protocols, and
-- deferred sampling across activations (`defer`).

module CategoricalCrypto.SSP.Dist.Laws where

open import Data.Bool.Base
open import Data.Product.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Distribution.Uniform.Flip

open import CategoricalCrypto.SSP.Dist
open import CategoricalCrypto.SSP.Dist.Kernel
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol

private variable
  A B : Iface
  X Y Z : Set

------------------------------------------------------------------------
-- Within an activation

coins-comm : (κ : Coins X) (t : Calls A Y) (k : X → Y → Calls A Z)
           → (coins κ >>=ᶜ λ x → t >>=ᶜ k x) ≈ᵏ (t >>=ᶜ λ y → coins κ >>=ᶜ λ x → k x y)
coins-comm κ t k = mk≈ᵏ λ O s ξ → trans
  (⟦coins⟧ κ (λ x → t >>=ᶜ k x) O s ξ) (trans
  (>>=ᴹ-congˡ (sample κ) (λ x → ⟦ t >>=ᶜ k x ⟧ O s) (λ x → ⟦ t ⟧ O s >>=⊥ λ p → ⟦ k x (proj₁ p) ⟧ O (proj₂ p))
              (λ x → ⟦>>=ᶜ⟧ t (k x) O s) ξ) (trans
  (>>=ᴹ-comm⊥ (sample κ) (⟦ t ⟧ O s) (λ x p → ⟦ k x (proj₁ p) ⟧ O (proj₂ p)) ξ) (sym (trans
  (⟦>>=ᶜ⟧ t (λ y → coins κ >>=ᶜ λ x → k x y) O s ξ)
  (>>=⊥-congˡ (⟦ t ⟧ O s) (λ p → ⟦ coins κ >>=ᶜ (λ x → k x (proj₁ p)) ⟧ O (proj₂ p))
              (λ p → sample κ >>=ᴹ λ x → ⟦ k x (proj₁ p) ⟧ O (proj₂ p))
              (λ p → ⟦coins⟧ κ (λ x → k x (proj₁ p)) O (proj₂ p)) ξ)))))

coin-call : (μ : Dist-ℚ Bool) (c : Ch A) (q : Q A c) (k : Bool → R A c → Calls A X)
          → coin μ (λ b → call c q (k b)) ≈ᵏ call c q (λ r → coin μ λ b → k b r)
coin-call μ c q = coins-comm (toss μ done) (call c q ret)

coin-comm : (μ ν : Dist-ℚ Bool) (k : Bool → Bool → Calls A X)
          → coin μ (λ b → coin ν (k b)) ≈ᵏ coin ν (λ b′ → coin μ λ b → k b b′)
coin-comm μ ν = coins-comm (toss μ done) (coin ν ret)

coin-drop : (μ : Dist-ℚ Bool) (t : Calls A X) → coin μ (λ _ → t) ≈ᵏ t
coin-drop μ t = mk≈ᵏ λ O s → >>=ᴹ-const μ (⟦ t ⟧ O s)

coin-flip : (k : Bool → Calls A X) → coin uniform-Bool k ≈ᵏ coin uniform-Bool (k ∘ not)
coin-flip k = mk≈ᵏ λ O s → uniform-flip {f = λ b → ⟦ k b ⟧ O s} {g = λ b → ⟦ k (not b) ⟧ O s} λ where
  false → λ _ → refl
  true  → λ _ → refl

coin-xor : (m : Bool) (k : Bool → Calls A X) → coin uniform-Bool (λ b → k (m xor b)) ≈ᵏ coin uniform-Bool k
coin-xor false k = ≈ᵏ-refl
coin-xor true  k = ≈ᵏ-sym (coin-flip k)

------------------------------------------------------------------------
-- Across activations

defer : {P P′ : Protocol A B} (ρ : St P → Coins (St P′)) → sample (ρ (init P)) ≈Mℚ return-ℚ (init P′)
      → (∀ s c q → (coins (ρ s) >>=ᶜ λ s′ → step P′ s′ c q)
                   ≈ᵏ (step P s c q >>=ᶜ λ z → coins (ρ (proj₁ z)) >>=ᶜ λ s′ → ret (s′ , proj₂ z)))
      → P ≈ᵈ P′
defer ρ e h = ⊑⇒≈ᵈ (sampling ρ e h)

stepwise : {P P′ : Protocol A B} (θ : St P → St P′) → θ (init P) ≡ init P′
         → (∀ s c q → mapᶜ (map₁ θ) (step P s c q) ≈ᵏ step P′ (θ s) c q) → P ≈ᵈ P′
stepwise {P = P} θ e h = defer (done ∘ θ) (λ ξ → cong (λ s → lookupᴰℚ (entries (return-ℚ s)) ξ) e)
  λ s c q → ≈ᵏ-trans (≈ᵏ-sym (h s c q)) (≈ᶜ⇒≈ᵏ (≈ᶜ-sym (>>=ᶜ-ret (map₁ θ) (step P s c q))))
