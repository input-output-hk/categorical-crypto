{-# OPTIONS --safe --without-K --guardedness #-}

-- One emission per activation is not a query bound. A domain-triggered
-- backwards echo spends a query without receiving any budget. It admits no
-- direct QB certificate at any rate, for any implementation with a value.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Computational.Obstruction (𝔖 : Signature) where

open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties.Ext using (0≤1ℚ; 1≰0)
open import Data.Sum.Base hiding (map₂)
open import Data.Unit
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Symbolic.Computational.Run 𝔖
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.UC.QueryBound
open Terms 𝔖

backwards : (s : Signature.Sort 𝔖) → Role (Var (port s s)) (Var void)
backwards s = record
  { n = 1 ; Γ = λ _ → [] ; start = zero ; fresh = refl
  ; react = λ where
      zero (here refl) _ → emit zero [] (here refl) (var (here refl))
      zero (there ()) _ }

module _ (sch : Scheme) (s : Signature.Sort 𝔖) (b : Scheme.Bits sch) where
  open Execution sch

  private
    S = Configᶜ 1 (λ _ → [])
    state₀ : S
    state₀ = configᶜ zero []

    state-unique : (q : S) → q ≡ state₀
    state-unique (configᶜ zero []) = refl
    state-unique (configᶜ (suc ()) _)

    point = returnₚ state₀

    step : S × (Scheme.Bits sch ⊎ ⊥) → Dₚ (S × (Scheme.Bits sch ⊎ ⊥))
    step (q , inj₁ v) = mapₚ (map₂ (encodeᶜ (Var (port s s)) (Var void)))
      (stepᶜ 0 (backwards s) q (decodeᶜ (Var (port s s)) (Var void) (inj₁ v)))
    step (_ , inj₂ ())

    step-echo : step (state₀ , inj₁ b) ≈ₚ returnₚ (state₀ , inj₁ b)
    step-echo = >>=ₚ-identityˡ _ _

  no-backwards-certificate : (c : ℕ) → ¬ Certified c (runᶜ 0 (backwards s))
  no-backwards-certificate c q = 1≰0 (subst₂ ℚ._≤_
    (returnₚ-cum {A = S × (Scheme.Bits sch ⊎ ⊥)} 0 (state₀ , inj₁ b) (λ _ → 1ℚ)) (empty-mass m) le)
    where
    open QBᵢ q

    impossible : Ans Φ (Scheme.Bits sch) ⊥ (Φ state₀) → ⊥
    impossible (inj₁ ((q′ , lt) , _)) = <-irrefl refl (subst (λ q′ → Φ q′ < Φ state₀) (state-unique q′) lt)
    impossible (inj₂ (_ , ()))

    empty-mass : (j : ℕ) → cum j (mapₚ forget (onLᵍ state₀ b)) (λ _ → 1ℚ) ≡ 0ℚ
    empty-mass zero = refl
    empty-mass (suc j) = trans (mapₚ-cum j forget (onLᵍ state₀ b) (λ _ → 1ℚ))
      (trans (cum-cong-P j (onLᵍ state₀ b) (λ _ → 1ℚ) (λ _ → 0ℚ) (λ a → ⊥-elim (impossible a)))
             (cum-zero j (onLᵍ state₀ b)))

    comparison : mapₚ forget (onLᵍ state₀ b) ≈ₚ returnₚ (state₀ , inj₁ b)
    comparison = cohL state₀ b ⟨≈⟩ step-echo

    m = proj₁ (proj₂ comparison (λ _ → 1ℚ) (λ _ → 0≤1ℚ) 1)
    le = proj₂ (proj₂ comparison (λ _ → 1ℚ) (λ _ → 0≤1ℚ) 1)
