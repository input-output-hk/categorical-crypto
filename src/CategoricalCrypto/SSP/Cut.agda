{-# OPTIONS --safe --without-K --guardedness #-}

-- A `Dₚ` computation cut at depth `n` into a closed call tree: its first `n`
-- coins become `coin`s, the rest is `dead`, so the tree evaluates to the
-- computation's depth-`n` mass (`ev-cutᵏ`).  `ev` is a closed tree's
-- expectation against a test; it is read off a coin, a map and a served call
-- (`ev-serve`: grafting a closed game is the game's tree, then the caller's).

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-identityʳ; ≤-reflexive) renaming (≤-trans to ≤ℚ-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol

module CategoricalCrypto.SSP.Cut where

private variable X Y : Set

------------------------------------------------------------------------
-- Closed trees against a test

ev : Calls unitᴵ X → (X → ℚ) → ℚ
ev t F = E⊥ (evalC t) F

ev-ret : (x : X) (F : X → ℚ) → ev (ret x) F ≡ F x
ev-ret = E⊥-return

ev-dead : (F : X → ℚ) → ev dead F ≡ 0ℚ
ev-dead F = lookupᴰℚ-return nothing (maybeℚ F)

ev-coin : (μ : Dist-ℚ Bool) (k : Bool → Calls unitᴵ X) (F : X → ℚ) → ev (coin μ k) F ≡ E μ (λ b → ev (k b) F)
ev-coin μ k F = E-bind μ (λ b → evalC (k b)) (maybeℚ F)

ev-map : (f : X → Y) (t : Calls unitᴵ X) (F : Y → ℚ) → ev (mapᶜ f t) F ≡ ev t (λ x → F (f x))
ev-map f (ret x)       F = trans (ev-ret (f x) F) (sym (ev-ret x (λ x → F (f x))))
ev-map f (call () _ _) F
ev-map f (coin μ k)    F =
  trans (ev-coin μ (λ b → mapᶜ f (k b)) F)
        (trans (lookupᴰℚ-cong-P (entries μ) λ b → ev-map f (k b) F) (sym (ev-coin μ k (λ x → F (f x)))))
ev-map f dead          F = trans (ev-dead F) (sym (ev-dead (λ x → F (f x))))

module _ {B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol unitᴵ B) where

  ev-serve : {b : Ch B} (k : R B b → Calls B (St P₂ × Y)) (u : Calls unitᴵ (St P₁ × R B b))
             (F : (St P₂ × St P₁) × Y → ℚ)
           → ev (serve P₂ P₁ k u) F ≡ ev u (λ p → ev (graft P₂ P₁ (k (proj₂ p)) (proj₁ p)) F)
  ev-serve k (ret (s₁ , r)) F = sym (ev-ret (s₁ , r) λ p → ev (graft P₂ P₁ (k (proj₂ p)) (proj₁ p)) F)
  ev-serve k (call () _ _)  F
  ev-serve k (coin μ k₁)    F =
    trans (ev-coin μ (λ b → serve P₂ P₁ k (k₁ b)) F)
          (trans (lookupᴰℚ-cong-P (entries μ) λ b → ev-serve k (k₁ b) F)
                 (sym (ev-coin μ k₁ λ p → ev (graft P₂ P₁ (k (proj₂ p)) (proj₁ p)) F)))
  ev-serve k dead           F = trans (ev-dead F) (sym (ev-dead λ p → ev (graft P₂ P₁ (k (proj₂ p)) (proj₁ p)) F))

------------------------------------------------------------------------
-- Cutting

-- A node of a `Dₚ` computation as a coin.
nodeᴰ : Dₚ X → Dist-ℚ Bool
nodeᴰ d = mk-Dist ((wt d true , true) NE.∷ (wt d false , false) ∷ [])
                  (trans (cong (wt d true ℚ.+_) (+-identityʳ (wt d false))) (wt-1 d))
                  (wt-nn d true All.∷ wt-nn d false All.∷ All.[])

-- Cut at depth `n`, the value reached handed to a continuation.
mutual
  cutᵏ : ℕ → Dₚ X → (X → Calls unitᴵ Y) → Calls unitᴵ Y
  cutᵏ zero    d k = dead
  cutᵏ (suc n) d k = coin (nodeᴰ d) λ b → cutLᵏ n (br d b) k

  cutLᵏ : ℕ → X ⊎ Dₚ X → (X → Calls unitᴵ Y) → Calls unitᴵ Y
  cutLᵏ n (inj₁ x)  k = k x
  cutLᵏ n (inj₂ d′) k = cutᵏ n d′ k

mutual
  ev-cutᵏ : (n : ℕ) (d : Dₚ X) (k : X → Calls unitᴵ Y) (F : Y → ℚ)
          → ev (cutᵏ n d k) F ≡ cum n d (λ x → ev (k x) F)
  ev-cutᵏ zero    d k F = ev-dead F
  ev-cutᵏ (suc n) d k F =
    trans (ev-coin (nodeᴰ d) (λ b → cutLᵏ n (br d b) k) F)
          (cong₂ (λ x y → wt d true ℚ.* x ℚ.+ y) (ev-cutLᵏ n (br d true) k F)
                 (trans (+-identityʳ _) (cong (wt d false ℚ.*_) (ev-cutLᵏ n (br d false) k F))))

  ev-cutLᵏ : (n : ℕ) (x : X ⊎ Dₚ X) (k : X → Calls unitᴵ Y) (F : Y → ℚ)
           → ev (cutLᵏ n x k) F ≡ leafₚ n x (λ x → ev (k x) F)
  ev-cutLᵏ n (inj₁ x)  k F = refl
  ev-cutLᵏ n (inj₂ d′) k F = ev-cutᵏ n d′ k F

-- A coin's depth-`n` mass is at most its expectation.
coin-≤E : (μ : Dist-ℚ Bool) (n : ℕ) (F : Bool → ℚ) → NNF F → cum n (coinₚ μ) F ℚ.≤ E μ F
coin-≤E μ n F nn = ≤ℚ-trans (cum-mono (≤-trans (n≤1+n n) (n≤1+n (suc n))) (coinₚ μ) F nn) (≤-reflexive (coinₚ-cum μ n F))
