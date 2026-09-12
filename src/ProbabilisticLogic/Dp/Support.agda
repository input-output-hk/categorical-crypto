{-# OPTIONS --safe --without-K --guardedness #-}

-- Two facts about `Dp.Supp` that `Dp`'s own `uniformize` does not give.
--
-- `Supp-map` weakens a depth-`n` support pointwise and `Supp-all` puts a fact
-- that holds everywhere on one.  `uniformizeˢ` is
-- `uniformize` with the witness ASSUMED only on the support rather than
-- everywhere, which is what a consumer whose per-value budget exists only at
-- reachable values needs — `Dp.Settle.Iter`'s loop, where an unreachable loop
-- re-entry has no bound at all.

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product.Base using (Σ-syntax; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (Level)

open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Support where

private variable
  a b : Level
  A : Set a

mutual
  Supp-map : (Φ Ψ : A → Set b) → (∀ p → Φ p → Ψ p)
           → (n : ℕ) (d : Dₚ A) → Supp n d Φ → Supp n d Ψ
  Supp-map Φ Ψ f zero    d sp        = tt
  Supp-map Φ Ψ f (suc n) d (s₁ , s₂) =
    SuppL-map Φ Ψ f n (br d true) s₁ , SuppL-map Φ Ψ f n (br d false) s₂

  SuppL-map : (Φ Ψ : A → Set b) → (∀ p → Φ p → Ψ p)
            → (n : ℕ) (x : A ⊎ Dₚ A) → SuppL n x Φ → SuppL n x Ψ
  SuppL-map Φ Ψ f n (inj₁ p)  s = f p s
  SuppL-map Φ Ψ f n (inj₂ d′) s = Supp-map Φ Ψ f n d′ s

mutual
  Supp-all : (Φ : A → Set b) → (∀ p → Φ p) → (n : ℕ) (d : Dₚ A) → Supp n d Φ
  Supp-all Φ w zero    d = tt
  Supp-all Φ w (suc n) d = SuppL-all Φ w n (br d true) , SuppL-all Φ w n (br d false)

  SuppL-all : (Φ : A → Set b) → (∀ p → Φ p) → (n : ℕ) (x : A ⊎ Dₚ A) → SuppL n x Φ
  SuppL-all Φ w n (inj₁ p)  = w p
  SuppL-all Φ w n (inj₂ d′) = Supp-all Φ w n d′

mutual
  uniformizeˢ : (Φ : A → ℕ → Set b) → (∀ p {i i′} → i ≤ i′ → Φ p i → Φ p i′)
              → (n : ℕ) (d : Dₚ A) → Supp n d (λ p → Σ[ i ∈ ℕ ] Φ p i)
              → Σ[ i ∈ ℕ ] Supp n d (λ p → Φ p i)
  uniformizeˢ Φ up zero    d sp        = 0 , tt
  uniformizeˢ Φ up (suc n) d (s₁ , s₂) =
    let i₁ , t₁ = uniformizeLˢ Φ up n (br d true)  s₁
        i₂ , t₂ = uniformizeLˢ Φ up n (br d false) s₂
    in i₁ ⊔ i₂
     , SuppL-mono Φ (λ p → up p) (m≤m⊔n i₁ i₂) n (br d true) t₁
     , SuppL-mono Φ (λ p → up p) (m≤n⊔m i₁ i₂) n (br d false) t₂

  uniformizeLˢ : (Φ : A → ℕ → Set b) → (∀ p {i i′} → i ≤ i′ → Φ p i → Φ p i′)
               → (n : ℕ) (x : A ⊎ Dₚ A) → SuppL n x (λ p → Σ[ i ∈ ℕ ] Φ p i)
               → Σ[ i ∈ ℕ ] SuppL n x (λ p → Φ p i)
  uniformizeLˢ Φ up n (inj₁ p)  s = s
  uniformizeLˢ Φ up n (inj₂ d′) s = uniformizeˢ Φ up n d′ s
