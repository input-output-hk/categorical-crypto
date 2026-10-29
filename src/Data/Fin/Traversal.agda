{-# OPTIONS --safe --without-K #-}

module Data.Fin.Traversal where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Maybe.Base using (Maybe; just; _>>=_)
open import Data.Nat.Base as ℕ using (ℕ)

∀F? : ∀ {ℓ} {n : ℕ} {P : Fin n → Set ℓ} → (∀ i → Maybe (P i)) → Maybe (∀ i → P i)
∀F? {n = ℕ.zero}  d = just λ ()
∀F? {n = ℕ.suc n} d =
  d zero                >>= λ p₀ →
  ∀F? (λ i → d (suc i)) >>= λ ps →
  just λ { zero → p₀ ; (suc i) → ps i }
