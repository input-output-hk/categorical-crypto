{-# OPTIONS --safe --without-K #-}

-- Polynomially-bounded functions

module Data.Nat.Poly where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Tactic.Solver.Ring

open ≤-Reasoning

private variable p q : ℕ → ℕ

Poly : (ℕ → ℕ) → Set
Poly p = Σ[ c ∈ ℕ ] Σ[ d ∈ ℕ ] ∀ n → p n ≤ c * n ^ d + c

^-monoʳ-≤-+1 : ∀ n {d e} → d ≤ e → n ^ d ≤ n ^ e + 1
^-monoʳ-≤-+1 zero    {zero}  {zero}  _   = s≤s z≤n
^-monoʳ-≤-+1 zero    {zero}  {suc e} _   = ≤-refl
^-monoʳ-≤-+1 zero    {suc d}         _   = z≤n
^-monoʳ-≤-+1 (suc n)                 d≤e = m≤n⇒m≤n+o 1 (^-monoʳ-≤ (suc n) d≤e)

-- Weaken a witness to a larger coefficient/degree; the doubled coefficient
-- absorbs the +1 of ^-monoʳ-≤-+1.
poly-relax : ∀ {C D} c d → c + c ≤ C → d ≤ D →
             (∀ n → p n ≤ c * n ^ d + c) → ∀ n → p n ≤ C * n ^ D + C
poly-relax {p = p} {C} {D} c d c+c≤C d≤D bnd n = begin
  p n                  ≤⟨ bnd n ⟩
  c * n ^ d + c        ≤⟨ +-monoˡ-≤ c (*-monoʳ-≤ c (^-monoʳ-≤-+1 n d≤D)) ⟩
  c * (n ^ D + 1) + c  ≡⟨ solve-≈ +-*-commutativeSemiring ⟩
  c * n ^ D + (c + c)  ≤⟨ +-mono-≤ (*-monoˡ-≤ (n ^ D) (≤-trans (m≤m+n c c) c+c≤C)) c+c≤C ⟩
  C * n ^ D + C        ∎

poly-≤ : (∀ n → p n ≤ q n) → Poly q → Poly p
poly-≤ p≤q (c , d , bnd) = c , d , λ n → ≤-trans (p≤q n) (bnd n)

poly-const : ∀ k → Poly (λ _ → k)
poly-const k = k , 0 , λ n → m≤n+m k (k * 1)

poly-id : Poly (λ n → n)
poly-id = 1 , 1 , λ n → m≤n⇒m≤n+o 1 (≤-reflexive (sym (trans (*-identityˡ (n ^ 1)) (^-identityʳ n))))

poly-+ : Poly p → Poly q → Poly (λ n → p n + q n)
poly-+ {p} {q} (c , d , bp) (c′ , e , bq) = K + K , d ⊔ e , λ n → begin
    p n + q n                                     ≤⟨ +-mono-≤ (rp n) (rq n) ⟩
    (K * n ^ (d ⊔ e) + K) + (K * n ^ (d ⊔ e) + K) ≡⟨ solve-≈ +-*-commutativeSemiring ⟩
    (K + K) * n ^ (d ⊔ e) + (K + K)               ∎
  where
  K : ℕ
  K = (c + c) ⊔ (c′ + c′)
  rp : ∀ n → p n ≤ K * n ^ (d ⊔ e) + K
  rp = poly-relax c d (m≤m⊔n (c + c) (c′ + c′)) (m≤m⊔n d e) bp
  rq : ∀ n → q n ≤ K * n ^ (d ⊔ e) + K
  rq = poly-relax c′ e (m≤n⇒m≤o⊔n (c + c) ≤-refl) (m≤n⇒m≤o⊔n d ≤-refl) bq

poly-⊔ : Poly p → Poly q → Poly (λ n → p n ⊔ q n)
poly-⊔ {p} {q} (c , d , bp) (c′ , e , bq) = K , d ⊔ e , λ n → ⊔-lub (rp n) (rq n)
  where
  K : ℕ
  K = (c + c) ⊔ (c′ + c′)
  rp : ∀ n → p n ≤ K * n ^ (d ⊔ e) + K
  rp = poly-relax c d (m≤m⊔n (c + c) (c′ + c′)) (m≤m⊔n d e) bp
  rq : ∀ n → q n ≤ K * n ^ (d ⊔ e) + K
  rq = poly-relax c′ e (m≤n⇒m≤o⊔n (c + c) ≤-refl) (m≤n⇒m≤o⊔n d ≤-refl) bq

poly-* : Poly p → Poly q → Poly (λ n → p n * q n)
poly-* {p} {q} (c , d , bp) (c′ , e , bq) = 3 * K , d + e , bound
  where
  K = c * c′

  step : ∀ n {a} → a ≤ d + e → K * n ^ a ≤ K * n ^ (d + e) + K
  step n a≤d+e = ≤-trans (*-monoʳ-≤ K (^-monoʳ-≤-+1 n a≤d+e))
    (≤-reflexive (solve-≈ +-*-commutativeSemiring))

  bound : ∀ n → p n * q n ≤ 3 * K * n ^ (d + e) + 3 * K
  bound n = begin
    p n * q n                            ≤⟨ *-mono-≤ (bp n) (bq n) ⟩
    (c * n ^ d + c) * (c′ * n ^ e + c′)  ≡⟨ solve-≈ +-*-commutativeSemiring ⟩
    K * (n ^ d * n ^ e) + (K * n ^ d + (K * n ^ e + K))
      ≡⟨ cong (λ z → K * z + (K * n ^ d + (K * n ^ e + K))) (sym (^-distribˡ-+-* n d e)) ⟩
    K * n ^ (d + e) + (K * n ^ d + (K * n ^ e + K))
      ≤⟨ +-monoʳ-≤ (K * n ^ (d + e))
                   (+-mono-≤ (step n (m≤m+n d e)) (+-monoˡ-≤ K (step n (m≤n⇒m≤o+n d ≤-refl)))) ⟩
    K * n ^ (d + e) + ((K * n ^ (d + e) + K) + ((K * n ^ (d + e) + K) + K))
      ≡⟨ solve-≈ +-*-commutativeSemiring ⟩
    3 * K * n ^ (d + e) + 3 * K          ∎
