{-# OPTIONS --safe --without-K #-}

-- Polynomially-bounded functions

module Data.Nat.Poly where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Ext
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open ≤-Reasoning

private variable p q : ℕ → ℕ

-- The base is suc n, not n, so that the degree can be relaxed: ^-monoʳ-≤ needs a
-- NonZero base, and indeed n ^ 0 ≰ n ^ e fails at n = 0.
Poly : (ℕ → ℕ) → Set
Poly p = Σ[ c ∈ ℕ ] Σ[ d ∈ ℕ ] ∀ n → p n ≤ c * suc n ^ d

poly-relax : ∀ {C D} c d → c ≤ C → d ≤ D →
             (∀ n → p n ≤ c * suc n ^ d) → ∀ n → p n ≤ C * suc n ^ D
poly-relax c d c≤C d≤D bnd n = ≤-trans (bnd n) (*-mono-≤ c≤C (^-monoʳ-≤ (suc n) d≤D))

poly-≤ : (∀ n → p n ≤ q n) → Poly q → Poly p
poly-≤ p≤q (c , d , bnd) = c , d , λ n → ≤-trans (p≤q n) (bnd n)

poly-const : ∀ k → Poly (λ _ → k)
poly-const k = k , 0 , λ _ → ≤-reflexive (sym (*-identityʳ k))

poly-id : Poly (λ n → n)
poly-id = 1 , 1 , λ n → ≤-trans (n≤1+n n)
  (≤-reflexive (sym (trans (*-identityˡ (suc n ^ 1)) (^-identityʳ (suc n)))))

poly-+ : Poly p → Poly q → Poly (λ n → p n + q n)
poly-+ {p} {q} (c , d , bp) (c′ , e , bq) = c + c′ , d ⊔ e , λ n → begin
  p n + q n                                   ≤⟨ +-mono-≤ (poly-relax c d ≤-refl (m≤m⊔n d e) bp n)
                                                          (poly-relax c′ e ≤-refl (m≤n⇒m≤o⊔n d ≤-refl) bq n) ⟩
  c * suc n ^ (d ⊔ e) + c′ * suc n ^ (d ⊔ e)  ≡⟨ sym (*-distribʳ-+ (suc n ^ (d ⊔ e)) c c′) ⟩
  (c + c′) * suc n ^ (d ⊔ e)                  ∎

poly-⊔ : Poly p → Poly q → Poly (λ n → p n ⊔ q n)
poly-⊔ (c , d , bp) (c′ , e , bq) = c ⊔ c′ , d ⊔ e , λ n →
  ⊔-lub (poly-relax c d (m≤m⊔n c c′) (m≤m⊔n d e) bp n)
        (poly-relax c′ e (m≤n⇒m≤o⊔n c ≤-refl) (m≤n⇒m≤o⊔n d ≤-refl) bq n)

poly-* : Poly p → Poly q → Poly (λ n → p n * q n)
poly-* {p} {q} (c , d , bp) (c′ , e , bq) = c * c′ , d + e , λ n → begin
  p n * q n                         ≤⟨ *-mono-≤ (bp n) (bq n) ⟩
  c * suc n ^ d * (c′ * suc n ^ e)  ≡⟨ [m*n]*[o*p]≡[m*o]*[n*p] c (suc n ^ d) c′ (suc n ^ e) ⟩
  c * c′ * (suc n ^ d * suc n ^ e)  ≡⟨ sym (cong (c * c′ *_) (^-distribˡ-+-* (suc n) d e)) ⟩
  c * c′ * suc n ^ (d + e)          ∎

poly-≤2^ : Poly p → Σ[ N ∈ ℕ ] ∀ n → N ≤ n → p n ≤ 2 ^ n
poly-≤2^ {p} (c , d , bnd) = let (N , dom) = deg≤2^ c d in
  N , λ n N≤n → ≤-trans (bnd n) (dom n N≤n)

------------------------------------------------------------------------
-- The base-n formulation
------------------------------------------------------------------------

-- The shape most bounds are quoted in: base n, with an additive slack constant
-- standing in for the degree-relaxability that Poly gets from its suc n base.
Poly′ : (ℕ → ℕ) → Set
Poly′ p = Σ[ c ∈ ℕ ] Σ[ d ∈ ℕ ] ∀ n → p n ≤ c * n ^ d + c

private
  2+m≤2*[1+m] : ∀ m → 2 + m ≤ 2 * (1 + m)
  2+m≤2*[1+m] m = +-mono-≤ (s≤s z≤n) (m≤m+n (suc m) 0)

  [2*n]^d≡2^d*n^d : ∀ d n → (2 * n) ^ d ≡ 2 ^ d * n ^ d
  [2*n]^d≡2^d*n^d zero    n = refl
  [2*n]^d≡2^d*n^d (suc d) n = trans (cong (2 * n *_) ([2*n]^d≡2^d*n^d d n))
                                    ([m*n]*[o*p]≡[m*o]*[n*p] 2 n (2 ^ d) (n ^ d))

Poly′⇒Poly : Poly′ p → Poly p
Poly′⇒Poly {p} (c , d , bnd) = c + c , d , λ n → begin
  p n                            ≤⟨ bnd n ⟩
  c * n ^ d + c                  ≤⟨ +-mono-≤ (*-monoʳ-≤ c (^-monoˡ-≤ d (n≤1+n n)))
                                             (m≤m*n c (suc n ^ d) {{m^n≢0 (suc n) d}}) ⟩
  c * suc n ^ d + c * suc n ^ d  ≡⟨ sym (*-distribʳ-+ (suc n ^ d) c c) ⟩
  (c + c) * suc n ^ d            ∎

Poly⇒Poly′ : Poly p → Poly′ p
Poly⇒Poly′ {p} (c , d , bnd) = C , d , bound
  where
  C = c * 2 ^ d

  bound : ∀ n → p n ≤ C * n ^ d + C
  bound zero = begin
    p 0            ≤⟨ bnd 0 ⟩
    c * 1 ^ d      ≡⟨ cong (c *_) (^-zeroˡ d) ⟩
    c * 1          ≡⟨ *-identityʳ c ⟩
    c              ≤⟨ m≤m*n c (2 ^ d) {{m^n≢0 2 d}} ⟩
    C              ≤⟨ m≤n+m C (C * 0 ^ d) ⟩
    C * 0 ^ d + C  ∎
  bound (suc m) = begin
    p (suc m)                ≤⟨ bnd (suc m) ⟩
    c * suc (suc m) ^ d      ≤⟨ *-monoʳ-≤ c (^-monoˡ-≤ d (2+m≤2*[1+m] m)) ⟩
    c * (2 * suc m) ^ d      ≡⟨ cong (c *_) ([2*n]^d≡2^d*n^d d (suc m)) ⟩
    c * (2 ^ d * suc m ^ d)  ≡⟨ sym (*-assoc c (2 ^ d) (suc m ^ d)) ⟩
    C * suc m ^ d            ≤⟨ m≤m+n (C * suc m ^ d) C ⟩
    C * suc m ^ d + C        ∎

Poly⇔Poly′ : Poly p ⇔ Poly′ p
Poly⇔Poly′ = mk⇔ Poly⇒Poly′ Poly′⇒Poly
