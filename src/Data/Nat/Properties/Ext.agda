{-# OPTIONS --safe --without-K #-}

-- The ℕ facts `Data.Nat.Properties` does not export: `_^_` over a product base,
-- and the growth comparisons that make `2 ^ n` outrun every polynomial.

module Data.Nat.Properties.Ext where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

open ≤-Reasoning

------------------------------------------------------------------------
-- `_^_` over a product base
------------------------------------------------------------------------

^-distribʳ-* : ∀ d m n → (m * n) ^ d ≡ m ^ d * n ^ d
^-distribʳ-* zero    m n = refl
^-distribʳ-* (suc d) m n = trans (cong (m * n *_) (^-distribʳ-* d m n))
                                 ([m*n]*[o*p]≡[m*o]*[n*p] m n (m ^ d) (n ^ d))

------------------------------------------------------------------------
-- 2 ^ n outgrows every polynomial
------------------------------------------------------------------------

m≤2^m : ∀ m → m ≤ 2 ^ m
m≤2^m zero    = z≤n
m≤2^m (suc m) = begin
  suc m          ≤⟨ +-mono-≤ (m^n>0 2 m) (m≤2^m m) ⟩
  2 ^ m + 2 ^ m  ≡⟨ sym (cong (2 ^ m +_) (*-identityˡ (2 ^ m))) ⟩
  2 ^ suc m      ∎

private
  2*≡+ : ∀ m → 2 * m ≡ m + m
  2*≡+ m = cong (m +_) (*-identityˡ m)

  -- the `t ∸ 1` slack of the ratio bound below, at the level of one factor
  [1+m]*[t∸1]≤m*t : ∀ m t → t ≤ m → suc m * (t ∸ 1) ≤ m * t
  [1+m]*[t∸1]≤m*t m zero    _     = ≤-reflexive (trans (*-zeroʳ (suc m)) (sym (*-zeroʳ m)))
  [1+m]*[t∸1]≤m*t m (suc s) 1+s≤m = begin
    s + m * s  ≤⟨ +-monoˡ-≤ (m * s) (<⇒≤ 1+s≤m) ⟩
    m + m * s  ≡⟨ sym (*-suc m s) ⟩
    m * suc s  ∎

  m∸[1+d] : ∀ m d → m ∸ suc d ≡ (m ∸ d) ∸ 1
  m∸[1+d] m d = sym (trans (∸-+-assoc m d 1) (cong (m ∸_) (+-comm d 1)))

  m≤2*[m∸d] : ∀ d m → 2 * d ≤ m → m ≤ 2 * (m ∸ d)
  m≤2*[m∸d] d m 2d≤m = begin
    m                  ≡⟨ sym (m+[n∸m]≡n d≤m) ⟩
    d + (m ∸ d)        ≤⟨ +-monoˡ-≤ (m ∸ d) d≤m∸d ⟩
    (m ∸ d) + (m ∸ d)  ≡⟨ sym (2*≡+ (m ∸ d)) ⟩
    2 * (m ∸ d)        ∎
    where
    d+d≤m = ≤-trans (≤-reflexive (sym (2*≡+ d))) 2d≤m
    d≤m   = ≤-trans (m≤m+n d d) d+d≤m
    d≤m∸d = ≤-trans (≤-reflexive (sym (m+n∸n≡m d d))) (∸-monoˡ-≤ d d+d≤m)

-- The ratio (1 + 1/m)^d ≤ m/(m ∸ d), with no binomial expansion: the `m ∸ d`
-- slack is exactly what makes the induction on the degree go through.
[1+m]^d*[m∸d]≤m^[1+d] : ∀ d m → suc m ^ d * (m ∸ d) ≤ m ^ suc d
[1+m]^d*[m∸d]≤m^[1+d] zero    m = ≤-reflexive (trans (*-identityˡ m) (sym (*-identityʳ m)))
[1+m]^d*[m∸d]≤m^[1+d] (suc d) m = begin
  suc m * suc m ^ d * (m ∸ suc d)      ≡⟨ cong (suc m * suc m ^ d *_) (m∸[1+d] m d) ⟩
  suc m * suc m ^ d * (m ∸ d ∸ 1)      ≡⟨ cong (_* (m ∸ d ∸ 1)) (*-comm (suc m) (suc m ^ d)) ⟩
  suc m ^ d * suc m * (m ∸ d ∸ 1)      ≡⟨ *-assoc (suc m ^ d) (suc m) (m ∸ d ∸ 1) ⟩
  suc m ^ d * (suc m * (m ∸ d ∸ 1))    ≤⟨ *-monoʳ-≤ (suc m ^ d) ([1+m]*[t∸1]≤m*t m (m ∸ d) (m∸n≤m m d)) ⟩
  suc m ^ d * (m * (m ∸ d))            ≡⟨ cong (suc m ^ d *_) (*-comm m (m ∸ d)) ⟩
  suc m ^ d * ((m ∸ d) * m)            ≡⟨ sym (*-assoc (suc m ^ d) (m ∸ d) m) ⟩
  suc m ^ d * (m ∸ d) * m              ≤⟨ *-monoˡ-≤ m ([1+m]^d*[m∸d]≤m^[1+d] d m) ⟩
  m ^ suc d * m                        ≡⟨ *-comm (m ^ suc d) m ⟩
  m * m ^ suc d                        ∎

[1+m]^d≤2*m^d : ∀ d m → 2 * d ≤ m → suc m ^ d ≤ 2 * m ^ d
[1+m]^d≤2*m^d zero    zero      _    = s≤s z≤n
[1+m]^d≤2*m^d (suc d) zero      ()
[1+m]^d≤2*m^d d       m@(suc _) 2d≤m = *-cancelʳ-≤ (suc m ^ d) (2 * m ^ d) m (begin
  suc m ^ d * m                ≤⟨ *-monoʳ-≤ (suc m ^ d) (m≤2*[m∸d] d m 2d≤m) ⟩
  suc m ^ d * (2 * (m ∸ d))    ≡⟨ sym (*-assoc (suc m ^ d) 2 (m ∸ d)) ⟩
  suc m ^ d * 2 * (m ∸ d)      ≡⟨ cong (_* (m ∸ d)) (*-comm (suc m ^ d) 2) ⟩
  2 * suc m ^ d * (m ∸ d)      ≡⟨ *-assoc 2 (suc m ^ d) (m ∸ d) ⟩
  2 * (suc m ^ d * (m ∸ d))    ≤⟨ *-monoʳ-≤ 2 ([1+m]^d*[m∸d]≤m^[1+d] d m) ⟩
  2 * (m * m ^ d)              ≡⟨ cong (2 *_) (*-comm m (m ^ d)) ⟩
  2 * (m ^ d * m)              ≡⟨ sym (*-assoc 2 (m ^ d) m) ⟩
  2 * m ^ d * m                ∎)

-- Every linear function is dominated by 2 ^ i at some i ≥ 2, by splitting the
-- exponent as 2 ^ (m + m) ≥ m * m.
lin≤2^ : ∀ a b → Σ[ i ∈ ℕ ] 2 ≤ i × a + b * i ≤ 2 ^ i
lin≤2^ a b = 2 * m , *-monoʳ-≤ 2 (s≤s z≤n) , bnd
  where
  m = suc (a + 2 * b)

  bnd : a + b * (2 * m) ≤ 2 ^ (2 * m)
  bnd = begin
    a + b * (2 * m)    ≡⟨ cong (a +_) (sym (*-assoc b 2 m)) ⟩
    a + b * 2 * m      ≤⟨ +-monoˡ-≤ (b * 2 * m) (≤-trans (m≤m+n a (2 * b)) (n≤1+n _)) ⟩
    m + b * 2 * m      ≤⟨ *-monoˡ-≤ m (s≤s (≤-trans (≤-reflexive (*-comm b 2)) (m≤n+m (2 * b) a))) ⟩
    m * m              ≤⟨ *-mono-≤ (m≤2^m m) (m≤2^m m) ⟩
    2 ^ m * 2 ^ m      ≡⟨ sym (^-distribˡ-+-* 2 m m) ⟩
    2 ^ (m + m)        ≡⟨ cong (2 ^_) (sym (2*≡+ m)) ⟩
    2 ^ (2 * m)        ∎

private
  -- one propagation step of the domination, on the strength of the ratio bound
  step≤2^ : ∀ c d j → 2 * d ≤ suc j → c * suc j ^ d ≤ 2 ^ j
          → c * suc (suc j) ^ d ≤ 2 ^ suc j
  step≤2^ c d j 2d≤ bnd = begin
    c * suc (suc j) ^ d    ≤⟨ *-monoʳ-≤ c ([1+m]^d≤2*m^d d (suc j) 2d≤) ⟩
    c * (2 * suc j ^ d)    ≡⟨ sym (*-assoc c 2 (suc j ^ d)) ⟩
    c * 2 * suc j ^ d      ≡⟨ cong (_* suc j ^ d) (*-comm c 2) ⟩
    2 * c * suc j ^ d      ≡⟨ *-assoc 2 c (suc j ^ d) ⟩
    2 * (c * suc j ^ d)    ≤⟨ *-monoʳ-≤ 2 bnd ⟩
    2 ^ suc j              ∎

  base≤2^ : ∀ c d → Σ[ j ∈ ℕ ] 2 * d ≤ suc j × c * suc j ^ d ≤ 2 ^ j
  base≤2^ c zero    = c , z≤n , ≤-trans (≤-reflexive (*-identityʳ c)) (m≤2^m c)
  base≤2^ c (suc d) = i * suc d , ≤-trans (*-monoˡ-≤ (suc d) 2≤i) (n≤1+n (i * suc d)) , bnd
    where
    C = suc c
    lin = lin≤2^ C (C * suc d)
    i = proj₁ lin
    2≤i = proj₁ (proj₂ lin)

    key : C * suc (i * suc d) ≤ 2 ^ i
    key = begin
      C * suc (i * suc d)      ≡⟨ *-suc C (i * suc d) ⟩
      C + C * (i * suc d)      ≡⟨ cong (C +_) (cong (C *_) (*-comm i (suc d))) ⟩
      C + C * (suc d * i)      ≡⟨ cong (C +_) (sym (*-assoc C (suc d) i)) ⟩
      C + C * suc d * i        ≤⟨ proj₂ (proj₂ lin) ⟩
      2 ^ i                    ∎

    bnd : c * suc (i * suc d) ^ suc d ≤ 2 ^ (i * suc d)
    bnd = begin
      c * suc (i * suc d) ^ suc d          ≤⟨ *-monoˡ-≤ _ (n≤1+n c) ⟩
      C * suc (i * suc d) ^ suc d          ≤⟨ *-monoˡ-≤ _ (m≤m*n C (C ^ d) ⦃ m^n≢0 C d ⦄) ⟩
      C ^ suc d * suc (i * suc d) ^ suc d  ≡⟨ sym (^-distribʳ-* (suc d) C (suc (i * suc d))) ⟩
      (C * suc (i * suc d)) ^ suc d        ≤⟨ ^-monoˡ-≤ (suc d) key ⟩
      (2 ^ i) ^ suc d                      ≡⟨ ^-*-assoc 2 i (suc d) ⟩
      2 ^ (i * suc d)                      ∎

-- 2 ^ n dominates `c · (1 + n)^d` from some point on.
deg≤2^ : ∀ c d → Σ[ N ∈ ℕ ] ∀ n → N ≤ n → c * suc n ^ d ≤ 2 ^ n
deg≤2^ c d = j₀ , λ n j₀≤n → go n (≤⇒≤′ j₀≤n)
  where
  j₀ = proj₁ (base≤2^ c d)
  2d≤ = proj₁ (proj₂ (base≤2^ c d))

  go : ∀ n → j₀ ≤′ n → c * suc n ^ d ≤ 2 ^ n
  go _       ≤′-refl      = proj₂ (proj₂ (base≤2^ c d))
  go (suc n) (≤′-step le) = step≤2^ c d n (≤-trans 2d≤ (s≤s (≤′⇒≤ le))) (go n le)
