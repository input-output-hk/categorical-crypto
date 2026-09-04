{-# OPTIONS --safe --without-K #-}

-- Vanishing bounds: polynomially many `1/2^j`-sized parts tend to 0.  `_→0` is
-- spelled exactly as `CategoricalCrypto.UC.Family._→0` (and as the inherited
-- `CategoricalCrypto.VanishingTV._→0`, which agrees), so that these lemmas
-- inhabit `UC.Family.VanishingBound` on the nose.

module ProbabilisticLogic.Distribution.Uniform.Decay where

open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Nat.Poly using (Poly; poly-*; poly-const; poly-≤2^)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (Σ-syntax; _,_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; ½; 1/_; _+_; _*_; _≤_; _<_; _>_; nonNegative; positive; >-nonZero)
open import Data.Rational.Properties using
  ( *-assoc; *-cancelˡ-≤-pos; *-identityˡ; *-inverseʳ; *-monoʳ-≤-nonNeg
  ; *-monoˡ-≤-nonNeg; +-mono-≤; 1/pos⇒pos; pos*pos⇒pos; positive⁻¹; <⇒≤; ≤-trans
  ; module ≤-Reasoning )
open import Data.Rational.Properties.Ext using (0<½*; ½*+½*)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; subst)

open import ProbabilisticLogic.Distribution.Uniform using
  ( fromℕ; inv-pow-2; archimedean; fromℕ-*; fromℕ-inv-pow-2; fromℕ-mono-≤
  ; 0<fromℕ-suc; 0≤inv-pow-2 )

private variable
  s t : ℕ → ℚ
  n k p : ℕ → ℕ

infix 4 _→0

_→0 : (ℕ → ℚ) → Set
s →0 = ∀ ε → ε > 0ℚ → Σ[ N ∈ ℕ ] ∀ n → N ℕ.≤ n → s n ≤ ε

------------------------------------------------------------------------
-- Closure rules
------------------------------------------------------------------------

-- `_→0` is one-sided (no absolute value), so domination is all that is asked.
→0-≤ : (∀ n → s n ≤ t n) → t →0 → s →0
→0-≤ s≤t h ε ε>0 = let (N , bnd) = h ε ε>0 in N , λ n N≤n → ≤-trans (s≤t n) (bnd n N≤n)

-- Scaling by a positive constant: `ε` is asked of `s` shrunk by `1/c`.
→0-*ˡ : ∀ c → 0ℚ < c → s →0 → (λ n → c * s n) →0
→0-*ˡ {s} c 0<c h ε ε>0 = let (N , bnd) = h (r * ε) 0<rε in N , λ n N≤n → begin
  c * s n      ≤⟨ *-monoˡ-≤-nonNeg c ⦃ nonNegative (<⇒≤ 0<c) ⦄ (bnd n N≤n) ⟩
  c * (r * ε)  ≡⟨ sym (*-assoc c r ε) ⟩
  c * r * ε    ≡⟨ cong (_* ε) (*-inverseʳ c ⦃ c≢0 ⦄) ⟩
  1ℚ * ε       ≡⟨ *-identityˡ ε ⟩
  ε            ∎
  where
  c≢0 = >-nonZero 0<c
  r = (1/ c) ⦃ c≢0 ⦄

  0<rε : 0ℚ < r * ε
  0<rε = positive⁻¹ (r * ε)
    ⦃ pos*pos⇒pos r ⦃ 1/pos⇒pos c ⦃ positive 0<c ⦄ ⦄ ε ⦃ positive ε>0 ⦄ ⦄

  open ≤-Reasoning

→0-+ : s →0 → t →0 → (λ n → s n + t n) →0
→0-+ {s} {t} hs ht ε ε>0 =
  let (N₁ , b₁) = hs (½ * ε) (0<½* ε>0)
      (N₂ , b₂) = ht (½ * ε) (0<½* ε>0)
  in N₁ ℕ.⊔ N₂ , λ n le → subst (s n + t n ≤_) (½*+½* ε)
       (+-mono-≤ (b₁ n (ℕₚ.≤-trans (ℕₚ.m≤m⊔n N₁ N₂) le))
                 (b₂ n (ℕₚ.≤-trans (ℕₚ.m≤n⊔m N₁ N₂) le)))

------------------------------------------------------------------------
-- Polynomially many `1/2^j`-sized parts
------------------------------------------------------------------------

private
  -- `a · 2^-j ≤ ε` as soon as `M · a ≤ 2^j` for an M with `1 ≤ M · ε`.
  step : ∀ {ε} M a j → 1ℚ ≤ fromℕ (suc M) * ε → suc M ℕ.* a ℕ.≤ 2 ℕ.^ j
       → fromℕ a * inv-pow-2 j ≤ ε
  step {ε} M a j 1≤Mε dom =
    *-cancelˡ-≤-pos (fromℕ (suc M)) ⦃ positive (0<fromℕ-suc M) ⦄ (begin
      fromℕ (suc M) * (fromℕ a * inv-pow-2 j)  ≡⟨ sym (*-assoc (fromℕ (suc M)) (fromℕ a) (inv-pow-2 j)) ⟩
      fromℕ (suc M) * fromℕ a * inv-pow-2 j
        ≡⟨ cong (_* inv-pow-2 j) (sym (fromℕ-* (suc M) a)) ⟩
      fromℕ (suc M ℕ.* a) * inv-pow-2 j
        ≤⟨ *-monoʳ-≤-nonNeg (inv-pow-2 j) ⦃ nonNegative (0≤inv-pow-2 j) ⦄ (fromℕ-mono-≤ dom) ⟩
      fromℕ (2 ℕ.^ j) * inv-pow-2 j            ≡⟨ fromℕ-inv-pow-2 j ⟩
      1ℚ                                       ≤⟨ 1≤Mε ⟩
      fromℕ (suc M) * ε                        ∎)
    where open ≤-Reasoning

-- 2^-j beats every polynomial numerator, along any schedule that keeps up
-- with the level (`j ≤ n j`).
poly-inv-pow-2-→0 : Poly p → (∀ j → j ℕ.≤ n j)
                  → (λ j → fromℕ (p j) * inv-pow-2 (n j)) →0
poly-inv-pow-2-→0 {p} {n} Pp j≤n ε ε>0 =
  let (M , 1≤Mε) = archimedean ε>0
      (N , dom)  = poly-≤2^ (poly-* (poly-const (suc M)) Pp)
  in N , λ j N≤j →
    step M (p j) (n j) 1≤Mε (ℕₚ.≤-trans (dom j N≤j) (ℕₚ.^-monoʳ-≤ 2 (j≤n j)))

-- `VanishingBound (λ j q → t j (q · k j) · 2^-(n j))` unfolded: a birthday-shaped
-- numerator against a schedule whose hash width keeps up with the level and a
-- polynomial block count.  A concrete numerator supplies only its quadratic
-- bound `t j m ≤ fromℕ (m · m)`.
vanishing-bound : ∀ (t : ℕ → ℕ → ℚ) (n k : ℕ → ℕ)
                → (∀ j m → t j m ≤ fromℕ (m ℕ.* m)) → (∀ j → j ℕ.≤ n j) → Poly k
                → ∀ p → Poly p → (λ j → t j (p j ℕ.* k j) * inv-pow-2 (n j)) →0
vanishing-bound t n k t≤ j≤n Pk p Pp = →0-≤ dominates
  (poly-inv-pow-2-→0 (poly-* Ppk Ppk) j≤n)
  where
  Ppk = poly-* Pp Pk

  dominates : ∀ j → t j (p j ℕ.* k j) * inv-pow-2 (n j)
                  ≤ fromℕ ((p j ℕ.* k j) ℕ.* (p j ℕ.* k j)) * inv-pow-2 (n j)
  dominates j = *-monoʳ-≤-nonNeg (inv-pow-2 (n j)) ⦃ nonNegative (0≤inv-pow-2 (n j)) ⦄
                                 (t≤ j (p j ℕ.* k j))
