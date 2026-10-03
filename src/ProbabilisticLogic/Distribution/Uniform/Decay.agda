{-# OPTIONS --safe --without-K #-}

-- Vanishing bounds: polynomially many `1/2^j`-sized parts tend to 0.  `_→0` and
-- `Negligible` are the two grades `CategoricalCrypto.UC.Approximate`'s bounds
-- are stated at, so these lemmas inhabit them on the nose.

module ProbabilisticLogic.Distribution.Uniform.Decay where

open import Data.Integer.Base using (+_)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Nat.Poly using (Poly; poly-*; poly-const; poly-≤2^)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (Σ-syntax; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _/_; _≤_; _>_; nonNegative; positive)
open import Data.Rational.Properties using
  ( *-assoc; *-cancelˡ-≤-pos; *-distribˡ-+; *-identityˡ; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg
  ; *-zeroʳ; +-mono-≤; <⇒≤; ≤-trans; module ≤-Reasoning)
open import Data.Rational.Properties.Ext using (0<½*; ½*+½*)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; subst)

open import ProbabilisticLogic.Distribution.Uniform using
  ( fromℕ; inv-pow-2; archimedean; fromℕ-*; fromℕ-/; fromℕ-inv-pow-2; fromℕ-mono-≤
  ; 0<fromℕ-suc; 0≤fromℕ; 0≤inv-pow-2 )

private variable
  s t u : ℕ → ℚ
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

→0-cong : (∀ n → s n ≡ t n) → s →0 → t →0
→0-cong eq h ε ε>0 = let (N , bnd) = h ε ε>0 in N , λ n le → subst (_≤ ε) (eq n) (bnd n le)

→0-0 : (λ (_ : ℕ) → 0ℚ) →0
→0-0 _ ε>0 = 0 , λ _ _ → <⇒≤ ε>0

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

------------------------------------------------------------------------
-- Negligible
------------------------------------------------------------------------

-- Negligible: eventually below every inverse polynomial, which is strictly more
-- than `_→0` (`1/n` vanishes and is not negligible).  Stated by MAGNIFICATION:
-- every polynomially magnified copy still vanishes.
Negligible : (ℕ → ℚ) → Set
Negligible s = (p : ℕ → ℕ) → Poly p → (λ n → (+ p n / 1) * s n) →0

Negligible⇒→0 : {s : ℕ → ℚ} → Negligible s → s →0
Negligible⇒→0 {s} neg = →0-cong (λ n → *-identityˡ (s n)) (neg (λ _ → 1) (poly-const 1))

Negligible-0 : Negligible (λ _ → 0ℚ)
Negligible-0 p _ = →0-cong (λ n → sym (*-zeroʳ (+ p n / 1))) →0-0

Negligible-+ : {s t : ℕ → ℚ} → Negligible s → Negligible t → Negligible (λ n → s n + t n)
Negligible-+ {s} {t} ns nt p Pp =
  →0-cong (λ n → sym (*-distribˡ-+ (+ p n / 1) (s n) (t n))) (→0-+ (ns p Pp) (nt p Pp))

Negligible-cong : ((n : ℕ) → s n ≡ u n) → Negligible s → Negligible u
Negligible-cong eq neg r Pr = →0-cong (λ n → cong ((+ r n / 1) *_) (eq n)) (neg r Pr)

-- Negligibility is a BOUND, so it passes to anything dominated pointwise: the
-- magnified copies are dominated too, the magnifier being nonnegative.
Negligible-≤ : ((n : ℕ) → s n ≤ u n) → Negligible u → Negligible s
Negligible-≤ {s} {u} s≤u neg r Pr = →0-≤ mono (neg r Pr)
  where
  mono : (n : ℕ) → (+ r n / 1) * s n ≤ (+ r n / 1) * u n
  mono n = subst (λ z → z * s n ≤ z * u n) (fromℕ-/ (r n))
             (*-monoˡ-≤-nonNeg (fromℕ (r n)) ⦃ nonNegative (0≤fromℕ (r n)) ⦄ (s≤u n))
