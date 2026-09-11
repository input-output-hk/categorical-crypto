{-# OPTIONS --safe --without-K #-}

-- Uniform sampling on bit-strings of fixed length, with the basic
-- probability lemma `P-uniform-Vec`: each specific bit-string is
-- sampled with probability `1/2^k`.

module ProbabilisticLogic.Distribution.Uniform where

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_)

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Integer as ℤ using (+_; +≤+)
import Data.Integer.Properties as ℤₚ
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; mkℚ; _/_; _+_; _*_; _≤_; _<_; *≤*; *<*)
open import Data.Rational.Properties using
  ( *-zeroˡ; *-zeroʳ; *-identityˡ; *-identityʳ; *-1-commutativeMonoid
  ; +-assoc; +-identityˡ; +-identityʳ; +-monoˡ-≤; +-monoʳ-≤; *-distribʳ-+
  ; ≤-refl; ≤-reflexive; ≤-trans; <-≤-trans; /-cong; positive⁻¹; ↥p/↧p≡p )
open import Data.Rational.Properties.Ext using (0≤1ℚ; 0≤*; /-*-/; /-+-/; /-mono-≤)
open import Data.Vec using (Vec; []; _∷_)

import Algebra.Properties.CommutativeSemigroup as CommutativeSemigroupProperties
import Data.Rational.Properties as ℚₚ

open import ProbabilisticLogic.Distribution.RationalDist renaming (_>>=ᴹ_ to _>>=_)

private
  module *-CS =
    CommutativeSemigroupProperties (CommutativeMonoid.commutativeSemigroup *-1-commutativeMonoid)

------------------------------------------------------------------------
-- ℚ-valued indicator function on bit-strings.

bool→ℚ : Bool → ℚ
bool→ℚ true  = 1ℚ
bool→ℚ false = 0ℚ

-- The indicator of a Boolean OUTCOME, `bool→ℚ` being the `true` one.  The
-- ε-relations observe both, which is what keeps an answer of `false` distinct
-- from divergence (`ProbabilisticLogic.Dp.Advantage`'s header).
indᵇ : Bool → Bool → ℚ
indᵇ true  = bool→ℚ
indᵇ false = bool→ℚ ∘ not

δ : ∀ {k} → Vec Bool k → Vec Bool k → ℚ
δ y x = bool→ℚ ⌊ x ≟ y ⌋

-- Cons rules for δ on Vec Bool: heads agree means the tail's
-- indicator, heads disagree means 0.
private
  δ-cons-eq : ∀ {k} (b : Bool) (ys xs : Vec Bool k)
            → δ (b ∷ ys) (b ∷ xs) ≡ δ ys xs
  δ-cons-eq false ys xs with xs ≟ ys
  ... | yes _ = refl
  ... | no  _ = refl
  δ-cons-eq true  ys xs with xs ≟ ys
  ... | yes _ = refl
  ... | no  _ = refl

  δ-cons-fT : ∀ {k} (ys xs : Vec Bool k) → δ (false ∷ ys) (true  ∷ xs) ≡ 0ℚ
  δ-cons-fT _ _ = refl

  δ-cons-tF : ∀ {k} (ys xs : Vec Bool k) → δ (true  ∷ ys) (false ∷ xs) ≡ 0ℚ
  δ-cons-tF _ _ = refl

------------------------------------------------------------------------
-- ℕ → ℚ and `1/2^k`, both defined recursively so that the recursion
-- step (`fromℕ (suc m) ≡ 1ℚ + fromℕ m`, resp. `inv-pow-2 (suc k) ≡
-- (1/2) · inv-pow-2 k`) holds definitionally.

fromℕ : ℕ → ℚ
fromℕ zero    = 0ℚ
fromℕ (suc m) = 1ℚ + fromℕ m

inv-pow-2 : ℕ → ℚ
inv-pow-2 zero    = 1ℚ
inv-pow-2 (suc k) = (+ 1 / 2) * inv-pow-2 k

-- `c + n · c ≡ (1ℚ + n) · c`: refold the recursive step.
suc·c : ∀ n c → c + n * c ≡ (1ℚ + n) * c
suc·c n c = trans (cong (_+ n * c) (sym (*-identityˡ c)))
                  (sym (*-distribʳ-+ c 1ℚ n))

0≤½ : 0ℚ ≤ (+ 1 / 2)
0≤½ = *≤* (+≤+ z≤n)

------------------------------------------------------------------------
-- `fromℕ` as a semiring map, `inv-pow-2 k` as the inverse of `fromℕ (2 ^ k)`,
-- and the Archimedean property of ℚ in the shape the vanishing bounds of
-- `ProbabilisticLogic.Distribution.Uniform.Decay` consume.

private
  x≤1+x : ∀ x → x ≤ 1ℚ + x
  x≤1+x x = ≤-trans (≤-reflexive (sym (+-identityˡ x))) (+-monoˡ-≤ x 0≤1ℚ)

0≤fromℕ : ∀ n → 0ℚ ≤ fromℕ n
0≤fromℕ zero    = ≤-refl
0≤fromℕ (suc m) = ≤-trans (0≤fromℕ m) (x≤1+x (fromℕ m))

0<fromℕ-suc : ∀ m → 0ℚ < fromℕ (suc m)
0<fromℕ-suc m = <-≤-trans (positive⁻¹ 1ℚ)
  (≤-trans (≤-reflexive (sym (+-identityʳ 1ℚ))) (+-monoʳ-≤ 1ℚ (0≤fromℕ m)))

fromℕ-mono-≤ : ∀ {m n} → m ℕ.≤ n → fromℕ m ≤ fromℕ n
fromℕ-mono-≤ {n = n} z≤n = 0≤fromℕ n
fromℕ-mono-≤ (s≤s m≤n)   = +-monoʳ-≤ 1ℚ (fromℕ-mono-≤ m≤n)

fromℕ-+ : ∀ m n → fromℕ (m ℕ.+ n) ≡ fromℕ m + fromℕ n
fromℕ-+ zero    n = sym (+-identityˡ (fromℕ n))
fromℕ-+ (suc m) n = trans (cong (λ z → 1ℚ + z) (fromℕ-+ m n))
                          (sym (+-assoc 1ℚ (fromℕ m) (fromℕ n)))

fromℕ-* : ∀ m n → fromℕ (m ℕ.* n) ≡ fromℕ m * fromℕ n
fromℕ-* zero    n = sym (*-zeroˡ (fromℕ n))
fromℕ-* (suc m) n = trans (fromℕ-+ n (m ℕ.* n))
  (trans (cong (λ z → fromℕ n + z) (fromℕ-* m n)) (suc·c (fromℕ m) (fromℕ n)))

fromℕ-/ : ∀ n → fromℕ n ≡ + n / 1
fromℕ-/ zero    = refl
fromℕ-/ (suc m) = begin
  1ℚ + fromℕ m                                ≡⟨ cong (λ z → 1ℚ + z) (fromℕ-/ m) ⟩
  (+ 1 / 1) + (+ m / 1)                       ≡⟨ /-+-/ (+ 1) 1 (+ m) 1 ⟩
  (+ 1 ℤ.* (+ 1) ℤ.+ + m ℤ.* (+ 1)) / (1 ℕ.* 1)
    ≡⟨ /-cong (cong (λ z → + 1 ℤ.* (+ 1) ℤ.+ z) (ℤₚ.*-identityʳ (+ m))) refl ⟩
  + suc m / 1                                 ∎
  where open ≡-Reasoning

0≤inv-pow-2 : ∀ k → 0ℚ ≤ inv-pow-2 k
0≤inv-pow-2 zero    = 0≤1ℚ
0≤inv-pow-2 (suc k) = 0≤* 0≤½ (0≤inv-pow-2 k)

fromℕ-inv-pow-2 : ∀ k → fromℕ (2 ℕ.^ k) * inv-pow-2 k ≡ 1ℚ
fromℕ-inv-pow-2 zero    = trans (*-identityʳ (fromℕ 1)) (+-identityʳ 1ℚ)
fromℕ-inv-pow-2 (suc k) = begin
  fromℕ (2 ℕ.* 2 ℕ.^ k) * ((+ 1 / 2) * inv-pow-2 k)
    ≡⟨ cong (_* ((+ 1 / 2) * inv-pow-2 k)) (fromℕ-* 2 (2 ℕ.^ k)) ⟩
  fromℕ 2 * fromℕ (2 ℕ.^ k) * ((+ 1 / 2) * inv-pow-2 k)
    ≡⟨ *-CS.interchange (fromℕ 2) (fromℕ (2 ℕ.^ k)) (+ 1 / 2) (inv-pow-2 k) ⟩
  fromℕ 2 * (+ 1 / 2) * (fromℕ (2 ℕ.^ k) * inv-pow-2 k)
    ≡⟨ cong (fromℕ 2 * (+ 1 / 2) *_) (fromℕ-inv-pow-2 k) ⟩
  1ℚ                                                    ∎
  where open ≡-Reasoning

-- Every positive ε has `1 ≤ (M + 1) · ε` for some M: ε's own denominator is
-- such an M, since its numerator is at least 1.
archimedean : ∀ {ε} → 0ℚ < ε → Σ[ M ∈ ℕ ] 1ℚ ≤ fromℕ (suc M) * ε
archimedean {ε@(mkℚ i d-1 _)} (*<* 0<i) = d-1 , bnd
  where
  D = suc d-1

  1≤i : + 1 ℤ.≤ i
  1≤i = ℤₚ.i<j⇒suc[i]≤j (subst₂ ℤ._<_ (ℤₚ.*-zeroˡ (+ D)) (ℤₚ.*-identityʳ i) 0<i)

  ineq : + 1 ℤ.* + (1 ℕ.* D) ℤ.≤ (+ D ℤ.* i) ℤ.* + 1
  ineq = begin
    + 1 ℤ.* + (1 ℕ.* D)  ≡⟨ ℤₚ.*-identityˡ (+ (1 ℕ.* D)) ⟩
    + (1 ℕ.* D)          ≡⟨ cong +_ (ℕₚ.*-identityˡ D) ⟩
    + D                  ≡⟨ sym (ℤₚ.*-identityʳ (+ D)) ⟩
    + D ℤ.* + 1          ≤⟨ ℤₚ.*-monoˡ-≤-nonNeg (+ D) 1≤i ⟩
    + D ℤ.* i            ≡⟨ sym (ℤₚ.*-identityʳ (+ D ℤ.* i)) ⟩
    (+ D ℤ.* i) ℤ.* + 1  ∎
    where open ℤₚ.≤-Reasoning

  bnd : 1ℚ ≤ fromℕ D * ε
  bnd = begin
    1ℚ                       ≤⟨ /-mono-≤ (+ 1) 1 (+ D ℤ.* i) (1 ℕ.* D) ineq ⟩
    (+ D ℤ.* i) / (1 ℕ.* D)  ≡⟨ sym (/-*-/ (+ D) 1 i D) ⟩
    (+ D / 1) * (i / D)      ≡⟨ cong₂ _*_ (sym (fromℕ-/ D)) (↥p/↧p≡p ε) ⟩
    fromℕ D * ε              ∎
    where open ℚₚ.≤-Reasoning

------------------------------------------------------------------------
-- Uniform sampling.

uniform-Bool : Dist-ℚ Bool
uniform-Bool = mk-Dist (((+ 1 / 2) , false) NE.∷ ((+ 1 / 2) , true) ∷ []) refl
                       (0≤½ All.∷ 0≤½ All.∷ All.[])

uniform-Vec : (k : ℕ) → Dist-ℚ (Vec Bool k)
uniform-Vec zero    = return-ℚ []
uniform-Vec (suc k) = uniform-Bool >>= λ b → Dmap (b ∷_) (uniform-Vec k)

------------------------------------------------------------------------
-- Each specific bit-string is sampled with probability `1/2^k`.

P-uniform-Vec : ∀ k (h : Vec Bool k)
              → lookupᴰℚ (entries (uniform-Vec k)) (δ h) ≡ inv-pow-2 k
P-uniform-Vec zero    []       = lookupᴰℚ-return [] (δ [])
P-uniform-Vec (suc k) (b ∷ bs) = trans (P-expand b) (P-collapse b)
  where
    open ≡-Reasoning

    -- Sum shape produced by expanding `uniform-Bool >>= Dmap (_ ∷ _)`:
    -- the inner lookup at head `b'` against `(c ∷ bs)`.
    L : Bool → Bool → ℚ
    L c b' = lookupᴰℚ (entries (uniform-Vec k)) (δ (c ∷ bs) ∘ (b' ∷_))

    pair : ℚ → ℚ → ℚ
    pair A B = (+ 1 / 2) * A + ((+ 1 / 2) * B + 0ℚ)

    -- Expand the lookup into the two head-cases.
    P-expand : ∀ c → lookupᴰℚ (entries (uniform-Vec (suc k))) (δ (c ∷ bs))
                  ≡ pair (L c false) (L c true)
    P-expand c = trans
      (lookupᴰℚ-bind (entries uniform-Bool)
        (λ b' → entries (Dmap (b' ∷_) (uniform-Vec k))) (δ (c ∷ bs)))
      (lookupᴰℚ-cong-P (entries uniform-Bool)
        (λ b' → lookupᴰℚ-Dmap (b' ∷_) (uniform-Vec k) (δ (c ∷ bs))))

    -- Algebra: pair specialised once one summand is `inv-pow-2 k` and
    -- the other is `0ℚ`. Both arrangements collapse to `(1/2)·inv-pow-2 k`.
    collapse-IZ : pair (inv-pow-2 k) 0ℚ ≡ (+ 1 / 2) * inv-pow-2 k
    collapse-IZ = begin
        (+ 1 / 2) * inv-pow-2 k + ((+ 1 / 2) * 0ℚ + 0ℚ)
          ≡⟨ cong (λ z → (+ 1 / 2) * inv-pow-2 k + (z + 0ℚ)) (*-zeroʳ (+ 1 / 2)) ⟩
        (+ 1 / 2) * inv-pow-2 k + (0ℚ + 0ℚ)
          ≡⟨ cong (λ z → (+ 1 / 2) * inv-pow-2 k + z) (+-identityˡ 0ℚ) ⟩
        (+ 1 / 2) * inv-pow-2 k + 0ℚ
          ≡⟨ +-identityʳ _ ⟩
        (+ 1 / 2) * inv-pow-2 k ∎

    collapse-ZI : pair 0ℚ (inv-pow-2 k) ≡ (+ 1 / 2) * inv-pow-2 k
    collapse-ZI = begin
        (+ 1 / 2) * 0ℚ + ((+ 1 / 2) * inv-pow-2 k + 0ℚ)
          ≡⟨ cong (_+ ((+ 1 / 2) * inv-pow-2 k + 0ℚ)) (*-zeroʳ (+ 1 / 2)) ⟩
        0ℚ + ((+ 1 / 2) * inv-pow-2 k + 0ℚ)
          ≡⟨ +-identityˡ _ ⟩
        (+ 1 / 2) * inv-pow-2 k + 0ℚ
          ≡⟨ +-identityʳ _ ⟩
        (+ 1 / 2) * inv-pow-2 k ∎

    μk = entries (uniform-Vec k)

    P-collapse : ∀ c → pair (L c false) (L c true) ≡ (+ 1 / 2) * inv-pow-2 k
    P-collapse false =
      trans (cong₂ pair (lookupᴰℚ-cong-P μk (δ-cons-eq false bs))
                        (lookupᴰℚ-cong-P μk (δ-cons-fT bs)))
      (trans (cong₂ pair (P-uniform-Vec k bs) (lookupᴰℚ-zero μk))
             collapse-IZ)
    P-collapse true  =
      trans (cong₂ pair (lookupᴰℚ-cong-P μk (δ-cons-tF bs))
                        (lookupᴰℚ-cong-P μk (δ-cons-eq true bs)))
      (trans (cong₂ pair (lookupᴰℚ-zero μk) (P-uniform-Vec k bs))
             collapse-ZI)
