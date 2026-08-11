{-# OPTIONS --safe #-}

-- Uniform sampling on bit-strings of fixed length, with the basic
-- probability lemma `P-uniform-Vec`: each specific bit-string is
-- sampled with probability `1/2^k`.

module ProbabilisticLogic.Distribution.Uniform where

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_)

open import Data.Integer using (+_)
import Data.List.NonEmpty as NE
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_)
open import Data.Rational.Properties using
  (*-zeroʳ; *-identityˡ; +-identityˡ; +-identityʳ; *-distribʳ-+)
open import Data.Vec using (Vec; []; _∷_)

open import ProbabilisticLogic.Distribution.RationalDist renaming (_>>=ᴹ_ to _>>=_)

------------------------------------------------------------------------
-- ℚ-valued indicator function on bit-strings.

bool→ℚ : Bool → ℚ
bool→ℚ true  = 1ℚ
bool→ℚ false = 0ℚ

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

------------------------------------------------------------------------
-- Uniform sampling.

uniform-Bool : Dist-ℚ Bool
uniform-Bool = mk-Dist (((+ 1 / 2) , false) NE.∷ ((+ 1 / 2) , true) ∷ []) refl

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
