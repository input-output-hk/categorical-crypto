{-# OPTIONS --safe --without-K #-}

-- Hitting a recorded set of bit-strings with a fresh uniform sample: the
-- counting a birthday bound spends at each query.
--
-- `countMatch hs` counts the entries of `hs` a sample equals.  It dominates
-- the indicator of "the sample is one of them" (`1≤countMatch`) and has
-- expectation exactly `|hs|/2ⁿ` (`E-countMatch`) — so a union bound over the
-- run needs no independence argument, only linearity of expectation.
--
-- `Examples.RandomOracle`'s `count-matches`/`E-collisions` are the same facts
-- read off a random-oracle table; this is the list-of-hashes form a bound that
-- counts something other than table entries asks for.

open import Class.DecEq

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Properties using
  ( *-zeroˡ; +-identityˡ; +-identityʳ; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤
  ; ≤-reflexive; ≤-trans )
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no; ⌊_⌋)

open import ProbabilisticLogic.Distribution.RationalDist using
  (entries; lookupᴰℚ-zero; lookupᴰℚ-+)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; 0≤bool)
open import ProbabilisticLogic.Distribution.Uniform using
  (P-uniform-Vec; bool→ℚ; fromℕ; inv-pow-2; suc·c; uniform-Vec; δ)

module ProbabilisticLogic.Distribution.Uniform.Collision (n : ℕ) where

private
  Hash : Set
  Hash = Vec Bool n

countMatch : List Hash → Hash → ℚ
countMatch []       _ = 0ℚ
countMatch (g ∷ gs) h = δ g h + countMatch gs h

private
  0≤δ : (g h : Hash) → 0ℚ ≤ δ g h
  0≤δ g h = 0≤bool ⌊ h ≟ g ⌋

0≤countMatch : ∀ hs h → 0ℚ ≤ countMatch hs h
0≤countMatch []       h = ≤-reflexive refl
0≤countMatch (g ∷ gs) h = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                                  (+-mono-≤ (0≤δ g h) (0≤countMatch gs h))

1≤countMatch : ∀ {h} hs → h ∈ hs → 1ℚ ≤ countMatch hs h
1≤countMatch {h} (g ∷ gs) (here refl) with h ≟ g
... | yes _  = ≤-trans (≤-reflexive (sym (+-identityʳ 1ℚ)))
                       (+-monoʳ-≤ 1ℚ (0≤countMatch gs h))
... | no ¬eq = ⊥-elim (¬eq refl)
1≤countMatch {h} (g ∷ gs) (there mem) =
  ≤-trans (1≤countMatch gs mem)
          (≤-trans (≤-reflexive (sym (+-identityˡ (countMatch gs h))))
                   (+-monoˡ-≤ (countMatch gs h) (0≤δ g h)))

-- Linearity of expectation, one entry at a time: no independence anywhere.
E-countMatch : ∀ hs → E (uniform-Vec n) (countMatch hs) ≡ fromℕ (length hs) * inv-pow-2 n
E-countMatch []       = trans (lookupᴰℚ-zero (entries (uniform-Vec n)))
                              (sym (*-zeroˡ (inv-pow-2 n)))
E-countMatch (g ∷ gs) = begin
  E (uniform-Vec n) (λ h → δ g h + countMatch gs h)
    ≡⟨ lookupᴰℚ-+ (entries (uniform-Vec n)) (δ g) (countMatch gs) ⟩
  E (uniform-Vec n) (δ g) + E (uniform-Vec n) (countMatch gs)
    ≡⟨ cong₂ _+_ (P-uniform-Vec n g) (E-countMatch gs) ⟩
  inv-pow-2 n + fromℕ (length gs) * inv-pow-2 n
    ≡⟨ suc·c (fromℕ (length gs)) (inv-pow-2 n) ⟩
  (1ℚ + fromℕ (length gs)) * inv-pow-2 n
    ∎
  where open ≡-Reasoning
