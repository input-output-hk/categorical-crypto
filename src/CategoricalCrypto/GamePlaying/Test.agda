{-# OPTIONS --safe --without-K #-}

-- Acceptance instances for the two ready-made potentials of
-- `GamePlaying.Potential`: the smallest kernel each one is about, carried all
-- the way to an ADAPTIVE bound (`badProb-bounded`), which is what says the
-- builders are usable and not merely well-typed.
--
--   • `LogMachine` — a query either idles or draws one fresh uniform n-bit
--     sample into a log; the flag is a repeat.  `(m² + m)·2⁻ⁿ`.
--   • `GuessMachine` — a query names a k-bit point and the kernel tests it
--     against a fresh uniform draw; the flag is a hit.  `m·2⁻ᵏ`.

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _*_; _+_)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.Rational using (ℚ) renaming (_*_ to _*ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-reflexive; ≤-trans)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import Class.DecEq

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Potential
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist using
  (Dist-ℚ; _>>=ᴹ_; entries; return-ℚ; lookupᴰℚ-cong-P; lookupᴰℚ-return)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; E-bind)
open import ProbabilisticLogic.Distribution.Uniform using
  (0≤inv-pow-2; bool→ℚ; fromℕ; inv-pow-2; uniform-Vec)

import ProbabilisticLogic.Distribution.Uniform.Duplicate as Dup

module CategoricalCrypto.GamePlaying.Test where

------------------------------------------------------------------------
-- The birthday potential at a bare sampling log

module LogMachine (n : ℕ) where

  open Dup n

  -- `false` idles, `true` draws one fresh sample and logs it.
  logK : Log → Bool → Dist-ℚ (Log × Maybe Hash)
  logK L false = return-ℚ (L , nothing)
  logK L true  = uniform-Vec n >>=ᴹ λ h → return-ℚ (h ∷ L , just h)

  private
    -- the integrand, annotated: the answer type is what fixes `nothing`'s
    onLog : (Log → ℚ) → Log × Maybe Hash → ℚ
    onLog F sr = F (proj₁ sr)

  keep-or-sample : KeepOrSample n logK id
  keep-or-sample L false F = inj₁ (lookupᴰℚ-return (L , nothing) (onLog F))
  keep-or-sample L true  F = inj₂
    (trans (E-bind (uniform-Vec n) (λ h → return-ℚ (h ∷ L , just h)) (onLog F))
           (lookupᴰℚ-cong-P (entries (uniform-Vec n))
             (λ h → lookupᴰℚ-return (h ∷ L , just h) (onLog F))))

  cert : SuperCert logK dup [] (λ m → fromℕ (m * m + m) *ℚ inv-pow-2 n)
  cert = collision-cert n logK id [] refl keep-or-sample

  -- the adaptive bound: `m` queries collide with probability ≤ (m² + m)·2⁻ⁿ
  bounded : ∀ m d → asks≤ m d → badProb logK dup [] d ≤ℚ fromℕ (m * m + m) *ℚ inv-pow-2 n
  bounded = badProb-bounded cert

------------------------------------------------------------------------
-- The guessing potential at a bare point-guessing game

module GuessMachine (k : ℕ) where

  Pt : Set
  Pt = Vec Bool k

  -- The state is the flag alone: a query names a point and the kernel tests
  -- it against a FRESH uniform draw (the lazily sampled secret).
  guessK : Bool → Pt → Dist-ℚ (Bool × ⊤)
  guessK f p = uniform-Vec k >>=ᴹ λ r → return-ℚ (f ∨ ⌊ r ≟ p ⌋ , tt)

  raise : RareRaise guessK id (inv-pow-2 k)
  raise f p = ≤-trans
    (≤-reflexive
      (trans (E-bind (uniform-Vec k) (λ r → return-ℚ (f ∨ ⌊ r ≟ p ⌋ , tt))
               (λ sr → bool→ℚ (proj₁ sr)))
             (lookupᴰℚ-cong-P (entries (uniform-Vec k))
               (λ r → lookupᴰℚ-return (f ∨ ⌊ r ≟ p ⌋ , tt) (λ sr → bool→ℚ (proj₁ sr))))))
    (guess-drift k f p)

  cert : SuperCert guessK id false (λ m → fromℕ m *ℚ inv-pow-2 k)
  cert = rare-cert guessK id false (inv-pow-2 k) (0≤inv-pow-2 k) refl raise

  -- the adaptive bound: `m` guesses hit the point with probability ≤ m·2⁻ᵏ
  bounded : ∀ m d → asks≤ m d → badProb guessK id false d ≤ℚ fromℕ m *ℚ inv-pow-2 k
  bounded = badProb-bounded cert
