{-# OPTIONS --safe --without-K #-}

-- Acceptance instances: each ready-made potential of `GamePlaying.Potential`,
-- and `GamePlaying.Defer`, at the smallest kernel it is about, carried to an
-- ADAPTIVE bound — what says the builders are usable and not merely well-typed.

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational using (ℚ) renaming (_*_ to _*ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-reflexive; ≤-trans)
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Vec.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import Class.DecEq

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Defer
open import CategoricalCrypto.GamePlaying.Potential
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

import ProbabilisticLogic.Distribution.Uniform.Duplicate as Dup

module CategoricalCrypto.GamePlaying.Test where

------------------------------------------------------------------------
-- The birthday potential at a bare sampling log

module LogMachine (n : ℕ) where

  open Dup n

  logK : Log → Bool → Dist-ℚ (Log × Maybe Hash)
  logK L false = return-ℚ (L , nothing)
  logK L true  = uniform-Vec n >>=ᴹ λ h → return-ℚ (h ∷ L , just h)

  private
    -- annotated: the answer type fixes the type of `nothing`
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

  bounded : ∀ m d → asks≤ m d → badProb guessK id false d ≤ℚ fromℕ m *ℚ inv-pow-2 k
  bounded = badProb-bounded cert

------------------------------------------------------------------------
-- Deferring the draw of a secret the kernel does not look at

module DeferMachine (k : ℕ) where

  open Dup k renaming (Hash to Pt)

  -- `logQ` files a point away without consulting the secret; `readQ` is the
  -- designated step — the only one that looks, and the one the deferring run
  -- draws at.
  data QD : Set where
    logQ  : Pt → QD
    readQ : QD

  St : Set
  St = Maybe Pt × Log

  respD : St → QD → Dist-ℚ (St × Bool)
  respD (mp , L) (logQ x)      = return-ℚ ((mp , x ∷ L) , false)
  respD (just p , L) readQ     = return-ℚ ((just p , L) , memb p L)
  respD (nothing , L) readQ    =
    uniform-Vec k >>=ᴹ λ p → return-ℚ ((just p , L) , memb p L)

  -- Planted, or not yet drawn, at a common log.
  _≋_ : (Pt → St) → St → Set
  f ≋ s = (Σ[ L ∈ Log ] ((∀ p → f p ≡ (just p , L)) × (s ≡ (nothing , L))))
        ⊎ (∀ p → f p ≡ s)

  private
    μ = uniform-Vec k

  avg-bisim : AvgBisim μ respD respD _≋_
  avg-bisim f s (inj₁ (L , ff , refl)) (logQ x) F F′ pt = trans
    (lookupᴰℚ-cong-P (entries μ)
      (λ p → trans (cong (λ z → E (respD z (logQ x)) F) (ff p))
                   (lookupᴰℚ-return ((just p , x ∷ L) , false) F)))
    (trans (pt (λ p → ((just p , x ∷ L) , false)) ((nothing , x ∷ L) , false)
              (inj₁ (x ∷ L , (λ _ → refl) , refl)) (λ _ → refl))
           (sym (lookupᴰℚ-return ((nothing , x ∷ L) , false) F′)))
  avg-bisim f s (inj₁ (L , ff , refl)) readQ F F′ pt = trans
    (lookupᴰℚ-cong-P (entries μ)
      (λ p → trans (cong (λ z → E (respD z readQ) F) (ff p))
                   (trans (lookupᴰℚ-return ((just p , L) , memb p L) F)
                          (avg-here μ _≋_ F F′ pt _ _ (inj₂ λ _ → refl)))))
    (sym (trans (E-bind μ (λ p → return-ℚ ((just p , L) , memb p L)) F′)
                (lookupᴰℚ-cong-P (entries μ)
                  (λ p → lookupᴰℚ-return ((just p , L) , memb p L) F′))))
  avg-bisim f s (inj₂ ff) q F F′ pt = trans
    (trans (lookupᴰℚ-cong-P (entries μ) (λ p → cong (λ z → E (respD z q) F) (ff p)))
           (E-const μ (E (respD s q) F)))
    (lookupᴰℚ-cong-P (entries (respD s q)) λ u → avg-here μ _≋_ F F′ pt u (proj₁ u) (inj₂ λ _ → refl))

  defer : ∀ d → E μ (λ p → Pr₁ (runWith respD (just p , []) d))
              ≡ Pr₁ (runWith respD (nothing , []) d)
  defer d = runWith-avg μ respD respD _≋_ avg-bisim d (λ p → just p , [])
              (nothing , []) (inj₁ ([] , (λ _ → refl) , refl))
