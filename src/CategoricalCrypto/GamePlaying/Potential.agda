{-# OPTIONS --safe --without-K #-}

-- Two ready-made potentials: `SuperCert`s a reactive kernel gets for free once
-- its flag is one of the two shapes a random-oracle argument keeps producing.
--
--   • `collision-cert` — the BIRTHDAY flag: the kernel keeps a log of uniform
--     n-bit samples and the flag is a repeat in it.  What the kernel owes is
--     `KeepOrSample`: per query the log either stays put or gains exactly one
--     fresh uniform sample.  The bound is `(m² + m)·2⁻ⁿ`.  The invariant is
--     trivial — `Uniform.Duplicate`'s potential needs none, because there the
--     flag IS the bad event; a consumer whose bad event is merely IMPLIED by a
--     coincidence (`Examples.ChimericLedger.Birthday`) owes the implication as
--     its own invariant and cannot use this builder as it stands.
--   • `rare-cert` — the RARE flag: any flag the kernel raises with probability
--     at most ε per query and never lowers is up with probability at most
--     `m·ε`.  `guess-drift` discharges its hypothesis at ε ≡ 2⁻ᵏ for the flag
--     "this query hit a fresh uniform k-bit point" — the GUESSING potential a
--     hiding argument for `commit = H(m ∥ r)` runs on.  NB the FRESH draw is
--     what makes the per-query drift provable: a secret already determined by
--     the state is one the next query can hit with probability 1, so a fixed
--     secret must be sampled LAZILY for this potential to apply (see
--     `docs/ro-game-hop.md`).

open import Class.DecEq

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty as NE using ()
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Nat.Base using (ℕ; suc; _*_; _+_)
open import Data.Product.Base using (_×_; proj₁)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; nonNegative)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  ( *-monoʳ-≤-nonNeg; *-zeroˡ; +-assoc; +-identityˡ; +-identityʳ; +-mono-≤
  ; +-monoˡ-≤; +-monoʳ-≤; ≤-reflexive; ≤-trans )
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality
open import Function.Base using (case_of_)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import CategoricalCrypto.GamePlaying
open import ProbabilisticLogic.Distribution.RationalDist using
  (Dist-ℚ; OnSupport; entries)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using
  (E; E-add; E-const; 0≤bool)
open import ProbabilisticLogic.Distribution.Uniform using
  ( 0≤fromℕ; 0≤inv-pow-2; P-uniform-Vec; bool→ℚ; fromℕ; inv-pow-2; suc·c
  ; uniform-Vec )

import ProbabilisticLogic.Distribution.Uniform.Duplicate as Dup

module CategoricalCrypto.GamePlaying.Potential where

private
  variable Q R St : Set

  -- the trivial invariant: no state is excluded, so `Preserved` is free
  os-⊤ : {A : Set} (μ : Dist-ℚ A) → OnSupport (λ _ → ⊤) μ
  os-⊤ μ = ListAll.universal (λ _ → tt) (NE.toList (entries μ))

  0≤scaled : ∀ {e} → 0ℚ ≤ℚ e → ∀ m → 0ℚ ≤ℚ fromℕ m *ℚ e
  0≤scaled {e} 0≤e m = ≤-trans (≤-reflexive (sym (*-zeroˡ e)))
    (*-monoʳ-≤-nonNeg e ⦃ nonNegative 0≤e ⦄ (0≤fromℕ m))

------------------------------------------------------------------------
-- The rare flag: a per-query raise probability of ε costs m·ε

-- A flag raised with probability at most ε per query, and never lowered.
RareRaise : (St → Q → Dist-ℚ (St × R)) → (St → Bool) → ℚ → Set
RareRaise resp flag e = ∀ s q → E (resp s q) (λ sr → bool→ℚ (flag (proj₁ sr)))
                              ≤ℚ bool→ℚ (flag s) +ℚ e

rare-cert : (resp : St → Q → Dist-ℚ (St × R)) (flag : St → Bool) (s₀ : St) (e : ℚ)
          → 0ℚ ≤ℚ e → flag s₀ ≡ false → RareRaise resp flag e
          → SuperCert resp flag s₀ (λ m → fromℕ m *ℚ e)
rare-cert {St = St} resp flag s₀ e 0≤e init raise = record
  { Inv    = λ _ → ⊤
  ; φ      = φ
  ; inv₀   = tt
  ; pres   = λ s q _ → os-⊤ (resp s q)
  ; φ-nn   = λ m s _ → ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                               (+-mono-≤ (0≤bool (flag s)) (0≤scaled 0≤e m))
  ; φ-bad  = λ m s _ fl → subst (λ b → 1ℚ ≤ℚ bool→ℚ b +ℚ fromℕ m *ℚ e) (sym fl)
                            (≤-trans (≤-reflexive (sym (+-identityʳ 1ℚ)))
                                     (+-monoʳ-≤ 1ℚ (0≤scaled 0≤e m)))
  ; φ-step = λ m s q _ → step m s q
  ; φ-init = λ m → ≤-trans (≤-reflexive (cong (λ b → bool→ℚ b +ℚ fromℕ m *ℚ e) init))
                           (≤-reflexive (+-identityˡ (fromℕ m *ℚ e)))
  }
  where
    φ : ℕ → St → ℚ
    φ m s = bool→ℚ (flag s) +ℚ fromℕ m *ℚ e

    step : ∀ m s q → E (resp s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s
    step m s q = ≤-trans
      (≤-reflexive (trans (E-add (resp s q) (λ sr → bool→ℚ (flag (proj₁ sr)))
                                            (λ _ → fromℕ m *ℚ e))
                          (cong (E (resp s q) (λ sr → bool→ℚ (flag (proj₁ sr))) +ℚ_)
                                (E-const (resp s q) (fromℕ m *ℚ e)))))
      (≤-trans (+-monoˡ-≤ (fromℕ m *ℚ e) (raise s q))
               (≤-reflexive (trans (+-assoc (bool→ℚ (flag s)) e (fromℕ m *ℚ e))
                                   (cong (bool→ℚ (flag s) +ℚ_) (suc·c (fromℕ m) e)))))

-- The drift of a flag the kernel raises by testing its query against a FRESH
-- uniform k-bit draw: 2⁻ᵏ per query, whatever the query — `rare-cert`'s
-- hypothesis at ε ≡ 2⁻ᵏ, which is the guessing potential.
guess-drift : ∀ k (f : Bool) (p : Vec Bool k)
            → E (uniform-Vec k) (λ r → bool→ℚ (f ∨ ⌊ r ≟ p ⌋))
            ≤ℚ bool→ℚ f +ℚ inv-pow-2 k
guess-drift k true  p = ≤-trans (≤-reflexive (E-const (uniform-Vec k) 1ℚ))
  (≤-trans (≤-reflexive (sym (+-identityʳ 1ℚ))) (+-monoʳ-≤ 1ℚ (0≤inv-pow-2 k)))
guess-drift k false p = ≤-trans (≤-reflexive (P-uniform-Vec k p))
                                (≤-reflexive (sym (+-identityˡ (inv-pow-2 k))))

------------------------------------------------------------------------
-- The birthday flag: a growing log of uniform samples

module _ (n : ℕ) where

  open Dup n

  -- Per query the log either stays put or gains ONE fresh uniform sample —
  -- read at the expectation of an ARBITRARY integrand, which makes this a
  -- statement about the log's marginal rather than about the whole kernel.
  KeepOrSample : (St → Q → Dist-ℚ (St × R)) → (St → Log) → Set
  KeepOrSample resp log = ∀ s q (F : Log → ℚ)
    → (E (resp s q) (λ sr → F (log (proj₁ sr))) ≡ F (log s))
    ⊎ (E (resp s q) (λ sr → F (log (proj₁ sr))) ≡ E (uniform-Vec n) (λ h → F (h ∷ log s)))

  collision-cert : (resp : St → Q → Dist-ℚ (St × R)) (log : St → Log) (s₀ : St)
                 → log s₀ ≡ [] → KeepOrSample resp log
                 → SuperCert resp (λ s → dup (log s)) s₀
                     (λ m → fromℕ (m * m + m) *ℚ inv-pow-2 n)
  collision-cert resp log s₀ init kos = record
    { Inv    = λ _ → ⊤
    ; φ      = λ m s → Φ m (log s)
    ; inv₀   = tt
    ; pres   = λ s q _ → os-⊤ (resp s q)
    ; φ-nn   = λ m s _ → 0≤Φ m (log s)
    ; φ-bad  = λ m s _ → dup⇒1≤Φ m (log s)
    ; φ-step = λ m s q _ → step m s q
    ; φ-init = λ m → subst (λ L → Φ m L ≤ℚ fromℕ (m * m + m) *ℚ inv-pow-2 n)
                           (sym init) (Φ-init m)
    }
    where
      step : ∀ m s q → E (resp s q) (λ sr → Φ m (log (proj₁ sr))) ≤ℚ Φ (suc m) (log s)
      step m s q = case kos s q (Φ m) of λ where
        (inj₁ keep)   → ≤-trans (≤-reflexive keep) (Φ-keep m (log s))
        (inj₂ sample) → ≤-trans (≤-reflexive sample) (Φ-fresh m (log s))
