{-# OPTIONS --safe --without-K #-}

-- Two ready-made potentials: `SuperCert`s a reactive kernel gets for free once
-- its flag is one of the two shapes a random-oracle argument keeps producing.
--
--   • `collision-cert` — the BIRTHDAY flag: the kernel keeps a log of uniform
--     n-bit samples and the flag is a repeat in it.  What the kernel owes is
--     `KeepOrSample`: per query the log either stays put or gains exactly one
--     fresh uniform sample.  The bound is `(m² + m)·2⁻ⁿ`.  The invariant is
--     trivial, so a bad event merely IMPLIED by a repeat needs its own
--     certificate carrying the implication as an invariant.
--   • `rare-cert` — the RARE flag: any flag the kernel raises with probability
--     at most ε per query is up at some point with probability at most
--     `m·ε`.  `guess-drift` discharges its hypothesis at ε ≡ 2⁻ᵏ for the flag
--     "this query hit a fresh uniform k-bit point" — the GUESSING potential a
--     hiding argument for `commit = H(m ∥ r)` runs on.  NB the FRESH draw is
--     what makes the per-query drift provable: a secret already determined by
--     the state is one the next query can hit with probability 1, so a fixed
--     secret must be sampled LAZILY for this potential to apply (see
--     `docs/ro-game-hop.md`).
--
-- `∨-cert` is the union bound the two are combined by: a proof whose bad event
-- is a disjunction — a binding argument's is — adds the potentials and adds the
-- bounds.

open import Class.DecEq

open import Data.Bool.Base
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.List.Base
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  ( +-assoc; +-identityˡ; +-identityʳ; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; ≤-reflexive
  ; ≤-trans )
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Vec.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import CategoricalCrypto.GamePlaying
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

import ProbabilisticLogic.Distribution.Uniform.Duplicate as Dup

module CategoricalCrypto.GamePlaying.Potential where

private variable Q R St : Set

------------------------------------------------------------------------
-- The rare flag: a per-query raise probability of ε costs m·ε

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
  ; pres   = λ s q _ → OnSupport-⊤ (resp s q)
  ; φ-nn   = λ m s _ → ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                               (+-mono-≤ (0≤bool (flag s)) (0≤* (0≤fromℕ m) 0≤e))
  ; φ-bad  = λ m s _ fl → subst (λ b → 1ℚ ≤ℚ bool→ℚ b +ℚ fromℕ m *ℚ e) (sym fl)
                            (≤-trans (≤-reflexive (sym (+-identityʳ 1ℚ)))
                                     (+-monoʳ-≤ 1ℚ (0≤* (0≤fromℕ m) 0≤e)))
  ; φ-step = λ m s q _ → step m s q
  ; φ-init = λ m → ≤-trans (≤-reflexive (cong (λ b → bool→ℚ b +ℚ fromℕ m *ℚ e) init))
                           (≤-reflexive (+-identityˡ (fromℕ m *ℚ e)))
  }
  where
    φ : ℕ → St → ℚ
    φ m s = bool→ℚ (flag s) +ℚ fromℕ m *ℚ e

    step : ∀ m s q → E (resp s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s
    step m s q = ≤-trans
      (≤-reflexive (E-+const (resp s q) (λ sr → bool→ℚ (flag (proj₁ sr))) (fromℕ m *ℚ e)))
      (≤-trans (+-monoˡ-≤ (fromℕ m *ℚ e) (raise s q))
               (≤-reflexive (trans (+-assoc (bool→ℚ (flag s)) e (fromℕ m *ℚ e))
                                   (cong (bool→ℚ (flag s) +ℚ_) (suc·c (fromℕ m) e)))))

guess-drift : ∀ k (f : Bool) (p : Vec Bool k)
            → E (uniform-Vec k) (λ r → bool→ℚ (f ∨ ⌊ r ≟ p ⌋))
            ≤ℚ bool→ℚ f +ℚ inv-pow-2 k
guess-drift k true  p = ≤-trans (≤-reflexive (E-const (uniform-Vec k) 1ℚ))
  (≤-trans (≤-reflexive (sym (+-identityʳ 1ℚ))) (+-monoʳ-≤ 1ℚ (0≤inv-pow-2 k)))
guess-drift k false p = ≤-trans (≤-reflexive (P-uniform-Vec k p))
                                (≤-reflexive (sym (+-identityˡ (inv-pow-2 k))))

-- A guess that is only made when `a` holds.
drift-∧ : ∀ k (g a : Bool) (p : Vec Bool k)
        → E (uniform-Vec k) (λ ρ → bool→ℚ (g ∨ (a ∧ ⌊ ρ ≟ p ⌋))) ≤ℚ bool→ℚ g +ℚ inv-pow-2 k
drift-∧ k g true  p = guess-drift k g p
drift-∧ k g false p = ≤-trans
  (≤-reflexive (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ _ → cong bool→ℚ (∨-identityʳ g)))
                      (E-const (uniform-Vec k) (bool→ℚ g))))
  (0≤drift k g)

∨-cert : {resp : St → Q → Dist-ℚ (St × R)} {f g : St → Bool} {s₀ : St}
         {ε₁ ε₂ : ℕ → ℚ}
       → SuperCert resp f s₀ ε₁ → SuperCert resp g s₀ ε₂
       → SuperCert resp (λ s → f s ∨ g s) s₀ (λ m → ε₁ m +ℚ ε₂ m)
∨-cert {resp = resp} {f} {g} c₁ c₂ = record
  { Inv    = λ s → C₁.Inv s × C₂.Inv s
  ; φ      = λ m s → C₁.φ m s +ℚ C₂.φ m s
  ; inv₀   = C₁.inv₀ , C₂.inv₀
  ; pres   = λ s q i → ListAll.zip (C₁.pres s q (proj₁ i) , C₂.pres s q (proj₂ i))
  ; φ-nn   = λ m s i → ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                               (+-mono-≤ (C₁.φ-nn m s (proj₁ i)) (C₂.φ-nn m s (proj₂ i)))
  ; φ-bad  = bad
  ; φ-step = step
  ; φ-init = λ m → +-mono-≤ (C₁.φ-init m) (C₂.φ-init m)
  }
  where
  module C₁ = SuperCert c₁
  module C₂ = SuperCert c₂

  bad : ∀ m s → C₁.Inv s × C₂.Inv s → (f s ∨ g s) ≡ true
      → 1ℚ ≤ℚ C₁.φ m s +ℚ C₂.φ m s
  bad m s i e with f s in ef
  ... | true  = ≤-trans (≤-reflexive (sym (+-identityʳ 1ℚ)))
      (+-mono-≤ (C₁.φ-bad m s (proj₁ i) ef) (C₂.φ-nn m s (proj₂ i)))
  ... | false = ≤-trans (≤-reflexive (sym (+-identityˡ 1ℚ)))
      (+-mono-≤ (C₁.φ-nn m s (proj₁ i)) (C₂.φ-bad m s (proj₂ i) e))

  step : ∀ m s q → C₁.Inv s × C₂.Inv s
       → E (resp s q) (λ sr → C₁.φ m (proj₁ sr) +ℚ C₂.φ m (proj₁ sr))
         ≤ℚ C₁.φ (suc m) s +ℚ C₂.φ (suc m) s
  step m s q i = ≤-trans
    (≤-reflexive (E-add (resp s q) (λ sr → C₁.φ m (proj₁ sr)) (λ sr → C₂.φ m (proj₁ sr))))
    (+-mono-≤ (C₁.φ-step m s q (proj₁ i)) (C₂.φ-step m s q (proj₂ i)))

------------------------------------------------------------------------
-- The birthday flag: a growing log of uniform samples

module _ (n : ℕ) where

  open Dup n

  -- Read at an ARBITRARY integrand of the log: a statement about the log's
  -- marginal, not about the whole kernel.
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
    ; pres   = λ s q _ → OnSupport-⊤ (resp s q)
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
