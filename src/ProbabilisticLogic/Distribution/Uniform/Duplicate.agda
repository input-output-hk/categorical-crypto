{-# OPTIONS --safe --without-K #-}

-- The DUPLICATE flag and its birthday potential, for a run that keeps a
-- growing log of uniform n-bit samples:
--
--     Φ m L = [ L has a repeated entry ] + Γ (length L) m
--
-- `Φ-fresh` is the drift ONE sample costs — `Collision.E-countMatch` pays for
-- it and `Birthday.Γ-step` books it — and `Φ-keep` says a step that samples
-- nothing is free.  Both hold with NO invariant, because here the flag IS the
-- bad event; a consumer whose bad event is only IMPLIED by a coincidence (as
-- `Examples.ChimericLedger.Birthday`'s is) still owes that implication.

open import Class.DecEq

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; suc; _*_; _+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  ( +-identityˡ; +-identityʳ; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤
  ; ≤-refl; ≤-reflexive; ≤-trans )
open import Data.Vec.Base using (Vec)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation.Core using (¬_)

open import ProbabilisticLogic.Distribution.RationalDist.Expectation using
  (E; E-add; E-const; E-mono; 0≤bool)
open import ProbabilisticLogic.Distribution.Uniform using
  (bool→ℚ; fromℕ; inv-pow-2; uniform-Vec)

module ProbabilisticLogic.Distribution.Uniform.Duplicate (n : ℕ) where

open import ProbabilisticLogic.Distribution.Uniform.Birthday n
open import ProbabilisticLogic.Distribution.Uniform.Collision n

Hash : Set
Hash = Vec Bool n

Log : Set
Log = List Hash

memb : Hash → Log → Bool
memb h []       = false
memb h (g ∷ gs) = ⌊ h ≟ g ⌋ ∨ memb h gs

dup : Log → Bool
dup []       = false
dup (h ∷ hs) = memb h hs ∨ dup hs

memb-∈ : ∀ hs h → memb h hs ≡ true → h ∈ hs
memb-∈ (g ∷ gs) h e with h ≟ g
... | yes p = here p
... | no  _ = there (memb-∈ gs h e)

memb-∉ : ∀ hs h → memb h hs ≡ false → ¬ (h ∈ hs)
memb-∉ (g ∷ gs) h e (here p)    with h ≟ g
...   | yes _ = case e of λ ()
...   | no ¬p = ⊥-elim (¬p p)
memb-∉ (g ∷ gs) h e (there mem) with h ≟ g
...   | yes _ = case e of λ ()
...   | no  _ = memb-∉ gs h e mem

-- "the sample is one of them" is dominated by the number of them it equals,
-- which is what `E-countMatch` averages.
indicator-≤ : ∀ hs h → bool→ℚ (memb h hs) ≤ℚ countMatch hs h
indicator-≤ hs h with memb h hs in e
... | true  = 1≤countMatch hs (memb-∈ hs h e)
... | false = 0≤countMatch hs h

------------------------------------------------------------------------
-- The potential

private
  ∨-trueʳ : ∀ b → (b ∨ true) ≡ true
  ∨-trueʳ true  = refl
  ∨-trueʳ false = refl

  ∨-falseʳ : ∀ b → (b ∨ false) ≡ b
  ∨-falseʳ true  = refl
  ∨-falseʳ false = refl

Φ : ℕ → Log → ℚ
Φ m L = bool→ℚ (dup L) +ℚ Γ (length L) m

0≤Φ : ∀ m L → 0ℚ ≤ℚ Φ m L
0≤Φ m L = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                  (+-mono-≤ (0≤bool (dup L)) (0≤Γ (length L) m))

dup⇒1≤Φ : ∀ m L → dup L ≡ true → 1ℚ ≤ℚ Φ m L
dup⇒1≤Φ m L fl = subst (λ b → 1ℚ ≤ℚ bool→ℚ b +ℚ Γ (length L) m) (sym fl)
  (≤-trans (≤-reflexive (sym (+-identityʳ 1ℚ))) (+-monoʳ-≤ 1ℚ (0≤Γ (length L) m)))

-- A step that does not sample pays nothing and gains a unit of budget.
Φ-keep : ∀ m L → Φ m L ≤ℚ Φ (suc m) L
Φ-keep m L = +-monoʳ-≤ (bool→ℚ (dup L)) (Γ-mono (length L) m)

-- ★ A step that appends ONE fresh uniform sample is paid for exactly: the
-- expected number of entries it collides with is `|L|·2⁻ⁿ`, which is what
-- `Γ-step` charges a unit of budget.
Φ-fresh : ∀ m L → E (uniform-Vec n) (λ h → Φ m (h ∷ L)) ≤ℚ Φ (suc m) L
Φ-fresh m L =
  ≤-trans (≤-reflexive (E-add (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L))
                                              (λ _ → Γ (suc (length L)) m)))
  (≤-trans (+-monoʳ-≤ (E (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L)))
                      (≤-reflexive (E-const (uniform-Vec n) (Γ (suc (length L)) m))))
           (aux (dup L) refl))
  where
    -- flagged already: the indicator is 1 and the budget only has to survive
    -- the pool's growth (`Γ-suc`); unflagged: the indicator is the collision
    -- count, whose average `Γ-step` books.
    aux : ∀ b → dup L ≡ b
        → E (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L)) +ℚ Γ (suc (length L)) m
        ≤ℚ Φ (suc m) L
    aux true fl = ≤-trans
      (+-monoˡ-≤ (Γ (suc (length L)) m)
        (≤-trans (E-mono (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L)) (λ _ → 1ℚ)
                   (λ h → ≤-reflexive (cong bool→ℚ
                            (trans (cong (memb h L ∨_) fl) (∨-trueʳ (memb h L))))))
                 (≤-reflexive (E-const (uniform-Vec n) 1ℚ))))
      (≤-trans (+-monoʳ-≤ 1ℚ (Γ-suc (length L) m))
               (≤-reflexive (cong (_+ℚ Γ (length L) (suc m)) (cong bool→ℚ (sym fl)))))
    aux false fl = ≤-trans
      (+-monoˡ-≤ (Γ (suc (length L)) m)
        (≤-trans (E-mono (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L))
                   (countMatch L) pointwise)
                 (≤-reflexive (E-countMatch L))))
      (≤-reflexive (trans (Γ-step (length L) m)
                          (sym (trans (cong (_+ℚ Γ (length L) (suc m)) (cong bool→ℚ fl))
                                      (+-identityˡ (Γ (length L) (suc m)))))))
      where
        pointwise : ∀ h → bool→ℚ (memb h L ∨ dup L) ≤ℚ countMatch L h
        pointwise h = ≤-trans
          (≤-reflexive (cong bool→ℚ (trans (cong (memb h L ∨_) fl) (∨-falseʳ (memb h L)))))
          (indicator-≤ L h)

-- The headline shape: from an empty log, `m` samples cost at most
-- `(m² + m)·2⁻ⁿ`.
Φ-init : ∀ m → Φ m [] ≤ℚ fromℕ (m * m + m) *ℚ inv-pow-2 n
Φ-init m = ≤-trans (≤-reflexive (+-identityˡ (Γ 0 m)))
                   (≤-trans (Γ-monoˡ 0 m) (birthday m))
