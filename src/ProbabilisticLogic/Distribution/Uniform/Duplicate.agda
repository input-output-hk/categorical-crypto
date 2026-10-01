{-# OPTIONS --safe --without-K #-}

-- The DUPLICATE flag and its birthday potential, for a run that keeps a
-- growing log of uniform n-bit samples:
--
--     Φ m L = [ L has a repeated entry ] + Γ (length L) m
--
-- `Φ-fresh` and `Φ-keep` need no invariant because the flag IS the bad event; a
-- consumer whose bad event is only implied by a coincidence still owes that
-- implication.

open import Class.DecEq

open import Data.Bool.Base
open import Data.Bool.Properties using (∨-identityʳ; ∨-zeroʳ)
open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat.Base
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  ( +-identityˡ; +-identityʳ; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤
  ; ≤-refl; ≤-reflexive; ≤-trans )
open import Data.Rational.Properties.Ext
open import Data.Vec.Base using (Vec)
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Negation.Core

open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

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

indicator-≤ : ∀ hs h → bool→ℚ (memb h hs) ≤ℚ countMatch hs h
indicator-≤ hs h with memb h hs in e
... | true  = 1≤countMatch hs (memb-∈ hs h e)
... | false = 0≤countMatch hs h

------------------------------------------------------------------------
-- The potential

Φ : ℕ → Log → ℚ
Φ m L = bool→ℚ (dup L) +ℚ Γ (length L) m

0≤Φ : ∀ m L → 0ℚ ≤ℚ Φ m L
0≤Φ m L = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                  (+-mono-≤ (0≤bool (dup L)) (0≤Γ (length L) m))

dup⇒1≤Φ : ∀ m L → dup L ≡ true → 1ℚ ≤ℚ Φ m L
dup⇒1≤Φ m L fl = subst (λ b → 1ℚ ≤ℚ bool→ℚ b +ℚ Γ (length L) m) (sym fl)
  (p≤p+q 1ℚ (0≤Γ (length L) m))

Φ-keep : ∀ m L → Φ m L ≤ℚ Φ (suc m) L
Φ-keep m L = +-monoʳ-≤ (bool→ℚ (dup L)) (Γ-mono (length L) m)

Φ-fresh : ∀ m L → E (uniform-Vec n) (λ h → Φ m (h ∷ L)) ≤ℚ Φ (suc m) L
Φ-fresh m L =
  ≤-trans (≤-reflexive (E-add (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L))
                                              (λ _ → Γ (suc (length L)) m)))
  (≤-trans (+-monoʳ-≤ (E (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L)))
                      (≤-reflexive (E-const (uniform-Vec n) (Γ (suc (length L)) m))))
           (aux (dup L) refl))
  where
    aux : ∀ b → dup L ≡ b
        → E (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L)) +ℚ Γ (suc (length L)) m
        ≤ℚ Φ (suc m) L
    aux true fl = ≤-trans
      (+-monoˡ-≤ (Γ (suc (length L)) m)
        (≤-trans (E-mono (uniform-Vec n) (λ h → bool→ℚ (memb h L ∨ dup L)) (λ _ → 1ℚ)
                   (λ h → ≤-reflexive (cong bool→ℚ
                            (trans (cong (memb h L ∨_) fl) (∨-zeroʳ (memb h L))))))
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
          (≤-reflexive (cong bool→ℚ (trans (cong (memb h L ∨_) fl) (∨-identityʳ (memb h L)))))
          (indicator-≤ L h)

Φ-init : ∀ m → Φ m [] ≤ℚ fromℕ (m * m + m) *ℚ inv-pow-2 n
Φ-init m = ≤-trans (≤-reflexive (+-identityˡ (Γ 0 m))) (≤-trans (Γ-monoˡ 0 m) (birthday m))
