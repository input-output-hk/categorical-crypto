{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Canonical equivalence of `_↭_` derivations, plus the one fact about
-- head-removal the Lehmer route needs.
--
-- `_≅↭_` relates two `_↭_` derivations that agree on their evaluated
-- finite bijection (via `eval-↭`).
--
-- Under `_≡_`, stdlib's `remove`/`punchOut` are opaque, so `remove 0F b`
-- is only *pointwise* equal to `remove 0F b'` when `b`, `b'` agree
-- pointwise.  `residual-pw-cong` supplies that pointwise equation; it is
-- consumed by `Word.canonW-resp-≈` and `LehmerRotate.canonW-cons-rotate`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Canonical where

open import Data.Nat.Base using (suc)
open import Data.Fin.Base using (Fin; suc; punchOut)
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Properties using (punchOut-cong)
import Data.Fin.Permutation as P
open P using (remove)
open import Data.List.Base using (List)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)

open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Canonical equivalence: two derivations are canonically equivalent when
-- they agree on the underlying finite bijection.

infix 4 _≅↭_
_≅↭_ : {xs ys : List A} → xs ↭ ys → xs ↭ ys → Set
p ≅↭ q = eval-↭ p ≈-fb eval-↭ q

------------------------------------------------------------------------
-- Pointwise congruence of head-removal.

-- `punchOut` is congruent in both arguments (stdlib provides only the `j` half).
private
  punchOut-cong-both
    : ∀ {n} (i i' j j' : Fin (suc n))
        (ei : i ≡ i') (ej : j ≡ j')
        (p : i ≢ j) (p' : i' ≢ j')
    → punchOut p ≡ punchOut p'
  punchOut-cong-both i .i j j' refl ej _ _ = punchOut-cong i ej

residual-pw-cong
  : ∀ {n} (b b' : FinBij (suc n) (suc n))
  → (∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
  → ∀ i → remove 0F b P.⟨$⟩ʳ i ≡ remove 0F b' P.⟨$⟩ʳ i
residual-pw-cong b b' eq i =
  punchOut-cong-both _ _ _ _ (eq 0F) (eq (suc i)) _ _
