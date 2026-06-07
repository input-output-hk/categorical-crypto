{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Propositional invariants of the canonical decoder
-- (`Canonical.canonical-go`) specialised at `id-fb`.
--
-- `canonical-target xs id-fb` is NOT *definitionally* `xs` (stdlib's
-- `P.id` is opaque enough that `residual id-fb` is only *pointwise*
-- `id-fb`), so we prove the propositional `canonical-target xs id-fb ≡ xs`
-- using `canonical-go-suc-unfold` to expose the with-block structure.
------------------------------------------------------------------------

module Categories.PermuteCoherence.CanonicalProps where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open P using (Permutation; _∘ₚ_; transpose; lift₀; remove)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.Product.Base using (Σ; _×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong; sym; trans)

open import Level using (Level)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.Canonical

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Pointwise-congruence of `canonical-go .proj₁`, needed for the prep case
-- of the canonical bridge (where `residual (cons-fb (eval-↭ p))` is only
-- *pointwise* equal to `eval-↭ p`).

open import Data.Fin.Properties using (punchOut-cong)
open import Data.Fin.Base using (punchOut)

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
  → ∀ i → residual b P.⟨$⟩ʳ i ≡ residual b' P.⟨$⟩ʳ i
residual-pw-cong b b' eq i =
  punchOut-cong-both _ _ _ _ (eq 0F) (eq (suc i)) _ _
