{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Fin-bijection reindexing of `tabulate`; cardinality equality follows
-- from injectivity in both directions, rather than a caller hypothesis.
--------------------------------------------------------------------------------

module Categories.Combinatorics.TabulateBij where

open import Data.Fin
import Data.Fin.Permutation as FinPerm
open import Data.Fin.Properties
open import Data.List
open import Data.List.Properties
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Nat using (ℕ; zero; suc)
import Function as Fun
open import Relation.Binary.PropositionalEquality

private
  variable
    n m : ℕ
    A : Set

  tabulate-shift-↭
    : (f : Fin (suc n) → A) (k : Fin (suc n))
    → tabulate f Perm.↭ f k ∷ tabulate (f Fun.∘ punchIn k)
  tabulate-shift-↭ f zero            = Perm.refl
  tabulate-shift-↭ {n = suc n'} f (suc k) =
    Perm.trans
      (Perm.prep (f zero) (tabulate-shift-↭ (f Fun.∘ suc) k))
      (Perm.swap (f zero) (f (suc k)) Perm.refl)

tabulate-bij-↭
  : (f : Fin n → A) (π : Fin n → Fin n) (π⁻¹ : Fin n → Fin n)
  → (∀ i → π⁻¹ (π i) ≡ i) → (∀ i → π (π⁻¹ i) ≡ i)
  → tabulate (f Fun.∘ π) Perm.↭ tabulate f
tabulate-bij-↭ {n = zero}    f π π⁻¹ _      _       = Perm.refl
tabulate-bij-↭ {n = suc n'}  f π π⁻¹ leftInv rightInv =
  Perm.trans (Perm.prep (f (π zero)) ih) (Perm.↭-sym (tabulate-shift-↭ f k))
  where
    k = π zero

    π-inj : ∀ {i j} → π i ≡ π j → i ≡ j
    π-inj {i} {j} eq = trans (sym (leftInv i)) (trans (cong π⁻¹ eq) (leftInv j))

    π-suc-≢-k : ∀ (i : Fin n') → k ≢ π (suc i)
    π-suc-≢-k i eq with π-inj (sym eq)
    ... | ()

    π' : Fin n' → Fin n'
    π' i = punchOut (π-suc-≢-k i)

    zero-≢-π⁻¹-pIn : ∀ (j : Fin n') → zero ≢ π⁻¹ (punchIn k j)
    zero-≢-π⁻¹-pIn j eq =
      punchInᵢ≢i k j
        (trans (sym (rightInv (punchIn k j))) (cong π (sym eq)))

    π'⁻¹ : Fin n' → Fin n'
    π'⁻¹ j = punchOut (zero-≢-π⁻¹-pIn j)

    punchIn-π' : ∀ (i : Fin n') → punchIn k (π' i) ≡ π (suc i)
    punchIn-π' i = punchIn-punchOut (π-suc-≢-k i)

    punchIn-π'⁻¹ : ∀ (j : Fin n') → punchIn zero (π'⁻¹ j) ≡ π⁻¹ (punchIn k j)
    punchIn-π'⁻¹ j = punchIn-punchOut (zero-≢-π⁻¹-pIn j)

    π'-left : ∀ i → π'⁻¹ (π' i) ≡ i
    π'-left i = punchOut-cong {n = n'} zero {i≢k = λ ()}
      (trans (cong π⁻¹ (punchIn-π' i)) (leftInv (suc i)))

    π'-rght : ∀ j → π' (π'⁻¹ j) ≡ j
    π'-rght j =
      trans (punchOut-cong k
              {i≢k = punchInᵢ≢i k j Fun.∘ sym}
              (trans (cong π (punchIn-π'⁻¹ j))
                     (rightInv (punchIn k j))))
            (punchOut-punchIn k)

    pointwise-eq : ∀ (i : Fin n') → f (π (suc i)) ≡ f (punchIn k (π' i))
    pointwise-eq i = cong f (sym (punchIn-π' i))

    ih : tabulate (f Fun.∘ π Fun.∘ suc) Perm.↭ tabulate (f Fun.∘ punchIn k)
    ih = subst (λ xs → xs Perm.↭ tabulate (f Fun.∘ punchIn k))
               (sym (tabulate-cong pointwise-eq))
               (tabulate-bij-↭ (f Fun.∘ punchIn k) π' π'⁻¹ π'-left π'-rght)

tabulate-bij-↭-via-eq
  : (f : Fin n → A) (π : Fin m → Fin n) (π⁻¹ : Fin n → Fin m)
  → (∀ i → π⁻¹ (π i) ≡ i) → (∀ i → π (π⁻¹ i) ≡ i)
  → tabulate (f Fun.∘ π) Perm.↭ tabulate f
tabulate-bij-↭-via-eq f π π⁻¹ leftInv rightInv
  with refl ← FinPerm.↔⇒≡ (FinPerm.permutation π π⁻¹ rightInv leftInv) =
  tabulate-bij-↭ f π π⁻¹ leftInv rightInv
