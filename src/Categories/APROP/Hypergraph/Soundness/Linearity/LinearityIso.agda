{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Fin-bijection / `tabulate`-reindexing leaf, used by `IsoInvarianceWiring` to
-- transport cardinalities and `tabulate`-built lists across a Fin-bijection
-- (`bij-fin-ℕ-≡`, `tabulate-bij-↭-via-eq`).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Linearity.LinearityIso (sig : APROPSignature) where

open APROP sig

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (_∷_; tabulate)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Nat using (zero; suc)
import Function as Fun
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)

--------------------------------------------------------------------------------
-- `tabulate (f ∘ π)` is a permutation of `tabulate f` when π is a
-- Fin-bijection.

open import Data.Fin using (punchIn; punchOut)
open import Data.Fin.Properties
  using (punchInᵢ≢i; punchOut-punchIn; punchIn-punchOut; punchOut-cong)

private
  -- `tabulate f` can be reordered to bring `f k` to the head, with
  -- the remaining elements being `f` at the indices `Fin (suc n) \ {k}`
  -- (via `punchIn k : Fin n → Fin (suc n)`).
  tabulate-shift-↭
    : ∀ {n} {A : Set} (f : Fin (suc n) → A) (k : Fin (suc n))
    → tabulate f Perm.↭ f k ∷ tabulate (f Fun.∘ punchIn k)
  tabulate-shift-↭ f zero            = Perm.refl
  tabulate-shift-↭ {n = suc n'} f (suc k) =
    Perm.trans
      (Perm.prep (f zero) (tabulate-shift-↭ (f Fun.∘ suc) k))
      (Perm.swap (f zero) (f (suc k)) Perm.refl)

-- Induction on `n`.  In the inductive step, `tabulate-shift-↭` brings
-- `f (π zero)` to the head of the RHS, then the IH is applied to a
-- bijection on `Fin n` obtained by deflating π through punchOut.

tabulate-bij-↭
  : ∀ {n} {A : Set} (f : Fin n → A)
      (π : Fin n → Fin n) (π⁻¹ : Fin n → Fin n)
  → (∀ i → π⁻¹ (π i) ≡ i) → (∀ i → π (π⁻¹ i) ≡ i)
  → tabulate (f Fun.∘ π) Perm.↭ tabulate f
tabulate-bij-↭ {n = zero}    f π π⁻¹ _      _       = Perm.refl
tabulate-bij-↭ {n = suc n'}  f π π⁻¹ leftInv rightInv =
  Perm.trans (Perm.prep (f (π zero)) ih) (Perm.↭-sym shift)
  where
    k = π zero

    π-inj : ∀ {i j} → π i ≡ π j → i ≡ j
    π-inj {i} {j} eq = trans (sym (leftInv i)) (trans (cong π⁻¹ eq) (leftInv j))

    π-suc-≢-k : ∀ (i : Fin n') → k ≢ π (suc i)
    π-suc-≢-k i eq with π-inj (sym eq)
    ... | ()

    -- The deflated bijection π' : Fin n' → Fin n'.
    π' : Fin n' → Fin n'
    π' i = punchOut (π-suc-≢-k i)

    zero-≢-π⁻¹-pIn : ∀ (j : Fin n') → zero ≢ π⁻¹ (punchIn k j)
    zero-≢-π⁻¹-pIn j eq =
      punchInᵢ≢i k j
        (trans (sym (rightInv (punchIn k j))) (cong π (sym eq)))

    π'⁻¹ : Fin n' → Fin n'
    π'⁻¹ j = punchOut (zero-≢-π⁻¹-pIn j)

    -- punchIn k (π' i) ≡ π (suc i), and the symmetric equation for π'⁻¹.
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

    -- The IH applied at (f ∘ punchIn k, π', π'⁻¹), rewritten via
    -- pointwise-eq to match the LHS shape `tabulate (f ∘ π ∘ suc)`.
    open import Data.List.Properties using (tabulate-cong)
    ih : tabulate (f Fun.∘ π Fun.∘ suc) Perm.↭ tabulate (f Fun.∘ punchIn k)
    ih = subst (λ xs → xs Perm.↭ tabulate (f Fun.∘ punchIn k))
               (sym (tabulate-cong pointwise-eq))
               (tabulate-bij-↭ (f Fun.∘ punchIn k) π' π'⁻¹ π'-left π'-rght)

    shift : tabulate f Perm.↭ f k ∷ tabulate (f Fun.∘ punchIn k)
    shift = tabulate-shift-↭ f k

--------------------------------------------------------------------------------
-- Cardinality equality m ≡ n from a Fin-bijection.

open import Data.Fin.Properties using (injective⇒≤)
open import Function.Definitions using (Injective)
import Data.Nat.Properties as NatProp

bij-fin-ℕ-≡
  : ∀ {m n} (π : Fin m → Fin n) (π⁻¹ : Fin n → Fin m)
  → (∀ i → π⁻¹ (π i) ≡ i) → (∀ i → π (π⁻¹ i) ≡ i)
  → m ≡ n
bij-fin-ℕ-≡ π π⁻¹ leftInv rightInv =
  NatProp.≤-antisym (injective⇒≤ π-inj) (injective⇒≤ π⁻¹-inj)
  where
    π-inj : Injective _≡_ _≡_ π
    π-inj {i} {j} eq = trans (sym (leftInv i)) (trans (cong π⁻¹ eq) (leftInv j))

    π⁻¹-inj : Injective _≡_ _≡_ π⁻¹
    π⁻¹-inj {i} {j} eq = trans (sym (rightInv i)) (trans (cong π eq) (rightInv j))

-- tabulate-bij-↭ generalized to bijections between different Fin types.

tabulate-bij-↭-via-eq
  : ∀ {m n} {A : Set} (m≡n : m ≡ n)
      (f : Fin n → A)
      (π : Fin m → Fin n) (π⁻¹ : Fin n → Fin m)
  → (∀ i → π⁻¹ (π i) ≡ i) → (∀ i → π (π⁻¹ i) ≡ i)
  → tabulate (f Fun.∘ π) Perm.↭ tabulate f
tabulate-bij-↭-via-eq refl f π π⁻¹ leftInv rightInv = tabulate-bij-↭ f π π⁻¹ leftInv rightInv
