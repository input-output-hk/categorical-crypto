{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Linear preservation under hypergraph isomorphism.
--
-- Theorem: `Linear-resp-iso : H ≅ᴴ K → Linear H → Linear K`, via count
-- invariance under permutation/bijection-map and `tabulate`-reindexing.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.LinearityIso (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Soundness.Linearity sig
  using (Linear; count; count-++; producedList; consumedList)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List as List using (List; []; _∷_; _++_; map; tabulate; concat)
open import Data.List.Properties using (++-assoc)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat as Nat using ()
import Data.Nat.Properties as Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Function as Fun
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)

--------------------------------------------------------------------------------
-- count is permutation-invariant.

private
  count-swap-2 : ∀ {n} (v x y : Fin n)
               → count v (x ∷ y ∷ []) ≡ count v (y ∷ x ∷ [])
  count-swap-2 v x y =
    trans (count-++ v (x ∷ []) (y ∷ []))
      (trans (Nat.+-comm (count v (x ∷ [])) (count v (y ∷ [])))
             (sym (count-++ v (y ∷ []) (x ∷ []))))

count-↭ : ∀ {n} (v : Fin n) {xs ys : List (Fin n)}
        → xs Perm.↭ ys
        → count v xs ≡ count v ys
count-↭ v Perm.refl       = refl
count-↭ v (Perm.prep x p) with v ≟ x
... | yes _ = cong suc (count-↭ v p)
... | no  _ = count-↭ v p
count-↭ v (Perm.swap {xs} {ys} x y p) =
  trans (count-++ v (x ∷ y ∷ []) xs)
    (trans (cong₂ _+_ (count-swap-2 v x y) (count-↭ v p))
           (sym (count-++ v (y ∷ x ∷ []) ys)))
count-↭ v (Perm.trans p q) = trans (count-↭ v p) (count-↭ v q)

--------------------------------------------------------------------------------
-- count under bijection-map.

count-map-via-bij
  : ∀ {n m} (φ : Fin n → Fin m) (φ⁻¹ : Fin m → Fin n)
  → (φ⁻¹φ : ∀ i → φ⁻¹ (φ i) ≡ i)
  → (φφ⁻¹ : ∀ j → φ (φ⁻¹ j) ≡ j)
  → ∀ (v : Fin m) (xs : List (Fin n))
  → count v (map φ xs) ≡ count (φ⁻¹ v) xs
count-map-via-bij φ φ⁻¹ φ⁻¹φ φφ⁻¹ v []       = refl
count-map-via-bij φ φ⁻¹ φ⁻¹φ φφ⁻¹ v (x ∷ xs)
    with v ≟ φ x | φ⁻¹ v ≟ x
... | yes _ | yes _ = cong suc (count-map-via-bij φ φ⁻¹ φ⁻¹φ φφ⁻¹ v xs)
... | yes p | no  q = ⊥-elim (q (trans (cong φ⁻¹ p) (φ⁻¹φ x)))
... | no  q | yes p = ⊥-elim (q (trans (sym (φφ⁻¹ v)) (cong φ p)))
... | no  _ | no  _ = count-map-via-bij φ φ⁻¹ φ⁻¹φ φφ⁻¹ v xs

--------------------------------------------------------------------------------
-- `tabulate (f ∘ π)` is a permutation of `tabulate f` when π is a
-- Fin-bijection.

open import Data.Fin using (punchIn; punchOut)
open import Data.Fin.Properties
  using (punchInᵢ≢i; punchOut-punchIn; punchIn-punchOut; punchOut-cong)
open import Relation.Binary.PropositionalEquality
  using () renaming (subst to ≡-subst)

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
  Perm.trans lhs-rewrite
    (Perm.trans (Perm.prep (f (π zero)) ih) (Perm.↭-sym shift))
  where
    k = π zero

    π-inj : ∀ {i j} → π i ≡ π j → i ≡ j
    π-inj {i} {j} eq =
      trans (sym (leftInv i)) (trans (cong π⁻¹ eq) (leftInv j))

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

    punchIn-π'⁻¹ : ∀ (j : Fin n')
                 → punchIn zero (π'⁻¹ j) ≡ π⁻¹ (punchIn k j)
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

    pointwise-eq : ∀ (i : Fin n')
                 → f (π (suc i)) ≡ f (punchIn k (π' i))
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

    lhs-rewrite : tabulate (f Fun.∘ π) Perm.↭ tabulate (f Fun.∘ π)
    lhs-rewrite = Perm.refl

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
    π-inj {i} {j} eq =
      trans (sym (leftInv i)) (trans (cong π⁻¹ eq) (leftInv j))

    π⁻¹-inj : Injective _≡_ _≡_ π⁻¹
    π⁻¹-inj {i} {j} eq =
      trans (sym (rightInv i)) (trans (cong π eq) (rightInv j))

-- tabulate-bij-↭ generalized to bijections between different Fin types.

tabulate-bij-↭-via-eq
  : ∀ {m n} {A : Set} (m≡n : m ≡ n)
      (f : Fin n → A)
      (π : Fin m → Fin n) (π⁻¹ : Fin n → Fin m)
  → (∀ i → π⁻¹ (π i) ≡ i) → (∀ i → π (π⁻¹ i) ≡ i)
  → tabulate (f Fun.∘ π) Perm.↭ tabulate f
tabulate-bij-↭-via-eq refl f π π⁻¹ leftInv rightInv =
  tabulate-bij-↭ f π π⁻¹ leftInv rightInv

-- concat preserves `↭` (not in stdlib).

concat-↭
  : ∀ {A : Set} {L₁ L₂ : List (List A)}
  → L₁ Perm.↭ L₂
  → concat L₁ Perm.↭ concat L₂
concat-↭ Perm.refl       = Perm.refl
concat-↭ (Perm.prep x p) = PermProp.++⁺ˡ x (concat-↭ p)
concat-↭ (Perm.swap {xs} {ys} x y p) =
  Perm.trans
    (Perm.↭-reflexive (sym (++-assoc x y (concat xs))))
    (Perm.trans
      (PermProp.++⁺ʳ (concat xs) (PermProp.++-comm x y))
      (Perm.trans
        (Perm.↭-reflexive (++-assoc y x (concat xs)))
        (PermProp.++⁺ˡ y (PermProp.++⁺ˡ x (concat-↭ p)))))
concat-↭ (Perm.trans p q) = Perm.trans (concat-↭ p) (concat-↭ q)

--------------------------------------------------------------------------------
-- The main `Linear-resp-iso` theorem: given `iso : H ≅ᴴ K` and
-- `Linear H`, derive `Linear K`.

open import Data.List.Properties using (map-tabulate; concat-map; tabulate-cong)

Linear-resp-iso
  : ∀ {H K : Hypergraph FlatGen}
  → H ≅ᴴ K → Linear H → Linear K
Linear-resp-iso {H} {K} iso linH = K-bal , K-bnd
  where
    module H = Hypergraph H
    module K = Hypergraph K
    open _≅ᴴ_ iso

    H-bal = proj₁ linH
    H-bnd = proj₂ linH

    nE-eq : H.nE ≡ K.nE
    nE-eq = bij-fin-ℕ-≡ ψ ψ⁻¹ ψ-left ψ-rght

    K-eout-via-H : ∀ (i : Fin K.nE) → K.eout i ≡ map φ (H.eout (ψ⁻¹ i))
    K-eout-via-H i = trans (cong K.eout (sym (ψ-rght i))) (ψ-eout (ψ⁻¹ i))

    K-ein-via-H : ∀ (i : Fin K.nE) → K.ein i ≡ map φ (H.ein (ψ⁻¹ i))
    K-ein-via-H i = trans (cong K.ein (sym (ψ-rght i))) (ψ-ein (ψ⁻¹ i))

    concat-tab-K-eout-eq
      : concat (tabulate K.eout)
      ≡ map φ (concat (tabulate (H.eout Fun.∘ ψ⁻¹)))
    concat-tab-K-eout-eq =
      trans (cong concat (tabulate-cong K-eout-via-H))
        (trans (cong concat (sym (map-tabulate (H.eout Fun.∘ ψ⁻¹) (map φ))))
               (concat-map (tabulate (H.eout Fun.∘ ψ⁻¹))))

    concat-tab-K-ein-eq
      : concat (tabulate K.ein)
      ≡ map φ (concat (tabulate (H.ein Fun.∘ ψ⁻¹)))
    concat-tab-K-ein-eq =
      trans (cong concat (tabulate-cong K-ein-via-H))
        (trans (cong concat (sym (map-tabulate (H.ein Fun.∘ ψ⁻¹) (map φ))))
               (concat-map (tabulate (H.ein Fun.∘ ψ⁻¹))))

    tab-H-eout-↭ : tabulate (H.eout Fun.∘ ψ⁻¹) Perm.↭ tabulate H.eout
    tab-H-eout-↭ = tabulate-bij-↭-via-eq (sym nE-eq) H.eout ψ⁻¹ ψ ψ-rght ψ-left

    tab-H-ein-↭ : tabulate (H.ein Fun.∘ ψ⁻¹) Perm.↭ tabulate H.ein
    tab-H-ein-↭ = tabulate-bij-↭-via-eq (sym nE-eq) H.ein ψ⁻¹ ψ ψ-rght ψ-left

    count-prod-K-eout
      : ∀ (v : Fin K.nV)
      → count v (concat (tabulate K.eout))
      ≡ count (φ⁻¹ v) (concat (tabulate H.eout))
    count-prod-K-eout v =
      trans (cong (count v) concat-tab-K-eout-eq)
        (trans (count-map-via-bij φ φ⁻¹ φ-left φ-rght v
                  (concat (tabulate (H.eout Fun.∘ ψ⁻¹))))
               (count-↭ (φ⁻¹ v) (concat-↭ tab-H-eout-↭)))

    count-cons-K-ein
      : ∀ (v : Fin K.nV)
      → count v (concat (tabulate K.ein))
      ≡ count (φ⁻¹ v) (concat (tabulate H.ein))
    count-cons-K-ein v =
      trans (cong (count v) concat-tab-K-ein-eq)
        (trans (count-map-via-bij φ φ⁻¹ φ-left φ-rght v
                  (concat (tabulate (H.ein Fun.∘ ψ⁻¹))))
               (count-↭ (φ⁻¹ v) (concat-↭ tab-H-ein-↭)))

    -- K.dom ≡ map φ H.dom directly from the iso, plus count-map-via-bij.
    count-K-dom : ∀ (v : Fin K.nV) → count v K.dom ≡ count (φ⁻¹ v) H.dom
    count-K-dom v =
      trans (cong (count v) φ-dom)
            (count-map-via-bij φ φ⁻¹ φ-left φ-rght v H.dom)

    count-K-cod : ∀ (v : Fin K.nV) → count v K.cod ≡ count (φ⁻¹ v) H.cod
    count-K-cod v =
      trans (cong (count v) φ-cod)
            (count-map-via-bij φ φ⁻¹ φ-left φ-rght v H.cod)

    count-prod-K
      : ∀ (v : Fin K.nV)
      → count v (producedList K) ≡ count (φ⁻¹ v) (producedList H)
    count-prod-K v =
      trans (count-++ v K.dom (concat (tabulate K.eout)))
        (trans (cong₂ _+_ (count-K-dom v) (count-prod-K-eout v))
               (sym (count-++ (φ⁻¹ v) H.dom (concat (tabulate H.eout)))))

    count-cons-K
      : ∀ (v : Fin K.nV)
      → count v (consumedList K) ≡ count (φ⁻¹ v) (consumedList H)
    count-cons-K v =
      trans (count-++ v K.cod (concat (tabulate K.ein)))
        (trans (cong₂ _+_ (count-K-cod v) (count-cons-K-ein v))
               (sym (count-++ (φ⁻¹ v) H.cod (concat (tabulate H.ein)))))

    -- Linear K follows by applying Linear H at the image φ⁻¹ v.
    K-bal : ∀ (v : Fin K.nV) → count v (producedList K) ≡ count v (consumedList K)
    K-bal v = trans (count-prod-K v)
                (trans (H-bal (φ⁻¹ v))
                       (sym (count-cons-K v)))

    K-bnd : ∀ (v : Fin K.nV) → count v (producedList K) Nat.≤ 1
    K-bnd v = subst (Nat._≤ 1) (sym (count-prod-K v)) (H-bnd (φ⁻¹ v))
