{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Linear preservation under hypergraph isomorphism, FULLY CONSTRUCTIVE.
--
-- Theorem: `Linear-resp-iso : H ≅ᴴ K → Linear H → Linear K`.  This is
-- sub-property (a) of the Route 1 discharge strategy for
-- `decode-rel-resp-iso` (see REFACTORING.md § "Route 1") — and it's
-- now in the bank.
--
-- BUILDING BLOCKS — all proven constructively in this file:
--
--   (1) `count-↭` — count is invariant under list permutation
--       (~13 LOC).  Induction on `Perm.↭`'s constructors; the swap
--       case factors via `count-++` + `Nat.+-comm`.
--
--   (2) `count-map-via-bij` — count of v in `map φ xs` equals count of
--       `φ⁻¹ v` in `xs`, when φ is a Fin-bijection (~10 LOC).
--       Induction on `xs` with 4-way case split on `v ≟ φ x | φ⁻¹ v ≟ x`.
--
--   (3) `tabulate-bij-↭` — `tabulate (f ∘ π)` is `↭`-equivalent to
--       `tabulate f` when π is a self-bijection on Fin n
--       (~70 LOC).  Induction on n with bijection deflation through
--       stdlib's `punchIn`/`punchOut`.  Workhorse helper
--       `tabulate-shift-↭` brings any `f k` to the head of
--       `tabulate f` via prep + swap.
--
--   (4) `bij-fin-ℕ-≡` — cardinality equality m ≡ n from a
--       Fin-bijection (~10 LOC).  Via `injective⇒≤` in both
--       directions + `Nat.≤-antisym`.
--
--   (5) `tabulate-bij-↭-via-eq` — (3) extended to bijections between
--       different Fin types, using (4)'s equality to bridge (~3 LOC).
--
--   (6) `concat-↭` — `concat` preserves `↭` (~10 LOC).  Induction on
--       the ↭ constructor; the swap case uses `++-comm` and
--       `++-assoc`.
--
-- THE MAIN THEOREM (~80 LOC):
--
--   `Linear-resp-iso` composes the helpers.  For each v : Fin K.nV,
--   it shows `count v (producedList K) ≡ count (φ⁻¹ v) (producedList H)`
--   (and similarly for `consumedList`) by chaining through the iso's
--   `φ-dom`/`φ-cod`/`ψ-rght`/`ψ-eout`/`ψ-ein` fields with `tabulate-cong`,
--   `map-tabulate`, `concat-map`, and the (1)–(6) helpers.  Linear K
--   then follows by applying Linear H at φ⁻¹ v.
--
-- All `--safe`-clean.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.LinearityIso (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
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
-- Helper 1 (CONSTRUCTIVE): count is permutation-invariant.

-- Helper for the swap case: count of a 2-element list is independent
-- of element order.  Proven via count-++ (splitting the 2-list) and
-- Nat.+-comm.
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
-- Helper 2 (CONSTRUCTIVE): count under bijection-map.

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
-- Helper 3 (CONSTRUCTIVE): `tabulate (f ∘ π)` is a permutation of
-- `tabulate f` when π is a Fin-bijection.  Discharged below.

-- Sub-helper: bring `f k` to the head of `tabulate f` via `punchIn`.
-- This is the workhorse — `Perm.shift` from stdlib generalised
-- to tabulate.
open import Data.Fin using (punchIn; punchOut)
open import Data.Fin.Properties
  using (punchInᵢ≢i; punchOut-punchIn; punchIn-punchOut; punchOut-cong)
open import Relation.Binary.PropositionalEquality
  using () renaming (subst to ≡-subst)

private
  -- `tabulate f` can be reordered to bring `f k` to the head, with
  -- the remaining (n) elements being `f` at the indices `Fin (suc n) \ {k}`
  -- (via `punchIn k : Fin n → Fin (suc n)`).
  tabulate-shift-↭
    : ∀ {n} {A : Set} (f : Fin (suc n) → A) (k : Fin (suc n))
    → tabulate f Perm.↭ f k ∷ tabulate (f Fun.∘ punchIn k)
  tabulate-shift-↭ f zero            = Perm.refl
  tabulate-shift-↭ {n = suc n'} f (suc k) =
    -- tabulate f = f zero ∷ tabulate (f ∘ suc)
    --   ↭ f zero ∷ f (suc k) ∷ tabulate (f ∘ suc ∘ punchIn k)  [prep + IH]
    --   ↭ f (suc k) ∷ f zero ∷ tabulate (f ∘ suc ∘ punchIn k)  [swap]
    -- and the RHS equals f (suc k) ∷ tabulate (f ∘ punchIn (suc k))
    -- definitionally (by punchIn's defn).
    Perm.trans
      (Perm.prep (f zero) (tabulate-shift-↭ (f Fun.∘ suc) k))
      (Perm.swap (f zero) (f (suc k)) Perm.refl)

-- The main lemma.  Proof by induction on `n`.  In the inductive step,
-- we use `tabulate-shift-↭` to bring `f (π zero)` to the head of the
-- RHS, then apply the IH to a deflated bijection on `Fin n`.

tabulate-bij-↭
  : ∀ {n} {A : Set} (f : Fin n → A)
      (π : Fin n → Fin n) (π⁻¹ : Fin n → Fin n)
  → (∀ i → π⁻¹ (π i) ≡ i) → (∀ i → π (π⁻¹ i) ≡ i)
  → tabulate (f Fun.∘ π) Perm.↭ tabulate f
tabulate-bij-↭ {n = zero}    f π π⁻¹ _      _       = Perm.refl
tabulate-bij-↭ {n = suc n'}  f π π⁻¹ leftInv rightInv =
  -- LHS: tabulate (f ∘ π) = f (π zero) ∷ tabulate (f ∘ π ∘ suc)  [defn]
  -- RHS bridge (tabulate-shift-↭):
  --   tabulate f ↭ f (π zero) ∷ tabulate (f ∘ punchIn (π zero))
  --
  -- After matching heads via Perm.prep, reduce to showing:
  --   tabulate (f ∘ π ∘ suc) ↭ tabulate (f ∘ punchIn (π zero))
  --
  -- Both sides are tabulates over Fin n'.  We apply the IH at
  -- (f ∘ punchIn (π zero), π', π'⁻¹), where π' is the bijection
  -- on Fin n' obtained by deflating π through punchOut.  The
  -- pointwise equation (f ∘ π ∘ suc) i ≡ (f ∘ punchIn (π zero)) (π' i)
  -- holds by construction.
  Perm.trans lhs-rewrite
    (Perm.trans (Perm.prep (f (π zero)) ih) (Perm.↭-sym shift))
  where
    k = π zero

    -- π is injective (from leftInv).
    π-inj : ∀ {i j} → π i ≡ π j → i ≡ j
    π-inj {i} {j} eq =
      trans (sym (leftInv i)) (trans (cong π⁻¹ eq) (leftInv j))

    -- For each `i : Fin n'`, k ≠ π (suc i) (by injectivity of π).
    -- Direction matches `punchOut`/`punchIn-punchOut`'s expected
    -- `i ≢ j` argument (where i = k, j = π (suc i)).
    π-suc-≢-k : ∀ (i : Fin n') → k ≢ π (suc i)
    π-suc-≢-k i eq with π-inj (sym eq)
    ... | ()

    -- The deflated bijection π' : Fin n' → Fin n'.
    π' : Fin n' → Fin n'
    π' i = punchOut (π-suc-≢-k i)

    -- π'⁻¹ is built similarly: take π⁻¹ at punchIn k j, and check it
    -- isn't zero (so we can punchOut).
    -- Direction matches `punchOut`'s `i ≢ j` argument (i = zero,
    -- j = π⁻¹ (punchIn k j)).
    zero-≢-π⁻¹-pIn : ∀ (j : Fin n') → zero ≢ π⁻¹ (punchIn k j)
    zero-≢-π⁻¹-pIn j eq =
      punchInᵢ≢i k j
        (trans (sym (rightInv (punchIn k j))) (cong π (sym eq)))

    π'⁻¹ : Fin n' → Fin n'
    π'⁻¹ j = punchOut (zero-≢-π⁻¹-pIn j)

    -- Bijection laws for (π', π'⁻¹).  Each direction unfolds the
    -- punchOut definitions and chains through punchIn-punchOut (or
    -- punchOut-punchIn) plus leftInv/rightInv on the inner π/π⁻¹
    -- application.

    -- The pointwise equation we need both for π'-rght and for the IH:
    -- punchIn k (π' i) ≡ π (suc i).  Direct from punchIn-punchOut.
    punchIn-π' : ∀ (i : Fin n') → punchIn k (π' i) ≡ π (suc i)
    punchIn-π' i = punchIn-punchOut (π-suc-≢-k i)

    -- Symmetric pointwise equation for π'⁻¹:
    -- punchIn zero (π'⁻¹ j) ≡ π⁻¹ (punchIn k j).
    -- Direct from punchIn-punchOut at i = zero.
    punchIn-π'⁻¹ : ∀ (j : Fin n')
                 → punchIn zero (π'⁻¹ j) ≡ π⁻¹ (punchIn k j)
    punchIn-π'⁻¹ j = punchIn-punchOut (zero-≢-π⁻¹-pIn j)

    -- π'-left.  Chain:
    --   π'⁻¹ (π' i) ≡ punchOut {0} {π⁻¹ (punchIn k (π' i))} _
    --              ≡ punchOut {0} {π⁻¹ (π (suc i))} _          [punchIn-π']
    --              ≡ punchOut {0} {suc i} _                    [leftInv]
    --              ≡ i                                          [definitional]
    -- We use `punchOut-cong zero` to bridge the inner-equality steps.
    π'-left : ∀ i → π'⁻¹ (π' i) ≡ i
    π'-left i = punchOut-cong {n = n'} zero {i≢k = λ ()}
      (trans (cong π⁻¹ (punchIn-π' i)) (leftInv (suc i)))

    -- π'-rght.  Chain:
    --   π' (π'⁻¹ j) ≡ punchOut {k} {π (suc (π'⁻¹ j))} _
    --              ≡ punchOut {k} {π (punchIn zero (π'⁻¹ j))} _   [suc = punchIn zero]
    --              ≡ punchOut {k} {π (π⁻¹ (punchIn k j))} _       [punchIn-π'⁻¹]
    --              ≡ punchOut {k} {punchIn k j} _                 [rightInv]
    --              ≡ j                                            [punchOut-punchIn]
    -- punchIn zero (π'⁻¹ j) ≡ suc (π'⁻¹ j) is definitional.
    π'-rght : ∀ j → π' (π'⁻¹ j) ≡ j
    π'-rght j =
      trans (punchOut-cong k
              {i≢k = punchInᵢ≢i k j Fun.∘ sym}
              (trans (cong π (punchIn-π'⁻¹ j))
                     (rightInv (punchIn k j))))
            (punchOut-punchIn k)

    -- The pointwise equation: (f ∘ π ∘ suc) i ≡ (f ∘ punchIn k) (π' i).
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

    -- The shift bridge from `tabulate f` to `f k ∷ tabulate (f ∘ punchIn k)`.
    shift : tabulate f Perm.↭ f k ∷ tabulate (f Fun.∘ punchIn k)
    shift = tabulate-shift-↭ f k

    -- The LHS rewrite step: tabulate (f ∘ π) ≡ f (π zero) ∷ tabulate (f ∘ π ∘ suc)
    -- is definitional, so Perm.refl.
    lhs-rewrite : tabulate (f Fun.∘ π) Perm.↭ tabulate (f Fun.∘ π)
    lhs-rewrite = Perm.refl

--------------------------------------------------------------------------------
-- Helper 4: cardinality equality from a Fin-bijection.  Given
-- (π : Fin m → Fin n, π⁻¹ : Fin n → Fin m) with inverse laws, we
-- have m ≡ n as natural numbers (via injective⇒≤ in both directions).

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

-- Helper 5: tabulate-bij-↭ generalized to bijections between different
-- Fin types (using the cardinality equality to bridge).

tabulate-bij-↭-via-eq
  : ∀ {m n} {A : Set} (m≡n : m ≡ n)
      (f : Fin n → A)
      (π : Fin m → Fin n) (π⁻¹ : Fin n → Fin m)
  → (∀ i → π⁻¹ (π i) ≡ i) → (∀ i → π (π⁻¹ i) ≡ i)
  → tabulate (f Fun.∘ π) Perm.↭ tabulate f
tabulate-bij-↭-via-eq refl f π π⁻¹ leftInv rightInv =
  tabulate-bij-↭ f π π⁻¹ leftInv rightInv

-- Helper 6: concat preserves `↭` (lifts list-of-list permutation to
-- list permutation).  Standard fact, not in stdlib.

concat-↭
  : ∀ {A : Set} {L₁ L₂ : List (List A)}
  → L₁ Perm.↭ L₂
  → concat L₁ Perm.↭ concat L₂
concat-↭ Perm.refl       = Perm.refl
concat-↭ (Perm.prep x p) = PermProp.++⁺ˡ x (concat-↭ p)
concat-↭ (Perm.swap {xs} {ys} x y p) =
  -- concat (x ∷ y ∷ xs) = x ++ (y ++ concat xs)
  -- concat (y ∷ x ∷ ys) = y ++ (x ++ concat ys)
  -- Bridge via ++-assoc and ++-comm.
  Perm.trans
    (Perm.↭-reflexive (sym (++-assoc x y (concat xs))))
    (Perm.trans
      (PermProp.++⁺ʳ (concat xs) (PermProp.++-comm x y))
      (Perm.trans
        (Perm.↭-reflexive (++-assoc y x (concat xs)))
        (PermProp.++⁺ˡ y (PermProp.++⁺ˡ x (concat-↭ p)))))
concat-↭ (Perm.trans p q) = Perm.trans (concat-↭ p) (concat-↭ q)

--------------------------------------------------------------------------------
-- Composition: the main `Linear-resp-iso` theorem.
--
-- Given `iso : H ≅ᴴ K` and `Linear H`, derive `Linear K`.  The proof
-- structure is documented below.  The mechanical assembly relies on:
--
--   * Helper 1 (count-↭) — to absorb the ψ-induced reindexing of edge
--     lists into a count-equality.
--   * Helper 2 (count-map-via-bij) — to push count through `map φ`
--     into a count at `φ⁻¹ v` on the original list.
--   * Helper 3 (tabulate-bij-↭, postulated) — to derive the
--     `_↭_` witness needed for count-↭.
--   * Iso fields `φ-dom`, `φ-cod`, `ψ-ein`, `ψ-eout`, `ψ-rght` to
--     rewrite K's lists in terms of H's.
--
-- Once Helper 3 is closed, this proof becomes a ~50 LOC mechanical
-- chain.

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

    -- Cardinality equality from the iso's edge bijection.
    nE-eq : H.nE ≡ K.nE
    nE-eq = bij-fin-ℕ-≡ ψ ψ⁻¹ ψ-left ψ-rght

    -- For each i : Fin K.nE, K.eout i ≡ map φ (H.eout (ψ⁻¹ i)).
    -- (Combines ψ-rght and ψ-eout.)
    K-eout-via-H : ∀ (i : Fin K.nE) → K.eout i ≡ map φ (H.eout (ψ⁻¹ i))
    K-eout-via-H i = trans (cong K.eout (sym (ψ-rght i))) (ψ-eout (ψ⁻¹ i))

    K-ein-via-H : ∀ (i : Fin K.nE) → K.ein i ≡ map φ (H.ein (ψ⁻¹ i))
    K-ein-via-H i = trans (cong K.ein (sym (ψ-rght i))) (ψ-ein (ψ⁻¹ i))

    -- Concat-tabulate-K reduces to map φ of concat-tabulate of H ∘ ψ⁻¹.
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

    -- tabulate-bij-↭-via-eq applied at H.eout, ψ⁻¹, ψ gives:
    --   tabulate (H.eout ∘ ψ⁻¹) ↭ tabulate H.eout
    tab-H-eout-↭ : tabulate (H.eout Fun.∘ ψ⁻¹) Perm.↭ tabulate H.eout
    tab-H-eout-↭ = tabulate-bij-↭-via-eq (sym nE-eq) H.eout ψ⁻¹ ψ ψ-rght ψ-left

    tab-H-ein-↭ : tabulate (H.ein Fun.∘ ψ⁻¹) Perm.↭ tabulate H.ein
    tab-H-ein-↭ = tabulate-bij-↭-via-eq (sym nE-eq) H.ein ψ⁻¹ ψ ψ-rght ψ-left

    -- The key count equation for the eout side.
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

    -- The dom and cod sides are easier: K.dom ≡ map φ H.dom directly
    -- from the iso, plus count-map-via-bij.
    count-K-dom : ∀ (v : Fin K.nV) → count v K.dom ≡ count (φ⁻¹ v) H.dom
    count-K-dom v =
      trans (cong (count v) φ-dom)
            (count-map-via-bij φ φ⁻¹ φ-left φ-rght v H.dom)

    count-K-cod : ∀ (v : Fin K.nV) → count v K.cod ≡ count (φ⁻¹ v) H.cod
    count-K-cod v =
      trans (cong (count v) φ-cod)
            (count-map-via-bij φ φ⁻¹ φ-left φ-rght v H.cod)

    -- Combined: count over the full producedList/consumedList.
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

    -- Linear K's balance and boundedness follow by applying Linear H
    -- at the bijection image φ⁻¹ v.
    K-bal : ∀ (v : Fin K.nV) → count v (producedList K) ≡ count v (consumedList K)
    K-bal v = trans (count-prod-K v)
                (trans (H-bal (φ⁻¹ v))
                       (sym (count-cons-K v)))

    K-bnd : ∀ (v : Fin K.nV) → count v (producedList K) Nat.≤ 1
    K-bnd v = subst (Nat._≤ 1) (sym (count-prod-K v)) (H-bnd (φ⁻¹ v))
