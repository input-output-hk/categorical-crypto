{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Pruning helpers for a canonical `hCompose` (TODO.org Option A).
--
-- Given `xs : List (Fin n)` (typically `K.dom` of the right operand of a
-- cospan composition), we want to identify the Fin values NOT in `xs`.
-- After composition, the positions named in `xs` have been "glued" to the
-- left operand's `cod`, so they become unreferenced and can be pruned.
--
-- This module provides:
--   * `nonMem xs`     — the list of Fin values not in `xs`.
--   * `count-non xs`  — its length (the count of "survivors").
--   * `classify xs v` — cases `v : Fin n` as either a position in `xs`
--                       or a position in `nonMem xs`.
--   * `remap xs f`    — combinator that routes members of `xs` to an
--                       arbitrary target space via `f`, and non-members
--                       to the fresh pruned space of size `count-non xs`.
--
-- The canonical `hCompose` will have vertex count
--   `G.nV + count-non K.dom`
-- and a `remap` that sends each K-vertex to either:
--   * a G-side position (if the vertex was in `K.dom`), via
--     `f i = G.cod[i]` composed with `inject+`, or
--   * a fresh pruned-K-side position (via an index lookup in `nonMem K.dom`).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Prune where

open import Data.Fin using (Fin; inject+; raise; splitAt)
open import Data.Fin.Properties using (_≟_; splitAt-inject+; splitAt-raise)
open import Data.List using (List; length; filter; allFin; lookup)
open import Data.List.Relation.Unary.Any using (index)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (¬?; yes; no)

--------------------------------------------------------------------------------
-- Non-members of a Fin list.

module _ {n : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-filter⁺; ∈-allFin)

  -- The Fin values not present in `xs`.
  nonMem : List (Fin n) → List (Fin n)
  nonMem xs = filter (λ v → ¬? (v ∈? xs)) (allFin n)

  -- Count of Fin values not in `xs`.
  count-non : List (Fin n) → ℕ
  count-non xs = length (nonMem xs)

  -- Classify `v : Fin n` as either a member of `xs` (paired with its index
  -- into `xs`) or a non-member (paired with its index into `nonMem xs`).
  classify : (xs : List (Fin n)) (v : Fin n) → Fin (length xs) ⊎ Fin (count-non xs)
  classify xs v with v ∈? xs
  ... | yes v∈xs = inj₁ (index v∈xs)
  ... | no  v∉xs =
    inj₂ (index (∈-filter⁺ (λ u → ¬? (u ∈? xs)) (∈-allFin v) v∉xs))

  -- Inversion: when classify returns `inj₁ i`, the member slot `i` in
  -- `xs` looks back to `v`.
  classify-inj₁-lookup : (xs : List (Fin n)) (v : Fin n) (i : Fin (length xs))
                       → classify xs v ≡ inj₁ i
                       → lookup xs i ≡ v
  classify-inj₁-lookup xs v i eq with v ∈? xs
  classify-inj₁-lookup xs v .(index v∈xs) refl
    | yes v∈xs = sym (lookup-index v∈xs)

  -- Inversion: when classify returns `inj₂ j`, the non-member slot `j` in
  -- `nonMem xs` looks back to `v`. This is the key lemma used by the
  -- pruned `hCompose` to recover vertex labels from the pruned space.
  classify-inj₂-lookup : (xs : List (Fin n)) (v : Fin n) (j : Fin (count-non xs))
                       → classify xs v ≡ inj₂ j
                       → lookup (nonMem xs) j ≡ v
  classify-inj₂-lookup xs v j eq with v ∈? xs
  classify-inj₂-lookup xs v .(index (∈-filter⁺ _ (∈-allFin v) v∉xs)) refl
    | no v∉xs = sym (lookup-index (∈-filter⁺ _ (∈-allFin v) v∉xs))

--------------------------------------------------------------------------------
-- Remap combinator.
--
-- Given xs ⊂ Fin n and a target map f : Fin (length xs) → Fin m for
-- members of xs, produces Fin n → Fin (m + count-non xs) by routing
-- members to `inject+ (count-non xs) (f i)` and non-members to
-- `raise m j` where j is the non-member's index in `nonMem xs`.

module _ {n m : ℕ} where
  remap : (xs : List (Fin n)) → (Fin (length xs) → Fin m)
        → Fin n → Fin (m + count-non xs)
  remap xs f v = [ (λ i → inject+ (count-non xs) (f i))
                 , (λ j → raise m j)
                 ]′ (classify xs v)

  -- Reduction of `remap` in the `inj₁` (member) case.
  remap-inj₁ : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (v : Fin n) (i : Fin (length xs))
             → classify xs v ≡ inj₁ i
             → remap xs f v ≡ inject+ (count-non xs) (f i)
  remap-inj₁ xs f v i eq with classify xs v
  remap-inj₁ xs f v i refl | inj₁ .i = refl

  -- Reduction of `remap` in the `inj₂` (non-member) case.
  remap-inj₂ : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (v : Fin n) (j : Fin (count-non xs))
             → classify xs v ≡ inj₂ j
             → remap xs f v ≡ raise m j
  remap-inj₂ xs f v j eq with classify xs v
  remap-inj₂ xs f v j refl | inj₂ .j = refl

--------------------------------------------------------------------------------
-- Label preservation.
--
-- The key lemma that makes the pruned `hCompose` work. Given:
--   * xs : List (Fin n)           — positions to prune (e.g., K.dom)
--   * f  : Fin (length xs) → Fin m — target map for member positions
--   * λK : Fin n → X              — labels for the source (K-side)
--   * λG : Fin m → X              — labels for the target (G-side)
--   * pointwise boundary agreement: ∀ i → λK (xs[i]) ≡ λG (f i)
--
-- The "pruned composite labeling" is
--   vlab-c : Fin (m + count-non xs) → X
--   vlab-c = [ λG , λ-non ]′ ∘ splitAt m
-- where λ-non j = λK (lookup (nonMem xs) j) reads back through the pruned
-- index. Then `vlab-c (remap xs f v) ≡ λK v` for every v : Fin n — the
-- pruning preserves K-side labels.

module _ {a} {X : Set a} {n m : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-filter⁺; ∈-allFin)

  remap-vlab : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (λK : Fin n → X) (λG : Fin m → X)
               (bdy : ∀ i → λK (lookup xs i) ≡ λG (f i))
               (v : Fin n)
             → [ λG , (λ j → λK (lookup (nonMem xs) j)) ]′
                  (splitAt m (remap xs f v))
             ≡ λK v
  remap-vlab xs f λK λG bdy v with v ∈? xs
  ... | yes v∈xs =
    -- classify xs v reduces to inj₁ (index v∈xs), so
    -- remap xs f v = inject+ (count-non xs) (f (index v∈xs)).
    trans
      (cong [ λG , (λ k → λK (lookup (nonMem xs) k)) ]′
        (splitAt-inject+ m (count-non xs) (f (index v∈xs))))
      (trans (sym (bdy (index v∈xs)))
             (cong λK (sym (lookup-index v∈xs))))
  ... | no v∉xs =
    -- classify xs v reduces to inj₂ (index v∈nonMem), so
    -- remap xs f v = raise m (index v∈nonMem).
    let v∈nonMem = ∈-filter⁺ (λ u → ¬? (u ∈? xs)) (∈-allFin v) v∉xs in
    trans
      (cong [ λG , (λ k → λK (lookup (nonMem xs) k)) ]′
        (splitAt-raise m (count-non xs) (index v∈nonMem)))
      (cong λK (sym (lookup-index v∈nonMem)))
