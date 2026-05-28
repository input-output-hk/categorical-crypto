{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Case-on-Y closure for the 4 A-trans-* residuals from
-- `RealFinalResidual` in `Sub/YangBaxterClosure.agda`:
--
--   * `rfr-A-trans-prep-prep`
--   * `rfr-A-trans-prep-swap`
--   * `rfr-A-trans-prep-trans`
--   * `rfr-A-trans-swap`
--
-- ## Target shapes
--
-- All four targets have the same outer cascade structure
--
--   p = trans (prep k a) (trans (swap k k' b) Y)
--     : (k ∷ k'' ∷ rest...) ↭ (k ∷ k'' ∷ rest...)
--
-- with
--   * `a : (k'' ∷ rest...) ↭ (k' ∷ rest)` (different inner shapes
--     across the four targets).
--   * `b : rest ↭ rest'`.
--   * `Y : (k' ∷ k ∷ rest') ↭ (k ∷ k'' ∷ rest...)`.
--   * `uniq` constraining `(k ∷ k'' ∷ rest...)` to be unique.
--   * `total-l p ≡ 0` (normal form).
--   * `self-rec` enabling lex descent.
--
-- ## Strategy: case-split on Y.
--
-- Since `Y` has type `(k' ∷ k ∷ rest') ↭ (k ∷ k'' ∷ rest...)`, the
-- LHS head is `k'` but the RHS head is `k`.  Pattern-matching forces:
--
--   * `Y = refl`:           `k' ≡ k` AND `k ≡ k''` (=second of RHS) → ⊥
--                           via Unique (since `k ≢ k''`).
--   * `Y = prep x Y'`:      `x ≡ k' ≡ k` → contradiction via the inner
--                           `Y' : (k ∷ rest') ↭ (k'' ∷ rest...)`,
--                           using `k ∈ Y'-codomain` ⊥ `k ∉ rest...`
--                           via Unique.
--   * `Y = swap x y Y'`:    `x = k'`, `y = k`.  RHS forces `y = k`,
--                           `x = k''`, so `k' ≡ k''`.  Since `k'` is
--                           not in Unique, this is NOT directly
--                           refuted.  NARROW to residual.
--   * `Y = trans Y₁ Y₂`:    further case-split on `Y₁`:
--       - `Y₁ = refl`:      collapse `trans refl Y₂ ≡ Y₂` and recurse
--                           via `self-rec` on a size-strict subproblem.
--       - `Y₁ = prep x p`:  no prep-fusion (outer is `prep k`, inner
--                           is `prep k'`).  NARROW to residual.
--       - `Y₁ = swap x y p`: dispatch to narrower residual.
--       - `Y₁ = trans _ _`: ⊥ via norm (top-level `trans (trans _ _) _`
--                           contributes a `suc` to `total-l`).
--
-- ## What this file delivers
--
--   * `ATransByYResidual` — narrower residual record with the
--     non-discharged Y-shape sub-cases for each of the 4 closures:
--
--       For rfr-A-trans-prep-prep:
--         1. `aprepprep-Y-swap`
--         2. `aprepprep-Y-trans-prep`
--         3. `aprepprep-Y-trans-swap`
--
--       For rfr-A-trans-prep-swap:
--         4. `aprepswap-Y-swap`
--         5. `aprepswap-Y-trans-prep`
--         6. `aprepswap-Y-trans-swap`
--
--       For rfr-A-trans-prep-trans:
--         7. `apreptrans-Y-swap`
--         8. `apreptrans-Y-trans-prep`
--         9. `apreptrans-Y-trans-swap`
--
--       For rfr-A-trans-swap:
--        10. `atransswap-Y-swap`
--        11. `atransswap-Y-trans-prep`
--        12. `atransswap-Y-trans-swap`
--
--   * Four closure functions with the EXACT signatures of the four
--     residual fields in `RealFinalResidual`.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `ATransByYResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ATransByCaseY
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopTransClosure sig-dec
  using (size)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure sig-dec
  using (total-l)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure2 sig-dec
  using (swap-count; measure; _≪₃_; ≪₃-fst; ≪₃-snd; ≪₃-thd)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; ≤-refl; n≤1+n; +-assoc; ≤-trans
                                      ; +-monoʳ-<; +-monoʳ-≤)
open import Data.Product using (_,_; _×_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc; acc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Arithmetic helpers.

private
  suc-non-zero : ∀ {n : ℕ} → suc n ≡ 0 → ⊥
  suc-non-zero ()

  +-zero-l-zero : ∀ a b → a + b ≡ 0 → a ≡ 0
  +-zero-l-zero zero    _ _ = refl
  +-zero-l-zero (suc _) _ ()

  +-zero-r-zero : ∀ a b → a + b ≡ 0 → b ≡ 0
  +-zero-r-zero zero    _ eq = eq
  +-zero-r-zero (suc _) _ ()

  -- For `Y = trans refl Y₂`, the new candidate q has size strictly
  -- less than p.
  --
  -- Let:
  --   A = size (prep k a)
  --   B = size (swap k k' b)
  --   sY₂ = size Y₂
  -- Then with Y = trans refl Y₂:
  --   size p = suc (A + suc (B + suc (suc sY₂)))
  -- With q using Y = Y₂:
  --   size q = suc (A + suc (B + sY₂))
  --
  -- We need: size q < size p, i.e. diff = 2.
  size-Y-trans-refl-aux
    : ∀ A B sY₂
    → suc (A + suc (B + sY₂))
      < suc (A + suc (B + suc (suc sY₂)))
  size-Y-trans-refl-aux A B sY₂ =
    s≤s (+-monoʳ-< A (s≤s (+-monoʳ-< B (s≤s (n≤1+n sY₂)))))


--------------------------------------------------------------------------------
-- ## Helper: `All-∈`, used to derive ⊥ from Y = prep unification.

private
  -- If `All P xs` and `x ∈ xs`, then `P x`.
  All-∈ : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} {x : A}
        → All P xs → x ∈ xs → P x
  All-∈ (px ∷ _) (here refl)  = px
  All-∈ (_ ∷ ps) (there x∈xs) = All-∈ ps x∈xs

--------------------------------------------------------------------------------
-- ## Total-l extractors.
--
-- For each closure shape, extract `total-l Y ≡ 0` from `total-l p ≡ 0`.

private
  -- Generic extractor: for the outer cascade
  --   p = trans (prep k a) (trans (swap k k' b) Y),
  -- given total-l p ≡ 0, extract total-l Y ≡ 0, assuming total-l a is
  -- structured in a particular way.
  --
  -- This is the common shape across all 4 closures.  We compute total-l p
  -- as total-l a + (total-l b + total-l Y).  Extracting total-l Y ≡ 0
  -- requires two +-zero-r-zero steps.
  --
  -- We provide a specialized extractor for each closure based on the
  -- structure of `a`.

  -- For rfr-A-trans-prep-prep: a = trans (prep k'' (prep k₃ a₁'')) a₂.
  -- total-l a = total-l (prep k₃ a₁'') + total-l a₂ = total-l a₁'' + total-l a₂.
  -- total-l p = (total-l a₁'' + total-l a₂) + (total-l b + total-l Y).
  total-l-aprepprep-extract-Y
    : ∀ {a} {A : Set a}
        {xs''' ms'' rest rest' : List A} {k k' k'' k₃ : A}
        (a₁'' : xs''' Perm.↭ ms'')
        (a₂ : (k'' ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
    → total-l (Perm.trans (Perm.prep k (Perm.trans (Perm.prep k''
                 (Perm.prep k₃ a₁'')) a₂))
                 (Perm.trans (Perm.swap k k' b) Y)) ≡ 0
    → total-l Y ≡ 0
  total-l-aprepprep-extract-Y a₁'' a₂ b Y eq =
    let tA = total-l a₁'' + total-l a₂
        inner = total-l b + total-l Y
        outer-eq : tA + inner ≡ 0
        outer-eq = eq
        inner-eq : inner ≡ 0
        inner-eq = +-zero-r-zero tA inner outer-eq
    in +-zero-r-zero (total-l b) (total-l Y) inner-eq

  -- For rfr-A-trans-prep-swap: a = trans (prep k'' (swap k₃ k₄ a₁'')) a₂.
  -- total-l a = total-l (swap k₃ k₄ a₁'') + total-l a₂ = total-l a₁'' + total-l a₂.
  total-l-aprepswap-extract-Y
    : ∀ {a} {A : Set a}
        {xs''' ms'' rest rest' : List A} {k k' k'' k₃ k₄ : A}
        (a₁'' : xs''' Perm.↭ ms'')
        (a₂ : (k'' ∷ k₄ ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
    → total-l (Perm.trans (Perm.prep k (Perm.trans (Perm.prep k''
                 (Perm.swap k₃ k₄ a₁'')) a₂))
                 (Perm.trans (Perm.swap k k' b) Y)) ≡ 0
    → total-l Y ≡ 0
  total-l-aprepswap-extract-Y a₁'' a₂ b Y eq =
    let tA = total-l a₁'' + total-l a₂
        inner = total-l b + total-l Y
        outer-eq : tA + inner ≡ 0
        outer-eq = eq
        inner-eq : inner ≡ 0
        inner-eq = +-zero-r-zero tA inner outer-eq
    in +-zero-r-zero (total-l b) (total-l Y) inner-eq

  -- For rfr-A-trans-prep-trans: a = trans (prep k'' (trans a₁'a a₁'b)) a₂.
  -- total-l a = total-l (trans a₁'a a₁'b) + total-l a₂.
  total-l-apreptrans-extract-Y
    : ∀ {a} {A : Set a}
        {xs'' xsM ms' rest rest' : List A} {k k' k'' : A}
        (a₁'a : xs'' Perm.↭ xsM)
        (a₁'b : xsM Perm.↭ ms')
        (a₂ : (k'' ∷ ms') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ xs''))
    → total-l (Perm.trans (Perm.prep k (Perm.trans (Perm.prep k''
                 (Perm.trans a₁'a a₁'b)) a₂))
                 (Perm.trans (Perm.swap k k' b) Y)) ≡ 0
    → total-l Y ≡ 0
  total-l-apreptrans-extract-Y a₁'a a₁'b a₂ b Y eq =
    let tA = total-l (Perm.trans a₁'a a₁'b) + total-l a₂
        inner = total-l b + total-l Y
        outer-eq : tA + inner ≡ 0
        outer-eq = eq
        inner-eq : inner ≡ 0
        inner-eq = +-zero-r-zero tA inner outer-eq
    in +-zero-r-zero (total-l b) (total-l Y) inner-eq

  -- For rfr-A-trans-swap: a = trans (swap k₂ k₃ a₁') a₂.
  -- total-l a = total-l (swap k₂ k₃ a₁') + total-l a₂ = total-l a₁' + total-l a₂.
  total-l-atransswap-extract-Y
    : ∀ {a} {A : Set a}
        {xs'' ms' rest rest' : List A} {k k' k₂ k₃ : A}
        (a₁' : xs'' Perm.↭ ms')
        (a₂ : (k₃ ∷ k₂ ∷ ms') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k₂ ∷ k₃ ∷ xs''))
    → total-l (Perm.trans (Perm.prep k (Perm.trans (Perm.swap k₂ k₃ a₁') a₂))
                 (Perm.trans (Perm.swap k k' b) Y)) ≡ 0
    → total-l Y ≡ 0
  total-l-atransswap-extract-Y a₁' a₂ b Y eq =
    let tA = total-l a₁' + total-l a₂
        inner = total-l b + total-l Y
        outer-eq : tA + inner ≡ 0
        outer-eq = eq
        inner-eq : inner ≡ 0
        inner-eq = +-zero-r-zero tA inner outer-eq
    in +-zero-r-zero (total-l b) (total-l Y) inner-eq

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- Three fields per closure for the non-discharged Y-shape sub-cases:
--   * Y = swap x y Y'                  (forces k' = k'')
--   * Y = trans (prep .k' Y₁') Y₂      (no prep-fusion)
--   * Y = trans (swap .k' .k Y₁') Y₂   (genuine Yang-Baxter braid)

record ATransByYResidual : Set where
  field
    --========================================================================
    -- == rfr-A-trans-prep-prep sub-residuals ===============================
    --========================================================================

    -- Y = swap .k' .k Y' with k' = k''. Y' : rest' ↭ (k₃ ∷ xs''').
    aprepprep-Y-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k'' k₃ : Fin n}
          {xs''' ms'' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k₃ ∷ xs'''))
          (a₁'' : xs''' Perm.↭ ms'')
          (a₂ : (k'' ∷ k₃ ∷ ms'') Perm.↭ (k'' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y' : rest' Perm.↭ (k₃ ∷ xs'''))
          (acc-p
            : let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.swap k'' k Y'
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k'' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.swap k'' k Y'
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k'' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k₃ ∷ xs''') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
              → let a₁' = Perm.prep k₃ a₁''
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.swap k'' k Y'
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k'' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.prep k₃ a₁''
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.swap k'' k Y'
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k'' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Y = trans (prep .k' Y₁') Y₂.
    -- Y₁' : (k ∷ rest') ↭ ms₁'.  Y₂ : (k' ∷ ms₁') ↭ (k ∷ k'' ∷ k₃ ∷ xs''').
    aprepprep-Y-trans-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' k₃ : Fin n}
          {xs''' ms'' rest rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k₃ ∷ xs'''))
          (a₁'' : xs''' Perm.↭ ms'')
          (a₂ : (k'' ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y₁' : (k ∷ rest') Perm.↭ ms₁')
          (Y₂ : (k' ∷ ms₁') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
          (acc-p
            : let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k₃ ∷ xs''') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
              → let a₁' = Perm.prep k₃ a₁''
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.trans (Perm.prep k' Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.prep k₃ a₁''
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.trans (Perm.prep k' Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Y = trans (swap .k' .k Y₁') Y₂.
    -- Y₁' : rest' ↭ ms₁'.  Y₂ : (k ∷ k' ∷ ms₁') ↭ (k ∷ k'' ∷ k₃ ∷ xs''').
    aprepprep-Y-trans-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' k₃ : Fin n}
          {xs''' ms'' rest rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k₃ ∷ xs'''))
          (a₁'' : xs''' Perm.↭ ms'')
          (a₂ : (k'' ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y₁' : rest' Perm.↭ ms₁')
          (Y₂ : (k ∷ k' ∷ ms₁') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
          (acc-p
            : let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k₃ ∷ xs''') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
              → let a₁' = Perm.prep k₃ a₁''
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.prep k₃ a₁''
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.trans (Perm.swap k' k Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    --========================================================================
    -- == rfr-A-trans-prep-swap sub-residuals ===============================
    --========================================================================

    -- Y = swap with k' = k''.
    aprepswap-Y-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k'' k₃ k₄ : Fin n}
          {xs''' ms'' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
          (a₁'' : xs''' Perm.↭ ms'')
          (a₂ : (k'' ∷ k₄ ∷ k₃ ∷ ms'') Perm.↭ (k'' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y' : rest' Perm.↭ (k₃ ∷ k₄ ∷ xs'''))
          (acc-p
            : let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.swap k'' k Y'
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k'' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.swap k'' k Y'
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k'' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs''')
                    Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
              → let a₁' = Perm.swap k₃ k₄ a₁''
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.swap k'' k Y'
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k'' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.swap k₃ k₄ a₁''
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.swap k'' k Y'
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k'' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Y = trans (prep .k' Y₁') Y₂.
    aprepswap-Y-trans-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' k₃ k₄ : Fin n}
          {xs''' ms'' rest rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
          (a₁'' : xs''' Perm.↭ ms'')
          (a₂ : (k'' ∷ k₄ ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y₁' : (k ∷ rest') Perm.↭ ms₁')
          (Y₂ : (k' ∷ ms₁') Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
          (acc-p
            : let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs''')
                    Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
              → let a₁' = Perm.swap k₃ k₄ a₁''
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.trans (Perm.prep k' Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.swap k₃ k₄ a₁''
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.trans (Perm.prep k' Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Y = trans (swap .k' .k Y₁') Y₂.
    aprepswap-Y-trans-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' k₃ k₄ : Fin n}
          {xs''' ms'' rest rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
          (a₁'' : xs''' Perm.↭ ms'')
          (a₂ : (k'' ∷ k₄ ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y₁' : rest' Perm.↭ ms₁')
          (Y₂ : (k ∷ k' ∷ ms₁') Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
          (acc-p
            : let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs''')
                    Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
              → let a₁' = Perm.swap k₃ k₄ a₁''
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.swap k₃ k₄ a₁''
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.trans (Perm.swap k' k Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    --========================================================================
    -- == rfr-A-trans-prep-trans sub-residuals ==============================
    --========================================================================

    -- Y = swap with k' = k''.
    apreptrans-Y-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k'' : Fin n} {xs'' xsM ms' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ xs''))
          (a₁'a : xs'' Perm.↭ xsM)
          (a₁'b : xsM Perm.↭ ms')
          (a₂ : (k'' ∷ ms') Perm.↭ (k'' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y' : rest' Perm.↭ xs'')
          (acc-p
            : let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.swap k'' k Y'
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k'' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.swap k'' k Y'
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k'' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ xs'') Perm.↭ (k ∷ k'' ∷ xs''))
              → let a₁' = Perm.trans a₁'a a₁'b
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.swap k'' k Y'
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k'' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.trans a₁'a a₁'b
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.swap k'' k Y'
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k'' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Y = trans (prep .k' Y₁') Y₂.
    apreptrans-Y-trans-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {xs'' xsM ms' rest rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ xs''))
          (a₁'a : xs'' Perm.↭ xsM)
          (a₁'b : xsM Perm.↭ ms')
          (a₂ : (k'' ∷ ms') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y₁' : (k ∷ rest') Perm.↭ ms₁')
          (Y₂ : (k' ∷ ms₁') Perm.↭ (k ∷ k'' ∷ xs''))
          (acc-p
            : let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ xs'') Perm.↭ (k ∷ k'' ∷ xs''))
              → let a₁' = Perm.trans a₁'a a₁'b
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.trans (Perm.prep k' Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.trans a₁'a a₁'b
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.trans (Perm.prep k' Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Y = trans (swap .k' .k Y₁') Y₂.
    apreptrans-Y-trans-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {xs'' xsM ms' rest rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ xs''))
          (a₁'a : xs'' Perm.↭ xsM)
          (a₁'b : xsM Perm.↭ ms')
          (a₂ : (k'' ∷ ms') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y₁' : rest' Perm.↭ ms₁')
          (Y₂ : (k ∷ k' ∷ ms₁') Perm.↭ (k ∷ k'' ∷ xs''))
          (acc-p
            : let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ xs'') Perm.↭ (k ∷ k'' ∷ xs''))
              → let a₁' = Perm.trans a₁'a a₁'b
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.trans a₁'a a₁'b
              a = Perm.trans (Perm.prep k'' a₁') a₂
              Y = Perm.trans (Perm.swap k' k Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    --========================================================================
    -- == rfr-A-trans-swap sub-residuals ====================================
    --========================================================================

    -- Y = swap with k' = k₂.
    atransswap-Y-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k₂ k₃ : Fin n} {xs'' ms' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ k₂ ∷ k₃ ∷ xs''))
          (a₁' : xs'' Perm.↭ ms')
          (a₂ : (k₃ ∷ k₂ ∷ ms') Perm.↭ (k₂ ∷ rest))
          (b : rest Perm.↭ rest')
          (Y' : rest' Perm.↭ (k₃ ∷ xs''))
          (acc-p
            : let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                  Y = Perm.swap k₂ k Y'
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k₂ b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                  Y = Perm.swap k₂ k Y'
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k₂ b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k₂ ∷ k₃ ∷ xs'') Perm.↭ (k ∷ k₂ ∷ k₃ ∷ xs''))
              → let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                    Y = Perm.swap k₂ k Y'
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k₂ b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
              Y = Perm.swap k₂ k Y'
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k₂ b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Y = trans (prep .k' Y₁') Y₂.
    atransswap-Y-trans-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' k₂ k₃ : Fin n} {xs'' ms' rest rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k₂ ∷ k₃ ∷ xs''))
          (a₁' : xs'' Perm.↭ ms')
          (a₂ : (k₃ ∷ k₂ ∷ ms') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y₁' : (k ∷ rest') Perm.↭ ms₁')
          (Y₂ : (k' ∷ ms₁') Perm.↭ (k ∷ k₂ ∷ k₃ ∷ xs''))
          (acc-p
            : let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k₂ ∷ k₃ ∷ xs'') Perm.↭ (k ∷ k₂ ∷ k₃ ∷ xs''))
              → let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                    Y = Perm.trans (Perm.prep k' Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
              Y = Perm.trans (Perm.prep k' Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Y = trans (swap .k' .k Y₁') Y₂.
    atransswap-Y-trans-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k₂ k₃ : Fin n} {xs'' ms' rest rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k₂ ∷ k₃ ∷ xs''))
          (a₁' : xs'' Perm.↭ ms')
          (a₂ : (k₃ ∷ k₂ ∷ ms') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y₁' : rest' Perm.↭ ms₁')
          (Y₂ : (k ∷ k' ∷ ms₁') Perm.↭ (k ∷ k₂ ∷ k₃ ∷ xs''))
          (acc-p
            : let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k₂ ∷ k₃ ∷ xs'') Perm.↭ (k ∷ k₂ ∷ k₃ ∷ xs''))
              → let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                    Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
              Y = Perm.trans (Perm.swap k' k Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id


--------------------------------------------------------------------------------
-- ## Main closures: case-on-Y for each of the 4 A-trans residuals.

module WithATransByYResidual (res : ATransByYResidual) where
  open ATransByYResidual res

  --==========================================================================
  -- ## rfr-A-trans-prep-prep-closed
  --==========================================================================

  rfr-A-trans-prep-prep-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' k₃ : Fin n}
        {xs''' ms'' rest rest' : List (Fin n)}
        (uniq : Unique (k ∷ k'' ∷ k₃ ∷ xs'''))
        (a₁'' : xs''' Perm.↭ ms'')
        (a₂ : (k'' ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
        (acc-p
          : let a₁' = Perm.prep k₃ a₁''
                a = Perm.trans (Perm.prep k'' a₁') a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let a₁' = Perm.prep k₃ a₁''
                a = Perm.trans (Perm.prep k'' a₁') a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k'' ∷ k₃ ∷ xs''') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
            → let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let a₁' = Perm.prep k₃ a₁''
            a = Perm.trans (Perm.prep k'' a₁') a₂
            p = Perm.trans (Perm.prep k a)
                  (Perm.trans (Perm.swap k k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case Y = refl -----
  -- Forces k' = k, k = k''.  Unique gives k ≢ k''.
  rfr-A-trans-prep-prep-closed vlab {k} {.k} {.k} {k₃} {xs'''} {ms''} {rest}
      {.(k₃ ∷ xs''')} ((k≢k'' ∷ _) ∷ _) a₁'' a₂ b Perm.refl _ _ _ =
    ⊥-elim (k≢k'' refl)

  -- ----- Case Y = prep .k Y' -----
  -- Forces k' = k.  Then Y' : (k ∷ rest') ↭ (k'' ∷ k₃ ∷ xs''').
  -- Use ∈-resp-↭: k ∈ (k ∷ rest') (here refl) → k ∈ codomain.
  -- Unique gives All (k ≢_) (k'' ∷ k₃ ∷ xs''').  Contradiction.
  rfr-A-trans-prep-prep-closed vlab {k} {.k} {k''} {k₃} {xs'''} {ms''} {rest}
      {rest'} (k≢tail ∷ _) a₁'' a₂ b (Perm.prep .k Y') _ _ _ =
    let k∈codom : k ∈ (k'' ∷ k₃ ∷ xs''')
        k∈codom = PermProp.∈-resp-↭ Y' (here refl)
        k≢k : k ≢ k
        k≢k = All-∈ k≢tail k∈codom
    in ⊥-elim (k≢k refl)
    where
      open import Relation.Binary.PropositionalEquality using (_≢_)

  -- ----- Case Y = swap .k' .k Y' -----
  -- Forces k' = k''.  This is NOT directly refuted by Unique.
  -- Dispatch to aprepprep-Y-swap.
  rfr-A-trans-prep-prep-closed vlab {k} {.k''} {k''} {k₃} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.swap .k'' .k Y') acc-p norm self-rec =
    aprepprep-Y-swap vlab uniq a₁'' a₂ b Y' acc-p norm self-rec

  -- ----- Case Y = trans Y₁ Y₂ -----

  -- Sub-case Y₁ = refl: collapse via self-rec (size strict).
  rfr-A-trans-prep-prep-closed vlab {k} {k'} {k''} {k₃} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.trans Perm.refl Y₂) _ _ self-rec =
    let a₁' = Perm.prep k₃ a₁''
        a = Perm.trans (Perm.prep k'' a₁') a₂
        p = Perm.trans (Perm.prep k a)
              (Perm.trans (Perm.swap k k' b)
                (Perm.trans Perm.refl Y₂))
        q = Perm.trans (Perm.prep k a)
              (Perm.trans (Perm.swap k k' b) Y₂)
        A = size (Perm.prep k a)
        B = size (Perm.swap k k' b)
        size-<-q : size q < size p
        size-<-q = size-Y-trans-refl-aux A B (size Y₂)
        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q} {l₂ = total-l p}
                       {c₁ = swap-count q} {c₂ = swap-count p}
                       size-<-q
        ih = self-rec q sub-≪
        bridge : permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
        bridge = ∘-resp-≈ (∘-resp-≈ idʳ ≈-Term-refl) ≈-Term-refl
    in ≈-Term-trans bridge ih

  -- Sub-case Y₁ = prep .k' Y₁': NARROW to aprepprep-Y-trans-prep.
  rfr-A-trans-prep-prep-closed vlab {k} {k'} {k''} {k₃} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.trans (Perm.prep .k' Y₁') Y₂)
      acc-p norm self-rec =
    aprepprep-Y-trans-prep vlab uniq a₁'' a₂ b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = swap .k' .k Y₁': NARROW to aprepprep-Y-trans-swap.
  rfr-A-trans-prep-prep-closed vlab {k} {k'} {k''} {k₃} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.trans (Perm.swap .k' .k Y₁') Y₂)
      acc-p norm self-rec =
    aprepprep-Y-trans-swap vlab uniq a₁'' a₂ b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = trans _ _: IMPOSSIBLE via norm.
  rfr-A-trans-prep-prep-closed vlab {k} {k'} {k''} {k₃} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂) _ norm _ =
    let Y = Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂
        tl-Y-eq : total-l Y ≡ 0
        tl-Y-eq = total-l-aprepprep-extract-Y a₁'' a₂ b Y norm
    in ⊥-elim (suc-non-zero tl-Y-eq)

  --==========================================================================
  -- ## rfr-A-trans-prep-swap-closed
  --==========================================================================

  rfr-A-trans-prep-swap-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' k₃ k₄ : Fin n}
        {xs''' ms'' rest rest' : List (Fin n)}
        (uniq : Unique (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
        (a₁'' : xs''' Perm.↭ ms'')
        (a₂ : (k'' ∷ k₄ ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
        (acc-p
          : let a₁' = Perm.swap k₃ k₄ a₁''
                a = Perm.trans (Perm.prep k'' a₁') a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let a₁' = Perm.swap k₃ k₄ a₁''
                a = Perm.trans (Perm.prep k'' a₁') a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs''')
                  Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
            → let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let a₁' = Perm.swap k₃ k₄ a₁''
            a = Perm.trans (Perm.prep k'' a₁') a₂
            p = Perm.trans (Perm.prep k a)
                  (Perm.trans (Perm.swap k k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case Y = refl -----
  rfr-A-trans-prep-swap-closed vlab {k} {.k} {.k} {k₃} {k₄} {xs'''} {ms''} {rest}
      {.(k₃ ∷ k₄ ∷ xs''')} ((k≢k'' ∷ _) ∷ _) a₁'' a₂ b Perm.refl _ _ _ =
    ⊥-elim (k≢k'' refl)

  -- ----- Case Y = prep .k Y' -----
  rfr-A-trans-prep-swap-closed vlab {k} {.k} {k''} {k₃} {k₄} {xs'''} {ms''} {rest}
      {rest'} (k≢tail ∷ _) a₁'' a₂ b (Perm.prep .k Y') _ _ _ =
    let k∈codom : k ∈ (k'' ∷ k₃ ∷ k₄ ∷ xs''')
        k∈codom = PermProp.∈-resp-↭ Y' (here refl)
        k≢k : k ≢ k
        k≢k = All-∈ k≢tail k∈codom
    in ⊥-elim (k≢k refl)
    where
      open import Relation.Binary.PropositionalEquality using (_≢_)

  -- ----- Case Y = swap .k' .k Y' -----
  rfr-A-trans-prep-swap-closed vlab {k} {.k''} {k''} {k₃} {k₄} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.swap .k'' .k Y') acc-p norm self-rec =
    aprepswap-Y-swap vlab uniq a₁'' a₂ b Y' acc-p norm self-rec

  -- ----- Case Y = trans Y₁ Y₂ -----

  -- Sub-case Y₁ = refl.
  rfr-A-trans-prep-swap-closed vlab {k} {k'} {k''} {k₃} {k₄} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.trans Perm.refl Y₂) _ _ self-rec =
    let a₁' = Perm.swap k₃ k₄ a₁''
        a = Perm.trans (Perm.prep k'' a₁') a₂
        p = Perm.trans (Perm.prep k a)
              (Perm.trans (Perm.swap k k' b)
                (Perm.trans Perm.refl Y₂))
        q = Perm.trans (Perm.prep k a)
              (Perm.trans (Perm.swap k k' b) Y₂)
        A = size (Perm.prep k a)
        B = size (Perm.swap k k' b)
        size-<-q : size q < size p
        size-<-q = size-Y-trans-refl-aux A B (size Y₂)
        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q} {l₂ = total-l p}
                       {c₁ = swap-count q} {c₂ = swap-count p}
                       size-<-q
        ih = self-rec q sub-≪
        bridge : permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
        bridge = ∘-resp-≈ (∘-resp-≈ idʳ ≈-Term-refl) ≈-Term-refl
    in ≈-Term-trans bridge ih

  -- Sub-case Y₁ = prep .k' Y₁'.
  rfr-A-trans-prep-swap-closed vlab {k} {k'} {k''} {k₃} {k₄} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.trans (Perm.prep .k' Y₁') Y₂) acc-p norm self-rec =
    aprepswap-Y-trans-prep vlab uniq a₁'' a₂ b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = swap .k' .k Y₁'.
  rfr-A-trans-prep-swap-closed vlab {k} {k'} {k''} {k₃} {k₄} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.trans (Perm.swap .k' .k Y₁') Y₂) acc-p norm self-rec =
    aprepswap-Y-trans-swap vlab uniq a₁'' a₂ b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = trans _ _.
  rfr-A-trans-prep-swap-closed vlab {k} {k'} {k''} {k₃} {k₄} {xs'''} {ms''} {rest}
      {rest'} uniq a₁'' a₂ b (Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂) _ norm _ =
    let Y = Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂
        tl-Y-eq : total-l Y ≡ 0
        tl-Y-eq = total-l-aprepswap-extract-Y a₁'' a₂ b Y norm
    in ⊥-elim (suc-non-zero tl-Y-eq)

  --==========================================================================
  -- ## rfr-A-trans-prep-trans-closed
  --==========================================================================

  rfr-A-trans-prep-trans-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' : Fin n} {xs'' xsM ms' rest rest' : List (Fin n)}
        (uniq : Unique (k ∷ k'' ∷ xs''))
        (a₁'a : xs'' Perm.↭ xsM)
        (a₁'b : xsM Perm.↭ ms')
        (a₂ : (k'' ∷ ms') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ xs''))
        (acc-p
          : let a₁' = Perm.trans a₁'a a₁'b
                a = Perm.trans (Perm.prep k'' a₁') a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let a₁' = Perm.trans a₁'a a₁'b
                a = Perm.trans (Perm.prep k'' a₁') a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k'' ∷ xs'') Perm.↭ (k ∷ k'' ∷ xs''))
            → let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let a₁' = Perm.trans a₁'a a₁'b
            a = Perm.trans (Perm.prep k'' a₁') a₂
            p = Perm.trans (Perm.prep k a)
                  (Perm.trans (Perm.swap k k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case Y = refl -----
  rfr-A-trans-prep-trans-closed vlab {k} {.k} {.k} {xs''} {xsM} {ms'} {rest}
      {.xs''} ((k≢k'' ∷ _) ∷ _) a₁'a a₁'b a₂ b Perm.refl _ _ _ =
    ⊥-elim (k≢k'' refl)

  -- ----- Case Y = prep .k Y' -----
  rfr-A-trans-prep-trans-closed vlab {k} {.k} {k''} {xs''} {xsM} {ms'} {rest}
      {rest'} (k≢tail ∷ _) a₁'a a₁'b a₂ b (Perm.prep .k Y') _ _ _ =
    let k∈codom : k ∈ (k'' ∷ xs'')
        k∈codom = PermProp.∈-resp-↭ Y' (here refl)
        k≢k : k ≢ k
        k≢k = All-∈ k≢tail k∈codom
    in ⊥-elim (k≢k refl)
    where
      open import Relation.Binary.PropositionalEquality using (_≢_)

  -- ----- Case Y = swap .k' .k Y' -----
  rfr-A-trans-prep-trans-closed vlab {k} {.k''} {k''} {xs''} {xsM} {ms'} {rest}
      {rest'} uniq a₁'a a₁'b a₂ b (Perm.swap .k'' .k Y') acc-p norm self-rec =
    apreptrans-Y-swap vlab uniq a₁'a a₁'b a₂ b Y' acc-p norm self-rec

  -- ----- Case Y = trans Y₁ Y₂ -----

  -- Sub-case Y₁ = refl.
  rfr-A-trans-prep-trans-closed vlab {k} {k'} {k''} {xs''} {xsM} {ms'} {rest}
      {rest'} uniq a₁'a a₁'b a₂ b (Perm.trans Perm.refl Y₂) _ _ self-rec =
    let a₁' = Perm.trans a₁'a a₁'b
        a = Perm.trans (Perm.prep k'' a₁') a₂
        p = Perm.trans (Perm.prep k a)
              (Perm.trans (Perm.swap k k' b)
                (Perm.trans Perm.refl Y₂))
        q = Perm.trans (Perm.prep k a)
              (Perm.trans (Perm.swap k k' b) Y₂)
        A = size (Perm.prep k a)
        B = size (Perm.swap k k' b)
        size-<-q : size q < size p
        size-<-q = size-Y-trans-refl-aux A B (size Y₂)
        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q} {l₂ = total-l p}
                       {c₁ = swap-count q} {c₂ = swap-count p}
                       size-<-q
        ih = self-rec q sub-≪
        bridge : permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
        bridge = ∘-resp-≈ (∘-resp-≈ idʳ ≈-Term-refl) ≈-Term-refl
    in ≈-Term-trans bridge ih

  -- Sub-case Y₁ = prep .k' Y₁'.
  rfr-A-trans-prep-trans-closed vlab {k} {k'} {k''} {xs''} {xsM} {ms'} {rest}
      {rest'} uniq a₁'a a₁'b a₂ b (Perm.trans (Perm.prep .k' Y₁') Y₂)
      acc-p norm self-rec =
    apreptrans-Y-trans-prep vlab uniq a₁'a a₁'b a₂ b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = swap .k' .k Y₁'.
  rfr-A-trans-prep-trans-closed vlab {k} {k'} {k''} {xs''} {xsM} {ms'} {rest}
      {rest'} uniq a₁'a a₁'b a₂ b (Perm.trans (Perm.swap .k' .k Y₁') Y₂)
      acc-p norm self-rec =
    apreptrans-Y-trans-swap vlab uniq a₁'a a₁'b a₂ b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = trans _ _.
  rfr-A-trans-prep-trans-closed vlab {k} {k'} {k''} {xs''} {xsM} {ms'} {rest}
      {rest'} uniq a₁'a a₁'b a₂ b (Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂) _ norm _ =
    let Y = Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂
        tl-Y-eq : total-l Y ≡ 0
        tl-Y-eq = total-l-apreptrans-extract-Y a₁'a a₁'b a₂ b Y norm
    in ⊥-elim (suc-non-zero tl-Y-eq)

  --==========================================================================
  -- ## rfr-A-trans-swap-closed
  --==========================================================================

  rfr-A-trans-swap-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k₂ k₃ : Fin n} {xs'' ms' rest rest' : List (Fin n)}
        (uniq : Unique (k ∷ k₂ ∷ k₃ ∷ xs''))
        (a₁' : xs'' Perm.↭ ms')
        (a₂ : (k₃ ∷ k₂ ∷ ms') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k₂ ∷ k₃ ∷ xs''))
        (acc-p
          : let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k₂ ∷ k₃ ∷ xs'') Perm.↭ (k ∷ k₂ ∷ k₃ ∷ xs''))
            → let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
            p = Perm.trans (Perm.prep k a)
                  (Perm.trans (Perm.swap k k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case Y = refl -----
  rfr-A-trans-swap-closed vlab {k} {.k} {.k} {k₃} {xs''} {ms'} {rest}
      {.(k₃ ∷ xs'')} ((k≢k₂ ∷ _) ∷ _) a₁' a₂ b Perm.refl _ _ _ =
    ⊥-elim (k≢k₂ refl)

  -- ----- Case Y = prep .k Y' -----
  rfr-A-trans-swap-closed vlab {k} {.k} {k₂} {k₃} {xs''} {ms'} {rest}
      {rest'} (k≢tail ∷ _) a₁' a₂ b (Perm.prep .k Y') _ _ _ =
    let k∈codom : k ∈ (k₂ ∷ k₃ ∷ xs'')
        k∈codom = PermProp.∈-resp-↭ Y' (here refl)
        k≢k : k ≢ k
        k≢k = All-∈ k≢tail k∈codom
    in ⊥-elim (k≢k refl)
    where
      open import Relation.Binary.PropositionalEquality using (_≢_)

  -- ----- Case Y = swap .k' .k Y' -----
  rfr-A-trans-swap-closed vlab {k} {.k₂} {k₂} {k₃} {xs''} {ms'} {rest}
      {rest'} uniq a₁' a₂ b (Perm.swap .k₂ .k Y') acc-p norm self-rec =
    atransswap-Y-swap vlab uniq a₁' a₂ b Y' acc-p norm self-rec

  -- ----- Case Y = trans Y₁ Y₂ -----

  -- Sub-case Y₁ = refl.
  rfr-A-trans-swap-closed vlab {k} {k'} {k₂} {k₃} {xs''} {ms'} {rest}
      {rest'} uniq a₁' a₂ b (Perm.trans Perm.refl Y₂) _ _ self-rec =
    let a = Perm.trans (Perm.swap k₂ k₃ a₁') a₂
        p = Perm.trans (Perm.prep k a)
              (Perm.trans (Perm.swap k k' b)
                (Perm.trans Perm.refl Y₂))
        q = Perm.trans (Perm.prep k a)
              (Perm.trans (Perm.swap k k' b) Y₂)
        A = size (Perm.prep k a)
        B = size (Perm.swap k k' b)
        size-<-q : size q < size p
        size-<-q = size-Y-trans-refl-aux A B (size Y₂)
        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q} {l₂ = total-l p}
                       {c₁ = swap-count q} {c₂ = swap-count p}
                       size-<-q
        ih = self-rec q sub-≪
        bridge : permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
        bridge = ∘-resp-≈ (∘-resp-≈ idʳ ≈-Term-refl) ≈-Term-refl
    in ≈-Term-trans bridge ih

  -- Sub-case Y₁ = prep .k' Y₁'.
  rfr-A-trans-swap-closed vlab {k} {k'} {k₂} {k₃} {xs''} {ms'} {rest}
      {rest'} uniq a₁' a₂ b (Perm.trans (Perm.prep .k' Y₁') Y₂)
      acc-p norm self-rec =
    atransswap-Y-trans-prep vlab uniq a₁' a₂ b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = swap .k' .k Y₁'.
  rfr-A-trans-swap-closed vlab {k} {k'} {k₂} {k₃} {xs''} {ms'} {rest}
      {rest'} uniq a₁' a₂ b (Perm.trans (Perm.swap .k' .k Y₁') Y₂)
      acc-p norm self-rec =
    atransswap-Y-trans-swap vlab uniq a₁' a₂ b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = trans _ _.
  rfr-A-trans-swap-closed vlab {k} {k'} {k₂} {k₃} {xs''} {ms'} {rest}
      {rest'} uniq a₁' a₂ b (Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂) _ norm _ =
    let Y = Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂
        tl-Y-eq : total-l Y ≡ 0
        tl-Y-eq = total-l-atransswap-extract-Y a₁' a₂ b Y norm
    in ⊥-elim (suc-non-zero tl-Y-eq)

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `ATransByYResidual` — a STRICTLY NARROWER residual record with
--     12 fields (3 per closure: Y-swap, Y-trans-prep, Y-trans-swap).
--
--   * Four closure functions in module `WithATransByYResidual`:
--       - `rfr-A-trans-prep-prep-closed`
--       - `rfr-A-trans-prep-swap-closed`
--       - `rfr-A-trans-prep-trans-closed`
--       - `rfr-A-trans-swap-closed`
--
--     Each has the EXACT signature of the corresponding field in
--     `RealFinalResidual`, parameterized by `ATransByYResidual`.
--
-- ## Discharge status (per closure)
--
--   * Y = refl:                       CLOSED via ⊥-elim from Unique.
--   * Y = prep _ _:                   CLOSED via ⊥-elim from Unique + Y'.
--   * Y = swap _ _ _:                 NARROWED (k' = ?₁, not refuted by uniq).
--   * Y = trans refl Y₂:              CLOSED via self-rec (size strict).
--   * Y = trans (prep _ _) Y₂:        NARROWED (no prep-fusion).
--   * Y = trans (swap _ _ _) Y₂:      NARROWED (genuine Yang-Baxter).
--   * Y = trans (trans _ _) Y₂:       CLOSED via ⊥-elim from norm.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `ATransByYResidual` record.
--------------------------------------------------------------------------------
