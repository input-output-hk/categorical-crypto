{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Case-on-Y closure for `RealFinalResidual.rfr-B-prep-trans-swap` from
-- `Sub/YangBaxterClosure.agda`.
--
-- ## Target
--
-- The σ-cascade self-loop
--
--   p = trans (swap k k' a) (trans (prep k' b) Y)
--     : (k ∷ k' ∷ rest) ↭ (k ∷ k' ∷ rest)
--
-- where:
--   * `b = trans (swap k k'' b₁') b₂`
--   * `a   : rest ↭ (k'' ∷ rest'')`
--   * `b₁' : rest'' ↭ ms'`
--   * `b₂  : (k'' ∷ k ∷ ms') ↭ tail'`
--   * `Y   : (k' ∷ tail') ↭ (k ∷ k' ∷ rest)`
--   * `Unique (k ∷ k' ∷ rest)`
--   * `total-l p ≡ 0` (normal form).
--   * `self-rec` enabling lex descent.
--
-- ## Strategy: case-split on Y.
--
-- Since `Y` has type `(k' ∷ tail') ↭ (k ∷ k' ∷ rest)`, we pattern-match
-- on its top-level constructor:
--
--   * `Y = refl`:           `k' ≡ k`           → ⊥ via Unique.
--   * `Y = prep x Y'`:      `x = k' = k`       → ⊥ via Unique.
--   * `Y = swap x y Y'`:    NARROW.
--                           `x = k', y = k`, `tail' = k ∷ xs`,
--                           `Y' : xs ↭ rest`.
--   * `Y = trans Y₁ Y₂`:    further case-split on `Y₁`:
--       - `Y₁ = refl`:      collapse `trans refl Y₂ ≡ Y₂`; recurse
--                           via `self-rec` on a size-strict subproblem.
--       - `Y₁ = prep x Y₁'`: prep-fusion produces a size-strictly-smaller
--                           q; recurse via `self-rec`.
--       - `Y₁ = swap x y Y₁'`: dispatch to narrower residual.
--       - `Y₁ = trans _ _`: ⊥ via norm (top-level `trans (trans _ _) _`
--                           contributes a `suc` to `total-l`).
--
-- ## What this file delivers
--
--   * `BPrepTransSwapByYResidual` — narrower residual record with the
--     TWO remaining (non-discharged) Y-shape sub-cases:
--       1. `bptsy-Y-swap`         : Y = swap _ _ _.
--       2. `bptsy-Y-trans-swap`   : Y = trans (swap _ _ _) Y₂.
--
--   * `rfr-B-prep-trans-swap-closed` — function with the EXACT signature
--     of `RealFinalResidual.rfr-B-prep-trans-swap`, dispatching the
--     discharge-able Y-cases (⊥-elim, size-strict via self-rec) and
--     forwarding the non-discharge-able cases to the residual fields.
--
-- ## Why this is strictly narrower than `rfr-B-prep-trans-swap`
--
-- The original `rfr-B-prep-trans-swap` quantifies uniformly over ALL `Y`
-- shapes.  The narrowed residual `BPrepTransSwapByYResidual` has only
-- TWO structurally-tight fields (Y = swap and Y = trans (swap _ _ _) Y₂,
-- the genuine Yang-Baxter braid sub-cases).
--
-- The following cases are CONSTRUCTIVELY eliminated:
--   * Y = refl:                    contradict `Unique (k ∷ k' ∷ rest)`.
--   * Y = prep _ _:                contradict `Unique` via head match.
--   * Y = trans refl _:            collapses via `self-rec` (size strict).
--   * Y = trans (prep _ _) _:      prep-fusion via `self-rec` (size strict).
--   * Y = trans (trans _ _) _:     contradicts `norm` (total-l increment).
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `BPrepTransSwapByYResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BPrepTransSwapByCaseY
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
  --   A = size (swap k k' a)
  --   B = size (prep k' (trans (swap k k'' b₁') b₂))
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

  -- For `Y = trans (prep .k' Y₁') Y₂`, prep-fusion gives a strict
  -- size decrease.
  --
  -- size p (with Y = trans (prep k' Y₁') Y₂)
  --   = suc (suc sa + suc (suc (suc (suc sb₁' + sb₂)) + suc (suc sY₁' + sY₂)))
  -- size q (after prep-fusion: prep k' (trans b Y₁'))
  --   = suc (suc sa + suc (suc (suc (suc (suc sb₁' + sb₂) + sY₁')) + sY₂))
  -- Diff = 1.
  --
  -- Strategy: peel off `suc (suc sa + ...)` via +-monoʳ-<, then prove
  -- the inner inequality by stepwise +-suc rewrites.
  size-Y-trans-prep-fusion-<-inner
    : ∀ sb₁' sb₂ sY₁' sY₂
    → suc (suc (suc (suc (suc sb₁' + sb₂) + sY₁')) + sY₂)
      < suc (suc (suc (suc sb₁' + sb₂)) + suc (suc sY₁' + sY₂))
  size-Y-trans-prep-fusion-<-inner sb₁' sb₂ sY₁' sY₂
    rewrite +-suc (suc (suc sb₁' + sb₂)) (suc (sY₁' + sY₂))
          | +-suc (suc (suc sb₁' + sb₂)) (sY₁' + sY₂)
          | +-assoc (suc (suc sb₁' + sb₂)) sY₁' sY₂
    = ≤-refl

  size-Y-trans-prep-fusion-<
    : ∀ sa sb₁' sb₂ sY₁' sY₂
    → suc (suc sa + suc (suc (suc (suc (suc sb₁' + sb₂) + sY₁')) + sY₂))
      < suc (suc sa + suc (suc (suc (suc sb₁' + sb₂)) + suc (suc sY₁' + sY₂)))
  size-Y-trans-prep-fusion-< sa sb₁' sb₂ sY₁' sY₂ =
    s≤s (+-monoʳ-< (suc sa) (size-Y-trans-prep-fusion-<-inner sb₁' sb₂ sY₁' sY₂))


--------------------------------------------------------------------------------
-- ## Helper: `All-∈` from `Any-∈`, used to derive ⊥ from Y-swap unification.

private
  -- If `All P xs` and `x ∈ xs`, then `P x`.
  All-∈ : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} {x : A}
        → All P xs → x ∈ xs → P x
  All-∈ (px ∷ _) (here refl)  = px
  All-∈ (_ ∷ ps) (there x∈xs) = All-∈ ps x∈xs

--------------------------------------------------------------------------------
-- ## Total-l extractor for the B-prep-trans-swap cascade.
--
-- total-l p where p = trans (swap k k' a) (trans (prep k' b) Y)
--   and b = trans (swap k k'' b₁') b₂
--
-- Computing:
--   total-l (trans (swap k k' a) Z) = total-l a + total-l Z       (swap left)
--   total-l (trans (prep k' b) Y)
--     = total-l b + total-l Y                                     (prep left)
--   total-l b = total-l (trans (swap k k'' b₁') b₂)
--     = total-l b₁' + total-l b₂                                  (swap left)
-- So:
--   total-l p = total-l a + ((total-l b₁' + total-l b₂) + total-l Y)

private
  total-l-bprep-trans-swap-extract-Y
    : ∀ {a} {A : Set a}
        {rest rest'' ms' tail' : List A} {k k' k'' : A}
        (a-perm : rest Perm.↭ (k'' ∷ rest''))
        (b₁' : rest'' Perm.↭ ms')
        (b₂ : (k'' ∷ k ∷ ms') Perm.↭ tail')
        (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
    → let b₁ = Perm.swap k k'' b₁'
          b  = Perm.trans b₁ b₂
      in total-l (Perm.trans (Perm.swap k k' a-perm)
                   (Perm.trans (Perm.prep k' b) Y)) ≡ 0
    → total-l Y ≡ 0
  total-l-bprep-trans-swap-extract-Y a-perm b₁' b₂ Y eq =
    let tb = total-l b₁' + total-l b₂
        inner = tb + total-l Y
        outer-eq : total-l a-perm + inner ≡ 0
        outer-eq = eq
        inner-eq : inner ≡ 0
        inner-eq = +-zero-r-zero (total-l a-perm) inner outer-eq
    in +-zero-r-zero tb (total-l Y) inner-eq

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- Two fields for the only non-discharged Y-shape sub-cases
-- (after refl/prep/trans-refl/trans-prep/trans-trans are all closed
-- constructively).

record BPrepTransSwapByYResidual : Set where
  field
    -- =================================================================
    -- Case Y = swap x y Y'.
    --
    -- Y : (k' ∷ tail') ↭ (k ∷ k' ∷ rest).
    -- Y = swap x y Y' matches (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys), so
    --   x = k', y = k, tail' = k ∷ xs, Y' : xs ↭ rest.
    -- =================================================================
    bptsy-Y-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n}
          {rest rest'' ms' xs : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ (k'' ∷ rest''))
          (b₁' : rest'' Perm.↭ ms')
          (b₂ : (k'' ∷ k ∷ ms') Perm.↭ (k ∷ xs))
          (Y' : xs Perm.↭ rest)
          (acc-p
            : let b₁ = Perm.swap k k'' b₁'
                  b  = Perm.trans b₁ b₂
                  Y  = Perm.swap k' k Y'
                  p  = Perm.trans (Perm.swap k k' a)
                         (Perm.trans (Perm.prep k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let b₁ = Perm.swap k k'' b₁'
                  b  = Perm.trans b₁ b₂
                  Y  = Perm.swap k' k Y'
                  p  = Perm.trans (Perm.swap k k' a)
                         (Perm.trans (Perm.prep k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
              → let b₁ = Perm.swap k k'' b₁'
                    b  = Perm.trans b₁ b₂
                    Y  = Perm.swap k' k Y'
                    p  = Perm.trans (Perm.swap k k' a)
                           (Perm.trans (Perm.prep k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let b₁ = Perm.swap k k'' b₁'
              b  = Perm.trans b₁ b₂
              Y  = Perm.swap k' k Y'
              p  = Perm.trans (Perm.swap k k' a)
                     (Perm.trans (Perm.prep k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- =================================================================
    -- Case Y = trans (swap x y Y₁') Y₂.
    --
    -- Y : (k' ∷ tail') ↭ (k ∷ k' ∷ rest).
    -- Y = trans Y₁ Y₂ with Y₁ = swap x y Y₁'.
    -- Y₁ : (k' ∷ tail') ↭ ms, with Y₁ = swap .k' y Y₁'.
    -- So tail' = y ∷ xs, ms = y ∷ k' ∷ ys, Y₁' : xs ↭ ys.
    -- Y₂ : (y ∷ k' ∷ ys) ↭ (k ∷ k' ∷ rest).
    -- =================================================================
    bptsy-Y-trans-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' k''' : Fin n}
          {rest rest'' ms' xs ys : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ (k'' ∷ rest''))
          (b₁' : rest'' Perm.↭ ms')
          (b₂ : (k'' ∷ k ∷ ms') Perm.↭ (k''' ∷ xs))
          (Y₁' : xs Perm.↭ ys)
          (Y₂ : (k''' ∷ k' ∷ ys) Perm.↭ (k ∷ k' ∷ rest))
          (acc-p
            : let b₁ = Perm.swap k k'' b₁'
                  b  = Perm.trans b₁ b₂
                  Y  = Perm.trans (Perm.swap k' k''' Y₁') Y₂
                  p  = Perm.trans (Perm.swap k k' a)
                         (Perm.trans (Perm.prep k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let b₁ = Perm.swap k k'' b₁'
                  b  = Perm.trans b₁ b₂
                  Y  = Perm.trans (Perm.swap k' k''' Y₁') Y₂
                  p  = Perm.trans (Perm.swap k k' a)
                         (Perm.trans (Perm.prep k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
              → let b₁ = Perm.swap k k'' b₁'
                    b  = Perm.trans b₁ b₂
                    Y  = Perm.trans (Perm.swap k' k''' Y₁') Y₂
                    p  = Perm.trans (Perm.swap k k' a)
                           (Perm.trans (Perm.prep k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let b₁ = Perm.swap k k'' b₁'
              b  = Perm.trans b₁ b₂
              Y  = Perm.trans (Perm.swap k' k''' Y₁') Y₂
              p  = Perm.trans (Perm.swap k k' a)
                     (Perm.trans (Perm.prep k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

--------------------------------------------------------------------------------
-- ## Main: `rfr-B-prep-trans-swap-closed`.
--
-- Case-split on `Y`.

module WithBPrepTransSwapByYResidual (res : BPrepTransSwapByYResidual) where
  open BPrepTransSwapByYResidual res

  rfr-B-prep-trans-swap-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' : Fin n} {rest rest'' ms' tail' : List (Fin n)}
        (uniq : Unique (k ∷ k' ∷ rest))
        (a : rest Perm.↭ (k'' ∷ rest''))
        (b₁' : rest'' Perm.↭ ms')
        (b₂ : (k'' ∷ k ∷ ms') Perm.↭ tail')
        (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
        (acc-p
          : let b₁ = Perm.swap k k'' b₁'
                b  = Perm.trans b₁ b₂
                p  = Perm.trans (Perm.swap k k' a)
                       (Perm.trans (Perm.prep k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let b₁ = Perm.swap k k'' b₁'
                b  = Perm.trans b₁ b₂
                p  = Perm.trans (Perm.swap k k' a)
                       (Perm.trans (Perm.prep k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
            → let b₁ = Perm.swap k k'' b₁'
                  b  = Perm.trans b₁ b₂
                  p  = Perm.trans (Perm.swap k k' a)
                         (Perm.trans (Perm.prep k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let b₁ = Perm.swap k k'' b₁'
            b  = Perm.trans b₁ b₂
            p  = Perm.trans (Perm.swap k k' a)
                   (Perm.trans (Perm.prep k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case Y = Perm.refl -----
  --
  -- Y : (k' ∷ tail') ↭ (k ∷ k' ∷ rest)
  -- Y = refl forces (k' ∷ tail') ≡ (k ∷ k' ∷ rest).
  -- Then k' ≡ k, but Unique (k ∷ k' ∷ rest) gives k ≠ k'.
  rfr-B-prep-trans-swap-closed vlab {k} {.k} {k''} {rest} {rest''} {ms'}
      {.(k ∷ rest)} ((k≢k' ∷ _) ∷ _) a b₁' b₂ Perm.refl _ _ _ =
    ⊥-elim (k≢k' refl)

  -- ----- Case Y = Perm.prep _ _ -----
  --
  -- Y = prep x Y' : (x ∷ xs) ↭ (x ∷ ys) means LHS head x ≡ k' (from
  -- Y's LHS k' ∷ tail') and x ≡ k (from Y's RHS k ∷ k' ∷ rest).
  -- So k' ≡ k.  Contradicts Unique.
  rfr-B-prep-trans-swap-closed vlab {k} {.k} {k''} {rest} {rest''} {ms'} {tail'}
      ((k≢k' ∷ _) ∷ _) a b₁' b₂ (Perm.prep .k _) _ _ _ =
    ⊥-elim (k≢k' refl)

  -- ----- Case Y = Perm.swap _ _ _ -----
  --
  -- Y = swap x y Y' : (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys).
  -- Matching LHS (k' ∷ tail''): x = k', tail' = y ∷ xs.
  -- Matching RHS (k ∷ k' ∷ rest): y = k, x = k', ys = rest.
  -- So tail' = k ∷ xs, Y' : xs ↭ rest.
  --
  -- This case is dispatched to `bptsy-Y-swap`.
  rfr-B-prep-trans-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {ms'}
      {.(k ∷ _)} uniq a b₁' b₂ (Perm.swap .k' .k Y') acc-p norm self-rec =
    bptsy-Y-swap vlab uniq a b₁' b₂ Y' acc-p norm self-rec

  -- ----- Case Y = Perm.trans Y₁ Y₂ -----

  -- Sub-case Y₁ = refl: collapse trans refl Y₂ → Y₂.
  -- Build q with Y replaced by Y₂.  size-strict descent.
  --
  -- permute(map⁺ vlab p)
  --   = pY ∘ ((id ⊗ pb) ∘ σ-block_kk')
  -- where pY = permute (map⁺ vlab (trans refl Y₂))
  --          = permute (map⁺ vlab Y₂) ∘ permute (map⁺ vlab refl)
  --          = permute (map⁺ vlab Y₂) ∘ id
  --          ≈Term permute (map⁺ vlab Y₂).
  --
  -- After collapse, permute p ≈Term permute q.  Apply self-rec.
  rfr-B-prep-trans-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {ms'} {tail'}
      uniq a b₁' b₂ (Perm.trans Perm.refl Y₂) _ _ self-rec =
    let b₁ = Perm.swap k k'' b₁'
        b  = Perm.trans b₁ b₂
        p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' b)
                (Perm.trans Perm.refl Y₂))
        q = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' b) Y₂)
        A = size (Perm.swap k k' a)
        B = size (Perm.prep k' b)
        size-<-q : size q < size p
        size-<-q = size-Y-trans-refl-aux A B (size Y₂)
        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q} {l₂ = total-l p}
                       {c₁ = swap-count q} {c₂ = swap-count p}
                       size-<-q
        ih = self-rec q sub-≪
        -- Bridge: permute p ≈Term permute q.
        --
        -- permute(map⁺ vlab p)
        --   = ((permute (map⁺ vlab Y₂) ∘ id) ∘ permute (...)) ∘ permute (swap k k' a)
        -- permute(map⁺ vlab q)
        --   = (permute (map⁺ vlab Y₂) ∘ permute (...)) ∘ permute (swap k k' a)
        -- Difference: `pY₂ ∘ id` vs `pY₂`.  Resolve via idʳ at depth 2.
        bridge : permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
        bridge = ∘-resp-≈ (∘-resp-≈ idʳ ≈-Term-refl) ≈-Term-refl
    in ≈-Term-trans bridge ih

  -- Sub-case Y₁ = prep x Y₁' : CLOSED constructively via prep-fusion.
  --
  -- Y = trans (prep .k' Y₁') Y₂.
  -- Y₁' : tail' ↭ ms'.
  -- Y₂ : (k' ∷ ms') ↭ (k ∷ k' ∷ rest).
  --
  -- Two `prep k'`'s at the same outer level fuse via prep-fusion:
  --   p = trans (swap k k' a) (trans (prep k' b)
  --                              (trans (prep k' Y₁') Y₂))
  --   q = trans (swap k k' a) (trans (prep k' (trans b Y₁')) Y₂)
  --
  -- size q < size p (diff 1).
  -- permute p ≈Term permute q via assoc + ⊗-∘-dist⁻¹ + idˡ collapse.
  rfr-B-prep-trans-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {ms'} {tail'}
      uniq a b₁' b₂ (Perm.trans (Perm.prep .k' Y₁') Y₂) _ _ self-rec =
    let b₁ = Perm.swap k k'' b₁'
        b  = Perm.trans b₁ b₂
        p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' b)
                (Perm.trans (Perm.prep k' Y₁') Y₂))
        q = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k'
                (Perm.trans b Y₁')) Y₂)
        sa   = size a
        sb₁' = size b₁'
        sb₂  = size b₂
        sY₁' = size Y₁'
        sY₂  = size Y₂
        size-<-q : size q < size p
        size-<-q = size-Y-trans-prep-fusion-< sa sb₁' sb₂ sY₁' sY₂
        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q} {l₂ = total-l p}
                       {c₁ = swap-count q} {c₂ = swap-count p}
                       size-<-q
        ih = self-rec q sub-≪
        -- Bridge: permute p ≈Term permute q.
        --
        -- permute p
        --   = ((pY₂ ∘ (id ⊗ pY₁')) ∘ (id ⊗ pb)) ∘ pSW_kk'
        --   where pb = permute (map⁺ vlab b)
        --         pSW_kk'  = permute (map⁺ vlab (swap k k' a))
        --
        -- permute q
        --   = (pY₂ ∘ (id ⊗ (pY₁' ∘ pb))) ∘ pSW_kk'
        --
        -- Bridge: (pY₂ ∘ (id ⊗ pY₁')) ∘ (id ⊗ pb)
        --     ≈ pY₂ ∘ ((id ⊗ pY₁') ∘ (id ⊗ pb))      (assoc)
        --     ≈ pY₂ ∘ ((id ∘ id) ⊗ (pY₁' ∘ pb))      (⊗-∘-dist⁻¹)
        --     ≈ pY₂ ∘ (id ⊗ (pY₁' ∘ pb))             (idˡ inside ⊗)
        bridge : permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
        bridge =
          ∘-resp-≈
            (≈-Term-trans assoc
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                  (⊗-resp-≈ idˡ ≈-Term-refl))))
            ≈-Term-refl
    in ≈-Term-trans bridge ih

  -- Sub-case Y₁ = swap x y Y₁' : dispatch to bptsy-Y-trans-swap.
  --
  -- Y = trans (swap x y Y₁') Y₂.
  -- Y₁ = swap x y Y₁' : (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys).
  -- LHS of Y : (k' ∷ tail'), so x = k', tail' = y ∷ xs.
  -- Y₁' : xs ↭ ys.
  -- Y₂ : (y ∷ k' ∷ ys) ↭ (k ∷ k' ∷ rest).
  rfr-B-prep-trans-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {ms'}
      {.(_ ∷ _)} uniq a b₁' b₂ (Perm.trans (Perm.swap .k' k''' Y₁') Y₂)
      acc-p norm self-rec =
    bptsy-Y-trans-swap vlab uniq a b₁' b₂ Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = trans _ _ : IMPOSSIBLE via norm.
  --
  -- total-l p
  --   = total-l a + total-l b + total-l Y
  --   = ... + total-l (trans (trans _ _) _)
  --   = ... + suc (...) > 0
  -- contradicts norm ≡ 0.
  rfr-B-prep-trans-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {ms'} {tail'}
      uniq a b₁' b₂ (Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂) _ norm _ =
    let Y = Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂
        tl-Y-eq : total-l Y ≡ 0
        tl-Y-eq = total-l-bprep-trans-swap-extract-Y a b₁' b₂ Y norm
    in ⊥-elim (suc-non-zero tl-Y-eq)

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `BPrepTransSwapByYResidual` — a STRICTLY NARROWER residual record
--     with TWO fields (Y = swap and Y = trans (swap _ _ _) _, the
--     genuine Yang-Baxter braid sub-cases).
--
--   * `rfr-B-prep-trans-swap-closed` (in module
--     `WithBPrepTransSwapByYResidual`) — a function with the EXACT
--     signature of `RealFinalResidual.rfr-B-prep-trans-swap`,
--     parameterized by `BPrepTransSwapByYResidual`.
--
-- ## Discharge status
--
--   * Y = refl:                       CLOSED via ⊥-elim from Unique.
--   * Y = prep _ _:                   CLOSED via ⊥-elim from Unique.
--   * Y = swap _ _ _:                 NARROWED (dispatch to bptsy-Y-swap).
--   * Y = trans refl Y₂:              CLOSED via self-rec (size strict).
--   * Y = trans (prep _ _) Y₂:        CLOSED via self-rec (prep-fusion).
--   * Y = trans (swap _ _ _) Y₂:      NARROWED (dispatch to bptsy-Y-trans-swap).
--   * Y = trans (trans _ _) Y₂:       CLOSED via ⊥-elim from norm.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BPrepTransSwapByYResidual` record.
--------------------------------------------------------------------------------
