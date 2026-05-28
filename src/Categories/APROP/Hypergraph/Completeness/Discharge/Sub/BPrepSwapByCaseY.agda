{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Case-on-Y closure for `RealFinalResidual.rfr-B-prep-swap` from
-- `Sub/YangBaxterClosure.agda`.
--
-- ## Target
--
-- The σ-cascade self-loop
--
--   p = trans (swap k k' a) (trans (prep k' (swap k k'' b')) Y)
--     : (k ∷ k' ∷ rest) ↭ (k ∷ k' ∷ rest)
--
-- with
--   * `a : rest ↭ (k'' ∷ rest'')`
--   * `b' : rest'' ↭ tail''`
--   * `Y : (k' ∷ k'' ∷ k ∷ tail'') ↭ (k ∷ k' ∷ rest)`
--   * `Unique (k ∷ k' ∷ rest)`
--   * `total-l p ≡ 0` (normal form).
--   * `self-rec` enabling lex descent.
--
-- ## Strategy: case-split on Y.
--
-- Since `Y` has type `(k' ∷ k'' ∷ k ∷ tail'') ↭ (k ∷ k' ∷ rest)`, the
-- LHS head is `k'` but the RHS head is `k`.  Pattern-matching forces:
--
--   * `Y = refl`:           `k' ≡ k`           → ⊥ via Unique.
--   * `Y = prep x Y'`:      head `x = k' = k`  → ⊥ via Unique.
--   * `Y = swap x y Y'`:    `y = k'' = k`      → ⊥ via Unique + a.
--                           `a : rest ↭ (k ∷ rest'')` (refined),
--                           so `k ∈ rest`; but Unique gives `k ∉ rest`.
--   * `Y = trans Y₁ Y₂`:    further case-split on `Y₁`:
--       - `Y₁ = refl`:      collapse `trans refl Y₂ ≡ Y₂` and recurse
--                           via `self-rec` on a size-strict subproblem.
--       - `Y₁ = prep x p`:  prep-fusion produces a size-strictly-smaller
--                           q; recurse via `self-rec`.
--       - `Y₁ = swap x y p`: dispatch to narrower residual.
--       - `Y₁ = trans _ _`: ⊥ via norm (top-level `trans (trans _ _) _`
--                           contributes a `suc` to `total-l`).
--
-- ## What this file delivers
--
--   * `BPrepSwapByYResidual` — narrower residual record with the
--     ONE remaining (non-discharged) Y-shape sub-case:
--       1. `bpsy-Y-trans-swap`   : Y = trans (swap _ _ _) Y₂.
--
--   * `rfr-B-prep-swap-closed` — function with the EXACT signature of
--     `RealFinalResidual.rfr-B-prep-swap`, dispatching the
--     discharge-able Y-cases (⊥-elim, size-strict via self-rec) and
--     forwarding the non-discharge-able case to the residual field.
--
-- ## Why this is strictly narrower than `rfr-B-prep-swap`
--
-- The original `rfr-B-prep-swap` quantifies uniformly over ALL `Y`
-- shapes.  The narrowed residual `BPrepSwapByYResidual` has just
-- ONE structurally-tight field (Y = trans (swap _ _ _) Y₂, the
-- genuine Yang-Baxter braid sub-case).
--
-- The following cases are CONSTRUCTIVELY eliminated:
--   * Y = refl:                    contradict `Unique (k ∷ k' ∷ rest)`.
--   * Y = prep _ _:                contradict `Unique` via head match.
--   * Y = swap _ _ _:              contradict `Unique` via `∈-resp-↭ a`
--                                  (forces `k = k''` and thus `k ∈ rest`).
--   * Y = trans refl _:            collapses via `self-rec` (size strict).
--   * Y = trans (prep _ _) _:      prep-fusion via `self-rec` (size strict).
--   * Y = trans (trans _ _) _:     contradicts `norm` (total-l increment).
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `BPrepSwapByYResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BPrepSwapByCaseY
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
  --   B = size (prep k' (swap k k'' b'))
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
  --   = suc (suc sa + suc (suc (suc sb') + suc (suc sY₁' + sY₂)))
  -- size q (after prep-fusion: prep k' (trans (swap k k'' b') Y₁'))
  --   = suc (suc sa + suc (suc (suc (suc sb' + sY₁')) + sY₂))
  -- Diff = 1.
  --
  -- Strategy: peel off `suc (suc sa + ...)` via +-monoʳ-<, then prove
  -- the inner inequality by stepwise +-suc rewrites.
  size-Y-trans-prep-fusion-<-inner
    : ∀ sb' sY₁' sY₂
    → suc (suc (suc (suc sb' + sY₁')) + sY₂)
      < suc (suc (suc sb') + suc (suc sY₁' + sY₂))
  size-Y-trans-prep-fusion-<-inner sb' sY₁' sY₂
    rewrite +-suc sb' (suc (sY₁' + sY₂))
          | +-suc sb' (sY₁' + sY₂)
          | +-assoc sb' sY₁' sY₂
    = ≤-refl

  size-Y-trans-prep-fusion-<
    : ∀ sa sb' sY₁' sY₂
    → suc (suc sa + suc (suc (suc (suc sb' + sY₁')) + sY₂))
      < suc (suc sa + suc (suc (suc sb') + suc (suc sY₁' + sY₂)))
  size-Y-trans-prep-fusion-< sa sb' sY₁' sY₂ =
    s≤s (+-monoʳ-< (suc sa) (size-Y-trans-prep-fusion-<-inner sb' sY₁' sY₂))


--------------------------------------------------------------------------------
-- ## Helper: `All-∉` from `Any-∈`, used to derive ⊥ from Y-swap unification.

private
  -- If `All P xs` and `x ∈ xs`, then `P x`.
  All-∈ : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} {x : A}
        → All P xs → x ∈ xs → P x
  All-∈ (px ∷ _) (here refl)  = px
  All-∈ (_ ∷ ps) (there x∈xs) = All-∈ ps x∈xs

--------------------------------------------------------------------------------
-- ## Total-l extractor for the B-prep-swap cascade.
--
-- total-l p where p = trans (swap k k' a) (trans (prep k' (swap k k'' b')) Y)
--
-- Computing:
--   total-l (trans (swap k k' a) Z) = total-l a + total-l Z       (swap left)
--   total-l (trans (prep k' (swap k k'' b')) Y)
--     = total-l (swap k k'' b') + total-l Y                       (prep left)
--     = total-l b' + total-l Y                                    (swap inner)
-- So:
--   total-l p = total-l a + (total-l b' + total-l Y)

private
  total-l-bprep-swap-extract-Y
    : ∀ {a} {A : Set a}
        {rest rest'' tail'' : List A} {k k' k'' : A}
        (a-perm : rest Perm.↭ (k'' ∷ rest''))
        (b' : rest'' Perm.↭ tail'')
        (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ rest))
    → total-l (Perm.trans (Perm.swap k k' a-perm)
                 (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)) ≡ 0
    → total-l Y ≡ 0
  total-l-bprep-swap-extract-Y a-perm b' Y eq =
    let inner = total-l b' + total-l Y
        outer-eq : total-l a-perm + inner ≡ 0
        outer-eq = eq
        inner-eq : inner ≡ 0
        inner-eq = +-zero-r-zero (total-l a-perm) inner outer-eq
    in +-zero-r-zero (total-l b') (total-l Y) inner-eq

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- One field for the only non-discharged Y-shape sub-case
-- (after refl/prep/swap/trans-refl/trans-prep/trans-trans are all
-- closed constructively).

record BPrepSwapByYResidual : Set where
  field
    -- =================================================================
    -- Case Y = trans (swap x y Y₁') Y₂.
    --
    -- Y : (k' ∷ k'' ∷ k ∷ tail'') ↭ (k ∷ k' ∷ rest).
    -- Y = trans Y₁ Y₂ with Y₁ = swap x y Y₁'.
    -- Y₁ : (k' ∷ k'' ∷ k ∷ tail'') ↭ ms, with Y₁ = swap .k' .k'' Y₁'.
    -- So ms = k'' ∷ k' ∷ ms', Y₁' : (k ∷ tail'') ↭ ms'.
    -- Y₂ : (k'' ∷ k' ∷ ms') ↭ (k ∷ k' ∷ rest).
    -- =================================================================
    bpsy-Y-trans-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {rest rest'' tail'' ms' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ (k'' ∷ rest''))
          (b' : rest'' Perm.↭ tail'')
          (Y₁' : (k ∷ tail'') Perm.↭ ms')
          (Y₂ : (k'' ∷ k' ∷ ms') Perm.↭ (k ∷ k' ∷ rest))
          (acc-p
            : let Y = Perm.trans (Perm.swap k' k'' Y₁') Y₂
                  p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let Y = Perm.trans (Perm.swap k' k'' Y₁') Y₂
                  p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
              → let Y = Perm.trans (Perm.swap k' k'' Y₁') Y₂
                    p = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let Y = Perm.trans (Perm.swap k' k'' Y₁') Y₂
              p = Perm.trans (Perm.swap k k' a)
                    (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

--------------------------------------------------------------------------------
-- ## Main: `rfr-B-prep-swap-closed`.
--
-- Case-split on `Y`.

module WithBPrepSwapByYResidual (res : BPrepSwapByYResidual) where
  open BPrepSwapByYResidual res

  rfr-B-prep-swap-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' : Fin n} {rest rest'' tail'' : List (Fin n)}
        (uniq : Unique (k ∷ k' ∷ rest))
        (a : rest Perm.↭ (k'' ∷ rest''))
        (b' : rest'' Perm.↭ tail'')
        (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ rest))
        (acc-p
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
            → let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let p = Perm.trans (Perm.swap k k' a)
                  (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case Y = Perm.refl -----
  --
  -- Y : (k' ∷ k'' ∷ k ∷ tail'') ↭ (k ∷ k' ∷ rest)
  -- Y = refl forces (k' ∷ k'' ∷ k ∷ tail'') ≡ (k ∷ k' ∷ rest).
  -- Then k' ≡ k (and k'' ≡ k', rest = k ∷ tail''), but
  -- Unique (k ∷ k' ∷ rest) gives k ≠ k'.
  rfr-B-prep-swap-closed vlab {k} {.k} {.k} {.(k ∷ tail'')} {rest''} {tail''}
      ((k≢k' ∷ _) ∷ _) a b' Perm.refl _ _ _ =
    ⊥-elim (k≢k' refl)

  -- ----- Case Y = Perm.prep _ _ -----
  --
  -- Y = prep x Y' : (x ∷ xs) ↭ (x ∷ ys) means LHS head x ≡ k' (from
  -- Y's LHS k' ∷ ...) and x ≡ k (from Y's RHS k ∷ ...).  So k' ≡ k.
  -- Contradicts Unique.
  rfr-B-prep-swap-closed vlab {k} {.k} {k''} {rest} {rest''} {tail''}
      ((k≢k' ∷ _) ∷ _) a b' (Perm.prep .k _) _ _ _ =
    ⊥-elim (k≢k' refl)

  -- ----- Case Y = Perm.swap _ _ _ -----
  --
  -- Y = swap x y Y' : (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys).
  -- Matching LHS (k' ∷ k'' ∷ k ∷ tail''): x = k', y = k''.
  -- Matching RHS (k ∷ k' ∷ rest): y = k, x = k'.
  -- So k'' = k AND the inner Y' : (k ∷ tail'') ↭ rest.
  --
  -- This case is CLOSED constructively via Unique + permutation `a`:
  --   * a : rest ↭ (k ∷ rest'')  (since k'' = k)
  --   * `here refl : k ∈ (k ∷ rest'')`
  --   * `∈-resp-↭ (↭-sym a) (here refl) : k ∈ rest`
  --   * Unique (k ∷ k' ∷ rest) gives `(k≢k' ∷ k≢rest) ∷ _`,
  --     where `k≢rest : All (_≢ k) rest`.
  --   * All-∈ k≢rest (k ∈ rest) gives `k ≢ k`, contradiction.
  rfr-B-prep-swap-closed vlab {k} {k'} {.k} {rest} {rest''} {tail''}
      ((_ ∷ k≢rest) ∷ _) a b' (Perm.swap .k' .k Y') _ _ _ =
    let k∈rest : k ∈ rest
        k∈rest = PermProp.∈-resp-↭ (Perm.↭-sym a) (here refl)
        k≢k : k ≢ k
        k≢k = All-∈ k≢rest k∈rest
    in ⊥-elim (k≢k refl)
    where
      open import Relation.Binary.PropositionalEquality using (_≢_)

  -- ----- Case Y = Perm.trans Y₁ Y₂ -----

  -- Sub-case Y₁ = refl: collapse trans refl Y₂ → Y₂.
  -- Build q with Y replaced by Y₂.  size-strict descent.
  --
  -- permute(map⁺ vlab p)
  --   = pY ∘ ((id ⊗ (id ⊗ pb')) ∘ σ-block) ∘ ((id ⊗ (id ⊗ pa)) ∘ σ-block)
  -- where pY = permute (map⁺ vlab (trans refl Y₂))
  --          = permute (map⁺ vlab Y₂) ∘ permute (map⁺ vlab refl)
  --          = permute (map⁺ vlab Y₂) ∘ id
  --          ≈Term permute (map⁺ vlab Y₂).
  --
  -- After collapse, permute p ≈Term permute q.  Apply self-rec.
  rfr-B-prep-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {tail''}
      uniq a b' (Perm.trans Perm.refl Y₂) _ _ self-rec =
    let p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' (Perm.swap k k'' b'))
                (Perm.trans Perm.refl Y₂))
        q = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y₂)
        A = size (Perm.swap k k' a)
        B = size (Perm.prep k' (Perm.swap k k'' b'))
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
  -- Y₁' : (k'' ∷ k ∷ tail'') ↭ ms'.
  -- Y₂ : (k' ∷ ms') ↭ (k ∷ k' ∷ rest).
  --
  -- Two `prep k'`'s at the same outer level fuse via prep-fusion:
  --   p = trans (swap k k' a) (trans (prep k' (swap k k'' b'))
  --                              (trans (prep k' Y₁') Y₂))
  --   q = trans (swap k k' a) (trans (prep k' (trans (swap k k'' b') Y₁')) Y₂)
  --
  -- size q < size p (diff 1).
  -- permute p ≈Term permute q via assoc + ⊗-∘-dist⁻¹ + idˡ collapse.
  rfr-B-prep-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {tail''}
      uniq a b' (Perm.trans (Perm.prep .k' Y₁') Y₂) _ _ self-rec =
    let p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' (Perm.swap k k'' b'))
                (Perm.trans (Perm.prep k' Y₁') Y₂))
        q = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k'
                (Perm.trans (Perm.swap k k'' b') Y₁')) Y₂)
        sa  = size a
        sb' = size b'
        sY₁' = size Y₁'
        sY₂  = size Y₂
        size-<-q : size q < size p
        size-<-q = size-Y-trans-prep-fusion-< sa sb' sY₁' sY₂
        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q} {l₂ = total-l p}
                       {c₁ = swap-count q} {c₂ = swap-count p}
                       size-<-q
        ih = self-rec q sub-≪
        -- Bridge: permute p ≈Term permute q.
        --
        -- permute p
        --   = ((pY₂ ∘ (id ⊗ pY₁')) ∘ (id ⊗ pSW_kk'')) ∘ pSW_kk'
        --   where pSW_kk'' = permute (map⁺ vlab (swap k k'' b'))
        --         pSW_kk'  = permute (map⁺ vlab (swap k k' a))
        --
        -- permute q
        --   = (pY₂ ∘ (id ⊗ (pY₁' ∘ pSW_kk''))) ∘ pSW_kk'
        --
        -- Bridge: (pY₂ ∘ (id ⊗ pY₁')) ∘ (id ⊗ pSW_kk'')
        --     ≈ pY₂ ∘ ((id ⊗ pY₁') ∘ (id ⊗ pSW_kk''))      (assoc)
        --     ≈ pY₂ ∘ ((id ∘ id) ⊗ (pY₁' ∘ pSW_kk''))      (⊗-∘-dist⁻¹)
        --     ≈ pY₂ ∘ (id ⊗ (pY₁' ∘ pSW_kk''))             (idˡ inside ⊗)
        bridge : permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
        bridge =
          ∘-resp-≈
            (≈-Term-trans assoc
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                  (⊗-resp-≈ idˡ ≈-Term-refl))))
            ≈-Term-refl
    in ≈-Term-trans bridge ih

  -- Sub-case Y₁ = swap x y Y₁' : dispatch to bpsy-Y-trans-swap.
  --
  -- Y = trans (swap x y Y₁') Y₂.
  -- Y₁ = swap x y Y₁' : (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys).
  -- LHS of Y : (k' ∷ k'' ∷ k ∷ tail''), so x = k', y = k'',
  -- xs = (k ∷ tail'').
  -- Y₁' : (k ∷ tail'') ↭ ys, so ms = k'' ∷ k' ∷ ys.
  -- Y₂ : (k'' ∷ k' ∷ ys) ↭ (k ∷ k' ∷ rest).
  rfr-B-prep-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {tail''}
      uniq a b' (Perm.trans (Perm.swap .k' .k'' Y₁') Y₂) acc-p norm self-rec =
    bpsy-Y-trans-swap vlab uniq a b' Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = trans _ _ : IMPOSSIBLE via norm.
  --
  -- total-l p
  --   = total-l a + total-l b' + total-l Y
  --   = ... + total-l (trans (trans _ _) _)
  --   = ... + suc (...) > 0
  -- contradicts norm ≡ 0.
  rfr-B-prep-swap-closed vlab {k} {k'} {k''} {rest} {rest''} {tail''}
      uniq a b' (Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂) _ norm _ =
    let Y = Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂
        tl-Y-eq : total-l Y ≡ 0
        tl-Y-eq = total-l-bprep-swap-extract-Y a b' Y norm
    in ⊥-elim (suc-non-zero tl-Y-eq)

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `BPrepSwapByYResidual` — a STRICTLY NARROWER residual record
--     with ONE field (the genuine Yang-Baxter braid sub-case
--     `Y = trans (swap _ _ _) _`).
--
--   * `rfr-B-prep-swap-closed` (in `module WithBPrepSwapByYResidual`) —
--     a function with the EXACT signature of
--     `RealFinalResidual.rfr-B-prep-swap`, parameterized by
--     `BPrepSwapByYResidual`.
--
-- ## Discharge status
--
--   * Y = refl:                       CLOSED via ⊥-elim from Unique.
--   * Y = prep _ _:                   CLOSED via ⊥-elim from Unique.
--   * Y = swap _ _ _:                 CLOSED via ⊥-elim from Unique+a.
--   * Y = trans refl Y₂:              CLOSED via self-rec (size strict).
--   * Y = trans (prep _ _) Y₂:        CLOSED via self-rec (prep-fusion).
--   * Y = trans (swap _ _ _) Y₂:      NARROWED (dispatch to bpsy-Y-trans-swap).
--   * Y = trans (trans _ _) Y₂:       CLOSED via ⊥-elim from norm.
--
-- ## FreeMonoidal lemmas used
--
-- The closure here uses structural case-splits, ⊥-elim from
-- Unique (refl/prep/swap/trans-trans), ⊥-elim from norm (trans-trans),
-- size-strict descent (trans-refl, trans-prep) via self-rec with
-- assoc + ⊗-∘-dist + idˡ + idʳ bridges.  No `hexagon`,
-- `σ-block-natural₃`, or `σ-block-hexagon` equational lemmas were
-- needed at the discharge level.  The remaining sub-residual
-- (Y = trans (swap _ _ _) _) contains the genuine Yang-Baxter algebra.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BPrepSwapByYResidual` record.
--------------------------------------------------------------------------------
