{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Case-on-Y closure for `RealFinalResidual.rfr-A-swap-swap` from
-- `Sub/YangBaxterClosure.agda`.
--
-- ## Target
--
-- The σ-cascade self-loop
--
--   p = trans (prep k a) (trans (swap k k' b) Y)
--     : (k ∷ k'' ∷ k' ∷ ms) ↭ (k ∷ k'' ∷ k' ∷ ms)
--
-- with
--   * `a = swap k'' k' a''`
--   * `a'' : ms ↭ ms'`
--   * `b : (k'' ∷ ms') ↭ rest'`
--   * `Y : (k' ∷ k ∷ rest') ↭ (k ∷ k'' ∷ k' ∷ ms)`
--   * `Unique (k ∷ k'' ∷ k' ∷ ms)`
--   * `total-l p ≡ 0` (normal form).
--   * `self-rec` enabling lex descent.
--
-- ## Strategy: case-split on Y.
--
-- Since `Y` has type `(k' ∷ k ∷ rest') ↭ (k ∷ k'' ∷ k' ∷ ms)`, the
-- LHS head is `k'` but the RHS head is `k`.  Pattern-matching forces:
--
--   * `Y = refl`:           `k' ≡ k`           → ⊥ via Unique.
--   * `Y = prep x Y'`:      head `x = k' = k`  → ⊥ via Unique.
--   * `Y = swap x y Y'`:    `(x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys)` forces
--                           `x = k' = k''` and `y = k = k`, so `k' ≡ k''`.
--                           Unique `(k ∷ k'' ∷ k' ∷ ms)` gives `k'' ≢ k'`.  ⊥.
--   * `Y = trans Y₁ Y₂`:    further case-split on `Y₁`:
--       - `Y₁ = refl`:      collapse `trans refl Y₂ ≡ Y₂` and recurse
--                           via `self-rec` on a size-strict subproblem.
--       - `Y₁ = prep x p`:  dispatch to narrower residual (no prep-fusion
--                           is available here because the outer prep is
--                           `prep k`, not `prep k'`).
--       - `Y₁ = swap x y p`: dispatch to narrower residual.
--       - `Y₁ = trans _ _`: ⊥ via norm (top-level `trans (trans _ _) _`
--                           contributes a `suc` to `total-l`).
--
-- ## What this file delivers
--
--   * `ASwapSwapByYResidual` — narrower residual record with the
--     TWO remaining (non-discharged) Y-shape sub-cases:
--       1. `aswap-swap-Y-trans-prep`  : Y = trans (prep _ _) Y₂.
--       2. `aswap-swap-Y-trans-swap`  : Y = trans (swap _ _ _) Y₂.
--
--   * `rfr-A-swap-swap-closed` — function with the EXACT signature of
--     `RealFinalResidual.rfr-A-swap-swap`, dispatching the
--     discharge-able Y-cases (⊥-elim, size-strict via self-rec) and
--     forwarding the non-discharge-able cases to the residual fields.
--
-- ## Why this is strictly narrower than `rfr-A-swap-swap`
--
-- The original `rfr-A-swap-swap` quantifies uniformly over ALL `Y`
-- shapes.  The narrowed residual `ASwapSwapByYResidual` has TWO
-- structurally-tight fields (Y = trans (prep _ _) Y₂ and
-- Y = trans (swap _ _ _) Y₂, the genuine Yang-Baxter cascade
-- sub-cases that interact with the outer `prep k` differently).
--
-- The following cases are CONSTRUCTIVELY eliminated:
--   * Y = refl:                    contradict `Unique` (k ≡ k').
--   * Y = prep _ _:                contradict `Unique` via head match.
--   * Y = swap _ _ _:              contradict `Unique` via swap RHS/LHS
--                                  unification forcing k'' ≡ k'.
--   * Y = trans refl _:            collapses via `self-rec` (size strict).
--   * Y = trans (trans _ _) _:     contradicts `norm` (total-l increment).
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `ASwapSwapByYResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ASwapSwapByCaseY
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
  --   A = size (prep k a)           = suc (size a) = suc (suc sa'')
  --   B = size (swap k k' b)         = suc (size b)
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
-- ## Helper: `All-∈` from `Any-∈`.

private
  -- If `All P xs` and `x ∈ xs`, then `P x`.
  All-∈ : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} {x : A}
        → All P xs → x ∈ xs → P x
  All-∈ (px ∷ _) (here refl)  = px
  All-∈ (_ ∷ ps) (there x∈xs) = All-∈ ps x∈xs

--------------------------------------------------------------------------------
-- ## Total-l extractor for the A-swap-swap cascade.
--
-- total-l p where p = trans (prep k (swap k'' k' a'')) (trans (swap k k' b) Y)
--
-- Computing:
--   total-l (trans (prep k a) Z)
--     = total-l a + total-l Z                          (prep left)
--     = total-l (swap k'' k' a'') + total-l Z
--     = total-l a'' + total-l Z                        (swap inner)
--   total-l (trans (swap k k' b) Y)
--     = total-l b + total-l Y                          (swap left)
-- So:
--   total-l p = total-l a'' + (total-l b + total-l Y)

private
  total-l-aswap-swap-extract-Y
    : ∀ {a} {A : Set a}
        {ms ms' rest' : List A} {k k' k'' : A}
        (a'' : ms Perm.↭ ms')
        (b : (k'' ∷ ms') Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ k' ∷ ms))
    → total-l (Perm.trans (Perm.prep k (Perm.swap k'' k' a''))
                 (Perm.trans (Perm.swap k k' b) Y)) ≡ 0
    → total-l Y ≡ 0
  total-l-aswap-swap-extract-Y a'' b Y eq =
    let inner = total-l b + total-l Y
        outer-eq : total-l a'' + inner ≡ 0
        outer-eq = eq
        inner-eq : inner ≡ 0
        inner-eq = +-zero-r-zero (total-l a'') inner outer-eq
    in +-zero-r-zero (total-l b) (total-l Y) inner-eq

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- Two fields for the non-discharged Y-shape sub-cases (after
-- refl/prep/swap/trans-refl/trans-trans are all closed constructively).

record ASwapSwapByYResidual : Set where
  field
    -- =================================================================
    -- Case Y = trans (prep .k' Y₁') Y₂.
    --
    -- Y : (k' ∷ k ∷ rest') ↭ (k ∷ k'' ∷ k' ∷ ms).
    -- Y = trans Y₁ Y₂ with Y₁ = prep x Y₁'.
    -- Y₁ : (k' ∷ k ∷ rest') ↭ ms₁, with Y₁ = prep .k' Y₁'.
    -- So ms₁ = k' ∷ ms₁', Y₁' : (k ∷ rest') ↭ ms₁'.
    -- Y₂ : (k' ∷ ms₁') ↭ (k ∷ k'' ∷ k' ∷ ms).
    -- =================================================================
    aswap-swap-Y-trans-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {ms ms' rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k' ∷ ms))
          (a'' : ms Perm.↭ ms')
          (b : (k'' ∷ ms') Perm.↭ rest')
          (Y₁' : (k ∷ rest') Perm.↭ ms₁')
          (Y₂ : (k' ∷ ms₁') Perm.↭ (k ∷ k'' ∷ k' ∷ ms))
          (acc-p
            : let a = Perm.swap k'' k' a''
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.swap k'' k' a''
                  Y = Perm.trans (Perm.prep k' Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k' ∷ ms) Perm.↭ (k ∷ k'' ∷ k' ∷ ms))
              → let a = Perm.swap k'' k' a''
                    Y = Perm.trans (Perm.prep k' Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.swap k'' k' a''
              Y = Perm.trans (Perm.prep k' Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- =================================================================
    -- Case Y = trans (swap x y Y₁') Y₂.
    --
    -- Y : (k' ∷ k ∷ rest') ↭ (k ∷ k'' ∷ k' ∷ ms).
    -- Y = trans Y₁ Y₂ with Y₁ = swap x y Y₁'.
    -- Y₁ : (k' ∷ k ∷ rest') ↭ ms₁, with Y₁ = swap .k' .k Y₁'.
    -- So ms₁ = k ∷ k' ∷ ms₁', Y₁' : rest' ↭ ms₁'.
    -- Y₂ : (k ∷ k' ∷ ms₁') ↭ (k ∷ k'' ∷ k' ∷ ms).
    -- =================================================================
    aswap-swap-Y-trans-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {ms ms' rest' ms₁' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k' ∷ ms))
          (a'' : ms Perm.↭ ms')
          (b : (k'' ∷ ms') Perm.↭ rest')
          (Y₁' : rest' Perm.↭ ms₁')
          (Y₂ : (k ∷ k' ∷ ms₁') Perm.↭ (k ∷ k'' ∷ k' ∷ ms))
          (acc-p
            : let a = Perm.swap k'' k' a''
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.swap k'' k' a''
                  Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k' ∷ ms) Perm.↭ (k ∷ k'' ∷ k' ∷ ms))
              → let a = Perm.swap k'' k' a''
                    Y = Perm.trans (Perm.swap k' k Y₁') Y₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.swap k'' k' a''
              Y = Perm.trans (Perm.swap k' k Y₁') Y₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

--------------------------------------------------------------------------------
-- ## Main: `rfr-A-swap-swap-closed`.
--
-- Case-split on `Y`.

module WithASwapSwapByYResidual (res : ASwapSwapByYResidual) where
  open ASwapSwapByYResidual res

  rfr-A-swap-swap-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' : Fin n} {ms ms' rest' : List (Fin n)}
        (uniq : Unique (k ∷ k'' ∷ k' ∷ ms))
        (a'' : ms Perm.↭ ms')
        (b : (k'' ∷ ms') Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ k' ∷ ms))
        (acc-p
          : let a = Perm.swap k'' k' a''
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let a = Perm.swap k'' k' a''
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k'' ∷ k' ∷ ms) Perm.↭ (k ∷ k'' ∷ k' ∷ ms))
            → let a = Perm.swap k'' k' a''
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let a = Perm.swap k'' k' a''
            p = Perm.trans (Perm.prep k a)
                  (Perm.trans (Perm.swap k k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case Y = Perm.refl -----
  --
  -- Y : (k' ∷ k ∷ rest') ↭ (k ∷ k'' ∷ k' ∷ ms)
  -- Y = refl forces (k' ∷ k ∷ rest') ≡ (k ∷ k'' ∷ k' ∷ ms).
  -- Then k' ≡ k (and k ≡ k'', rest' = k' ∷ ms), but
  -- Unique (k ∷ k'' ∷ k' ∷ ms) gives k ≠ k''.
  -- Wait: k' ≡ k contradicts directly via the first All:
  --   (k ≢ k'' ∷ k ≢ k' ∷ k ≢ ms ...) ∷ ...
  -- The second element k ≢ k' (matching positions of `k` and `k'`
  -- in `k ∷ k'' ∷ k' ∷ ms`) — but Y refl forces k' ≡ k, so we get
  -- k ≢ k applied to refl.
  --
  -- After Y = refl unification: k' ↦ k, k ↦ k'', rest' ↦ k' ∷ ms.
  -- Substituting back into Unique: Unique (k ∷ k'' ∷ k' ∷ ms) becomes
  -- Unique (k'' ∷ k'' ∷ k ∷ ms) which is impossible.
  rfr-A-swap-swap-closed vlab {k} {.k} {.k} {ms} {ms'} {rest'}
      ((k≢k'' ∷ _) ∷ _ ∷ _) a'' b Perm.refl _ _ _ =
    ⊥-elim (k≢k'' refl)

  -- ----- Case Y = Perm.prep _ _ -----
  --
  -- Y = prep x Y' : (x ∷ xs) ↭ (x ∷ ys) means LHS head x ≡ k' and
  -- RHS head x ≡ k.  So k' ≡ k.
  -- Unique gives (k ≢ k'' ∷ k ≢ k' ∷ ...).  k ≡ k' contradicts k ≢ k'.
  rfr-A-swap-swap-closed vlab {k} {.k} {k''} {ms} {ms'} {rest'}
      ((_ ∷ k≢k' ∷ _) ∷ _ ∷ _) a'' b (Perm.prep .k _) _ _ _ =
    ⊥-elim (k≢k' refl)

  -- ----- Case Y = Perm.swap _ _ _ -----
  --
  -- Y = swap x y Y' : (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys).
  -- Matching LHS (k' ∷ k ∷ rest'): x = k', y = k.
  -- Matching RHS (k ∷ k'' ∷ k' ∷ ms): y = k, x = k''.
  -- So x = k' AND x = k''.  Hence k' ≡ k''.
  -- Inner Y' : (k ∷ rest') ↭ (k' ∷ ms).
  --
  -- Unique (k ∷ k'' ∷ k' ∷ ms) gives `_ ∷ (k''≢k' ∷ _) ∷ _`,
  -- where `k'' ≢ k'`.  Substituting k' ↦ k'' (or k'' ↦ k') yields
  -- `k'' ≢ k''` applied to refl.  ⊥.
  --
  -- We unify by pattern-matching: Y = swap .k' .k Y' with x ↦ k',
  -- and the RHS k '' must match k', i.e. we get the case k'' = k'.
  rfr-A-swap-swap-closed vlab {k} {k'} {.k'} {ms} {ms'} {rest'}
      (_ ∷ (k''≢k' ∷ _) ∷ _) a'' b (Perm.swap .k' .k Y') _ _ _ =
    ⊥-elim (k''≢k' refl)

  -- ----- Case Y = Perm.trans Y₁ Y₂ -----

  -- Sub-case Y₁ = refl: collapse trans refl Y₂ → Y₂.
  -- Build q with Y replaced by Y₂.  size-strict descent.
  --
  -- permute(map⁺ vlab p)
  --   = pY ∘ ((id ⊗ (id ⊗ pb)) ∘ σ-block) ∘ (id ⊗ pa)
  -- where pY = permute (map⁺ vlab (trans refl Y₂))
  --          = permute (map⁺ vlab Y₂) ∘ permute (map⁺ vlab refl)
  --          = permute (map⁺ vlab Y₂) ∘ id
  --          ≈Term permute (map⁺ vlab Y₂).
  --
  -- After collapse, permute p ≈Term permute q.  Apply self-rec.
  rfr-A-swap-swap-closed vlab {k} {k'} {k''} {ms} {ms'} {rest'}
      uniq a'' b (Perm.trans Perm.refl Y₂) _ _ self-rec =
    let a = Perm.swap k'' k' a''
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
        -- Bridge: permute p ≈Term permute q.
        --
        -- permute(map⁺ vlab p)
        --   = ((permute (map⁺ vlab Y₂) ∘ id) ∘ permute (swap k k' b))
        --       ∘ permute (prep k a)
        -- permute(map⁺ vlab q)
        --   = (permute (map⁺ vlab Y₂) ∘ permute (swap k k' b))
        --       ∘ permute (prep k a)
        -- Difference: `pY₂ ∘ id` vs `pY₂`.  Resolve via idʳ at depth 2.
        bridge : permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
        bridge = ∘-resp-≈ (∘-resp-≈ idʳ ≈-Term-refl) ≈-Term-refl
    in ≈-Term-trans bridge ih

  -- Sub-case Y₁ = prep .k' Y₁' : dispatch to aswap-swap-Y-trans-prep.
  --
  -- Y = trans (prep x Y₁') Y₂.
  -- Y₁ = prep x Y₁' : (x ∷ xs) ↭ (x ∷ ys), so x = k' (head of Y's LHS).
  -- Y₁' : (k ∷ rest') ↭ ms₁'.
  -- Y₂ : (k' ∷ ms₁') ↭ (k ∷ k'' ∷ k' ∷ ms).
  --
  -- No prep-fusion is available since the outer prep is `prep k`, not
  -- `prep k'`.  Defer to residual field.
  rfr-A-swap-swap-closed vlab {k} {k'} {k''} {ms} {ms'} {rest'}
      uniq a'' b (Perm.trans (Perm.prep .k' Y₁') Y₂) acc-p norm self-rec =
    aswap-swap-Y-trans-prep vlab uniq a'' b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = swap .k' .k Y₁' : dispatch to aswap-swap-Y-trans-swap.
  --
  -- Y = trans (swap x y Y₁') Y₂.
  -- Y₁ = swap x y Y₁' : (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys), so x = k', y = k.
  -- Y₁' : rest' ↭ ms₁', ms₁ = k ∷ k' ∷ ms₁'.
  -- Y₂ : (k ∷ k' ∷ ms₁') ↭ (k ∷ k'' ∷ k' ∷ ms).
  rfr-A-swap-swap-closed vlab {k} {k'} {k''} {ms} {ms'} {rest'}
      uniq a'' b (Perm.trans (Perm.swap .k' .k Y₁') Y₂) acc-p norm self-rec =
    aswap-swap-Y-trans-swap vlab uniq a'' b Y₁' Y₂ acc-p norm self-rec

  -- Sub-case Y₁ = trans _ _ : IMPOSSIBLE via norm.
  --
  -- total-l p
  --   = total-l a'' + (total-l b + total-l Y)
  --   = ... + total-l (trans (trans _ _) _)
  --   = ... + suc (...) > 0
  -- contradicts norm ≡ 0.
  rfr-A-swap-swap-closed vlab {k} {k'} {k''} {ms} {ms'} {rest'}
      uniq a'' b (Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂) _ norm _ =
    let Y = Perm.trans (Perm.trans Y₁₁ Y₁₂) Y₂
        tl-Y-eq : total-l Y ≡ 0
        tl-Y-eq = total-l-aswap-swap-extract-Y a'' b Y norm
    in ⊥-elim (suc-non-zero tl-Y-eq)

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `ASwapSwapByYResidual` — a STRICTLY NARROWER residual record
--     with TWO fields:
--       1. `aswap-swap-Y-trans-prep` (Y = trans (prep _ _) Y₂)
--       2. `aswap-swap-Y-trans-swap` (Y = trans (swap _ _ _) Y₂).
--
--   * `rfr-A-swap-swap-closed` (in `module WithASwapSwapByYResidual`) —
--     a function with the EXACT signature of
--     `RealFinalResidual.rfr-A-swap-swap`, parameterized by
--     `ASwapSwapByYResidual`.
--
-- ## Discharge status
--
--   * Y = refl:                       CLOSED via ⊥-elim from Unique.
--   * Y = prep _ _:                   CLOSED via ⊥-elim from Unique.
--   * Y = swap _ _ _:                 CLOSED via ⊥-elim from Unique.
--   * Y = trans refl Y₂:              CLOSED via self-rec (size strict).
--   * Y = trans (prep _ _) Y₂:        NARROWED to aswap-swap-Y-trans-prep
--                                     (no prep-fusion available because
--                                     outer prep is `prep k`, not the same
--                                     key as `prep k'` in Y₁).
--   * Y = trans (swap _ _ _) Y₂:      NARROWED to aswap-swap-Y-trans-swap.
--   * Y = trans (trans _ _) Y₂:       CLOSED via ⊥-elim from norm.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `ASwapSwapByYResidual` record.
--------------------------------------------------------------------------------
