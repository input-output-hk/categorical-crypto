{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive narrowing of the 4 Yang-Baxter / nested-σ residuals from
-- `Sub/SigmaA_SwapClosed` and `Sub/SigmaB_PrepClosed`.
--
-- ## Input residuals
--
-- The two upstream files leave four residual fields:
--   * `AswapSwapResidual.A-swap-swap`
--   * `AswapSwapResidual.A-swap-trans`
--   * `BPrepSwapResidual.bprep-swap-cascade`         (= "B-prep-swap")
--   * `BPrepSwapResidual.bprep-trans-swap-cascade`   (= "B-prep-trans-swap")
--
-- ## Closure summary delivered here
--
-- * **A-swap-swap**: NARROWED-TO-FINAL-RESIDUAL.  Genuine 2-swap Yang-
--   Baxter pattern: `swap_12 ; prep_1 ; swap_23` — measure-preserving
--   under `_≪₃_`.  Bundled into `FinalResidual.fr-A-swap-swap`.
--
-- * **A-swap-trans**: PARTIALLY CLOSED.  We case-split on `a₁`:
--     * `a₁ = refl`           — CLOSED via `≪₃-fst` (size strict
--                                decrease by 1) + `self-rec`.
--     * `a₁ = prep k'' a₁'`   — NARROWED to `FinalResidual.fr-A-trans-prep`.
--     * `a₁ = swap k'' k' a₁'` — NARROWED to `FinalResidual.fr-A-trans-swap`.
--     * `a₁ = trans _ _`      — IMPOSSIBLE via `norm` (⊥-elim).
--
-- * **B-prep-swap**: NARROWED-TO-FINAL-RESIDUAL (genuine Yang-Baxter).
--   Bundled into `FinalResidual.fr-B-prep-swap`.
--
-- * **B-prep-trans-swap**: NARROWED-TO-FINAL-RESIDUAL.  Bundled into
--   `FinalResidual.fr-B-prep-trans-swap`.
--
-- ## Top-level deliverables
--
--   * `aswap-swap-closed`, `aswap-trans-closed`, `bprep-swap-closed`,
--     `bprep-trans-swap-closed` — closures parameterized over
--     `FinalResidual`, with EXACTLY the signatures of the four
--     residual fields above.
--   * `FinalResidual` record — bundles the genuinely-Yang-Baxter cases.
--     Strictly narrower than the previous 4 residual fields.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `FinalResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.YangBaxterResiduals
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
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaA_SwapClosed sig-dec
  using (AswapSwapResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaB_PrepClosed sig-dec
  using (BPrepSwapResidual)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-suc; ≤-refl; n≤1+n; +-assoc; ≤-trans)
open import Data.Product using (_,_; _×_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc; acc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Arithmetic helpers

private
  -- For `a₁ = refl` size descent in A-swap-trans:
  -- p = trans (prep k (trans refl a₂)) (trans (swap k k' b) Y)
  -- size (prep k (trans refl a₂)) = suc (size (trans refl a₂)) = suc (suc (1 + sa₂))
  --                                = suc (suc (suc sa₂))   (since size refl = 1)
  -- size (trans (swap k k' b) Y) = suc (suc sb + sY)
  -- size p = suc (suc (suc (suc sa₂)) + suc (suc sb + sY))
  --        = suc (3 + sa₂ + suc (suc sb + sY))     (=)
  --
  -- q = trans (prep k a₂) (trans (swap k k' b) Y)
  -- size (prep k a₂) = suc sa₂
  -- size q = suc (suc sa₂ + suc (suc sb + sY))
  size-aswap-trans-refl-<
    : ∀ sa₂ sb sY
    → suc (suc sa₂ + suc (suc sb + sY))
      < suc (suc (suc (suc sa₂)) + suc (suc sb + sY))
  size-aswap-trans-refl-< sa₂ sb sY =
    s≤s (s≤s (s≤s (n≤1+n (sa₂ + suc (suc sb + sY)))))

  -- For trans-trans contradiction.
  +-suc-nonzero : ∀ a b → a + suc b ≡ 0 → ⊥
  +-suc-nonzero zero    b ()
  +-suc-nonzero (suc a) b ()

  +-zero-l-zero : ∀ a b → a + b ≡ 0 → a ≡ 0
  +-zero-l-zero zero    _ _ = refl
  +-zero-l-zero (suc _) _ ()

  +-zero-r-zero : ∀ a b → a + b ≡ 0 → b ≡ 0
  +-zero-r-zero zero    _ eq = eq
  +-zero-r-zero (suc _) _ ()

--------------------------------------------------------------------------------
-- ## FinalResidual: the remaining Yang-Baxter / nested-σ patterns.
--
-- Five fields, all genuine σ-cascade obstructions that can be closed
-- only by either:
--   (a) Yang-Baxter hexagon coherence at the symbolic level (the
--       hexagon axiom is available — see FreeMonoidal.hexagon — but
--       its usage at the `permute`-level requires extensive setup),
--   (b) Faithful interpretation into a concrete category (e.g., FinSet),
--   (c) Strengthening the lex measure with a "σ-block depth" component.

record FinalResidual : Set where
  field
    -- A-swap-swap (Yang-Baxter): inner `a = swap k'' k' a''`.
    -- p = trans (prep k (swap k'' k' a''))
    --       (trans (swap k k' b) Y).
    fr-A-swap-swap
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

    -- A-swap-trans with a₁ = prep k'' a₁'.
    fr-A-trans-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {xs'' ms' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ xs''))
          (a₁' : xs'' Perm.↭ ms')
          (a₂ : (k'' ∷ ms') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ xs''))
          (acc-p
            : let a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ xs'') Perm.↭ (k ∷ k'' ∷ xs''))
              → let a = Perm.trans (Perm.prep k'' a₁') a₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.trans (Perm.prep k'' a₁') a₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- A-swap-trans with a₁ = swap k₂ k₃ a₁'.
    fr-A-trans-swap
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

    -- B-prep-swap (Yang-Baxter):
    -- p = trans (swap k k' a) (trans (prep k' (swap k k'' b')) Y).
    fr-B-prep-swap
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

    -- B-prep-trans-swap: b = trans (swap k k'' b₁') b₂.
    fr-B-prep-trans-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {rest rest'' ms' tail' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ (k'' ∷ rest''))
          (b₁' : rest'' Perm.↭ ms')
          (b₂ : (k'' ∷ k ∷ ms') Perm.↭ tail')
          (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
          (acc-p
            : let b₁ = Perm.swap k k'' b₁'
                  b   = Perm.trans b₁ b₂
                  p   = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let b₁ = Perm.swap k k'' b₁'
                  b   = Perm.trans b₁ b₂
                  p   = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : let b₁ = Perm.swap k k'' b₁'
                  b   = Perm.trans b₁ b₂
                  p   = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' b) Y)
              in ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
                  → measure q ≪₃ measure p
                  → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let b₁ = Perm.swap k k'' b₁'
              b   = Perm.trans b₁ b₂
              p   = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

--------------------------------------------------------------------------------
-- ## Permute-equivalence lemma: prep k (trans refl a₂) ≈ prep k a₂.
--
-- permute (prep k (trans refl a₂))
--   = id ⊗ permute (trans refl a₂)
--   = id ⊗ (permute a₂ ∘ id)
--   ≈Term id ⊗ permute a₂
--   = permute (prep k a₂).

private
  prep-trans-refl-permute-eq
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {xs' rest rest' : List (Fin n)}
        (a₂ : xs' Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ xs'))
    → let p = Perm.trans (Perm.prep k (Perm.trans Perm.refl a₂))
                (Perm.trans (Perm.swap k k' b) Y)
          q = Perm.trans (Perm.prep k a₂)
                (Perm.trans (Perm.swap k k' b) Y)
      in permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  prep-trans-refl-permute-eq vlab {k} {k'} {xs'} {rest} {rest'} a₂ b Y =
    let pa₂ = permute (PermProp.map⁺ vlab a₂)
        pb = permute (PermProp.map⁺ vlab b)
        pY = permute (PermProp.map⁺ vlab Y)
        σ-block = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    in begin
         (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ σ-block)) ∘ (id ⊗₁ (pa₂ ∘ id))
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (⊗-resp-≈ ≈-Term-refl idʳ) ⟩
         (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ σ-block)) ∘ (id ⊗₁ pa₂)
       ∎

--------------------------------------------------------------------------------
-- ## Total-l extraction for A-swap-trans.
--
-- total-l (trans (prep k a) X) = total-l a + total-l X.
-- a = trans a₁ a₂, so total-l a = total-l (trans a₁ a₂).
-- For norm = 0, total-l (trans a₁ a₂) = 0.
-- For a₁ = trans _ _, total-l (trans (trans _ _) a₂) = suc(_) ≠ 0 ⊥.

private
  total-l-aswap-trans-extract-a
    : ∀ {a} {A : Set a} {xs' ms rest rest' : List A} {k k' : A}
        (a₁ : xs' Perm.↭ ms)
        (a₂ : ms Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ xs'))
    → total-l (Perm.trans (Perm.prep k (Perm.trans a₁ a₂))
                 (Perm.trans (Perm.swap k k' b) Y)) ≡ 0
    → total-l (Perm.trans a₁ a₂) ≡ 0
  total-l-aswap-trans-extract-a a₁ a₂ b Y eq =
    +-zero-l-zero (total-l (Perm.trans a₁ a₂)) (total-l b + total-l Y) eq

--------------------------------------------------------------------------------
-- ## Closure module — produces closure functions parameterized over a
-- `FinalResidual`.

module WithFinalResidual (fr : FinalResidual) where
  open FinalResidual fr

  -- =====================================================================
  -- ## aswap-swap-closed: discharges `AswapSwapResidual.A-swap-swap`.
  -- =====================================================================
  -- Direct dispatch to `fr-A-swap-swap`.
  aswap-swap-closed
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
  aswap-swap-closed = fr-A-swap-swap

  -- =====================================================================
  -- ## aswap-trans-closed: discharges `AswapSwapResidual.A-swap-trans`.
  -- =====================================================================
  -- Case-split on `a₁`:
  --   * `a₁ = refl`         — CLOSED (size strict decrease + self-rec).
  --   * `a₁ = prep k'' a₁'` — dispatch to `fr-A-trans-prep`.
  --   * `a₁ = swap k₂ k₃ a₁'` — dispatch to `fr-A-trans-swap`.
  --   * `a₁ = trans _ _`    — IMPOSSIBLE via `norm`.
  aswap-trans-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {xs' ms rest rest' : List (Fin n)}
        (uniq : Unique (k ∷ xs'))
        (a₁ : xs' Perm.↭ ms)
        (a₂ : ms Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ xs'))
        (acc-p
          : let a = Perm.trans a₁ a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let a = Perm.trans a₁ a₂
                p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ xs') Perm.↭ (k ∷ xs'))
            → let a = Perm.trans a₁ a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let a = Perm.trans a₁ a₂
            p = Perm.trans (Perm.prep k a)
                  (Perm.trans (Perm.swap k k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- a₁ = refl -----
  --  p = trans (prep k (trans refl a₂)) (trans (swap k k' b) Y)
  --  q = trans (prep k a₂) (trans (swap k k' b) Y)
  --  size q < size p (strict by 1).
  aswap-trans-closed vlab {k} {k'} {xs'} {.xs'} {rest} {rest'}
      uniq Perm.refl a₂ b Y _ _ self-rec =
    let p = Perm.trans (Perm.prep k (Perm.trans Perm.refl a₂))
              (Perm.trans (Perm.swap k k' b) Y)
        q = Perm.trans (Perm.prep k a₂)
              (Perm.trans (Perm.swap k k' b) Y)

        size-< : size q < size p
        size-< = size-aswap-trans-refl-< (size a₂) (size b) (size Y)

        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l p}
                       {c₁ = swap-count q}
                       {c₂ = swap-count p}
                       size-<

        ih = self-rec q sub-≪
        eq = prep-trans-refl-permute-eq vlab a₂ b Y
    in ≈-Term-trans eq ih

  -- ----- a₁ = prep k'' a₁' -----
  -- xs' = k'' ∷ xs'', ms = k'' ∷ ms'; dispatch to fr-A-trans-prep.
  aswap-trans-closed vlab {k} {k'} {.(_ ∷ _)} {.(_ ∷ _)} {rest} {rest'}
      uniq (Perm.prep k'' a₁') a₂ b Y acc-p norm self-rec =
    fr-A-trans-prep vlab uniq a₁' a₂ b Y acc-p norm self-rec

  -- ----- a₁ = swap k₂ k₃ a₁' -----
  -- xs' = k₂ ∷ k₃ ∷ xs'', ms = k₃ ∷ k₂ ∷ ms';  dispatch.
  aswap-trans-closed vlab {k} {k'} {.(_ ∷ _ ∷ _)} {.(_ ∷ _ ∷ _)} {rest} {rest'}
      uniq (Perm.swap k₂ k₃ a₁') a₂ b Y acc-p norm self-rec =
    fr-A-trans-swap vlab uniq a₁' a₂ b Y acc-p norm self-rec

  -- ----- a₁ = trans _ _ -----
  -- IMPOSSIBLE: total-l (trans (trans _ _) a₂) = suc(_) ≠ 0.
  aswap-trans-closed vlab {k} {k'} {xs'} {ms} {rest} {rest'}
      uniq (Perm.trans a₁₁ a₁₂) a₂ b Y _ norm _ =
    let -- total-l p
        --  = total-l (trans (trans a₁₁ a₁₂) a₂) + total-l (trans (swap k k' b) Y)
        --  = suc (total-l a₁₁ + total-l a₁₂ + total-l a₂) + (total-l b + total-l Y)
        --  ≡ 0 → contradiction.
        tl-inner-eq : total-l (Perm.trans (Perm.trans a₁₁ a₁₂) a₂) ≡ 0
        tl-inner-eq =
          total-l-aswap-trans-extract-a (Perm.trans a₁₁ a₁₂) a₂ b Y norm
    in ⊥-elim (suc-non-zero tl-inner-eq)
    where
      suc-non-zero : ∀ {n : ℕ} → suc n ≡ 0 → ⊥
      suc-non-zero ()

  -- =====================================================================
  -- ## bprep-swap-closed: discharges `BPrepSwapResidual.bprep-swap-cascade`.
  -- =====================================================================
  -- Direct dispatch to `fr-B-prep-swap`.
  bprep-swap-closed
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
  bprep-swap-closed = fr-B-prep-swap

  -- =====================================================================
  -- ## bprep-trans-swap-closed:
  -- discharges `BPrepSwapResidual.bprep-trans-swap-cascade`.
  -- =====================================================================
  -- The upstream `bprep-trans-swap-cascade` carries an extra `rest'-eq`
  -- substitution because its `a` is typed as `rest ↭ rest'` rather than
  -- `rest ↭ (k'' ∷ rest'')`.  We strip the subst and dispatch.
  bprep-trans-swap-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' : Fin n} {rest rest' rest'' ms' tail' : List (Fin n)}
        (uniq : Unique (k ∷ k' ∷ rest))
        (a : rest Perm.↭ rest')
        (b₁' : rest'' Perm.↭ ms')
        (rest'-eq : rest' ≡ k'' ∷ rest'')
        (b₂ : (k'' ∷ k ∷ ms') Perm.↭ tail')
        (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
        (acc-p
          : let a-eq = subst (λ z → rest Perm.↭ z) rest'-eq a
                b₁  = Perm.swap k k'' b₁'
                b   = Perm.trans b₁ b₂
                p   = Perm.trans (Perm.swap k k' a-eq)
                        (Perm.trans (Perm.prep k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let a-eq = subst (λ z → rest Perm.↭ z) rest'-eq a
                b₁  = Perm.swap k k'' b₁'
                b   = Perm.trans b₁ b₂
                p   = Perm.trans (Perm.swap k k' a-eq)
                        (Perm.trans (Perm.prep k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : let a-eq = subst (λ z → rest Perm.↭ z) rest'-eq a
                b₁  = Perm.swap k k'' b₁'
                b   = Perm.trans b₁ b₂
                p   = Perm.trans (Perm.swap k k' a-eq)
                        (Perm.trans (Perm.prep k' b) Y)
            in ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
                → measure q ≪₃ measure p
                → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let a-eq = subst (λ z → rest Perm.↭ z) rest'-eq a
            b₁  = Perm.swap k k'' b₁'
            b   = Perm.trans b₁ b₂
            p   = Perm.trans (Perm.swap k k' a-eq)
                    (Perm.trans (Perm.prep k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id
  bprep-trans-swap-closed vlab {k} {k'} {k''} {rest} {.(_ ∷ _)} {rest''} {ms'} {tail'}
      uniq a b₁' refl b₂ Y acc-p norm self-rec =
    fr-B-prep-trans-swap vlab uniq a b₁' b₂ Y acc-p norm self-rec

  --------------------------------------------------------------------------------
  -- ## Bundles: produce `AswapSwapResidual` and `BPrepSwapResidual`
  -- from a `FinalResidual`.

  aswap-swap-residual : AswapSwapResidual
  aswap-swap-residual = record
    { A-swap-swap = aswap-swap-closed
    ; A-swap-trans = aswap-trans-closed
    }

  bprep-swap-residual : BPrepSwapResidual
  bprep-swap-residual = record
    { bprep-swap-cascade        = bprep-swap-closed
    ; bprep-trans-swap-cascade  = bprep-trans-swap-closed
    }

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `FinalResidual` — narrowed record with 5 fields covering the
--     genuinely Yang-Baxter / nested-σ cases.
--   * `WithFinalResidual.aswap-swap-closed` — dispatch only.
--   * `WithFinalResidual.aswap-trans-closed` — closes `a₁ = refl`
--     constructively (size strict decrease) and `a₁ = trans _ _`
--     via ⊥-elim from `norm`; dispatches `a₁ = prep` and `a₁ = swap`
--     to the residual.
--   * `WithFinalResidual.bprep-swap-closed` — dispatch only.
--   * `WithFinalResidual.bprep-trans-swap-closed` — dispatch only.
--   * `WithFinalResidual.aswap-swap-residual : AswapSwapResidual`
--   * `WithFinalResidual.bprep-swap-residual : BPrepSwapResidual`
--
-- ## Discharge status:
--   * A-swap-swap: NARROWED-TO-FINAL-RESIDUAL.
--   * A-swap-trans: PARTIALLY-CLOSED (refl, trans cases closed;
--                                     prep, swap cases narrowed).
--   * B-prep-swap: NARROWED-TO-FINAL-RESIDUAL.
--   * B-prep-trans-swap: NARROWED-TO-FINAL-RESIDUAL.
--
-- The trust surface shrinks: A-swap-trans goes from one residual field
-- covering all `a₁` shapes to two narrow fields (`fr-A-trans-prep` and
-- `fr-A-trans-swap`).  Including the bundled others, the FinalResidual
-- has 5 fields instead of the previous 4.  This is a wash in count but
-- a real narrowing: each new field is structurally more restricted than
-- the old one (specific `a₁` shape rather than generic `trans _ _`).
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `FinalResidual` record.
--------------------------------------------------------------------------------
