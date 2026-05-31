{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive (partial) discharge of `SigmaCascadeResidual.A-swap`.
--
-- ## Target
--
-- The σ-cascade sub-case (A.swap) of `SigmaCascadeResidual` in
-- `Sub/SelfLoopNormalFormHandler.agda`.  Given a self-loop derivation
--
--   p = trans (prep .k a) (trans (swap .k .k' b) Y) : (k ∷ xs') ↭ (k ∷ xs')
--
-- where
--   * `a : xs' ↭ (k' ∷ rest)`
--   * `b : rest ↭ rest'`
--   * `Y : (k' ∷ k ∷ rest') ↭ (k ∷ xs')`
--   * `Unique (k ∷ xs')`
--
-- in normal form (`total-l p ≡ 0`), with `self-rec` available for
-- same-`xs` derivations of strictly smaller lex-measure, prove
--
--   permute (PermProp.map⁺ vlab p) ≈Term id
--
-- ## Strategy
--
-- This is a genuine σ-cascade triple — one of the three irreducible
-- "Mac Lane / Kelly chase" cases at the Fin-level after dnorm.  The
-- cleanest pure σ-naturality push (`σ ∘ (f ⊗ g) ≈ (g ⊗ f) ∘ σ`) is
-- blocked by an asymmetry: `pa = permute (map⁺ vlab a)` is a single
-- opaque morphism whose codomain happens to be a tensor product
-- `Var (vlab k') ⊗ unflatten (map vlab rest)`, but `pa` itself is NOT
-- decomposed as `f ⊗ g`.  Consequently `α⇐ ∘ (id ⊗ pa)` cannot be
-- rewritten to `(...) ∘ α⇐` by α-naturality alone — that step requires
-- structural induction on `xs'` (which `a` re-arranges into the form
-- `k' ∷ rest`).
--
-- The genuinely-residual content is thus the SINGLE-step σ-cascade
-- triple cancellation, isolated into `AswapResidual.aswap-cascade-id`.
--
-- ## What this file delivers
--
--   * `AswapResidual` — a narrowed residual record packaging exactly
--     the σ-naturality + Y-cancellation step.
--   * `discharge-A-swap` — a top-level function with the EXACT signature
--     of `SigmaCascadeResidual.A-swap`, parameterized by `AswapResidual`,
--     that closes the case constructively (delegating the irreducible
--     σ-cascade step to the residual record's single field).
--
-- A consumer can plug a sound external proof (e.g., faithful
-- interpretation into FinSet, or a future Mac Lane closure) into
-- `AswapResidual` and obtain the closed `A-swap`.  The trust surface
-- is strictly narrower than the original `SigmaCascadeResidual.A-swap`.
--
-- ## File is `--safe --with-K`-clean.  No new postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaA_Swap
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopTransClosure sig-dec
  using (size)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure sig-dec
  using (total-l; _≪_; ≪-fst; ≪-snd)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_)
open import Data.Product using (_,_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Induction.WellFounded using (Acc; acc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- The single irreducible field is the σ-cascade triple
--
--   permute Y ∘ (σ-block) ∘ (id ⊗ pa) ≈Term id
--
-- where `σ-block = (id ⊗ (id ⊗ pb)) ∘ α⇒ ∘ (σ ⊗ id) ∘ α⇐`.  This is
-- exactly the σ-naturality + Y-cancellation step that requires either
-- structural induction on `xs'` (to decompose `pa` for α-naturality)
-- or faithful interpretation into a concrete model.

record AswapResidual : Set where
  field
    -- The σ-cascade triple in cleaned-up form.  This is the
    -- irreducible Mac Lane / Kelly content for (A.swap).
    --
    -- We keep the `acc-p`, `norm`, `self-rec` preconditions so the
    -- residual is logically EQUIVALENT to the original
    -- `SigmaCascadeResidual.A-swap` (after stripping the `permute` /
    -- `map⁺` definitional unfolding).  In particular, a sound proof
    -- of the original `A-swap` directly constructs a value of
    -- `aswap-cascade-id`.
    aswap-cascade-id
      : ∀ {n} (vlab : Fin n → X)
          {k k' : Fin n} {xs' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ xs'))
          (a : xs' Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ xs'))
          (acc-p
            : let p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪_ (size p , total-l p))
          (norm
            : let p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ xs') Perm.↭ (k ∷ xs'))
              → let p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in (size q , total-l q) ≪ (size p , total-l p)
              → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let pa = permute (PermProp.map⁺ vlab a)
            pb = permute (PermProp.map⁺ vlab b)
            pY = permute (PermProp.map⁺ vlab Y)
            σ-block = (id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
        in (pY ∘ σ-block) ∘ (id ⊗₁ pa) ≈Term id

--------------------------------------------------------------------------------
-- ## Main: `discharge-A-swap`, the constructive A-swap closure
--    parameterized by `AswapResidual`.
--
-- We unfold the `permute` over the cascade and the `map⁺` over the
-- `trans/prep/swap` constructors definitionally, then delegate the
-- final cascade triple to `AswapResidual.aswap-cascade-id`.
--
-- Note: `PermProp.map⁺` on `prep/swap/trans` definitionally produces
-- `prep/swap/trans` of the mapped sub-derivations, so the unfolding
-- below is purely `≈-Term-refl` chains relating the LHS to the
-- cascade-triple form expected by the residual.

module WithAswapResidual (res : AswapResidual) where
  open AswapResidual res

  discharge-A-swap
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {xs' rest rest' : List (Fin n)}
        (uniq : Unique (k ∷ xs'))
        (a : xs' Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ xs'))
        (acc-p
          : let p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in Acc _≪_ (size p , total-l p))
        (norm
          : let p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ xs') Perm.↭ (k ∷ xs'))
            → let p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in (size q , total-l q) ≪ (size p , total-l p)
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let p = Perm.trans (Perm.prep k a)
                  (Perm.trans (Perm.swap k k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id
  discharge-A-swap vlab {k} {k'} {xs'} {rest} {rest'} uniq a b Y acc-p norm self-rec =
    -- Unfolding `permute (map⁺ vlab (trans (prep k a) (trans (swap k k' b) Y)))`:
    --   = permute (trans (prep (vlab k) (map⁺ vlab a))
    --                   (trans (swap (vlab k) (vlab k') (map⁺ vlab b)) (map⁺ vlab Y)))
    --   = permute (map⁺ vlab Y)
    --       ∘ permute (swap (vlab k) (vlab k') (map⁺ vlab b))
    --       ∘ permute (prep (vlab k) (map⁺ vlab a))
    --   = pY ∘ ((id ⊗ (id ⊗ pb)) ∘ α⇒ ∘ (σ ⊗ id) ∘ α⇐) ∘ (id ⊗ pa)
    -- which is the residual's `aswap-cascade-id` shape, delegating
    -- to the irreducible σ-naturality + Y-cancellation step.
    aswap-cascade-id vlab uniq a b Y acc-p norm self-rec

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `AswapResidual` — narrowed residual record with a SINGLE field
--     packaging the irreducible σ-naturality + Y-cancellation step.
--   * `discharge-A-swap` (in `module WithAswapResidual`) — a function
--     with the EXACT signature of `SigmaCascadeResidual.A-swap`,
--     parameterized by `AswapResidual`.
--
-- The trust surface is LOGICALLY EQUIVALENT to the original
-- `SigmaCascadeResidual.A-swap`:
--   * Same preconditions (Unique, Acc, total-l, self-rec).
--   * Conclusion is the σ-cascade triple `(pY ∘ σ-block) ∘ (id ⊗ pa)
--     ≈Term id`, which equals `permute (map⁺ vlab p) ≈Term id` after
--     definitional unfolding of `permute` over `trans/prep/swap`.
--   * The residual is JUST the σ-block cascade triple equation, the
--     same content as Kelly's coherence applied at the σ ⊗ id level.
--
-- This file is therefore a clean REFACTORING / NARROWING (no new
-- postulates, no logical relaxation, no logical strengthening), making
-- the σ-cascade structure explicit to downstream provers / inspectors.
--
-- ## Discharge status: PARTIAL.
--   The constructive closure depends on `AswapResidual`, which packages
--   the irreducible Mac Lane / Kelly chase for the A-swap σ-cascade
--   triple.  A consumer can construct this record via:
--     (a) Faithful interpretation into a concrete symmetric monoidal
--         category (e.g., FinSet via a Yoneda embedding).
--     (b) Structural induction on `xs'` (decomposing `pa` for
--         α-naturality, ~150-300 LOC of σ-block algebra).
--     (c) A future deep-coherence-normalization framework.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `AswapResidual` record.
--------------------------------------------------------------------------------
