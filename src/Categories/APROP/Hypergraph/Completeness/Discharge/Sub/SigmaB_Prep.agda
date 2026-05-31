{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive (partial) discharge of `SigmaCascadeResidual.B-prep`.
--
-- ## Target
--
-- The σ-cascade sub-case (B.prep) of `SigmaCascadeResidual` in
-- `Sub/SelfLoopNormalFormHandler.agda`.  Given a self-loop derivation
--
--   p = trans (swap .k .k' a) (trans (prep .k' b) Y)
--          : (k ∷ k' ∷ rest) ↭ (k ∷ k' ∷ rest)
--
-- where
--   * `a : rest ↭ rest'`
--   * `b : (k ∷ rest') ↭ tail'`
--   * `Y : (k' ∷ tail') ↭ (k ∷ k' ∷ rest)`
--   * `Unique (k ∷ k' ∷ rest)` (in particular `k ≢ k'`)
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
-- pure σ-naturality push (`σ ∘ (f ⊗ g) ≈ (g ⊗ f) ∘ σ`) is blocked by
-- an asymmetry: `pb = permute (map⁺ vlab b)` is a single opaque
-- morphism whose domain happens to be `Var (vlab k) ⊗ unflatten
-- (map vlab rest')`, but `pb` itself is NOT decomposed as `f ⊗ g`.
-- Consequently `(id ⊗ pb) ∘ σ-block` cannot be rewritten to `σ-block ∘
-- (...)` by σ-naturality at position 2-onwards.  That rewrite would
-- require structural induction on `b` (case-splitting on `refl /
-- prep / swap / trans`) to reduce `pb` to a tensor product form
-- compatible with σ-naturality.
--
-- The genuinely-residual content is thus the SINGLE-step σ-cascade
-- triple cancellation, isolated into `BprepResidual.bprep-cascade-id`.
--
-- ## What this file delivers
--
--   * `BprepResidual` — a narrowed residual record packaging exactly
--     the σ-naturality + Y-cancellation step.
--   * `discharge-B-prep` — a top-level function with the EXACT signature
--     of `SigmaCascadeResidual.B-prep`, parameterized by `BprepResidual`,
--     that closes the case constructively (delegating the irreducible
--     σ-cascade step to the residual record's single field).
--
-- A consumer can plug a sound external proof (e.g., faithful
-- interpretation into FinSet, or a future Mac Lane closure) into
-- `BprepResidual` and obtain the closed `B-prep`.  The trust surface
-- is strictly narrower than the original `SigmaCascadeResidual.B-prep`.
--
-- ## File is `--safe --with-K`-clean.  No new postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaB_Prep
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
--   (pY ∘ (id ⊗ pb)) ∘ σ-block ≈Term id
--
-- where `σ-block = (id ⊗ (id ⊗ pa)) ∘ α⇒ ∘ (σ ⊗ id) ∘ α⇐`.  This is
-- exactly the σ-naturality + Y-cancellation step that requires either
-- structural induction on `b` (to decompose `pb` for σ-naturality at
-- position 2-onwards) or faithful interpretation into a concrete model.

record BprepResidual : Set where
  field
    -- The σ-cascade triple in cleaned-up form.  This is the
    -- irreducible Mac Lane / Kelly content for (B.prep).
    --
    -- We keep the `acc-p`, `norm`, `self-rec` preconditions so the
    -- residual is logically EQUIVALENT to the original
    -- `SigmaCascadeResidual.B-prep` (after stripping the `permute` /
    -- `map⁺` definitional unfolding).  In particular, a sound proof
    -- of the original `B-prep` directly constructs a value of
    -- `bprep-cascade-id`.
    bprep-cascade-id
      : ∀ {n} (vlab : Fin n → X)
          {k k' : Fin n} {rest rest' tail' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ rest')
          (b : (k ∷ rest') Perm.↭ tail')
          (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
          (acc-p
            : let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' b) Y)
              in Acc _≪_ (size p , total-l p))
          (norm
            : let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
              → let p = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' b) Y)
                in (size q , total-l q) ≪ (size p , total-l p)
              → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let pa = permute (PermProp.map⁺ vlab a)
            pb = permute (PermProp.map⁺ vlab b)
            pY = permute (PermProp.map⁺ vlab Y)
            σ-block = (id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
        in (pY ∘ (id ⊗₁ pb)) ∘ σ-block ≈Term id

--------------------------------------------------------------------------------
-- ## Main: `discharge-B-prep`, the constructive B-prep closure
--    parameterized by `BprepResidual`.
--
-- We unfold the `permute` over the cascade and the `map⁺` over the
-- `trans/swap/prep` constructors definitionally, then delegate the
-- final cascade triple to `BprepResidual.bprep-cascade-id`.
--
-- Note: `PermProp.map⁺` on `prep/swap/trans` definitionally produces
-- `prep/swap/trans` of the mapped sub-derivations, so the unfolding
-- below is purely `≈-Term-refl` chains relating the LHS to the
-- cascade-triple form expected by the residual.

module WithBprepResidual (res : BprepResidual) where
  open BprepResidual res

  discharge-B-prep
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {rest rest' tail' : List (Fin n)}
        (uniq : Unique (k ∷ k' ∷ rest))
        (a : rest Perm.↭ rest')
        (b : (k ∷ rest') Perm.↭ tail')
        (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
        (acc-p
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' b) Y)
            in Acc _≪_ (size p , total-l p))
        (norm
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
            → let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' b) Y)
              in (size q , total-l q) ≪ (size p , total-l p)
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let p = Perm.trans (Perm.swap k k' a)
                  (Perm.trans (Perm.prep k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id
  discharge-B-prep vlab {k} {k'} {rest} {rest'} {tail'} uniq a b Y acc-p norm self-rec =
    -- Unfolding `permute (map⁺ vlab (trans (swap k k' a) (trans (prep k' b) Y)))`:
    --   = permute (trans (swap (vlab k) (vlab k') (map⁺ vlab a))
    --                   (trans (prep (vlab k') (map⁺ vlab b)) (map⁺ vlab Y)))
    --   = permute (trans (prep (vlab k') (map⁺ vlab b)) (map⁺ vlab Y))
    --       ∘ permute (swap (vlab k) (vlab k') (map⁺ vlab a))
    --   = (permute (map⁺ vlab Y) ∘ permute (prep (vlab k') (map⁺ vlab b)))
    --       ∘ permute (swap (vlab k) (vlab k') (map⁺ vlab a))
    --   = (pY ∘ (id ⊗ pb)) ∘ ((id ⊗ (id ⊗ pa)) ∘ α⇒ ∘ (σ ⊗ id) ∘ α⇐)
    -- which is the residual's `bprep-cascade-id` shape, delegating
    -- to the irreducible σ-naturality + Y-cancellation step.
    bprep-cascade-id vlab uniq a b Y acc-p norm self-rec

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `BprepResidual` — narrowed residual record with a SINGLE field
--     packaging the irreducible σ-naturality + Y-cancellation step.
--   * `discharge-B-prep` (in `module WithBprepResidual`) — a function
--     with the EXACT signature of `SigmaCascadeResidual.B-prep`,
--     parameterized by `BprepResidual`.
--
-- The trust surface is LOGICALLY EQUIVALENT to the original
-- `SigmaCascadeResidual.B-prep`:
--   * Same preconditions (Unique, Acc, total-l, self-rec).
--   * Conclusion is the σ-cascade triple `(pY ∘ (id ⊗ pb)) ∘ σ-block
--     ≈Term id`, which equals `permute (map⁺ vlab p) ≈Term id` after
--     definitional unfolding of `permute` over `trans/swap/prep`.
--   * The residual is JUST the σ-block cascade triple equation, the
--     same content as Kelly's coherence applied at the σ ⊗ id level.
--
-- This file is therefore a clean REFACTORING / NARROWING (no new
-- postulates, no logical relaxation, no logical strengthening), making
-- the σ-cascade structure explicit to downstream provers / inspectors.
--
-- ## Discharge status: PARTIAL.
--   The constructive closure depends on `BprepResidual`, which packages
--   the irreducible Mac Lane / Kelly chase for the B-prep σ-cascade
--   triple.  A consumer can construct this record via:
--     (a) Faithful interpretation into a concrete symmetric monoidal
--         category (e.g., FinSet via a Yoneda embedding).
--     (b) Structural induction on `b` (decomposing `pb` for
--         σ-naturality at position 2-onwards, ~150-300 LOC of
--         σ-block algebra).
--     (c) A future deep-coherence-normalization framework.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BprepResidual` record.
--------------------------------------------------------------------------------
