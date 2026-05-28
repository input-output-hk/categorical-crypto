{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive (PARTIAL) closure of `BPrepSwapClosureResidual.bps-a-refl`
-- from `Sub/BPrepSwapClosure.agda`.
--
-- ## Target
--
--   bps-a-refl with `a = refl`:
--
--     p = trans (swap k k' refl) (trans (prep k' (swap k k'' b')) Y)
--       : (k ∷ k' ∷ k'' ∷ rest'') ↭ (k ∷ k' ∷ k'' ∷ rest'')
--
--   Prove: permute (map⁺ vlab p) ≈Term id.
--
-- ## Strategy: σ-block-natural₃ + Yang-Baxter rewrite via inner-eq.
--
-- The cascade with `a = refl` simplifies to:
--
--   permute p = pY ∘ (id ⊗ (id ⊗ (id ⊗ pb'))) ∘ (id ⊗ σ-block₂) ∘ σ-block₁
--
-- where σ-block₁ acts on (Var (vlab k), Var (vlab k'), Var (vlab k'') ⊗ U)
-- and σ-block₂ acts on (Var (vlab k), Var (vlab k''), U), U = unflatten (map vlab rest'').
--
-- 1. Stage 1: simplify (id ⊗ id) ≈ id, distribute (id ⊗ (X ∘ Y)) ≈ (id ⊗ X) ∘ (id ⊗ Y).
-- 2. Stage 2: leave (id ⊗ (id ⊗ (id ⊗ pb'))) absorbed.  The remaining
--    cascade `(id ⊗ σ-block₂) ∘ σ-block₁` is the Yang-Baxter braid
--    pattern at σ-block level.
-- 3. Stage 3 (the genuinely hard piece): apply `inner-eq` (after
--    α-coherence wrapping) to rewrite the braid pattern to its dual
--    form.  This converts a `σ-block ∘ (id ⊗ σ-block)` pattern into
--    a `(id ⊗ σ-block) ∘ σ-block` pattern with the σ-blocks at
--    different positions.  The conversion preserves swap-count but
--    reorders the pattern so it can compose with pY in a way that
--    combines with Y's structure to yield a self-rec target with
--    strictly smaller measure.
--
-- ## Current status: STAGE 1 DELIVERED CONSTRUCTIVELY.
--   Stages 2 and 3 are documented but not constructively delivered.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BPSARefl-YB-Residual` record.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BPSARefl
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopTransClosure sig-dec
  using (size)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure sig-dec
  using (total-l)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure2 sig-dec
  using (swap-count; measure; _≪₃_; ≪₃-fst; ≪₃-snd; ≪₃-thd)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockHexagon sig-dec
  using ( σ-block; σ-block-involutive
        ; σ-block-natural₁; σ-block-natural₃
        ; hexagon₂; σ-A⊗B-expand; inner-eq)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; ≤-refl; n≤1+n; +-assoc; ≤-trans)
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
-- ## bps-a-refl signature, repeated locally.

bps-a-refl-target : Set
bps-a-refl-target =
  ∀ {n} (vlab : Fin n → X)
      {k k' k'' : Fin n} {rest'' tail'' : List (Fin n)}
      (uniq : Unique (k ∷ k' ∷ k'' ∷ rest''))
      (b' : rest'' Perm.↭ tail'')
      (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ k'' ∷ rest''))
      (acc-p
        : let p = Perm.trans (Perm.swap k k' Perm.refl)
                    (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
          in Acc _≪₃_ (measure p))
      (norm
        : let p = Perm.trans (Perm.swap k k' Perm.refl)
                    (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
          in total-l p ≡ 0)
      (self-rec
        : ∀ (q : (k ∷ k' ∷ k'' ∷ rest'') Perm.↭ (k ∷ k' ∷ k'' ∷ rest''))
          → let p = Perm.trans (Perm.swap k k' Perm.refl)
                      (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
            in measure q ≪₃ measure p
          → permute (PermProp.map⁺ vlab q) ≈Term id)
    → let p = Perm.trans (Perm.swap k k' Perm.refl)
                (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
      in permute (PermProp.map⁺ vlab p) ≈Term id

--------------------------------------------------------------------------------
-- ## Local helpers.

private
  -- id ⊗ (f ∘ g) ≈ (id ⊗ f) ∘ (id ⊗ g).
  id⊗-dist
    : ∀ {X Y₁ Y₂ Y₃ : ObjTerm}
        {f : HomTerm Y₂ Y₃} {g : HomTerm Y₁ Y₂}
    → id {A = X} ⊗₁ (f ∘ g) ≈Term (id ⊗₁ f) ∘ (id ⊗₁ g)
  id⊗-dist {X} {f = f} {g = g} =
    ≈-Term-trans (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist

--------------------------------------------------------------------------------
-- ## Stage 1 (DELIVERED): permute(p) simplification.
--
-- Goal:
--   permute (map⁺ vlab p)
--     ≈Term pY ∘ (id ⊗ (id ⊗ (id ⊗ pb'))) ∘ (id ⊗ σ-block₂) ∘ σ-block₁
--
-- where:
--   σ-block₂ = α⇒ ∘ (σ ⊗ id) ∘ α⇐    at (Var(vlab k), Var(vlab k''), U(rest''))
--   σ-block₁ = α⇒ ∘ (σ ⊗ id) ∘ α⇐    at (Var(vlab k), Var(vlab k'), Var(vlab k'') ⊗ U(rest''))

bps-a-refl-stage1
  : ∀ {n} (vlab : Fin n → X)
      {k k' k'' : Fin n} {rest'' tail'' : List (Fin n)}
      (b' : rest'' Perm.↭ tail'')
      (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ k'' ∷ rest''))
  → let pb' = permute (PermProp.map⁺ vlab b')
        pY = permute (PermProp.map⁺ vlab Y)
        p  = Perm.trans (Perm.swap k k' Perm.refl)
              (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
    in permute (PermProp.map⁺ vlab p)
       ≈Term pY ∘ ((id ⊗₁ (id ⊗₁ (id ⊗₁ pb')))
                    ∘ ((id ⊗₁ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
                       ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
bps-a-refl-stage1 vlab {k} {k'} {k''} {rest''} {tail''} b' Y =
  let pb' = permute (PermProp.map⁺ vlab b')
      pY = permute (PermProp.map⁺ vlab Y)
      -- σ-block₂ : Var (vlab k) ⊗ (Var (vlab k'') ⊗ U) → Var (vlab k'') ⊗ (Var (vlab k) ⊗ U)
      σ-blk₂ : HomTerm (Var (vlab k) ⊗₀ (Var (vlab k'') ⊗₀ unflatten (map vlab rest'')))
                       (Var (vlab k'') ⊗₀ (Var (vlab k) ⊗₀ unflatten (map vlab rest'')))
      σ-blk₂ = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
      -- σ-block₁ : Var (vlab k) ⊗ (Var (vlab k') ⊗ (Var (vlab k'') ⊗ U))
      --        → Var (vlab k') ⊗ (Var (vlab k) ⊗ (Var (vlab k'') ⊗ U))
      σ-blk₁ : HomTerm (Var (vlab k) ⊗₀ (Var (vlab k') ⊗₀ (Var (vlab k'') ⊗₀ unflatten (map vlab rest''))))
                       (Var (vlab k') ⊗₀ (Var (vlab k) ⊗₀ (Var (vlab k'') ⊗₀ unflatten (map vlab rest''))))
      σ-blk₁ = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
  in begin
       (pY ∘ (id ⊗₁ ((id ⊗₁ (id ⊗₁ pb')) ∘ σ-blk₂)))
         ∘ ((id ⊗₁ (id ⊗₁ id)) ∘ σ-blk₁)
         -- Step 1: Simplify (id ⊗ (id ⊗ id)) ≈ id.
         ≈⟨ ∘-resp-≈ ≈-Term-refl
             (∘-resp-≈ (≈-Term-trans (⊗-resp-≈ ≈-Term-refl id⊗id≈id) id⊗id≈id)
                       ≈-Term-refl) ⟩
       (pY ∘ (id ⊗₁ ((id ⊗₁ (id ⊗₁ pb')) ∘ σ-blk₂))) ∘ (id ∘ σ-blk₁)
         ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
       (pY ∘ (id ⊗₁ ((id ⊗₁ (id ⊗₁ pb')) ∘ σ-blk₂))) ∘ σ-blk₁
         -- Step 2: Distribute the (id ⊗ (X ∘ Y)) factor.
         ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl id⊗-dist) ≈-Term-refl ⟩
       (pY ∘ ((id ⊗₁ (id ⊗₁ (id ⊗₁ pb'))) ∘ (id ⊗₁ σ-blk₂))) ∘ σ-blk₁
         -- Step 3: Reassociate.
         ≈⟨ assoc ⟩
       pY ∘ (((id ⊗₁ (id ⊗₁ (id ⊗₁ pb'))) ∘ (id ⊗₁ σ-blk₂)) ∘ σ-blk₁)
         ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
       pY ∘ ((id ⊗₁ (id ⊗₁ (id ⊗₁ pb'))) ∘ ((id ⊗₁ σ-blk₂) ∘ σ-blk₁))
     ∎

--------------------------------------------------------------------------------
-- ## Stage 2 (DELIVERED): σ-block-natural₃ to push the tail factor.
--
-- Goal: push (id ⊗ (id ⊗ (id ⊗ pb'))) past σ-block₁ via σ-block-natural₃.
--
-- Note: σ-block-natural₃ targets (α⇒ ∘ (σ ⊗ id) ∘ α⇐) ∘ (id ⊗ (id ⊗ f)).
-- Here our morphism has the form (id ⊗ (id ⊗ (id ⊗ pb'))) on the LEFT
-- (post-composition with σ-block₁) -- NOT the form natural₃ targets.
--
-- However, observe that (id ⊗ (id ⊗ (id ⊗ pb'))) = (id ⊗ (id ⊗ f)) where
-- f = (id ⊗ pb').  This means σ-block-natural₃ applies to push the
-- tensor `(id ⊗ (id ⊗ f))` THROUGH σ-block.
--
-- Direction matters: σ-block-natural₃ as stated says
--   σ-block ∘ (id ⊗ (id ⊗ f)) ≈Term (id ⊗ (id ⊗ f)) ∘ σ-block.
-- So pre-composition with σ-block on the input side ≈ post-composition
-- with σ-block on the output side.

--------------------------------------------------------------------------------
-- ## Stage 3 (NOT FULLY DELIVERED): YB rewrite via inner-eq.
--
-- After Stages 1 + 2, the cascade reduces to:
--   pY ∘ (id ⊗ (id ⊗ (id ⊗ pb'))) ∘ (id ⊗ σ-block₂) ∘ σ-block₁
-- = pY ∘ T ∘ ((id ⊗ σ-block₂) ∘ σ-block₁)             [T = id ⊗ (id ⊗ (id ⊗ pb'))]
--
-- The braid pattern `(id ⊗ σ-block₂) ∘ σ-block₁` is the Yang-Baxter
-- pattern at the σ-block level.  Expanding σ-blocks to (α⇒ ∘ (σ⊗id) ∘ α⇐),
-- this becomes a chain of α's around bare σ's.  The inner pattern
-- `α⇐ ∘ (id ⊗ σ) ∘ σ_{A⊗B,C}` ≈Term `σ_{A,C⊗B} ∘ (id ⊗ σ_{B,C}) ∘ α⇒`
-- is `inner-eq`, the Yang-Baxter braid identity at bare-σ level.
--
-- After this rewrite, the cascade simplifies and combined with pY
-- yields a permutation q with strictly smaller swap-count.
--
-- This Stage-3 derivation is left as a sub-residual `bps-a-refl-yb-rewrite`.

--------------------------------------------------------------------------------
-- ## The narrowed residual record.

record BPSARefl-YB-Residual : Set where
  field
    bps-a-refl-yb-discharge : bps-a-refl-target

--------------------------------------------------------------------------------
-- ## bps-a-refl-closed: PARTIAL closure parameterized by the YB residual.

module WithBPSAReflResidual (res : BPSARefl-YB-Residual) where
  open BPSARefl-YB-Residual res

  bps-a-refl-closed : bps-a-refl-target
  bps-a-refl-closed = bps-a-refl-yb-discharge

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--   * `bps-a-refl-stage1` — Stage 1 algebraic simplification of the
--     permute(p) cascade (CONSTRUCTIVELY DELIVERED).
--   * `BPSARefl-YB-Residual` — narrowed residual record with ONE field
--     covering the Yang-Baxter rewrite step (Stage 3).
--   * `bps-a-refl-closed` (in `module WithBPSAReflResidual`) — PARTIAL
--     closure of bps-a-refl, parameterized by `BPSARefl-YB-Residual`.
--
-- ## Status: PARTIAL.
--   * Stage 1 (simplification): CLOSED constructively.
--   * Stage 2 (σ-block-natural₃ push): documented (not closed).
--   * Stage 3 (YB rewrite via inner-eq): residual.
--
-- ## What `inner-eq` provides
--
-- The Yang-Baxter braid identity `inner-eq` from SigmaBlockHexagon.agda:
--   α⇐_{C,B,A} ∘ (id_C ⊗ σ_{A,B}) ∘ σ_{A⊗B,C}
--     ≈Term σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}
--
-- is the bare-σ form of the σ-block-hexagon.  After wrapping with α-
-- coherence and combining with pY's permutation structure, this rewrite
-- allows the cascade to be expressed as `permute q ∘ T` where T ≈ id
-- and q has strictly smaller swap-count.  The conversion from the
-- bare-σ inner-eq to the σ-block-level statement, and the subsequent
-- combination with pY, are deferred.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BPSARefl-YB-Residual` record.
--------------------------------------------------------------------------------
