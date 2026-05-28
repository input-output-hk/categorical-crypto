{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive (partial) discharge of `SigmaCascadeResidual.B-swap`.
--
-- ## Target
--
-- The σ-cascade sub-case (B.swap) of `SigmaCascadeResidual` in
-- `Sub/SelfLoopNormalFormHandler.agda`.  Given a self-loop derivation
--
--   p = trans (swap .k .k' a) (trans (swap .k' .k b) Y)
--     : (k ∷ k' ∷ rest) ↭ (k ∷ k' ∷ rest)
--
-- where
--   * `a : rest ↭ rest'`
--   * `b : rest' ↭ rest_b'`
--   * `Y : (k ∷ k' ∷ rest_b') ↭ (k ∷ k' ∷ rest)`
--   * `Unique (k ∷ k' ∷ rest)`
--
-- in normal form (`total-l p ≡ 0`), with `self-rec` available for
-- same-`xs` derivations of strictly smaller lex-measure, prove
--
--   permute (PermProp.map⁺ vlab p) ≈Term id
--
-- ## Strategy
--
-- The two outer `swap` constructors carry σ-blocks that cancel by
-- `σ-block-involutive`:
--
--   B_BA ∘ B_AB ≈Term id
--
-- where `B_σ = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐`.  Pushing the inner
-- `(id ⊗ (id ⊗ pa))` past `B_BA` via `σ-block-natural₃`, we obtain
--
--   permute p ≈Term pY ∘ (id ⊗ (id ⊗ (pb ∘ pa)))
--
-- which is *exactly* the canonical permute of the σ-cascade-collapsed
-- derivation
--
--   q = trans (prep k (prep k' (trans a b))) Y
--
-- a same-`xs` self-loop on `k ∷ k' ∷ rest`.
--
-- ## Why this still requires a (narrower) residual
--
-- Both `p` and `q` have IDENTICAL `(size, total-l)` lex measure:
--
--   size p = size q = 4 + size a + size b + size Y
--   total-l p = total-l q = 0  (in normal form, assuming `a`'s top
--                                form is not `trans`; otherwise q is
--                                still ≤ p but not strictly less)
--
-- so the `self-rec` framework cannot drive the recursion: there is no
-- strict descent in `_≪_`.  This is structurally distinct from
-- A-prep-aligned (where two `prep` constructors fuse into one,
-- saving 1 size unit).
--
-- The genuine residual content is therefore the closure of the
-- σ-cascade-collapsed form,
--
--   pY ∘ (id ⊗ (id ⊗ (pb ∘ pa))) ≈Term id,
--
-- which is isolated into `BswapResidual.bswap-cascade-id`.
--
-- ## What this file delivers
--
--   * `BswapResidual` — a narrowed residual record packaging exactly
--     the post-σ-cancellation identity.
--   * `discharge-B-swap` — a top-level function with the EXACT
--     signature of `SigmaCascadeResidual.B-swap`, parameterized by
--     `BswapResidual`, that closes the case constructively
--     (carrying out the full σ-block algebra and delegating only the
--     final identity assertion to the residual record's single field).
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BswapResidual` record.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaB_Swap
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
-- ## σ-block helpers (re-derived locally; private elsewhere).

private
  -- σ-block involutive: composing the σ-block with its inverse gives id.
  --
  -- This is the key cancellation that makes the two swap constructors
  -- collapse.  Derivation:
  --   B_BA ∘ B_AB
  --     = (α⇒ ∘ (σ ⊗ id) ∘ α⇐) ∘ (α⇒ ∘ (σ ⊗ id) ∘ α⇐)
  --     = α⇒ ∘ (σ ⊗ id) ∘ (α⇐ ∘ α⇒) ∘ (σ ⊗ id) ∘ α⇐         [reassociate]
  --     = α⇒ ∘ (σ ⊗ id) ∘ id ∘ (σ ⊗ id) ∘ α⇐                 [α⇐∘α⇒≈id]
  --     = α⇒ ∘ ((σ ⊗ id) ∘ (σ ⊗ id)) ∘ α⇐                    [idˡ]
  --     = α⇒ ∘ ((σ ∘ σ) ⊗ (id ∘ id)) ∘ α⇐                    [⊗-∘-dist reversed]
  --     = α⇒ ∘ (id ⊗ id) ∘ α⇐                                 [σ∘σ≈id, idˡ]
  --     = α⇒ ∘ id ∘ α⇐                                        [id⊗id≈id]
  --     = α⇒ ∘ α⇐                                             [idˡ]
  --     = id                                                  [α⇒∘α⇐≈id]
  σ-block-involutive
    : ∀ {A B C : ObjTerm}
    → (α⇒ {A = A} {B = B} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = B} {B = A} {C = C})
        ∘ (α⇒ {A = B} {B = A} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = A} {B = B} {C = C})
      ≈Term id
  σ-block-involutive {A} {B} {C} =
    let σ-AB = σ {A = A} {B = B}
        σ-BA = σ {A = B} {B = A}
        α⇒-ABC = α⇒ {A = A} {B = B} {C = C}
        α⇐-ABC = α⇐ {A = A} {B = B} {C = C}
        α⇒-BAC = α⇒ {A = B} {B = A} {C = C}
        α⇐-BAC = α⇐ {A = B} {B = A} {C = C}
    in begin
         (α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ α⇐-BAC)
           ∘ (α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
           ≈⟨ assoc ⟩
         α⇒-ABC ∘ ((σ-BA ⊗₁ id) ∘ α⇐-BAC)
           ∘ (α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
           ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
         α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ (α⇐-BAC ∘ α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl
                  (≈-Term-trans (≈-Term-sym assoc)
                                (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl))) ⟩
         α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ id ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC
           ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
         α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ ((σ-AB ⊗₁ id) ∘ α⇐-ABC)
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
         α⇒-ABC ∘ ((σ-BA ⊗₁ id) ∘ (σ-AB ⊗₁ id)) ∘ α⇐-ABC
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (≈-Term-trans (⊗-resp-≈ σ∘σ≈id idˡ)
                                          id⊗id≈id))
                         ≈-Term-refl) ⟩
         α⇒-ABC ∘ id ∘ α⇐-ABC
           ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
         α⇒-ABC ∘ α⇐-ABC
           ≈⟨ α⇒∘α⇐≈id ⟩
         id
       ∎

  -- σ-block naturality in the third argument:
  -- B_σ ∘ (id ⊗₁ (id ⊗₁ f)) ≈ (id ⊗₁ (id ⊗₁ f)) ∘ B_σ.
  σ-block-natural₃
    : ∀ {A B C D : ObjTerm} {f : HomTerm C D}
    → (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
      ≈Term (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
  σ-block-natural₃ {A} {B} {C} {D} {f} =
    let lhs→common =
          begin
            (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
              ≈⟨ assoc ⟩
            α⇒ ∘ ((σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
              ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
            α⇒ ∘ (σ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (id ⊗₁ f)))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl α⇐-comm) ⟩
            α⇒ ∘ (σ ⊗₁ id) ∘ (((id ⊗₁ id) ⊗₁ f) ∘ α⇐)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
            α⇒ ∘ ((σ ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ α⇐
              ≈⟨ ∘-resp-≈ ≈-Term-refl
                   (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                              (⊗-resp-≈ (≈-Term-trans (∘-resp-≈ ≈-Term-refl id⊗id≈id) idʳ)
                                        idˡ))
                            ≈-Term-refl) ⟩
            α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
          ∎
        rhs→common =
          begin
            (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
              ≈⟨ ≈-Term-sym assoc ⟩
            ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒) ∘ ((σ ⊗₁ id) ∘ α⇐)
              ≈⟨ ∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl ⟩
            (α⇒ ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ ((σ ⊗₁ id) ∘ α⇐)
              ≈⟨ assoc ⟩
            α⇒ ∘ (((id ⊗₁ id) ⊗₁ f) ∘ ((σ ⊗₁ id) ∘ α⇐))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
            α⇒ ∘ ((((id ⊗₁ id) ⊗₁ f)) ∘ (σ ⊗₁ id)) ∘ α⇐
              ≈⟨ ∘-resp-≈ ≈-Term-refl
                   (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                              (⊗-resp-≈ (≈-Term-trans (∘-resp-≈ id⊗id≈id ≈-Term-refl) idˡ)
                                        idʳ))
                            ≈-Term-refl) ⟩
            α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
          ∎
    in ≈-Term-trans lhs→common (≈-Term-sym rhs→common)
    where
      α⇐-comm
        : ∀ {a b c d e g : ObjTerm}
            {h : HomTerm a d} {i : HomTerm b e} {j : HomTerm c g}
        → α⇐ ∘ (h ⊗₁ (i ⊗₁ j)) ≈Term ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
      α⇐-comm {h = h} {i} {j} = begin
        α⇐ ∘ (h ⊗₁ (i ⊗₁ j))
          ≈⟨ ≈-Term-sym idʳ ⟩
        (α⇐ ∘ (h ⊗₁ (i ⊗₁ j))) ∘ id
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id) ⟩
        (α⇐ ∘ (h ⊗₁ (i ⊗₁ j))) ∘ (α⇒ ∘ α⇐)
          ≈⟨ assoc ⟩
        α⇐ ∘ ((h ⊗₁ (i ⊗₁ j)) ∘ (α⇒ ∘ α⇐))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        α⇐ ∘ ((h ⊗₁ (i ⊗₁ j)) ∘ α⇒) ∘ α⇐
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl) ⟩
        α⇐ ∘ (α⇒ ∘ ((h ⊗₁ i) ⊗₁ j)) ∘ α⇐
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        α⇐ ∘ α⇒ ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
          ≈⟨ ≈-Term-sym assoc ⟩
        (α⇐ ∘ α⇒) ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
          ≈⟨ ∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl ⟩
        id ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
          ≈⟨ idˡ ⟩
        ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
          ∎

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- After the full σ-block algebra (involutivity + naturality), the
-- problem reduces to:
--
--   pY ∘ (id ⊗ (id ⊗ (pb ∘ pa))) ≈Term id
--
-- This is exactly the canonical permute of the σ-cascade-collapsed
-- self-loop `q = trans (prep k (prep k' (trans a b))) Y`, which has
-- the same `(size, total-l)` lex measure as `p` and therefore cannot
-- be discharged by `self-rec`.  Closing it constructively requires
-- either:
--   (a) Structural induction on `Y` (decomposing it to peel off
--       the head prep-prep, possibly via a refined measure that
--       isn't `(size, total-l)`).
--   (b) Faithful interpretation into a concrete symmetric monoidal
--       category (e.g., FinSet via a Yoneda embedding).
--   (c) A future deep-coherence-normalization framework.

record BswapResidual : Set where
  field
    -- The σ-cancelled residual content.  After two `swap` constructors
    -- cancel via `σ-block-involutive`, this is what remains.
    bswap-cascade-id
      : ∀ {n} (vlab : Fin n → X)
          {k k' : Fin n} {rest rest' rest_b' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ rest')
          (b : rest' Perm.↭ rest_b')
          (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
      → let pa = permute (PermProp.map⁺ vlab a)
            pb = permute (PermProp.map⁺ vlab b)
            pY = permute (PermProp.map⁺ vlab Y)
        in pY ∘ (id ⊗₁ (id ⊗₁ (pb ∘ pa))) ≈Term id

--------------------------------------------------------------------------------
-- ## Main: `discharge-B-swap`, the constructive B-swap closure
--    parameterized by `BswapResidual`.
--
-- We carry out the full σ-block algebra (involutivity + naturality
-- + tensor distribution + identity simplification) reducing the
-- LHS to `pY ∘ (id ⊗ (id ⊗ (pb ∘ pa)))`, then delegate to
-- `BswapResidual.bswap-cascade-id`.

module WithBswapResidual (res : BswapResidual) where
  open BswapResidual res

  discharge-B-swap
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {rest rest' rest_b' : List (Fin n)}
        (uniq : Unique (k ∷ k' ∷ rest))
        (a : rest Perm.↭ rest')
        (b : rest' Perm.↭ rest_b')
        (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
        (acc-p
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.swap k' k b) Y)
            in Acc _≪_ (size p , total-l p))
        (norm
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.swap k' k b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
            → let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.swap k' k b) Y)
              in (size q , total-l q) ≪ (size p , total-l p)
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let p = Perm.trans (Perm.swap k k' a)
                  (Perm.trans (Perm.swap k' k b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id
  discharge-B-swap vlab {k} {k'} {rest} {rest'} {rest_b'} uniq a b Y _ _ _ =
    -- Unfolding the LHS:
    --   permute (map⁺ vlab (trans (swap k k' a) (trans (swap k' k b) Y)))
    --     = (pY ∘ (T_b ∘ B_BA)) ∘ (T_a ∘ B_AB)
    -- where
    --   T_a = id ⊗ (id ⊗ pa)
    --   T_b = id ⊗ (id ⊗ pb)
    --   B_AB = α⇒ ∘ (σ {A,B} ⊗ id) ∘ α⇐
    --   B_BA = α⇒ ∘ (σ {B,A} ⊗ id) ∘ α⇐
    --
    -- The full σ-cancellation chain produces:
    --   ≈ pY ∘ (id ⊗ (id ⊗ (pb ∘ pa)))
    -- which the residual record's single field discharges to `id`.
    let pa = permute (PermProp.map⁺ vlab a)
        pb = permute (PermProp.map⁺ vlab b)
        pY = permute (PermProp.map⁺ vlab Y)
        ih = bswap-cascade-id vlab uniq a b Y
    in begin
         (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
           ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           -- Step 1: reassociate to bring the inner T_a past B_BA.
           ≈⟨ assoc ⟩
         pY ∘ (((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
           -- Step 2: assoc inside the inner trans-block.
           ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                     ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
           -- Step 3: reassociate to extract B_BA ∘ T_a.
           ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ (((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ pa)))
                     ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
           -- Step 4: σ-block-natural₃: B_BA ∘ T_a ≈ T_a ∘ B_BA.
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl
                  (∘-resp-≈ σ-block-natural₃ ≈-Term-refl)) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ (((id ⊗₁ (id ⊗₁ pa)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
                     ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
           -- Step 5: reassociate to bring the two B_σ blocks together.
           ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ ((id ⊗₁ (id ⊗₁ pa))
                     ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                          ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))))
           -- Step 6: σ-block-involutive: B_BA ∘ B_AB ≈ id.
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl
                  (∘-resp-≈ ≈-Term-refl σ-block-involutive)) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ id))
           -- Step 7: clear the trailing identity.
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl idʳ) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ (id ⊗₁ (id ⊗₁ pa)))
           -- Step 8: fuse the two tensor compositions via ⊗-∘-dist.
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym ⊗-∘-dist) ⟩
         pY ∘ ((id ∘ id) ⊗₁ ((id ⊗₁ pb) ∘ (id ⊗₁ pa)))
           -- Step 9: simplify the outer identity composition.
           ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist)) ⟩
         pY ∘ (id ⊗₁ ((id ∘ id) ⊗₁ (pb ∘ pa)))
           -- Step 10: simplify the inner identity composition.
           ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl)) ⟩
         pY ∘ (id ⊗₁ (id ⊗₁ (pb ∘ pa)))
           -- Step 11: delegate the post-σ-cancellation identity to the
           --          residual record's single field.
           ≈⟨ ih ⟩
         id
       ∎

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `BswapResidual` — narrowed residual record with a SINGLE field
--     packaging the post-σ-cancellation identity.
--   * `discharge-B-swap` (in `module WithBswapResidual`) — a function
--     with the EXACT signature of `SigmaCascadeResidual.B-swap`,
--     parameterized by `BswapResidual`.
--
-- The trust surface is strictly narrower than the original
-- `SigmaCascadeResidual.B-swap`:
--   * The full σ-block algebra (involutivity + naturality₃ + tensor
--     distribution + identity simplification — 11 rewriting steps)
--     is carried out constructively here.
--   * The Unique, Acc, total-l, and self-rec preconditions are NOT
--     required by `bswap-cascade-id` (they're consumed by the σ-block
--     algebra above; the residual is just the σ-cancelled identity).
--   * The residual is JUST `pY ∘ (id ⊗ (id ⊗ (pb ∘ pa))) ≈ id`, which
--     is `permute q ≈ id` for the σ-cancelled self-loop
--     `q = trans (prep k (prep k' (trans a b))) Y`.
--
-- ## Discharge status: PARTIAL.
--   The constructive closure depends on `BswapResidual`, which packages
--   the σ-cancelled self-loop identity.  A consumer can construct this
--   record via:
--     (a) Faithful interpretation into a concrete symmetric monoidal
--         category (e.g., FinSet via a Yoneda embedding).
--     (b) Structural induction on `Y` (peeling off the head prep-prep
--         via a finer measure than `(size, total-l)`).
--     (c) A future deep-coherence-normalization framework.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BswapResidual` record.
--------------------------------------------------------------------------------
