{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive (partial) `NormalFormHandler` for the residual cases left
-- exposed by `SelfLoopFullClosure.self-loop-lex`.
--
-- ## Background
--
-- `SelfLoopFullClosure` reduces `SelfLoopPostulate.Fin-permute-self-loop-id`
-- to a `NormalFormHandler`, which must close `permute (map⁺ vlab p) ≈Term id`
-- for `p : xs ↭ xs` in *normal form* (`total-l p ≡ 0`).
--
-- After dnorm-normalization, only two top-level catch-all patterns remain
-- (the other cases are dispatched by `self-loop-lex` BEFORE calling the
-- handler):
--
--   (A) `p = trans (prep .k a) (trans X Y)` with `X ∈ {prep, swap}`.
--   (B) `p = trans (swap .k .k' a) (trans X Y)` with `X ∈ {prep, swap}`.
--
-- (The `X = refl` sub-cases are handled inside `self-loop-lex` via the
-- `trans p₁ (trans refl p₂')` pattern.)
--
-- ## What this file delivers
--
-- We constructively close `A.prep` (the aligned-prep-prep-via-trans
-- fusion) by rewriting `p` to a strictly-smaller equivalent
-- `q : xs ↭ xs`:
--
--     trans (prep .k a) (trans (prep .k b) Y)
--   ≈Term-permute
--     trans (prep .k (trans a b)) Y
--
-- and `size q < size p`, so we recurse via `self-rec` using `≪-fst`.
--
-- The remaining three σ-cascade sub-cases (A.swap, B.prep, B.swap) and
-- the "shouldn't reach here" cases (which are upstream-handled but
-- needed for totality of the handler signature) are bundled into a
-- single narrower residual record `SigmaCascadeResidual`.
--
-- ## Sub-case status
--
--   A.refl                : handled upstream (in `self-loop-lex`).
--   A.prep   (aligned)    : CLOSED constructively here.
--   A.prep   (misaligned) : impossible by Agda's dot-pattern unification
--                           (the `prep .k` patterns force the head).
--   A.swap                : narrowed to `SigmaCascadeResidual.A-swap`.
--   B.refl                : handled upstream.
--   B.prep                : narrowed to `SigmaCascadeResidual.B-prep`.
--   B.swap   (aligned)    : narrowed to `SigmaCascadeResidual.B-swap`.
--   B.swap   (misaligned) : impossible by Agda's dot-pattern unification.
--
-- ## Dead branches (refl, prep, swap at the handler's outer level)
--
-- `NormalFormHandler`'s type allows arbitrary `p`, but `self-loop-lex`
-- only invokes the handler with `p = trans p₁ p₂` (after dnorm).  For
-- totality we handle:
--
--   * `refl`        — `≈-Term-refl` (directly).
--   * `swap k k _`  — `⊥-elim` from `Unique` (directly).
--   * `prep .k p'`  — packaged as the residual field `dead-prep`.
--     This field is unreachable in practice; the user can construct
--     it via any sound external proof or postulate.
--   * `trans` sub-cases that `self-loop-lex` handles inline
--     (prep-prep-aligned, swap-swap-aligned, prep-swap-impossible,
--     swap-prep-impossible, trans-refl-inner): also handled via
--     residual fields when their structure requires recursion at a
--     different xs.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `SigmaCascadeResidual` record.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopNormalFormHandler
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (SelfLoopPostulate)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopTransClosure sig-dec
  using (size; size-map⁺)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure sig-dec
  using (total-l; total-l-map⁺; _≪_; ≪-fst; ≪-snd; ≪-wf
        ; NormalFormHandler; module WithNormalFormHandler)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-suc; ≤-refl; ≤-trans; +-comm; m≤m+n; m≤n+m; <-trans; +-assoc
        ; +-monoʳ-≤; +-monoˡ-≤; +-monoˡ-<; +-monoʳ-<; +-mono-<; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc; acc; WellFounded)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Narrower residual: `SigmaCascadeResidual`.
--
-- Wraps the dead-branch and σ-cascade sub-cases into a single record.
-- A user can construct this record by providing each field via any
-- sound proof (e.g., `Fin-permute-self-loop-id-aux` from SelfLoop.agda
-- if they accept the upstream postulate, or via deeper σ-block algebra).

record SigmaCascadeResidual : Set where
  field
    -- Dead branch: `p = prep k p'`.  Unreachable in practice (upstream
    -- catches this case before calling the handler).
    dead-prep
      : ∀ {n} (vlab : Fin n → X)
          {k : Fin n} {xs' : List (Fin n)}
          (uniq : Unique (k ∷ xs'))
          (p' : xs' Perm.↭ xs')
          (acc-p
            : Acc _≪_ ( size (Perm.prep k p')
                      , total-l (Perm.prep k p')))
          (norm : total-l (Perm.prep k p') ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ xs') Perm.↭ (k ∷ xs'))
              → (size q , total-l q)
                ≪ (size (Perm.prep k p') , total-l (Perm.prep k p'))
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → permute (PermProp.map⁺ vlab (Perm.prep k p')) ≈Term id

    -- Dead branch: `p = trans (prep .k a) (prep .k b)` (aligned).
    -- Unreachable in practice (upstream handles this).
    dead-prep-prep-aligned
      : ∀ {n} (vlab : Fin n → X)
          {k : Fin n} {xs' zs' : List (Fin n)}
          (uniq : Unique (k ∷ xs'))
          (a : xs' Perm.↭ zs')
          (b : zs' Perm.↭ xs')
          (acc-p
            : let p = Perm.trans (Perm.prep k a) (Perm.prep k b)
              in Acc _≪_ (size p , total-l p))
          (norm
            : let p = Perm.trans (Perm.prep k a) (Perm.prep k b)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ xs') Perm.↭ (k ∷ xs'))
              → let p = Perm.trans (Perm.prep k a) (Perm.prep k b)
                in (size q , total-l q) ≪ (size p , total-l p)
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let p = Perm.trans (Perm.prep k a) (Perm.prep k b)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Dead branch: `p = trans (swap .k .k' a) (swap .k' .k b)` (aligned).
    dead-swap-swap-aligned
      : ∀ {n} (vlab : Fin n → X)
          {k k' : Fin n} {rest mid : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ mid)
          (b : mid Perm.↭ rest)
          (acc-p
            : let p = Perm.trans (Perm.swap k k' a) (Perm.swap k' k b)
              in Acc _≪_ (size p , total-l p))
          (norm
            : let p = Perm.trans (Perm.swap k k' a) (Perm.swap k' k b)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
              → let p = Perm.trans (Perm.swap k k' a) (Perm.swap k' k b)
                in (size q , total-l q) ≪ (size p , total-l p)
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let p = Perm.trans (Perm.swap k k' a) (Perm.swap k' k b)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- (A.swap): `p = trans (prep .k a) (trans (swap .k k' b) Y)`.
    -- Boundary: (k ∷ xs') ↭ (k ∷ xs').
    A-swap
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

    -- (B.prep): `p = trans (swap .k .k' a) (trans (prep .k' b) Y)`.
    B-prep
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

    -- (B.swap): `p = trans (swap .k .k' a) (trans (swap .k' .k b) Y)`.
    B-swap
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

--------------------------------------------------------------------------------
-- ## Size arithmetic for the prep-prep-aligned fusion.

private
  -- size (trans (prep k a) (trans (prep k b) Y))
  --   = 1 + (1 + size a) + (1 + (1 + size b) + size Y)
  --   = 4 + size a + size b + size Y.
  --
  -- size (trans (prep k (trans a b)) Y)
  --   = 1 + (1 + (1 + size a + size b)) + size Y
  --   = 3 + size a + size b + size Y.
  --
  -- Strict decrease by 1.
  prep-fusion-size-<
    : ∀ sa sb sY
    → suc (suc (suc (sa + sb)) + sY)
      <
      suc (suc sa + suc (suc sb + sY))
  prep-fusion-size-< sa sb sY
    rewrite +-suc sa (suc sb + sY)
          | +-suc sa (sb + sY)
          | sym (+-assoc sa sb sY)
    = s≤s (s≤s (s≤s (s≤s ≤-refl)))

  -- For `trans p₁ (trans refl p₂')` refl-strip.
  refl-strip-< : ∀ a b → a + b < a + suc (suc b)
  refl-strip-< zero    b = s≤s (n≤1+n b)
  refl-strip-< (suc a) b = s≤s (refl-strip-< a b)

  -- a + suc b is never zero.
  +-suc-nonzero : ∀ a b → a + suc b ≡ 0 → ⊥
  +-suc-nonzero zero    b ()
  +-suc-nonzero (suc a) b ()

--------------------------------------------------------------------------------
-- ## Main: constructive normal-form handler parameterized over the
--    residual record.

module WithSigmaResidual (scr : SigmaCascadeResidual) where
  open SigmaCascadeResidual scr

  constructive-normal-form-handler : NormalFormHandler

  -- ----- refl -----
  constructive-normal-form-handler vlab _ Perm.refl _ _ _ = ≈-Term-refl

  -- ----- prep .k _ (dead branch, packaged) -----
  constructive-normal-form-handler vlab uniq (Perm.prep k p') acc-p norm self-rec =
    dead-prep vlab uniq p' acc-p norm self-rec

  -- ----- swap k k _ (impossible by Unique) -----
  constructive-normal-form-handler vlab ((k≢k' ∷ _) ∷ _) (Perm.swap k k p') _ _ _ =
    ⊥-elim (k≢k' refl)

  -- ----- trans p₁ p₂ -----
  -- Dispatch on (p₁, p₂) structure.

  -- trans refl p₂: via self-rec on p₂.
  constructive-normal-form-handler vlab uniq (Perm.trans Perm.refl p₂) acc-p norm self-rec =
    let sub-< : (size p₂ , total-l p₂) ≪ (size (Perm.trans Perm.refl p₂) , total-l (Perm.trans Perm.refl p₂))
        sub-< = ≪-fst {l₁ = total-l p₂} {l₂ = total-l p₂}
                      (s≤s (n≤1+n (size p₂)))
        ih = self-rec p₂ sub-<
    in begin
         permute (PermProp.map⁺ vlab p₂) ∘ id
           ≈⟨ idʳ ⟩
         permute (PermProp.map⁺ vlab p₂)
           ≈⟨ ih ⟩
         id
       ∎

  -- trans p₁ refl: via self-rec on p₁.
  constructive-normal-form-handler vlab uniq (Perm.trans p₁ Perm.refl) acc-p norm self-rec =
    let sub-< : (size p₁ , total-l p₁) ≪ (size (Perm.trans p₁ Perm.refl) , total-l (Perm.trans p₁ Perm.refl))
        sub-< = ≪-fst {l₁ = total-l p₁} {l₂ = total-l (Perm.trans p₁ Perm.refl)}
                      (s≤s (m≤m+n (size p₁) 1))
        ih = self-rec p₁ sub-<
    in begin
         id ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ idˡ ⟩
         permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ih ⟩
         id
       ∎

  -- trans (prep .k _) (prep .k _): dead branch (handled upstream).
  -- We package as residual.
  constructive-normal-form-handler vlab uniq
      (Perm.trans (Perm.prep k p₁') (Perm.prep .k p₂')) acc-p norm self-rec =
    dead-prep-prep-aligned vlab uniq p₁' p₂' acc-p norm self-rec

  -- trans (swap .k .k' _) (swap .k' .k _): dead branch (handled upstream).
  constructive-normal-form-handler vlab uniq
      (Perm.trans (Perm.swap k k' p₁') (Perm.swap .k' .k p₂')) acc-p norm self-rec =
    dead-swap-swap-aligned vlab uniq p₁' p₂' acc-p norm self-rec

  -- trans (prep k _) (swap k k _): impossible by Unique.
  constructive-normal-form-handler vlab ((k≢k ∷ _) ∷ _)
      (Perm.trans (Perm.prep k p₁') (Perm.swap k k p₂')) _ _ _ =
    ⊥-elim (k≢k refl)

  -- trans (swap k k _) (prep k _): impossible by Unique.
  constructive-normal-form-handler vlab ((k≢k ∷ _) ∷ _)
      (Perm.trans (Perm.swap k k p₁') (Perm.prep k p₂')) _ _ _ =
    ⊥-elim (k≢k refl)

  -- trans p₁ (trans refl p₂'): handled upstream, refl-strip.
  constructive-normal-form-handler vlab uniq
      (Perm.trans p₁ (Perm.trans Perm.refl p₂')) acc-p norm self-rec =
    let q = Perm.trans p₁ p₂'
        size-< : size q < size (Perm.trans p₁ (Perm.trans Perm.refl p₂'))
        size-< = s≤s (refl-strip-< (size p₁) (size p₂'))
        sub-< = ≪-fst size-<
        ih = self-rec q sub-<
    in begin
         (permute (PermProp.map⁺ vlab p₂') ∘ id) ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ∘-resp-≈ idʳ ≈-Term-refl ⟩
         permute (PermProp.map⁺ vlab p₂') ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ih ⟩
         id
       ∎

  -- =====================================================================
  -- (A.prep-aligned): trans (prep .k a) (trans (prep .k b) Y)
  --                  → fuse and self-rec.
  -- =====================================================================
  constructive-normal-form-handler vlab {k ∷ xs'} (_ ∷ uniq')
      (Perm.trans (Perm.prep .k a)
        (Perm.trans (Perm.prep .k b) Y)) acc-p norm self-rec =
    let q = Perm.trans (Perm.prep k (Perm.trans a b)) Y
        size-q-< : size q < size (Perm.trans (Perm.prep k a)
                                    (Perm.trans (Perm.prep k b) Y))
        size-q-< = prep-fusion-size-< (size a) (size b) (size Y)
        sub-< = ≪-fst size-q-<
        ih = self-rec q sub-<
        -- permute (trans (prep k a) (trans (prep k b) Y))
        --   = (permute Y ∘ (id ⊗ permute b)) ∘ (id ⊗ permute a)
        -- permute q = permute Y ∘ (id ⊗ (permute b ∘ permute a))
        -- These are ≈Term-equal by assoc + ⊗-∘-dist + idˡ.
        pa = permute (PermProp.map⁺ vlab a)
        pb = permute (PermProp.map⁺ vlab b)
        pY = permute (PermProp.map⁺ vlab Y)
    in begin
         (pY ∘ (id ⊗₁ pb)) ∘ (id ⊗₁ pa)
           ≈⟨ assoc ⟩
         pY ∘ ((id ⊗₁ pb) ∘ (id ⊗₁ pa))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym ⊗-∘-dist) ⟩
         pY ∘ ((id ∘ id) ⊗₁ (pb ∘ pa))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl) ⟩
         pY ∘ (id ⊗₁ (pb ∘ pa))
           ≈⟨ ih ⟩
         id
       ∎

  -- =====================================================================
  -- (A.swap): trans (prep .k a) (trans (swap k k' b) Y)
  --           → residual.
  -- =====================================================================
  constructive-normal-form-handler vlab {k ∷ xs'} uniq
      (Perm.trans (Perm.prep .k a)
        (Perm.trans (Perm.swap k k' b) Y)) acc-p norm self-rec =
    A-swap vlab uniq a b Y acc-p norm self-rec

  -- =====================================================================
  -- (B.prep): trans (swap .k .k' a) (trans (prep k'' b) Y)
  --           → residual (after unification, k'' = k').
  -- =====================================================================
  constructive-normal-form-handler vlab {k ∷ k' ∷ rest} uniq
      (Perm.trans (Perm.swap .k .k' a)
        (Perm.trans (Perm.prep .k' b) Y)) acc-p norm self-rec =
    B-prep vlab uniq a b Y acc-p norm self-rec

  -- =====================================================================
  -- (B.swap): trans (swap .k .k' a) (trans (swap k'' k''' b) Y)
  --           → residual (after unification, k'' = k', k''' = k).
  -- =====================================================================
  constructive-normal-form-handler vlab {k ∷ k' ∷ rest} uniq
      (Perm.trans (Perm.swap .k .k' a)
        (Perm.trans (Perm.swap .k' .k b) Y)) acc-p norm self-rec =
    B-swap vlab uniq a b Y acc-p norm self-rec

  -- =====================================================================
  -- Impossible cases: `trans (prep _ _) (trans (trans _ _) _)` and
  -- `trans (swap _ _ _) (trans (trans _ _) _)` have total-l > 0
  -- (contradicting `norm : total-l p ≡ 0`).
  -- =====================================================================
  constructive-normal-form-handler vlab uniq
      (Perm.trans (Perm.prep x p) (Perm.trans (Perm.trans p₁ p₂) p₃)) _ norm _ =
    ⊥-elim (+-suc-nonzero (total-l p) (total-l p₁ + total-l p₂ + total-l p₃) norm)

  constructive-normal-form-handler vlab uniq
      (Perm.trans (Perm.swap x y p) (Perm.trans (Perm.trans p₁ p₂) p₃)) _ norm _ =
    ⊥-elim (+-suc-nonzero (total-l p) (total-l p₁ + total-l p₂ + total-l p₃) norm)

--------------------------------------------------------------------------------
-- ## Bundle: `WithSigmaResidual` gives a `SelfLoopPostulate`.

module WithSigmaResidual-SelfLoop (scr : SigmaCascadeResidual) where
  open WithSigmaResidual scr
  open WithNormalFormHandler constructive-normal-form-handler public
    using (selfLoopPostulate)

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--   * Constructive closure of A.prep-aligned via prep-prep fusion.
--   * Constructive closure of trans-refl-left/right and
--     trans-refl-inner sub-cases (via self-rec).
--   * Constructive closure of prep-swap/swap-prep impossible cases
--     (via Unique).
--   * Packaging A.swap, B.prep, B.swap, and the (unreachable in
--     practice) dead branches as the residual record
--     `SigmaCascadeResidual`.
--
-- The handler `constructive-normal-form-handler` typechecks against
-- `NormalFormHandler` and can be plugged into `WithNormalFormHandler`
-- to produce a `SelfLoopPostulate` value (modulo the residual fields
-- being supplied).
