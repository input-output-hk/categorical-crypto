{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Partial constructive closure of `TwoCascadeResidual.B-prep` by inner
-- induction on the `b` sub-derivation.
--
-- ## Target
--
-- The B-prep σ-cascade case from
-- `Sub/SelfLoopFullClosure2.agda::TwoCascadeResidual.B-prep` is, after
-- expansion,
--
--   p = trans (swap k k' a) (trans (prep k' b) Y)
--     : (k ∷ k' ∷ rest) ↭ (k ∷ k' ∷ rest)
--
-- where
--   * `a : rest ↭ rest'`
--   * `b : (k ∷ rest') ↭ tail'`
--   * `Y : (k' ∷ tail') ↭ (k ∷ k' ∷ rest)`
--   * `Unique (k ∷ k' ∷ rest)` (in particular `k ≢ k'`)
--   * `total-l p ≡ 0` (normal form)
--
-- and `self-rec` is available for `(k ∷ k' ∷ rest) ↭ (k ∷ k' ∷ rest)`
-- of strictly smaller `_≪₃_`-measure.
--
-- ## Strategy: case-split on `b`.
--
-- In normal form (`total-l p ≡ 0`), the inner `b` is right-associated
-- (no `trans (trans _ _) _` subterms), so `b` is one of `refl`,
-- `prep _ _`, `swap _ _ _`, or `trans b₁ b₂` with `b₁` not itself
-- `trans`.
--
-- ### Closeable cases (constructive, strict-size descent via self-rec):
--
-- * `b = refl`:  q = trans (swap k k' a) Y.
-- * `b = prep k b'`:  q = trans (swap k k' (trans a b')) Y.
-- * `b = trans refl b₂`:  q = trans (swap k k' a) (trans (prep k' b₂) Y).
-- * `b = trans (prep k b₁') b₂`:
--      q = trans (swap k k' (trans a b₁')) (trans (prep k' b₂) Y).
-- * `b = trans (trans _ _) _`:  ⊥-elim via `norm`.
--
-- ### Residual cases (Yang-Baxter / nested-σ-block):
--
-- * `b = swap k k'' b'`.
-- * `b = trans (swap k k'' b₁') b₂`.
--
-- These two cases involve nested σ-blocks at adjacent tensor positions
-- (Yang-Baxter braid configuration), which the `_≪₃_` measure does not
-- directly close.  They are isolated into `BPrepSwapResidual`.
--
-- ## What this file delivers
--
--   * `BPrepSwapResidual` — narrowed residual with TWO fields covering
--     the b = swap and b = trans-with-swap-left sub-cases ONLY.
--   * `discharge-B-prep-closed` — a function with the EXACT signature
--     of `TwoCascadeResidual.B-prep`, parameterized by
--     `BPrepSwapResidual`.  Closeable cases are handled constructively.
--
-- The trust surface is STRICTLY NARROWER than the original
-- `TwoCascadeResidual.B-prep` (which covers ALL `b` shapes).
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BPrepSwapResidual` record.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaB_PrepClosed
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
import Data.Nat.Base
open Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-suc; ≤-refl; m≤m+n; n≤1+n; +-assoc; ≤-trans)
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
-- ## Arithmetic helpers (size descent witnesses).

private
  -- Generic suc-non-zero contradiction (for b = trans (trans _ _) _).
  +-suc-nonzero : ∀ a b → a + suc b ≡ 0 → ⊥
  +-suc-nonzero zero    b ()
  +-suc-nonzero (suc a) b ()

  +-zero-l-zero : ∀ a b → a + b ≡ 0 → a ≡ 0
  +-zero-l-zero zero    _ _ = refl
  +-zero-l-zero (suc _) _ ()

  +-zero-r-zero : ∀ a b → a + b ≡ 0 → b ≡ 0
  +-zero-r-zero zero    _ eq = eq
  +-zero-r-zero (suc _) _ ()

  -- Case 1 (b = refl) size descent:
  --   q = trans (swap k k' a) Y         size = 2 + sa + sY
  --   p has size = suc (suc sa + suc (suc (suc sY))) = 5 + sa + sY
  --   q.size < p.size  ⇔  2 + sa + sY < 5 + sa + sY  ✓
  size-refl-< : ∀ sa sY
    → suc (suc sa + sY) < suc (suc sa + suc (suc (suc sY)))
  size-refl-< sa sY
    rewrite +-suc sa (suc (suc sY))
          | +-suc sa (suc sY)
          | +-suc sa sY
    = s≤s (s≤s (s≤s (≤-trans (n≤1+n _) (n≤1+n _))))

  -- Case 2 (b = prep k b') size descent:
  --   q = trans (swap k k' (trans a b')) Y         size = 3 + sa + sb' + sY
  --   p has size                                          5 + sa + sb' + sY
  size-prep-< : ∀ sa sb' sY
    → suc (suc (suc (sa + sb')) + sY) < suc (suc sa + suc (suc (suc sb') + sY))
  size-prep-< sa sb' sY
    rewrite +-suc sa (suc (suc sb' + sY))
          | +-suc sa (suc (sb' + sY))
          | +-suc sa (sb' + sY)
          | sym (+-assoc sa sb' sY)
    = s≤s (s≤s (s≤s (s≤s (n≤1+n (sa + sb' + sY)))))

  -- Case 4a (b = trans refl b₂) size descent:
  --   q = trans (swap k k' a) (trans (prep k' b₂) Y)
  --       size = 1 + (1+sa) + (1 + (1+sb₂) + sY) = 5 + sa + sb₂ + sY
  --   p (b = trans refl b₂):
  --       size (trans refl b₂) = 1 + 1 + sb₂ = 2 + sb₂
  --       size p = 1 + (1+sa) + (1 + (1 + size(trans refl b₂)) + sY)
  --              = 1 + (1+sa) + (1 + (1 + (2 + sb₂)) + sY)
  --              = 7 + sa + sb₂ + sY
  --   q < p by 2.
  size-trans-refl-<
    : ∀ sa sb₂ sY
    → suc (suc sa + suc (suc sb₂ + sY))
      < suc (suc sa + suc (suc (suc (suc sb₂)) + sY))
  size-trans-refl-< sa sb₂ sY
    rewrite +-suc sa (suc (suc (suc sb₂)) + sY)
          | +-suc sa (suc (suc sb₂ + sY))
          | +-suc sa (suc sb₂ + sY)
          | +-suc sa (sb₂ + sY)
    = s≤s (s≤s (s≤s (s≤s (s≤s (n≤1+n (sa + (sb₂ + sY)))))))

  -- Case 4b (b = trans (prep k b₁') b₂) size descent:
  --   q = trans (swap k k' (trans a b₁')) (trans (prep k' b₂) Y)
  --       size = 1 + (1+(1+sa+sb₁')) + (1 + (1+sb₂) + sY)
  --            = 5 + sa + sb₁' + sb₂ + sY
  --   p:
  --       size (prep k b₁') = 1 + sb₁'
  --       size (trans (prep k b₁') b₂) = 1 + (1+sb₁') + sb₂ = 2 + sb₁' + sb₂
  --       size p = 1 + (1+sa) + (1 + (1 + (2+sb₁'+sb₂)) + sY)
  --              = 7 + sa + sb₁' + sb₂ + sY
  --   q < p by 2.
  -- Case 4b (b = trans (prep k b₁') b₂) size descent:
  --   q = trans (swap k k' (trans a b₁')) (trans (prep k' b₂) Y)
  --       size (trans a b₁') = suc (sa + sb₁')
  --       size (swap k k' (trans a b₁')) = suc (suc (sa + sb₁'))
  --       size (prep k' b₂) = suc sb₂
  --       size (trans (prep k' b₂) Y) = suc (suc sb₂ + sY)
  --       size q = suc (suc (suc (sa + sb₁')) + suc (suc sb₂ + sY))
  --   p:
  --       size (prep k b₁') = suc sb₁'
  --       size (trans (prep k b₁') b₂) = suc (suc sb₁' + sb₂)
  --       size (prep k' (trans (prep k b₁') b₂)) = suc (suc (suc sb₁' + sb₂))
  --       size (trans (prep k' (...)) Y) = suc (suc (suc (suc sb₁' + sb₂)) + sY)
  --       size p = suc (suc sa + suc (suc (suc (suc sb₁' + sb₂)) + sY))
  size-trans-prep-<
    : ∀ sa sb₁' sb₂ sY
    → suc (suc (suc (sa + sb₁')) + suc (suc sb₂ + sY))
      < suc (suc sa + suc (suc (suc (suc sb₁' + sb₂)) + sY))
  size-trans-prep-< sa sb₁' sb₂ sY = lemma sa
    where
      -- Induct on sa, with everything else fixed.
      -- The base case sa=0 reduces to a concrete arithmetic comparison.
      -- The step case strips one suc from both sides.
      lemma : ∀ s
        → suc (suc (suc (suc (s + sb₁')) + suc (suc sb₂ + sY)))
          Data.Nat.Base.≤
          suc (suc (s + suc (suc (suc (suc sb₁' + sb₂)) + sY)))
      lemma zero = base
        where
          -- sa = 0: 0 + X reduces to X.
          -- LHS = suc (suc (suc (suc sb₁') + suc (suc sb₂ + sY)))
          --     = suc (suc (suc (suc (sb₁' + suc (suc sb₂ + sY)))))      [defn]
          --     = 5 + sb₁' + sb₂ + sY (semantically, after +-suc etc.)
          -- RHS = suc (suc (suc (suc (suc (suc sb₁' + sb₂)) + sY)))
          --     = 6 + sb₁' + sb₂ + sY (semantically).
          base
            : suc (suc (suc (suc (zero + sb₁')) + suc (suc sb₂ + sY)))
              Data.Nat.Base.≤
              suc (suc (zero + suc (suc (suc (suc sb₁' + sb₂)) + sY)))
          base
            rewrite +-suc sb₁' (suc sb₂ + sY)
                  | +-suc sb₁' (sb₂ + sY)
                  | sym (+-assoc sb₁' sb₂ sY)
            = s≤s (s≤s (s≤s ≤-refl))
      lemma (suc s) = s≤s (lemma s)

--------------------------------------------------------------------------------
-- ## Total-l rules for the cascade.
--
-- Recall (from SelfLoopFullClosure.agda):
--   total-l Perm.refl = 0
--   total-l (Perm.prep _ p) = total-l p
--   total-l (Perm.swap _ _ p) = total-l p
--   total-l (Perm.trans Perm.refl q) = total-l q
--   total-l (Perm.trans (Perm.prep _ p) q) = total-l p + total-l q
--   total-l (Perm.trans (Perm.swap _ _ p) q) = total-l p + total-l q
--   total-l (Perm.trans (Perm.trans p₁ p₂) q) = suc (...)
--
-- For p = trans (swap k k' a) (trans (prep k' b) Y):
--   total-l p
--     = total-l a + total-l (trans (prep k' b) Y)      [outer trans, left=swap]
--     = total-l a + total-l b + total-l Y              [inner trans, left=prep]
--
-- So `total-l p ≡ 0` ⇒ total-l b ≡ 0.
-- For b = trans b₁ b₂:  total-l b = (depends on b₁'s shape)
--   * b₁ = trans _ _:    suc(...) > 0  → contradicts norm.
--   * b₁ = refl:         total-l b₂.
--   * b₁ = prep _ _:     total-l (inner of b₁) + total-l b₂ = 0 + total-l b₂.
--   * b₁ = swap _ _ _:   similar.

private
  -- Extract total-l b ≡ 0 from total-l p ≡ 0.
  -- total-l p = total-l a + total-l b + total-l Y.
  total-l-extract-b
    : ∀ {a} {A : Set a}
        {xs xs' xs''' : List A} {k k' : A}
        (P : xs Perm.↭ xs')
        (B : (k ∷ xs') Perm.↭ xs''')
        (Y : (k' ∷ xs''') Perm.↭ (k ∷ k' ∷ xs))
    → total-l (Perm.trans (Perm.swap k k' P) (Perm.trans (Perm.prep k' B) Y)) ≡ 0
    → total-l B ≡ 0
  total-l-extract-b P B Y eq =
    +-zero-l-zero (total-l B) (total-l Y)
      (+-zero-r-zero (total-l P) (total-l B + total-l Y) eq)

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- Two residual fields, covering the σ-block / Yang-Baxter sub-cases:
--   * b = swap k k'' b'.
--   * b = trans (swap k k'' b₁') b₂.

record BPrepSwapResidual : Set where
  field
    -- Case 3: b = swap k k'' b'.
    bprep-swap-cascade
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

    -- Sub-case 4c: b = trans (swap k k'' b₁') b₂.
    bprep-trans-swap-cascade
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {rest rest' rest'' ms' tail' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ rest')
          (b₁' : rest'' Perm.↭ ms')
          -- b₁ = swap k k'' b₁' : (k ∷ rest') ↭ (k'' ∷ k ∷ ms')
          -- requires rest' = k'' ∷ rest''
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

--------------------------------------------------------------------------------
-- ## Permute-equivalence lemmas (for each closeable case).

module WithBPrepSwapResidual (res : BPrepSwapResidual) where
  open BPrepSwapResidual res

  -- Case 1: permute p ≈Term permute (trans (swap k k' a) Y)
  -- where p = trans (swap k k' a) (trans (prep k' refl) Y).
  case-refl-permute-eq
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {rest rest' : List (Fin n)}
        (a : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k' ∷ rest))
    → let p = Perm.trans (Perm.swap k k' a)
                (Perm.trans (Perm.prep k' Perm.refl) Y)
          q = Perm.trans (Perm.swap k k' a) Y
      in permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  case-refl-permute-eq vlab {k} {k'} {rest} {rest'} a Y =
    let pa = permute (PermProp.map⁺ vlab a)
        pY = permute (PermProp.map⁺ vlab Y)
        T_a = (id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    in begin
         (pY ∘ (id ⊗₁ id)) ∘ T_a
           ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl id⊗id≈id) ≈-Term-refl ⟩
         (pY ∘ id) ∘ T_a
           ≈⟨ ∘-resp-≈ idʳ ≈-Term-refl ⟩
         pY ∘ T_a
       ∎

  -- Case 2: permute p ≈Term permute (trans (swap k k' (trans a b')) Y)
  -- where p = trans (swap k k' a) (trans (prep k' (prep k b')) Y).
  case-prep-permute-eq
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {rest rest' tail'' : List (Fin n)}
        (a : rest Perm.↭ rest')
        (b' : rest' Perm.↭ tail'')
        (Y : (k' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ rest))
    → let p = Perm.trans (Perm.swap k k' a)
                (Perm.trans (Perm.prep k' (Perm.prep k b')) Y)
          q = Perm.trans (Perm.swap k k' (Perm.trans a b')) Y
      in permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  case-prep-permute-eq vlab {k} {k'} {rest} {rest'} {tail''} a b' Y =
    let pa = permute (PermProp.map⁺ vlab a)
        pb' = permute (PermProp.map⁺ vlab b')
        pY = permute (PermProp.map⁺ vlab Y)
        σ-block = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    in begin
         (pY ∘ (id ⊗₁ (id ⊗₁ pb'))) ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ σ-block)
           ≈⟨ assoc ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb')) ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ σ-block))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
         pY ∘ (((id ⊗₁ (id ⊗₁ pb')) ∘ (id ⊗₁ (id ⊗₁ pa))) ∘ σ-block)
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
         pY ∘ (((id ∘ id) ⊗₁ ((id ⊗₁ pb') ∘ (id ⊗₁ pa))) ∘ σ-block)
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ (⊗-resp-≈ idˡ ≈-Term-refl) ≈-Term-refl) ⟩
         pY ∘ ((id ⊗₁ ((id ⊗₁ pb') ∘ (id ⊗₁ pa))) ∘ σ-block)
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym ⊗-∘-dist)) ≈-Term-refl) ⟩
         pY ∘ ((id ⊗₁ ((id ∘ id) ⊗₁ (pb' ∘ pa))) ∘ σ-block)
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl)) ≈-Term-refl) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ (pb' ∘ pa))) ∘ σ-block)
       ∎

  -- Case 4a: permute p ≈Term permute (trans (swap k k' a) (trans (prep k' b₂) Y))
  -- where p = trans (swap k k' a) (trans (prep k' (trans refl b₂)) Y).
  --
  -- The only difference is the inner `prep k' (trans refl b₂)` vs `prep k' b₂`.
  -- permute (prep k' (trans refl b₂)) = id ⊗ (permute b₂ ∘ id) ≈ id ⊗ permute b₂ = permute (prep k' b₂).
  case-trans-refl-permute-eq
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {rest rest' tail' : List (Fin n)}
        (a : rest Perm.↭ rest')
        (b₂ : (k ∷ rest') Perm.↭ tail')
        (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
    → let p = Perm.trans (Perm.swap k k' a)
                (Perm.trans (Perm.prep k' (Perm.trans Perm.refl b₂)) Y)
          q = Perm.trans (Perm.swap k k' a)
                (Perm.trans (Perm.prep k' b₂) Y)
      in permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  case-trans-refl-permute-eq vlab {k} {k'} {rest} {rest'} {tail'} a b₂ Y =
    let pa = permute (PermProp.map⁺ vlab a)
        pb₂ = permute (PermProp.map⁺ vlab b₂)
        pY = permute (PermProp.map⁺ vlab Y)
        T_a = (id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    in begin
         (pY ∘ (id ⊗₁ (pb₂ ∘ id))) ∘ T_a
           ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl idʳ)) ≈-Term-refl ⟩
         (pY ∘ (id ⊗₁ pb₂)) ∘ T_a
       ∎

  -- Case 4b: permute p ≈Term permute (trans (swap k k' (trans a b₁')) (trans (prep k' b₂) Y))
  -- where p = trans (swap k k' a) (trans (prep k' (trans (prep k b₁') b₂)) Y).
  case-trans-prep-permute-eq
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {rest rest' ms-of-b₁' tail' : List (Fin n)}
        (a : rest Perm.↭ rest')
        (b₁' : rest' Perm.↭ ms-of-b₁')
        (b₂ : (k ∷ ms-of-b₁') Perm.↭ tail')
        (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
    → let p = Perm.trans (Perm.swap k k' a)
                (Perm.trans (Perm.prep k' (Perm.trans (Perm.prep k b₁') b₂)) Y)
          q = Perm.trans (Perm.swap k k' (Perm.trans a b₁'))
                (Perm.trans (Perm.prep k' b₂) Y)
      in permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  case-trans-prep-permute-eq vlab {k} {k'} {rest} {rest'} {ms-of-b₁'} {tail'} a b₁' b₂ Y =
    let pa = permute (PermProp.map⁺ vlab a)
        pb₁' = permute (PermProp.map⁺ vlab b₁')
        pb₂ = permute (PermProp.map⁺ vlab b₂)
        pY = permute (PermProp.map⁺ vlab Y)
        σ-block = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
        -- LHS:
        --   (pY ∘ (id ⊗ (pb₂ ∘ (id ⊗ pb₁')))) ∘ ((id ⊗ (id ⊗ pa)) ∘ σ-block)
        -- RHS:
        --   (pY ∘ (id ⊗ pb₂)) ∘ ((id ⊗ (id ⊗ (pb₁' ∘ pa))) ∘ σ-block)
        --
        -- We bridge via:
        --   id ⊗ (pb₂ ∘ (id ⊗ pb₁')) ≈ (id ⊗ pb₂) ∘ (id ⊗ (id ⊗ pb₁'))
        --   (id ⊗ (id ⊗ pb₁')) ∘ (id ⊗ (id ⊗ pa)) ≈ id ⊗ (id ⊗ (pb₁' ∘ pa))
    in begin
         (pY ∘ (id ⊗₁ (pb₂ ∘ (id ⊗₁ pb₁')))) ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ σ-block)
           -- Step 1: distribute the outer (id ⊗ (pb₂ ∘ ...)).
           ≈⟨ ∘-resp-≈
                (∘-resp-≈ ≈-Term-refl
                  (≈-Term-trans (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl)
                                ⊗-∘-dist))
                ≈-Term-refl ⟩
         (pY ∘ ((id ⊗₁ pb₂) ∘ (id ⊗₁ (id ⊗₁ pb₁')))) ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ σ-block)
           ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
         ((pY ∘ (id ⊗₁ pb₂)) ∘ (id ⊗₁ (id ⊗₁ pb₁'))) ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ σ-block)
           ≈⟨ assoc ⟩
         (pY ∘ (id ⊗₁ pb₂)) ∘ ((id ⊗₁ (id ⊗₁ pb₁')) ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ σ-block))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
         (pY ∘ (id ⊗₁ pb₂)) ∘ (((id ⊗₁ (id ⊗₁ pb₁')) ∘ (id ⊗₁ (id ⊗₁ pa))) ∘ σ-block)
           -- Step 2: fuse (id ⊗ (id ⊗ pb₁')) ∘ (id ⊗ (id ⊗ pa)) ≈ id ⊗ (id ⊗ (pb₁' ∘ pa))
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈
                  (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                    (≈-Term-trans (⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist))
                                  (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl))))
                  ≈-Term-refl) ⟩
         (pY ∘ (id ⊗₁ pb₂)) ∘ ((id ⊗₁ (id ⊗₁ (pb₁' ∘ pa))) ∘ σ-block)
       ∎

  -- Main discharge function.

  discharge-B-prep-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {rest rest' tail' : List (Fin n)}
        (uniq : Unique (k ∷ k' ∷ rest))
        (a : rest Perm.↭ rest')
        (b : (k ∷ rest') Perm.↭ tail')
        (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
        (acc-p
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
            → let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let p = Perm.trans (Perm.swap k k' a)
                  (Perm.trans (Perm.prep k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ===================================================================
  -- Case 1: b = refl   →   q = trans (swap k k' a) Y, strict size <.
  -- ===================================================================
  discharge-B-prep-closed vlab {k} {k'} {rest} {rest'} {.(k ∷ rest')}
      uniq a Perm.refl Y acc-p norm self-rec =
    let p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' Perm.refl) Y)
        q = Perm.trans (Perm.swap k k' a) Y

        size-< : size q < size p
        size-< = size-refl-< (size a) (size Y)

        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l p}
                       {c₁ = swap-count q}
                       {c₂ = swap-count p}
                       size-<

        ih = self-rec q sub-≪
        eq = case-refl-permute-eq vlab a Y
    in ≈-Term-trans eq ih

  -- ===================================================================
  -- Case 2: b = prep .k b'   →   q = trans (swap k k' (trans a b')) Y.
  -- ===================================================================
  discharge-B-prep-closed vlab {k} {k'} {rest} {rest'} {.(k ∷ _)}
      uniq a (Perm.prep .k b') Y acc-p norm self-rec =
    let p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' (Perm.prep k b')) Y)
        q = Perm.trans (Perm.swap k k' (Perm.trans a b')) Y

        size-< : size q < size p
        size-< = size-prep-< (size a) (size b') (size Y)

        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l p}
                       {c₁ = swap-count q}
                       {c₂ = swap-count p}
                       size-<

        ih = self-rec q sub-≪
        eq = case-prep-permute-eq vlab a b' Y
    in ≈-Term-trans eq ih

  -- ===================================================================
  -- Case 3: b = swap k k'' b'   →   residual.
  -- ===================================================================
  discharge-B-prep-closed vlab {k} {k'} {rest} {.(_ ∷ _)} {.(_ ∷ k ∷ _)}
      uniq a (Perm.swap .k k'' b') Y acc-p norm self-rec =
    bprep-swap-cascade vlab uniq a b' Y acc-p norm self-rec

  -- ===================================================================
  -- Case 4a: b = trans refl b₂   →   q = trans (swap k k' a) (trans (prep k' b₂) Y).
  -- ===================================================================
  discharge-B-prep-closed vlab {k} {k'} {rest} {rest'} {tail'}
      uniq a (Perm.trans Perm.refl b₂) Y acc-p norm self-rec =
    let p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' (Perm.trans Perm.refl b₂)) Y)
        q = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' b₂) Y)

        size-< : size q < size p
        size-< = size-trans-refl-< (size a) (size b₂) (size Y)

        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l p}
                       {c₁ = swap-count q}
                       {c₂ = swap-count p}
                       size-<

        ih = self-rec q sub-≪
        eq = case-trans-refl-permute-eq vlab a b₂ Y
    in ≈-Term-trans eq ih

  -- ===================================================================
  -- Case 4b: b = trans (prep .k b₁') b₂
  --   →   q = trans (swap k k' (trans a b₁')) (trans (prep k' b₂) Y).
  -- ===================================================================
  discharge-B-prep-closed vlab {k} {k'} {rest} {rest'} {tail'}
      uniq a (Perm.trans (Perm.prep .k b₁') b₂) Y acc-p norm self-rec =
    let p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.prep k' (Perm.trans (Perm.prep k b₁') b₂)) Y)
        q = Perm.trans (Perm.swap k k' (Perm.trans a b₁'))
              (Perm.trans (Perm.prep k' b₂) Y)

        size-< : size q < size p
        size-< = size-trans-prep-< (size a) (size b₁') (size b₂) (size Y)

        sub-≪ : measure q ≪₃ measure p
        sub-≪ = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l p}
                       {c₁ = swap-count q}
                       {c₂ = swap-count p}
                       size-<

        ih = self-rec q sub-≪
        eq = case-trans-prep-permute-eq vlab a b₁' b₂ Y
    in ≈-Term-trans eq ih

  -- ===================================================================
  -- Case 4c: b = trans (swap .k k'' b₁') b₂   →   residual.
  -- ===================================================================
  discharge-B-prep-closed vlab {k} {k'} {rest} {.(_ ∷ _)} {tail'}
      uniq a (Perm.trans (Perm.swap .k k'' b₁') b₂) Y acc-p norm self-rec =
    bprep-trans-swap-cascade vlab uniq a b₁' refl b₂ Y acc-p norm self-rec

  -- ===================================================================
  -- Case 4d: b = trans (trans _ _) _   →   IMPOSSIBLE (total-l p > 0).
  --
  -- total-l p = total-l a + total-l b + total-l Y
  --           = total-l a + suc(...) + total-l Y
  -- ≡ 0 is impossible (suc(_) + _ ≢ 0).
  -- ===================================================================
  discharge-B-prep-closed vlab {k} {k'} {rest} {rest'} {tail'}
      uniq a (Perm.trans (Perm.trans b₁₁ b₁₂) b₂) Y acc-p norm self-rec =
    let -- total-l p = total-l a + total-l (trans (trans b₁₁ b₁₂) b₂) + total-l Y
        -- total-l (trans (trans b₁₁ b₁₂) b₂) = suc (total-l b₁₁ + total-l b₁₂ + total-l b₂)
        -- So total-l p = total-l a + suc(...) + total-l Y ≡ 0 → contradiction.
        --
        -- We use total-l-extract-b to extract total-l b ≡ 0:
        b = Perm.trans (Perm.trans b₁₁ b₁₂) b₂
        tl-b-eq : total-l b ≡ 0
        tl-b-eq = total-l-extract-b a b Y norm
        -- Now `total-l b = suc (total-l b₁₁ + total-l b₁₂ + total-l b₂)`,
        -- which is `suc _`, contradicting `tl-b-eq : suc _ ≡ 0`.
    in ⊥-elim (suc-non-zero tl-b-eq)
    where
      suc-non-zero : ∀ {n : ℕ} → suc n ≡ 0 → ⊥
      suc-non-zero ()

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `BPrepSwapResidual` — narrowed residual record with TWO fields
--     packaging the b = swap and b = trans-with-swap-left sub-cases.
--   * `discharge-B-prep-closed` (in `module WithBPrepSwapResidual`) —
--     a function with the EXACT signature of
--     `TwoCascadeResidual.B-prep`, parameterized by `BPrepSwapResidual`.
--
-- The discharge closes constructively:
--   * `b = refl` via self-rec with q = trans (swap k k' a) Y.
--   * `b = prep k b'` via self-rec with q = trans (swap k k' (trans a b')) Y.
--   * `b = trans refl b₂` via self-rec with q = trans (swap k k' a) (trans (prep k' b₂) Y).
--   * `b = trans (prep k b₁') b₂` via self-rec with
--      q = trans (swap k k' (trans a b₁')) (trans (prep k' b₂) Y).
--   * `b = trans (trans _ _) _` via ⊥-elim from `norm`.
-- The discharge delegates to BPrepSwapResidual for:
--   * `b = swap k k'' b'`.
--   * `b = trans (swap k k'' b₁') b₂`.
--
-- The trust surface is STRICTLY NARROWER than the original
-- `TwoCascadeResidual.B-prep` (which covers ALL b shapes uniformly).
--
-- ## Discharge status: PARTIAL.
--   The constructive closure depends on `BPrepSwapResidual`.  A consumer
--   can construct this record via:
--     (a) Yang-Baxter / σ-block braid coherence at the symbolic level.
--     (b) Faithful interpretation into a concrete symmetric monoidal
--         category (e.g., FinSet via a Yoneda embedding).
--     (c) Extension of the lex measure to capture "leading swap count"
--         or "nested-σ-block depth".
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BPrepSwapResidual` record.
--------------------------------------------------------------------------------
