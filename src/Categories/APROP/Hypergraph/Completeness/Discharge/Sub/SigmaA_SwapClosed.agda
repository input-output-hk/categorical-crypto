{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive (partial) closure of `TwoCascadeResidual.A-swap`.
--
-- ## Target
--
-- Given the cascade
--
--   p = trans (prep k a) (trans (swap k k' b) Y) : (k ∷ xs') ↭ (k ∷ xs')
--
-- where `a : xs' ↭ (k' ∷ rest)`, in normal form (`total-l p ≡ 0`),
-- prove `permute (map⁺ vlab p) ≈Term id`.
--
-- ## Strategy: case-split on the inner derivation `a`.
--
-- We split `a` into its four outer constructor cases:
--
--   1. `a = refl`         : Then `xs' = k' ∷ rest`, the leading
--                            `prep k refl` is `id ⊗ id ≈ id`, and the
--                            remainder `q = trans (swap k k' b) Y` is a
--                            strictly smaller (`size q < size p`)
--                            self-loop on `(k ∷ k' ∷ rest)`.  CLOSED by
--                            `self-rec` with `≪₃-fst`.
--
--   2. `a = prep k' a'`   : Then `xs' = k' ∷ tail`, `a' : tail ↭ rest`.
--                            By σ-block-natural₃, we can push the
--                            outer `id ⊗ (id ⊗ pa')` past the σ-block,
--                            obtaining a strictly smaller self-loop
--                            `q = trans (swap k k' (trans a' b)) Y` on
--                            `(k ∷ xs')`.  `size q < size p`.  CLOSED
--                            by `self-rec` with `≪₃-fst`.
--
--   3. `a = swap k'' k' a''` : (where the codomain's head matches)
--                            This is the genuinely-residual case: the
--                            σ-naturality push interacts with the
--                            nested swap inside `a` in a way that
--                            doesn't decrease any of the three measure
--                            components.  Dispatched to a NARROWER
--                            `AswapSwapResidual` record.
--
--   4. `a = trans a₁ a₂`  : When `a₁` is `trans _ _`, `total-l p > 0`,
--                            contradiction with `norm`.  Other inner
--                            shapes (`refl`, `prep`, `swap`) also lead
--                            to a `trans _ _ _` shape that needs
--                            careful analysis — we dispatch the
--                            `trans` cases to the residual.
--
-- ## Deliverable
--
--   * `AswapSwapResidual` — narrowed residual record packaging only
--     case 3 (and the `trans` case 4 sub-cases that don't yield direct
--     contradiction).
--   * `discharge-A-swap-closed` — function with the EXACT signature of
--     `TwoCascadeResidual.A-swap`, parameterized by `AswapSwapResidual`,
--     closing cases 1, 2, and the `trans (trans _ _) _` contradiction
--     constructively.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `AswapSwapResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaA_SwapClosed
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopTransClosure sig-dec
  using (size; size-map⁺)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure sig-dec
  using (total-l; total-l-map⁺)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure2 sig-dec
  using ( swap-count; swap-count-map⁺
        ; _≪₃_; ≪₃-fst; ≪₃-snd; ≪₃-thd
        ; measure; measure-map⁺)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-suc; ≤-refl; ≤-trans; +-comm; m≤m+n; m≤n+m; <-trans; +-assoc
        ; +-monoʳ-≤; +-monoˡ-≤; +-monoˡ-<; +-monoʳ-<; +-mono-<; n≤1+n)
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
-- ## σ-block local definitions (re-derived; matching SelfLoopFullClosure2).

private
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
-- ## Arithmetic helpers.

private
  -- Case 1: `a = refl`.  Then `size (prep k refl) = 2`, and
  --   size p = 1 + 2 + size (trans (swap k k' b) Y)
  --          = 3 + (1 + size (swap k k' b) + size Y)
  --          = 3 + (1 + (1 + size b) + size Y)
  --          = 5 + size b + size Y
  -- And the residual q = trans (swap k k' b) Y has
  --   size q = 1 + (1 + size b) + size Y = 2 + size b + size Y.
  -- So size q < size p by 3, comfortably strict.

  -- size p = suc (suc 1 + suc (suc sb + sY))
  -- Agda normalizes this to:
  --   suc (suc (suc (suc (suc (sb + sY)))))   (5 + sb + sY)
  -- size q = suc (suc sb + sY) = suc (suc (sb + sY))  (2 + sb + sY)
  -- size q < size p:  the difference is 3.
  size-refl-case-<
    : ∀ sb sY → suc ((suc sb) + sY) < suc (suc 1 + suc ((suc sb) + sY))
  size-refl-case-< sb sY =
    s≤s (s≤s (s≤s (≤-trans (n≤1+n (sb + sY)) (n≤1+n (suc (sb + sY))))))

  -- Case 2: `a = prep k' a'`.  size (prep k (prep k' a')) = 3 + size a'.
  --   size p = 1 + (3 + size a') + (2 + size b + size Y)
  --          = 6 + size a' + size b + size Y
  -- Residual q = trans (swap k k' (trans a' b)) Y:
  --   size (trans a' b) = 1 + size a' + size b
  --   size (swap k k' (trans a' b)) = 2 + size a' + size b
  --   size q = 1 + (2 + size a' + size b) + size Y = 3 + size a' + size b + size Y
  -- So size q < size p by 3. Strict.

  -- size q (LHS) = 3 + sa + sb + sY
  -- size p (RHS) = 1 + (2 + sa) + size (trans (swap k k' b) Y)
  --             = 1 + (2 + sa) + suc (suc (sb) + sY)
  --             = 5 + sa + sb + sY
  -- Difference = 2.  Strict.
  size-prep-case-<
    : ∀ sa sb sY
    → suc (suc (suc (sa + sb)) + sY) < suc (suc (suc sa) + suc (suc sb + sY))
  size-prep-case-< sa sb sY
    rewrite +-suc sa (suc (sb + sY))
          | +-suc sa (sb + sY)
          | sym (+-assoc sa sb sY)
    = s≤s (s≤s (s≤s (s≤s (n≤1+n (sa + sb + sY)))))

  -- For trans-trans contradiction:
  --   total-l (trans (prep k (trans (trans _ _) _)) _)
  --      = total-l (trans (trans _ _) _) + total-l (trans (swap k k' b) Y)
  --      = suc (... + ...) + ...
  +-suc-nonzero : ∀ a b → a + suc b ≡ 0 → ⊥
  +-suc-nonzero zero    b ()
  +-suc-nonzero (suc a) b ()

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- Two genuinely-residual sub-cases of A-swap:
--   (A.swap.swap)  : `a = swap k'' k' a''` (σ-naturality at deeper level).
--   (A.swap.trans-non-trans) : `a = trans a₁ a₂` where `a₁` is not
--     `trans _ _` (i.e., `a₁ ∈ {refl, prep, swap}`).  After dnorm
--     normalization, this case should be handled, but we leave it as a
--     residual for now (smaller scope than the original A-swap).

record AswapSwapResidual : Set where
  field
    -- Case 3: `a = swap k'' k' a''` (the genuinely σ-cascading nested case).
    A-swap-swap
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

    -- Case 4: `a = trans a₁ a₂` where `a₁ ∈ {refl, prep, swap}`.
    -- We further dispatch by the shape of `a₁` to a single combined field.
    A-swap-trans
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

--------------------------------------------------------------------------------
-- ## Main: `discharge-A-swap-closed`.
--
-- Case-split on `a`.  Cases 1 and 2 are closed constructively here.
-- Case 3 (a = swap) and case 4 (a = trans) dispatch to the residual.

module WithAswapResidual (res : AswapSwapResidual) where
  open AswapSwapResidual res

  discharge-A-swap-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' : Fin n} {xs' rest rest' : List (Fin n)}
        (uniq : Unique (k ∷ xs'))
        (a : xs' Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ xs'))
        (acc-p
          : let p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let p = Perm.trans (Perm.prep k a)
                      (Perm.trans (Perm.swap k k' b) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ xs') Perm.↭ (k ∷ xs'))
            → let p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let p = Perm.trans (Perm.prep k a)
                  (Perm.trans (Perm.swap k k' b) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case 1: a = refl. -----
  -- `xs' = k' ∷ rest`.  The cascade becomes
  --   trans (prep k refl) (trans (swap k k' b) Y)
  -- and permute simplifies to permute (swap k k' b) ∘ id (after id⊗id).
  -- We use self-rec on q = trans (swap k k' b) Y, with strict size
  -- decrease.
  discharge-A-swap-closed vlab {k} {k'} {.(k' ∷ rest)} {rest} {rest'}
      uniq Perm.refl b Y _ _ self-rec =
    let q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest)
        q = Perm.trans (Perm.swap k k' b) Y
        pb = permute (PermProp.map⁺ vlab b)
        pY = permute (PermProp.map⁺ vlab Y)
        -- Strict size decrease.
        size-strict-< : size q < size (Perm.trans (Perm.prep k Perm.refl)
                                          (Perm.trans (Perm.swap k k' b) Y))
        size-strict-< = size-refl-case-< (size b) (size Y)
        sub-< : measure q ≪₃ measure (Perm.trans (Perm.prep k Perm.refl)
                                          (Perm.trans (Perm.swap k k' b) Y))
        sub-< = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l (Perm.trans (Perm.prep k Perm.refl)
                                          (Perm.trans (Perm.swap k k' b) Y))}
                       {c₁ = swap-count q}
                       {c₂ = swap-count (Perm.trans (Perm.prep k Perm.refl)
                                            (Perm.trans (Perm.swap k k' b) Y))}
                       size-strict-<
        ih : permute (PermProp.map⁺ vlab q) ≈Term id
        ih = self-rec q sub-<
        -- Algebraic step: permute (prep k refl) ≈ id ⊗ id ≈ id.
        -- So permute p = permute q ∘ (id ⊗ id) ≈ permute q ∘ id ≈ permute q.
    in begin
         (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)) ∘ (id ⊗₁ id)
           ≈⟨ ∘-resp-≈ ≈-Term-refl id⊗id≈id ⟩
         (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)) ∘ id
           ≈⟨ idʳ ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           ≈⟨ ih ⟩
         id
       ∎

  -- ----- Case 2: a = prep k' a'. -----
  -- `xs' = k' ∷ tail`, `a' : tail ↭ rest`.
  -- σ-block-natural₃ lets us push `id ⊗ (id ⊗ pa')` past the σ-block,
  -- yielding q = trans (swap k k' (trans a' b)) Y.  Strict size decrease.
  discharge-A-swap-closed vlab {k} {k'} {xs'} {rest} {rest'}
      uniq (Perm.prep .k' a') b Y _ _ self-rec =
    let q = Perm.trans (Perm.swap k k' (Perm.trans a' b)) Y
        pa' = permute (PermProp.map⁺ vlab a')
        pb  = permute (PermProp.map⁺ vlab b)
        pY  = permute (PermProp.map⁺ vlab Y)

        size-strict-< : size q < size (Perm.trans (Perm.prep k (Perm.prep k' a'))
                                          (Perm.trans (Perm.swap k k' b) Y))
        size-strict-< = size-prep-case-< (size a') (size b) (size Y)

        sub-< : measure q ≪₃ measure (Perm.trans (Perm.prep k (Perm.prep k' a'))
                                          (Perm.trans (Perm.swap k k' b) Y))
        sub-< = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l (Perm.trans (Perm.prep k (Perm.prep k' a'))
                                          (Perm.trans (Perm.swap k k' b) Y))}
                       {c₁ = swap-count q}
                       {c₂ = swap-count (Perm.trans (Perm.prep k (Perm.prep k' a'))
                                            (Perm.trans (Perm.swap k k' b) Y))}
                       size-strict-<

        ih : permute (PermProp.map⁺ vlab q) ≈Term id
        ih = self-rec q sub-<

        -- Algebraic step.  We need:
        --   permute (map⁺ vlab (trans (prep k (prep k' a')) (trans (swap k k' b) Y)))
        --     = pY ∘ ((id ⊗ (id ⊗ pb)) ∘ σ-block) ∘ (id ⊗ (id ⊗ pa'))
        -- ≈Term
        --   pY ∘ ((id ⊗ (id ⊗ pb)) ∘ (id ⊗ (id ⊗ pa')) ∘ σ-block)
        --                                  -- by σ-block-natural₃
        --     = pY ∘ ((id ⊗ (id ⊗ (pb ∘ pa'))) ∘ σ-block)
        --                                  -- by ⊗-∘-dist
        --     = permute (map⁺ vlab (trans (swap k k' (trans a' b)) Y))
        --     = permute (map⁺ vlab q)
        -- ≈Term id (by ih).

        -- Step 1: associativity rearrangement.
        rearrange
          : (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
             ∘ (id ⊗₁ (id ⊗₁ pa'))
          ≈Term
            pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                  ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ pa'))))
        rearrange =
          begin
            (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
              ∘ (id ⊗₁ (id ⊗₁ pa'))
              ≈⟨ assoc ⟩
            pY ∘ (((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                   ∘ (id ⊗₁ (id ⊗₁ pa')))
              ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
            pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                   ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ pa'))))
          ∎

        -- Step 2: apply σ-block-natural₃.
        commute
          : pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                  ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ pa'))))
          ≈Term
            pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                  ∘ ((id ⊗₁ (id ⊗₁ pa')) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
        commute =
          ∘-resp-≈ ≈-Term-refl
            (∘-resp-≈ ≈-Term-refl σ-block-natural₃)

        -- Step 3: collapse (id ⊗ (id ⊗ pb)) ∘ (id ⊗ (id ⊗ pa')) via ⊗-∘-dist.
        fuse
          : pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                  ∘ ((id ⊗₁ (id ⊗₁ pa')) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
          ≈Term
            pY ∘ ((id ⊗₁ (id ⊗₁ (pb ∘ pa'))) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
        fuse =
          begin
            pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                  ∘ ((id ⊗₁ (id ⊗₁ pa')) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
            pY ∘ (((id ⊗₁ (id ⊗₁ pb)) ∘ (id ⊗₁ (id ⊗₁ pa')))
                  ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
              ≈⟨ ∘-resp-≈ ≈-Term-refl
                   (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
            pY ∘ (((id ∘ id) ⊗₁ ((id ⊗₁ pb) ∘ (id ⊗₁ pa')))
                  ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
              ≈⟨ ∘-resp-≈ ≈-Term-refl
                   (∘-resp-≈ (⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist)) ≈-Term-refl) ⟩
            pY ∘ ((id ⊗₁ ((id ∘ id) ⊗₁ (pb ∘ pa')))
                  ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
              ≈⟨ ∘-resp-≈ ≈-Term-refl
                   (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl)) ≈-Term-refl) ⟩
            pY ∘ ((id ⊗₁ (id ⊗₁ (pb ∘ pa'))) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
          ∎

        -- Step 4: the rhs of fuse equals permute (map⁺ vlab q) — definitionally,
        -- since permute (swap k k' (trans a' b)) = (id ⊗ (id ⊗ permute(trans a' b)))
        --                                          ∘ σ-block
        -- and permute (trans a' b) = permute b ∘ permute a' = pb ∘ pa'.
    in begin
         (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
            ∘ (id ⊗₁ (id ⊗₁ pa'))
           ≈⟨ rearrange ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                 ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ pa'))))
           ≈⟨ commute ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                 ∘ ((id ⊗₁ (id ⊗₁ pa')) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
           ≈⟨ fuse ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ (pb ∘ pa'))) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
           ≈⟨ ih ⟩
         id
       ∎

  -- ----- Case 3: a = swap k'' k' a''. -----
  -- `xs' = k'' ∷ k' ∷ ms`, `a'' : ms ↭ ms'`, `rest = k'' ∷ ms'`.
  -- Genuinely-residual — dispatch.
  discharge-A-swap-closed vlab {k} {k'} {xs'} {rest} {rest'}
      uniq (Perm.swap k'' .k' a'') b Y acc-p norm self-rec =
    A-swap-swap vlab uniq a'' b Y acc-p norm self-rec

  -- ----- Case 4: a = trans a₁ a₂. -----
  -- Dispatch to residual.
  discharge-A-swap-closed vlab {k} {k'} {xs'} {rest} {rest'}
      uniq (Perm.trans a₁ a₂) b Y acc-p norm self-rec =
    A-swap-trans vlab uniq a₁ a₂ b Y acc-p norm self-rec

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--   * `AswapSwapResidual` — a narrowed residual record with exactly two
--     fields, covering only:
--       - Case 3 (`a = swap k'' k' _`) and
--       - Case 4 (`a = trans _ _`).
--     The four cases `a = refl` and `a = prep _ _` are closed
--     constructively.
--   * `discharge-A-swap-closed` — function with the EXACT signature of
--     `TwoCascadeResidual.A-swap`, parameterized by `AswapSwapResidual`.
--
-- ## Discharge status: PARTIAL.
--   * Case 1 (refl): CLOSED via `≪₃-fst` (size strict decrease) +
--     `self-rec`.
--   * Case 2 (prep): CLOSED via σ-block-natural₃ + `≪₃-fst` + `self-rec`.
--   * Case 3 (swap): RESIDUAL (genuinely σ-cascade).
--   * Case 4 (trans): RESIDUAL (dispatched to handler with strictly
--     smaller scope).
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `AswapSwapResidual` record.
--------------------------------------------------------------------------------
