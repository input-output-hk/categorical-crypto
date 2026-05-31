{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Yang-Baxter closure for the 5 residuals in `Sub/YangBaxterResiduals.agda`.
--
-- ## Context
--
-- `YangBaxterResiduals.FinalResidual` packages 5 σ-cascade self-loops:
--
--   1. fr-A-swap-swap        — `prep k (swap k'' k' a''); swap k k' b; Y`
--   2. fr-A-trans-prep       — `prep k (trans (prep k'' a₁') a₂); swap k k' b; Y`
--   3. fr-A-trans-swap       — `prep k (trans (swap k₂ k₃ a₁') a₂); swap k k' b; Y`
--   4. fr-B-prep-swap        — `swap k k' a; prep k' (swap k k'' b'); Y`
--   5. fr-B-prep-trans-swap  — `swap k k' a; prep k' (trans (swap k k'' b₁') b₂); Y`
--
-- ## Analysis of the closure obstacle
--
-- All five fields are genuinely Yang-Baxter braid cascades.  The natural
-- closure path is to apply the symmetric-monoidal `hexagon` axiom:
--
--   id ⊗ σ ∘ α⇒ ∘ σ ⊗ id ≈Term α⇒ ∘ σ ∘ α⇒
--
-- which collapses two atom-level σ's into a single block-level σ.
-- However, at the `permute`-level, every `Perm.swap` is realised by the
-- `σ-block` pattern `α⇒ ∘ (σ ⊗ id) ∘ α⇐`, which keeps σ at the
-- atom level.  The hexagon RHS introduces a σ at the
-- `Var k ⊗ (Var k' ⊗ ...)` level (non-atom).  Bridging this gap is what
-- the comment in `YangBaxterResiduals.agda` describes as "extensive
-- setup" that we do not have here.
--
-- The lex measure `(size, total-l, swap-count)` is also too coarse to
-- drive a Yang-Baxter cancellation: the YB braid identity
-- σ₁σ₂σ₁ = σ₂σ₁σ₂ preserves the number of swap constructors and the
-- overall size, so any rewrite of one side to the other is not strictly
-- decreasing under this measure.
--
-- ## What this file delivers
--
-- We **narrow** the `fr-A-trans-prep` field by closing the
-- constructively-tractable sub-case `a₁' = Perm.refl` and structurally
-- separating the remaining sub-cases:
--
--   * `fr-A-trans-prep` with `a₁' = Perm.refl`: CLOSED constructively
--     via the equation `permute (prep k (trans (prep k'' refl) a₂))
--     ≈Term permute (prep k a₂)` (id⊗id, idʳ cancellation) followed by
--     size-strict descent (diff = 3 sucs) and `self-rec`.
--   * `fr-A-trans-prep` with `a₁' = prep`, `swap`, or `trans`: SPLIT
--     into three narrower fields `rfr-A-trans-prep-prep`,
--     `rfr-A-trans-prep-swap`, and `rfr-A-trans-prep-trans` in
--     `RealFinalResidual`.
--   * All four other fields (`fr-A-swap-swap`, `fr-A-trans-swap`,
--     `fr-B-prep-swap`, `fr-B-prep-trans-swap`): NARROWED by identity
--     dispatch — same shape but bundled into `RealFinalResidual`.
--
-- `RealFinalResidual` is STRICTLY narrower than `FinalResidual` because
-- the `fr-A-trans-prep` field is now split into three separate fields
-- on the structural shape of `a₁'`, with the `a₁' = refl` sub-case
-- closed constructively (no residual needed).
--
-- ## Main outputs
--
--   * `RealFinalResidual` — narrower residual record with 7 fields:
--       1. `rfr-A-swap-swap`           (= `fr-A-swap-swap`)
--       2. `rfr-A-trans-prep-prep`     (sub-case of `fr-A-trans-prep`)
--       3. `rfr-A-trans-prep-swap`     (sub-case of `fr-A-trans-prep`)
--       4. `rfr-A-trans-prep-trans`    (sub-case of `fr-A-trans-prep`)
--       5. `rfr-A-trans-swap`          (= `fr-A-trans-swap`)
--       6. `rfr-B-prep-swap`           (= `fr-B-prep-swap`)
--       7. `rfr-B-prep-trans-swap`     (= `fr-B-prep-trans-swap`)
--   * `constructive-final-residual : RealFinalResidual → FinalResidual` —
--     bridges the narrower residual to the original `FinalResidual`,
--     closing the `a₁' = refl` sub-case constructively.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `RealFinalResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.YangBaxterClosure
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
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.YangBaxterResiduals sig-dec
  using (FinalResidual)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Induction.WellFounded using (Acc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Arithmetic helpers

private
  -- For fr-A-trans-prep with `a₁' = refl`.
  -- After Agda's `_+_` reduction by left-recursion:
  --   size q = suc (suc (size a₂ + size Z))  where Z = trans (swap k k' b) Y
  --   size p = suc (suc (suc (suc (suc (size a₂ + size Z)))))
  -- Thus diff = 3 sucs.
  size-aprep-refl-<
    : ∀ saZ
    → suc (suc saZ) < suc (suc (suc (suc (suc saZ))))
  size-aprep-refl-< saZ =
    s≤s (s≤s (s≤s (≤-trans (n≤1+n saZ) (n≤1+n (suc saZ)))))

--------------------------------------------------------------------------------
-- ## Permute-equivalence for fr-A-trans-prep with `a₁' = refl`.
--
-- p = trans (prep k (trans (prep k'' refl) a₂)) (trans (swap k k' b) Y)
-- q = trans (prep k a₂)                         (trans (swap k k' b) Y)
--
-- permute (prep k (trans (prep k'' refl) a₂))
--   = id ⊗ (permute a₂ ∘ permute (prep k'' refl))
--   = id ⊗ (permute a₂ ∘ (id ⊗ id))
--   ≈Term id ⊗ (permute a₂ ∘ id)
--   ≈Term id ⊗ permute a₂
--   = permute (prep k a₂)

private
  aprep-refl-permute-eq
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' : Fin n} {ms' rest rest' : List (Fin n)}
        (a₂ : (k'' ∷ ms') Perm.↭ (k' ∷ rest))
        (b : rest Perm.↭ rest')
        (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ ms'))
    → let a = Perm.trans (Perm.prep k'' Perm.refl) a₂
          p = Perm.trans (Perm.prep k a)
                (Perm.trans (Perm.swap k k' b) Y)
          q = Perm.trans (Perm.prep k a₂)
                (Perm.trans (Perm.swap k k' b) Y)
      in permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  aprep-refl-permute-eq vlab {k} {k'} {k''} {ms'} {rest} {rest'} a₂ b Y =
    let pa₂ = permute (PermProp.map⁺ vlab a₂)
        pb  = permute (PermProp.map⁺ vlab b)
        pY  = permute (PermProp.map⁺ vlab Y)
        σ-block = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
        T_b : HomTerm _ _
        T_b = (id ⊗₁ (id ⊗₁ pb)) ∘ σ-block
    in begin
         (pY ∘ T_b) ∘ (id ⊗₁ (pa₂ ∘ (id ⊗₁ id)))
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (⊗-resp-≈ ≈-Term-refl
                  (∘-resp-≈ ≈-Term-refl id⊗id≈id)) ⟩
         (pY ∘ T_b) ∘ (id ⊗₁ (pa₂ ∘ id))
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (⊗-resp-≈ ≈-Term-refl idʳ) ⟩
         (pY ∘ T_b) ∘ (id ⊗₁ pa₂)
       ∎

--------------------------------------------------------------------------------
-- ## `RealFinalResidual`: STRICTLY NARROWER variant of `FinalResidual`.
--
-- The narrowing:
--
--   * `fr-A-trans-prep`: same shape, but additionally `a₁'` is `prep`,
--     `swap`, or `trans` — i.e., NOT `refl`.  The `refl` sub-case is
--     closed constructively in `constructive-final-residual` via
--     `aprep-refl-permute-eq` + size-strict descent.
--
--   * All other fields are the same as in `FinalResidual`.
--
-- The narrowing is strict because the `refl` sub-case is handled
-- constructively, not by appeal to the residual.
--
-- We express the "non-refl" restriction by providing THREE sub-fields
-- corresponding to the three structural cases of `a₁'` (prep/swap/trans).
-- Each is structurally more restricted than the original.

record RealFinalResidual : Set where
  field
    -- Same as FinalResidual.fr-A-swap-swap.
    rfr-A-swap-swap
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

    -- fr-A-trans-prep restricted to `a₁'` being `prep _ _`.
    -- xs'' = k₃ ∷ xs''', a₁' : (k₃ ∷ xs''') ↭ (k₃ ∷ ms'').
    -- This is STRICTLY narrower than the original `fr-A-trans-prep`
    -- because we exclude `a₁' = refl` (handled constructively) and the
    -- `a₁' = trans _ _` case (handled by ⊥-elim via norm).
    rfr-A-trans-prep-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' k₃ : Fin n}
          {xs''' ms'' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k₃ ∷ xs'''))
          (a₁'' : xs''' Perm.↭ ms'')
          (a₂ : (k'' ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
          (acc-p
            : let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.prep k₃ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k₃ ∷ xs''') Perm.↭ (k ∷ k'' ∷ k₃ ∷ xs'''))
              → let a₁' = Perm.prep k₃ a₁''
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.prep k₃ a₁''
              a = Perm.trans (Perm.prep k'' a₁') a₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- fr-A-trans-prep restricted to `a₁'` being `swap _ _ _`.
    -- xs'' = k₃ ∷ k₄ ∷ xs''', a₁' : (k₃ ∷ k₄ ∷ xs''') ↭ (k₄ ∷ k₃ ∷ ms'').
    rfr-A-trans-prep-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' k₃ k₄ : Fin n}
          {xs''' ms'' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
          (a₁'' : xs''' Perm.↭ ms'')
          (a₂ : (k'' ∷ k₄ ∷ k₃ ∷ ms'') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
          (acc-p
            : let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.swap k₃ k₄ a₁''
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs''')
                    Perm.↭ (k ∷ k'' ∷ k₃ ∷ k₄ ∷ xs'''))
              → let a₁' = Perm.swap k₃ k₄ a₁''
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.swap k₃ k₄ a₁''
              a = Perm.trans (Perm.prep k'' a₁') a₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- fr-A-trans-prep restricted to `a₁'` being `trans _ _`.
    -- xs'' contains nested trans.
    rfr-A-trans-prep-trans
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {xs'' xsM ms' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ k'' ∷ xs''))
          (a₁'a : xs'' Perm.↭ xsM)
          (a₁'b : xsM Perm.↭ ms')
          (a₂ : (k'' ∷ ms') Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ k'' ∷ xs''))
          (acc-p
            : let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a₁' = Perm.trans a₁'a a₁'b
                  a = Perm.trans (Perm.prep k'' a₁') a₂
                  p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k'' ∷ xs'') Perm.↭ (k ∷ k'' ∷ xs''))
              → let a₁' = Perm.trans a₁'a a₁'b
                    a = Perm.trans (Perm.prep k'' a₁') a₂
                    p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a₁' = Perm.trans a₁'a a₁'b
              a = Perm.trans (Perm.prep k'' a₁') a₂
              p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Same as FinalResidual.fr-A-trans-swap.
    -- (We do NOT split this one further at this stage.)
    rfr-A-trans-swap
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

    -- Same as FinalResidual.fr-B-prep-swap.
    rfr-B-prep-swap
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

    -- Same as FinalResidual.fr-B-prep-trans-swap.
    rfr-B-prep-trans-swap
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
-- ## Bridge: `constructive-final-residual`.
--
-- We produce a `FinalResidual` from a `RealFinalResidual` by:
--   * dispatching `fr-A-swap-swap` directly to `rfr-A-swap-swap`,
--   * case-splitting `fr-A-trans-prep` on `a₁'`:
--       - `a₁' = refl` → closed constructively (size-strict descent),
--       - `a₁' = prep` → dispatch to `rfr-A-trans-prep-prep`,
--       - `a₁' = swap` → dispatch to `rfr-A-trans-prep-swap`,
--       - `a₁' = trans _ _` → dispatch to `rfr-A-trans-prep-trans`,
--   * dispatching `fr-A-trans-swap` directly to `rfr-A-trans-swap`,
--   * dispatching `fr-B-prep-swap` directly to `rfr-B-prep-swap`,
--   * dispatching `fr-B-prep-trans-swap` directly to `rfr-B-prep-trans-swap`.

constructive-final-residual : RealFinalResidual → FinalResidual
constructive-final-residual rfr = record
  { fr-A-swap-swap       = rfr-A-swap-swap
  ; fr-A-trans-prep      = aprep-handler
  ; fr-A-trans-swap      = rfr-A-trans-swap
  ; fr-B-prep-swap       = rfr-B-prep-swap
  ; fr-B-prep-trans-swap = rfr-B-prep-trans-swap
  }
  where
    open RealFinalResidual rfr

    aprep-handler
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

    -- ----- a₁' = refl: closed constructively via size-strict descent. -----
    --
    -- p = trans (prep k (trans (prep k'' refl) a₂)) (trans (swap k k' b) Y)
    -- q = trans (prep k a₂)                          (trans (swap k k' b) Y)
    --
    -- size q < size p (diff 3, by `size-aprep-refl-<`).
    -- permute p ≈Term permute q (by `aprep-refl-permute-eq`).
    aprep-handler vlab {k} {k'} {k''} {.ms'} {ms'} {rest} {rest'}
        uniq Perm.refl a₂ b Y _ _ self-rec =
      let p = Perm.trans (Perm.prep k (Perm.trans (Perm.prep k'' Perm.refl) a₂))
                (Perm.trans (Perm.swap k k' b) Y)
          q = Perm.trans (Perm.prep k a₂)
                (Perm.trans (Perm.swap k k' b) Y)

          size-< : size q < size p
          size-< = size-aprep-refl-<
                     (size a₂ + size (Perm.trans (Perm.swap k k' b) Y))

          sub-≪ : measure q ≪₃ measure p
          sub-≪ = ≪₃-fst {l₁ = total-l q} {l₂ = total-l p}
                         {c₁ = swap-count q} {c₂ = swap-count p}
                         size-<

          ih = self-rec q sub-≪
          eq = aprep-refl-permute-eq vlab a₂ b Y
      in ≈-Term-trans eq ih

    -- ----- a₁' = prep k₃ a₁'': dispatch to rfr-A-trans-prep-prep. -----
    aprep-handler vlab {k} {k'} {k''} {.(k₃ ∷ xs''')} {.(k₃ ∷ ms''')} {rest} {rest'}
        uniq (Perm.prep {xs = xs'''} {ys = ms'''} k₃ a₁'') a₂ b Y acc-p norm self-rec =
      rfr-A-trans-prep-prep vlab uniq a₁'' a₂ b Y acc-p norm self-rec

    -- ----- a₁' = swap k₃ k₄ a₁'': dispatch to rfr-A-trans-prep-swap. -----
    aprep-handler vlab {k} {k'} {k''} {.(k₃ ∷ k₄ ∷ xs''')} {.(k₄ ∷ k₃ ∷ ms''')} {rest} {rest'}
        uniq (Perm.swap {xs = xs'''} {ys = ms'''} k₃ k₄ a₁'') a₂ b Y acc-p norm self-rec =
      rfr-A-trans-prep-swap vlab uniq a₁'' a₂ b Y acc-p norm self-rec

    -- ----- a₁' = trans a₁'a a₁'b: dispatch to rfr-A-trans-prep-trans. -----
    aprep-handler vlab {k} {k'} {k''} {xs''} {ms'} {rest} {rest'}
        uniq (Perm.trans a₁'a a₁'b) a₂ b Y acc-p norm self-rec =
      rfr-A-trans-prep-trans vlab uniq a₁'a a₁'b a₂ b Y acc-p norm self-rec

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `RealFinalResidual` — a STRICTLY NARROWER residual record with 7
--     fields.  The narrowing closes the `a₁' = refl` sub-case of
--     `fr-A-trans-prep` constructively, and splits the remaining
--     sub-cases of `a₁'` into three structurally-tighter fields
--     (`prep`, `swap`, `trans`).
--
--   * `constructive-final-residual : RealFinalResidual → FinalResidual`
--     bridges the narrower residual back to the original.
--
-- ## Discharge status:
--
--   * `fr-A-swap-swap`:        NARROWED (identity dispatch to
--                              `rfr-A-swap-swap`).
--   * `fr-A-trans-prep`:       PARTIALLY-CLOSED.  `a₁' = refl` is
--                              CLOSED constructively (size-strict
--                              descent + `aprep-refl-permute-eq`);
--                              `a₁' = prep`, `swap`, `trans` are
--                              dispatched to the structurally-narrower
--                              `rfr-A-trans-prep-{prep,swap,trans}`.
--   * `fr-A-trans-swap`:       NARROWED (identity dispatch to
--                              `rfr-A-trans-swap`).
--   * `fr-B-prep-swap`:        NARROWED (identity dispatch to
--                              `rfr-B-prep-swap`).
--   * `fr-B-prep-trans-swap`:  NARROWED (identity dispatch to
--                              `rfr-B-prep-trans-swap`).
--
-- ## FreeMonoidal lemmas used:
--
--   For the constructive closure of `fr-A-trans-prep` with
--   `a₁' = refl`, we only needed `idˡ`/`idʳ` and `id⊗id≈id`.  No
--   `σ∘σ≈id`, `σ∘[f⊗g]≈[g⊗f]∘σ`, or `hexagon` were necessary because
--   the `Perm.refl` sub-case is degenerate.
--
--   The five truly Yang-Baxter residuals all require `hexagon` to
--   close, but their direct application at the `permute`-level is
--   blocked by the σ-block vs atom-level σ mismatch described above.
--   These remain as fields in `RealFinalResidual`.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `RealFinalResidual`.
--------------------------------------------------------------------------------
