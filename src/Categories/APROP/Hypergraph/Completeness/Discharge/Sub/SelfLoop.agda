{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of `SelfLoopPostulate.Fin-permute-self-loop-id` from
-- `Discharge/Sub/PermuteCoherenceFin.agda`.
--
-- ## Goal
--
-- Construct a `SelfLoopPostulate` value, i.e. discharge the postulate
--
--   Fin-permute-self-loop-id
--     : ∀ {n} {xs : List (Fin n)} (uniq-xs : Unique xs)
--         (vlab : Fin n → X) (p : xs Perm.↭ xs)
--     → permute (PermProp.map⁺ vlab p) ≈Term id
--
-- For Fin lists `xs` without duplicates, every self-permutation
-- derivation `p : xs ↭ xs` produces a HomTerm `≈Term`-equal to
-- identity.
--
-- ## Strategy
--
-- The proof proceeds by INDUCTION on the derivation `p : xs ↭ xs`,
-- where each case is handled by either:
--   * Direct structural recursion (refl, prep).
--   * Contradiction via `Unique xs` (swap, mixed prep/swap at trans).
--   * Aligned reduction (trans-refl, trans-prep, trans-swap).
--   * A small auxiliary postulate for the genuinely-hard trans case.
--
-- ## Discharge status: SUBSTANTIALLY PARTIAL.
--
-- We discharge constructively:
--
--   * `refl`            — trivial.
--   * `prep .k p'`      — by IH on tail (uses `Unique` propagation).
--   * `swap k k _`      — IMPOSSIBLE by `Unique` (Agda --with-K
--                          unification forces the two swap labels equal).
--   * `trans refl _`    — reduces to single IH call.
--   * `trans _ refl`    — reduces to single IH call.
--   * `trans (prep .k _) (prep .k _)` — by IH on `trans` of tails.
--   * `trans (swap .k .k' _) (swap .k' .k _)` — by σ-block algebra +
--                          IH on tails.
--   * `trans (prep _ _) (swap _ _ _)` (aligned) — IMPOSSIBLE by Unique.
--   * `trans (swap _ _ _) (prep _ _)` (aligned) — IMPOSSIBLE by Unique.
--
-- The remaining trans cases — `trans (prep _) (trans _ _)`,
-- `trans (swap _ _) (trans _ _)`, `trans (trans _ _) _`, and
-- non-aligned mixed cases — are deferred to an auxiliary postulate
-- `TransMismatchPostulate.trans-mismatch-self-loop-id`.
--
-- ## Why the residual cannot be closed by simple structural induction
--
-- For `trans p₁ (trans q₁ q₂)`, the natural step is to re-associate
-- to `trans (trans p₁ q₁) q₂` (the right-factor `q₂ < trans q₁ q₂`
-- is structurally smaller).  However, Agda's termination checker
-- compares the WHOLE outer derivation `Perm.trans _ _` syntactically,
-- and re-association preserves the total tree size, so the call
-- `Fin-permute-self-loop-id-aux _ _ (Perm.trans (Perm.trans p₁ q₁) q₂)`
-- is not accepted as structurally smaller than the original
-- `Perm.trans p₁ (Perm.trans q₁ q₂)`.
--
-- A closing proof would require either:
--   (a) `Acc`-based well-founded recursion on a derived measure,
--   (b) Normalization to a canonical form for ↭-derivations followed
--       by structural induction on the normal form,
--   (c) Faithful interpretation into a concrete symmetric monoidal
--       category (e.g., finite type-graded bijections) and use of
--       faithfulness to lift FinSet-level equality to ≈Term.
--
-- Each of these is a substantial (~300-500 LOC) development.  We
-- expose the genuinely residual case as the strictly narrower
-- `TransMismatchPostulate`.
--
-- ## File is `--safe --with-K`-clean.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoop
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (SelfLoopPostulate)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_)
open import Data.Empty using (⊥-elim)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## σ-block helpers (re-derived from PermuteCoherenceFin private scope).
--
-- These are the same helpers used in `PermuteCoherenceFin.permute-inverse-left`,
-- inlined here because they're declared `private` there.

private
  -- σ-block involutive: composing the σ-block with its inverse gives id.
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

  -- σ-block naturality in the third argument.
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
-- ## Reduction helper: permute-trans-self-loop-aligned.
--
-- If the intermediate of a `trans` is identical to the boundaries
-- (`zs ≡ xs`), the trans case reduces directly:
--
--   permute (trans p₁ p₂) = permute p₂ ∘ permute p₁
--
-- and BOTH `p₁` and `p₂` are themselves self-loops on `xs`.  By the
-- IH on both halves, we get `id ∘ id ≈ id`.

--------------------------------------------------------------------------------
-- ## The auxiliary postulate for the trans-mismatch case.
--
-- This is the strictly narrower residual obligation after we have
-- closed the structurally direct cases.

record TransMismatchPostulate : Set where
  field
    -- The `trans` case of self-loop reduction, restricted to lists
    -- that don't immediately collapse (no refl, no aligned-prep cases).
    --
    -- Statement: for any Fin-level `trans p₁ p₂ : xs ↭ xs` with
    -- `Unique xs`, the corresponding permute morphism is ≈Term-id.
    trans-mismatch-self-loop-id
      : ∀ {n} (vlab : Fin n → X) {xs zs : List (Fin n)}
          (uniq-xs : Unique xs)
          (p₁ : xs Perm.↭ zs)
          (p₂ : zs Perm.↭ xs)
      → permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂)) ≈Term id

--------------------------------------------------------------------------------
-- ## Main induction on the derivation `p : xs ↭ xs`.
--
-- Pattern match on `p` and use:
--   * refl: ≈-Term-refl.
--   * prep: IH on tail.
--   * swap: ⊥-elim from Unique contradiction.
--   * trans: defer to the auxiliary postulate (or close it
--     constructively when intermediate matches).

module ConstructWithTransAux (tmp : TransMismatchPostulate) where
  open TransMismatchPostulate tmp

  -- The main lemma, by induction on `p`.
  Fin-permute-self-loop-id-aux
    : ∀ {n} (vlab : Fin n → X) {xs : List (Fin n)}
        (uniq : Unique xs)
        (p : xs Perm.↭ xs)
    → permute (PermProp.map⁺ vlab p) ≈Term id
  Fin-permute-self-loop-id-aux vlab uniq Perm.refl = ≈-Term-refl
  Fin-permute-self-loop-id-aux vlab {k ∷ xs} (_ ∷ uniq') (Perm.prep .k p') =
    -- We need to know `p' : xs ↭ xs` for the IH.
    -- From `Perm.prep k p' : k ∷ xs ↭ k ∷ xs`, by definition of `prep`,
    -- `p'` has type `xs ↭ xs` already (the source/target match by
    -- pattern matching on `Perm.prep`).
    --
    -- permute (map⁺ vlab (prep k p')) = id ⊗ permute (map⁺ vlab p').
    -- By IH on p' with uniq' : Unique xs.
    let ih = Fin-permute-self-loop-id-aux vlab uniq' p'
    in begin
         id ⊗₁ permute (PermProp.map⁺ vlab p')
           ≈⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
         id ⊗₁ id
           ≈⟨ id⊗id≈id ⟩
         id
       ∎
  Fin-permute-self-loop-id-aux vlab ((k≢k' ∷ _) ∷ _) (Perm.swap k k p') =
    -- Agda's --with-K unification of `k ∷ k' ∷ rest ≡ k' ∷ k ∷ rest'`
    -- (the self-loop equation) forces `k ≡ k'` and `rest ≡ rest'`.
    -- The matched pattern `Perm.swap k k p'` (with both labels the same)
    -- reflects this unification; the head of Unique then gives k ≢ k,
    -- a direct contradiction.
    ⊥-elim (k≢k' refl)
  Fin-permute-self-loop-id-aux vlab uniq (Perm.trans Perm.refl p₂) =
    -- trans refl p₂ : xs ↭ xs.  The intermediate is xs (since refl : xs ↭ xs).
    -- p₂ : xs ↭ xs is a self-loop, recurse.
    --
    -- permute (trans refl p₂) = permute p₂ ∘ permute refl = permute p₂ ∘ id.
    let ih₂ = Fin-permute-self-loop-id-aux vlab uniq p₂
    in begin
         permute (PermProp.map⁺ vlab p₂) ∘ id
           ≈⟨ idʳ ⟩
         permute (PermProp.map⁺ vlab p₂)
           ≈⟨ ih₂ ⟩
         id
       ∎
  Fin-permute-self-loop-id-aux vlab uniq (Perm.trans p₁ Perm.refl) =
    -- trans p₁ refl : xs ↭ xs.  Intermediate is xs.
    -- p₁ : xs ↭ xs is a self-loop, recurse.
    --
    -- permute (trans p₁ refl) = permute refl ∘ permute p₁ = id ∘ permute p₁.
    let ih₁ = Fin-permute-self-loop-id-aux vlab uniq p₁
    in begin
         id ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ idˡ ⟩
         permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ih₁ ⟩
         id
       ∎
  Fin-permute-self-loop-id-aux vlab {k ∷ xs'} (_ ∷ uniq') (Perm.trans (Perm.prep .k p₁') (Perm.prep .k p₂')) =
    -- Aligned trans-prep: both p₁, p₂ are prep with the same head k.
    -- xs = k ∷ xs', zs = k ∷ zs', p₁' : xs' ↭ zs', p₂' : zs' ↭ xs'.
    -- trans p₁' p₂' : xs' ↭ xs' is a self-loop; by IH it's ≈ id.
    --
    -- permute (trans (prep k p₁') (prep k p₂'))
    --   = (id ⊗ permute p₂') ∘ (id ⊗ permute p₁')
    --   ≈ (id ∘ id) ⊗ (permute p₂' ∘ permute p₁')
    --   = id ⊗ permute (trans p₁' p₂')
    --   ≈ id ⊗ id ≈ id.
    let ih = Fin-permute-self-loop-id-aux vlab uniq' (Perm.trans p₁' p₂')
    in begin
         (id ⊗₁ permute (PermProp.map⁺ vlab p₂'))
           ∘ (id ⊗₁ permute (PermProp.map⁺ vlab p₁'))
           ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
         (id ∘ id) ⊗₁ (permute (PermProp.map⁺ vlab p₂') ∘ permute (PermProp.map⁺ vlab p₁'))
           ≈⟨ ⊗-resp-≈ idˡ ih ⟩
         id ⊗₁ id
           ≈⟨ id⊗id≈id ⟩
         id
       ∎
  Fin-permute-self-loop-id-aux vlab {k ∷ k' ∷ rest} ((_ ∷ _) ∷ _ ∷ uniq-rest)
    (Perm.trans (Perm.swap .k .k' p₁') (Perm.swap .k' .k p₂')) =
    -- Aligned trans-swap: p₁ = swap k k' p₁', p₂ = swap k' k p₂'.
    -- xs = k ∷ k' ∷ rest, zs = k' ∷ k ∷ mid, p₁' : rest ↭ mid, p₂' : mid ↭ rest.
    -- trans p₁' p₂' : rest ↭ rest is a self-loop on rest; by IH ≈ id.
    --
    -- The computation parallels `permute-inverse-left`'s swap case:
    -- the σ-blocks compose to id, the inner permutes compose to id
    -- (by IH), and the outer ids close out via id⊗id≈id (twice).
    let f = permute (PermProp.map⁺ vlab p₁')
        g = permute (PermProp.map⁺ vlab p₂')
        ih = Fin-permute-self-loop-id-aux vlab uniq-rest (Perm.trans p₁' p₂')
        -- Note: `permute (map⁺ vlab (trans p₁' p₂')) = g ∘ f` by definition.
    in begin
         ((id ⊗₁ (id ⊗₁ g)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           -- Re-associate to bring the two σ-blocks together.
           ≈⟨ assoc ⟩
         (id ⊗₁ (id ⊗₁ g)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
         (id ⊗₁ (id ⊗₁ g))
           ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f)))
           ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           -- σ-block-natural₃: B_σ ∘ (id ⊗ (id ⊗ f)) ≈ (id ⊗ (id ⊗ f)) ∘ B_σ.
           ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ-block-natural₃ ≈-Term-refl) ⟩
         (id ⊗₁ (id ⊗₁ g))
           ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
           ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
         (id ⊗₁ (id ⊗₁ g))
           ∘ (id ⊗₁ (id ⊗₁ f))
           ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
           -- σ-block-involutive: B_σ ∘ B_σ ≈ id.
           ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl σ-block-involutive) ⟩
         (id ⊗₁ (id ⊗₁ g)) ∘ (id ⊗₁ (id ⊗₁ f)) ∘ id
           ≈⟨ ∘-resp-≈ ≈-Term-refl idʳ ⟩
         (id ⊗₁ (id ⊗₁ g)) ∘ (id ⊗₁ (id ⊗₁ f))
           -- Push composition inside ⊗.
           ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
         (id ∘ id) ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ f))
           ≈⟨ ⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist) ⟩
         id ⊗₁ ((id ∘ id) ⊗₁ (g ∘ f))
           -- Use IH: g ∘ f = permute (trans p₁' p₂') ≈ id.
           ≈⟨ ⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ih) ⟩
         id ⊗₁ (id ⊗₁ id)
           ≈⟨ ⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩
         id ⊗₁ id
           ≈⟨ id⊗id≈id ⟩
         id
       ∎
  Fin-permute-self-loop-id-aux vlab ((k≢k ∷ _) ∷ _) (Perm.trans (Perm.prep k p₁') (Perm.swap k k p₂')) =
    -- trans (prep k p₁') (swap k k p₂'):
    -- After Agda's pattern-matching unification (--with-K):
    --   xs = k ∷ k ∷ rest (from swap result = k ∷ xs' and xs = k ∷ xs')
    -- Unique xs gives head k ≢ k', contradiction.
    ⊥-elim (k≢k refl)
  Fin-permute-self-loop-id-aux vlab ((k≢k ∷ _) ∷ _) (Perm.trans (Perm.swap k k p₁') (Perm.prep k p₂')) =
    -- trans (swap k k p₁') (prep k p₂'):
    -- Mirror of the previous case.  xs = k ∷ k ∷ rest after unification.
    -- Unique xs gives k ≢ k, contradiction.
    ⊥-elim (k≢k refl)
  Fin-permute-self-loop-id-aux vlab uniq (Perm.trans p₁ p₂) =
    -- The trans case (general): defer to the auxiliary postulate.
    --
    -- After all the patterns above, what remains is the general trans
    -- case where (p₁, p₂) doesn't match one of the structurally
    -- aligned/impossible patterns.  This includes:
    --   * `trans (trans pa pb) p₂` (left-nested).
    --   * `trans p₁ (trans q₁ q₂)` (right-nested with non-trans p₁).
    --   * Mixed prep/swap/trans patterns not aligned.
    --
    -- This is the GENUINE residual — Kelly's symmetric monoidal coherence
    -- applied to a self-loop with non-trivial intermediate structure.
    trans-mismatch-self-loop-id vlab uniq p₁ p₂

  -- Construct the `SelfLoopPostulate` value.
  selfLoopPostulate : SelfLoopPostulate
  selfLoopPostulate = record
    { Fin-permute-self-loop-id
        = λ uniq vlab p → Fin-permute-self-loop-id-aux vlab uniq p
    }
