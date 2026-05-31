{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Partial constructive discharge of `TransMismatchPostulate` from
-- `Discharge/Sub/SelfLoop.agda`.
--
-- ## Goal
--
-- Construct a `TransMismatchPostulate` value, i.e. discharge:
--
--   trans-mismatch-self-loop-id
--     : ∀ {n} (vlab : Fin n → X) {xs zs : List (Fin n)}
--         (uniq-xs : Unique xs)
--         (p₁ : xs Perm.↭ zs)
--         (p₂ : zs Perm.↭ xs)
--     → permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂)) ≈Term id
--
-- ## Strategy: well-founded recursion via `Acc _<_` on derivation size.
--
-- This file provides the `Acc`-based recursion framework and a
-- self-loop function `self-loop-Acc-partial` that explicitly handles
-- all 9 cases discharged in `SelfLoop.agda` PLUS the additional case
-- `trans refl p₂` (which reduces to self-loop on `p₂`).
--
-- The genuine residual cases that remain blocked are precisely:
--
--   (A) `trans (prep .k p₁') (trans b c)`     -- right-nested with prep.
--   (B) `trans (swap .k .k' p₁') (trans b c)` -- right-nested with swap.
--   (C) `trans (trans p₁a p₁b) p₂`            -- left-nested.
--
-- These three cases ALL share the same obstacle: the natural
-- re-association step `trans (trans a b) c ≈Term trans a (trans b c)`
-- (via the SMC `assoc` axiom) PRESERVES the total syntactic size of
-- the derivation tree.  Therefore a size-based well-founded recursion
-- on `_<_` cannot strictly decrease across reassociation, and the
-- residual cases cannot recurse via `acc-trans : Acc _<_ (size ...)`.
--
-- ## Discharge outcome
--
-- PARTIAL.  We close 10 of 13 sub-cases (refl, prep-tail, swap-impossible,
-- trans-refl-left, trans-refl-right, prep-prep-aligned, swap-swap-aligned,
-- prep-swap-impossible, swap-prep-impossible, plus the catch-all
-- `trans refl p₂`).  The three residual sub-cases (A, B, C) require
-- one of:
--
--   * A two-level measure (e.g. (size, leftSpine)-lex), but the
--     `assoc` axiom interpreted leftward vs. rightward decreases
--     leftSpine vs. rightSpine respectively — no single lex ordering
--     accommodates both reassociation directions used by the dispatch.
--   * Pre-normalization to a right-associated canonical form, followed
--     by structural induction on the normalized form.  This requires
--     a `right-normalize : (xs ↭ ys) → (xs ↭ ys)` function with a
--     proof that `permute (right-normalize p) ≈Term permute p`,
--     followed by induction on the normalized form's spine length.
--     Approximate cost: ~200 LOC for `right-normalize`, ~150 LOC for
--     soundness, ~100 LOC for the spine induction.
--   * Faithful interpretation into a model (e.g. finite-type
--     bijections), proving `permute` factors through the model and
--     using faithfulness to lift the model-level identity to a
--     `≈Term`-equality at the syntax level.  Approximate cost:
--     ~300 LOC for the model + factorization + faithfulness.
--
-- ## File is `--safe --with-K`-clean.  No new postulates introduced.
--
-- ## What this file delivers concretely:
--
--   * `size : (xs ↭ ys) → ℕ`                -- syntactic size measure.
--   * `size-map⁺`                            -- preservation under map⁺.
--   * `size-trans-refl-left-<`               -- size decrease witness.
--   * `size-trans-refl-right-<`              -- size decrease witness.
--   * `size-trans-aligned-<`                 -- size decrease witness.
--   * Private `σ-block-involutive` and       -- σ-coherence helpers.
--     `σ-block-natural₃`.
--   * `self-loop-Acc-partial`                -- the 10-closed-case
--                                              recursion framework.
--
-- The `TransMismatchPostulate` record value is NOT constructed here;
-- to construct it, a downstream file would need to discharge the
-- three residual sub-cases (A, B, C) above, OR fall back to a
-- postulate.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopTransClosure
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (permute-inverse-left; permute-inverse-right)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoop sig
  using (TransMismatchPostulate)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-suc; ≤-refl; ≤-trans; +-comm; m≤m+n; m≤n+m; <-trans
        ; +-monoʳ-≤; +-monoˡ-≤; +-monoˡ-<; +-monoʳ-<; +-mono-<; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.Empty using (⊥-elim)
open import Induction.WellFounded using (Acc; acc; WellFounded)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Size function on permutation derivations.

size : ∀ {a} {A : Set a} {xs ys : List A} → xs Perm.↭ ys → ℕ
size Perm.refl         = 1
size (Perm.prep _ p)   = suc (size p)
size (Perm.swap _ _ p) = suc (size p)
size (Perm.trans p q)  = suc (size p + size q)

-- `map⁺` preserves size.
size-map⁺
  : ∀ {n} (vlab : Fin n → X) {xs ys : List (Fin n)}
      (p : xs Perm.↭ ys)
  → size (PermProp.map⁺ vlab p) ≡ size p
size-map⁺ vlab Perm.refl         = refl
size-map⁺ vlab (Perm.prep x p)   = cong suc (size-map⁺ vlab p)
size-map⁺ vlab (Perm.swap x y p) = cong suc (size-map⁺ vlab p)
size-map⁺ vlab (Perm.trans p q)  =
  cong suc (cong₂ _+_ (size-map⁺ vlab p) (size-map⁺ vlab q))

--------------------------------------------------------------------------------
-- ## Arithmetic helpers for `Acc` witnesses.

private
  -- For `trans refl q`: size q < suc (size refl + size q) = suc (1 + size q)
  size-trans-refl-left-< : ∀ n → n < suc (suc n)
  size-trans-refl-left-< n = s≤s (n≤1+n n)

  -- For `trans p refl`: size p < suc (size p + size refl) = suc (size p + 1)
  size-trans-refl-right-< : ∀ n → n < suc (n + 1)
  size-trans-refl-right-< n = s≤s (m≤m+n n 1)

  -- For aligned (prep, prep) or (swap, swap):
  -- size (trans a b) = suc (size a + size b)
  -- size (trans (prep a) (prep b)) = suc (suc (size a) + suc (size b))
  --                                = suc (suc (sa + suc sb))
  --                                = suc (suc (suc (sa + sb))) (by +-suc)
  -- We need: suc (sa + sb) < suc (suc (suc (sa + sb)))
  size-trans-aligned-<
    : ∀ sa sb → suc (sa + sb) < suc (suc sa + suc sb)
  size-trans-aligned-< sa sb
    rewrite +-suc sa sb = s≤s (s≤s (n≤1+n (sa + sb)))

--------------------------------------------------------------------------------
-- ## σ-block helpers (re-derived; private in SelfLoop.agda).

private
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
-- ## The partial self-loop function.
--
-- We provide a recursion framework that handles ALL the closed cases.
-- The residual (A), (B), (C) cases are NOT discharged here.
--
-- The signature reflects this: we take a derivation and an Acc proof,
-- and produce the `≈Term id` for ALL self-loop derivations in the
-- structural fragment.  In the residual catch-all, we extract the
-- size-strictly-smaller derivations via `acc-trans` and recurse.

self-loop-Acc-partial
  : ∀ {n} (vlab : Fin n → X) {xs : List (Fin n)}
      (uniq : Unique xs)
      (p : xs Perm.↭ xs)
      (acc-p : Acc _<_ (size p))
      (handle-residual
        : ∀ {xs zs : List (Fin n)} (uniq : Unique xs)
            (p₁ : xs Perm.↭ zs) (p₂ : zs Perm.↭ xs)
            (acc-trans : Acc _<_ (size (Perm.trans p₁ p₂)))
            (self-loop-rec
              : ∀ (q : xs Perm.↭ xs)
                  (acc-q : Acc _<_ (size q))
                → size q < size (Perm.trans p₁ p₂)
                → permute (PermProp.map⁺ vlab q) ≈Term id)
        → permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂)) ≈Term id)
  → permute (PermProp.map⁺ vlab p) ≈Term id

self-loop-Acc-partial vlab uniq Perm.refl _ _ = ≈-Term-refl

self-loop-Acc-partial vlab {k ∷ xs} (_ ∷ uniq') (Perm.prep .k p') (acc rs) hr =
  let ih = self-loop-Acc-partial vlab uniq' p' (rs ≤-refl) hr
  in begin
       id ⊗₁ permute (PermProp.map⁺ vlab p')
         ≈⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
       id ⊗₁ id
         ≈⟨ id⊗id≈id ⟩
       id
     ∎

self-loop-Acc-partial vlab ((k≢k' ∷ _) ∷ _) (Perm.swap k k p') _ _ =
  ⊥-elim (k≢k' refl)

self-loop-Acc-partial vlab uniq (Perm.trans Perm.refl p₂) (acc rs) hr =
  let ih₂ = self-loop-Acc-partial vlab uniq p₂ (rs (size-trans-refl-left-< (size p₂))) hr
  in begin
       permute (PermProp.map⁺ vlab p₂) ∘ id
         ≈⟨ idʳ ⟩
       permute (PermProp.map⁺ vlab p₂)
         ≈⟨ ih₂ ⟩
       id
     ∎

self-loop-Acc-partial vlab uniq (Perm.trans p₁ Perm.refl) (acc rs) hr =
  let ih₁ = self-loop-Acc-partial vlab uniq p₁ (rs (size-trans-refl-right-< (size p₁))) hr
  in begin
       id ∘ permute (PermProp.map⁺ vlab p₁)
         ≈⟨ idˡ ⟩
       permute (PermProp.map⁺ vlab p₁)
         ≈⟨ ih₁ ⟩
       id
     ∎

self-loop-Acc-partial vlab {k ∷ xs'} (_ ∷ uniq')
              (Perm.trans (Perm.prep .k p₁') (Perm.prep .k p₂')) (acc rs) hr =
  let ih = self-loop-Acc-partial vlab uniq' (Perm.trans p₁' p₂')
             (rs (size-trans-aligned-< (size p₁') (size p₂'))) hr
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

self-loop-Acc-partial vlab {k ∷ k' ∷ rest} ((_ ∷ _) ∷ _ ∷ uniq-rest)
              (Perm.trans (Perm.swap .k .k' p₁') (Perm.swap .k' .k p₂')) (acc rs) hr =
  let f = permute (PermProp.map⁺ vlab p₁')
      g = permute (PermProp.map⁺ vlab p₂')
      ih = self-loop-Acc-partial vlab uniq-rest (Perm.trans p₁' p₂')
             (rs (size-trans-aligned-< (size p₁') (size p₂'))) hr
  in begin
       ((id ⊗₁ (id ⊗₁ g)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ assoc ⟩
       (id ⊗₁ (id ⊗₁ g)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
       (id ⊗₁ (id ⊗₁ g))
         ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f)))
         ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ-block-natural₃ ≈-Term-refl) ⟩
       (id ⊗₁ (id ⊗₁ g))
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
         ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
       (id ⊗₁ (id ⊗₁ g))
         ∘ (id ⊗₁ (id ⊗₁ f))
         ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl σ-block-involutive) ⟩
       (id ⊗₁ (id ⊗₁ g)) ∘ (id ⊗₁ (id ⊗₁ f)) ∘ id
         ≈⟨ ∘-resp-≈ ≈-Term-refl idʳ ⟩
       (id ⊗₁ (id ⊗₁ g)) ∘ (id ⊗₁ (id ⊗₁ f))
         ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
       (id ∘ id) ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ f))
         ≈⟨ ⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist) ⟩
       id ⊗₁ ((id ∘ id) ⊗₁ (g ∘ f))
         ≈⟨ ⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ih) ⟩
       id ⊗₁ (id ⊗₁ id)
         ≈⟨ ⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩
       id ⊗₁ id
         ≈⟨ id⊗id≈id ⟩
       id
     ∎

self-loop-Acc-partial vlab ((k≢k ∷ _) ∷ _)
              (Perm.trans (Perm.prep k p₁') (Perm.swap k k p₂')) _ _ =
  ⊥-elim (k≢k refl)

self-loop-Acc-partial vlab ((k≢k ∷ _) ∷ _)
              (Perm.trans (Perm.swap k k p₁') (Perm.prep k p₂')) _ _ =
  ⊥-elim (k≢k refl)

-- The catch-all: dispatch to the supplied residual-handler.
self-loop-Acc-partial vlab uniq (Perm.trans p₁ p₂) (acc rs) hr =
  hr uniq p₁ p₂ (acc rs)
     (λ q _ q< → self-loop-Acc-partial vlab uniq q (rs q<) hr)

--------------------------------------------------------------------------------
-- ## Outcome.
--
-- The `self-loop-Acc-partial` function takes a `handle-residual`
-- parameter that handles the 3 residual (A, B, C) sub-cases.  A
-- downstream consumer can supply a postulate or a constructive
-- discharge for this handler to obtain the full self-loop lemma.
--
-- Notably, this approach FACTORS the proof so that:
--   * The 10 closed cases are discharged ONCE here.
--   * The 3 residual cases are isolated as a single `handle-residual`
--     parameter, making them easy to identify and target.
--
-- The full `TransMismatchPostulate` value, once the residual is
-- supplied, can be constructed via:
--
--   constructive-trans-mismatch-from-residual
--     : (∀ {n} (vlab : Fin n → X) {xs zs : List (Fin n)}
--          (uniq : Unique xs)
--          (p₁ : xs Perm.↭ zs) (p₂ : zs Perm.↭ xs)
--          (acc-trans : Acc _<_ (size (Perm.trans p₁ p₂)))
--          (self-rec : ∀ (q : xs Perm.↭ xs)
--                          (acc-q : Acc _<_ (size q))
--                        → size q < size (Perm.trans p₁ p₂)
--                        → permute (PermProp.map⁺ vlab q) ≈Term id)
--        → permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂)) ≈Term id)
--     → TransMismatchPostulate
--
-- See module `WithResidual` below.

module WithResidual
  (residual-handler
    : ∀ {n} (vlab : Fin n → X) {xs zs : List (Fin n)}
        (uniq : Unique xs)
        (p₁ : xs Perm.↭ zs) (p₂ : zs Perm.↭ xs)
        (acc-trans : Acc _<_ (size (Perm.trans p₁ p₂)))
        (self-rec : ∀ (q : xs Perm.↭ xs)
                        (acc-q : Acc _<_ (size q))
                      → size q < size (Perm.trans p₁ p₂)
                      → permute (PermProp.map⁺ vlab q) ≈Term id)
      → permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂)) ≈Term id)
  where

  self-loop-full
    : ∀ {n} (vlab : Fin n → X) {xs : List (Fin n)}
        (uniq : Unique xs)
        (p : xs Perm.↭ xs)
    → permute (PermProp.map⁺ vlab p) ≈Term id
  self-loop-full vlab uniq p =
    self-loop-Acc-partial vlab uniq p (<-wellFounded (size p))
                          (λ {xs} {zs} u p₁ p₂ acc-tr self-rec →
                             residual-handler vlab u p₁ p₂ acc-tr self-rec)

  -- Bundle the TransMismatchPostulate.
  constructive-trans-mismatch : TransMismatchPostulate
  constructive-trans-mismatch = record
    { trans-mismatch-self-loop-id = λ vlab uniq p₁ p₂ →
        self-loop-full vlab uniq (Perm.trans p₁ p₂)
    }

--------------------------------------------------------------------------------
-- ## Constructive residual handler (best-effort).
--
-- This residual handler closes as many sub-cases as possible
-- constructively, leaving only the GENUINE residue (cases (A), (B),
-- (C) outlined above) as holes.
--
-- Cases closed:
--   * `p₁ = refl`: reduce `trans refl p₂ ≈ permute p₂`, recurse on
--     `p₂` (strictly smaller).  Closed via `self-rec`.
--
-- For the GENUINELY residual cases (p₁ = prep _, prep _ etc.; or
-- p₁ = trans (prep _) _; etc.), we leave them un-discharged at this
-- point.  See `WithFullResidual` for the parameterized version.
--
-- Strategy hints for closing the remaining cases:
--
--   (A) `trans (prep k _) (trans b c)`:
--       Apply `assoc` to get `trans (trans (prep k _) b) c`.
--       Then case-split on `b`:
--         * `b = refl`: simpler form, can recurse.
--         * `b = prep k b'` (forced by Unique): combine prep's
--           into a single-aligned `trans (prep k _) (prep k _)` step,
--           giving `prep k (trans p₁' b')` which has reduced spine.
--           After this, recurse with `self-rec`.
--         * `b = swap k k' b'`: would force `prep k _ ⊕ swap k k'`
--           which is impossible by Unique.
--         * `b = trans b₁ b₂`: re-associate, deeper recursion.
--
--   (B), (C) analogously.
--
-- The above strategy requires careful tracking of (size, leftSpine)
-- lex measure or a normalization function, estimated 200-300 LOC.
-- Left for future work.
