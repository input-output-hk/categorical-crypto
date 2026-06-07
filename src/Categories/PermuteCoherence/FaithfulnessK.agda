{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Companion to `Faithfulness`.  Provides:
--
--   * `permute-inverse-left`  : permute (↭-sym p) ∘ permute p ≈Term id
--   * `permute-inverse-right` : permute p ∘ permute (↭-sym p) ≈Term id
--
-- The `swap` case of `permute-inverse-left` is reduced to the purely
-- algebraic `σ-block-self-inverse` (`SwapBlockInverseResidual` record;
-- no combinatorial content), which is then discharged constructively in
-- §5' below.  Sections 8-10 derive each direction of the equivalence
-- between `TransSelfLoopResidual` and `PermuteRespSymResidual`.
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.FaithfulnessK
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; permute; α⇐-comm)

------------------------------------------------------------------------
-- 1. The narrow algebraic residual: σ-block self-inverse — the SMC
-- identity needed for the `swap` case of `permute-inverse-left`.

record SwapBlockInverseResidual : Set where
  field
    σ-block-self-inverse
      : ∀ {A B C D}
          (f : HomTerm C D) (g : HomTerm D C)
      → g ∘ f ≈Term id
      → ((id {A = A} ⊗₁ (id {A = B} ⊗₁ g)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
        ∘
        ((id {A = B} ⊗₁ (id {A = A} ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
        ≈Term id

------------------------------------------------------------------------
-- 2. permute-inverse-left, parameterised by the SwapBlock residual.

module _ (R : SwapBlockInverseResidual) where
  open SwapBlockInverseResidual R

  permute-inverse-left
    : {xs ys : List X} (p : xs Perm.↭ ys)
    → permute (Perm.↭-sym p) ∘ permute p ≈Term id
  permute-inverse-left Perm.refl = idˡ
  permute-inverse-left (Perm.prep x p) =
    ≈-Term-trans
      (≈-Term-sym ⊗-∘-dist)
      (≈-Term-trans
        (⊗-resp-≈ idˡ (permute-inverse-left p))
        id⊗id≈id)
  permute-inverse-left (Perm.swap x y p) =
    σ-block-self-inverse (permute p) (permute (Perm.↭-sym p))
                         (permute-inverse-left p)
  permute-inverse-left (Perm.trans p q) =
    ≈-Term-trans
      assoc
      (≈-Term-trans
        (∘-resp-≈ ≈-Term-refl
          (≈-Term-trans
            (≈-Term-sym assoc)
            (∘-resp-≈ (permute-inverse-left q) ≈-Term-refl)))
        (≈-Term-trans
          (∘-resp-≈ ≈-Term-refl idˡ)
          (permute-inverse-left p)))

  ----------------------------------------------------------------------
  -- 3. ↭-sym is involutive structurally.

  ↭-sym-involutive
    : {xs ys : List X} (p : xs Perm.↭ ys)
    → permute (Perm.↭-sym (Perm.↭-sym p)) ≈Term permute p
  ↭-sym-involutive Perm.refl       = ≈-Term-refl
  ↭-sym-involutive (Perm.prep x p) = ⊗-resp-≈ ≈-Term-refl (↭-sym-involutive p)
  ↭-sym-involutive (Perm.swap x y p) =
    ∘-resp-≈
      (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl (↭-sym-involutive p)))
      ≈-Term-refl
  ↭-sym-involutive (Perm.trans p q) =
    ∘-resp-≈ (↭-sym-involutive q) (↭-sym-involutive p)

  ----------------------------------------------------------------------
  -- 4. permute-inverse-right.

  permute-inverse-right
    : {xs ys : List X} (p : xs Perm.↭ ys)
    → permute p ∘ permute (Perm.↭-sym p) ≈Term id
  permute-inverse-right p =
    -- `permute-inverse-left (↭-sym p)`, with the first factor rewritten
    -- by `↭-sym-involutive`.
    ≈-Term-trans
      (∘-resp-≈ (≈-Term-sym (↭-sym-involutive p)) ≈-Term-refl)
      (permute-inverse-left (Perm.↭-sym p))

------------------------------------------------------------------------
-- 5. Constructive discharge of SwapBlockInverseResidual.
--
-- Two auxiliary σ-block lemmas:
--   * σ-block-involutive : σ-block ∘ σ-block ≈ id.
--   * σ-block-natural₃   : σ-block ∘ (id ⊗ (id ⊗ f)) ≈ (id ⊗ (id ⊗ f)) ∘ σ-block.
--
-- `σ-block-self-inverse-direct` then pushes the inner `(id ⊗ (id ⊗ f))`
-- past `σ-block₂` (naturality), collapses the two σ-blocks (involutivity),
-- and finishes with `g ∘ f ≈ id`.

private
  σ-block-involutive
    : ∀ {A B C : ObjTerm}
    → (α⇒ {A = A} {B = B} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = B} {B = A} {C = C})
        ∘ (α⇒ {A = B} {B = A} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = A} {B = B} {C = C})
      ≈Term id
  σ-block-involutive =
    ≈-Term-trans assoc
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                    (∘-resp-≈ ≈-Term-refl
                      (≈-Term-trans (≈-Term-sym assoc)
                                    (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl))))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                    (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                                (≈-Term-trans (⊗-resp-≈ σ∘σ≈id idˡ)
                                              id⊗id≈id))
                              ≈-Term-refl))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ)
                   α⇒∘α⇐≈id))))))

  σ-block-natural₃
    : ∀ {A B C D : ObjTerm} {f : HomTerm C D}
    → (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
      ≈Term (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
  σ-block-natural₃ {A} {B} {C} {D} {f} =
    let lhs→common
          : (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
            ≈Term α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
        lhs→common =
          ≈-Term-trans assoc
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl α⇐-comm))
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
                         (∘-resp-≈ ≈-Term-refl
                           (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                                       (⊗-resp-≈
                                         (≈-Term-trans (∘-resp-≈ ≈-Term-refl id⊗id≈id) idʳ)
                                         idˡ))
                                     ≈-Term-refl)))))
        rhs→common
          : (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐)
            ≈Term α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
        rhs→common =
          ≈-Term-trans (≈-Term-sym assoc)
          (≈-Term-trans (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl)
          (≈-Term-trans assoc
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
                         (∘-resp-≈ ≈-Term-refl
                           (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                                       (⊗-resp-≈
                                         (≈-Term-trans (∘-resp-≈ id⊗id≈id ≈-Term-refl) idˡ)
                                         idʳ))
                                     ≈-Term-refl)))))
    in ≈-Term-trans lhs→common (≈-Term-sym rhs→common)

-- The constructive discharge.
σ-block-self-inverse-direct
  : ∀ {A B C D} (f : HomTerm C D) (g : HomTerm D C)
  → g ∘ f ≈Term id
  → ((id {A = A} ⊗₁ (id {A = B} ⊗₁ g)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
    ∘
    ((id {A = B} ⊗₁ (id {A = A} ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
    ≈Term id
σ-block-self-inverse-direct {A} {B} {C} {D} f g g∘f≈id =
  ≈-Term-trans assoc
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                  (∘-resp-≈ σ-block-natural₃ ≈-Term-refl))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
  (≈-Term-trans (≈-Term-sym assoc)
  (≈-Term-trans (∘-resp-≈
                  (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                    (⊗-resp-≈ idˡ
                      (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                        (⊗-resp-≈ idˡ g∘f≈id))))
                  σ-block-involutive)
  (≈-Term-trans idʳ
  (≈-Term-trans (⊗-resp-≈ ≈-Term-refl id⊗id≈id)
                 id⊗id≈id)))))))

------------------------------------------------------------------------
-- 6. The residual record.

constructive-swap-block-inverse : SwapBlockInverseResidual
constructive-swap-block-inverse = record
  { σ-block-self-inverse = σ-block-self-inverse-direct
  }

------------------------------------------------------------------------
-- 7. Unparameterised top-level wrappers.

permute-inverse-left!
  : ∀ {xs ys : List X} (p : xs Perm.↭ ys)
  → permute (Perm.↭-sym p) ∘ permute p ≈Term id
permute-inverse-left! = permute-inverse-left constructive-swap-block-inverse

permute-inverse-right!
  : ∀ {xs ys : List X} (p : xs Perm.↭ ys)
  → permute p ∘ permute (Perm.↭-sym p) ≈Term id
permute-inverse-right! = permute-inverse-right constructive-swap-block-inverse

------------------------------------------------------------------------
-- 8. The sym-restricted congruence residual `PermuteRespSymResidual`:
-- `permute` respects `_≅↭_` on pairs `(q, Perm.↭-sym p)`.  This is the
-- missing SMC-coherence-for-permute fact, scoped narrowly (rather than to
-- all `≅↭`-related pairs as in the wide `FaithfulnessResidual`).

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.Soundness using (eval-↭-sym)

record PermuteRespSymResidual : Set where
  field
    permute-resp-sym
      : ∀ {xs ys : List X} (p : xs Perm.↭ ys) (q : ys Perm.↭ xs)
      → eval-↭ q ≈-fb eval-↭ (Perm.↭-sym p)
      → permute q ≈Term permute (Perm.↭-sym p)

------------------------------------------------------------------------
-- 9. From the narrow algebraic + sym-congruence residuals we DISCHARGE
--    `TransSelfLoopResidual` constructively.

open import Categories.PermuteCoherence.Faithfulness d
  using (TransSelfLoopResidual)

-- Pointwise: from `eval q ∘ eval p ≈ id` derive `eval q ≈ inv-fb (eval p)`.
-- Specialised so as to match `eval-↭-sym` on the RHS without extra rewrites.
private
  open import Data.Fin.Base using (Fin)
  open import Relation.Binary.PropositionalEquality.Core
    using (_≡_; refl; sym; trans; cong)
  import Data.Fin.Permutation as P

  -- A self-loop `q ∘ p ≈ id` forces `q ≈ inv p` (pointwise).
  inv-from-self-loop
    : ∀ {n m} (p : P.Permutation n m) (q : P.Permutation m n)
    → (q ∘-fb p) ≈-fb P.id
    → q ≈-fb P.flip p
  inv-from-self-loop p q hyp j =
    trans (cong (q P.⟨$⟩ʳ_) (sym (P.inverseʳ p {j})))
          (hyp (P.flip p P.⟨$⟩ʳ j))

module _ (R : PermuteRespSymResidual) where
  open PermuteRespSymResidual R

  constructive-trans-self-loop : TransSelfLoopResidual
  constructive-trans-self-loop = record
    { permute-trans-self-loop-id = λ {xs} {ys} p q hyp →
        let eq-inv : eval-↭ q ≈-fb P.flip (eval-↭ p)
            eq-inv = inv-from-self-loop (eval-↭ p) (eval-↭ q) hyp
            eq-sym : eval-↭ q ≈-fb eval-↭ (Perm.↭-sym p)
            eq-sym i =
              let open Relation.Binary.PropositionalEquality.Core
              in trans (eq-inv i) (sym (eval-↭-sym p i))
            permq≈permsym : permute q ≈Term permute (Perm.↭-sym p)
            permq≈permsym = permute-resp-sym p q eq-sym
        in ≈-Term-trans
             (∘-resp-≈ permq≈permsym ≈-Term-refl)
             (permute-inverse-left! p)
    }

------------------------------------------------------------------------
-- 10. Reverse reduction: TransSelfLoopResidual implies
-- PermuteRespSymResidual (a groupoid inversion argument), so the two
-- residuals are equivalent.

module _ (R-TSL : TransSelfLoopResidual) where
  open TransSelfLoopResidual R-TSL

  -- `eval q ≈ eval (↭-sym p)` implies `eval q ∘-fb eval p ≈ id-fb`.
  private
    eval-comp-id-from-sym
      : ∀ {xs ys : List X} (p : xs Perm.↭ ys) (q : ys Perm.↭ xs)
      → eval-↭ q ≈-fb eval-↭ (Perm.↭-sym p)
      → eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb
    eval-comp-id-from-sym p q hyp i =
      let open Relation.Binary.PropositionalEquality.Core
          step₁ : (eval-↭ q P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i)
                ≡ (eval-↭ (Perm.↭-sym p) P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i)
          step₁ = hyp (eval-↭ p P.⟨$⟩ʳ i)
          step₂ : (eval-↭ (Perm.↭-sym p) P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i)
                ≡ (P.flip (eval-↭ p) P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i)
          step₂ = eval-↭-sym p (eval-↭ p P.⟨$⟩ʳ i)
          step₃ : (P.flip (eval-↭ p) P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i) ≡ i
          step₃ = P.inverseˡ (eval-↭ p) {i}
      in trans step₁ (trans step₂ step₃)

  constructive-permute-resp-sym : PermuteRespSymResidual
  constructive-permute-resp-sym = record
    { permute-resp-sym = λ {xs} {ys} p q hyp →
        let eval-loop : eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb
            eval-loop = eval-comp-id-from-sym p q hyp
            perm-loop : permute q ∘ permute p ≈Term id
            perm-loop = permute-trans-self-loop-id p q eval-loop
            -- groupoid inversion: cancel-right by `permute p`.
        in ≈-Term-trans (≈-Term-sym idʳ)
           (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym (permute-inverse-right! p)))
           (≈-Term-trans (≈-Term-sym assoc)
           (≈-Term-trans (∘-resp-≈ perm-loop ≈-Term-refl)
                          idˡ)))
    }
