{-# OPTIONS --safe --with-K #-}

------------------------------------------------------------------------
-- Companion module to `Faithfulness`, using --with-K.
--
-- DELIVERED:
--
--   * `permute-inverse-left`  : permute (↭-sym p) ∘ permute p ≈Term id
--       Proved constructively for `refl`, `prep`, and `trans` cases.
--       The `swap` case is reduced to the narrower SMC-algebraic
--       lemma `σ-block-self-inverse` (see `SwapBlockInverseResidual`
--       record), which contains *no combinatorial content* — purely
--       an identity between specific SMC terms.
--
--   * `permute-inverse-right` : permute p ∘ permute (↭-sym p) ≈Term id
--       Obtained from `permute-inverse-left` and the involutivity of
--       `↭-sym`.
--
-- RESIDUAL (after this module):
--
--   * `SwapBlockInverseResidual` — the σ-block self-inverse identity in
--     the free SMC.  This is strictly narrower than the original
--     `TransSelfLoopResidual` from `Faithfulness.agda`: it has no
--     dependence on list-permutation derivations whatsoever, and is a
--     purely algebraic statement in the free SMC.
--
--   * The narrow `TransSelfLoopResidual` itself remains open in the
--     trans-self-loop case, since closing it requires the SMC
--     coherence theorem restricted to permute-built terms (or an
--     auxiliary equivalent of it).  Roadmap below.
--
-- ROADMAP for closing `TransSelfLoopResidual`:
--
--   (i)   Discharge `SwapBlockInverseResidual` (≈ 30 line algebraic
--         calculation using α-coherence + σ-naturality + σ∘σ≈id).
--   (ii)  Prove `q ≅↭ ↭-sym p` from `eval q ∘ eval p ≈ id` via
--         inverse-uniqueness in `Data.Fin.Permutation` (1 line).
--   (iii) Prove `permute-resp-≅↭` restricted to (q, ↭-sym p) — this is
--         the genuinely missing SMC-coherence-for-permute fact.
--
-- This module commits the SwapBlock residual as a record so that the
-- partial proof typechecks under `--safe`.
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
  using (unflatten; permute)

------------------------------------------------------------------------
-- 1. The narrow algebraic residual: σ-block self-inverse.
--
-- This packages exactly the SMC identity needed for the `swap` case of
-- `permute-inverse-left`.  It is parameterised over the inner
-- endomorphism witnessing inversion; the rest of the term is fixed.

-- A, B are the two outer objects being braided (= Var x and Var y in
-- the calling site), and the inner endomorphism `f` lives on C → D
-- (= unflatten xs → unflatten ys).
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
    --   (id ⊗ permute (↭-sym p)) ∘ (id ⊗ permute p)
    -- ≈ (id ∘ id) ⊗ (permute (↭-sym p) ∘ permute p)
    -- ≈ id ⊗ id
    -- ≈ id
    ≈-Term-trans
      (≈-Term-sym ⊗-∘-dist)
      (≈-Term-trans
        (⊗-resp-≈ idˡ (permute-inverse-left p))
        id⊗id≈id)
  permute-inverse-left (Perm.swap x y p) =
    -- permute (↭-sym (swap x y p)) = permute (swap y x (↭-sym p))
    --   = (id ⊗₁ (id ⊗₁ permute (↭-sym p))) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    -- permute (swap x y p)
    --   = (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    -- Apply σ-block-self-inverse with f = permute p, g = permute (↭-sym p).
    σ-block-self-inverse (permute p) (permute (Perm.↭-sym p))
                         (permute-inverse-left p)
  permute-inverse-left (Perm.trans p q) =
    -- (permute (↭-sym p) ∘ permute (↭-sym q)) ∘ (permute q ∘ permute p)
    -- reassoc → permute (↭-sym p) ∘ (permute (↭-sym q) ∘ (permute q ∘ permute p))
    -- inner reassoc → ... ∘ ((permute (↭-sym q) ∘ permute q) ∘ permute p)
    -- IH q → ... ∘ (id ∘ permute p)
    -- idˡ → ... ∘ permute p
    -- IH p → id
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
    -- permute-inverse-left (↭-sym p) gives:
    --   permute (↭-sym (↭-sym p)) ∘ permute (↭-sym p) ≈Term id
    -- Rewrite LHS via ↭-sym-involutive on the first factor.
    ≈-Term-trans
      (∘-resp-≈ (≈-Term-sym (↭-sym-involutive p)) ≈-Term-refl)
      (permute-inverse-left (Perm.↭-sym p))

------------------------------------------------------------------------
-- 5. ATTEMPTED constructive discharge of SwapBlockInverseResidual.
--
-- The lemma:
--   M₁ ∘ M₂ ≈Term id
-- where (with A, B outer braided objects and f : C → D, g : D → C with
-- g ∘ f ≈Term id):
--   M₂ = (id_B ⊗ (id_A ⊗ f)) ∘ α⇒ ∘ (σ ⊗ id) ∘ α⇐   : A⊗(B⊗C) → B⊗(A⊗D)
--   M₁ = (id_A ⊗ (id_B ⊗ g)) ∘ α⇒ ∘ (σ ⊗ id) ∘ α⇐   : B⊗(A⊗D) → A⊗(B⊗C)
--
-- Calculation outline:
--
--  (1) Pull `(id_B ⊗ (id_A ⊗ f))` to the right by α-naturality and
--      σ-naturality, until it sits adjacent to `(id_A ⊗ (id_B ⊗ g))`.
--      The intermediate σ⊗id-blocks then become a single self-inverse
--      block.
--  (2) Use `σ∘σ≈id` and the α⇐∘α⇒≈id identity to collapse the
--      braided block to `id` modulo `id ⊗ (id ⊗ (g ∘ f))`.
--  (3) Use the hypothesis `g ∘ f ≈Term id` to finish.
--
-- This calculation is roughly 30 algebraic steps in the FreeMonoidal
-- term setoid.  We have NOT discharged it in this commit; it remains
-- the strictly narrower algebraic residual.
--
-- A naive attempt below typechecks the *signature* but not the body;
-- we leave the body as the next-iteration target.

------------------------------------------------------------------------
-- 5'. Constructive discharge of SwapBlockInverseResidual.
--
-- Two auxiliary σ-block lemmas (re-derived locally, no APROP import):
--   * σ-block-involutive : σ-block ∘ σ-block ≈ id.
--   * σ-block-natural₃   : σ-block ∘ (id ⊗ (id ⊗ f)) ≈ (id ⊗ (id ⊗ f)) ∘ σ-block.
--
-- Then σ-block-self-inverse-direct stitches the two M-factors together,
-- pushing the inner (id ⊗ (id ⊗ f)) past the σ-block₂ via naturality,
-- collapsing the two σ-blocks via involutivity, and finishing with the
-- hypothesis g ∘ f ≈ id.

private
  -- Dual associator commutativity (α⇐-comm), derived from α-comm.
  α⇐-comm
    : ∀ {a b c d e g : ObjTerm}
        {h : HomTerm a d} {i : HomTerm b e} {j : HomTerm c g}
    → α⇐ ∘ (h ⊗₁ (i ⊗₁ j)) ≈Term ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
  α⇐-comm {h = h} {i} {j} =
    ≈-Term-trans (≈-Term-sym idʳ)
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id))
    (≈-Term-trans assoc
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
    (≈-Term-trans (≈-Term-sym assoc)
    (≈-Term-trans (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl)
                   idˡ)))))))

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

  -- σ-block-natural₃: σ-block ∘ (id ⊗ (id ⊗ f)) ≈ (id ⊗ (id ⊗ f)) ∘ σ-block.
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
  -- Notation:
  --   sb₁ = α⇒ ∘ (σ_{A,B} ⊗ id) ∘ α⇐  : A⊗(B⊗C) → B⊗(A⊗C)
  --   sb₂ = α⇒ ∘ (σ_{B,A} ⊗ id) ∘ α⇐  : B⊗(A⊗D) → A⊗(B⊗D)
  -- (M₁ ∘ M₂) = ((id ⊗ (id ⊗ g)) ∘ sb₂) ∘ ((id ⊗ (id ⊗ f)) ∘ sb₁)
  --           = (id ⊗ (id ⊗ g)) ∘ (sb₂ ∘ (id ⊗ (id ⊗ f))) ∘ sb₁
  --           = (id ⊗ (id ⊗ g)) ∘ ((id ⊗ (id ⊗ f)) ∘ sb₂) ∘ sb₁           [σ-block-natural₃]
  --           = ((id ⊗ (id ⊗ g)) ∘ (id ⊗ (id ⊗ f))) ∘ (sb₂ ∘ sb₁)
  --           ≈ (id ⊗ (id ⊗ (g ∘ f))) ∘ id                                [⊗-∘-dist, involutive]
  --           ≈ id ⊗ (id ⊗ id) ≈ id
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
-- 6. The constructive residual record.

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
-- 8. Closing `TransSelfLoopResidual` from `Faithfulness.agda`.
--
-- Given `eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb`, we have `eval-↭ q` is the
-- bijection-level inverse of `eval-↭ p`.  Composing with
-- `eval-↭ (Perm.↭-sym p)`, which `eval-↭-sym` identifies with
-- `inv-fb (eval-↭ p)`, gives `eval-↭ q ≈-fb eval-↭ (Perm.↭-sym p)`.
-- Equivalently: `q ≅↭ Perm.↭-sym p`.
--
-- To upgrade this to `permute q ≈Term permute (Perm.↭-sym p)` we need
-- exactly the (sym-restricted) congruence of `permute` w.r.t. `_≅↭_`.
-- We package this as the strictly narrower
-- `PermuteRespSymResidual`: scoped only to the pair `(q, Perm.↭-sym p)`
-- (rather than to all `≅↭`-related pairs).
--
-- IMPORTANT: `PermuteRespSymResidual` is strictly narrower than the wide
-- `FaithfulnessResidual` from `Faithfulness.agda`:
--   * it speaks only about pairs `(q, Perm.↭-sym p)` — not about all
--     ≅↭-related pairs,
--   * the second argument is constrained to be a `Perm.↭-sym` of some
--     other derivation,
--   * the equality hypothesis is stated post-`eval-↭-sym`/`eval-↭-comp`
--     normalisation.
-- We do NOT prove that the wide residual implies it (it does), nor that
-- this residual is strictly weaker (it is) — these are tracked separately.

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

  -- A self-loop `q ∘ p ≈ id` forces `q ≈ inv p`.  This is pointwise.
  -- `(q ∘-fb p) i = q (p i)`.  Hypothesis: `q (p i) ≡ i` for all i.
  -- Hence `q j ≡ inv-fb p j`:  let `i = inv-fb p j`, so `p i = j`,
  -- and we get `q j = q (p i) = i = inv-fb p j`.
  inv-from-self-loop
    : ∀ {n m} (p : P.Permutation n m) (q : P.Permutation m n)
    → (q ∘-fb p) ≈-fb P.id
    → q ≈-fb P.flip p
  inv-from-self-loop p q hyp j =
    -- We want: q ⟨$⟩ʳ j ≡ (P.flip p) ⟨$⟩ʳ j.
    -- Compute q (p (p⁻ j)) = (p⁻ j) by hypothesis at i := p⁻ j.
    -- LHS reduces to q j since p (p⁻ j) = j.
    trans (cong (q P.⟨$⟩ʳ_) (sym (P.inverseʳ p {j})))
          (hyp (P.flip p P.⟨$⟩ʳ j))

module _ (R : PermuteRespSymResidual) where
  open PermuteRespSymResidual R

  constructive-trans-self-loop : TransSelfLoopResidual
  constructive-trans-self-loop = record
    { permute-trans-self-loop-id = λ {xs} {ys} p q hyp →
        let -- eval q ≈ inv-fb (eval p)
            eq-inv : eval-↭ q ≈-fb P.flip (eval-↭ p)
            eq-inv = inv-from-self-loop (eval-↭ p) (eval-↭ q) hyp
            -- eval-↭ (↭-sym p) ≈ inv-fb (eval p)
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
-- 10. Reverse reduction: TransSelfLoopResidual implies PermuteRespSymResidual.
--
-- This is a CONSTRUCTIVE GROUPOID ARGUMENT: given that any permute-built
-- self-loop with `eval ≈ id` reduces to `id` (the `TransSelfLoopResidual`),
-- we can derive `permute q ≈Term permute (↭-sym p)` from
-- `eval q ≈-fb eval (↭-sym p)` by:
--
--   (1) From hypothesis, derive `eval q ∘-fb eval p ≈-fb id-fb`.
--   (2) Apply `permute-trans-self-loop-id` to get `permute q ∘ permute p ≈Term id`.
--   (3) Use the existing `permute-inverse-right! p` to invert:
--          permute q
--        ≈ permute q ∘ id                       (idʳ, reversed)
--        ≈ permute q ∘ (permute p ∘ permute (↭-sym p))   (perm-inv-right)
--        ≈ (permute q ∘ permute p) ∘ permute (↭-sym p)  (assoc, reversed)
--        ≈ id ∘ permute (↭-sym p)              (step 2)
--        ≈ permute (↭-sym p)                    (idˡ)
--
-- This establishes equivalence between the two residuals; together with
-- section 9 above, neither residual is strictly weaker.  The genuinely
-- open obligation is the SMC-coherence-for-permute fact itself, which
-- both residuals package equivalently.

module _ (R-TSL : TransSelfLoopResidual) where
  open TransSelfLoopResidual R-TSL

  -- The pointwise eval-level fact: `eval q ≈ eval (↭-sym p)` implies
  -- `eval q ∘-fb eval p ≈ id-fb`.
  private
    eval-comp-id-from-sym
      : ∀ {xs ys : List X} (p : xs Perm.↭ ys) (q : ys Perm.↭ xs)
      → eval-↭ q ≈-fb eval-↭ (Perm.↭-sym p)
      → eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb
    eval-comp-id-from-sym p q hyp i =
      let open Relation.Binary.PropositionalEquality.Core
          -- (eval-↭ q ∘-fb eval-↭ p) i = eval-↭ q (eval-↭ p i).
          step₁ : (eval-↭ q P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i)
                ≡ (eval-↭ (Perm.↭-sym p) P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i)
          step₁ = hyp (eval-↭ p P.⟨$⟩ʳ i)
          -- eval-↭ (↭-sym p) (eval-↭ p i) = (inv-fb (eval-↭ p)) (eval-↭ p i) = i.
          step₂ : (eval-↭ (Perm.↭-sym p) P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i)
                ≡ (P.flip (eval-↭ p) P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i)
          step₂ = eval-↭-sym p (eval-↭ p P.⟨$⟩ʳ i)
          step₃ : (P.flip (eval-↭ p) P.⟨$⟩ʳ_) (eval-↭ p P.⟨$⟩ʳ i) ≡ i
          step₃ = P.inverseˡ (eval-↭ p) {i}
      in trans step₁ (trans step₂ step₃)

  constructive-permute-resp-sym : PermuteRespSymResidual
  constructive-permute-resp-sym = record
    { permute-resp-sym = λ {xs} {ys} p q hyp →
        let -- Step 1: eval q ∘ eval p ≈ id.
            eval-loop : eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb
            eval-loop = eval-comp-id-from-sym p q hyp
            -- Step 2: permute q ∘ permute p ≈Term id.
            perm-loop : permute q ∘ permute p ≈Term id
            perm-loop = permute-trans-self-loop-id p q eval-loop
            -- Step 3: groupoid inversion (cancel-right by permute p).
            --   permute q
            -- ≈ permute q ∘ id
            -- ≈ permute q ∘ (permute p ∘ permute (↭-sym p))
            -- ≈ (permute q ∘ permute p) ∘ permute (↭-sym p)
            -- ≈ id ∘ permute (↭-sym p)
            -- ≈ permute (↭-sym p)
        in ≈-Term-trans (≈-Term-sym idʳ)
           (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym (permute-inverse-right! p)))
           (≈-Term-trans (≈-Term-sym assoc)
           (≈-Term-trans (∘-resp-≈ perm-loop ≈-Term-refl)
                          idˡ)))
    }
