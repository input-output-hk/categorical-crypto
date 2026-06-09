{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Tests for the morphism-variable monoidal-diagram solver.
--
-- The module sets up a shared two-colour wire type `Ty` and a
-- Frobenius/bialgebra-flavoured generator signature `Gen`.  Tests are grouped
-- into four sub-modules, each focused on one aspect of the pipeline:
--
--   * `Sound`       — `reflect-sound` on representative WTerms.
--   * `Interchange` — disjoint-box interchange, via the kernel and normalizeD.
--   * `Decision`    — the `decide?` procedure (positive and negative).
--   * `Transport`   — lifting free-category equations into a target MonoidalCategory.
--
-- Hole-free, postulate-free, --safe.
--------------------------------------------------------------------------------

module Categories.SolverTests where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped
open import Categories.SolverReflect
open import Categories.SolverNormalize
open import Categories.SolverCompare
open import Categories.SolveMorSpike

------------------------------------------------------------------------
-- Wire colours, shared across all sub-modules.

data Ty : Set where ⋆ • : Ty

_≟Ty_ : DecidableEquality Ty
⋆ ≟Ty ⋆ = yes refl
⋆ ≟Ty • = no λ ()
• ≟Ty ⋆ = no λ ()
• ≟Ty • = yes refl

------------------------------------------------------------------------
-- Generator signature: Frobenius/bialgebra kit on Ty.
--
-- We index generators by Fin 6 (as in the Symmetric.Test convention)
-- so that decidable equality comes for free from _≟F_.
--
--   0 → μ : ⋆⋆ → ⋆      (multiply)
--   1 → η : · → ⋆        (unit)
--   2 → δ : ⋆ → ⋆⋆      (comultiply)
--   3 → ε : ⋆ → ·        (counit)
--   4 → s : ⋆ → ⋆        (endo on ⋆)
--   5 → t : • → •        (endo on •)

arity : Fin 6 → List Ty × List Ty
arity zero                             = (⋆ ∷ ⋆ ∷ []) , (⋆ ∷ [])
arity (suc zero)                       = [] , (⋆ ∷ [])
arity (suc (suc zero))                 = (⋆ ∷ []) , (⋆ ∷ ⋆ ∷ [])
arity (suc (suc (suc zero)))           = (⋆ ∷ []) , []
arity (suc (suc (suc (suc zero))))     = (⋆ ∷ []) , (⋆ ∷ [])
arity (suc (suc (suc (suc (suc _))))) = (• ∷ []) , (• ∷ [])

data Gen : List Ty → List Ty → Set where
  gen : (i : Fin 6) → Gen (proj₁ (arity i)) (proj₂ (arity i))

-- Readable aliases matching the reference convention.
private
  μ = gen zero
  η = gen (suc zero)
  δ = gen (suc (suc zero))
  ε = gen (suc (suc (suc zero)))
  s = gen (suc (suc (suc (suc zero))))
  t = gen (suc (suc (suc (suc (suc zero)))))

------------------------------------------------------------------------
-- Solver machinery at this signature.

open Untyped {Ty} Gen
open Reflect  {Ty} Gen
open Normalize {Ty} Gen
open FreeMonoidalHelper Mon Ty using (ObjTerm; unit; _⊗₀_; Var)
open FreeMonoidalHelper.Mor Mon Ty mor
open ≈R
open SortD _≟Ty_

private bs : BoxSound
        bs = boxSound

------------------------------------------------------------------------
-- Module Sound: reflect soundness.
--
-- For each WTerm `t`, `reflect-sound bs t` is a machine-checked witness
-- that `coeCod' (out-reflect t) ⟦ reflect t ⟧ ≈Term embed t`.
-- The ⊗ʷ cases exercise boxes at non-trivial wire offsets.

module Sound where

  private
    tμ    = boxʷ μ
    tδμ   = boxʷ δ ∘ʷ boxʷ μ
    tμ⊗η  = boxʷ μ ⊗ʷ boxʷ η
    ts⊗id = boxʷ s ⊗ʷ idʷ {⋆ ∷ []}

  test-μ     : coeCod' (out-reflect tμ)    ⟦ reflect tμ    ⟧ ≈Term embed tμ
  test-μ     = reflect-sound bs tμ

  test-δ∘μ   : coeCod' (out-reflect tδμ)   ⟦ reflect tδμ   ⟧ ≈Term embed tδμ
  test-δ∘μ   = reflect-sound bs tδμ

  test-μ⊗η   : coeCod' (out-reflect tμ⊗η)  ⟦ reflect tμ⊗η  ⟧ ≈Term embed tμ⊗η
  test-μ⊗η   = reflect-sound bs tμ⊗η

  test-s⊗id  : coeCod' (out-reflect ts⊗id) ⟦ reflect ts⊗id ⟧ ≈Term embed ts⊗id
  test-s⊗id  = reflect-sound bs ts⊗id

------------------------------------------------------------------------
-- Module Interchange: disjoint-box interchange, two ways.
--
-- `s : ⋆ → ⋆` and `t : • → •` occupy disjoint wires in a ⋆ ∷ • ∷ []
-- context; their firing order is immaterial in the free monoidal category.
-- We verify this (a) via the categorical kernel `two-box-swap` and (b) via
-- the autonomous `normalizeD` bubble-sort engine, with refl-checked reorder.

module Interchange where

  -- (a) Two-box-swap kernel at pre = mid = r = [].
  private module IX = TwoBoxSwap [] [] [] s t

  test-swap : IX.f-first ≈Term IX.g-first
  test-swap = IX.two-box-swap

  -- (b) The normalizeD engine on the out-of-order input (t-first, then s).

  private
    ixFit : LeftFit (⋆ ∷ []) [] [] (• ∷ []) t s
    ixFit = leftFit [] [] [] refl refl refl refl

    ixTail : DiagU (⋆ ∷ • ∷ [])
    ixTail = []_ (⋆ ∷ • ∷ [])

  -- leftFit? fires on the out-of-order pair (t at offset ⋆∷[], s at []).
  test-leftFit? : leftFit? (⋆ ∷ []) [] [] (• ∷ []) t s
                ≡ just (leftFit [] [] [] refl refl refl refl)
  test-leftFit? = refl

  -- leftFit? rejects the already-in-order pair.
  test-leftFit?-no : leftFit? [] [] [] [] s t ≡ nothing
  test-leftFit?-no = refl

  -- normalizeD reorders t-first → s-first.
  test-reorders : fromDiagU-ls (normalizeD 4 ixFit ixTail)
                ≡ mk-pad [] (• ∷ []) s ∷ mk-pad (⋆ ∷ []) [] t ∷ []
  test-reorders = refl

  -- The cast in the soundness proof collapses to refl (pre = mid = r = []).
  test-cast-id : proj₁ (normalizeD-sound 4 ixFit ixTail) ≡ refl
  test-cast-id = refl

  -- The sound interchange: the two firing orders have equal interpretations.
  test-sound : id ∘ ⟦ dInput ixFit ixTail ⟧ ≈Term ⟦ normalizeD 4 ixFit ixTail ⟧
  test-sound = proj₂ (normalizeD-sound 4 ixFit ixTail)

------------------------------------------------------------------------
-- Module Decision: the reflect-then-compare decision procedure.
--
-- `decide? f g` reflects both terms to DiagU, decides propositional NF
-- equality, and on a hit chains the two reflect-sound witnesses into a
-- proof `embed f ≈Term embed g`.  This is the structural fragment of the
-- solver (no normalizeD yet); positive cases must differ only by identity
-- laws and sequential composition order.

module Decision where

  open SolverCompare _≟Ty_ Gen using () renaming (Gen to GenΣ)

  -- Decidable equality on GenΣ via _≟F_ on the Fin 6 index.
  private
    _≟Gen_ : DecidableEquality GenΣ
    (_ , _ , gen i) ≟Gen (_ , _ , gen j) with i ≟F j
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl

  open SolverCompare.Decide _≟Ty_ Gen _≟Gen_
    using (_≈NF_; _≟DiagU_; ≈NF⇒≡)

  decide? : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
  decide? f g with reflect f ≟DiagU reflect g
  ... | no  _  = nothing
  ... | yes eq = just (chain eq)
    where
      chain : reflect f ≈NF reflect g → embed f ≈Term embed g
      chain eq = begin
        embed f
          ≈⟨ reflect-sound bs f ⟨
        coeCod' (out-reflect f) ⟦ reflect f ⟧
          ≈⟨ eq-≈Term (≈NF⇒≡ eq) (out-reflect f) (out-reflect g) ⟩
        coeCod' (out-reflect g) ⟦ reflect g ⟧
          ≈⟨ reflect-sound bs g ⟩
        embed g ∎
        where
          eq-≈Term : ∀ {n p} {d d' : DiagU n}
                       (e : d ≡ d') (q₁ : out d ≡ p) (q₂ : out d' ≡ p)
                   → coeCod' q₁ ⟦ d ⟧ ≈Term coeCod' q₂ ⟦ d' ⟧
          eq-≈Term refl refl refl = ≈-Term-refl

  -- Positive: `id ∘ μ` and `μ` reflect to the same diagram.
  test-pos₁ : Is-just (decide? (idʷ ∘ʷ boxʷ μ) (boxʷ μ))
  test-pos₁ = just _

  -- Positive: `μ ∘ id` and `μ`.
  test-pos₂ : Is-just (decide? (boxʷ μ ∘ʷ idʷ) (boxʷ μ))
  test-pos₂ = just _

  -- Negative: `μ` vs `s ∘ μ` — diagrams differ by an extra layer.
  test-neg₁ : decide? (boxʷ μ) (boxʷ s ∘ʷ boxʷ μ) ≡ nothing
  test-neg₁ = refl

  -- Negative: `δ` vs `δ ∘ s`.
  test-neg₂ : decide? (boxʷ δ) (boxʷ δ ∘ʷ boxʷ s) ≡ nothing
  test-neg₂ = refl

------------------------------------------------------------------------
-- Module Transport: lifting free-category proofs to a target MonoidalCategory.
--
-- Parameterised by a monoidal category C, an object interpretation ⟦_⟧₀
-- for wire colours, and a morphism interpretation ⟦Gen⟧ for each generator,
-- so that `≈Term` equations transport via the free functor to C-level
-- equalities.  All tests are genuine equations between morphisms of C.

module Transport
  {o ℓ e} (C : MonoidalCategory o ℓ e)
  (⟦_⟧obj₀ : Ty → C .MonoidalCategory.U .Category.Obj)
  where

  open SolveMor {o} {ℓ} {e} {Ty} Gen C ⟦_⟧obj₀

  module WithMorphisms
    (⟦Gen⟧ : ∀ {a b} → Gen a b
           → C .MonoidalCategory.U [ ⟦ wires a ⟧obj , ⟦ wires b ⟧obj ])
    where

    open WithMor ⟦Gen⟧

    -- The disjoint interchange `s ‖ t` (s on ⋆, t on •) lifts to C.
    test-interchange : C .MonoidalCategory.U
                         [ ⟦ TwoBoxSwap.f-first [] [] [] s t ⟧₁
                         ≈ ⟦ TwoBoxSwap.g-first [] [] [] s t ⟧₁ ]
    test-interchange = interchange-target s t
