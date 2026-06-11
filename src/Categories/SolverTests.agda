{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Tests for the morphism-variable monoidal-diagram solver.
--
-- The module sets up a shared two-colour wire type `Ty` and a
-- Frobenius/bialgebra-flavoured generator signature `Gen`.  Tests are grouped
-- into three sub-modules, each focused on one aspect of the pipeline:
--
--   * `Sound`       — `reflect-sound` on representative WTerms.
--   * `Interchange` — disjoint-box interchange, via the kernel and normalizeD.
--   * `Decision`    — the `decide?` procedure (positive and negative).
--
-- (Transport of free-category equations into a target MonoidalCategory is
-- covered by `Categories.SolverFrontendTests`; the raw swap-engine litmus
-- lives in `Categories.SolverNormalizeTests`.)
--
-- Hole-free, postulate-free, --safe.
--------------------------------------------------------------------------------

module Categories.SolverTests where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)

open import Categories.DiagramRewriteUntyped
open import Categories.FreeMonoidal
open import Categories.SolverCompare
open import Categories.SolverNormalize
open import Categories.SolverReflect

------------------------------------------------------------------------
-- Wire colours, shared across all sub-modules.

data Ty : Set where ⋆ • : Ty

_≟Ty_ : DecidableEquality Ty
⋆ ≟Ty ⋆ = yes refl
⋆ ≟Ty • = no λ ()
• ≟Ty ⋆ = no λ ()
• ≟Ty • = yes refl

-- UIP on wire lists, via Hedberg (decidable equality), --without-K.
private
  uipLTy : ∀ {x y : List Ty} (e e' : x ≡ y) → e ≡ e'
  uipLTy = Decidable⇒UIP.≡-irrelevant (≡-dec _≟Ty_)

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

open Untyped Mon {Ty} Gen
open Reflect  Mon {Ty} _≟Ty_ Gen
open Normalize Mon {Ty} _≟Ty_ Gen
open FreeMonoidalHelper.Mor Mon Ty mor
open ≈R
open SortD

------------------------------------------------------------------------
-- Module Sound: reflect soundness.
--
-- For each WTerm `t`, `reflect-sound t` is a machine-checked witness
-- that `castW (out-reflect t) ∘ ⟦ reflect t ⟧ ≈Term embed t`.
-- The ⊗ʷ cases exercise boxes at non-trivial wire offsets.

module Sound where

  private
    tμ    = boxʷ μ
    tδμ   = boxʷ δ ∘ʷ boxʷ μ
    tμ⊗η  = boxʷ μ ⊗ʷ boxʷ η
    ts⊗id = boxʷ s ⊗ʷ idʷ {⋆ ∷ []}

  test-μ     : castW (out-reflect tμ)    ∘ ⟦ reflect tμ    ⟧ ≈Term embed tμ
  test-μ     = reflect-sound tμ

  test-δ∘μ   : castW (out-reflect tδμ)   ∘ ⟦ reflect tδμ   ⟧ ≈Term embed tδμ
  test-δ∘μ   = reflect-sound tδμ

  test-μ⊗η   : castW (out-reflect tμ⊗η)  ∘ ⟦ reflect tμ⊗η  ⟧ ≈Term embed tμ⊗η
  test-μ⊗η   = reflect-sound tμ⊗η

  test-s⊗id  : castW (out-reflect ts⊗id) ∘ ⟦ reflect ts⊗id ⟧ ≈Term embed ts⊗id
  test-s⊗id  = reflect-sound ts⊗id

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

  open SolverCompare Mon _≟Ty_ Gen using () renaming (Gen to GenΣ)

  -- Decidable equality on GenΣ via _≟F_ on the Fin 6 index.
  private
    _≟Gen_ : DecidableEquality GenΣ
    (_ , _ , gen i) ≟Gen (_ , _ , gen j) with i ≟F j
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl

  open SolverCompare.Decide Mon _≟Ty_ Gen _≟Gen_
    using (_≈NF_; _≟DiagU_; ≈NF⇒≡)

  decide? : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
  decide? f g with reflect f ≟DiagU reflect g
  ... | no  _  = nothing
  ... | yes eq = just (chain eq)
    where
      chain : reflect f ≈NF reflect g → embed f ≈Term embed g
      chain eq = begin
        embed f
          ≈⟨ reflect-sound f ⟨
        castW (out-reflect f) ∘ ⟦ reflect f ⟧
          ≈⟨ eq-≈Term (≈NF⇒≡ eq) (out-reflect f) (out-reflect g) ⟩
        castW (out-reflect g) ∘ ⟦ reflect g ⟧
          ≈⟨ reflect-sound g ⟩
        embed g ∎
        where
          eq-≈Term : ∀ {n p} {d d' : DiagU n}
                       (e : d ≡ d') (q₁ : out d ≡ p) (q₂ : out d' ≡ p)
                   → castW q₁ ∘ ⟦ d ⟧ ≈Term castW q₂ ∘ ⟦ d' ⟧
          eq-≈Term {d = d} refl q₁ q₂ =
            ≡⇒≈Term (cong (λ q → castW q ∘ ⟦ d ⟧) (uipLTy q₁ q₂))

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
