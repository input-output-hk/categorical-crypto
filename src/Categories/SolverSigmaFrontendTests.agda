{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Tests for the SYMMETRIC solver front-end (`Categories.SolverSigmaFrontend`).
--
-- A two-colour atom alphabet (⋆, •) and a three-generator signature
-- (μ : ⋆⊗⋆→⋆, s : ⋆→⋆, t : •→•).  Machine-checked:
--
--   * `Braiding`   — σ∘σ≈id, as a one-liner and DEEP inside a ⊗/α context.
--   * `Naturality` — σ-naturality through box generators; the headline
--     `σ ∘ (s ⊗ t) ≈ (t ⊗ s) ∘ σ` needs TWO machine-fired slides (one per
--     image block), the single-sided variants isolate each slide.
--   * `Mixed`      — σ moves interleaved with coherence/functoriality.
--   * `Negative`   — `≡ nothing`-pinned boundaries: the HEXAGON (Lσ1) and a
--     straddling box (Lσ2) do not decide; distinct generators stay apart.
--   * `Target`     — C-level showcase through `FinSetupσ`: `solveMorσ!`
--     one-liners reading in a symmetric monoidal target's own vocabulary,
--     plus a `rewriteMorσAuto!` rewrite (`test-rwσ-cancel`).
--------------------------------------------------------------------------------

module Categories.SolverSigmaFrontendTests where

open import Level using (Level)

open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (_∷_; [])
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Categories.Category using (_[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.FreeMonoidal
open import Categories.SolverFrontendCore using (module FinSig)
open import Categories.SolverSigmaFrontend using (module FrontendS; module FinSetupσ)

------------------------------------------------------------------------
-- Wire colours and the generator signature (ObjTerm arities, Fin-indexed).
--
--   0 → μ : ⋆ ⊗ ⋆ → ⋆     (multi-wire input)
--   1 → s : ⋆ → ⋆          (endo on ⋆)
--   2 → t : • → •          (endo on •)

data Ty : Set where ⋆ • : Ty

_≟Ty_ : DecidableEquality Ty
⋆ ≟Ty ⋆ = yes refl
⋆ ≟Ty • = no λ ()
• ≟Ty ⋆ = no λ ()
• ≟Ty • = yes refl

open FreeMonoidalHelper Symm Ty using (ObjTerm; unit; _⊗₀_; Var)

arityT : Fin 3 → ObjTerm × ObjTerm
arityT zero             = Var ⋆ ⊗₀ Var ⋆ , Var ⋆
arityT (suc zero)       = Var ⋆ , Var ⋆
arityT (suc (suc zero)) = Var • , Var •

open FinSig Symm {Ty} arityT using (GenS; genS; _≟G_; rankS)

------------------------------------------------------------------------
-- The front-end term language and the solver instance.

private module S = FreeMonoidalHelper.Mor Symm Ty GenS

open FrontendS {Ty} _≟Ty_ GenS

open Decide _≟G_ rankS

-- readable term-language aliases.
private
  infix  4 _≈'_
  infixr 9 _∘'_
  infixr 10 _⊗'_
  _≈'_ : ∀ {A B} → S.HomTerm A B → S.HomTerm A B → Set
  _≈'_ = S._≈Term_
  _∘'_ : ∀ {A B C} → S.HomTerm B C → S.HomTerm A B → S.HomTerm A C
  _∘'_ = S._∘_
  _⊗'_ : ∀ {A B C D} → S.HomTerm A B → S.HomTerm C D
       → S.HomTerm (A ⊗₀ C) (B ⊗₀ D)
  _⊗'_ = S._⊗₁_
  id' : ∀ {A} → S.HomTerm A A
  id' = S.id
  σ' : ∀ {A B} → S.HomTerm (A ⊗₀ B) (B ⊗₀ A)
  σ' = S.σ
  μ' = S.var (genS zero)
  s' = S.var (genS (suc zero))
  t' = S.var (genS (suc (suc zero)))

------------------------------------------------------------------------
-- Braiding involution: σ∘σ≈id, as a one-liner and deep in context.

module Braiding where

  test-σσ : σ' ∘' σ' ≈' id' {Var ⋆ ⊗₀ Var •}
  test-σσ = solveTerm! (σ' ∘' σ') id'

  -- the inverse pair fires DEEP: inside a ⊗-context, with α-recasts around.
  test-σσ-deep
    : S.α⇒ ∘' ((σ' {Var ⋆} {Var •} ∘' σ') ⊗' id' {Var ⋆}) ≈' S.α⇒
  test-σσ-deep = solveTerm! (S.α⇒ ∘' ((σ' ∘' σ') ⊗' id')) S.α⇒

  -- multi-wire blocks: σ at (⋆⊗⋆ , •) cancels too.
  test-σσ-wide : σ' {Var •} {Var ⋆ ⊗₀ Var ⋆} ∘' σ' ≈' id'
  test-σσ-wide = solveTerm! (σ' ∘' σ') id'

------------------------------------------------------------------------
-- σ-naturality through box generators: the SLIDES fire.

module Naturality where

  -- the headline: TWO machine-fired slides (s through the a-image block,
  -- t through the b-image block).
  test-σ-nat : σ' ∘' (s' ⊗' t') ≈' (t' ⊗' s') ∘' σ'
  test-σ-nat = solveTerm! (σ' ∘' (s' ⊗' t')) ((t' ⊗' s') ∘' σ')

  -- the single-sided variants (one slide each).
  test-σ-nat-left : σ' ∘' (s' ⊗' id' {Var •}) ≈' (id' ⊗' s') ∘' σ'
  test-σ-nat-left = solveTerm! (σ' ∘' (s' ⊗' id')) ((id' ⊗' s') ∘' σ')

  test-σ-nat-right : σ' ∘' (id' {Var ⋆} ⊗' t') ≈' (t' ⊗' id') ∘' σ'
  test-σ-nat-right = solveTerm! (σ' ∘' (id' ⊗' t')) ((t' ⊗' id') ∘' σ')

  -- σ-conjugation: slides + σσ-cancellation combined.
  test-σ-conj : σ' ∘' (s' ⊗' t') ∘' σ' ≈' t' ⊗' s'
  test-σ-conj = solveTerm! (σ' ∘' (s' ⊗' t') ∘' σ') (t' ⊗' s')

  -- a MULTI-WIRE box slides as one block: μ : ⋆⊗⋆ → ⋆ through σ.
  test-σ-nat-μ
    : σ' {Var ⋆} {Var •} ∘' (μ' ⊗' id' {Var •})
      ≈' (id' {Var •} ⊗' μ') ∘' σ' {Var ⋆ ⊗₀ Var ⋆} {Var •}
  test-σ-nat-μ = solveTerm! (σ' ∘' (μ' ⊗' id')) ((id' ⊗' μ') ∘' σ')

------------------------------------------------------------------------
-- Mixed goals: σ interleaved with the Mon repertoire.

module Mixed where

  -- cancellation under functoriality: σσ-conjugated tensor of composites.
  test-mix-∘ : (σ' ∘' σ') ∘' ((s' ∘' s') ⊗' t') ≈' (s' ⊗' t') ∘' (s' ⊗' id')
  test-mix-∘ =
    solveTerm! ((σ' ∘' σ') ∘' ((s' ∘' s') ⊗' t')) ((s' ⊗' t') ∘' (s' ⊗' id'))

  -- σ against the unitors: the inverse σ-pair at (⋆, unit) cancels under
  -- a right unitor.
  test-mix-unit : S.ρ⇒ ∘' σ' {unit} {Var ⋆} ∘' σ' ≈' S.ρ⇒ {Var ⋆}
  test-mix-unit = solveTerm! (S.ρ⇒ ∘' σ' ∘' σ') S.ρ⇒

------------------------------------------------------------------------
-- NEGATIVE boundaries, pinned with ≡ nothing.

module Negative where

  -- Lσ1: the HEXAGON (a TRUE axiom) does not decide — the normalizer never
  -- splits or merges crossing BLOCKS, so the two routings are distinct normal
  -- forms.
  neg-hexagon
    : decide?F ((id' {Var •} ⊗' σ') ∘' S.α⇒ ∘' (σ' {Var ⋆} {Var •} ⊗' id' {Var ⋆}))
               (S.α⇒ ∘' σ' ∘' S.α⇒)
      ≡ nothing
  neg-hexagon = refl

  -- distinct generators stay apart (sanity: every just is a real proof).
  neg-distinct : decide?F (s' ∘' s') s' ≡ nothing
  neg-distinct = refl

  -- Lσ2: a box STRADDLING the two image blocks of a crossing does not slide.
  -- Over `σ' {⋆⊗⋆}{⋆}`, mapping wires [a₁,a₂,b]↦[b,a₁,a₂], the multi-input box
  -- `μ` (after `α⇐`) consumes [b,a₁] — one wire from each image block — so it
  -- straddles the crossing.  Both sides denote the SAME free-symmetric morphism
  -- (the equation is TRUE), but the solver returns `nothing`: sliding μ would
  -- split it across the two image blocks.  (This pin also exercises the Lσ1
  -- crossing-routing boundary; a straddle-only pin is not constructible here.)
  neg-straddle
    : decide?F ((μ' ⊗' id' {Var ⋆}) ∘' S.α⇐ ∘' σ' {Var ⋆ ⊗₀ Var ⋆} {Var ⋆})
               ((μ' ⊗' id' {Var ⋆}) ∘'
                  (σ' {Var ⋆} {Var ⋆} ⊗' id' {Var ⋆}) ∘' S.α⇐ ∘'
                  (id' {Var ⋆} ⊗' σ' {Var ⋆} {Var ⋆}) ∘' S.α⇒)
      ≡ nothing
  neg-straddle = refl

------------------------------------------------------------------------
-- C-level showcase through `FinSetupσ`: statements read in the target's
-- own vocabulary, σ landing on the target's braiding.

module Target {o ℓ e : Level}
              (C : MonoidalCategory o ℓ e)
              (Sym : Symmetric (C .MonoidalCategory.monoidal)) where

  private
    module MC = MonoidalCategory C
    module Sy = Symmetric Sym

  module At
    (A B : MC.Obj)
    (sᴹ : C .MonoidalCategory.U [ A , A ])
    (tᴹ : C .MonoidalCategory.U [ B , B ])
    -- a rule hypothesis for the shared rewriting layer
    -- (`rewriteMorσ!` / `rewriteMorσAuto!`).
    (invσ : C .MonoidalCategory.U [ sᴹ MC.∘ sᴹ ≈ MC.id ])
    where

    open FinSetupσ C Sym (A ∷ B ∷ [])
    open Sig {2} (λ { zero       → V zero , V zero
                    ; (suc zero) → V (suc zero) , V (suc zero) })
      renaming (module S to Sσ)
    open WithGen (λ { (genS zero)       → sᴹ
                    ; (genS (suc zero)) → tᴹ })

    private
      sᵗ = gen zero
      tᵗ = gen (suc zero)
      -- σ pinned at the atom pair (the object interpretation is not
      -- injective, so the implicits must be supplied term-side).
      σᵗ : Sσ.HomTerm (V zero ⊗ᵒ V (suc zero)) (V (suc zero) ⊗ᵒ V zero)
      σᵗ = Sσ.σ
      σᵗ' : Sσ.HomTerm (V (suc zero) ⊗ᵒ V zero) (V zero ⊗ᵒ V (suc zero))
      σᵗ' = Sσ.σ

    open MC using () renaming (_⊗₁_ to _⊗C_)

    -- the target's braiding at (A , B).
    σC : C .MonoidalCategory.U [ MC._⊗₀_ A B , MC._⊗₀_ B A ]
    σC = Sy.braiding.⇒.η (A , B)

    -- braiding involution, in C.
    test-σσ-C
      : C .MonoidalCategory.U
          [ Sy.braiding.⇒.η (B , A) MC.∘ σC ≈ MC.id ]
    test-σσ-C = solveMorσ! (Sσ._∘_ σᵗ' σᵗ) Sσ.id

    -- σ-naturality, in C: two machine-fired slides.
    test-σ-nat-C
      : C .MonoidalCategory.U
          [ σC MC.∘ (sᴹ ⊗C tᴹ) ≈ (tᴹ ⊗C sᴹ) MC.∘ σC ]
    test-σ-nat-C =
      solveMorσ! (Sσ._∘_ σᵗ (Sσ._⊗₁_ sᵗ tᵗ)) (Sσ._∘_ (Sσ._⊗₁_ tᵗ sᵗ) σᵗ)

    -- the shared rewriting layer in the σ front-end: the rule `sᴹ ∘ sᴹ ≈ id`
    -- fires (auto-positioned) in the right factor of a tensor, collapsing the
    -- composite to `id` in context.
    test-rwσ-cancel
      : C .MonoidalCategory.U
          [ tᴹ ⊗C (sᴹ MC.∘ sᴹ) ≈ tᴹ ⊗C MC.id ]
    test-rwσ-cancel =
      rewriteMorσAuto! (Sσ._⊗₁_ tᵗ (Sσ._∘_ sᵗ sᵗ)) (Sσ._⊗₁_ tᵗ Sσ.id)
                       (Sσ._∘_ sᵗ sᵗ) Sσ.id invσ
