{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Limitations catalogue for the monoidal coherence solver
--
-- This module is the SINGLE authoritative list of what the solver family does
-- NOT do.  Every limitation is named here once, with a status tag:
--
--   {machine-checked here}      — pinned below as a `decide?F … ≡ nothing`
--                                 (a TRUE equation the solver soundly declines
--                                 to prove), checked by `refl`.
--   {meta-property, prose only} — the ABSENCE of a theorem; no single equation
--                                 witnesses it either way.
--   {type-error, commented out} — exhibited only by a snippet that FAILS to
--                                 typecheck; kept commented below so this file
--                                 still builds, with a note on the expected
--                                 error.
--
-- The catalogue
-- =============
--
--   * Soundness without completeness      {meta-property, prose only}
--   * Non-injective rank                   {machine-checked — `lim-equal-rank`}
--   * Generator naturality not decided     {machine-checked — `lim-generator-naturality`}
--   * Braided hexagon not decided          {machine-checked — `lim-hexagon`}
--   * Straddling box does not slide        {machine-checked — `lim-straddle`}
--   * No canonicity for `norm ∘ reflect`   {meta-property, prose only}
--   * `Structural` is monoidal only        {type-error, commented out below}
--   * Concrete signatures only             {meta-property, prose only}
--
-- Soundness without completeness.  The solver is sound — every `just` it
-- returns is a real proof — but not complete: it may return `nothing` on a
-- true equation.  The machine-checked entries below are concrete witnesses of
-- that incompleteness.
--
-- Non-injective rank.  Ambiguous (scalar-like) reorderings are separated by a
-- rank tiebreak.  Under a constant / non-injective rank the tiebreak never
-- fires, so the two scalar orderings `u ∘ v` and `v ∘ u` are not
-- distinguished (`lim-equal-rank`).
--
-- Generator naturality not decided.  Box generators are opaque; the solver
-- assumes no generator-specific law (naturality of a box, an internal identity,
-- …).  Such laws, when they hold, must be supplied as rewrite rules (the
-- `rewriteMor!` / `rewriteMorσ!` family).  `lim-generator-naturality` pins
-- that a bare naturality goal for an opaque box is not decided.
--
-- Braided hexagon not decided.  The symmetric normalizer never splits or
-- merges crossing BLOCKS, so the hexagon axiom's two routings are distinct
-- normal forms (`lim-hexagon`).
--
-- Straddling box does not slide.  A box consuming one wire from each image
-- block of a crossing straddles it and will not slide, even when the equation
-- is true (`lim-straddle`).
--
-- No canonicity for `norm ∘ reflect`.  There is no claim that interchange-equal
-- diagrams reach the same normal form — the open confluence question for the
-- normalizer.
--
-- `Structural` is monoidal only, no braiding.  The braiding term `σ` is guarded
-- by an instance witnessing that the free variant is symmetric (`Symm ≤
-- variant`), which the monoidal variant underlying `Structural` does not
-- provide, so a goal using `σ` under `Structural` does not typecheck; use
-- `Symmetric` for braided goals.  See the commented `StructuralHasNoBraiding`
-- module at the bottom of this file for the exhibit.
--
-- Concrete signatures only.  The front-end takes a concrete `Fin`-indexed
-- signature (`FinSig`); an abstract generator family cannot be fed through the
-- same entry point.  This is an API-shape constraint, not a crisp type error,
-- so it is prose only.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Test.Limitations where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Data.Fin
open import Data.Vec using (_∷_; [])

open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Coherence.Monoidal.Frontend.Core
open import Categories.Coherence.Monoidal.Frontend.Sigma
import Categories.Coherence.Monoidal.Api as Coh

-- `v≤v` is a non-`instance` constructor in `Categories.FreeMonoidal` (a global
-- instance would clash with the APROP cone's local `Symm ≤ v` instances); the
-- symmetric interpretation below builds free `σ` at the `Symm` variant, so
-- supply it locally.  (No type signature: it fixes the `_≤_` ambiguity with
-- `Data.Fin._≤_`.)
instance Symm≤Symm = v≤v {Symm}

------------------------------------------------------------------------
-- Machine-checked, monoidal front-end: the non-injective-rank and
-- generator-naturality limitations, pinned with `decide?F … ≡ nothing`.
--
-- We wire the internal front-end decision procedure by hand from a `FinSig`
-- signature: a two-colour atom alphabet and a Fin-indexed arity table.
--
--   0 → μ  : ⋆ ⊗ ⋆ → ⋆     (multi-wire input)
--   1 → η  : unit  → ⋆      (empty domain)
--   2 → s  : ⋆ → ⋆          (endo on ⋆)
--   3 → s' : ⋆ → ⋆          (second endo on ⋆)
--   4 → t  : • → •          (endo on •)
--   5 → u  : unit → unit    (scalar)
--   6 → v  : unit → unit    (second scalar, for the non-injective-rank exhibit)

module MonLimits where

  data Ty : Set where ⋆ • : Ty

  instance
    DecEq-Ty : DecEq Ty
    DecEq-Ty .DecEq._≟_ = λ where
      ⋆ ⋆ → yes refl
      ⋆ • → no λ ()
      • ⋆ → no λ ()
      • • → yes refl

  open FreeMonoidalHelper Mon Ty using () renaming (ObjTerm to ObjTermᴵ; unit to unitᴵ; _⊗₀_ to _⊗₀ᴵ_; Var to Varᴵ)

  arityT : Fin 7 → ObjTermᴵ × ObjTermᴵ
  arityT zero                            = Varᴵ ⋆ ⊗₀ᴵ Varᴵ ⋆ , Varᴵ ⋆
  arityT (suc zero)                      = unitᴵ , Varᴵ ⋆
  arityT (suc (suc zero))                = Varᴵ ⋆ , Varᴵ ⋆
  arityT (suc (suc (suc zero)))          = Varᴵ ⋆ , Varᴵ ⋆
  arityT (suc (suc (suc (suc zero))))    = Varᴵ • , Varᴵ •
  arityT (suc (suc (suc (suc (suc _))))) = unitᴵ , unitᴵ   -- 5 → u, 6 → v

  private module FS = FinSig Mon {Ty} arityT
  open FS
  open Frontend {Ty} GenS
  open Decide rankS

  private
    infixr 9 _∘ᴵ_
    _∘ᴵ_ : ∀ {A B C} → S.HomTerm B C → S.HomTerm A B → S.HomTerm A C
    _∘ᴵ_ = S._∘_
    infixr 10 _⊗ᴵ_
    _⊗ᴵ_ : ∀ {A B C D} → S.HomTerm A B → S.HomTerm C D → S.HomTerm (A ⊗₀ᴵ C) (B ⊗₀ᴵ D)
    _⊗ᴵ_ = S._⊗₁_
    idᴵ : ∀ {A} → S.HomTerm A A
    idᴵ = S.id
    μ'  = gen zero
    s'  = gen (suc (suc zero))
    u'  = gen (suc (suc (suc (suc (suc zero)))))
    v'  = gen (suc (suc (suc (suc (suc (suc zero))))))

  -- Generator naturality not decided: the solver treats `μ` as opaque, so it
  -- does not identify `s ∘ μ` with `μ ∘ (s ⊗ id)`.
  lim-generator-naturality : decide?F (s' ∘ᴵ μ') (μ' ∘ᴵ (s' ⊗ᴵ idᴵ)) ≡ nothing
  lim-generator-naturality = refl

  -- Non-injective rank: under a constant rank the ambiguous-pair tiebreak never
  -- fires, so the two scalar orderings `u ∘ v` / `v ∘ u` are not separated.
  private module D₀ = Decide (λ _ → 0)

  lim-equal-rank : D₀.decide?F (u' ∘ᴵ v') (v' ∘ᴵ u') ≡ nothing
  lim-equal-rank = refl

------------------------------------------------------------------------
-- Machine-checked, symmetric front-end: the braided-hexagon and
-- straddling-box limitations, pinned with `decide?F … ≡ nothing`.
--
--   0 → μ : ⋆ ⊗ ⋆ → ⋆     (multi-wire input)
--   1 → s : ⋆ → ⋆          (endo on ⋆)
--   2 → t : • → •          (endo on •)

module SigmaLimits where

  data Ty : Set where ⋆ • : Ty

  instance
    DecEq-Ty : DecEq Ty
    DecEq-Ty .DecEq._≟_ = λ where
      ⋆ ⋆ → yes refl
      ⋆ • → no λ ()
      • ⋆ → no λ ()
      • • → yes refl

  open FreeMonoidalHelper Symm Ty using () renaming (ObjTerm to ObjTermᴵ; unit to unitᴵ; _⊗₀_ to _⊗₀ᴵ_; Var to Varᴵ)

  arityT : Fin 3 → ObjTermᴵ × ObjTermᴵ
  arityT zero             = Varᴵ ⋆ ⊗₀ᴵ Varᴵ ⋆ , Varᴵ ⋆
  arityT (suc zero)       = Varᴵ ⋆ , Varᴵ ⋆
  arityT (suc (suc zero)) = Varᴵ • , Varᴵ •

  private module FS = FinSig Symm {Ty} arityT
  open FS renaming (gen to genᵗ)
  open FrontendS {Ty} GenS
  open Decide rankS

  private
    infixr 9 _∘ᴵ_
    _∘ᴵ_ : ∀ {A B C} → S.HomTerm B C → S.HomTerm A B → S.HomTerm A C
    _∘ᴵ_ = S._∘_
    infixr 10 _⊗ᴵ_
    _⊗ᴵ_ : ∀ {A B C D} → S.HomTerm A B → S.HomTerm C D → S.HomTerm (A ⊗₀ᴵ C) (B ⊗₀ᴵ D)
    _⊗ᴵ_ = S._⊗₁_
    idᴵ : ∀ {A} → S.HomTerm A A
    idᴵ = S.id
    σᴵ : ∀ {A B} → S.HomTerm (A ⊗₀ᴵ B) (B ⊗₀ᴵ A)
    σᴵ = S.σ
    μ' = genᵗ zero

  -- Braided hexagon not decided: the normalizer never splits or merges crossing
  -- BLOCKS, so the hexagon axiom's two routings are distinct normal forms.
  lim-hexagon
    : decide?F ((idᴵ ⊗ᴵ σᴵ) ∘ᴵ S.α⇒ ∘ᴵ (σᴵ {Varᴵ ⋆} {Varᴵ •} ⊗ᴵ idᴵ {Varᴵ ⋆}))
               (S.α⇒ ∘ᴵ σᴵ ∘ᴵ S.α⇒)
      ≡ nothing
  lim-hexagon = refl

  -- Straddling box does not slide.  Over `σ {⋆⊗⋆}{⋆}`, mapping wires
  -- [a₁,a₂,b]↦[b,a₁,a₂], the multi-input box `μ` (after `α⇐`) consumes [b,a₁] —
  -- one wire from each image block — so it straddles the crossing.  Both sides
  -- denote the SAME free-symmetric morphism (the equation is TRUE), but the
  -- solver returns `nothing`: sliding μ would split it across the two image
  -- blocks.  (This pin also exercises the hexagon crossing-routing boundary; a
  -- straddle-only pin is not constructible here.)
  lim-straddle
    : decide?F ((μ' ⊗ᴵ idᴵ) ∘ᴵ S.α⇐ ∘ᴵ σᴵ)
               ((μ' ⊗ᴵ idᴵ) ∘ᴵ
                  (σᴵ ⊗ᴵ idᴵ) ∘ᴵ S.α⇐ ∘ᴵ
                  (idᴵ ⊗ᴵ σᴵ {Varᴵ ⋆}) ∘ᴵ S.α⇒)
      ≡ nothing
  lim-straddle = refl

------------------------------------------------------------------------
-- `Structural` is monoidal only, no braiding {type-error, commented out}.
--
-- The braiding term `σ` is guarded by an instance argument witnessing that the
-- free variant is (at least) symmetric (`Symm ≤ variant`); the monoidal variant
-- underlying `Structural` provides no such instance.  Uncommenting the module
-- below should therefore FAIL to typecheck with an `InstanceNoCandidate` error
-- ("No instance of type … Symm ≤ …"), demonstrating that braided goals cannot
-- be stated under `Structural` (use `Symmetric`).
--
-- module StructuralHasNoBraiding
--   {o ℓ e} (C : MonoidalCategory o ℓ e) (A B : C .MonoidalCategory.Obj) where
--   open Coh.Structural C (A ∷ B ∷ [])
--   -- `σ`'s `Symm ≤ variant` instance is unavailable for the monoidal variant.
--   _ = σ
