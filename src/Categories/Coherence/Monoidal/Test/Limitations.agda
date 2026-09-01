{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Limitations catalogue for the monoidal coherence solver
--
-- This module is the single authoritative list of what the solver family does
-- not do.  Every limitation is named here once, with a status tag:
--
--   {machine-checked here}      — pinned below as a `decide?F … ≡ nothing`
--                                 (a true equation the solver soundly declines
--                                 to prove), checked by `refl`.
--   {meta-property, prose only} — the absence of a theorem; no single equation
--                                 witnesses it either way.
--   {type-error, commented out} — exhibited only by a snippet that fails to
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
--   * No canonicity for `norm ∘ reflect`   {meta-property, prose only}
--   * Monoidal targets only                {meta-property, prose only}
--   * Fin-indexed call-site wrapper only   {meta-property, prose only}
--   * Fuel exhaustion is silent            {meta-property, prose only}
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
-- `rewriteMor!` family).  `lim-generator-naturality` pins that a bare
-- naturality goal for an opaque box is not decided.
--
-- No canonicity for `norm ∘ reflect`.  There is no claim that interchange-equal
-- diagrams reach the same normal form — the open confluence question for the
-- normalizer.
--
-- Monoidal targets only, no braiding.  Braided and symmetric goals are outside
-- this solver's scope entirely: the term language's braiding `σ` is available
-- only under the `Symm` variant of `Categories.FreeMonoidal`, and this solver
-- instantiates that syntax at `Mon` throughout.
--
-- Fin-indexed call-site wrapper only.  `Frontend` and `Frontend.Decide` are
-- parametric in the generator family `GenF` (this file instantiates them at a
-- hand-built one), and so is the `FSolve`/`Into`/`WithGen` transport; it is
-- only the convenience wrappers `FinSig`/`FinSetup` — hence the
-- entry points re-exported from `Categories.Coherence.Monoidal` — that are
-- `Fin`-bound.  An abstract generator family has to be wired to `Frontend`
-- directly.  This is an API-shape constraint, not a crisp type error, so it is
-- prose only.
--
-- Fuel exhaustion is silent.  The normalizer is a fuel-bounded loop
-- (`Normalize.normFuelWith`) whose budget is `1 + k²` in the diagram depth `k`
-- (`Frontend.Decide.norm`).  On exhaustion it returns its *input* paired with
-- the reflexive witness — exactly what it returns when no step applies — so a
-- caller cannot distinguish "no rewrite was needed" from "the budget ran out",
-- and `decide?F` then reports a plain `nothing`.  The budget is a heuristic,
-- not a proven bound: it is only sufficient if every fired swap strictly
-- decreases the number of out-of-order pairs, which the rank tiebreak does not
-- guarantee for ambiguous pairs.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Test.Limitations where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Data.Fin

open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Coherence.Monoidal.Frontend.Core

------------------------------------------------------------------------
-- Machine-checked: the non-injective-rank and generator-naturality
-- limitations, pinned with `decide?F … ≡ nothing`.
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

  private module FS = FinSig {Ty} arityT
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
