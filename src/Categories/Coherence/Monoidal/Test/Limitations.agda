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
--   * Non-termination on degenerate
--     signatures (reported, not fixed)     {machine-checked — `lim-cycle-*`}
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
-- Non-termination on degenerate signatures — reported, not fixed.  On a
-- signature with an empty-arity generator side the guarded step relation has
-- genuine cycles (a scalar orbiting a state/effect pair; period 4 at the
-- minimal instance below), so no fuel budget normalizes such inputs and the
-- equation is refused even when true.  The loop (`Normalize.normDetectWith`,
-- budget `1 + k²` in the diagram depth `k`) detects this: the step function is
-- deterministic, so a revisited state is a proof of divergence, and the loop
-- stops there with the verdict `cycled` (`exhausted` when the budget ran out
-- first, `converged` when the result is a genuine normal form).  The verdict
-- is exposed per side as `Frontend.Decide.statusF` / the call-site `statusMor`,
-- so a caller CAN distinguish "the normal forms differ" from "the normalizer
-- did not terminate" — `lim-cycle-status` pins the verdict on the minimal
-- cycling family and `lim-cycle-nothing` that the true equation is still
-- refused; `lim-converged` pins the honest verdict on a decided goal.
-- Completeness on such signatures is out of reach for this normalizer family
-- (an insertion-order-free counterexample exists); nondegenerate signatures
-- have no cycles.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Test.Limitations where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Data.Fin
open import Data.Maybe using (is-just)

open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Coherence.Monoidal.Frontend.Core
open import Categories.Coherence.Monoidal.Normalize using (NormStatus; converged; cycled; exhausted)

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

  open import Categories.Coherence.Monoidal.Test.Frontend using (Ty; ⋆; •; DecEq-Ty)

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

  -- The honest verdict on a decided goal: the compared form is a genuine
  -- normal form.
  lim-converged : statusF (s' ∘ᴵ μ') ≡ converged
  lim-converged = refl

------------------------------------------------------------------------
-- Machine-checked: non-termination on a degenerate signature, reported.
--
-- The minimal cycling family: e : ⋆ → unit, w : unit → unit, u : unit → ⋆.
-- `rankS` gives rank e = 0 < rank w = 1 < rank u = 2, and exactly this order
-- closes the scalar `w`'s orbit around the `u`/`e` pair into a period-4
-- cycle, so the true scalar equation below is refused — with the verdict
-- saying why.

module CycleLimits where

  data Ty : Set where ⋆ : Ty

  instance
    DecEq-Ty : DecEq Ty
    DecEq-Ty .DecEq._≟_ = λ where ⋆ ⋆ → yes refl

  open FreeMonoidalHelper Mon Ty using () renaming (ObjTerm to ObjTermᴵ; unit to unitᴵ; Var to Varᴵ)

  arityT : Fin 3 → ObjTermᴵ × ObjTermᴵ
  arityT zero             = Varᴵ ⋆ , unitᴵ    -- 0 → e : ⋆ → unit
  arityT (suc zero)       = unitᴵ , unitᴵ     -- 1 → w : unit → unit
  arityT (suc (suc zero)) = unitᴵ , Varᴵ ⋆    -- 2 → u : unit → ⋆

  private module FS = FinSig {Ty} arityT
  open FS
  open Frontend {Ty} GenS
  open Decide rankS

  private
    infixr 9 _∘ᴵ_
    _∘ᴵ_ : ∀ {A B C} → S.HomTerm B C → S.HomTerm A B → S.HomTerm A C
    _∘ᴵ_ = S._∘_
    e' = gen zero
    w' = gen (suc zero)
    u' = gen (suc (suc zero))

    -- the same scalar equation, laid out with `w` before and after `u ∘ e`
    t₀ = e' ∘ᴵ (u' ∘ᴵ w')
    t₂ = w' ∘ᴵ (e' ∘ᴵ u')

  -- both sides cycle, and the loop says so …
  lim-cycle-status : statusF t₀ ≡ cycled
  lim-cycle-status = refl

  lim-cycle-statusʳ : statusF t₂ ≡ cycled
  lim-cycle-statusʳ = refl

  -- … and the true equation is refused.
  lim-cycle-nothing : decide?F t₀ t₂ ≡ nothing
  lim-cycle-nothing = refl

  -- The machine check that the refused equation IS true (solver soundness):
  -- the identical pair under a rank making `w` minimal converges and is
  -- decided.
  private
    rankW : GenΣ → ℕ
    rankW (_ , _ , genS zero)          = 1
    rankW (_ , _ , genS (suc zero))    = 0
    rankW (_ , _ , genS (suc (suc _))) = 2

    module DW = Decide rankW

  lim-cycle-true : is-just (DW.decide?F t₀ t₂) ≡ true
  lim-cycle-true = refl
