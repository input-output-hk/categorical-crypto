{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- SPIKE: augmenting `solveM` to a solver that handles MORPHISM VARIABLES.
--
-- `Categories.MonoidalCoherence.Solver.solveM` works in the free monoidal
-- category over an OBJECT-variable assignment with `mor = ⊥` (no morphism
-- generators).  Its coherence engine `all-Comm` can only prove equations
-- between structural morphisms (composites of α/λ/ρ and ⊗/∘), and it
-- *provably cannot* prove a two-box interchange, because there are no boxes
-- to interchange: `mor x y = ⊥`.
--
-- Here we set up the SAME transport architecture as `Solver`, but over a
-- free monoidal category WITH morphism generators, namely the `mor` of
-- `Categories.DiagramRewriteUntyped.Untyped`.  We then:
--
--   1. build a `FreeFunctorData` whose `mor` is exactly `Untyped`'s box
--      wrapper and whose `⟦_⟧ᵖ₁` interprets each `box (f : Mor a b)` as a
--      user-supplied target morphism;
--   2. expose `solveMorReflected = Functor.F-resp-≈ freeFunctor`, the engine
--      that transports any `≈Term` into the target;
--   3. feed `Untyped.TwoBoxSwap.two-box-swap` (an honest morphism-variable
--      coherence the structural solver cannot prove) through it, landing a
--      genuine interchange equation in an ARBITRARY target monoidal category.
--
-- The whole file is hole-free and postulate-free.
--------------------------------------------------------------------------------

module Categories.SolveMorSpike where

open import Level using (Level)
open import Data.List using (List; []; _++_)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Functor using (Functor)

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped using (module Untyped)

--------------------------------------------------------------------------------
-- Parameters of the augmented solver.
--
--   * `X`          : the set of object variables (wire labels).
--   * `Mor`        : the morphism-generator family, indexed by lists of wires
--                    (this is precisely the indexing `Untyped` expects).
--   * `C`          : an ARBITRARY target monoidal category.
--   * `⟦_⟧ᵖ₀`      : interpretation of object variables into `C`.
--   * `⟦Mor⟧`      : interpretation of each generator `Mor a b` into `C`, as a
--                    morphism between the interpreted wire-objects.
--
-- The crucial plumbing: `Untyped {X} Mor` opens `FreeMonoidalHelper.Mor Mon X
-- (Untyped.mor)`.  So if we build `FreeMonoidalData` with that very `mor`,
-- then `FreeMonoidal d`'s `HomTerm`/`≈Term` are *definitionally identical* to
-- `Untyped`'s, and `two-box-swap` typechecks unchanged against the functor.
--------------------------------------------------------------------------------

module SolveMor
  {o ℓ e : Level}
  {X : Set}
  (Mor : List X → List X → Set)
  (C : MonoidalCategory o ℓ e)
  (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
  where

  open MonoidalCategory C using () renaming (U to Cᵤ)
  module Cᵤ = Category Cᵤ

  -- Bring `Untyped`'s machinery (wires, box, mor, ⟦_⟧, TwoBoxSwap, …) into
  -- scope.  `Untyped` itself opens `FreeMonoidalHelper.Mor Mon X mor`.
  open Untyped Mon {X} Mor

  -- The free monoidal data whose generators ARE `Untyped`'s boxes.
  -- `mor` here is the `data mor` of `Untyped`, so `FreeMonoidal d`'s HomTerm
  -- coincides definitionally with `Untyped`'s HomTerm.
  d : FreeMonoidalData
  d = record { v = Mon ; X = X ; mor = mor }

  -- `FreeMonoidal d` re-exports `HomTerm`/`_≈Term_`/`var`/… publicly, and
  -- because `d.mor = Untyped.mor`, these coincide *definitionally* with the
  -- ones `Untyped` (hence `two-box-swap`) uses.  This is the key plumbing
  -- the spike had to nail.
  open FreeMonoidal d using (HomTerm; _≈Term_)

  -- The target as a `⟦ Mon ⟧ᵥ` value.  We define it ONCE and reuse it both for
  -- the object interpretation `⟦_⟧obj` and for `ffd`'s `⟦v⟧`, so the two agree
  -- definitionally (an inline `λ where ⦃ () ⦄` in each place would otherwise be
  -- two *distinct* extended lambdas and fail to unify).
  ⟦v⟧ : ⟦ Mon ⟧ᵥ {o} {ℓ} {e}
  ⟦v⟧ = record
    { C = Cᵤ
    ; Monoidal-C = C .MonoidalCategory.monoidal
    ; Symmetric-C = λ where ⦃ () ⦄
    }

  -- We need the interpretation of each generator into `C`.  A generator is a
  -- `box (f : Mor a b) : mor (wires a) (wires b)`, so we additionally take an
  -- interpretation of the underlying `Mor` family into target homs between the
  -- interpreted wire objects.  We first need `⟦_⟧₀` to even *state* its type,
  -- which `FreeFunctorHelper.Go` provides; we recover it below.

  -- Object interpretation, mirrored from `FreeFunctorData`'s `Go ⟦_⟧ᵖ₀`.
  open FreeFunctorHelper d ⟦v⟧ using (module Go)
  open Go ⟦_⟧ᵖ₀ using () renaming (⟦_⟧₀ to ⟦_⟧obj) public

  module WithMor
    -- interpretation of each generator into the target
    (⟦Mor⟧ : ∀ {a b} → Mor a b → Cᵤ [ ⟦ wires a ⟧obj , ⟦ wires b ⟧obj ])
    where

    -- The free-functor data: same shape as `Solver`'s, but with a real `mor`
    -- and a real `⟦_⟧ᵖ₁` (instead of `mor = ⊥`, `⟦_⟧ᵖ₁ = λ ()`).
    ffd : FreeFunctorData d {o} {ℓ} {e}
    ffd = record
      { ⟦v⟧ = ⟦v⟧
      ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀
      ; ⟦_⟧ᵖ₁ = λ where (box f) → ⟦Mor⟧ f   -- a box is interpreted by ⟦Mor⟧
      }

    open FreeFunctor {d = d} ffd public
      using (⟦_⟧₁; freeFunctor)

    ------------------------------------------------------------------------
    -- (2) The augmentation engine: transport any free-category equation
    -- through the free functor into the target.  This is the morphism-aware
    -- analogue of the final line of `solveM`.
    ------------------------------------------------------------------------
    solveMorReflected : ∀ {A B} {f g : HomTerm A B}
                      → f ≈Term g → Cᵤ [ ⟦ f ⟧₁ ≈ ⟦ g ⟧₁ ]
    solveMorReflected = Functor.F-resp-≈ freeFunctor

    ------------------------------------------------------------------------
    -- (3) THE PAYOFF.  Instantiate the two-box interchange at the smallest
    -- nontrivial frame (pre = mid = r = []), giving a genuine `≈Term`
    -- equation between two morphism-variable composites in the FREE category,
    -- then transport it into the arbitrary target `C`.
    --
    -- This is exactly what `solveM` cannot do: with `mor = ⊥` there are no
    -- `f`, `g` to interchange.
    ------------------------------------------------------------------------
    module _ {a₁ b₁ a₂ b₂ : List X}
             (f : Mor a₁ b₁) (g : Mor a₂ b₂) where

      open TwoBoxSwap [] [] [] f g using (f-first; g-first; two-box-swap)

      -- the interchange, in the free category (with morphism generators)
      interchange : f-first ≈Term g-first
      interchange = two-box-swap

      -- the interchange, transported into the ARBITRARY target monoidal `C`
      interchange-target : Cᵤ [ ⟦ f-first ⟧₁ ≈ ⟦ g-first ⟧₁ ]
      interchange-target = solveMorReflected interchange
