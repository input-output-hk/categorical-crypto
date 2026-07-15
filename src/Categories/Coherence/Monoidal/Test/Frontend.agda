{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Test suite for the solver front-end (`Categories.Coherence.Monoidal.Frontend.solveMor!`),
-- organised by capability, with the solver's LIMITATIONS exhibited as
-- machine-checked `decide?F … ≡ nothing` facts (so the boundary of the
-- decision procedure is itself checked).
--
--   * `Coherence`     — pure MacLane coherence (unitors, associator,
--                       triangle, pentagon).
--   * `Naturality`    — unitor/associator naturality THROUGH box generators.
--   * `Functorial`    — id/∘ laws and in-order ⊗-functoriality.
--   * `Interchange`   — disjoint boxes in either firing order: multi-wire
--                       boxes (μ), empty-domain boxes (η), scalars
--                       (u : unit → unit); NON-HEAD inversions and a 3-swap
--                       full sort exercise machine-fired interchange swaps.
--   * `Reorder`       — the black-box re-expression of the former white-box
--                       `Test.Normalize` litmus (two single-wire boxes).
--   * `Negative`      — sound rejections.
--   * `Limitations`   — TRUE equations the solver does NOT decide, pinned by
--                       `≡ nothing`.
--   * `Target`        — C-level showcase: `solveMor!` one-liners reading in
--                       the target's own vocabulary.
--   * `Rewrite`       — the focusing / rewriting layer (`rewriteMor!`,
--                       `rewriteMorₙ!`, `rewriteMorAuto!`, `focusAtₙ`).
--
-- LIMITATION CATALOGUE (L2 machine-checked below):
--
--   L1 (soundness only).  Every `just` carries a real `_≈Term_` proof, but
--       `nothing` does not refute the equation.
--
--   L2 (ambiguous pairs need an injective rank).  Scalar-like layers at
--       the same offset (`mid ≡ [] ∧ by ≡ [] ∧ ax ≡ []`) fit the swap
--       recogniser in BOTH orders, so they are canonicalized by the
--       user-supplied `rank`; under a NON-INJECTIVE rank the sort cannot
--       separate them (`lim-equal-rank` pins `u ∘ v ≈ v ∘ u` at constant
--       rank, `test-scalar-order` decides with the Fin-index rank).
--
--   L3 (monoidal only).  At `Variant` `Mon`: no braiding, so symmetric goals
--       (anything mentioning σ) are not expressible.
--
--   L4 (concrete signatures only).  The decision computes by evaluation; over
--       ABSTRACT atoms the `++`-casts inside `reflectF` do not reduce, so the
--       implicit hit of `solveTerm!`/`solveMor!` cannot be auto-discharged.
--
--   L5 (syntactic generators).  Generator-specific equations (a box's
--       naturality, Frobenius laws, …) are not DISCOVERED by the decision
--       procedure (`neg-generator-naturality`); they are instead APPLIED by
--       the `rewriteMor!` family (the `Rewrite` module below).
--
--   L6 (no canonicity claim).  `norm ∘ reflect` is not claimed to be a
--       canonical form; the suite documents which equation SHAPES decide.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Test.Frontend where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_])

open import Data.Fin using (Fin; zero; suc)

open import Categories.Category using (_[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.FreeMonoidal using (Mon; module FreeMonoidalHelper)
open import Categories.Coherence.Monoidal.Frontend using (module Frontend)
open import Categories.Coherence.Monoidal.Frontend.Core using (module FinSig)

------------------------------------------------------------------------
-- Wire colours and the generator signature (ObjTerm arities, Fin-indexed).
--
--   0 → μ  : ⋆ ⊗ ⋆ → ⋆     (multi-wire input)
--   1 → η  : unit  → ⋆      (empty domain)
--   2 → s  : ⋆ → ⋆          (endo on ⋆)
--   3 → s' : ⋆ → ⋆          (second endo on ⋆)
--   4 → t  : • → •          (endo on •)
--   5 → u  : unit → unit    (scalar)
--   6 → v  : unit → unit    (second scalar, for the L2 exhibit)

data Ty : Set where ⋆ • : Ty

_≟Ty_ : DecidableEquality Ty
⋆ ≟Ty ⋆ = yes refl
⋆ ≟Ty • = no λ ()
• ≟Ty ⋆ = no λ ()
• ≟Ty • = yes refl

open FreeMonoidalHelper Mon Ty using (ObjTerm; unit; _⊗₀_; Var)

arityT : Fin 7 → ObjTerm × ObjTerm
arityT zero                            = Var ⋆ ⊗₀ Var ⋆ , Var ⋆
arityT (suc zero)                      = unit , Var ⋆
arityT (suc (suc zero))                = Var ⋆ , Var ⋆
arityT (suc (suc (suc zero)))          = Var ⋆ , Var ⋆
arityT (suc (suc (suc (suc zero))))    = Var • , Var •
arityT (suc (suc (suc (suc (suc _))))) = unit , unit   -- 5 → u, 6 → v

open FinSig Mon {Ty} arityT using (GenS; genS; module S; gen; _≟G_; rankS)

------------------------------------------------------------------------
-- The front-end term language and the solver instance.

open Frontend {Ty} _≟Ty_ GenS

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
  μ'  = gen zero
  η'  = gen (suc zero)
  s'  = gen (suc (suc zero))
  s'' = gen (suc (suc (suc zero)))
  t'  = gen (suc (suc (suc (suc zero))))
  u'  = gen (suc (suc (suc (suc (suc zero)))))
  v'  = gen (suc (suc (suc (suc (suc (suc zero))))))

------------------------------------------------------------------------
-- Coherence: pure MacLane equations decide.

module Coherence where

  test-λ-iso : S.λ⇒ ∘' S.λ⇐ ≈' id' {Var ⋆}
  test-λ-iso = solveTerm! (S.λ⇒ ∘' S.λ⇐) id'

  test-ρ-iso : S.ρ⇒ ∘' S.ρ⇐ ≈' id' {Var ⋆}
  test-ρ-iso = solveTerm! (S.ρ⇒ ∘' S.ρ⇐) id'

  test-α-iso : S.α⇐ ∘' S.α⇒ ≈' id' {(Var ⋆ ⊗₀ Var •) ⊗₀ Var ⋆}
  test-α-iso = solveTerm! (S.α⇐ ∘' S.α⇒) id'

  -- Kelly: the two unitors agree on the unit object.
  test-λ≈ρ-unit : S.λ⇒ {unit} ≈' S.ρ⇒ {unit}
  test-λ≈ρ-unit = solveTerm! S.λ⇒ S.ρ⇒

  test-triangle : (id' ⊗' S.λ⇒) ∘' S.α⇒ ≈' S.ρ⇒ {Var ⋆} ⊗' id' {Var •}
  test-triangle = solveTerm! ((id' ⊗' S.λ⇒) ∘' S.α⇒) (S.ρ⇒ ⊗' id')

  test-pentagon
    : (id' ⊗' S.α⇒) ∘' S.α⇒ ∘' (S.α⇒ ⊗' id')
      ≈' S.α⇒ ∘' S.α⇒ {Var ⋆ ⊗₀ Var •} {Var ⋆} {Var •}
  test-pentagon =
    solveTerm! ((id' ⊗' S.α⇒) ∘' S.α⇒ ∘' (S.α⇒ ⊗' id')) (S.α⇒ ∘' S.α⇒)

------------------------------------------------------------------------
-- Naturality of the structural morphisms through box generators.

module Naturality where

  test-λ-nat : S.λ⇒ ∘' (id' {unit} ⊗' s') ≈' s' ∘' S.λ⇒
  test-λ-nat = solveTerm! (S.λ⇒ ∘' (id' ⊗' s')) (s' ∘' S.λ⇒)

  test-ρ-nat : S.ρ⇒ ∘' (s' ⊗' id' {unit}) ≈' s' ∘' S.ρ⇒
  test-ρ-nat = solveTerm! (S.ρ⇒ ∘' (s' ⊗' id')) (s' ∘' S.ρ⇒)

  test-α-nat
    : S.α⇒ ∘' ((s' ⊗' t') ⊗' s'') ≈' (s' ⊗' (t' ⊗' s'')) ∘' S.α⇒
  test-α-nat =
    solveTerm! (S.α⇒ ∘' ((s' ⊗' t') ⊗' s'')) ((s' ⊗' (t' ⊗' s'')) ∘' S.α⇒)

  -- a box with non-trivial arity through the associator.
  test-α-nat-μ
    : S.α⇒ ∘' ((μ' ⊗' t') ⊗' s') ≈' (μ' ⊗' (t' ⊗' s')) ∘' S.α⇒
  test-α-nat-μ =
    solveTerm! (S.α⇒ ∘' ((μ' ⊗' t') ⊗' s')) ((μ' ⊗' (t' ⊗' s')) ∘' S.α⇒)

------------------------------------------------------------------------
-- Functoriality: id/∘ laws and IN-ORDER ⊗-functoriality.

module Functorial where

  test-idˡ : id' ∘' s' ≈' s'
  test-idˡ = solveTerm! (id' ∘' s') s'

  test-idʳ : s' ∘' id' ≈' s'
  test-idʳ = solveTerm! (s' ∘' id') s'

  test-assoc : (s'' ∘' s') ∘' s' ≈' s'' ∘' (s' ∘' s')
  test-assoc = solveTerm! ((s'' ∘' s') ∘' s') (s'' ∘' (s' ∘' s'))

  test-id⊗id : id' {Var ⋆} ⊗' id' {Var •} ≈' id'
  test-id⊗id = solveTerm! (id' ⊗' id') id'

  -- ⊗-functoriality with firing orders agreeing after reflect:
  -- left factor's layers all before the right factor's.
  test-⊗-∘-in-order
    : (s'' ∘' s') ⊗' t' ≈' (s'' ⊗' t') ∘' (s' ⊗' id')
  test-⊗-∘-in-order =
    solveTerm! ((s'' ∘' s') ⊗' t') ((s'' ⊗' t') ∘' (s' ⊗' id'))

------------------------------------------------------------------------
-- Interchange: disjoint boxes in either firing order.  The out-of-order
-- sides exercise a genuine machine-fired swap inside `norm`.

module Interchange where

  -- the pure interchange equation, both composites.
  test-swap
    : (id' ⊗' t') ∘' (s' ⊗' id') ≈' (s' ⊗' id') ∘' (id' ⊗' t')
  test-swap =
    solveTerm! ((id' ⊗' t') ∘' (s' ⊗' id')) ((s' ⊗' id') ∘' (id' ⊗' t'))

  -- collapse to the tensor, s-first (in order) and t-first (one swap).
  test-s-first : (id' ⊗' t') ∘' (s' ⊗' id') ≈' s' ⊗' t'
  test-s-first = solveTerm! ((id' ⊗' t') ∘' (s' ⊗' id')) (s' ⊗' t')

  test-t-first : (s' ⊗' id') ∘' (id' ⊗' t') ≈' s' ⊗' t'
  test-t-first = solveTerm! ((s' ⊗' id') ∘' (id' ⊗' t')) (s' ⊗' t')

  -- normalization fires on the RIGHT side too.
  test-rhs-swap : s' ⊗' t' ≈' (s' ⊗' id') ∘' (id' ⊗' t')
  test-rhs-swap = solveTerm! (s' ⊗' t') ((s' ⊗' id') ∘' (id' ⊗' t'))

  -- a deeper wire context: t on the LAST of three wires.
  test-deep
    : (s' ⊗' (id' {Var •} ⊗' id')) ∘' (id' ⊗' (id' ⊗' t'))
      ≈' s' ⊗' (id' ⊗' t')
  test-deep =
    solveTerm! ((s' ⊗' (id' ⊗' id')) ∘' (id' ⊗' (id' ⊗' t')))
               (s' ⊗' (id' ⊗' t'))

  -- a multi-wire box (μ : ⋆⊗⋆ → ⋆) interchanging with t.
  test-μ-swap : (μ' ⊗' id') ∘' (id' ⊗' t') ≈' μ' ⊗' t'
  test-μ-swap = solveTerm! ((μ' ⊗' id') ∘' (id' ⊗' t')) (μ' ⊗' t')

  -- an empty-domain box (η : unit → ⋆) interchanging with t.
  test-η-swap : (η' ⊗' id') ∘' (id' {unit} ⊗' t') ≈' η' ⊗' t'
  test-η-swap = solveTerm! ((η' ⊗' id') ∘' (id' ⊗' t')) (η' ⊗' t')

  -- a scalar (u : unit → unit) interchanging with s.
  test-u-swap : (u' ⊗' id') ∘' (id' {unit} ⊗' s') ≈' u' ⊗' s'
  test-u-swap = solveTerm! ((u' ⊗' id') ∘' (id' ⊗' s')) (u' ⊗' s')

  -- Eckmann-Hilton-style scalar reordering canonicalized by the `rank`
  -- tiebreak (L2): u = index 5 fires before v = index 6.
  test-scalar-order : u' ∘' v' ≈' v' ∘' u'
  test-scalar-order = solveTerm! (u' ∘' v') (v' ∘' u')

  -- interchange is transparent to reassociation: the same two-box diagram
  -- stated across an associator conjugation.
  test-α-transparent
    : S.α⇒ ∘' ((s' ⊗' id') ⊗' t') ∘' S.α⇐ ≈' s' ⊗' (id' {Var ⋆} ⊗' t')
  test-α-transparent =
    solveTerm! (S.α⇒ ∘' ((s' ⊗' id') ⊗' t') ∘' S.α⇐) (s' ⊗' (id' ⊗' t'))

  -- the head swap fires with a non-trivial third layer in the tail.
  test-swap-with-tail
    : (s'' ⊗' id') ∘' (s' ⊗' id') ∘' (id' {Var ⋆} ⊗' t')
      ≈' (s'' ⊗' id') ∘' (id' ⊗' t') ∘' (s' ⊗' id')
  test-swap-with-tail =
    solveTerm! ((s'' ⊗' id') ∘' (s' ⊗' id') ∘' (id' ⊗' t'))
               ((s'' ⊗' id') ∘' (id' ⊗' t') ∘' (s' ⊗' id'))

  -- a NON-HEAD inversion (layers 2-3): the position loop `step?` walks past
  -- the in-order head pair and fires deeper.
  test-non-head-swap
    : (s'' ∘' s') ⊗' t' ≈' (s'' ⊗' id') ∘' (s' ⊗' t')
  test-non-head-swap =
    solveTerm! ((s'' ∘' s') ⊗' t') ((s'' ⊗' id') ∘' (s' ⊗' t'))

  -- three independent boxes fired fully descending vs ascending: the
  -- fuel-driven loop (`normFuelWith`) fires THREE genuine swaps.
  private
    W₃' = Var ⋆ ⊗₀ (Var ⋆ ⊗₀ Var ⋆)
    desc₃ : S.HomTerm W₃' W₃'
    desc₃ = (s' ⊗' (id' ⊗' id'))
         ∘' (id' ⊗' (s' ⊗' id'))
         ∘' (id' ⊗' (id' ⊗' s'))
    asc₃ : S.HomTerm W₃' W₃'
    asc₃ = (id' ⊗' (id' ⊗' s'))
        ∘' (id' ⊗' (s' ⊗' id'))
        ∘' (s' ⊗' (id' ⊗' id'))

  test-three-desc : desc₃ ≈' asc₃
  test-three-desc = solveTerm! desc₃ asc₃

------------------------------------------------------------------------
-- Reorder: the front-end (black-box) re-expression of the former white-box
-- `Categories.Coherence.Monoidal.Test.Normalize` litmus.  There, two independent
-- single-wire boxes `fbox` (wire 0) and `gbox` (wire 1), presented out of
-- order, were reordered by directly poking the normalizer internals
-- (`leftFit?`, `swapHeadD`, `normalizeD`).  Here the SAME two single-wire
-- endos — `s'` on ⋆ (= `fbox`, offset 0) and `t'` on • (= `gbox`, offset 1) —
-- are reordered by that very engine, which `solveTerm!` runs internally; we
-- observe only the decided `≈Term` instead of the engine's intermediates.

module Reorder where

  -- both orderings of the two disjoint boxes agree (was `clean-reorder` /
  -- `litDiagUSwap`): the swap fires inside `norm`.
  reorder-swap
    : (id' ⊗' t') ∘' (s' ⊗' id') ≈' (s' ⊗' id') ∘' (id' ⊗' t')
  reorder-swap =
    solveTerm! ((id' ⊗' t') ∘' (s' ⊗' id')) ((s' ⊗' id') ∘' (id' ⊗' t'))

  -- the higher-offset-first presentation (old `gbox`-first input) is
  -- canonicalised to the plain tensor — one swap fires (was the
  -- `normalizeD`/`leftFit?` reorder `litNormReorders`).
  reorder-canonicalise : (s' ⊗' id') ∘' (id' ⊗' t') ≈' s' ⊗' t'
  reorder-canonicalise = solveTerm! ((s' ⊗' id') ∘' (id' ⊗' t')) (s' ⊗' t')

  -- the recogniser conservatively does NOT swap an in-order same-wire pair
  -- (was `litLeftFit?-no`): sequential order on one wire is preserved.
  reorder-no-false-swap : decide?F (s'' ∘' s') (s' ∘' s'') ≡ nothing
  reorder-no-false-swap = refl

------------------------------------------------------------------------
-- Sound rejections: the solver answers `nothing` on non-equations.

module Negative where

  -- distinct endo generators are not identified.
  neg-distinct-endos : decide?F s' s'' ≡ nothing
  neg-distinct-endos = refl

  -- sequential order of two boxes on the SAME wire matters.
  neg-sequential-order : decide?F (s'' ∘' s') (s' ∘' s'') ≡ nothing
  neg-sequential-order = refl

  -- diagrams of DIFFERENT length stay apart: one box vs an extra layer.
  -- (The reflected diagrams have unequal layer counts, so the structural
  -- compare rejects on the nil-vs-cons branch of the encoding.)
  neg-extra-layer : decide?F s' (s'' ∘' s') ≡ nothing
  neg-extra-layer = refl

  -- generator naturality is NOT known to the solver (L5): s' past μ.
  neg-generator-naturality
    : decide?F (s' ∘' μ') (μ' ∘' (s' ⊗' id')) ≡ nothing
  neg-generator-naturality = refl

------------------------------------------------------------------------
-- LIMITATIONS, machine-checked: TRUE equations answered `nothing`.

module Limitations where

  -- L2: under a constant (non-injective) rank the tiebreak never fires.
  private module D₀ = Decide _≟G_ (λ _ → 0)

  lim-equal-rank : D₀.decide?F (u' ∘' v') (v' ∘' u') ≡ nothing
  lim-equal-rank = refl

------------------------------------------------------------------------
-- C-level showcase: statements read in the target's own vocabulary.

module Target {o ℓ e : Level} (C : MonoidalCategory o ℓ e) where

  private module MC = MonoidalCategory C

  module At
    (A B : MC.Obj)
    (μᴹ  : C .MonoidalCategory.U [ A MC.⊗₀ A , A ])
    (ηᴹ  : C .MonoidalCategory.U [ MC.unit , A ])
    (sᴹ  : C .MonoidalCategory.U [ A , A ])
    (s'ᴹ : C .MonoidalCategory.U [ A , A ])
    (tᴹ  : C .MonoidalCategory.U [ B , B ])
    (uᴹ  : C .MonoidalCategory.U [ MC.unit , MC.unit ])
    where

    private
      ⟦_⟧₀T : Ty → MC.Obj
      ⟦ ⋆ ⟧₀T = A
      ⟦ • ⟧₀T = B

    open Into C ⟦_⟧₀T
    open WithGen (λ { (genS zero)                            → μᴹ
                    ; (genS (suc zero))                      → ηᴹ
                    ; (genS (suc (suc zero)))                → sᴹ
                    ; (genS (suc (suc (suc zero))))          → s'ᴹ
                    ; (genS (suc (suc (suc (suc zero)))))    → tᴹ
                    ; (genS (suc (suc (suc (suc (suc _)))))) → uᴹ })

    open MC using () renaming (_⊗₁_ to _⊗C_)

    -- interchange, the out-of-order composite (a machine-fired swap).
    test-interchange
      : C .MonoidalCategory.U
          [ (sᴹ ⊗C MC.id) MC.∘ (MC.id ⊗C tᴹ) ≈ sᴹ ⊗C tᴹ ]
    test-interchange = solveMor! ((s' ⊗' id') ∘' (id' ⊗' t')) (s' ⊗' t')

    -- ⊗-functoriality, in-order composite.
    test-⊗-∘
      : C .MonoidalCategory.U
          [ (s'ᴹ MC.∘ sᴹ) ⊗C tᴹ ≈ (s'ᴹ ⊗C tᴹ) MC.∘ (sᴹ ⊗C MC.id) ]
    test-⊗-∘ = solveMor! ((s'' ∘' s') ⊗' t') ((s'' ⊗' t') ∘' (s' ⊗' id'))

    -- unitor naturality at a generator.
    test-ρ-nat
      : C .MonoidalCategory.U
          [ MC.unitorʳ.from MC.∘ (sᴹ ⊗C MC.id) ≈ sᴹ MC.∘ MC.unitorʳ.from ]
    test-ρ-nat = solveMor! (S.ρ⇒ ∘' (s' ⊗' id')) (s' ∘' S.ρ⇒)

    ------------------------------------------------------------------------
    -- Rewriting: rule application in context (the L5 mitigation).  A rule is
    -- any C-equation between interpretations of front-end terms — here
    -- abstract hypotheses (commuting endos, an inverse law); the rewrite
    -- layer carries it across and the solver absorbs surrounding structure.

    module Rewrite
      -- the rules: abstract hypotheses about the generators.
      (comm : C .MonoidalCategory.U [ s'ᴹ MC.∘ sᴹ ≈ sᴹ MC.∘ s'ᴹ ])
      (inv  : C .MonoidalCategory.U [ sᴹ MC.∘ s'ᴹ ≈ MC.id ])
      where

      -- the rule fires in the RIGHT factor of a tensor (auto-positioned).
      test-rw-right
        : C .MonoidalCategory.U
            [ tᴹ ⊗C (s'ᴹ MC.∘ sᴹ) ≈ tᴹ ⊗C (sᴹ MC.∘ s'ᴹ) ]
      test-rw-right =
        rewriteMorAuto! (t' ⊗' (s'' ∘' s')) (t' ⊗' (s' ∘' s''))
                        (s'' ∘' s') (s' ∘' s'') comm

      -- the rule fires in the LEFT factor.
      test-rw-left
        : C .MonoidalCategory.U
            [ (s'ᴹ MC.∘ sᴹ) ⊗C tᴹ ≈ (sᴹ MC.∘ s'ᴹ) ⊗C tᴹ ]
      test-rw-left =
        rewriteMorAuto! ((s'' ∘' s') ⊗' t') ((s' ∘' s'') ⊗' t')
                        (s'' ∘' s') (s' ∘' s'') comm

      -- the redex is NOT a syntactic subterm (it is split across an
      -- interchange): the manual frame + the solver's reconciliation
      -- absorb the reshaping.
      test-rw-interchange
        : C .MonoidalCategory.U
            [ (s'ᴹ ⊗C MC.id) MC.∘ (sᴹ ⊗C tᴹ) ≈ (sᴹ ⊗C MC.id) MC.∘ (s'ᴹ ⊗C tᴹ) ]
      test-rw-interchange =
        rewriteMor! ((s'' ⊗' id') ∘' (s' ⊗' t')) ((s' ⊗' id') ∘' (s'' ⊗' t'))
                    (S.λ⇐ ∘' (id' ⊗' t')) S.λ⇒
                    (s'' ∘' s') (s' ∘' s'') comm

      -- iso-cancellation as a rewrite: the inverse law collapses the
      -- composite to id inside a context.
      test-rw-cancel
        : C .MonoidalCategory.U
            [ tᴹ ⊗C (sᴹ MC.∘ s'ᴹ) ≈ tᴹ ⊗C MC.id ]
      test-rw-cancel =
        rewriteMorAuto! (t' ⊗' (s' ∘' s'')) (t' ⊗' id')
                        (s' ∘' s'') id' inv

      -- explicit occurrence index: the redex appears in BOTH tensor factors;
      -- `rewriteMorₙ!` at n = 1 selects the second occurrence (right factor),
      -- leaving the first untouched.
      test-rw-nth
        : C .MonoidalCategory.U
            [ (s'ᴹ MC.∘ sᴹ) ⊗C (s'ᴹ MC.∘ sᴹ) ≈ (s'ᴹ MC.∘ sᴹ) ⊗C (sᴹ MC.∘ s'ᴹ) ]
      test-rw-nth =
        rewriteMorₙ! ((s'' ∘' s') ⊗' (s'' ∘' s')) ((s'' ∘' s') ⊗' (s' ∘' s''))
                     (s'' ∘' s') (s' ∘' s'') 1 comm
