{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Test suite for the PUBLIC monoidal solver front-end
-- (`Categories.Coherence.Monoidal`), organised by capability.  Every test
-- states its goal in an ARBITRARY target monoidal category `C`'s own
-- vocabulary and discharges it with a public solver:
--
--   * `Coherence`     — pure MacLane coherence (unitors, associator,
--                       triangle, pentagon), via `Structural.solveM`.
--   * `Naturality`    — unitor/associator naturality THROUGH box generators,
--                       via `Mor.solveMor!`.
--   * `Functorial`    — id/∘ laws and in-order ⊗-functoriality, via
--                       `Mor.solveMor!`.
--   * `Interchange`   — disjoint boxes in either firing order: multi-wire
--                       boxes (μ), empty-domain boxes (η), scalars
--                       (u : unit → unit); NON-HEAD inversions and a 3-swap
--                       full sort exercise machine-fired interchange swaps,
--                       via `Mor.solveMor!`.
--   * `Rewrite`       — rule application in context, via the
--                       `Mor.rewriteMor!` family.
--
-- Because the goals read in `C`'s vocabulary, `solveMor!`/`solveM` over an
-- arbitrary `C` exercise the free-level decision procedures, just stated in
-- the target's terms.
--
-- The `Negative` module below adds SOUND-REJECTION tests via the
-- INTERNAL front-end API: they pin the decision procedure with
-- `decide?F … ≡ nothing` on FALSE equations, which the public solvers
-- cannot express.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Test.Frontend where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Data.Fin
open import Data.Vec using (_∷_; [])

open import Categories.Category using (_[_,_]; _[_≈_])
open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Coherence.Monoidal.Frontend.Core
import Categories.Coherence.Monoidal.Api as Coh

------------------------------------------------------------------------
-- Coherence: pure MacLane equations decide, via the structural solver.
--
-- Two object atoms `A , B`; the solver's term DSL (`Var`, `_⊗₀_`, `unit`,
-- `_⊗₁_`, `_∘_`, `id`, `λ⇒`, `ρ⇒`, `α⇒`, …) and interpretation `⟦_⟧₁` are
-- exposed by the `Structural` module.

module Coherence {o ℓ e : Level} (C : MonoidalCategory o ℓ e) (A B : C .MonoidalCategory.Obj) where

  open Coh.Structural C (A ∷ B ∷ [])

  private
    a : ObjTerm
    a = Var zero
    b : ObjTerm
    b = Var (suc zero)

  test-λ-iso : C .MonoidalCategory.U [ ⟦ λ⇒ ∘ λ⇐ {a} ⟧₁ ≈ ⟦ id {a} ⟧₁ ]
  test-λ-iso = solveM (λ⇒ ∘ λ⇐) (id {a})

  test-ρ-iso : C .MonoidalCategory.U [ ⟦ ρ⇒ ∘ ρ⇐ {a} ⟧₁ ≈ ⟦ id {a} ⟧₁ ]
  test-ρ-iso = solveM (ρ⇒ ∘ ρ⇐) (id {a})

  test-α-iso : C .MonoidalCategory.U [ ⟦ α⇐ ∘ α⇒ {a} {b} {a} ⟧₁ ≈ ⟦ id {(a ⊗₀ b) ⊗₀ a} ⟧₁ ]
  test-α-iso = solveM (α⇐ ∘ α⇒) (id {(a ⊗₀ b) ⊗₀ a})

  -- Kelly: the two unitors agree on the unit object.
  test-λ≈ρ-unit : C .MonoidalCategory.U [ ⟦ λ⇒ {unit} ⟧₁ ≈ ⟦ ρ⇒ {unit} ⟧₁ ]
  test-λ≈ρ-unit = solveM (λ⇒) (ρ⇒)

  test-triangle : C .MonoidalCategory.U [ ⟦ (id ⊗₁ λ⇒) ∘ α⇒ {a} {unit} {b} ⟧₁ ≈ ⟦ ρ⇒ {a} ⊗₁ id {b} ⟧₁ ]
  test-triangle = solveM ((id ⊗₁ λ⇒) ∘ α⇒ {a} {unit}) (ρ⇒ ⊗₁ id {b})

  test-pentagon
    : C .MonoidalCategory.U
        [ ⟦ (id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ {a} {b} {a} ⊗₁ id {b}) ⟧₁
        ≈ ⟦ α⇒ ∘ α⇒ {a ⊗₀ b} {a} {b} ⟧₁ ]
  test-pentagon = solveM ((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ {a} ⊗₁ id)) (α⇒ ∘ α⇒ {a ⊗₀ b} {a} {b})

------------------------------------------------------------------------
-- The morphism-solver tests: over an arbitrary monoidal category `C` with
-- two atoms `A , B` and a signature of box generators:
--
--   0 → μ  : A ⊗ A → A     (multi-wire input)
--   1 → η  : unit  → A      (empty domain)
--   2 → s  : A → A          (endo on A)
--   3 → s' : A → A          (second endo on A)
--   4 → t  : B → B          (endo on B)
--   5 → u  : unit → unit    (scalar)

module Morphism {o ℓ e : Level} (C : MonoidalCategory o ℓ e) where

  private module MC = MonoidalCategory C
  open MC

  module _
    (A B : MC.Obj)
    (μᴹ  : MC.U [ A ⊗₀ A , A ])
    (ηᴹ  : MC.U [ unit , A ])
    (sᴹ  : MC.U [ A , A ])
    (s'ᴹ : MC.U [ A , A ])
    (tᴹ  : MC.U [ B , B ])
    (uᴹ  : MC.U [ unit , unit ])
    where

    module O = FreeMonoidalHelper Mon (Fin 2)
    open O renaming (Var to V) using ()
    open Coh.Mor C (A ∷ B ∷ [])
         ( ((V zero O.⊗₀ V zero , V zero)         , μᴹ)   -- gen 0 : A⊗A → A ↦ μ
         ∷ ((O.unit , V zero)                     , ηᴹ)   -- gen 1 : unit → A ↦ η
         ∷ ((V zero , V zero)                     , sᴹ)   -- gen 2 : A → A ↦ s
         ∷ ((V zero , V zero)                     , s'ᴹ)  -- gen 3 : A → A ↦ s'
         ∷ ((V (suc zero) , V (suc zero))         , tᴹ)   -- gen 4 : B → B ↦ t
         ∷ ((O.unit , O.unit)                     , uᴹ)   -- gen 5 : unit → unit ↦ u
         ∷ [] )

    private
      μ'  = gen zero
      η'  = gen (suc zero)
      s'  = gen (suc (suc zero))
      s'' = gen (suc (suc (suc zero)))
      t'  = gen (suc (suc (suc (suc zero))))
      u'  = gen (suc (suc (suc (suc (suc zero)))))

    ------------------------------------------------------------------------
    -- Naturality of the structural morphisms through box generators.

    module Naturality where

      test-λ-nat : MC.U [ unitorˡ.from ∘ (id ⊗₁ sᴹ) ≈ sᴹ ∘ unitorˡ.from ]
      test-λ-nat = solveMor! (S.λ⇒ S.∘ (S.id S.⊗₁ s')) (s' S.∘ S.λ⇒)

      test-ρ-nat : MC.U [ unitorʳ.from ∘ (sᴹ ⊗₁ id) ≈ sᴹ ∘ unitorʳ.from ]
      test-ρ-nat = solveMor! (S.ρ⇒ S.∘ (s' S.⊗₁ S.id)) (s' S.∘ S.ρ⇒)

      test-α-nat : MC.U [ associator.from ∘ ((sᴹ ⊗₁ tᴹ) ⊗₁ s'ᴹ) ≈ (sᴹ ⊗₁ (tᴹ ⊗₁ s'ᴹ)) ∘ associator.from ]
      test-α-nat = solveMor! (S.α⇒ S.∘ ((s' S.⊗₁ t') S.⊗₁ s'')) ((s' S.⊗₁ (t' S.⊗₁ s'')) S.∘ S.α⇒)

      -- a box with non-trivial arity through the associator.
      test-α-nat-μ : MC.U [ associator.from ∘ ((μᴹ ⊗₁ tᴹ) ⊗₁ sᴹ) ≈ (μᴹ ⊗₁ (tᴹ ⊗₁ sᴹ)) ∘ associator.from ]
      test-α-nat-μ = solveMor! (S.α⇒ S.∘ ((μ' S.⊗₁ t') S.⊗₁ s')) ((μ' S.⊗₁ (t' S.⊗₁ s')) S.∘ S.α⇒)

    ------------------------------------------------------------------------
    -- Functoriality: id/∘ laws and IN-ORDER ⊗-functoriality.

    module Functorial where

      test-idˡ : MC.U [ id ∘ sᴹ ≈ sᴹ ]
      test-idˡ = solveMor! (S.id S.∘ s') s'

      test-idʳ : MC.U [ sᴹ ∘ id ≈ sᴹ ]
      test-idʳ = solveMor! (s' S.∘ S.id) s'

      test-assoc : MC.U [ (s'ᴹ ∘ sᴹ) ∘ sᴹ ≈ s'ᴹ ∘ (sᴹ ∘ sᴹ) ]
      test-assoc = solveMor! ((s'' S.∘ s') S.∘ s') (s'' S.∘ (s' S.∘ s'))

      test-id⊗id : MC.U [ id ⊗₁ id ≈ id ]
      test-id⊗id = solveMor! (S.id S.⊗₁ S.id) (S.id {O.Var zero O.⊗₀ O.Var (suc zero)})

      -- ⊗-functoriality with firing orders agreeing after reflect:
      -- left factor's layers all before the right factor's.
      test-⊗-∘-in-order : MC.U [ (s'ᴹ ∘ sᴹ) ⊗₁ tᴹ ≈ (s'ᴹ ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ]
      test-⊗-∘-in-order = solveMor! ((s'' S.∘ s') S.⊗₁ t') ((s'' S.⊗₁ t') S.∘ (s' S.⊗₁ S.id))

    ------------------------------------------------------------------------
    -- Interchange: disjoint boxes in either firing order.  The out-of-order
    -- sides exercise a genuine machine-fired swap inside `norm`.

    module Interchange where

      -- the pure interchange equation, both composites.
      test-swap : MC.U [ (id ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ≈ (sᴹ ⊗₁ id) ∘ (id ⊗₁ tᴹ) ]
      test-swap = solveMor! ((S.id S.⊗₁ t') S.∘ (s' S.⊗₁ S.id)) ((s' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ t'))

      -- collapse to the tensor, s-first (in order) and t-first (one swap).
      test-s-first : MC.U [ (id ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ≈ sᴹ ⊗₁ tᴹ ]
      test-s-first = solveMor! ((S.id S.⊗₁ t') S.∘ (s' S.⊗₁ S.id)) (s' S.⊗₁ t')

      test-t-first : MC.U [ (sᴹ ⊗₁ id) ∘ (id ⊗₁ tᴹ) ≈ sᴹ ⊗₁ tᴹ ]
      test-t-first = solveMor! ((s' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ t')) (s' S.⊗₁ t')

      -- normalization fires on the RIGHT side too.
      test-rhs-swap : MC.U [ sᴹ ⊗₁ tᴹ ≈ (sᴹ ⊗₁ id) ∘ (id ⊗₁ tᴹ) ]
      test-rhs-swap = solveMor! (s' S.⊗₁ t') ((s' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ t'))

      -- a deeper wire context: t on the LAST of three wires.
      test-deep : MC.U [ (sᴹ ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ (id ⊗₁ tᴹ)) ≈ sᴹ ⊗₁ (id ⊗₁ tᴹ) ]
      test-deep =
        solveMor! ((s' S.⊗₁ (S.id S.⊗₁ S.id))
                     S.∘ (S.id S.⊗₁ (S.id S.⊗₁ t')))
                  (s' S.⊗₁ (S.id {O.Var (suc zero)} S.⊗₁ t'))

      -- a multi-wire box (μ : A⊗A → A) interchanging with t.
      test-μ-swap : MC.U [ (μᴹ ⊗₁ id) ∘ (id ⊗₁ tᴹ) ≈ μᴹ ⊗₁ tᴹ ]
      test-μ-swap = solveMor! ((μ' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ t')) (μ' S.⊗₁ t')

      -- an empty-domain box (η : unit → A) interchanging with t.
      test-η-swap : MC.U [ (ηᴹ ⊗₁ id) ∘ (id ⊗₁ tᴹ) ≈ ηᴹ ⊗₁ tᴹ ]
      test-η-swap = solveMor! ((η' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ t')) (η' S.⊗₁ t')

      -- a scalar (u : unit → unit) interchanging with s.
      test-u-swap : MC.U [ (uᴹ ⊗₁ id) ∘ (id ⊗₁ sᴹ) ≈ uᴹ ⊗₁ sᴹ ]
      test-u-swap = solveMor! ((u' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ s')) (u' S.⊗₁ s')

      -- interchange is transparent to reassociation: the same two-box diagram
      -- stated across an associator conjugation.
      test-α-transparent : MC.U [ associator.from ∘ ((sᴹ ⊗₁ id) ⊗₁ tᴹ) ∘ associator.to ≈ sᴹ ⊗₁ (id ⊗₁ tᴹ) ]
      test-α-transparent =
        solveMor! (S.α⇒ S.∘ ((s' S.⊗₁ S.id) S.⊗₁ t') S.∘ S.α⇐)
                  (s' S.⊗₁ (S.id {O.Var zero} S.⊗₁ t'))

      -- the head swap fires with a non-trivial third layer in the tail.
      test-swap-with-tail
        : MC.U
            [ (s'ᴹ ⊗₁ id) ∘ (sᴹ ⊗₁ id) ∘ (id ⊗₁ tᴹ)
            ≈ (s'ᴹ ⊗₁ id) ∘ (id ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ]
      test-swap-with-tail =
        solveMor! ((s'' S.⊗₁ S.id) S.∘ (s' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ t'))
                  ((s'' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ t') S.∘ (s' S.⊗₁ S.id))

      -- a NON-HEAD inversion (layers 2-3): the position loop `step?` walks past
      -- the in-order head pair and fires deeper.
      test-non-head-swap : MC.U [ (s'ᴹ ∘ sᴹ) ⊗₁ tᴹ ≈ (s'ᴹ ⊗₁ id) ∘ (sᴹ ⊗₁ tᴹ) ]
      test-non-head-swap = solveMor! ((s'' S.∘ s') S.⊗₁ t') ((s'' S.⊗₁ S.id) S.∘ (s' S.⊗₁ t'))

      -- three independent boxes fired fully descending vs ascending: the
      -- fuel-driven loop (`normFuelWith`) fires THREE genuine swaps.
      private
        W₃ : O.ObjTerm
        W₃ = O.Var zero O.⊗₀ (O.Var zero O.⊗₀ O.Var zero)
        desc₃ : S.HomTerm W₃ W₃
        desc₃ = (s' S.⊗₁ (S.id S.⊗₁ S.id)) S.∘ (S.id S.⊗₁ (s' S.⊗₁ S.id)) S.∘ (S.id S.⊗₁ (S.id S.⊗₁ s'))
        asc₃ : S.HomTerm W₃ W₃
        asc₃ = (S.id S.⊗₁ (S.id S.⊗₁ s')) S.∘ (S.id S.⊗₁ (s' S.⊗₁ S.id)) S.∘ (s' S.⊗₁ (S.id S.⊗₁ S.id))

      test-three-desc
        : MC.U
            [ (sᴹ ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ (sᴹ ⊗₁ id)) ∘ (id ⊗₁ (id ⊗₁ sᴹ))
            ≈ (id ⊗₁ (id ⊗₁ sᴹ)) ∘ (id ⊗₁ (sᴹ ⊗₁ id)) ∘ (sᴹ ⊗₁ (id ⊗₁ id)) ]
      test-three-desc = solveMor! desc₃ asc₃

    ------------------------------------------------------------------------
    -- Rewriting: rule application in context.  A rule is
    -- any C-equation between interpretations of front-end terms — here
    -- abstract hypotheses (commuting endos, an inverse law); the rewrite
    -- layer carries it across and the solver absorbs surrounding structure.

    module Rewrite
      -- the rules: abstract hypotheses about the generators.
      (comm : MC.U [ s'ᴹ ∘ sᴹ ≈ sᴹ ∘ s'ᴹ ])
      (inv  : MC.U [ sᴹ ∘ s'ᴹ ≈ id ])
      where

      -- the rule fires in the RIGHT factor of a tensor (auto-positioned).
      test-rw-right : MC.U [ tᴹ ⊗₁ (s'ᴹ ∘ sᴹ) ≈ tᴹ ⊗₁ (sᴹ ∘ s'ᴹ) ]
      test-rw-right =
        rewriteMorAuto! (t' S.⊗₁ (s'' S.∘ s')) (t' S.⊗₁ (s' S.∘ s''))
                        (s'' S.∘ s') (s' S.∘ s'') comm

      -- the rule fires in the LEFT factor.
      test-rw-left : MC.U [ (s'ᴹ ∘ sᴹ) ⊗₁ tᴹ ≈ (sᴹ ∘ s'ᴹ) ⊗₁ tᴹ ]
      test-rw-left = rewriteMorAuto! ((s'' S.∘ s') S.⊗₁ t') ((s' S.∘ s'') S.⊗₁ t') (s'' S.∘ s') (s' S.∘ s'') comm

      -- the redex is NOT a syntactic subterm (it is split across an
      -- interchange): the manual frame + the solver's reconciliation
      -- absorb the reshaping.
      test-rw-interchange : MC.U [ (s'ᴹ ⊗₁ id) ∘ (sᴹ ⊗₁ tᴹ) ≈ (sᴹ ⊗₁ id) ∘ (s'ᴹ ⊗₁ tᴹ) ]
      test-rw-interchange =
        rewriteMor! ((s'' S.⊗₁ S.id) S.∘ (s' S.⊗₁ t')) ((s' S.⊗₁ S.id) S.∘ (s'' S.⊗₁ t'))
                    (S.λ⇐ S.∘ (S.id S.⊗₁ t')) S.λ⇒
                    (s'' S.∘ s') (s' S.∘ s'') comm

      -- iso-cancellation as a rewrite: the inverse law collapses the
      -- composite to id inside a context.
      test-rw-cancel : MC.U [ tᴹ ⊗₁ (sᴹ ∘ s'ᴹ) ≈ tᴹ ⊗₁ id ]
      test-rw-cancel = rewriteMorAuto! (t' S.⊗₁ (s' S.∘ s'')) (t' S.⊗₁ S.id) (s' S.∘ s'') S.id inv

      -- explicit occurrence index: the redex appears in BOTH tensor factors;
      -- `rewriteMorₙ!` at n = 1 selects the second occurrence (right factor),
      -- leaving the first untouched.
      test-rw-nth : MC.U [ (s'ᴹ ∘ sᴹ) ⊗₁ (s'ᴹ ∘ sᴹ) ≈ (s'ᴹ ∘ sᴹ) ⊗₁ (sᴹ ∘ s'ᴹ) ]
      test-rw-nth =
        rewriteMorₙ! ((s'' S.∘ s') S.⊗₁ (s'' S.∘ s')) ((s'' S.∘ s') S.⊗₁ (s' S.∘ s''))
                     (s'' S.∘ s') (s' S.∘ s'') 1 comm

------------------------------------------------------------------------
-- Sound rejections
--
-- These assert `decide?F … ≡ nothing`, so they require the INTERNAL front-end
-- decision procedure (`Frontend.Decide.decide?F`) rather than a public solver.
-- We wire it by hand from a `FinSig` signature: a two-colour atom alphabet and
-- a Fin-indexed table of two endo generators.
--
--   0 → s  : ⋆ → ⋆          (endo on ⋆)
--   1 → s' : ⋆ → ⋆          (second endo on ⋆)

data Ty : Set where ⋆ • : Ty

instance
  DecEq-Ty : DecEq Ty
  DecEq-Ty .DecEq._≟_ = λ where
    ⋆ ⋆ → yes refl
    ⋆ • → no λ ()
    • ⋆ → no λ ()
    • • → yes refl

open FreeMonoidalHelper Mon Ty using () renaming (ObjTerm to ObjTermᴵ; Var to Varᴵ)

arityT : Fin 2 → ObjTermᴵ × ObjTermᴵ
arityT zero       = Varᴵ ⋆ , Varᴵ ⋆
arityT (suc zero) = Varᴵ ⋆ , Varᴵ ⋆

private module FS = FinSig Mon {Ty} arityT
open FS

open Frontend {Ty} GenS
open Decide rankS

private
  infixr 9 _∘ᴵ_
  _∘ᴵ_ : ∀ {A B C} → S.HomTerm B C → S.HomTerm A B → S.HomTerm A C
  _∘ᴵ_ = S._∘_
  s'  = gen zero
  s'' = gen (suc zero)

module Negative where

  -- distinct endo generators are not identified.
  neg-distinct-endos : decide?F s' s'' ≡ nothing
  neg-distinct-endos = refl

  -- sequential order of two boxes on the SAME wire matters.
  neg-sequential-order : decide?F (s'' ∘ᴵ s') (s' ∘ᴵ s'') ≡ nothing
  neg-sequential-order = refl

  -- diagrams of DIFFERENT length stay apart: one box vs an extra layer.
  -- (The reflected diagrams have unequal layer counts, so the structural
  -- compare rejects on the nil-vs-cons branch of the encoding.)
  neg-extra-layer : decide?F s' (s'' ∘ᴵ s') ≡ nothing
  neg-extra-layer = refl
