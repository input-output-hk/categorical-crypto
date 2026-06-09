{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Test suite for the solver front-end (`Categories.SolverFrontend.solveMor!`).
--
-- Organised by capability, with the solver's LIMITATIONS exhibited as
-- machine-checked `decide?F … ≡ nothing` facts (so the boundary of the
-- decision procedure is itself part of the checked test suite).
--
--   * `Coherence`     — pure MacLane coherence (unitors, associator,
--                       triangle, pentagon) decides: both sides reflect to
--                       the same (usually empty) diagram.
--   * `Naturality`    — unitor/associator naturality THROUGH box generators.
--   * `Functorial`    — id/∘ laws and in-order ⊗-functoriality.
--   * `Interchange`   — disjoint boxes in either firing order, including
--                       multi-wire boxes (μ), empty-domain boxes (η) and
--                       scalars (u : unit → unit); the out-of-order variants
--                       exercise a genuine machine-fired interchange swap.
--   * `Negative`      — sound rejections (distinct generators, dependent /
--                       overlapping boxes, sequential order on a wire).
--   * `Limitations`   — TRUE equations the solver does NOT decide, each
--                       pinned by `≡ nothing`; see the catalogue below.
--   * `Target`        — C-level showcase: `solveMor!` one-liners whose
--                       statements read in the target's own vocabulary.
--
-- LIMITATION CATALOGUE (precise statements; L2/L3 machine-checked below):
--
--   L1 (soundness only).  `decide?F` is sound but NOT complete: every `just`
--       carries a real `_≈Term_` proof, but `nothing` does not refute the
--       equation.  L2/L3 are true equations answered `nothing`.
--
--   L2 (head-only normalization).  The interchange normalizer `norm1` fires
--       at most ONE bubble swap, and only on the HEAD pair (the first two
--       fired layers).  A true equation whose diagrams differ by an
--       inversion deeper in the layer list is not decided —
--       `lim-non-head-swap` pins the ⊗-functoriality composite
--       `(s' ∘ s) ⊗ t ≈ (s' ⊗ id) ∘ (s ⊗ t)`, whose right side has its
--       inversion at layers 2-3.
--
--   L3 (single swap).  Diagrams needing ≥ 2 swaps are not decided —
--       `lim-three-desc` pins three independent boxes fired in fully
--       descending order against ascending order (needs 3 swaps).
--       (Generic multi-step recursion is blocked because the swapped tail
--       sits behind `substDiagU`; a re-representation of `DiagU` with
--       equality-field wiring is the known follow-up.)
--
--   L4 (monoidal only).  The front-end is at `Variant` `Mon`: no braiding,
--       so symmetric/braided goals (anything mentioning σ) are not even
--       expressible in the term language.
--
--   L5 (concrete signatures only).  The decision computes by evaluation:
--       it requires a concrete atom set with computing `DecidableEquality`
--       and concrete generator arities.  Over ABSTRACT atoms the
--       `++-identityʳ`/`++-assoc` casts inside `reflectF` do not reduce, so
--       `IsJust (decide?F …)` does not normalize and the implicit hit of
--       `solveTerm!`/`solveMor!` cannot be auto-discharged.
--
--   L6 (syntactic generators).  Generator equality is the supplied
--       syntactic `≟G`; no generator-specific equations (naturality of a
--       concrete box, Frobenius laws, …) are known to the solver — see
--       `neg-distinct-endos`/`neg-sequential-order`.  Such equations belong
--       to a rewriting layer on top (cf. `rewriteH!` in the hypergraph
--       solver), not to this coherence+interchange decision procedure.
--
--   L7 (no canonicity claim).  `norm1 ∘ reflect` is not claimed to be a
--       canonical form; the test suite documents which equation SHAPES
--       decide, not a completeness theorem for some fragment.
--
-- Hole-free, postulate-free, --safe.
--------------------------------------------------------------------------------

module Categories.SolverFrontendTests where

open import Level using (Level)

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.FreeMonoidal
open import Categories.SolverFrontend using (module Frontend)

------------------------------------------------------------------------
-- Wire colours and the generator signature (ObjTerm arities, Fin-indexed).
--
--   0 → μ  : ⋆ ⊗ ⋆ → ⋆     (multi-wire input)
--   1 → η  : unit  → ⋆      (empty domain)
--   2 → s  : ⋆ → ⋆          (endo on ⋆)
--   3 → s' : ⋆ → ⋆          (second endo on ⋆)
--   4 → t  : • → •          (endo on •)
--   5 → u  : unit → unit    (scalar)

data Ty : Set where ⋆ • : Ty

_≟Ty_ : DecidableEquality Ty
⋆ ≟Ty ⋆ = yes refl
⋆ ≟Ty • = no λ ()
• ≟Ty ⋆ = no λ ()
• ≟Ty • = yes refl

open FreeMonoidalHelper Mon Ty using (ObjTerm; unit; _⊗₀_; Var)

arityT : Fin 6 → ObjTerm × ObjTerm
arityT zero                            = Var ⋆ ⊗₀ Var ⋆ , Var ⋆
arityT (suc zero)                      = unit , Var ⋆
arityT (suc (suc zero))                = Var ⋆ , Var ⋆
arityT (suc (suc (suc zero)))          = Var ⋆ , Var ⋆
arityT (suc (suc (suc (suc zero))))    = Var • , Var •
arityT (suc (suc (suc (suc (suc _))))) = unit , unit

data GenT : ObjTerm → ObjTerm → Set where
  genT : (i : Fin 6) → GenT (proj₁ (arityT i)) (proj₂ (arityT i))

------------------------------------------------------------------------
-- The front-end term language and the solver instance.

private module S = FreeMonoidalHelper.Mor Mon Ty GenT

open Frontend {Ty} GenT

_≟G_ : DecidableEquality GenΣ
(_ , _ , genT i) ≟G (_ , _ , genT j) with i ≟F j
... | yes refl = yes refl
... | no ¬p    = no λ where refl → ¬p refl

open Decide _≟Ty_ _≟G_

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
  μ'  = S.var (genT zero)
  η'  = S.var (genT (suc zero))
  s'  = S.var (genT (suc (suc zero)))
  s'' = S.var (genT (suc (suc (suc zero))))
  t'  = S.var (genT (suc (suc (suc (suc zero)))))
  u'  = S.var (genT (suc (suc (suc (suc (suc zero))))))

------------------------------------------------------------------------
-- Coherence: pure MacLane equations decide (both sides reflect to the
-- same structural-free diagram; all index casts compute to refl on the
-- concrete signature).

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
-- sides exercise a genuine machine-fired swap inside `norm1`.

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

------------------------------------------------------------------------
-- Sound rejections: the solver answers `nothing` on non-equations.

module Negative where

  -- distinct endo generators are not identified.
  neg-distinct-endos : decide?F s' s'' ≡ nothing
  neg-distinct-endos = refl

  -- sequential order of two boxes on the SAME wire matters.
  neg-sequential-order : decide?F (s'' ∘' s') (s' ∘' s'') ≡ nothing
  neg-sequential-order = refl

  -- generator naturality is NOT known to the solver (L6): s' past μ.
  neg-generator-naturality
    : decide?F (s' ∘' μ') (μ' ∘' (s' ⊗' id')) ≡ nothing
  neg-generator-naturality = refl

------------------------------------------------------------------------
-- LIMITATIONS, machine-checked: TRUE equations answered `nothing`.

module Limitations where

  -- L2: the inversion sits at layers 2-3, not at the head; `norm1` only
  -- inspects the head pair.  (True by bifunctoriality.)
  lim-non-head-swap
    : decide?F ((s'' ∘' s') ⊗' t') ((s'' ⊗' id') ∘' (s' ⊗' t')) ≡ nothing
  lim-non-head-swap = refl

  -- L3: three independent boxes fired in fully descending order vs
  -- ascending order need 3 swaps; `norm1` fires one.
  private
    W₃ = Var ⋆ ⊗₀ (Var ⋆ ⊗₀ Var ⋆)
    desc : S.HomTerm W₃ W₃
    desc = (s' ⊗' (id' ⊗' id'))
        ∘' (id' ⊗' (s' ⊗' id'))
        ∘' (id' ⊗' (id' ⊗' s'))
    asc : S.HomTerm W₃ W₃
    asc = (id' ⊗' (id' ⊗' s'))
       ∘' (id' ⊗' (s' ⊗' id'))
       ∘' (s' ⊗' (id' ⊗' id'))

  lim-three-desc : decide?F desc asc ≡ nothing
  lim-three-desc = refl

------------------------------------------------------------------------
-- C-level showcase: statements read in the target's own vocabulary.

module Target {o ℓ e : Level} (C : MonoidalCategory o ℓ e) where

  private module MC = MonoidalCategory C

  module At
    (A B : MC.Obj)
    (μᴹ  : C .MonoidalCategory.U [ MC._⊗₀_ A A , A ])
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
    open WithGen (λ { (genT zero)                            → μᴹ
                    ; (genT (suc zero))                      → ηᴹ
                    ; (genT (suc (suc zero)))                → sᴹ
                    ; (genT (suc (suc (suc zero))))          → s'ᴹ
                    ; (genT (suc (suc (suc (suc zero)))))    → tᴹ
                    ; (genT (suc (suc (suc (suc (suc _)))))) → uᴹ })

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
