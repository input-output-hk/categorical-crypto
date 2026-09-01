# Monoidal coherence solver

Decision procedures for equality of morphisms in a monoidal category, in
the style of Mac Lane's coherence theorem. Two variants are exposed:

  * `Structural` — the bare coherence theorem: any two parallel composites
    of *structural* isomorphisms (associators, unitors, and their inverses)
    are equal. No generating morphisms.
  * `MorSolve` / `MorRewrite` (with `MorAtoms`) — the same, extended with
    opaque *generating morphisms* (`boxes`).  They discharge goals that hold by
    naturality and bifunctoriality / interchange of `_⊗₁_` and `_∘_`, e.g.
    `(s ⊗₁ id) ∘ (id ⊗₁ t) ≈ s ⊗₁ t`; `MorRewrite` additionally fires rules.

This file is the user-facing entry point. It is literate Agda: the
implementation lives in the `Categories.Coherence.Monoidal.*` submodules, and
here each solver is given a short documented *re-definition* — a thin alias
delegating to the implementation — so that jumping to a solver's definition
lands on this documentation. The test suites in
`Categories.Coherence.Monoidal.Test.*` exercise each variant.

```agda
{-# OPTIONS --safe --without-K #-}
module Categories.Coherence.Monoidal where

open import Level using (Level)
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Categories.Category
open import Categories.Category.Monoidal

open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.MacLane
open import Categories.Coherence.Monoidal.Frontend

-- the normalizer's verdict type, for callers of `statusMor` below
open import Categories.Coherence.Monoidal.Normalize public
  using (NormStatus; converged; cycled; exhausted)
```

## `Structural`: coherence of structural isomorphisms

`Structural C vars` instantiates the solver at a target monoidal category
`C`, with `vars` a `Vec` of object atoms. Its term language is the free
monoidal category over those atoms with *no* generating morphisms
(`mor = λ _ _ → ⊥`), so every morphism is a structural iso. `solveM f g`
then discharges `⟦ f ⟧₁ ≈ ⟦ g ⟧₁` for any parallel pair `f g`, the content
of Mac Lane's coherence theorem (`MacLane.CoherenceThm.all-Comm`, via the
normal-form functor). Use it for associator/unitor bookkeeping in a
goal with no generators; the `Test.Frontend` suite's `Coherence` module
exercises it.

```agda
module Structural
  {o ℓ e} (C : MonoidalCategory o ℓ e)
  {n} (vars : Vec (C .MonoidalCategory.Obj) n)
  where

  private module Impl = Solver C vars
  -- the free-monoidal term DSL (Var, _⊗₀_, _⊗₁_, id, ρ⇒, α⇐, ⟦_⟧₁, …)
  open Impl public hiding (solveM)

  -- | Discharge `⟦ f ⟧₁ ≈ ⟦ g ⟧₁` for parallel structural morphisms `f g`.
  solveM = Impl.solveM
```

## `MorRewrite` / `MorSolve`: the monoidal morphism solver

`MorRewrite C vars gens` adds generating morphisms. `vars` are the object atoms and
`gens` is the signature: one `(source , target , interpretation)` triple per
generator — the arities are `ObjTerm`s over the atoms, the interpretation a
`C`-morphism between their images. It exposes the term DSL `S` over those
generators and the solver `solveMor!`, which discharges a goal between
interpretations of front-end terms whose normal forms agree — handling
monoidal coherence together with naturality and the interchange law for
`_⊗₁_`/`_∘_`; see `Categories.GradedKleisli` for a call site. `rewriteMor!`
and friends additionally fire a user-supplied equational rule in a context
(`rewriteMorAuto!` locates it automatically); the `Rewrite` module of
`Categories.Coherence.Monoidal.Test.Frontend` exercises that family.
`statusMor` reports the normalizer's verdict on a front-end term: a failed
`solveMor!` whose sides report `cycled` or `exhausted` hit the rewrite
loop's non-termination on degenerate signatures (a generator with an empty
arity side), not a decided inequality — see `Test.Limitations`.

Warning: `MorRewrite` is slow to `open`. Prefer `MorSolve` if you simply want
to call `solveMor!`.

The reflection macro `solve-mor C` (`Categories.Coherence.Monoidal.Tactic`)
synthesises all of this — the atom vector, the generator signature, and both
front-end terms — from the goal itself; use it when the goal is stated in
`C`'s own vocabulary, and fall back to `MorSolve` where the goal's type is
not determined at the call site (a component of a Σ whose record is still
elaborating, say).

```agda
module MorAtoms
  {o ℓ e} (C : MonoidalCategory o ℓ e)
  {nA} (vars : Vec (C .MonoidalCategory.Obj) nA)
  = FinSetup C vars using (ObjTerm; V; unitᵒ; _⊗ᵒ_)

module MorRewrite
  {o ℓ e} (C : MonoidalCategory o ℓ e)
  {nA} (vars : Vec (C .MonoidalCategory.Obj) nA)
  (let module Impl = FinSetup C vars)
  -- the signature is one vector of triples: source arity, target arity, and
  -- the generator's interpretation (typed by `Impl`'s generator-free `⟦_⟧ₒ`).
  {nG} (gens : Vec (Σ[ st ∈ Impl.ObjTerm × Impl.ObjTerm ]
                      (C .MonoidalCategory.U [ Impl.⟦ proj₁ st ⟧ₒ , Impl.⟦ proj₂ st ⟧ₒ ])) nG)
  (let module ImplS = Impl.Sig (λ i → proj₁ (lookup gens i)))
  where
  open ImplS public using (module S; gen; statusMor)
  open ImplS using (genS)

  private module ImplW = ImplS.WithGen (λ { (genS i) → proj₂ (lookup gens i) })

  -- | Discharge a goal between interpretations of parallel front-end terms.
  solveMor!       = ImplW.solveMor!
  -- | Fire a rule (a `C`-equation between term interpretations) in context.
  rewriteMor!     = ImplW.rewriteMor!
  rewriteMorₙ!    = ImplW.rewriteMorₙ!
  -- | …with the rule's context located automatically.
  rewriteMorAuto! = ImplW.rewriteMorAuto!

module MorSolve
  {o ℓ e} (C : MonoidalCategory o ℓ e)
  {nA} (vars : Vec (C .MonoidalCategory.Obj) nA)
  (let module Impl = FinSetup C vars)
  {nG} (gens : Vec (Σ[ st ∈ Impl.ObjTerm × Impl.ObjTerm ]
                      (C .MonoidalCategory.U [ Impl.⟦ proj₁ st ⟧ₒ , Impl.⟦ proj₂ st ⟧ₒ ])) nG)
  = MorRewrite C vars gens using (solveMor!; gen; module S; statusMor)
```

### Example

A worked example over an arbitrary monoidal category `C`, with two object atoms
`A , B` and two generators `s : A → A`, `t : B → B`. The solver takes the whole
signature as a single vector of triples — each
`(source , target , interpretation)` — and exposes in one open the term
DSL `S`, the generators `gen i`, and the solver `solveMor!`. (`MorAtoms`
supplies just the atom term `V`, so the arities can be written.) Each goal is
then stated in `C`'s own vocabulary; the `solveMor!` arguments are the two
front-end terms whose normal forms it compares.

```agda
module Morphism-example {o ℓ e} (C : MonoidalCategory o ℓ e) where

  private module MC = MonoidalCategory C
  open MC using (_⊗₁_; _∘_; id; unitorʳ)

  module _
    (A B : MC.Obj)
    (s : C .MonoidalCategory.U [ A , A ])
    (t : C .MonoidalCategory.U [ B , B ])
    (s∘s≈id : C .MonoidalCategory.U [ s ∘ s ≈ id ])
    where

    vars = A ∷ B ∷ []
    open MorAtoms C vars
    open MorRewrite C vars
         ( ((V zero , V zero)             , s)            -- gen 0 : A → A ↦ s
         ∷ ((V (suc zero) , V (suc zero)) , t)            -- gen 1 : B → B ↦ t
         ∷ [] )

    private
      s' = gen zero
      t' = gen (suc zero)

    -- interchange: disjoint boxes fire in either order to the same morphism.
    interchange : C .MonoidalCategory.U [ (s ⊗₁ id) ∘ (id ⊗₁ t) ≈ s ⊗₁ t ]
    interchange = solveMor! ((s' S.⊗₁ S.id) S.∘ (S.id S.⊗₁ t')) (s' S.⊗₁ t')

    -- right-unitor naturality at the generator `s`.
    ρ-naturality : C .MonoidalCategory.U [ unitorʳ.from ∘ (s ⊗₁ id) ≈ s ∘ unitorʳ.from ]
    ρ-naturality = solveMor! (S.ρ⇒ S.∘ (s' S.⊗₁ S.id)) (s' S.∘ S.ρ⇒)

    -- a rule applied in context: `rewriteMorAuto!` locates the `s ∘ s` redex,
    -- and the solver absorbs the surrounding `t ⊗₁ -`.
    cancel : C .MonoidalCategory.U [ t ⊗₁ (s ∘ s) ≈ t ⊗₁ id ]
    cancel =
      rewriteMorAuto! (t' S.⊗₁ (s' S.∘ s')) (t' S.⊗₁ S.id) (s' S.∘ s') S.id s∘s≈id
```

## Scope and limitations

Both variants target monoidal categories only.

The solver family is sound but not complete: it may return `nothing` on a
true equation. The full list of what it does *not* decide — the ambiguous
rank convention, opaque generators, and the meta-properties
(incompleteness, no confluence claim) — is catalogued, with
machine-checked witnesses, in
`Categories.Coherence.Monoidal.Test.Limitations`.
```
