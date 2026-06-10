{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Solving symmetric-monoidal equations in an *arbitrary* target SMC.
--
-- `solveM` (Categories.MonoidalCoherence) discharges a *monoidal* coherence
-- equation in any monoidal category by proving it in the free monoidal
-- category and transporting it along the interpreting functor.  This module
-- is the symmetric / string-diagram analogue.
--
-- Given a signature `(X , mor)` of atoms and generators, the free symmetric
-- monoidal category `FreeMonoidal` is the syntax.  An equation `f ≈ g`
-- between two such terms is witnessed by a hypergraph isomorphism
-- `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` (typically produced by `findIso`), which
-- `soundness-full-wired` turns into a genuine `f ≈Term g`.  We then transport
-- that equation into the target SMC `C` along the free functor `freeFunctor`
-- that interprets atoms via `⟦_⟧ᵖ₀` and generators via `⟦_⟧ᵖ₁`.
--
-- The interface mirrors `solveM`: `solveH` takes the two terms `f g`
-- explicitly (so the goal need not pin them down through the non-injective
-- `⟦_⟧₁`), plus the hypergraph isomorphism.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Interpret (sig-dec : APROPSignatureDec) where

open import Categories.APROP using (module APROP)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.FreeMonoidal
open import Categories.Functor using (Functor)

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso sig-dec using (findIso)
open import Categories.APROP.Hypergraph.Solver.FindIsoTab sig-dec using (findIsoᵀ)
open import Categories.APROP.Hypergraph.Solver.Split sig-dec using (solveSplitR?)
open import Categories.APROP.Hypergraph.SoundnessFullWired sig-dec
  using (soundness-full-wired)

open import Level using (Level)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Bool.Base using (T)

private
  -- Extract the value of a `Maybe` from a proof (`T (is-just _)`) that it is
  -- `just`.  Unlike `from-just`, the proof is a separate argument, so this
  -- can be applied to an *abstract* `Maybe` and still type-check; the proof is
  -- the unit value `tt` (filled implicitly) whenever the `Maybe` is concretely
  -- `just`, and uninhabitable when it is `nothing`.
  fromWitness! : ∀ {a} {A : Set a} (m : Maybe A) → T (is-just m) → A
  fromWitness! (just x) _ = x

--------------------------------------------------------------------------------
-- The object interpretation `⟦_⟧₀ : ObjTerm → C.Obj`, which depends only on
-- the atom interpretation `⟦_⟧ᵖ₀`.  Exposed separately from `Solver` so that
-- callers can *name the type* of a generator-interpretation table —
-- `(i : Fin n) → ⟦ dom i ⟧₀ C.⇒ ⟦ cod i ⟧₀` — before committing the table
-- itself (which `Solver` needs as its `⟦_⟧ᵖ₁` argument).

module ObjInterp {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (let ⟦v⟧ : ⟦ Symm ⟧ᵥ {o} {ℓ} {e}
       ⟦v⟧ = record
         { C           = C.U
         ; Monoidal-C  = C.monoidal
         ; Symmetric-C = λ ⦃ _ ⦄ → C.symmetric
         })
  (⟦_⟧ᵖ₀ : X → C.Obj)
  where
  open FreeFunctorHelper asFreeMonoidalData ⟦v⟧ using (module Go)
  open Go ⟦_⟧ᵖ₀ public using (⟦_⟧₀)

--------------------------------------------------------------------------------
-- The solver, parameterised by a target SMC `C` and an interpretation of the
-- signature: `⟦_⟧ᵖ₀` on atoms, `⟦_⟧ᵖ₁` on generators.  The `let`-bindings in
-- the telescope assemble the `⟦ Symm ⟧ᵥ` package and bring the object
-- interpretation `⟦_⟧₀` into scope so the type of `⟦_⟧ᵖ₁` can mention it.

module Solver {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (let ⟦v⟧ : ⟦ Symm ⟧ᵥ {o} {ℓ} {e}
       ⟦v⟧ = record
         { C           = C.U
         ; Monoidal-C  = C.monoidal
         ; Symmetric-C = λ ⦃ _ ⦄ → C.symmetric
         })
  (⟦_⟧ᵖ₀ : X → C.Obj)
  (let open FreeFunctorHelper asFreeMonoidalData ⟦v⟧ using (module Go))
  (let open Go ⟦_⟧ᵖ₀ using (⟦_⟧₀))
  (⟦_⟧ᵖ₁ : ∀ {x y} → mor x y → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀)
  where

  ffd : FreeFunctorData asFreeMonoidalData {o} {ℓ} {e}
  ffd = record { ⟦v⟧ = ⟦v⟧ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀ ; ⟦_⟧ᵖ₁ = ⟦_⟧ᵖ₁ }

  open FreeFunctor ffd public using (⟦_⟧₁; freeFunctor)

  -- The target category, with its monoidal/symmetric shorthands (`_∘_`, `id`,
  -- `_⊗₁_`, `λ⇒`, `α⇒`, `σ`, …).  `⟦_⟧₁` is defined compositionally into this
  -- module, so `⟦ t ⟧₁` is *definitionally* the corresponding `Tgt`-expression
  -- — letting callers state goals as equations in `C` directly, with no
  -- mention of `⟦_⟧₁`.
  module Tgt = ⟦_⟧ᵥ.Cat ⟦v⟧

  -- Discharge a free-SMC equation `f ≈ g` — given as a hypergraph iso
  -- `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` between the translations — into the target category `C`.
  solveH
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH f g iso =
    Functor.F-resp-≈ freeFunctor (soundness-full-wired {f = f} {g = g} iso)

  -- Same, but the witnessing iso is located internally by `findIso`, so the
  -- two free-SMC terms `f g` need only be written once.  The implicit
  -- `T (is-just …)` argument is discharged automatically (it reduces to the
  -- unit type `⊤`) exactly when `findIso ⟪ f ⟫ ⟪ g ⟫` succeeds at type-check
  -- time; if the search fails it reduces to `⊥` and the call is rejected.
  solveH!
    : ∀ {A B} (f g : HomTerm A B)
    → {_ : T (is-just (findIso ⟪ f ⟫ ⟪ g ⟫))}
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH! f g {pf} = solveH f g (fromWitness! (findIso ⟪ f ⟫ ⟪ g ⟫) pf)

  -- Same, but the iso search runs on the TABULATED translations
  -- (`findIsoᵀ = findIso ∘ tabH`, transported back along `tab-≅ᴴ`):
  -- the hypergraph fields become shared, memoizing vectors, so the
  -- search does not re-walk the `hComposeP` tower at every field access.
  -- Measured 2.4–4.2× faster than `solveH!` on chains gᴺ (N = 8–32),
  -- the gap growing with size.
  solveH!ᵀ
    : ∀ {A B} (f g : HomTerm A B)
    → {_ : T (is-just (findIsoᵀ ⟪ f ⟫ ⟪ g ⟫))}
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH!ᵀ f g {pf} = solveH f g (fromWitness! (findIsoᵀ ⟪ f ⟫ ⟪ g ⟫) pf)

  -- Same, but the witness is produced by the equation-splitting front-end
  -- `solveSplitR?`: both sides are reassociated to right-nested `∘`-chains,
  -- shared syntactic structure is peeled by `refl`/congruence, and only the
  -- differing windows go to the hypergraph solver (`findIsoᵀ`), with the
  -- whole-term solve as fallback — so anything `solveH!ᵀ` solves, this
  -- solves too.  `solveSplitR?` already yields a `f ≈Term g`, so it is
  -- transported by `F-resp-≈` directly (no `solveH`).
  solveH!ˢ
    : ∀ {A B} (f g : HomTerm A B)
    → {_ : T (is-just (solveSplitR? f g))}
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH!ˢ f g {pf} =
    Functor.F-resp-≈ freeFunctor (fromWitness! (solveSplitR? f g) pf)
