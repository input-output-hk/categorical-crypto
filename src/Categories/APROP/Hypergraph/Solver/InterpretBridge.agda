{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- The BRIDGE-based solver: `solveH!ᴮ`, the no-search drop-in for `solveH!`
-- whose witnessing iso is produced by the canonical-form hypergraph↔matrix
-- bridge `findIsoᴮ` (Solver.MatrixBridge) instead of the backtracking
-- `findIso` (Solver.FindIso).
--
-- This is a SEPARATE module (not part of `Interpret`) for one reason only:
-- `Interpret`/`InterpretTests` are `--safe`, but `MatrixBridge` brings in the
-- matrix world and is `--without-K` (not `--safe`).  Importing the bridge into
-- a `--safe` module is rejected, so the bridge path lives here, `--without-K`.
-- The iso path itself is POSTULATE-FREE: `findIsoᴮ` assembles every `_≅ᴴ_`
-- field via `matIso→hgIso` from purely-decided witnesses (count equalities +
-- `decBijLaws` + `decCanonMatch`); `soundness-full-wired` then turns the iso
-- into a syntactic `≈Term`, and `freeFunctor` transports it into the target.
--
-- The only EXTRA datum the bridge needs over `Solver` is a per-generator code
-- `morCode : ∀ {x y} → mor x y → ℕ` (folded into the canonical tie-break — see
-- MatrixBridge §2).  A FAITHFUL `morCode` (distinct generators ↦ distinct ℕ)
-- canonicalises all monogamous inputs except genuine same-generator
-- automorphisms; a `const 0` code is still SOUND but only complete when no two
-- distinct generators structurally tie.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.InterpretBridge (sig-dec : APROPSignatureDec) where

open import Categories.APROP using (module APROP)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.FreeMonoidal
open import Categories.Functor using (Functor)

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.MatrixBridge sig-dec using (findIsoᴮ)
open import Categories.APROP.Hypergraph.Solver.Verify sig-dec using (view; FlatView)
open import Categories.APROP.Hypergraph.SoundnessFullWired sig-dec
  using (soundness-full-wired)

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Bool.Base using (T)

private
  fromWitness! : ∀ {a} {A : Set a} (m : Maybe A) → T (is-just m) → A
  fromWitness! (just x) _ = x

--------------------------------------------------------------------------------
-- The per-hypergraph edge code, read off each edge's `FlatGen` label via the
-- `FlatView` (mirrors `MatrixBridgeDemo.ecodeOf` and `Verify`'s extraction).

ecodeOf : (morCode : ∀ {x y} → mor x y → ℕ)
        → (G : Hypergraph FlatGen) → Fin (Hypergraph.nE G) → ℕ
ecodeOf morCode G e = morCode (FlatView.f (view (Hypergraph.elab G e)))

--------------------------------------------------------------------------------
-- The object interpretation, exposed exactly as in `Interpret`.

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
-- The bridge solver.  Same telescope as `Interpret.Solver`, plus the extra
-- `morCode` parameter feeding the canonical tie-break.

module Solverᴮ {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
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
  (morCode : ∀ {x y} → mor x y → ℕ)
  where

  ffd : FreeFunctorData asFreeMonoidalData {o} {ℓ} {e}
  ffd = record { ⟦v⟧ = ⟦v⟧ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀ ; ⟦_⟧ᵖ₁ = ⟦_⟧ᵖ₁ }

  open FreeFunctor ffd public using (⟦_⟧₁; freeFunctor)

  module Tgt = ⟦_⟧ᵥ.Cat ⟦v⟧

  -- Same `solveH` as `Interpret.Solver`: an explicit iso → target equation.
  solveHᴮ
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveHᴮ f g iso =
    Functor.F-resp-≈ freeFunctor (soundness-full-wired {f = f} {g = g} iso)

  -- The bridge drop-in.  The witnessing iso is located by `findIsoᴮ` (canonical
  -- form, no search) at the two hypergraphs' edge codes; the implicit
  -- `T (is-just …)` is discharged automatically exactly when `findIsoᴮ`
  -- reduces to `just _` at typecheck time.
  solveH!ᴮ
    : ∀ {A B} (f g : HomTerm A B)
    → {_ : T (is-just (findIsoᴮ ⟪ f ⟫ ⟪ g ⟫ (ecodeOf morCode ⟪ f ⟫) (ecodeOf morCode ⟪ g ⟫)))}
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH!ᴮ f g {pf} =
    solveHᴮ f g
      (fromWitness! (findIsoᴮ ⟪ f ⟫ ⟪ g ⟫ (ecodeOf morCode ⟪ f ⟫) (ecodeOf morCode ⟪ g ⟫)) pf)
