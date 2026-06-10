{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- The `≈M → ≅ᴴ` BRIDGE solver: `solveH!ᴹ`, the no-search drop-in for `solveH!`
-- whose witnessing iso is produced by the *matrix-equivalence* bridge
-- `findIsoᴹ` (Solver.MatrixBridgeM) — the cheap-per-use-decision variant of
-- `findIsoᴮ`.
--
-- Identical telescope to `InterpretBridge.Solverᴮ` (same `morCode` extra
-- parameter); the ONLY difference is `findIsoᴹ` (decide `canonMat H ≡ canonMat
-- J`, then the OPAQUE `matEquiv→hgIso`) replaces `findIsoᴮ` (`decBijLaws` +
-- `decCanonMatch`).  Per the design (`MatrixBridgeM`), the per-use decision is
-- the flat matrix compare and never touches the (opaque) faithfulness proof.
--
-- `soundness-full-wired` then turns the iso into a syntactic `≈Term`, and
-- `freeFunctor` transports it into the target.  `--without-K` (not `--safe`):
-- the matrix bridge is not `--safe`.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.InterpretBridgeM (sig-dec : APROPSignatureDec) where

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
open import Categories.APROP.Hypergraph.Solver.MatrixBridgeM sig-dec using (findIsoᴹ)
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
-- The per-hypergraph edge code (identical to `InterpretBridge.ecodeOf`).

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
-- The matrix-bridge solver.  Same telescope as `InterpretBridge.Solverᴮ`.

module Solverᴹ {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
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
  solveHᴹ
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveHᴹ f g iso =
    Functor.F-resp-≈ freeFunctor (soundness-full-wired {f = f} {g = g} iso)

  -- The matrix-bridge drop-in.  The witnessing iso is located by `findIsoᴹ`
  -- (decide `canonMat ⟪f⟫ ≡ canonMat ⟪g⟫`, then the OPAQUE faithfulness); the
  -- implicit `T (is-just …)` is discharged automatically exactly when `findIsoᴹ`
  -- reduces to `just _` at typecheck time.
  solveH!ᴹ
    : ∀ {A B} (f g : HomTerm A B)
    → {_ : T (is-just (findIsoᴹ ⟪ f ⟫ ⟪ g ⟫ (ecodeOf morCode ⟪ f ⟫) (ecodeOf morCode ⟪ g ⟫)))}
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH!ᴹ f g {pf} =
    solveHᴹ f g
      (fromWitness! (findIsoᴹ ⟪ f ⟫ ⟪ g ⟫ (ecodeOf morCode ⟪ f ⟫) (ecodeOf morCode ⟪ g ⟫)) pf)
