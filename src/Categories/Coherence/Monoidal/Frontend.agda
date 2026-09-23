{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The solver front-end: from wire-list diagrams to ObjTerm-arity generators.
--
-- The reflect/normalize/compare pipeline lives in the *wire-list* world; this
-- module lifts it to arbitrary-object-term generators `GenF`, so a target-
-- category goal like `(id ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ≈ sᴹ ⊗₁ tᴹ` reads directly.
-- `flatten : ObjTerm → List X` re-indexes the generators to the wire level,
-- and the soundness bridge is proven once at the free level:
--
--     bridgeF : inj (embed (reflectF t)) ∘ flat⇒ ≈ flat⇒ ∘ t
--
-- The shared machinery lives in `Frontend.Core`; this file assembles the
-- decision procedure and the call-site wrapper `FinSetup`.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Frontend where

import Data.Maybe
open import categorical-crypto.Prelude
  hiding (_∘_; id; map; merge; zero; suc; lookup; [_]; [_,_])

open import Data.Fin
open import Data.Nat using () renaming (suc to nsuc)
open import Data.Vec

open import Categories.Category
open import Categories.Category.Monoidal

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend.Core

open import Categories.Coherence.Monoidal.Normalize
open import Categories.Coherence.Monoidal.Reflect

module Frontend
  {X : Set} ⦃ _ : DecEq X ⦄
  (let open FreeMonoidalHelper Mon X using (ObjTerm; flatten))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  private module Core = FCore {X = X} GenF
  open Core

  -- the reflection / soundness-bridge layer at the wire-level generators
  -- `MorW`; `F` is the front-end free category.
  private module FB = FBridge GenF
  open FB

  open DiagramI MorW
  open ReflectI MorW

  ------------------------------------------------------------------------
  -- The decision procedure
  ------------------------------------------------------------------------

  module Decide
    ⦃ _ : DecEq GenΣ ⦄
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous pairs
    where

    private
      open NormalizeI MorW
      open SortD
      open Steps PrimSwap
      open FreeMonoidalHelper.Mor Mon X mor
      module DC = DecideCore MorW

      rankW : ∀ {a b} → MorW a b → ℕ
      rankW = Core.rankMorW rank

      -- one interchange swap at the first applicable position, as an `_⤳D_`
      -- rewrite witness.
      step? : ∀ {n m} (d : Diag n m) → Maybe (Σ[ d' ∈ Diag n m ] (d ⤳D d'))
      step? = stepWith (interchangeGo rankW)

      open DC.SCmp.Decide using (_≟Diag_)

      -- a fuel-bounded bubble sort, stopping at the first revisited state.
      norm = normDetectSoundˢ prim-swap-soundˢ _≟Diag_ step? (λ k → nsuc (k * k))

    open DC.Decide norm using () renaming (decideW to decide?W; statusW to status?W)

    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r = Data.Maybe.map solveF (decide?W (reflectF l) (reflectF r))

    -- Diagnostic mirror of `decide?F`, per side: `converged` means the
    -- compared form is a genuine normal form; `cycled`/`exhausted` mean
    -- the normalizer did not terminate on this input.
    statusF : ∀ {Y Z} (t : F.HomTerm Y Z) → NormStatus
    statusF t = status?W (reflectF t)

--------------------------------------------------------------------------------
-- `FinSetup`: the call-site convenience wrapper.  From a target monoidal
-- category `C`, a `Vec` of object atoms, and a Fin-indexed `arity` table, it
-- assembles the signature, decidable equalities and rank, exposing the term
-- language `S`, the embedding `gen`, the object interpretation `⟦_⟧ₒ` and
-- `solveMor!`.
--------------------------------------------------------------------------------

module FinSetup
  {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  {nA : ℕ} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  where

  -- the object language over the atom indices, with constructors renamed so
  -- they coexist with a caller's own free-category vocabulary.
  open FreeMonoidalHelper Mon (Fin nA) public using (ObjTerm) renaming (Var to V; unit to unitᵒ; _⊗₀_ to _⊗ᵒ_)

  -- the object interpretation `ObjTerm → C.Obj`, independent of any generator
  -- signature, so it can type a generator's interpretation before the
  -- signature is fixed.
  open FreeObjInterp Mon (Fin nA) (fromMC C noSymmetric) (lookup vars) public using () renaming (⟦_⟧₀ to ⟦_⟧ₒ)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    open FinSig {X = Fin nA} arity public using (GenS; genS; module S; gen; GenΣ; DecEq-Gen; rankS)

    -- build the front-end's decision procedure at this signature, then run
    -- the transport pipeline at the target.
    open Frontend {Fin nA} GenS
    private module D = Decide rankS
    open D

    open FSolve GenS decide?F public using (solveTerm!; module Into)
    open Into C (lookup vars) public

    statusMor = D.statusF
