{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The solver FRONT-END: from wire-list diagrams to ObjTerm-arity generators.
--
-- The reflect/normalize/compare pipeline (Reflect / Normalize /
-- Compare) lives in the *wire-list* world, where the tensor of flat
-- terms needs a merge/split conjugation that leaks into every statement.  This
-- module lifts that to ARBITRARY-object-term generators `GenF`, so a clean
-- target-category goal like `(id ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ≈ sᴹ ⊗₁ tᴹ` reads
-- directly, mirroring the hypergraph (SMC) solver's setup layer.
--
-- `flatten : ObjTerm → List X` (with `flatten (Y ⊗₀ Z) ≡ flatten Y ++
-- flatten Z` definitionally) re-indexes the generators to the wire level, and
-- the soundness bridge is proven ONCE at the free level:
--
--     bridgeF : inj (embed (reflectF t)) ∘ flat⇒ ≈ flat⇒ ∘ t
--
-- `Decide.solveTerm!` packages reflect → normalize → compare → bridge into a
-- decision procedure for the front-end `_≈Term_`; `Decide.Into.WithGen.solveMor!`
-- transports a hit into an arbitrary target monoidal category along the free
-- functor — definitionally, so the equation reads in the target's vocabulary.
--
-- The shared machinery (flatten/MorW, flat⇒/flat⇐, inj,
-- reflectF, bridgeF, solveF) lives in `Categories.Coherence.Monoidal.Frontend.Core`
-- (`FCore`/`FBridge`), instantiated here at (Mon, MorW, ⟦box⟧).  This file
-- supplies the Mon-specific clauses (`injBox`, `reflectVarM`, vacuous σ on the
-- empty `Symm ≤ Mon`).
--
-- What decides is machine-checked in
-- `Categories.Coherence.Monoidal.Test.Frontend`, whose `Negative`/`Limitations`
-- suites pin the two boundaries expressible as `decide?F … ≡ nothing`: the
-- syntactic-generator limitation (L5, `neg-generator-naturality`) and the
-- non-injective-rank limitation (L2, `lim-equal-rank`).  The remaining
-- limitations are meta-properties, not single equations: soundness-without-
-- completeness (L1), monoidal-only / no braiding (L3), concrete-signatures-only
-- (L4), and no canonicity claim for `norm ∘ reflect` (L6).
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Frontend where

import Data.Maybe
open import categorical-crypto.Prelude
  hiding (_∘_; id; map; merge; zero; suc; lookup; [_]; [_,_])

open import Data.Fin
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Nat using () renaming (suc to nsuc)
open import Data.Vec

open import Categories.Category
open import Categories.Category.Monoidal

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal using (Mon; module FreeMonoidalHelper; noSymmetric)
open import Categories.Coherence.Monoidal.Frontend.Core
  using (FreeSig; module FCore; module FBridge; module FSolve; module FinSig; module FinSetupCore)
open import Categories.Coherence.Monoidal.Normalize
open import Categories.Coherence.Monoidal.Reflect

module Frontend
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (let open FreeMonoidalHelper Mon X using (ObjTerm))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  ------------------------------------------------------------------------
  -- The engine-free shared layer: flatten, MorW, GenΣ
  ------------------------------------------------------------------------

  private module Core = FCore Mon {X = X} GenF
  open Core

  open Untyped Mon {X} MorW
  open Reflect Mon {X} _≟X_ MorW

  -- the wire-level engine instance (MorW + ⟦box⟧), shared by FBridge/DecideCore.
  private
    EW : WireEngine Mon {X}
    EW = record { Mor = MorW ; ⟦box⟧ = ⟦box⟧ }

    -- the generator signature, shared by the engine modules below; `F` is its
    -- free category (HomTerm over GenF).
    sig : FreeSig Mon {X}
    sig = record { _≟X_ = _≟X_ ; GenF = GenF }
  open FreeSig sig using (module F)

  ------------------------------------------------------------------------
  -- The engine-generic shared layer, at (Mon, MorW, ⟦box⟧)
  ------------------------------------------------------------------------

  private module FB = FBridge Mon _≟X_ GenF EW
  open FB

  ------------------------------------------------------------------------
  -- The Mon-specific clauses: a box is conjugated by the canonical iso;
  -- the σ clauses are vacuous (`Symm ≤ Mon` is empty)
  ------------------------------------------------------------------------

  private
    injBox : ∀ {a b} → MorW a b → F.HomTerm (wires a) (wires b)
    injBox (mk {Y} {Z} g) = flat⇒ Z F.∘ (F.var g F.∘ flat⇐ Y)

    reflectVarM : ∀ {Y Z} → GenF Y Z → WTerm (flatten Y) (flatten Z)
    reflectVarM g = boxʷ (mk g)

  private module FBI = FB.WithInj injBox reflectVarM (λ where ⦃ () ⦄)
  open FBI

  private module FBB = FBI.Bridge (λ _ → refl) (λ where ⦃ () ⦄)
  open FBB

  ------------------------------------------------------------------------
  -- The decision procedure
  ------------------------------------------------------------------------

  module Decide
    (_≟G_ : DecidableEquality GenΣ)
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous pairs
    where

    private
      _≟W_ = Core.decMorW _≟G_

      open Normalize Mon {X} _≟X_ MorW
      open SortD
      open Steps PrimSwap
      open FreeMonoidalHelper.Mor Mon X mor using (_≈Term_)
      module DC = DecideCore EW _≟X_

      rankW : ∀ {a b} → MorW a b → ℕ
      rankW = Core.rankMorW rank

      -- one interchange swap at the FIRST applicable position, as an `_≈D_`
      -- rewrite witness.
      step? : ∀ {n m} (d : DiagU n m) → Maybe (Σ[ d' ∈ DiagU n m ] (d ≈D d'))
      step? = stepWith (interchangeGo rankW)

      -- a fuel-bounded bubble sort emitting an `_≈D_` trace, discharged to a
      -- semantic witness by the shared `normSound` (the worst-case budget is
      -- ≥ #inversions).
      norm : ∀ {n m} (d : DiagU n m) → Σ[ d' ∈ DiagU n m ] (⟦ d ⟧ ≈Term ⟦ d' ⟧)
      norm = normSound prim-swap-sound step? (λ k → nsuc (k * k))

    open DC.Decide _≟W_ norm using () renaming (decideW to decide?W)

    -- front-end decision: a hit is a genuine `_≈Term_` of the free
    -- monoidal category over the ObjTerm-arity generators.
    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r = Data.Maybe.map solveF (decide?W (reflectF l) (reflectF r))

    open FSolve sig decide?F public using (module Into)

--------------------------------------------------------------------------------
-- `FinSetup`: the call-site convenience wrapper.  From a target monoidal
-- category `C`, a `Vec` of object atoms, and a Fin-indexed `arity` table, it
-- assembles the signature, decidable equalities and rank, exposing the term
-- language `S`, the embedding `gen`, the object interpretation `⟦_⟧ₒ` and —
-- after `WithGen` supplies the generator interpretations — `solveMor!`.
-- (Mirror of `Frontend.Sigma`'s `FinSetupσ`.  Both Fin wrappers are
-- call-site conveniences; the test suites — `Test.Frontend.Target` and
-- `Test.SigmaFrontend.Target` — instead wire the pieces (`FinSig` +
-- `module Frontend`/`FrontendS` + `Into`/`WithGen`) by hand.)
--------------------------------------------------------------------------------

module FinSetup
  {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  {nA : ℕ} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  where

  private module Core = FinSetupCore {v = Mon} C noSymmetric vars
  open Core public using (ObjTerm; V; unitᵒ; _⊗ᵒ_; ⟦_⟧ₒ)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    -- build the Mon front-end's decision procedure at this signature, then
    -- hand it to the variant-generic `FinSetupCore.Sig` (the `FinSig Mon arity`
    -- here and inside `Core.Sig` are the SAME `GenS`/`S`, so the types match).
    open FinSig Mon {X = Fin nA} arity
    open Frontend {Fin nA} _≟Fin_ GenS
    open Decide _≟G_ rankS

    open Core.Sig arity decide?F public
