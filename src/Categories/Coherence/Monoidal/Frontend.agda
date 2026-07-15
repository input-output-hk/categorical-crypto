{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The solver FRONT-END: from wire-list diagrams to ObjTerm-arity generators.
--
-- The reflect/normalize/compare pipeline (Reflect / Normalize /
-- Compare) lives in the *wire-list* world, where the tensor of flat
-- terms needs a merge/split conjugation that leaks into every statement.  This
-- module lifts that to ARBITRARY-object-term generators `GenF`, so a clean
-- target-category goal like `(id ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ≈ sᴹ ⊗₁ tᴹ` reads
-- directly, mirroring the hypergraph solver's `Coherence.Symmetric.Setup`.
--
-- `flatten : ObjTerm → List X` (with `flatten (Y ⊗₀ Z) ≡ flatten Y ++
-- flatten Z` definitionally) re-indexes the generators to the wire level, and
-- the soundness bridge is proven ONCE at the free level:
--
--     bridgeF : inj (embed (reflectF t)) ∘ flat⇒ ≈ flat⇒ ∘ t
--
-- `Decide.solveTerm!` packages reflect → normalize → compare → bridge into a
-- decision procedure for the front-end `_≈Term_`; `Decide.Into.solveMor!`
-- transports a hit into an arbitrary target monoidal category along the free
-- functor — definitionally, so the equation reads in the target's vocabulary.
--
-- The shared machinery (flatten/MorW, mergeF/splitF, flat⇒/flat⇐, inj,
-- reflectF, bridgeF, solveF) lives in `Categories.Coherence.Monoidal.Frontend.Core`
-- (`FCore`/`FBridge`), instantiated here at (Mon, MorW, ⟦box⟧).  This file
-- supplies the Mon-specific clauses (`injBox`, `reflectVarM`, vacuous σ on the
-- empty `Symm ≤ Mon`).
--
-- What decides and the precise limitation catalogue (L1–L6) are
-- machine-checked in `Categories.Coherence.Monoidal.Test.Frontend`.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Frontend where

import Data.Maybe
open import categorical-crypto.Prelude
  hiding (_∘_; id; map; merge; zero; suc; lookup; [_]; [_,_])

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Nat using () renaming (suc to nsuc)
open import Data.Vec using (Vec; lookup)

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Monoidal using (MonoidalCategory)

open import Categories.Coherence.Monoidal.Diagram using (WireEngine; module Untyped)
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend.Core
  using (FreeSig; module FCore; module FBridge; module IntoCore; module FinSig; module FFocus)
open import Categories.Coherence.Monoidal.Normalize using (module Normalize)
open import Categories.Coherence.Monoidal.Reflect using (module Reflect; module DecideCore)

module Frontend
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (let open FreeMonoidalHelper Mon X using (ObjTerm; unit; _⊗₀_; Var))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  ------------------------------------------------------------------------
  -- The engine-free shared layer: flatten, MorW, GenΣ
  ------------------------------------------------------------------------

  private module Core = FCore Mon {X = X} GenF
  open Core public using (flatten; MorW; mk; GenΣ)

  open Untyped Mon {X} MorW                -- wires, mor, box, ⟦box⟧, merge, split, …
  open Reflect Mon {X} _≟X_ MorW           -- WTerm, embed, reflect, castW, merge-ρ, …

  -- the wire-level engine instance (MorW + ⟦box⟧), shared by FBridge/DecideCore.
  private
    EW : WireEngine Mon {X}
    EW = record { Mor = MorW ; ⟦box⟧ = ⟦box⟧ }

  -- the generator signature, shared by the engine modules below; `F` is its
  -- free category (HomTerm over GenF).
  private
    sig : FreeSig Mon {X}
    sig = record { _≟X_ = _≟X_ ; GenF = GenF }
  open FreeSig sig using (module F)

  ------------------------------------------------------------------------
  -- The engine-generic shared layer, at (Mon, MorW, ⟦box⟧)
  ------------------------------------------------------------------------

  private module FB = FBridge Mon _≟X_ GenF EW
  open FB using (flat⇒; flat⇐)

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
  open FBI using (reflectF)

  private module FBB = FBI.Bridge (λ g → refl) (λ where ⦃ () ⦄)
  open FBB using (solveF)

  ------------------------------------------------------------------------
  -- The decision procedure
  ------------------------------------------------------------------------

  module Decide
    (_≟G_ : DecidableEquality GenΣ)
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous (mutually-fitting) pairs;
                        -- for a Fin-indexed signature, `toℕ` of the index.
    where

    private
      _≟W_ = Core.decMorW _≟G_

    open Normalize Mon {X} _≟X_ MorW using (module SortD)
    open SortD using (SwapRes; interchangeGo; stepWith; depthD; normFuelWith)

    private
      rankW : ∀ {a b} → MorW a b → ℕ
      rankW = Core.rankMorW rank

      -- one interchange swap at the FIRST applicable position.
      step? : ∀ {n} (d : DiagU n) → Maybe (SwapRes d)
      step? = stepWith (interchangeGo rankW)

      -- a fuel-bounded bubble sort; the worst-case budget is ≥ #inversions.
      norm : ∀ {n} (d : DiagU n) → SwapRes d
      norm d = normFuelWith step? (nsuc (depthD d * depthD d)) d

    private module DC = DecideCore EW _≟X_
    open DC.Decide _≟W_ norm using () renaming (decideW to decide?W)

    -- front-end decision: a hit is a genuine `_≈Term_` of the free
    -- monoidal category over the ObjTerm-arity generators.
    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r = Data.Maybe.map solveF (decide?W (reflectF l) (reflectF r))

    module FF = FFocus sig decide?F
    open FF public using (IsJust; solveTerm!; _≟O_; Foc; plug; focusAll; focusAtₙ)

    ------------------------------------------------------------------------
    -- Transport into an arbitrary target monoidal category, along the
    -- free functor.  Definitional on every constructor, so `solveMor!`'s
    -- equation reads in the target's own vocabulary
    ------------------------------------------------------------------------

    module Into
      {o ℓ e : Level}
      (C : MonoidalCategory o ℓ e)
      (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
      where

      private module IC = IntoCore sig decide?F (fromMC C noSymmetric) ⟦_⟧ᵖ₀
      open IC public using (⟦_⟧ₒ)

      module WithGen
        (⟦gen⟧ : ∀ {Y Z} → GenF Y Z
               → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
        where

        open IC.WithGenC ⟦gen⟧ public
          using (⟦_⟧₁; ⟦⟧-resp-≈; solveMor!;
                 rewriteMor!; rewriteMorₙ!; rewriteMorAuto!)

--------------------------------------------------------------------------------
-- `FinSetup`: the call-site convenience wrapper.  From a target monoidal
-- category `C`, a `Vec` of object atoms, and a Fin-indexed `arity` table, it
-- assembles the signature, decidable equalities and rank, exposing the term
-- language `S`, the embedding `gen`, the object interpretation `⟦_⟧ₒ` and —
-- after `WithGen` supplies the generator interpretations — `solveMor!`.
-- Usage in `Test.Frontend.Target`.
--------------------------------------------------------------------------------

module FinSetup
  {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  {nA : ℕ} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  where

  -- the object language over the atom indices, with constructors renamed so
  -- they coexist with a caller's own free-category vocabulary.
  open FreeMonoidalHelper Mon (Fin nA) public
    using (ObjTerm) renaming (Var to V; unit to unitᵒ; _⊗₀_ to _⊗ᵒ_)

  -- the object interpretation `ObjTerm → C.Obj`.  Independent of any generator
  -- signature — definitionally the `⟦_⟧ₒ` each `Sig` exposes — so it can type a
  -- generator's interpretation BEFORE the signature is fixed (see `Mor`).
  open FreeObjInterp Mon (Fin nA) (fromMC C noSymmetric) (lookup vars)
    public using () renaming (⟦_⟧₀ to ⟦_⟧ₒ)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    open FinSig Mon {X = Fin nA} arity public using (GenS; genS; module S; gen; GenΣ; _≟G_; rankS)

    open Frontend {Fin nA} _≟Fin_ GenS using (module Decide)

    open Decide _≟G_ rankS public
      using (decide?F; IsJust; solveTerm!; module Into
            ; Foc; plug; focusAll; focusAtₙ; _≟O_)
    open Into C (lookup vars) public
