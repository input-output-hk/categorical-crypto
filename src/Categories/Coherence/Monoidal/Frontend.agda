{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The solver FRONT-END: from wire-list diagrams to ObjTerm-arity generators.
--
-- The reflect/normalize/compare pipeline (Reflect / Normalize /
-- Compare) lives in the *wire-list* world, where the tensor of flat
-- terms is a merge/split conjugation (paid once, in `embed-resp-≈`).  This
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
-- `Decide.decide?F` packages reflect → normalize → compare → bridge into a
-- decision procedure for the front-end `_≈Term_`; `FinSetup.Sig` feeds it to
-- the shared `FinSetupCore.Sig` pipeline, whose `solveMor!` transports a hit
-- into an arbitrary target monoidal category along the free functor —
-- definitionally, so the equation reads in the target's vocabulary.
--
-- The shared machinery (flatten/MorW, flat⇒/flat⇐, inj,
-- reflectF, bridgeF, solveF) lives in `Categories.Coherence.Monoidal.Frontend.Core`
-- (`FCore`/`FBridge`), instantiated here at (Mon, MorW, ⟦_⟧ᵇ).  This file
-- supplies the Mon-specific clauses (`injBox`, `reflectVarM`, vacuous σ on the
-- empty `Symm ≤ Mon`).
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

  ------------------------------------------------------------------------
  -- The engine-free shared layer: flatten, MorW, GenΣ
  ------------------------------------------------------------------------

  private module Core = FCore Mon {X = X} GenF
  open Core

  -- the wire-level engine instance (MorW at the standard interpretation),
  -- shared by the whole wire pipeline and FBridge/DecideCore.
  private
    EW : WireEngine Mon
    EW = stdEngine Mon MorW

    -- the generator signature, shared by the engine modules below; `F` is its
    -- free category (HomTerm over GenF).
    sig : FreeSig Mon
    sig = record { GenF = GenF }
  open FreeSig sig using (module F)

  open DiagramI EW
  open ReflectI EW

  ------------------------------------------------------------------------
  -- The engine-generic shared layer, at (Mon, MorW, ⟦_⟧ᵇ)
  ------------------------------------------------------------------------

  private module FB = FBridge sig EW
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
    ⦃ _ : DecEq GenΣ ⦄
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous pairs
    where

    private
      open NormalizeI EW
      open SortD
      open Steps PrimSwap
      open FreeMonoidalHelper.Mor Mon X mor
      module DC = DecideCore EW

      rankW : ∀ {a b} → MorW a b → ℕ
      rankW = Core.rankMorW rank

      -- one interchange swap at the FIRST applicable position, as an `_⤳D_`
      -- rewrite witness.
      step? : ∀ {n m} (d : Diag n m) → Maybe (Σ[ d' ∈ Diag n m ] (d ⤳D d'))
      step? = stepWith (interchangeGo rankW)

      -- a fuel-bounded bubble sort emitting an `_⤳D_` trace, discharged to a
      -- STRICT semantic witness by `normSoundˢ` at the EMPTY engine `R = ⊥`
      -- (the Mon path has no engine axioms).  The worst-case budget is
      -- ≥ #inversions.
      norm = normSoundˢ (λ _ _ → ⊥) (prim-swap-soundˢ (λ _ _ → ⊥)) step? (λ k → nsuc (k * k))

    open DC.Decide (λ _ _ → ⊥) (λ ()) norm using () renaming (decideW to decide?W)

    -- front-end decision: a hit is a genuine `_≈Term_` of the free
    -- monoidal category over the ObjTerm-arity generators.
    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r = Data.Maybe.map solveF (decide?W (reflectF l) (reflectF r))

--------------------------------------------------------------------------------
-- `FinSetup`: the call-site convenience wrapper.  From a target monoidal
-- category `C`, a `Vec` of object atoms, and a Fin-indexed `arity` table, it
-- assembles the signature, decidable equalities and rank, exposing the term
-- language `S`, the embedding `gen`, the object interpretation `⟦_⟧ₒ` and —
-- after `WithGen` supplies the generator interpretations — `solveMor!`.
-- (Mirror of `Frontend.Sigma`'s `FinSetupσ`.  The entry points in
-- `Categories.Coherence.Monoidal` go through these wrappers; the negative
-- test suites instead open `Frontend`/`Decide` directly, to state
-- `decide?F … ≡ nothing` boundaries.)
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
    open Frontend {Fin nA} GenS
    open Decide rankS

    open Core.Sig arity decide?F public
