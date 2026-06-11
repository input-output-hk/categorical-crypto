{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The solver FRONT-END: from wire-list diagrams to ObjTerm-arity generators.
--
-- The reflect/normalize/compare pipeline (SolverReflect / SolverNormalize /
-- SolverCompare) lives in the *wire-list* world: generators sit between
-- `wires a` / `wires b` and the tensor of flat terms needs a merge/split
-- conjugation (`embed (s ⊗ʷ t) = merge ∘ (… ⊗₁ …) ∘ split`).  That
-- conjugation leaks into every statement, so a clean target-category goal
-- like `(id ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ≈ sᴹ ⊗₁ tᴹ` cannot be discharged directly.
--
-- This module adds the missing front-end, mirroring the architecture of the
-- hypergraph solver's `Categories.Coherence.Symmetric.Setup`:
--
--   * generators `GenF : ObjTerm → ObjTerm → Set` live at ARBITRARY object
--     terms, and the front-end term language is `FreeMonoidalHelper.Mor`'s
--     `HomTerm` over `GenF`, whose interpretation into a target monoidal
--     category is DEFINITIONAL on every constructor (via `FreeFunctor`);
--
--   * `flatten : ObjTerm → List X` (with `flatten (Y ⊗₀ Z) ≡ flatten Y ++
--     flatten Z` definitionally) re-indexes the generators into a wire-level
--     family `MorW`, and `reflectF` maps front-end terms to wire terms
--     (structural morphisms die into casted `idʷ`s);
--
--   * the soundness bridge is proven ONCE, at the free level: `inj` maps the
--     wire-level free category into the front-end free category (boxes get
--     conjugated by the canonical structural iso `flat⇒`/`flat⇐`), and
--
--         bridgeF : inj (embed (reflectF t)) ∘ flat⇒ ≈ flat⇒ ∘ t
--
--     holds by induction, with the structural cases discharged by the
--     wire-level coherence lemmas (`merge-ρ`, `merge-assoc`, `merge∘split`)
--     transferred along `inj`;
--
--   * `Decide.solveTerm!` packages reflect → normalize → compare → bridge →
--     cancel into a decision procedure for the front-end `_≈Term_`, and
--     `Decide.Into.solveMor!` transports the result into an arbitrary target
--     monoidal category along the free functor — definitionally, so the
--     equation's two sides appear in the target's own vocabulary.
--
-- The shared machinery (flatten/MorW, mergeF/splitF, flat⇒/flat⇐, inj,
-- reflectF, the transfer lemmas, bridgeF, solveF) lives in
-- `Categories.SolverFrontendCore` (`FCore`/`FBridge`), instantiated here at
-- (Mon, MorW, ⟦box⟧); this file supplies the Mon-specific clauses (the
-- conjugated-box `injBox`, `reflectVar`, and the vacuous σ clauses on the
-- empty `Symm ≤ Mon`), the `Decide` layer (the interchange oracle `go`, the
-- first-applicable-position loop `step?`, and the fuel budget — the chaining
-- loop itself is the generic `normFuelWith` from `SolverNormalize.SortD`
-- §12d), term-level focusing, the rewriting layer, and `FinSetup`.
--
-- WHAT DECIDES (verified in `Categories.SolverFrontendTests`):
--   pure MacLane coherence (unitor/associator iso laws, triangle, pentagon,
--   λ≈ρ on unit); unitor/associator NATURALITY through box generators;
--   id/∘ laws and ⊗-functoriality; disjoint-box interchange in EITHER
--   firing order — the normalizer is a fuel-bounded bubble sort (`norm`,
--   budget (#layers)²+1) firing genuine interchange swaps at ANY position,
--   so multi-swap and non-head inversions decide — including multi-wire
--   boxes, empty-domain boxes and scalars (Eckmann-Hilton-style scalar
--   reordering decides via the `rank` tiebreak).
--
-- LIMITATIONS (precise; L2 machine-checked as `≡ nothing` in the tests):
--   L1  Sound, NOT complete: every `just` is a real `_≈Term_` proof, but
--       `nothing` does not refute the equation.
--   L2  Ambiguous pairs need an injective rank: scalar-like layers at the
--       same offset (`mid ≡ [] ∧ by ≡ [] ∧ ax ≡ []`) fit the swap
--       recogniser in BOTH orders and are ordered by the user-supplied
--       `rank` tiebreak; under a NON-INJECTIVE rank the sort cannot
--       separate them and `u ∘ v ≈ v ∘ u` stays undecided
--       (`Limitations.lim-equal-rank`).
--   L3  Monoidal only (`Variant` `Mon`): braided/symmetric goals are not
--       expressible (no σ in the term language).
--   L4  Decision-by-evaluation: requires a CONCRETE atom set (computing
--       `DecidableEquality`) and concrete arities; over abstract atoms the
--       `++-identityʳ`/`++-assoc` casts in `reflectF` do not reduce, so the
--       `IsJust` hit of `solveTerm!`/`solveMor!` cannot auto-discharge.
--       (For the same reason `step?` only iterates productively on concrete
--       diagrams: the `substDiagU` casts inside a swap result reduce only
--       at concrete indices.)
--   L5  Generator equality is the supplied syntactic `_≟G_`: no
--       generator-specific equations (naturality of a concrete box,
--       Frobenius laws, …) are known to the DECISION procedure.  The
--       rewriting layer (`rewriteMor!`/`rewriteMorₙ!`/`rewriteMorAuto!`)
--       carries such equations across as RULES: the rule fires inside a
--       two-sided frame `post ∘ (id ⊗ (– ⊗ id)) ∘ pre` (supplied, or
--       located by `focusAtₙ`), and the solver reconciles the endpoints.
--   L6  No canonicity/completeness theorem is claimed for `norm ∘ reflect`;
--       the test suite documents which equation shapes decide.
--
-- Hole-free, postulate-free, --safe.
--------------------------------------------------------------------------------

module Categories.SolverFrontend where

open import Data.Bool using (not; _∨_; if_then_else_)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Nat using (ℕ; _*_; _<ᵇ_) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Vec using (Vec; lookup)
open import Function using (case_of_)
open import Level using (Level)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)
open import Relation.Nullary using (yes; no)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)

import Categories.Morphism.Reasoning as MR

open import Categories.DiagramRewriteUntyped using (module Untyped)
open import Categories.FreeMonoidal
open import Categories.SolverCompare using (module SolverCompare)
open import Categories.SolverFrontendCore
  using (module MaybeHit; module FCore; module FBridge; module IntoCore; module FinSig; module FFocus)
open import Categories.SolverNormalize using (module Normalize)
open import Categories.SolverReflect using (module Reflect; module DecideCore)

module Frontend
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (let open FreeMonoidalHelper Mon X using (ObjTerm; unit; _⊗₀_; Var))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  ------------------------------------------------------------------------
  -- The engine-free shared layer: flatten, MorW, GenΣ, F≈R.
  ------------------------------------------------------------------------

  private module Core = FCore Mon {X = X} GenF
  open Core public using (flatten; MorW; mk; GenΣ; module F≈R)

  -- Wire-level machinery at MorW.
  open Untyped Mon {X} MorW                -- wires, mor, box, ⟦box⟧, merge, split, …
  open FreeMonoidalHelper.Mor Mon X mor    -- W-side HomTerm, _≈Term_, …
  open Reflect Mon {X} _≟X_ MorW           -- WTerm, embed, reflect, coeC, merge-ρ, …
  open ≈R

  -- Front-end free category: HomTerm over GenF, qualified `F`.
  private module F = FreeMonoidalHelper.Mor Mon X GenF

  -- stock combinators at the wire-level free category (proofs-only, not
  -- exported; used by the `Decide` layer below).
  open MR FreeMonoidal using (pullˡ)

  ------------------------------------------------------------------------
  -- The engine-generic shared layer, at (Mon, MorW, ⟦box⟧).
  ------------------------------------------------------------------------

  private module FB = FBridge Mon _≟X_ GenF MorW ⟦box⟧
  open FB public
    using (mergeF; splitF; flat⇒; flat⇐;
           coeCF; coeCF-∘ˡ; coeCF-resp; coe-coe;
           castʷ; embed-castʷ; fwd-λ; flipF)

  ------------------------------------------------------------------------
  -- The Mon-specific clauses: a box generator is conjugated by the
  -- canonical iso; the σ clauses are vacuous (`Symm ≤ Mon` is empty).
  ------------------------------------------------------------------------

  private
    injBox : ∀ {a b} → MorW a b → F.HomTerm (wires a) (wires b)
    injBox (mk {Y} {Z} g) = F._∘_ (flat⇒ Z) (F._∘_ (F.var g) (flat⇐ Y))

    reflectVarM : ∀ {Y Z} → GenF Y Z → WTerm (flatten Y) (flatten Z)
    reflectVarM g = boxʷ (mk g)

    reflectσM : ∀ ⦃ s : Symm ≤ Mon ⦄ (A B : ObjTerm)
              → WTerm (flatten A ++ flatten B) (flatten B ++ flatten A)
    reflectσM ⦃ () ⦄

  private module FBI = FB.WithInj injBox reflectVarM (λ ⦃ s ⦄ A B → reflectσM ⦃ s ⦄ A B)
  open FBI public
    using (inj; inj-resp-≈; inj-merge; inj-split; inj-coeC; reflectF;
           splitF∘mergeF; mergeF-ρ; mergeF-assoc; flat⇐∘flat⇒;
           cast-half; fwd-ρ; fwd-α)

  private
    bridge-σM : ∀ {A B : ObjTerm} ⦃ s : Symm ≤ Mon ⦄
              → F._∘_ (inj (embed (reflectσM ⦃ s ⦄ A B))) (flat⇒ (A ⊗₀ B))
                F.≈Term F._∘_ (flat⇒ (B ⊗₀ A)) (F.σ ⦃ s ⦄)
    bridge-σM ⦃ () ⦄

  private module FBB = FBI.Bridge (λ g → refl) (λ {A} {B} ⦃ s ⦄ → bridge-σM {A} {B} ⦃ s ⦄)
  open FBB public using (bridgeF; solveF)

  ------------------------------------------------------------------------
  -- The decision procedure: reflect both sides to DiagU, decide NF
  -- equality, chain the reflect-soundness witnesses, cancel through the
  -- bridge.  `Decide` needs decidable equality on labels and on the
  -- (Σ-packaged) front-end generators.
  ------------------------------------------------------------------------

  module Decide
    (_≟G_ : DecidableEquality GenΣ)
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous (mutually-fitting) pairs;
                        -- for a Fin-indexed signature, `toℕ` of the index.
    where

    private module SC = SolverCompare Mon _≟X_ MorW

    -- decidable equality on the Σ-packaged wire-level generators, derived
    -- from the front-end one (via the shared core helper).
    private
      _≟W_ : DecidableEquality SC.Gen
      _≟W_ = Core.decMorW _≟G_

    -- the SortD swap engine (the generic interchange oracle/loop now live in
    -- §12d/§12e; only the DecEq-dependent transport stays from Normalize).
    open Normalize Mon {X} _≟X_ MorW using ( substDiagU; module SortD )
    open SortD using (SwapRes; interchangeGo; stepWith; depthD; normFuelWith)

    private
      -- the wire-level generator's tiebreak key.
      rankW : ∀ {a b} → MorW a b → ℕ
      rankW = Core.rankMorW rank

    -- one interchange swap at the FIRST applicable position (the generic
    -- oracle/loop from SortD, at the Mon rank).
    step? : ∀ {n} (d : DiagU n) → Maybe (SwapRes d)
    step? = stepWith (interchangeGo rankW)

    -- layer count, and the worst-case bubble budget (≥ #inversions).
    norm : ∀ {n} (d : DiagU n) → SwapRes d
    norm d = normFuelWith step? (nsuc (depthD d * depthD d)) d

    ------------------------------------------------------------------------
    -- The wire-level decision: the shared DecideCore assembly at `norm`.
    ------------------------------------------------------------------------

    private module DC = DecideCore Mon {X} _≟X_ MorW ⟦box⟧
    open DC.Decide _≟W_ norm public using () renaming (decideW to decide?W)

    -- front-end decision: a hit is a genuine `_≈Term_` of the free
    -- monoidal category over the ObjTerm-arity generators.
    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r = Data.Maybe.map solveF (decide?W (reflectF l) (reflectF r))

    -- the computing hit-witness (`IsJust` normalizes to ⊤ exactly on a
    -- solver hit) and the hit extractor, shared via the core.
    open MaybeHit public using (IsJust; fromHit)

    -- reference-style entry point at the free level.
    solveTerm! : ∀ {Y Z} (l r : F.HomTerm Y Z)
                 {hit : IsJust (decide?F l r)} → l F.≈Term r
    solveTerm! l r {hit} = fromHit (decide?F l r) hit

    ------------------------------------------------------------------------
    -- Term-level FOCUSING (the Mon analogue of the SMC solver's `Carve`):
    -- find a frame  `post ∘ (id {k} ⊗ (– ⊗ id {m})) ∘ pre`  exhibiting an
    -- occurrence of a redex `lᵗ` inside `s`.  The symmetric version routes
    -- a left-factor wire past the redex with σ; the Mon fragment has no
    -- braiding, so the frame is TWO-SIDED (pads on both sides of the hole).
    -- The search is unverified: a `focusAtₙ` hit is certified downstream by
    -- `decide?F s (plug foc lᵗ)`, so soundness rests solely on the solver.
    ------------------------------------------------------------------------

    -- the focusing layer (_≟O_/Foc/plug/focusAll/focusAtₙ) is now the generic
    -- core layer, instantiated at this front-end's `decide?F`.  A single shared
    -- application `FF` is reused below (the rewrite layer lives in `FF.Rewrite`).
    module FF = FFocus Mon {X} _≟X_ GenF decide?F
    open FF public using (_≟O_; Foc; plug; focusAll; focusAtₙ)

    ------------------------------------------------------------------------
    -- Transport into an arbitrary target monoidal category, along the free
    -- functor at the ObjTerm-arity generators.  The interpretation is
    -- definitional on every term constructor, so `solveMor!`'s equation
    -- reads in the target's own vocabulary.
    ------------------------------------------------------------------------

    module Into
      {o ℓ e : Level}
      (C : MonoidalCategory o ℓ e)
      (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
      where

      private module IC = IntoCore Mon GenF C (λ where ⦃ () ⦄) ⟦_⟧ᵖ₀
      open IC public using (⟦_⟧ₒ)

      module WithGen
        (⟦gen⟧ : ∀ {Y Z} → GenF Y Z
               → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
        where

        private module ICW = IC.WithGenC ⟦gen⟧
        open ICW public using (⟦_⟧₁; ⟦⟧-resp-≈)

        -- THE entry point: discharge a target-category equation whose two
        -- sides are interpretations of front-end terms.
        solveMor! : ∀ {Y Z} (l r : F.HomTerm Y Z)
                    {hit : IsJust (decide?F l r)}
                  → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
        solveMor! l r {hit} = ⟦⟧-resp-≈ (solveTerm! l r {hit})

        ------------------------------------------------------------------------
        -- Diagrammatic REWRITING in C (the Mon analogue of the SMC solver's
        -- `rewriteH!`/`rewriteAutoₙ!`).  A *rule* is any C-equation
        -- `⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁` between interpretations of front-end terms —
        -- definitionally whatever raw C-equation the caller has (a generator
        -- law, an opaque-iso cancellation, an induction hypothesis, …).  The
        -- rule fires inside the two-sided frame
        --     post ∘ (id {k} ⊗ (– ⊗ id {m})) ∘ pre
        -- and the solver reconciles the caller's terms with the frames, so
        -- only the rule itself crosses the congruence.
        ------------------------------------------------------------------------

        private
          module MCc = MonoidalCategory C

          -- transport a rule across the frame of a focus, by congruence.
          -- (Reduction-sensitive: stays here where `⟦_⟧₁` is concrete.)
          plugCong : ∀ {A B P Q} (foc : Foc A B P Q) (l r : F.HomTerm P Q)
                   → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
                   → C .MonoidalCategory.U [ ⟦ plug foc l ⟧₁ ≈ ⟦ plug foc r ⟧₁ ]
          plugCong (k , m , pre , post) l r rule =
            MCc.∘-resp-≈ʳ (MCc.∘-resp-≈ˡ
              (MCc.⊗.F-resp-≈ (MCc.Equiv.refl , MCc.⊗.F-resp-≈ (rule , MCc.Equiv.refl))))

        -- the rewrite wrappers (rewriteMor!/rewriteMorₙ!/rewriteMorAuto!) are
        -- now the generic core layer, at this target's interpretation.
        open FF.Rewrite C ⟦_⟧ₒ ⟦_⟧₁ solveMor! plugCong public
          using (rewriteMor!; rewriteMorₙ!; rewriteMorAuto!)

--------------------------------------------------------------------------------
-- `FinSetup`: the call-site convenience wrapper (the analogue of the
-- hypergraph solver's `Coherence.Symmetric.Setup`).  From
--
--   * a target monoidal category `C`,
--   * a `Vec` of object atoms (the opaque objects of the goal), and
--   * a Fin-indexed `arity` table of generator arities (ObjTerms over the
--     atom indices),
--
-- it assembles the signature, decidable equalities and the rank tiebreak,
-- exposing the term language `S`, the generator embedding `gen`, the
-- object interpretation `⟦_⟧ₒ`, and — after `WithGen` supplies the
-- generator interpretations — the `solveMor!` entry point.
--
-- Typical use, discharging a C-equation between composites of opaque
-- morphisms and structural isos (cf. SolverFrontendTests.Target):
--
--   open FinSetup C (A ∷ B ∷ []) (λ { zero → Var zero , Var zero ; … })
--   open WithGen  (λ { (genS zero) → f ; … })
--   goal = solveMor! lhsᵗ rhsᵗ
--------------------------------------------------------------------------------

module FinSetup
  {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  {nA : ℕ} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  where

  -- the object language over the atom indices, with constructors renamed so
  -- they coexist with a caller's own free-category vocabulary.
  open FreeMonoidalHelper Mon (Fin nA) public
    using (ObjTerm) renaming (Var to V; unit to unitᵒ; _⊗₀_ to _⊗ᵒ_)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    -- the variant-generic Fin-signature prelude (GenS / S / gen / _≟G_ /
    -- rankS / GenΣ), shared with `FinSetupσ` via the core.
    open FinSig Mon {nA} arity public using (GenS; genS; module S; gen; GenΣ; _≟G_; rankS)

    open Frontend {Fin nA} _≟Fin_ GenS using (module Decide)

    open Decide _≟G_ rankS public
      using (decide?F; IsJust; solveTerm!; module Into
            ; Foc; plug; focusAll; focusAtₙ; fromHit; _≟O_)
    open Into C (lookup vars) public
