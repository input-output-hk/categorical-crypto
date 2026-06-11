{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The SYMMETRIC solver front-end: `solveMorσ!`.
--
-- The Mon front-end (`Categories.SolverFrontend`) decides clean monoidal
-- goals between ObjTerm-arity generators by reflecting through the
-- wire-level engine.  This module is its `Symm` mirror over the σ-EXTENDED
-- wire engine (`Categories.SolverSigma`): the front-end term language is
-- `FreeMonoidalHelper.Mor Symm X GenF`'s `HomTerm` — WITH the braiding σ —
-- and the wire level is `Sigma`'s `MorS` family (opaque boxes + transparent
-- block crossings), whose driver `decideσ?` normalizes by σσ-cancellation,
-- the two naturality SLIDES and disjoint interchange.
--
-- The shared machinery (flatten/MorW, mergeF/splitF, flat⇒/flat⇐, inj,
-- reflectF, the transfer lemmas, bridgeF, solveF) lives in
-- `Categories.SolverFrontendCore` (`FCore`/`FBridge`), instantiated at
-- (Symm, MorS, ⟦box⟧S).  This file supplies ONLY the σ-specific clauses:
--
--   * `injBox (cross a b)` — the crossing maps to the σ-composite
--     `mergeF b ∘ σ ∘ splitF a` (the box case is the usual conjugated
--     generator);
--   * `reflectσ A B = boxʷ (cross (flatten A) (flatten B))` — CAST-FREE,
--     since `flatten (A ⊗₀ B) ≡ flatten A ++ flatten B` holds
--     definitionally;
--   * `bridge-σ` — the ONE genuinely new bridge case: for σ the goal
--     reduces — after `splitF ∘ mergeF` cancellation — to braiding
--     naturality at the pair (flat⇒ A , flat⇒ B), i.e. the
--     σ∘[f⊗g]≈[g⊗f]∘σ axiom;
--   * `Decide` wraps the σ-engine's `decideσ?` (the slide-capable driver);
--     `Into` takes a target MONOIDAL category TOGETHER WITH a `Symmetric`
--     structure on it, and `WithGen.solveMorσ!` transports a decided
--     front-end equation along the free functor — definitionally, so the
--     equation's two sides read in the target's own vocabulary;
--   * `FinSetupσ` is the call-site convenience wrapper (the σ-analogue of
--     the Mon `FinSetup`).
--
-- WHAT DECIDES (verified in `Categories.SolverSigmaFrontendTests`): all
-- Mon front-end shapes, plus σ∘σ≈id (also deep in context), σ-naturality
-- through box generators (TWO machine-fired slides, one per image block),
-- and mixes of σ-cancellation with coherence/functoriality.
--
-- LIMITATIONS: the Mon front-end's L1/L2/L4/L6 carry over verbatim, and so
-- does L5's negative half (generator-specific equations are unknown to the
-- decision procedure) — but with NO mitigation: this front-end has no
-- rewriting/focusing layer (`rewriteMor!`/`focusAtₙ` exist only in the Mon
-- front-end).
-- The braiding-specific boundary (machine-checked in the tests):
--   Lσ1  HEXAGON-shaped goals do not decide: the normalizer never splits
--        or merges crossing BLOCKS (`cross a b` vs `cross a (b₁ ++ b₂)`
--        compositions are distinct normal forms).  Only cancellation of
--        exact inverse pairs and box-slides through a crossing fire.
--   Lσ2  A box STRADDLING the two image blocks of a crossing does not
--        slide (no sound move exists without splitting the box).
--
-- Hole-free, postulate-free, --safe --without-K.
--------------------------------------------------------------------------------

module Categories.SolverSigmaFrontend where

open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Vec using (Vec; lookup)
open import Function using (case_of_)
open import Level using (Level)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

import Categories.Category.Monoidal.Reasoning as MonR

open import Categories.FreeMonoidal
open import Categories.SolverFrontendCore
  using (module MaybeHit; module FCore; module FBridge; module IntoCore)
open import Categories.SolverSigma using (module Sigma)

module FrontendS
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (let open FreeMonoidalHelper Symm X using (ObjTerm; unit; _⊗₀_; Var))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  -- `Symm ≤ Symm` for instance search, so σ needs no explicit ⦃ v≤v ⦄.
  private instance
    S≤S : Symm ≤ Symm
    S≤S = v≤v

  ------------------------------------------------------------------------
  -- The engine-free shared layer: flatten, MorW, GenΣ, F≈R.
  ------------------------------------------------------------------------

  private module Core = FCore Symm {X = X} GenF
  open Core public using (flatten; MorW; mk; GenΣ; module F≈R)
  open F≈R

  -- THE σ-ENGINE at MorW: the extended generators `MorS MorW` (box|cross),
  -- the wire signature, ⟦box⟧S, reflect/embed, and the `Decide` driver
  -- (renamed `DecideW`, the front-end defines its own `Decide` below).
  open Sigma _≟X_ MorW renaming (module Decide to DecideW)
  open FreeMonoidalHelper.Mor Symm X mor    -- W-side HomTerm, _≈Term_, σ, …

  -- Front-end free category: HomTerm over GenF, qualified `F`.
  private module F = FreeMonoidalHelper.Mor Symm X GenF

  -- stock combinators at the F-side free category (proofs-only, not exported).
  open MonR F.Monoidal-FreeMonoidal
    using ()
    renaming (refl⟩∘⟨_ to infixr 4 reflF⟩∘⟨_; _⟩∘⟨refl to infixl 5 _⟩∘F⟨refl;
              ⟺ to ⟺F; _○_ to infixr 3 _○F_)

  ------------------------------------------------------------------------
  -- The engine-generic shared layer, at (Symm, MorS, ⟦box⟧S).
  ------------------------------------------------------------------------

  private module FB = FBridge Symm _≟X_ GenF MorS ⟦box⟧S
  open FB public
    using (mergeF; splitF; flat⇒; flat⇐;
           coeCF; coeCF-∘ˡ; coeCF-resp; coe-coe;
           castʷ; embed-castʷ; fwd-λ; flipF)

  -- readability aliases (function aliases of the F constructors)
  private
    infixr 9 _∘F_
    infixr 10 _⊗F_
    _∘F_ : ∀ {A B C} → F.HomTerm B C → F.HomTerm A B → F.HomTerm A C
    _∘F_ = F._∘_
    _⊗F_ : ∀ {A B C D} → F.HomTerm A B → F.HomTerm C D → F.HomTerm (A ⊗₀ C) (B ⊗₀ D)
    _⊗F_ = F._⊗₁_
    reflF : ∀ {A B} {f : F.HomTerm A B} → f F.≈Term f
    reflF = F.≈-Term-refl

  ------------------------------------------------------------------------
  -- The σ-specific clauses: a box generator is conjugated by the canonical
  -- iso; a crossing is the σ-composite in flat coordinates.  (The `cross`
  -- case of `injBox` is UNREACHABLE from `embed ∘ reflectF` — embed
  -- unfolds a `boxʷ (cross …)` to ⟦box⟧S's σ-composite, never to a `var` —
  -- so only its well-typedness matters.)
  ------------------------------------------------------------------------

  private
    injBox : ∀ {a b} → MorS a b → F.HomTerm (wires a) (wires b)
    injBox (box (mk {Y} {Z} g)) = flat⇒ Z ∘F (F.var g ∘F flat⇐ Y)
    injBox (cross a b)          = mergeF b {a} ∘F (F.σ ∘F splitF a {b})

    reflectVarS : ∀ {Y Z} → GenF Y Z → WTerm (flatten Y) (flatten Z)
    reflectVarS g = boxʷ (box (mk g))

    reflectσS : ∀ ⦃ s : Symm ≤ Symm ⦄ (A B : ObjTerm)
              → WTerm (flatten A ++ flatten B) (flatten B ++ flatten A)
    reflectσS A B = boxʷ (cross (flatten A) (flatten B))

  private module FBI = FB.WithInj injBox reflectVarS (λ ⦃ s ⦄ A B → reflectσS ⦃ s ⦄ A B)
  open FBI public
    using (inj; inj-resp-≈; inj-merge; inj-split; inj-coeC; reflectF;
           splitF∘mergeF; mergeF-ρ; mergeF-assoc; flat⇐∘flat⇒;
           cast-half; fwd-ρ; fwd-α)

  ------------------------------------------------------------------------
  -- The σ bridge law — the ONE genuinely new case of bridgeF:
  -- `embed (boxʷ (cross fA fB))` unfolds to `merge fB ∘ σ ∘ split fA`;
  -- after `splitF ∘ mergeF` cancellation the goal is braiding naturality
  -- at the pair (flat⇒ A , flat⇒ B).
  ------------------------------------------------------------------------

  private
    bridge-σS : ∀ {A B : ObjTerm} ⦃ s : Symm ≤ Symm ⦄
              → inj (embed (reflectσS ⦃ s ⦄ A B)) ∘F flat⇒ (A ⊗₀ B)
                F.≈Term flat⇒ (B ⊗₀ A) ∘F F.σ ⦃ s ⦄
    bridge-σS {A} {B} ⦃ v≤v ⦄ = beginF
      inj (embed (reflectσS A B)) ∘F (mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B))
        ≈F⟨ F.≡⇒≈Term (cong₂ (λ h j → h ∘F (σF ∘F j))
                       (inj-merge fB {fA}) (inj-split fA {fB})) ⟩∘F⟨refl ⟩
      (mergeF fB {fA} ∘F (F.σ ∘F splitF fA {fB})) ∘F (mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B))
        ≈F⟨ F.assoc ⟩
      mergeF fB {fA} ∘F ((F.σ ∘F splitF fA {fB}) ∘F (mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B)))
        ≈F⟨ reflF⟩∘⟨ F.assoc ⟩
      mergeF fB {fA} ∘F (F.σ ∘F (splitF fA {fB} ∘F (mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B))))
        ≈F⟨ reflF⟩∘⟨ (reflF⟩∘⟨ (⟺F F.assoc)) ⟩
      mergeF fB {fA} ∘F (F.σ ∘F ((splitF fA {fB} ∘F mergeF fA {fB}) ∘F (f⇒A ⊗F f⇒B)))
        ≈F⟨ reflF⟩∘⟨ (reflF⟩∘⟨
              ((((splitF∘mergeF fA {fB}) ⟩∘F⟨refl)) ○F F.idˡ)) ⟩
      mergeF fB {fA} ∘F (F.σ ∘F (f⇒A ⊗F f⇒B))
        ≈F⟨ reflF⟩∘⟨ F.σ∘[f⊗g]≈[g⊗f]∘σ ⟩
      mergeF fB {fA} ∘F ((f⇒B ⊗F f⇒A) ∘F F.σ)
        ≈F⟨ ⟺F F.assoc ⟩
      (mergeF fB {fA} ∘F (f⇒B ⊗F f⇒A)) ∘F F.σ ∎F
      where
        fA = flatten A ; fB = flatten B
        f⇒A = flat⇒ A ; f⇒B = flat⇒ B
        σF : F.HomTerm (wires fA ⊗₀ wires fB) (wires fB ⊗₀ wires fA)
        σF = F.σ

  private module FBB = FBI.Bridge (λ g → refl) (λ {A} {B} ⦃ s ⦄ → bridge-σS {A} {B} ⦃ s ⦄)
  open FBB public using (bridgeF; solveF)

  ------------------------------------------------------------------------
  -- The decision procedure: reflect both sides, hand them to the σ-engine
  -- driver `decideσ?` (σσ-cancel + slides + interchange), cancel through
  -- the bridge.
  ------------------------------------------------------------------------

  module Decide
    (_≟G_ : DecidableEquality GenΣ)
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous (mutually-fitting) pairs;
                        -- for a Fin-indexed signature, `toℕ` of the index.
    where

    -- decidable equality and rank on the Σ-packaged wire-level generators,
    -- derived from the front-end ones (via the shared core helpers).
    private
      _≟GM_ : DecidableEquality GenM
      _≟GM_ = Core.decMorW _≟G_

      rankM : GenM → ℕ
      rankM (_ , _ , w) = Core.rankMorW rank w

      module DW = DecideW _≟GM_ rankM

    -- front-end decision: a hit is a genuine `_≈Term_` of the free
    -- SYMMETRIC monoidal category over the ObjTerm-arity generators.
    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r = Data.Maybe.map solveF (DW.decideσ? (reflectF l) (reflectF r))

    -- the computing hit-witness: normalizes to ⊤ exactly on a solver hit, so
    -- the implicit is auto-discharged at concrete test sites.
    open MaybeHit public using (IsJust)
    open MaybeHit using (fromHit)

    -- reference-style entry point at the free level.
    solveTerm! : ∀ {Y Z} (l r : F.HomTerm Y Z)
                 {hit : IsJust (decide?F l r)} → l F.≈Term r
    solveTerm! l r {hit} = fromHit (decide?F l r) hit

    ------------------------------------------------------------------------
    -- Transport into an arbitrary target SYMMETRIC monoidal category (a
    -- monoidal category bundled with a `Symmetric` structure), along the
    -- free functor at the ObjTerm-arity generators.  The interpretation is
    -- definitional on every term constructor — σ lands on the target's
    -- braiding — so `solveMorσ!`'s equation reads in the target's own
    -- vocabulary.
    ------------------------------------------------------------------------

    module Into
      {o ℓ e : Level}
      (C : MonoidalCategory o ℓ e)
      (Sym : Symmetric (C .MonoidalCategory.monoidal))
      (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
      where

      private module IC = IntoCore Symm GenF C (λ ⦃ _ ⦄ → Sym) ⟦_⟧ᵖ₀
      open IC public using (⟦_⟧ₒ)

      module WithGen
        (⟦gen⟧ : ∀ {Y Z} → GenF Y Z
               → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
        where

        private module ICW = IC.WithGenC ⟦gen⟧
        open ICW public using (⟦_⟧₁; ⟦⟧-resp-≈)

        -- THE entry point: discharge a target-category equation whose two
        -- sides are interpretations of front-end terms (with σ).
        solveMorσ! : ∀ {Y Z} (l r : F.HomTerm Y Z)
                     {hit : IsJust (decide?F l r)}
                   → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
        solveMorσ! l r {hit} = ⟦⟧-resp-≈ (solveTerm! l r {hit})

--------------------------------------------------------------------------------
-- `FinSetupσ`: the call-site convenience wrapper (the σ-analogue of the Mon
-- front-end's `FinSetup`).  From
--
--   * a target monoidal category `C` WITH a `Symmetric` structure,
--   * a `Vec` of object atoms, and
--   * a Fin-indexed `arity` table of generator arities,
--
-- it assembles the signature, decidable equalities and the rank tiebreak,
-- exposing the term language `S` (with σ), the generator embedding `gen`,
-- the object interpretation `⟦_⟧ₒ`, and — after `WithGen` supplies the
-- generator interpretations — the `solveMorσ!` entry point.
--------------------------------------------------------------------------------

module FinSetupσ
  {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  (Sym : Symmetric (C .MonoidalCategory.monoidal))
  {nA : ℕ} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  where

  -- the object language over the atom indices, with constructors renamed so
  -- they coexist with a caller's own free-category vocabulary.
  open FreeMonoidalHelper Symm (Fin nA) public
    using (ObjTerm) renaming (Var to V; unit to unitᵒ; _⊗₀_ to _⊗ᵒ_)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    data GenS : ObjTerm → ObjTerm → Set where
      genS : (i : Fin nG) → GenS (proj₁ (arity i)) (proj₂ (arity i))

    -- the front-end term language over the assembled signature.
    module S = FreeMonoidalHelper.Mor Symm (Fin nA) GenS

    gen : (i : Fin nG) → S.HomTerm (proj₁ (arity i)) (proj₂ (arity i))
    gen i = S.var (genS i)

    open FrontendS {Fin nA} _≟Fin_ GenS using (GenΣ; module Decide)

    private
      _≟G_ : DecidableEquality GenΣ
      (_ , _ , genS i) ≟G (_ , _ , genS j) = case i ≟Fin j of λ where
        (yes refl) → yes refl
        (no ¬p)    → no λ where refl → ¬p refl

      rankS : GenΣ → ℕ
      rankS (_ , _ , genS i) = toℕ i

    open Decide _≟G_ rankS public
      using (decide?F; IsJust; solveTerm!; module Into)
    open Into C Sym (lookup vars) public
