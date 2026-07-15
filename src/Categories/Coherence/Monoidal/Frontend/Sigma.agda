{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The SYMMETRIC solver front-end: `solveMorσ!`.
--
-- The `Symm` mirror of `Categories.Coherence.Monoidal.Frontend` over the σ-EXTENDED wire
-- engine (`Categories.Coherence.Monoidal.Sigma`): the front-end term language carries the
-- braiding σ, and the wire level is `Sigma`'s `MorS` family (opaque boxes +
-- transparent block crossings), whose driver `decideσ?` normalizes by
-- σσ-cancellation, the two naturality SLIDES and disjoint interchange.
--
-- The shared machinery lives in `Categories.Coherence.Monoidal.Frontend.Core`
-- (`FCore`/`FBridge`), instantiated at (Symm, MorS, ⟦box⟧S).  This file
-- supplies only the σ-specific clauses:
--
--   * `injBox (cross a b)` maps a crossing to the σ-composite
--     `F.merge b ∘ σ ∘ F.split a`;
--   * `reflectσ A B = boxʷ (cross (flatten A) (flatten B))`, cast-free since
--     `flatten (A ⊗₀ B) ≡ flatten A ++ flatten B` holds definitionally;
--   * `bridge-σ` — the ONE genuinely new bridge case: after `F.split ∘ F.merge`
--     cancellation the goal reduces to braiding naturality at
--     (flat⇒ A , flat⇒ B), i.e. the σ∘[f⊗g]≈[g⊗f]∘σ axiom.
--
-- `Into` takes a target monoidal category WITH a `Symmetric` structure, so σ
-- lands on the target's braiding.  What decides, the inherited L1/L2/L4/L6,
-- the shared L5 mitigation, and the braiding-specific boundaries Lσ1 (hexagon)
-- / Lσ2 (straddling box) are machine-checked in
-- `Categories.Coherence.Monoidal.Test.SigmaFrontend`.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Frontend.Sigma where

import Data.Maybe
open import categorical-crypto.Prelude
  hiding (_∘_; id; map; merge; zero; suc; lookup; [_]; [_,_])

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Vec using (Vec; lookup)

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend.Core
  using (FreeSig; module FCore; module FBridge; module IntoCore; module FinSig; module FFocus)
open import Categories.Coherence.Monoidal.Sigma using (module Sigma)

module FrontendS
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (let open FreeMonoidalHelper Symm X using (ObjTerm; _⊗₀_))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  ------------------------------------------------------------------------
  -- The engine-free shared layer: flatten, MorW, GenΣ, F≈R
  ------------------------------------------------------------------------

  private module Core = FCore Symm {X = X} GenF
  open Core public using (flatten; MorW; mk; GenΣ; module F≈R)
  open F≈R

  -- the σ-engine at MorW; its `Decide` driver renamed `DecideW`, the
  -- front-end defines its own `Decide` below.
  open Sigma _≟X_ MorW renaming (module Decide to DecideW)

  -- Front-end free category: HomTerm over GenF, qualified `F`.
  -- the generator signature, shared by the engine modules below; `F` is its
  -- free category (HomTerm over GenF).
  private
    sig : FreeSig Symm {X}
    sig = record { _≟X_ = _≟X_ ; GenF = GenF }
  open FreeSig sig using (module F)

  ------------------------------------------------------------------------
  -- The engine-generic shared layer, at (Symm, MorS, ⟦box⟧S)
  ------------------------------------------------------------------------

  private module FB = FBridge Symm _≟X_ GenF ES
  open FB public using (flat⇒; flat⇐)

  ------------------------------------------------------------------------
  -- The σ-specific clauses: a box is conjugated by the canonical iso, a
  -- crossing is the σ-composite in flat coordinates.  The `cross` case of
  -- `injBox` is unreachable from `embed ∘ reflectF`, so only its
  -- well-typedness matters
  ------------------------------------------------------------------------

  private
    injBox : ∀ {a b} → MorS a b → F.HomTerm (wires a) (wires b)
    injBox (box (mk {Y} {Z} g)) = flat⇒ Z F.∘ (F.var g F.∘ flat⇐ Y)
    injBox (cross a b)          = F.merge b {a} F.∘ (F.σ F.∘ F.split a {b})

    reflectVarS : ∀ {Y Z} → GenF Y Z → WTerm (flatten Y) (flatten Z)
    reflectVarS g = boxʷ (box (mk g))

    reflectσS : ∀ ⦃ s : Symm ≤ Symm ⦄ (A B : ObjTerm)
              → WTerm (flatten A ++ flatten B) (flatten B ++ flatten A)
    reflectσS A B = boxʷ (cross (flatten A) (flatten B))

  private module FBI = FB.WithInj injBox reflectVarS (λ ⦃ s ⦄ A B → reflectσS ⦃ s ⦄ A B)
  open FBI public
    using (inj; inj-merge; inj-split; reflectF)

  ------------------------------------------------------------------------
  -- The σ bridge law — the ONE genuinely new case of bridgeF: after
  -- `F.split ∘ F.merge` cancellation the goal is braiding naturality at
  -- (flat⇒ A , flat⇒ B)
  ------------------------------------------------------------------------

  private
    bridge-σS : ∀ {A B : ObjTerm} ⦃ s : Symm ≤ Symm ⦄
              → inj (embed (reflectσS ⦃ s ⦄ A B)) F.∘ flat⇒ (A ⊗₀ B)
                F.≈Term flat⇒ (B ⊗₀ A) F.∘ F.σ ⦃ s ⦄
    bridge-σS {A} {B} ⦃ v≤v ⦄ = beginF
      inj (embed (reflectσS A B)) F.∘ (F.merge fA {fB} F.∘ (f⇒A F.⊗₁ f⇒B))
        ≈F⟨ F.≡⇒≈Term (cong₂ (λ h j → h F.∘ (F.σ F.∘ j))
                       (inj-merge fB {fA}) (inj-split fA {fB})) F.⟩∘⟨refl ⟩
      (F.merge fB {fA} F.∘ (F.σ F.∘ F.split fA {fB})) F.∘ (F.merge fA {fB} F.∘ (f⇒A F.⊗₁ f⇒B))
        ≈F⟨ F.assoc²βε F.○ (F.refl⟩∘⟨ (F.refl⟩∘⟨ F.cancelˡ (F.split∘merge fA {fB}))) ⟩
      F.merge fB {fA} F.∘ (F.σ F.∘ (f⇒A F.⊗₁ f⇒B))
        ≈F⟨ F.refl⟩∘⟨ F.σ∘[f⊗g]≈[g⊗f]∘σ ⟩
      F.merge fB {fA} F.∘ ((f⇒B F.⊗₁ f⇒A) F.∘ F.σ)
        ≈F⟨ F.⟺ F.assoc ⟩
      (F.merge fB {fA} F.∘ (f⇒B F.⊗₁ f⇒A)) F.∘ F.σ ∎F
      where
        fA = flatten A ; fB = flatten B
        f⇒A = flat⇒ A ; f⇒B = flat⇒ B

  private module FBB = FBI.Bridge (λ g → refl) (λ {A} {B} ⦃ s ⦄ → bridge-σS {A} {B} ⦃ s ⦄)
  open FBB using (solveF)

  ------------------------------------------------------------------------
  -- The decision procedure: reflect both sides, hand them to the
  -- σ-engine driver `decideσ?`, cancel through the bridge
  ------------------------------------------------------------------------

  module Decide
    (_≟G_ : DecidableEquality GenΣ)
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous (mutually-fitting) pairs;
                        -- for a Fin-indexed signature, `toℕ` of the index.
    where

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

    module FF = FFocus sig decide?F
    open FF public using (IsJust; solveTerm!; _≟O_; Foc; plug; focusAll; focusAtₙ)

    ------------------------------------------------------------------------
    -- Transport into a target symmetric monoidal category, along the free
    -- functor.  σ lands on the target's braiding, so `solveMorσ!`'s equation
    -- reads in the target's own vocabulary
    ------------------------------------------------------------------------

    module Into
      {o ℓ e : Level}
      (C : MonoidalCategory o ℓ e)
      (Sym : Symmetric (C .MonoidalCategory.monoidal))
      (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
      where

      private module IC = IntoCore sig decide?F (fromMC C (λ ⦃ _ ⦄ → Sym)) ⟦_⟧ᵖ₀
      open IC public using (⟦_⟧ₒ)

      module WithGen
        (⟦gen⟧ : ∀ {Y Z} → GenF Y Z
               → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
        where

        open IC.WithGenC ⟦gen⟧ public
          using (⟦_⟧₁; ⟦⟧-resp-≈)
          renaming (solveMor! to solveMorσ!;
                    rewriteMor! to rewriteMorσ!; rewriteMorₙ! to rewriteMorσₙ!;
                    rewriteMorAuto! to rewriteMorσAuto!)

--------------------------------------------------------------------------------
-- `FinSetupσ`: the call-site convenience wrapper (the σ-analogue of the Mon
-- front-end's `FinSetup`).  Takes a target monoidal category WITH a
-- `Symmetric` structure; exposes the term language `S` (with σ) and, after
-- `WithGen`, the `solveMorσ!` entry point.
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

  -- the object interpretation `ObjTerm → C.Obj`, independent of any generator
  -- signature — definitionally the `⟦_⟧ₒ` each `Sig` exposes (see `Morσ`).
  open FreeObjInterp Symm (Fin nA) (fromMC C (λ ⦃ _ ⦄ → Sym)) (lookup vars)
    public using () renaming (⟦_⟧₀ to ⟦_⟧ₒ)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    open FinSig Symm {X = Fin nA} arity public using (GenS; genS; module S; gen; GenΣ; _≟G_; rankS)

    open FrontendS {Fin nA} _≟Fin_ GenS using (module Decide)

    open Decide _≟G_ rankS public
      using (decide?F; IsJust; solveTerm!; module Into
            ; Foc; plug; focusAll; focusAtₙ; _≟O_)
    open Into C Sym (lookup vars) public
