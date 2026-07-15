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
-- (`FCore`/`FBridge`), instantiated at (Symm, MorS, ⟦_⟧ᵇˢ).  This file
-- supplies only the σ-specific clauses:
--
--   * `reflectσ A B = boxʷ (cross (flatten A) (flatten B))`, cast-free since
--     `flatten (A ⊗₀ B) ≡ flatten A ++ flatten B` holds definitionally;
--   * `bridge-σ` — the only σ-specific bridge case (beyond Core's bridgeF): after `F.split ∘ F.merge`
--     cancellation the goal reduces to braiding naturality at
--     (flat⇒ A , flat⇒ B), i.e. the σ∘[f⊗g]≈[g⊗f]∘σ axiom.
--
-- The target (via `FinSetupσ`) is a monoidal category WITH a `Symmetric`
-- structure, so σ lands on the target's braiding.  The positive σ cases and the
-- braiding-specific boundaries Lσ1 (hexagon) / Lσ2 (straddling box) are
-- machine-checked in `Categories.Coherence.Monoidal.Test.SigmaFrontend`; the
-- limitations inherited from the shared `Frontend.Core` pipeline are
-- catalogued in the Mon `Categories.Coherence.Monoidal.Test.Frontend`
-- (which pins the non-injective-rank L2 and syntactic-generator L5 as
-- `≡ nothing`, the others being meta-properties).
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Frontend.Sigma where

import Data.Maybe
open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; lookup; [_]; [_,_])

open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric

open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend.Core
open import Categories.Coherence.Monoidal.Sigma

module FrontendS
  {X : Set} ⦃ _ : DecEq X ⦄
  (let open FreeMonoidalHelper Symm X using (ObjTerm; _⊗₀_))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  ------------------------------------------------------------------------
  -- The engine-free shared layer: flatten, MorW, GenΣ, F≈R
  ------------------------------------------------------------------------

  private module Core = FCore Symm GenF
  open Core
  open Core.F≈R

  -- the σ-engine at MorW; its wire-level driver is `Decideσ`, the
  -- front-end defines its own `Decide` below.
  open Sigma MorW

  -- the generator signature, shared by the engine modules below; `F` is its
  -- free category (HomTerm over GenF).
  private
    sig : FreeSig Symm {X}
    sig = record { GenF = GenF }
  open FreeSig sig using (module F)

  ------------------------------------------------------------------------
  -- The engine-generic shared layer, at (Symm, MorS, ⟦_⟧ᵇˢ)
  ------------------------------------------------------------------------

  private module FB = FBridge sig ES
  open FB

  ------------------------------------------------------------------------
  -- The σ-specific clauses: a box is conjugated by the canonical iso, a
  -- crossing is the σ-composite in flat coordinates.  The `cross` case of
  -- `injBox` is unreachable from `embed ∘ reflectF`, so only its
  -- well-typedness matters
  ------------------------------------------------------------------------

  private
    injBox : ∀ {a b} → MorS a b → F.HomTerm (wires a) (wires b)
    injBox (box (mk {Y} {Z} g)) = flat⇒ Z F.∘ (F.var g F.∘ flat⇐ Y)
    injBox (cross a b)          = F.merge b F.∘ (F.σ F.∘ F.split a)

    reflectVarS : ∀ {Y Z} → GenF Y Z → WTerm (flatten Y) (flatten Z)
    reflectVarS g = boxʷ (box (mk g))

    reflectσS : ∀ ⦃ s : Symm ≤ Symm ⦄ (A B : ObjTerm)
              → WTerm (flatten A ++ flatten B) (flatten B ++ flatten A)
    reflectσS A B = boxʷ (cross (flatten A) (flatten B))

  private module FBI = FB.WithInj injBox reflectVarS (λ ⦃ s ⦄ → reflectσS ⦃ s ⦄)
  open FBI

  ------------------------------------------------------------------------
  -- The σ bridge law — the only σ-specific case of bridgeF: after
  -- `F.split ∘ F.merge` cancellation the goal is braiding naturality at
  -- (flat⇒ A , flat⇒ B)
  ------------------------------------------------------------------------

  private
    bridge-σS : ∀ {A B : ObjTerm} ⦃ s : Symm ≤ Symm ⦄
              → inj (embed (reflectσS ⦃ s ⦄ A B)) F.∘ flat⇒ (A ⊗₀ B)
                F.≈Term flat⇒ (B ⊗₀ A) F.∘ F.σ ⦃ s ⦄
    bridge-σS {A} {B} ⦃ v≤v ⦄ = beginF
      inj (embed (reflectσS A B)) F.∘ (F.merge fA F.∘ (f⇒A F.⊗₁ f⇒B))
        ≈F⟨ F.≡⇒≈Term (cong₂ (λ h j → h F.∘ (F.σ F.∘ j))
                       (inj-merge fB) (inj-split fA)) F.⟩∘⟨refl ⟩
      (F.merge fB F.∘ (F.σ F.∘ F.split fA)) F.∘ (F.merge fA F.∘ (f⇒A F.⊗₁ f⇒B))
        ≈F⟨ merge-split-mid fA (F.merge fB) F.σ (f⇒A F.⊗₁ f⇒B) ⟩
      F.merge fB F.∘ (F.σ F.∘ (f⇒A F.⊗₁ f⇒B))
        ≈F⟨ F.refl⟩∘⟨ F.σ∘[f⊗g]≈[g⊗f]∘σ ⟩
      F.merge fB F.∘ ((f⇒B F.⊗₁ f⇒A) F.∘ F.σ)
        ≈F⟨ F.⟺ F.assoc ⟩
      (F.merge fB F.∘ (f⇒B F.⊗₁ f⇒A)) F.∘ F.σ ∎F
      where
        fA = flatten A ; fB = flatten B
        f⇒A = flat⇒ A ; f⇒B = flat⇒ B

  private module FBB = FBI.Bridge (λ g → refl) (λ {A} {B} ⦃ s ⦄ → bridge-σS {A} ⦃ s ⦄)
  open FBB

  ------------------------------------------------------------------------
  -- The decision procedure: reflect both sides, hand them to the
  -- σ-engine driver `decideσ?`, cancel through the bridge
  ------------------------------------------------------------------------

  module Decide
    ⦃ _ : DecEq GenΣ ⦄
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous pairs
    where

    private
      rankM : GenM → ℕ
      rankM (_ , _ , w) = Core.rankMorW rank w

      module DW = Decideσ rankM

    -- front-end decision: a hit is a genuine `_≈Term_` of the free
    -- SYMMETRIC monoidal category over the ObjTerm-arity generators.
    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r = Data.Maybe.map solveF (DW.decideσ? (reflectF l) (reflectF r))

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

  private module Core = FinSetupCore {v = Symm} C (λ ⦃ _ ⦄ → Sym) vars
  open Core public using (ObjTerm; V; unitᵒ; _⊗ᵒ_; ⟦_⟧ₒ)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    -- build the Symm front-end's decision procedure at this signature, then
    -- hand it to the variant-generic `FinSetupCore.Sig` (the `FinSig Symm arity`
    -- here and inside `Core.Sig` are the SAME `GenS`/`S`, so the types match).
    open FinSig Symm arity
    open FrontendS GenS
    open Decide rankS

    open Core.Sig arity decide?F public
