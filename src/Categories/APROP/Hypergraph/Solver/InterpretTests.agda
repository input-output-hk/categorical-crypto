{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Tests for the string-diagram solver `solveH!`: discharging free-SMC
-- equations in an *arbitrary* target symmetric monoidal category `C`.
--
-- The module is parameterised by `C` alone.  Each *configuration* of atoms
-- and generators lives in its own sub-module, parameterised by the objects
-- and morphisms of `C` interpreting them, so different diagram vocabularies
-- can be exercised side by side:
--
--   * `Setup`     — shared wiring: from an atom set, an `arity` table and an
--                   index-keyed interpretation of the generators it builds the
--                   `FinSignature` and opens the solver (`solveH!`, the term
--                   language `S`, the generator constructor `gen`, and the
--                   target-category vocabulary `Tgt`).
--   * `Atoms3`    — the shared three-atom alphabet a₀ a₁ a₂ and its
--                   interpretation A₀ A₁ A₂.
--   * `Cycle3`    — generators f,g,h forming a 3-cycle; the category /
--                   monoidal structural laws.
--   * `Braiding`  — symmetry-heavy, non-trivial string-diagram equalities.
--   * `Crossings` — f, h (one in/out) and a merge g (two in, one out); one
--                   braided diagram `σ ∘ (h ⊗ g) ∘ α⇒ ∘ σ ∘ (f ⊗ id)`
--                   re-expressed along a ten-step `HomReasoning` chain in `C`
--                   (folding f into g by interchange, swapping g and h), then
--                   discharged by the solver in one line.
--
-- Each test states a genuine equation between morphisms of `C` (via `Tgt`);
-- no `⟦_⟧₁` appears, because each `Tgt`-expression is *definitionally* the
-- interpretation of the corresponding free-SMC term, and each free-SMC term
-- is written exactly once (`solveH!` finds the witnessing hypergraph iso).
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.APROP.Hypergraph.Solver.InterpretTests
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Categories.APROP using (module APROP)
open import Categories.FreeMonoidal
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.APROP.Hypergraph.Solver.FinSignature as FinSig
import Categories.APROP.Hypergraph.Solver.Interpret as Interp

private module C = SymmetricMonoidalCategory C

--------------------------------------------------------------------------------
-- Shared wiring.  Given an atom set with decidable equality, an `arity` table
-- describing the generators, an atom interpretation `⟦_⟧ᵖ₀`, and a plain
-- `Fin n`-indexed table interpreting each generator, assemble the
-- `FinSignature` and open the solver — exposing everything a configuration
-- needs: the term language `S`, the generator constructor `gen`, the target
-- vocabulary `Tgt`, and `solveH!`.
--
-- The `let`-bindings in the telescope compute the signature (`FS`), the object
-- interpretation (`OI.⟦_⟧₀`) and `dom`/`cod`, so the generator table's type
-- can be stated; the table itself is the last parameter, so a caller supplies
-- it inline with no `⟦ dom i ⟧₀`-style annotation of its own.

module Setup
  {Atom : Set} (_≟A_ : DecidableEquality Atom)
  {n : ℕ}
  (let open FreeMonoidalHelper Symm Atom using (ObjTerm))
  (arity : Fin n → ObjTerm × ObjTerm)
  (⟦_⟧ᵖ₀ : Atom → C.Obj)
  (let module FS = FinSig _≟A_ arity)
  (let module IM = Interp FS.finSigDec)
  (let module OI = IM.ObjInterp C ⟦_⟧ᵖ₀)
  (⟦gen⟧ : (i : Fin n) → OI.⟦ FS.dom i ⟧₀ C.⇒ OI.⟦ FS.cod i ⟧₀)
  where
  open FS public using (dom; cod; gen; finSig)
  module S = APROP finSig
  open IM public using (module Solver)
  open OI public using (⟦_⟧₀)
  open Solver C ⟦_⟧ᵖ₀ (FS.genElim ⟦gen⟧) public
  open Tgt public

--------------------------------------------------------------------------------
-- The shared three-atom alphabet a₀ a₁ a₂ and its interpretation A₀ A₁ A₂.

module Atoms3 (A₀ A₁ A₂ : C.Obj) where
  open FreeMonoidalHelper Symm (Fin 3) using (ObjTerm; Var) public

  a₀ a₁ a₂ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ = Var (suc (suc zero))

  ⟦_⟧ᵖ₀ : Fin 3 → C.Obj
  ⟦ zero        ⟧ᵖ₀ = A₀
  ⟦ suc zero    ⟧ᵖ₀ = A₁
  ⟦ suc (suc _) ⟧ᵖ₀ = A₂

--------------------------------------------------------------------------------
-- Configuration 1: generators f,g,h forming the 3-cycle a₀ → a₁ → a₂ → a₀.
-- The category and monoidal structural laws.

module Cycle3 (A₀ A₁ A₂ : C.Obj)
  (fᴹ : A₀ C.⇒ A₁) (gᴹ : A₁ C.⇒ A₂) (hᴹ : A₂ C.⇒ A₀)
  where

  open Atoms3 A₀ A₁ A₂

  -- Generator arities (source , target): f : a₀ → a₁, g : a₁ → a₂, h : a₂ → a₀.
  arity : Fin 3 → ObjTerm × ObjTerm
  arity zero          = a₀ , a₁
  arity (suc zero)    = a₁ , a₂
  arity (suc (suc _)) = a₂ , a₀

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero          → fᴹ
    (suc zero)    → gᴹ
    (suc (suc _)) → hᴹ)

  private
    f g h : S.HomTerm _ _
    f = S.Agen (gen zero)
    g = S.Agen (gen (suc zero))
    h = S.Agen (gen (suc (suc zero)))

  test-idˡ : id ∘ fᴹ ≈ fᴹ
  test-idˡ = solveH! (S.id S.∘ f) f

  test-assoc : (hᴹ ∘ gᴹ) ∘ fᴹ ≈ hᴹ ∘ (gᴹ ∘ fᴹ)
  test-assoc = solveH! ((h S.∘ g) S.∘ f) (h S.∘ (g S.∘ f))

  test-⊗-∘-dist : (gᴹ ∘ fᴹ) ⊗₁ (fᴹ ∘ hᴹ) ≈ (gᴹ ⊗₁ fᴹ) ∘ (fᴹ ⊗₁ hᴹ)
  test-⊗-∘-dist = solveH! ((g S.∘ f) S.⊗₁ (f S.∘ h)) ((g S.⊗₁ f) S.∘ (f S.⊗₁ h))

  test-triangle : (id ⊗₁ λ⇒) ∘ α⇒ ≈ ρ⇒ {A₀} ⊗₁ id {A₁}
  test-triangle = solveH! ((S.id S.⊗₁ S.λ⇒) S.∘ S.α⇒) (S.ρ⇒ {a₀} S.⊗₁ S.id {a₁})

--------------------------------------------------------------------------------
-- Configuration 2: two *parallel* generators p, q : a₀ → a₁ and s : a₁ → a₂.
-- Non-trivial string-diagram equalities involving the symmetry.

module Braiding (A₀ A₁ A₂ : C.Obj)
  (pᴹ qᴹ : A₀ C.⇒ A₁) (sᴹ : A₁ C.⇒ A₂)
  where

  open Atoms3 A₀ A₁ A₂

  -- p, q : a₀ → a₁ (parallel), s : a₁ → a₂.
  arity : Fin 3 → ObjTerm × ObjTerm
  arity zero          = a₀ , a₁
  arity (suc zero)    = a₀ , a₁
  arity (suc (suc _)) = a₁ , a₂

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero          → pᴹ
    (suc zero)    → qᴹ
    (suc (suc _)) → sᴹ)

  private
    p q s : S.HomTerm _ _
    p = S.Agen (gen zero)
    q = S.Agen (gen (suc zero))
    s = S.Agen (gen (suc (suc zero)))

  test-σ-invol : σ ∘ σ ≈ id {A₀ ⊗₀ A₁}
  test-σ-invol = solveH! (S.σ S.∘ S.σ) (S.id {a₀ S.⊗₀ a₁})

  test-σ-nat : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ (sᴹ ⊗₁ pᴹ) ∘ σ
  test-σ-nat = solveH! (S.σ S.∘ (p S.⊗₁ s)) ((s S.⊗₁ p) S.∘ S.σ)

  test-σ-conj : σ ∘ (pᴹ ⊗₁ qᴹ) ∘ σ ≈ qᴹ ⊗₁ pᴹ
  test-σ-conj = solveH! (S.σ S.∘ (p S.⊗₁ q) S.∘ S.σ) (q S.⊗₁ p)

  test-hexagon
    : id ⊗₁ σ ∘ α⇒ ∘ σ ⊗₁ id ≈ α⇒ ∘ σ ∘ α⇒ {A₀} {A₁} {A₂}
  test-hexagon = solveH! (S.id S.⊗₁ S.σ S.∘ S.α⇒ S.∘ S.σ S.⊗₁ S.id)
                         (S.α⇒ S.∘ S.σ S.∘ S.α⇒ {a₀} {a₁} {a₂})

  test-σ-slide
    : σ ∘ ((sᴹ ∘ pᴹ) ⊗₁ id {A₂}) ≈ (id {A₂} ⊗₁ (sᴹ ∘ pᴹ)) ∘ σ
  test-σ-slide = solveH! (S.σ S.∘ ((s S.∘ p) S.⊗₁ S.id {a₂}))
                         ((S.id {a₂} S.⊗₁ (s S.∘ p)) S.∘ S.σ)

--------------------------------------------------------------------------------
-- Configuration 3: f, g, h with g a merge

module Crossings (A₀ A₁ A₂ : C.Obj)
  (fᴹ : A₀ C.⇒ A₁) (gᴹ : (A₂ C.⊗₀ A₁) C.⇒ A₀) (hᴹ : A₁ C.⇒ A₂)
  where

  open Atoms3 A₀ A₁ A₂
  open FreeMonoidalHelper Symm (Fin 3) using (_⊗₀_)

  arity : Fin 3 → ObjTerm × ObjTerm
  arity zero          = a₀ , a₁
  arity (suc zero)    = (a₂ ⊗₀ a₁) , a₀
  arity (suc (suc _)) = a₁ , a₂

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero          → fᴹ
    (suc zero)    → gᴹ
    (suc (suc _)) → hᴹ)

  private
    f g h : S.HomTerm _ _
    f = S.Agen (gen zero)
    g = S.Agen (gen (suc zero))
    h = S.Agen (gen (suc (suc zero)))

  private module MR = MonoidalReasoning C.monoidal
  open C.HomReasoning

  byHand : σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
       C.≈ (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ)
  byHand = begin
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.braiding.⇒.commute (fᴹ , C.id) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ (id {A₁ C.⊗₀ A₂} ⊗₁ fᴹ) ∘ σ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (MR.⊗-resp-≈ˡ (⟺ C.⊗.identity) ⟩∘⟨refl) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ ((id {A₁} ⊗₁ id {A₂}) ⊗₁ fᴹ) ∘ σ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ ((α⇒ ∘ ((id {A₁} ⊗₁ id {A₂}) ⊗₁ fᴹ)) ∘ σ)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (C.assoc-commute-from ⟩∘⟨refl) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ (((id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ)) ∘ α⇒) ∘ σ)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ ((id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ)) ∘ (α⇒ ∘ σ))
        ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
      σ ∘ ((hᴹ ⊗₁ gᴹ) ∘ (id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ)
        ≈⟨ refl⟩∘⟨ ((⟺ C.⊗.homomorphism) ⟩∘⟨refl) ⟩
      σ ∘ (((hᴹ ∘ id {A₁}) ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ))
        ≈⟨ refl⟩∘⟨ ((MR.⊗-resp-≈ˡ C.identityʳ) ⟩∘⟨refl) ⟩
      σ ∘ ((hᴹ ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ))
        ≈⟨ C.sym-assoc ⟩
      (σ ∘ (hᴹ ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ)))) ∘ (α⇒ ∘ σ)
        ≈⟨ C.braiding.⇒.commute (hᴹ , gᴹ C.∘ (C.id C.⊗₁ fᴹ)) ⟩∘⟨refl ⟩
      (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ) ∎

  auto : σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
     C.≈ (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ)
  auto = solveH! (S.σ S.∘ (h S.⊗₁ g) S.∘ S.α⇒ S.∘ S.σ S.∘ (f S.⊗₁ S.id {a₁ S.⊗₀ a₂}))
                 ((((g S.∘ (S.id {a₂} S.⊗₁ f)) S.⊗₁ h) S.∘ S.σ) S.∘ (S.α⇒ S.∘ S.σ))
