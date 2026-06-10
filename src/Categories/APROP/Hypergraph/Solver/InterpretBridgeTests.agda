{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DELIVERABLE: coherence equations discharged END-TO-END through the
-- BRIDGE-based solver `solveH!ᴮ` (Solver.InterpretBridge), whose witnessing
-- hypergraph isomorphism is produced by the canonical-form hypergraph↔matrix
-- bridge `findIsoᴮ` (Solver.MatrixBridge) — NOT the backtracking `findIso`.
--
-- Each test states a genuine equation between morphisms of an ARBITRARY target
-- symmetric monoidal category `C`; the only `solveH!ᴮ` argument is the pair of
-- free-SMC terms, and the implicit `T (is-just (findIsoᴮ ⟪f⟫ ⟪g⟫ …))` witness
-- is DISCHARGED AUTOMATICALLY — i.e. `findIsoᴮ` reduces to `just _` at
-- typecheck time, so the canonical bridge genuinely finds the iso with no
-- search.  `matIso→hgIso` does the real work; there is NO postulate in the
-- iso path.
--
-- `--without-K` (not `--safe`): the bridge brings in the matrix world.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.APROP.Hypergraph.Solver.InterpretBridgeTests
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Categories.APROP using (module APROP)
open import Categories.FreeMonoidal
import Categories.APROP.Hypergraph.Solver.FinSignature as FinSig
import Categories.APROP.Hypergraph.Solver.InterpretBridge as InterpB

private module C = SymmetricMonoidalCategory C

--------------------------------------------------------------------------------
-- Shared wiring, mirroring `InterpretTests.Setup`, but opening the BRIDGE
-- solver `Solverᴮ` (with `solveH!ᴮ`) and supplying the faithful generator code
-- `morCode = toℕ ∘ index` (each `FinMor` generator's index is its code).

module Setup
  {Atom : Set} (_≟A_ : DecidableEquality Atom)
  {n : ℕ}
  (let open FreeMonoidalHelper Symm Atom using (ObjTerm))
  (arity : Fin n → ObjTerm × ObjTerm)
  (⟦_⟧ᵖ₀ : Atom → C.Obj)
  (let module FS = FinSig _≟A_ arity)
  (let module IM = InterpB FS.finSigDec)
  (let module OI = IM.ObjInterp C ⟦_⟧ᵖ₀)
  (⟦gen⟧ : (i : Fin n) → OI.⟦ FS.dom i ⟧₀ C.⇒ OI.⟦ FS.cod i ⟧₀)
  where
  open FS public using (dom; cod; gen; finSig; FinMor)
  module S = APROP finSig
  open IM public using (module Solverᴮ)
  open OI public using (⟦_⟧₀)

  -- FAITHFUL per-generator code: a `FinMor` is `(i , _ , _)`; its index `i`
  -- (as a ℕ) is a distinct code per generator.
  morCode : ∀ {x y} → FinMor x y → ℕ
  morCode (i , _ , _) = toℕ i

  open Solverᴮ C ⟦_⟧ᵖ₀ (FS.genElim ⟦gen⟧) morCode public
  open Tgt public

--------------------------------------------------------------------------------
-- The shared three-atom alphabet (as in `InterpretTests.Atoms3`).

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
-- Configuration: two parallel generators p,q : a₀ → a₁ and s : a₁ → a₂
-- (mirrors `InterpretTests.Braiding`).  The σ-naturality test is the
-- EDGE-BEARING demonstration the bridge demos already exercise.

module Braiding (A₀ A₁ A₂ : C.Obj)
  (pᴹ qᴹ : A₀ C.⇒ A₁) (sᴹ : A₁ C.⇒ A₂)
  where

  open Atoms3 A₀ A₁ A₂

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

  -- EDGE-BEARING σ-naturality, through the bridge: σ ∘ (p ⊗ s) ≈ (s ⊗ p) ∘ σ.
  -- The `Tgt`-notation operators (`σ`/`∘`/`⊗₁`/`≈`) are definitionally the
  -- `C`-operations, so this is a genuine equation in `C`.
  test-σ-nat : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ (sᴹ ⊗₁ pᴹ) ∘ σ
  test-σ-nat = solveH!ᴮ (S.σ S.∘ (p S.⊗₁ s)) ((s S.⊗₁ p) S.∘ S.σ)

  -- EDGE-BEARING unit law `id ∘ p ≈ p` (one edge, `nE = 1`).
  test-idˡ : id ∘ pᴹ ≈ pᴹ
  test-idˡ = solveH!ᴮ (S.id S.∘ p) p

  -- EDGE-BEARING symmetry involution composed with a generator:
  -- σ ∘ σ ∘ (p ⊗ s) ≈ p ⊗ s.
  test-σσ-nat : σ ∘ σ ∘ (pᴹ ⊗₁ sᴹ) ≈ pᴹ ⊗₁ sᴹ
  test-σσ-nat = solveH!ᴮ (S.σ S.∘ S.σ S.∘ (p S.⊗₁ s)) (p S.⊗₁ s)

  -- EDGE-FREE structural law exercising the empty-`Fin` fix (`nE = 0` on both
  -- sides): the symmetry involution `σ ∘ σ ≈ id` on two atoms.  `⟪ σ ∘ σ ⟫`
  -- and `⟪ id ⟫` translate to edge-free hypergraphs, so `findIsoᴮ` is callable
  -- here ONLY because `align'` demands no uninhabited `Fin 0` edge default.
  test-σ-invol : σ ∘ σ ≈ id {A₀ ⊗₀ A₁}
  test-σ-invol = solveH!ᴮ (S.σ S.∘ S.σ) (S.id {a₀ S.⊗₀ a₁})
