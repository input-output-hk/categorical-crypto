{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- WITNESS-DISCHARGE CHECK for the `≈M → ≅ᴴ` matrix-bridge solver `solveH!ᴹ`
-- (Solver.InterpretBridgeM).  Each test states a genuine equation in an
-- ARBITRARY target SMC `C`; the only argument to `solveH!ᴹ` is the pair of
-- free-SMC terms, and the implicit `T (is-just (findIsoᴹ ⟪f⟫ ⟪g⟫ …))` witness is
-- DISCHARGED AUTOMATICALLY — i.e. `findIsoᴹ` reduces to `just _` at typecheck
-- time, so the matrix bridge genuinely finds the iso via the cheap
-- `decideMatrixEquiv` (matrix compare) + the OPAQUE `matEquiv→hgIso`.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.APROP.Hypergraph.Solver.InterpretBridgeMTests
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Categories.APROP using (module APROP)
open import Categories.FreeMonoidal
import Categories.APROP.Hypergraph.Solver.FinSignature as FinSig
import Categories.APROP.Hypergraph.Solver.InterpretBridgeM as InterpM

private module C = SymmetricMonoidalCategory C

module Setup
  {Atom : Set} (_≟A_ : DecidableEquality Atom)
  {n : ℕ}
  (let open FreeMonoidalHelper Symm Atom using (ObjTerm))
  (arity : Fin n → ObjTerm × ObjTerm)
  (⟦_⟧ᵖ₀ : Atom → C.Obj)
  (let module FS = FinSig _≟A_ arity)
  (let module IM = InterpM FS.finSigDec)
  (let module OI = IM.ObjInterp C ⟦_⟧ᵖ₀)
  (⟦gen⟧ : (i : Fin n) → OI.⟦ FS.dom i ⟧₀ C.⇒ OI.⟦ FS.cod i ⟧₀)
  where
  open FS public using (dom; cod; gen; finSig; FinMor)
  module S = APROP finSig
  open IM public using (module Solverᴹ)
  open OI public using (⟦_⟧₀)

  morCode : ∀ {x y} → FinMor x y → ℕ
  morCode (i , _ , _) = toℕ i

  open Solverᴹ C ⟦_⟧ᵖ₀ (FS.genElim ⟦gen⟧) morCode public
  open Tgt public

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

  -- σ-naturality, through the matrix bridge: σ ∘ (p ⊗ s) ≈ (s ⊗ p) ∘ σ.
  test-σ-nat : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ (sᴹ ⊗₁ pᴹ) ∘ σ
  test-σ-nat = solveH!ᴹ (S.σ S.∘ (p S.⊗₁ s)) ((s S.⊗₁ p) S.∘ S.σ)

  -- Unit law `id ∘ p ≈ p` (one edge, nE = 1).
  test-idˡ : id ∘ pᴹ ≈ pᴹ
  test-idˡ = solveH!ᴹ (S.id S.∘ p) p

  -- σ ∘ σ ∘ (p ⊗ s) ≈ p ⊗ s.
  test-σσ-nat : σ ∘ σ ∘ (pᴹ ⊗₁ sᴹ) ≈ pᴹ ⊗₁ sᴹ
  test-σσ-nat = solveH!ᴹ (S.σ S.∘ S.σ S.∘ (p S.⊗₁ s)) (p S.⊗₁ s)

  -- Edge-free `σ ∘ σ ≈ id` (nE = 0 on both sides; exercises the empty-Fin fix).
  test-σ-invol : σ ∘ σ ≈ id {A₀ ⊗₀ A₁}
  test-σ-invol = solveH!ᴹ (S.σ S.∘ S.σ) (S.id {a₀ S.⊗₀ a₁})
