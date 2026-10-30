{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Equations for the G construction, before packaging its category.
-- Keeping these statements in the base category avoids a dependency on
-- the category record whose fields they prove.
-- Certificate types use target-category equations: exposing finite-signature
-- interpretations here makes later conversion repeatedly expand the solver.
------------------------------------------------------------------------

module Categories.GConstruction.CoreProofs where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE
open import Categories.Category.Monoidal.Bundle
import Categories.Coherence.Symmetric as CS
open import Categories.FreeMonoidal using (module FreeMonoidalHelper; Symm)
open import Categories.Functor using (Functor)
import Categories.GConstruction.Core as Core
open Core using (module Wiring)
open import Data.Fin using (Fin; suc)
open import Data.Fin.Patterns
open import Data.Product
open import Data.Vec using ([]; _∷_)
open import Level
open import Relation.Binary.PropositionalEquality using (refl)

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstruction.Trace as GT

module GCoh {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (a⁺ a⁻ b⁺ b⁻ d⁺ d⁻ e⁺ e⁻ : C.Obj)
  (f₀ : (a⁺ C.⊗₀ b⁻) C.⇒ (a⁻ C.⊗₀ b⁺))
  (g₀ : (b⁺ C.⊗₀ d⁻) C.⇒ (b⁻ C.⊗₀ d⁺))
  (h₀ : (d⁺ C.⊗₀ e⁻) C.⇒ (d⁻ C.⊗₀ e⁺)) where
  private
    module Target where
      open C
      open U.Shorthands C.monoidal
      open Wiring C.symmetric

      lhs rhs : ((a⁺ ⊗₀ e⁻) ⊗₀ (d⁻ ⊗₀ d⁺)) ⊗₀ (b⁻ ⊗₀ b⁺)
              ⇒ ((a⁻ ⊗₀ e⁺) ⊗₀ (d⁻ ⊗₀ d⁺)) ⊗₀ (b⁻ ⊗₀ b⁺)
      lhs = β ∘ (α ⊗₁ id ∘ (β ∘ (α ∘ h₀ ⊗₁ g₀ ∘ γ) ⊗₁ id ∘ β) ∘ (id ⊗₁ f₀ ∘ γ) ⊗₁ id) ∘ β
      rhs = α ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ (α ∘ g₀ ⊗₁ f₀ ∘ γ) ∘ α⇒) ∘ (h₀ ⊗₁ id ∘ γ) ⊗₁ id

    open FreeMonoidalHelper Symm (Fin 8) using (ObjTerm; Var; _⊗₀_)
    A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : ObjTerm
    A⁺ = Var 0F ; A⁻ = Var 1F ; B⁺ = Var 2F ; B⁻ = Var 3F
    D⁺ = Var 4F ; D⁻ = Var 5F ; E⁺ = Var 6F ; E⁻ = Var 7F

    open CS.Solver C (a⁺ ∷ a⁻ ∷ b⁺ ∷ b⁻ ∷ d⁺ ∷ d⁻ ∷ e⁺ ∷ e⁻ ∷ [])
      (((A⁺ ⊗₀ B⁻) , (A⁻ ⊗₀ B⁺) , f₀) ∷
       ((B⁺ ⊗₀ D⁻) , (B⁻ ⊗₀ D⁺) , g₀) ∷
       ((D⁺ ⊗₀ E⁻) , (D⁻ ⊗₀ E⁺) , h₀) ∷ [])
    open S using (HomTerm; Agen; id; _∘_; _⊗₁_; α⇒; α⇐)
    open Wiring S.Symmetric-Monoidal using () renaming (α to αᵗ; β to βᵗ; γ to γᵗ)
    open import Categories.APROP.Hypergraph.Solver.Split finSig using (solveTerm!)

    f' g' h' : HomTerm _ _
    f' = Agen (gen 0F)
    g' = Agen (gen 1F)
    h' = Agen (gen 2F)

    lhsᵗ rhsᵗ : HomTerm (((A⁺ ⊗₀ E⁻) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
                        (((A⁻ ⊗₀ E⁺) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
    lhsᵗ = βᵗ ∘ (αᵗ ⊗₁ id ∘ (βᵗ ∘ (αᵗ ∘ h' ⊗₁ g' ∘ γᵗ) ⊗₁ id ∘ βᵗ) ∘ (id ⊗₁ f' ∘ γᵗ) ⊗₁ id) ∘ βᵗ
    rhsᵗ = αᵗ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ (αᵗ ∘ g' ⊗₁ f' ∘ γᵗ) ∘ α⇒) ∘ (h' ⊗₁ id ∘ γᵗ) ⊗₁ id

  abstract
    coherence : Target.lhs C.≈ Target.rhs
    coherence = Functor.F-resp-≈ freeFunctor (solveTerm! lhsᵗ rhsᵗ refl)

module ECoh {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj) where
  private
    open FreeMonoidalHelper Symm (Fin 6) using (ObjTerm; Var; _⊗₀_)
    a⁺ a⁻ b⁺ b⁻ d⁺ d⁻ : ObjTerm
    a⁺ = Var 0F ; a⁻ = Var 1F ; b⁺ = Var 2F
    b⁻ = Var 3F ; d⁺ = Var 4F ; d⁻ = Var 5F

  module L (g₀ : (A⁺ C.⊗₀ B⁻) C.⇒ (A⁻ C.⊗₀ B⁺))
           (u₀ : B⁺ C.⇒ D⁺) (v₀ : D⁻ C.⇒ B⁻) where
    private
      module Target where
        open C
        open Wiring C.symmetric
        open BProps.Shorthands C.braided
        lhs rhs : (A⁺ C.⊗₀ D⁻) C.⊗₀ (B⁻ C.⊗₀ B⁺) ⇒ (A⁻ C.⊗₀ D⁺) C.⊗₀ (B⁻ C.⊗₀ B⁺)
        lhs = α ∘ (σ⇒ ∘ u₀ ⊗₁ v₀) ⊗₁ g₀ ∘ γ
        rhs = (id ⊗₁ u₀) ⊗₁ id ∘ (α ∘ σ⇒ ⊗₁ g₀ ∘ γ) ∘ (id ⊗₁ v₀) ⊗₁ id

      module P = CS.Solver C (A⁺ ∷ A⁻ ∷ B⁺ ∷ B⁻ ∷ D⁺ ∷ D⁻ ∷ [])
        (((a⁺ ⊗₀ b⁻) , (a⁻ ⊗₀ b⁺) , g₀) ∷ (b⁺ , d⁺ , u₀) ∷ (d⁻ , b⁻ , v₀) ∷ [])
      open P.S using (HomTerm; Agen; id; _∘_; _⊗₁_; σ)
      open Wiring P.S.Symmetric-Monoidal using () renaming (α to αᵗ; γ to γᵗ)
      g : HomTerm (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
      g = Agen (P.gen 0F)
      u : HomTerm b⁺ d⁺
      u = Agen (P.gen 1F)
      v : HomTerm d⁻ b⁻
      v = Agen (P.gen 2F)
      lhs rhs : HomTerm ((a⁺ ⊗₀ d⁻) ⊗₀ (b⁻ ⊗₀ b⁺)) ((a⁻ ⊗₀ d⁺) ⊗₀ (b⁻ ⊗₀ b⁺))
      lhs = αᵗ ∘ (σ ∘ u ⊗₁ v) ⊗₁ g ∘ γᵗ
      rhs = (id ⊗₁ u) ⊗₁ id ∘ (αᵗ ∘ σ ⊗₁ g ∘ γᵗ) ∘ (id ⊗₁ v) ⊗₁ id

    abstract
      AL : Target.lhs C.≈ Target.rhs
      AL = P.solveH! lhs rhs

  module R (f₀ : (B⁺ C.⊗₀ D⁻) C.⇒ (B⁻ C.⊗₀ D⁺))
           (p₀ : A⁺ C.⇒ B⁺) (q₀ : B⁻ C.⇒ A⁻) where
    private
      module Target where
        open C
        open Wiring C.symmetric
        open BProps.Shorthands C.braided
        lhs rhs : (A⁺ C.⊗₀ D⁻) C.⊗₀ (B⁻ C.⊗₀ B⁺) ⇒ (A⁻ C.⊗₀ D⁺) C.⊗₀ (B⁻ C.⊗₀ B⁺)
        lhs = α ∘ f₀ ⊗₁ (σ⇒ ∘ p₀ ⊗₁ q₀) ∘ γ
        rhs = (q₀ ⊗₁ id) ⊗₁ id ∘ (α ∘ f₀ ⊗₁ σ⇒ ∘ γ) ∘ (p₀ ⊗₁ id) ⊗₁ id

      module P = CS.Solver C (A⁺ ∷ A⁻ ∷ B⁺ ∷ B⁻ ∷ D⁺ ∷ D⁻ ∷ [])
        (((b⁺ ⊗₀ d⁻) , (b⁻ ⊗₀ d⁺) , f₀) ∷ (a⁺ , b⁺ , p₀) ∷ (b⁻ , a⁻ , q₀) ∷ [])
      open P.S using (HomTerm; Agen; id; _∘_; _⊗₁_; σ)
      open Wiring P.S.Symmetric-Monoidal using () renaming (α to αᵗ; γ to γᵗ)
      f : HomTerm (b⁺ ⊗₀ d⁻) (b⁻ ⊗₀ d⁺)
      f = Agen (P.gen 0F)
      p : HomTerm a⁺ b⁺
      p = Agen (P.gen 1F)
      q : HomTerm b⁻ a⁻
      q = Agen (P.gen 2F)
      lhs rhs : HomTerm ((a⁺ ⊗₀ d⁻) ⊗₀ (b⁻ ⊗₀ b⁺)) ((a⁻ ⊗₀ d⁺) ⊗₀ (b⁻ ⊗₀ b⁺))
      lhs = αᵗ ∘ f ⊗₁ (σ ∘ p ⊗₁ q) ∘ γᵗ
      rhs = (q ⊗₁ id) ⊗₁ id ∘ (αᵗ ∘ f ⊗₁ σ ∘ γᵗ) ∘ (p ⊗₁ id) ⊗₁ id

    abstract
      AR : Target.lhs C.≈ Target.rhs
      AR = P.solveH! lhs rhs

-- Keep the target-category statement: exposing the finite interpretation here
-- makes conversion at homomorphismᴳ exhaust 6 GiB.
module HCoh {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻ : C.Obj)
  (f₀  : (A⁺ C.⊗₀ B⁻) C.⇒ (A⁻ C.⊗₀ B⁺))
  (f₀′ : (B⁺ C.⊗₀ D⁻) C.⇒ (B⁻ C.⊗₀ D⁺))
  (g₀  : (P⁺ C.⊗₀ Q⁻) C.⇒ (P⁻ C.⊗₀ Q⁺))
  (g₀′ : (Q⁺ C.⊗₀ R⁻) C.⇒ (Q⁻ C.⊗₀ R⁺)) where
  private
    module Target where
      open C
      open Wiring C.symmetric
      lhs rhs : ((A⁺ ⊗₀ P⁺) ⊗₀ (D⁻ ⊗₀ R⁻)) ⊗₀ ((B⁻ ⊗₀ B⁺) ⊗₀ (Q⁻ ⊗₀ Q⁺))
              ⇒ ((A⁻ ⊗₀ P⁻) ⊗₀ (D⁺ ⊗₀ R⁺)) ⊗₀ ((B⁻ ⊗₀ B⁺) ⊗₀ (Q⁻ ⊗₀ Q⁺))
      lhs = mid ⊗₁ id ∘ (mid ∘ (α ∘ f₀′ ⊗₁ f₀ ∘ γ) ⊗₁ (α ∘ g₀′ ⊗₁ g₀ ∘ γ) ∘ mid) ∘ mid ⊗₁ id
      rhs = id ⊗₁ mid ∘ (α ∘ (mid ∘ f₀′ ⊗₁ g₀′ ∘ mid) ⊗₁ (mid ∘ f₀ ⊗₁ g₀ ∘ mid) ∘ γ) ∘ id ⊗₁ mid

    pattern 10F = suc 9F
    pattern 11F = suc 10F
    open FreeMonoidalHelper Symm (Fin 12) using (ObjTerm; Var; _⊗₀_)
    a⁺ a⁻ b⁺ b⁻ d⁺ d⁻ p⁺ p⁻ q⁺ q⁻ r⁺ r⁻ : ObjTerm
    a⁺ = Var 0F  ; a⁻ = Var 1F  ; b⁺ = Var 2F  ; b⁻ = Var 3F
    d⁺ = Var 4F  ; d⁻ = Var 5F  ; p⁺ = Var 6F  ; p⁻ = Var 7F
    q⁺ = Var 8F  ; q⁻ = Var 9F  ; r⁺ = Var 10F ; r⁻ = Var 11F

    module P = CS.Solver C (A⁺ ∷ A⁻ ∷ B⁺ ∷ B⁻ ∷ D⁺ ∷ D⁻ ∷ P⁺ ∷ P⁻ ∷ Q⁺ ∷ Q⁻ ∷ R⁺ ∷ R⁻ ∷ [])
      (((a⁺ ⊗₀ b⁻) , (a⁻ ⊗₀ b⁺) , f₀) ∷ ((b⁺ ⊗₀ d⁻) , (b⁻ ⊗₀ d⁺) , f₀′) ∷
       ((p⁺ ⊗₀ q⁻) , (p⁻ ⊗₀ q⁺) , g₀) ∷ ((q⁺ ⊗₀ r⁻) , (q⁻ ⊗₀ r⁺) , g₀′) ∷ [])
    open P.S using (HomTerm; Agen; id; _∘_; _⊗₁_)
    open Wiring P.S.Symmetric-Monoidal using () renaming (α to αᵗ; γ to γᵗ; mid to midᵗ)
    open import Categories.APROP.Hypergraph.Solver.Split P.finSig using (solveTerm!)
    X Y W W′ : ObjTerm
    X = b⁻ ⊗₀ b⁺                  ; Y  = q⁻ ⊗₀ q⁺
    W = (a⁺ ⊗₀ p⁺) ⊗₀ (d⁻ ⊗₀ r⁻) ; W′ = (a⁻ ⊗₀ p⁻) ⊗₀ (d⁺ ⊗₀ r⁺)
    f : HomTerm (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
    f = Agen (P.gen 0F)
    f′ : HomTerm (b⁺ ⊗₀ d⁻) (b⁻ ⊗₀ d⁺)
    f′ = Agen (P.gen 1F)
    g : HomTerm (p⁺ ⊗₀ q⁻) (p⁻ ⊗₀ q⁺)
    g = Agen (P.gen 2F)
    g′ : HomTerm (q⁺ ⊗₀ r⁻) (q⁻ ⊗₀ r⁺)
    g′ = Agen (P.gen 3F)
    lhs rhs : HomTerm (W ⊗₀ (X ⊗₀ Y)) (W′ ⊗₀ (X ⊗₀ Y))
    lhs = midᵗ ⊗₁ id ∘ (midᵗ ∘ (αᵗ ∘ f′ ⊗₁ f ∘ γᵗ) ⊗₁ (αᵗ ∘ g′ ⊗₁ g ∘ γᵗ) ∘ midᵗ) ∘ midᵗ ⊗₁ id
    rhs = id ⊗₁ midᵗ ∘ (αᵗ ∘ (midᵗ ∘ f′ ⊗₁ g′ ∘ midᵗ) ⊗₁ (midᵗ ∘ f ⊗₁ g ∘ midᵗ) ∘ γᵗ) ∘ id ⊗₁ midᵗ

  abstract
    HOM : Target.lhs C.≈ Target.rhs
    HOM = Functor.F-resp-≈ P.freeFunctor (solveTerm! lhs rhs refl)

module ICoh {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (x⁺ x⁻ y⁺ y⁻ u : C.Obj)
  (f₀ : (x⁺ C.⊗₀ y⁻) C.⇒ (x⁻ C.⊗₀ y⁺)) where
  private
    module Target where
      open C
      open Wiring C.symmetric
      open U.Shorthands C.monoidal
      open BProps.Shorthands C.braided
      hL : ∀ {W} → (x⁺ ⊗₀ W) ⊗₀ y⁻ ⇒ (x⁻ ⊗₀ W) ⊗₀ y⁺
      hL = β ∘ f₀ ⊗₁ id ∘ β
      PR : (x⁺ ⊗₀ y⁻) ⊗₀ x⁻ ⇒ (y⁻ ⊗₀ x⁻) ⊗₀ x⁺
      PR = β ∘ σ⇒ ⊗₁ id
      mR : (y⁻ ⊗₀ x⁻) ⊗₀ x⁺ ⇒ (x⁻ ⊗₀ y⁺) ⊗₀ x⁻
      mR = (β ∘ σ⇒ ⊗₁ id ∘ β) ∘ f₀ ⊗₁ id ∘ (σ⇒ ⊗₁ id ∘ β)
      C1L-lhs C1L-rhs : ((x⁺ ⊗₀ y⁻) ⊗₀ y⁻) ⊗₀ y⁺ ⇒ ((x⁻ ⊗₀ y⁺) ⊗₀ y⁻) ⊗₀ y⁺
      C1L-lhs = α⇐ ∘ (α ∘ σ⇒ ⊗₁ f₀ ∘ γ) ∘ α⇒
      C1L-rhs = (β ⊗₁ id ∘ β) ∘ hL ⊗₁ id
      C1R-lhs C1R-rhs : ((x⁺ ⊗₀ y⁻) ⊗₀ x⁻) ⊗₀ x⁺ ⇒ ((x⁻ ⊗₀ y⁺) ⊗₀ x⁻) ⊗₀ x⁺
      C1R-lhs = α⇐ ∘ (α ∘ f₀ ⊗₁ σ⇒ ∘ γ) ∘ α⇒
      C1R-rhs = mR ⊗₁ id ∘ β ∘ PR ⊗₁ id
      C3R-lhs C3R-rhs : (x⁺ ⊗₀ y⁻) ⊗₀ x⁻ ⇒ (x⁻ ⊗₀ y⁺) ⊗₀ x⁻
      C3R-lhs = mR ∘ PR
      C3R-rhs = (σ⇒ ⊗₁ id ∘ β) ∘ (σ⇒ ∘ f₀) ⊗₁ id
      RS-lhs RS-rhs : (x⁺ ⊗₀ u) ⊗₀ y⁻ ⇒ (x⁻ ⊗₀ u) ⊗₀ y⁺
      RS-lhs = σ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ f₀ ∘ α⇒) ∘ σ⇒ ⊗₁ id
      RS-rhs = hL

    open FreeMonoidalHelper Symm (Fin 5) using (ObjTerm; Var; _⊗₀_)
    a⁺ a⁻ b⁺ b⁻ y : ObjTerm
    a⁺ = Var 0F ; a⁻ = Var 1F ; b⁺ = Var 2F ; b⁻ = Var 3F ; y = Var 4F
    module P = CS.Solver C (x⁺ ∷ x⁻ ∷ y⁺ ∷ y⁻ ∷ u ∷ [])
      (((a⁺ ⊗₀ b⁻) , (a⁻ ⊗₀ b⁺) , f₀) ∷ [])
    open P.S using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐)
    open Wiring P.S.Symmetric-Monoidal using () renaming (α to αᵗ; β to βᵗ; γ to γᵗ)
    f' : HomTerm (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
    f' = Agen (P.gen 0F)
    hLᵗ : ∀ {W} → HomTerm ((a⁺ ⊗₀ W) ⊗₀ b⁻) ((a⁻ ⊗₀ W) ⊗₀ b⁺)
    hLᵗ = βᵗ ∘ f' ⊗₁ id ∘ βᵗ
    PRᵗ : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ a⁻) ((b⁻ ⊗₀ a⁻) ⊗₀ a⁺)
    PRᵗ = βᵗ ∘ σ ⊗₁ id
    mRᵗ : HomTerm ((b⁻ ⊗₀ a⁻) ⊗₀ a⁺) ((a⁻ ⊗₀ b⁺) ⊗₀ a⁻)
    mRᵗ = (βᵗ ∘ σ ⊗₁ id ∘ βᵗ) ∘ f' ⊗₁ id ∘ (σ ⊗₁ id ∘ βᵗ)
    C1Lᵗ-lhs C1Lᵗ-rhs : HomTerm (((a⁺ ⊗₀ b⁻) ⊗₀ b⁻) ⊗₀ b⁺) (((a⁻ ⊗₀ b⁺) ⊗₀ b⁻) ⊗₀ b⁺)
    C1Lᵗ-lhs = α⇐ ∘ (αᵗ ∘ σ ⊗₁ f' ∘ γᵗ) ∘ α⇒
    C1Lᵗ-rhs = (βᵗ ⊗₁ id ∘ βᵗ) ∘ hLᵗ ⊗₁ id
    C1Rᵗ-lhs C1Rᵗ-rhs : HomTerm (((a⁺ ⊗₀ b⁻) ⊗₀ a⁻) ⊗₀ a⁺) (((a⁻ ⊗₀ b⁺) ⊗₀ a⁻) ⊗₀ a⁺)
    C1Rᵗ-lhs = α⇐ ∘ (αᵗ ∘ f' ⊗₁ σ ∘ γᵗ) ∘ α⇒
    C1Rᵗ-rhs = mRᵗ ⊗₁ id ∘ βᵗ ∘ PRᵗ ⊗₁ id
    C3Rᵗ-lhs C3Rᵗ-rhs : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ a⁻) ((a⁻ ⊗₀ b⁺) ⊗₀ a⁻)
    C3Rᵗ-lhs = mRᵗ ∘ PRᵗ
    C3Rᵗ-rhs = (σ ⊗₁ id ∘ βᵗ) ∘ (σ ∘ f') ⊗₁ id
    RSᵗ-lhs RSᵗ-rhs : HomTerm ((a⁺ ⊗₀ y) ⊗₀ b⁻) ((a⁻ ⊗₀ y) ⊗₀ b⁺)
    RSᵗ-lhs = σ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ f' ∘ α⇒) ∘ σ ⊗₁ id
    RSᵗ-rhs = hLᵗ

  abstract
    C1L : Target.C1L-lhs C.≈ Target.C1L-rhs
    C1L = P.solveH! C1Lᵗ-lhs C1Lᵗ-rhs
    C1R : Target.C1R-lhs C.≈ Target.C1R-rhs
    C1R = P.solveH! C1Rᵗ-lhs C1Rᵗ-rhs
    C3R : Target.C3R-lhs C.≈ Target.C3R-rhs
    C3R = P.solveH! C3Rᵗ-lhs C3Rᵗ-rhs
    RS : Target.RS-lhs C.≈ Target.RS-rhs
    RS = P.solveH! RSᵗ-lhs RSᵗ-rhs

module TCoh {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (A A′ B B′ X Y : C.Obj)
  (u₀ : (A C.⊗₀ X) C.⇒ (B C.⊗₀ X))
  (v₀ : (A′ C.⊗₀ Y) C.⇒ (B′ C.⊗₀ Y)) where
  private
    module Target where
      open C
      open Wiring C.symmetric
      open U.Shorthands C.monoidal
      lhs rhs : ((A ⊗₀ A′) ⊗₀ X) ⊗₀ Y ⇒ ((B ⊗₀ B′) ⊗₀ X) ⊗₀ Y
      lhs = (β ∘ u₀ ⊗₁ id ∘ β) ⊗₁ id ∘ β
            ∘ (α⇐ ∘ id ⊗₁ v₀ ∘ α⇒) ⊗₁ id ∘ β
      rhs = α⇐ ∘ (mid ∘ u₀ ⊗₁ v₀ ∘ mid) ∘ α⇒

    open FreeMonoidalHelper Symm (Fin 6) using (ObjTerm; Var; _⊗₀_)
    a b a′ b′ x y : ObjTerm
    a = Var 0F ; b = Var 1F ; a′ = Var 2F
    b′ = Var 3F ; x = Var 4F ; y = Var 5F
    module P = CS.Solver C (A ∷ B ∷ A′ ∷ B′ ∷ X ∷ Y ∷ [])
      (((a ⊗₀ x) , (b ⊗₀ x) , u₀) ∷ ((a′ ⊗₀ y) , (b′ ⊗₀ y) , v₀) ∷ [])
    open P.S using (HomTerm; Agen; id; _∘_; _⊗₁_; α⇒; α⇐)
    open Wiring P.S.Symmetric-Monoidal using () renaming (β to βᵗ; mid to midᵗ)
    u : HomTerm (a ⊗₀ x) (b ⊗₀ x)
    u = Agen (P.gen 0F)
    v : HomTerm (a′ ⊗₀ y) (b′ ⊗₀ y)
    v = Agen (P.gen 1F)
    lhs rhs : HomTerm (((a ⊗₀ a′) ⊗₀ x) ⊗₀ y) (((b ⊗₀ b′) ⊗₀ x) ⊗₀ y)
    lhs = (βᵗ ∘ u ⊗₁ id ∘ βᵗ) ⊗₁ id ∘ βᵗ
          ∘ (α⇐ ∘ id ⊗₁ v ∘ α⇒) ⊗₁ id ∘ βᵗ
    rhs = α⇐ ∘ (midᵗ ∘ u ⊗₁ v ∘ midᵗ) ∘ α⇒

  TM : Target.lhs C.≈ Target.rhs
  TM = P.solveH! lhs rhs

module _ {a b c} (C : Category a b c) (M : Monoidal C) (T : Traced M) where

  open Category C
  open Traced T
  open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric using (β-β)
  open U M using (triangle-inv; pentagon-inv)
  open U.Shorthands M
  open import Categories.Category.Monoidal.Reasoning M
    using (serialize₁₂; serialize₂₁; ⊗-distrib-over-∘; _⟩⊗⟨_)
  open import Categories.Morphism.Reasoning C
    using (introˡ; pullˡ; pullʳ; pushˡ; elimˡ; elimʳ; cancelˡ; cancelʳ)
  open BProps.Shorthands braided
  private module W = GT C M T
  open W using (α; β; γ; Cˢ; mid; mid-σ; mid-natural; mid-involutive; mid-unitˡ; mid-unitʳ; mid-assoc;
                trace-βyank; trace-gyank; trace-mid)
  open HomReasoning

  open Core.Construction C M T
  opaque
    unfolding composeᴳ

    composeᴳ-raw : ∀ {A B D} {f : B ⇒ᴳ D} {g : A ⇒ᴳ B} →
                   composeᴳ f g ≈ trace (α ∘ f ⊗₁ g ∘ γ)
    composeᴳ-raw = Equiv.refl

  ⌜⌝-resp-≈ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} {u u' : A⁺ ⇒ B⁺} {v v' : B⁻ ⇒ A⁻} →
              u ≈ u' → v ≈ v' → ⌜ u , v ⌝ ≈ ⌜ u' , v' ⌝
  ⌜⌝-resp-≈ e₁ e₂ = refl⟩∘⟨ (e₁ ⟩⊗⟨ e₂)

  opaque
    unfolding _⊗₁ᴳ_

    ⊗₁ᴳ-resp-≈ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Obj}
                   {f f' : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺}
                   {g g' : D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺} →
                 f ≈ f' → g ≈ g' → f ⊗₁ᴳ g ≈ f' ⊗₁ᴳ g'
    ⊗₁ᴳ-resp-≈ e₁ e₂ = refl⟩∘⟨ ((e₁ ⟩⊗⟨ e₂) ⟩∘⟨refl)

    ⌜⌝-⊗ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Obj}
             {u : A⁺ ⇒ B⁺} {v : B⁻ ⇒ A⁻} {p : D⁺ ⇒ E⁺} {q : E⁻ ⇒ D⁻} →
           ⌜ u , v ⌝ ⊗₁ᴳ ⌜ p , q ⌝ ≈ ⌜ u ⊗₁ p , v ⊗₁ q ⌝
    ⌜⌝-⊗ = refl⟩∘⟨ (⊗-distrib-over-∘ ⟩∘⟨refl)
         ○ pullˡ (pullˡ mid-σ)
         ○ (pullʳ mid-natural ⟩∘⟨refl)
         ○ assoc
         ○ refl⟩∘⟨ cancelʳ mid-involutive

  module _ where

    open TE T

    right-superposing : ∀ {X Y A' B'} {f' : A' ⊗₀ X ⇒ B' ⊗₀ X} →
      trace f' ⊗₁ id {Y} ≈ trace (β ∘ f' ⊗₁ id ∘ β)
    right-superposing {X} {Y} {A'} {B'} {f'} = begin
      trace f' ⊗₁ id
        ≈⟨ introˡ commutative ○ pullʳ (braiding.⇒.commute _) ⟩
      σ⇒ ∘ id ⊗₁ trace f' ∘ σ⇒
        ≈⟨ refl⟩∘⟨ Equiv.sym superposing ⟩∘⟨refl ⟩
      σ⇒ ∘ trace (α⇐ ∘ id ⊗₁ f' ∘ α⇒) ∘ σ⇒
        ≈⟨ refl⟩∘⟨ ⟺ tightenᵣ ⟩
      σ⇒ ∘ trace ((α⇐ ∘ id ⊗₁ f' ∘ α⇒) ∘ σ⇒ ⊗₁ id)
        ≈⟨ ⟺ tightenₗ ⟩
      trace (σ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ f' ∘ α⇒) ∘ σ⇒ ⊗₁ id)
        ≈⟨ trace-resp-≈ (ICoh.RS Cˢ A' B' X X Y f') ⟩
      trace (β ∘ f' ⊗₁ id ∘ β) ∎

    ⊗-trace-mid : ∀ {X Y A A' B B' : Obj}
                    {u : A ⊗₀ X ⇒ B ⊗₀ X} {v : A' ⊗₀ Y ⇒ B' ⊗₀ Y} →
                  trace u ⊗₁ trace v ≈ trace (mid ∘ u ⊗₁ v ∘ mid)
    ⊗-trace-mid {X} {Y} {A} {A'} {B} {B'} {u} {v} =
      serialize₁₂
      ○ (right-superposing ⟩∘⟨ Equiv.sym superposing)
      ○ ⟺ tightenᵣ
      ○ trace-resp-≈ (refl⟩∘⟨ right-superposing)
      ○ trace-resp-≈ (⟺ tightenₗ)
      ○ trace-resp-≈ (trace-resp-≈ (TCoh.TM Cˢ A A' B B' X Y u v))
      ○ vanishing₂

    opaque
      unfolding composeᴳ

      compose-resp-≈ : ∀ {A B D} {f h : B ⇒ᴳ D} {g i : A ⇒ᴳ B}
                     → f ≈ h → g ≈ i → composeᴳ f g ≈ composeᴳ h i
      compose-resp-≈ p q = trace-resp-≈ (refl⟩∘⟨ ((p ⟩⊗⟨ q) ⟩∘⟨refl))

      identityˡ' : ∀ {A B} {f : A ⇒ᴳ B} → composeᴳ σ⇒ f ≈ f
      -- Vanishing splits the two-wire loop; coherence exposes framed yanks.
      identityˡ' {A} {B} {f} =
        ⟺ (vanishing₂ {X = proj₂ B} {Y = proj₁ B})
        ○ trace-resp-≈ (trace-resp-≈ ICW.C1L ○ tightenᵣ
                        ○ (trace-gyank ⟩∘⟨refl) ○ cancelˡ β-β)
        ○ trace-gyank
        where
          module ICW = ICoh Cˢ
            (proj₁ A) (proj₂ A) (proj₁ B) (proj₂ B) (proj₁ A) f

      identityʳ' : ∀ {A B} {f : A ⇒ᴳ B} → composeᴳ f σ⇒ ≈ f
      identityʳ' {A} {B} {f} =
        ⟺ (vanishing₂ {X = proj₂ A} {Y = proj₁ A})
        ○ trace-resp-≈ (trace-resp-≈ ICW.C1R ○ tightenₗ
                        ○ (refl⟩∘⟨ (tightenᵣ ○ elimˡ trace-βyank))
                        ○ ICW.C3R)
        ○ tightenᵣ ○ (trace-gyank ⟩∘⟨refl)
        ○ cancelˡ commutative
        where
          module ICW = ICoh Cˢ
            (proj₁ A) (proj₂ A) (proj₁ B) (proj₂ B) (proj₁ A) f

      assoc' : ∀ {A B D E} {f : A ⇒ᴳ B} {g : B ⇒ᴳ D} {h : D ⇒ᴳ E}
             → composeᴳ (composeᴳ h g) f ≈ composeᴳ h (composeᴳ g f)
      -- Expose both loops, exchange them by Fubini, then compare their bodies
      -- by symmetric coherence before undoing naturality and superposing.
      assoc' {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} {E⁺ , E⁻} {f} {g} {h} =
        trace-resp-≈ (refl⟩∘⟨ pushˡ serialize₁₂)
        ○ trace-resp-≈ (refl⟩∘⟨ right-superposing ⟩∘⟨refl)
        ○ trace-resp-≈ (refl⟩∘⟨ ⟺ tightenᵣ)
        ○ trace-resp-≈ (⟺ tightenₗ)
        ○ trace-comm
        ○ trace-resp-≈ (trace-resp-≈
            (GCoh.coherence Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ f g h))
        ○ trace-resp-≈ tightenₗ
        ○ trace-resp-≈ (refl⟩∘⟨ tightenᵣ)
        ○ trace-resp-≈ (refl⟩∘⟨ superposing ⟩∘⟨refl)
        ○ trace-resp-≈ (refl⟩∘⟨ pullˡ (⟺ serialize₂₁))

    ⌜⌝-id : ∀ {A⁺ A⁻ : Obj} → ⌜ id , id ⌝ ≈ σ⇒ {A⁺} {A⁻}
    ⌜⌝-id = elimʳ ⊗.identity

    opaque
      unfolding composeᴳ

      absorbˡ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} {u : B⁺ ⇒ D⁺} {v : D⁻ ⇒ B⁻}
                  {g : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
                composeᴳ ⌜ u , v ⌝ g ≈ id ⊗₁ u ∘ g ∘ id ⊗₁ v
      absorbˡ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {u} {v} {g} =
        trace-resp-≈ (ECoh.L.AL Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ g u v)
        ○ tightenₗ
        ○ (refl⟩∘⟨ tightenᵣ)
        ○ (refl⟩∘⟨ (identityˡ' ⟩∘⟨refl))

      absorbʳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} {p : A⁺ ⇒ B⁺} {q : B⁻ ⇒ A⁻}
                  {f : B⁺ ⊗₀ D⁻ ⇒ B⁻ ⊗₀ D⁺} →
                composeᴳ f ⌜ p , q ⌝ ≈ q ⊗₁ id ∘ f ∘ p ⊗₁ id
      absorbʳ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {p} {q} {f} =
        trace-resp-≈ (ECoh.R.AR Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ f p q)
        ○ tightenₗ
        ○ (refl⟩∘⟨ tightenᵣ)
        ○ (refl⟩∘⟨ (identityʳ' ⟩∘⟨refl))

    ⌜⌝-∘ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} {u : B⁺ ⇒ D⁺} {v : D⁻ ⇒ B⁻}
             {p : A⁺ ⇒ B⁺} {q : B⁻ ⇒ A⁻} →
           composeᴳ ⌜ u , v ⌝ ⌜ p , q ⌝ ≈ ⌜ u ∘ p , q ∘ v ⌝
    ⌜⌝-∘ {u = u} = absorbˡ ○ (refl⟩∘⟨ assoc)
      ○ pullˡ (⟺ (braiding.⇒.commute (u , id))) ○ assoc
      ○ (refl⟩∘⟨ (refl⟩∘⟨ ⟺ ⊗-distrib-over-∘))
      ○ (refl⟩∘⟨ ⟺ ⊗-distrib-over-∘)
      ○ (refl⟩∘⟨ (refl⟩∘⟨ identityʳ) ⟩⊗⟨ identityˡ)

    ⌜⌝-⊗ˡ : ∀ {A⁺ A⁻ D⁺ D⁻ E⁺ E⁻ : Obj} {p : D⁺ ⇒ E⁺} {q : E⁻ ⇒ D⁻} →
            σ⇒ {A⁺} {A⁻} ⊗₁ᴳ ⌜ p , q ⌝ ≈ ⌜ id ⊗₁ p , id ⊗₁ q ⌝
    ⌜⌝-⊗ˡ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) Equiv.refl ○ ⌜⌝-⊗

    ⌜⌝-⊗ʳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} {u : A⁺ ⇒ B⁺} {v : B⁻ ⇒ A⁻} →
            ⌜ u , v ⌝ ⊗₁ᴳ σ⇒ {D⁺} {D⁻} ≈ ⌜ u ⊗₁ id , v ⊗₁ id ⌝
    ⌜⌝-⊗ʳ = ⊗₁ᴳ-resp-≈ Equiv.refl (⟺ ⌜⌝-id) ○ ⌜⌝-⊗

    identityᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} → σ⇒ {A⁺} {A⁻} ⊗₁ᴳ σ⇒ {B⁺} {B⁻} ≈ σ⇒
    identityᴳ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) (⟺ ⌜⌝-id)
              ○ ⌜⌝-⊗ ○ ⌜⌝-resp-≈ ⊗.identity ⊗.identity ○ ⌜⌝-id

    opaque
      unfolding _⊗₁ᴳ_ composeᴳ

      homomorphismᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻ : Obj}
                        {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺}
                        {f′ : B⁺ ⊗₀ D⁻ ⇒ B⁻ ⊗₀ D⁺}
                        {g : P⁺ ⊗₀ Q⁻ ⇒ P⁻ ⊗₀ Q⁺}
                        {g′ : Q⁺ ⊗₀ R⁻ ⇒ Q⁻ ⊗₀ R⁺} →
                      composeᴳ {A⁺ , A⁻} {B⁺ , B⁻} f′ f
                        ⊗₁ᴳ composeᴳ {P⁺ , P⁻} g′ g
                        ≈ composeᴳ {A⁺ ⊗₀ P⁺ , A⁻ ⊗₀ P⁻}
                                    {B⁺ ⊗₀ Q⁺ , B⁻ ⊗₀ Q⁻}
                                    (f′ ⊗₁ᴳ g′) (f ⊗₁ᴳ g)
      homomorphismᴳ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {P⁺} {P⁻} {Q⁺} {Q⁻} {R⁺} {R⁻}
                    {f} {f′} {g} {g′} =
        (refl⟩∘⟨ (⊗-trace-mid ⟩∘⟨refl))
        ○ (refl⟩∘⟨ ⟺ tightenᵣ) ○ ⟺ tightenₗ
        ○ trace-resp-≈
            (HCoh.HOM Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻ f f′ g g′)
        ○ ⟺ trace-mid

    opaque
      unfolding _⊗₁ᴳ_ composeᴳ

      triangleᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} →
                  composeᴳ (σ⇒ {A⁺} {A⁻} ⊗₁ᴳ ⌜ λ⇒ , λ⇐ ⌝) ⌜ α⇒ , α⇐ ⌝
                    ≈ ⌜ ρ⇒ , ρ⇐ ⌝ ⊗₁ᴳ σ⇒ {B⁺} {B⁻}
      triangleᴳ = compose-resp-≈ ⌜⌝-⊗ˡ Equiv.refl
                ○ ⌜⌝-∘ ○ ⌜⌝-resp-≈ triangle triangle-inv ○ ⟺ ⌜⌝-⊗ʳ

      pentagonᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Obj} →
                  composeᴳ (σ⇒ {A⁺} {A⁻} ⊗₁ᴳ ⌜ α⇒ {B⁺} {D⁺} , α⇐ {B⁻} {D⁻} ⌝)
                           (composeᴳ ⌜ α⇒ , α⇐ ⌝ (⌜ α⇒ , α⇐ ⌝ ⊗₁ᴳ σ⇒ {E⁺} {E⁻}))
                    ≈ composeᴳ ⌜ α⇒ {A⁺} , α⇐ ⌝ ⌜ α⇒ , α⇐ ⌝
      pentagonᴳ = compose-resp-≈ ⌜⌝-⊗ˡ (compose-resp-≈ Equiv.refl ⌜⌝-⊗ʳ ○ ⌜⌝-∘)
                ○ ⌜⌝-∘ ○ ⌜⌝-resp-≈ pentagon pentagon-inv ○ ⟺ ⌜⌝-∘

      unitorˡ-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
                         composeᴳ ⌜ λ⇒ , λ⇐ ⌝ (σ⇒ ⊗₁ᴳ f) ≈ composeᴳ f ⌜ λ⇒ , λ⇐ ⌝
      unitorˡ-commuteᴳ = absorbˡ ○ mid-unitˡ ○ ⟺ absorbʳ

      unitorʳ-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
                         composeᴳ ⌜ ρ⇒ , ρ⇐ ⌝ (f ⊗₁ᴳ σ⇒) ≈ composeᴳ f ⌜ ρ⇒ , ρ⇐ ⌝
      unitorʳ-commuteᴳ = absorbˡ ○ mid-unitʳ ○ ⟺ absorbʳ

      assoc-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ : Obj}
                         {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺}
                         {g : D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺}
                         {h : P⁺ ⊗₀ Q⁻ ⇒ P⁻ ⊗₀ Q⁺} →
                       composeᴳ ⌜ α⇒ , α⇐ ⌝ ((f ⊗₁ᴳ g) ⊗₁ᴳ h)
                         ≈ composeᴳ (f ⊗₁ᴳ (g ⊗₁ᴳ h)) ⌜ α⇒ , α⇐ ⌝
      assoc-commuteᴳ = absorbˡ ○ mid-assoc ○ ⟺ absorbʳ
