{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Interchange equations and trace algebra independent of the G category laws.
-- The solver certificates needed by right superposing and tensoring traces
-- live with those proofs in GConstruction.CoreProofs.
------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced

import Categories.Coherence.Symmetric as CS
open import Categories.FreeMonoidal using (module FreeMonoidalHelper; Symm)
open import Categories.GConstruction.Core using (module Wiring)
open import Data.Fin using (Fin; suc)
open import Data.Fin.Patterns
open import Data.Product using (_,_)
open import Data.Vec using ([]; _∷_)

module Categories.GConstruction.Trace
  {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Interchange.Braided as IB
import Categories.Category.Monoidal.Interchange.Symmetric as IS
import Categories.Category.Monoidal.Utilities as U

private
  module UnitCoherence {a b c} (Cˢ : SymmetricMonoidalCategory a b c)
    (let module S = SymmetricMonoidalCategory Cˢ)
    (A⁺ A⁻ B⁺ B⁻ : S.Obj) (f₀ : (A⁺ S.⊗₀ B⁻) S.⇒ (A⁻ S.⊗₀ B⁺)) where
    open FreeMonoidalHelper Symm (Fin 4) using (ObjTerm; Var; _⊗₀_) renaming (unit to I)

    a⁺ a⁻ b⁺ b⁻ : ObjTerm
    a⁺ = Var 0F ; a⁻ = Var 1F ; b⁺ = Var 2F ; b⁻ = Var 3F

    module P = CS.Solver Cˢ (A⁺ ∷ A⁻ ∷ B⁺ ∷ B⁻ ∷ [])
      (((a⁺ ⊗₀ b⁻) , (a⁻ ⊗₀ b⁺) , f₀) ∷ [])
    open P.S using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; λ⇒; λ⇐; ρ⇒; ρ⇐)
    open Wiring P.S.Symmetric-Monoidal using () renaming (mid to midᵗ)

    f : HomTerm (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
    f = Agen (P.gen 0F)

    lhsˡ rhsˡ : HomTerm ((I ⊗₀ a⁺) ⊗₀ b⁻) ((I ⊗₀ a⁻) ⊗₀ b⁺)
    lhsˡ = id ⊗₁ λ⇒ ∘ (midᵗ ∘ σ ⊗₁ f ∘ midᵗ) ∘ id ⊗₁ λ⇐
    rhsˡ = λ⇐ ⊗₁ id ∘ f ∘ λ⇒ ⊗₁ id

    lhsʳ rhsʳ : HomTerm ((a⁺ ⊗₀ I) ⊗₀ b⁻) ((a⁻ ⊗₀ I) ⊗₀ b⁺)
    lhsʳ = id ⊗₁ ρ⇒ ∘ (midᵗ ∘ f ⊗₁ σ ∘ midᵗ) ∘ id ⊗₁ ρ⇐
    rhsʳ = ρ⇐ ⊗₁ id ∘ f ∘ ρ⇒ ⊗₁ id

  module AssocCoherence {a b c} (Cˢ : SymmetricMonoidalCategory a b c)
    (let module S = SymmetricMonoidalCategory Cˢ)
    (A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ : S.Obj)
    (f₀ : (A⁺ S.⊗₀ B⁻) S.⇒ (A⁻ S.⊗₀ B⁺))
    (g₀ : (D⁺ S.⊗₀ E⁻) S.⇒ (D⁻ S.⊗₀ E⁺))
    (h₀ : (P⁺ S.⊗₀ Q⁻) S.⇒ (P⁻ S.⊗₀ Q⁺)) where
    open FreeMonoidalHelper Symm (Fin 12) using (ObjTerm; Var; _⊗₀_)

    a⁺ a⁻ b⁺ b⁻ d⁺ d⁻ e⁺ e⁻ p⁺ p⁻ q⁺ q⁻ : ObjTerm
    a⁺ = Var 0F ; a⁻ = Var 1F ; b⁺ = Var 2F ; b⁻ = Var 3F
    d⁺ = Var 4F ; d⁻ = Var 5F ; e⁺ = Var 6F ; e⁻ = Var 7F
    p⁺ = Var 8F ; p⁻ = Var 9F ; q⁺ = Var (suc 9F) ; q⁻ = Var (suc (suc 9F))

    module P = CS.Solver Cˢ (A⁺ ∷ A⁻ ∷ B⁺ ∷ B⁻ ∷ D⁺ ∷ D⁻ ∷ E⁺ ∷ E⁻ ∷ P⁺ ∷ P⁻ ∷ Q⁺ ∷ Q⁻ ∷ [])
      (((a⁺ ⊗₀ b⁻) , (a⁻ ⊗₀ b⁺) , f₀) ∷
       ((d⁺ ⊗₀ e⁻) , (d⁻ ⊗₀ e⁺) , g₀) ∷ ((p⁺ ⊗₀ q⁻) , (p⁻ ⊗₀ q⁺) , h₀) ∷ [])
    open P.S using (HomTerm; Agen; id; _∘_; _⊗₁_; α⇒; α⇐)
    open Wiring P.S.Symmetric-Monoidal using () renaming (mid to midᵗ)

    f : HomTerm (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
    f = Agen (P.gen 0F)
    g : HomTerm (d⁺ ⊗₀ e⁻) (d⁻ ⊗₀ e⁺)
    g = Agen (P.gen 1F)
    h : HomTerm (p⁺ ⊗₀ q⁻) (p⁻ ⊗₀ q⁺)
    h = Agen (P.gen 2F)

    lhs rhs : HomTerm (((a⁺ ⊗₀ d⁺) ⊗₀ p⁺) ⊗₀ (b⁻ ⊗₀ (e⁻ ⊗₀ q⁻)))
                      (((a⁻ ⊗₀ d⁻) ⊗₀ p⁻) ⊗₀ (b⁺ ⊗₀ (e⁺ ⊗₀ q⁺)))
    lhs = id ⊗₁ α⇒ ∘ (midᵗ ∘ (midᵗ ∘ f ⊗₁ g ∘ midᵗ) ⊗₁ h ∘ midᵗ) ∘ id ⊗₁ α⇐
    rhs = α⇐ ⊗₁ id ∘ (midᵗ ∘ f ⊗₁ (midᵗ ∘ g ⊗₁ h ∘ midᵗ) ∘ midᵗ) ∘ α⇒ ⊗₁ id

open Category C
open Traced Traced
open U.Shorthands Monoidal
open import Categories.Category.Monoidal.Reasoning Monoidal using (refl⟩⊗⟨_; ⊗-distrib-over-∘; _⟩⊗⟨_)
open import Categories.Morphism.Reasoning C
open BProps.Shorthands braided

open HomReasoning

open Wiring symmetric public using (α; β; γ; mid)

Cˢ : SymmetricMonoidalCategory a b c
Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = symmetric }

mid-involutive : ∀ {P Q R S : Obj} → mid {P} {Q} {R} {S} ∘ mid ≈ id
mid-involutive = IS.swapInner-commutative symmetric

mid-natural : ∀ {P P′ Q Q′ R R′ S S′ : Obj}
                {f : P ⇒ P′} {g : Q ⇒ Q′} {h : R ⇒ R′} {k : S ⇒ S′} →
              mid ∘ (f ⊗₁ g) ⊗₁ (h ⊗₁ k)
              ≈ (f ⊗₁ h) ⊗₁ (g ⊗₁ k) ∘ mid
mid-natural = IB.swapInner-natural braided

mid-σ : ∀ {P Q R S : Obj} → mid ∘ σ⇒ ⊗₁ σ⇒ ≈ σ⇒ ∘ mid {P} {R} {Q} {S}
mid-σ = switch-fromtoʳ (IS.swapInner-iso symmetric) (assoc ○ IB.swapInner-braiding braided)

-- The unitor and associator squares of `f ⊗₁ᴳ g = mid ∘ f ⊗ g ∘ mid`
-- (`GConstruction.CoreProofs`, after `absorbˡ`/`absorbʳ`).  `⊗` is strong monoidal
-- with `⊗-homo = swapInner` (upstream `Categories.Functor.Monoidal.Tensor`), and
-- these are its `swapInner-unitˡ`/`-unitʳ`/`-assoc` read through the conjugation.
mid-unitˡ : ∀ {A⁺ A⁻ B⁺ B⁻} {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
            id ⊗₁ λ⇒ ∘ (mid ∘ σ⇒ ⊗₁ f ∘ mid) ∘ id ⊗₁ λ⇐ ≈ λ⇐ ⊗₁ id ∘ f ∘ λ⇒ ⊗₁ id
mid-unitˡ {A⁺} {A⁻} {B⁺} {B⁻} {f} = P.solveH! lhsˡ rhsˡ
  where open UnitCoherence Cˢ A⁺ A⁻ B⁺ B⁻ f

mid-unitʳ : ∀ {A⁺ A⁻ B⁺ B⁻} {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
            id ⊗₁ ρ⇒ ∘ (mid ∘ f ⊗₁ σ⇒ ∘ mid) ∘ id ⊗₁ ρ⇐ ≈ ρ⇐ ⊗₁ id ∘ f ∘ ρ⇒ ⊗₁ id
mid-unitʳ {A⁺} {A⁻} {B⁺} {B⁻} {f} = P.solveH! lhsʳ rhsʳ
  where open UnitCoherence Cˢ A⁺ A⁻ B⁺ B⁻ f

mid-assoc : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻}
              {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} {g : D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺} {h : P⁺ ⊗₀ Q⁻ ⇒ P⁻ ⊗₀ Q⁺} →
            id ⊗₁ α⇒ ∘ (mid ∘ (mid ∘ f ⊗₁ g ∘ mid) ⊗₁ h ∘ mid) ∘ id ⊗₁ α⇐
            ≈ α⇐ ⊗₁ id ∘ (mid ∘ f ⊗₁ (mid ∘ g ⊗₁ h ∘ mid) ∘ mid) ∘ α⇒ ⊗₁ id
mid-assoc {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {E⁺} {E⁻} {P⁺} {P⁻} {Q⁺} {Q⁻} {f} {g} {h} =
  P.solveH! lhs rhs
  where open AssocCoherence Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ f g h

trace-βyank : ∀ {Y X : Obj} → trace (β {Y} {X}) ≈ id
trace-βyank = superposing ○ (refl⟩⊗⟨ yanking) ○ ⊗.identity

trace-gyank : ∀ {Y X B' : Obj} {g : Y ⊗₀ X ⇒ B'} → trace (g ⊗₁ id ∘ β) ≈ g
trace-gyank = tightenₗ ○ elimʳ trace-βyank

-- Re-bracketing the loop object along `mid`: slide, then `mid`'s involution.
trace-mid : ∀ {A B P Q R S : Obj}
              {f : A ⊗₀ ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S)) ⇒ B ⊗₀ ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))} →
            trace f ≈ trace (id ⊗₁ mid ∘ f ∘ id ⊗₁ mid)
trace-mid = ⟺ (⟺ slide ○ trace-resp-≈ (cancelʳ
  (⟺ ⊗-distrib-over-∘ ○ (identityˡ ⟩⊗⟨ mid-involutive) ○ ⊗.identity)))
