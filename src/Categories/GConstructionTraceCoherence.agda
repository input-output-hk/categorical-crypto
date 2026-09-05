{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The coherence step of `GConstructionTrace.⊗-trace-mid`: the loop body that
-- `⊗-trace` leaves — two β-conjugations around the two factors — is the
-- middle-four interchange of the plain tensor `u ⊗ v`,
--
--   TM : (β ∘ u ⊗ id ∘ β) ⊗ id ∘ β ∘ (α⇐ ∘ id ⊗ v ∘ α⇒) ⊗ id ∘ β
--          ≈ α⇐ ∘ (mid ∘ u ⊗ v ∘ mid) ∘ α⇒
--
-- so that `vanishing₂` merges the two loops into `X ⊗ Y`.  Two generators over
-- the six objects they connect.
--------------------------------------------------------------------------------

module Categories.GConstructionTraceCoherence where

open import Level

open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Categories.APROP
open import Categories.FreeMonoidal

import Categories.APROP.Hypergraph.Solver.Frontend as Interp

private instance S≤S : Symm ≤ Symm
                 S≤S = v≤v

open FreeMonoidalHelper Symm (Fin 6) using (ObjTerm; Var; _⊗₀_)

a b a′ b′ x y : ObjTerm
a = Var 0F ; b = Var 1F ; a′ = Var 2F
b′ = Var 3F ; x = Var 4F ; y = Var 5F

data Mor : ObjTerm → ObjTerm → Set where
  gu : Mor (a ⊗₀ x) (b ⊗₀ x)
  gv : Mor (a′ ⊗₀ y) (b′ ⊗₀ y)

_≟-Mor_ : ∀ {A B} → DecidableEquality (Mor A B)
gu ≟-Mor gu = yes refl
gv ≟-Mor gv = yes refl

sig : APROPSignature
sig = record { X = Fin 6 ; mor = Mor ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-Mor_ }

open APROP sig using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; _≈Term_)

βᵗ : ∀ {P Q R} → HomTerm ((P ⊗₀ Q) ⊗₀ R) ((P ⊗₀ R) ⊗₀ Q)
βᵗ = α⇐ ∘ id ⊗₁ σ ∘ α⇒

midᵗ : ∀ {P Q R S} → HomTerm ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
midᵗ = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ ⊗₁ id ∘ α⇐) ∘ α⇒

lhs rhs : HomTerm (((a ⊗₀ a′) ⊗₀ x) ⊗₀ y) (((b ⊗₀ b′) ⊗₀ x) ⊗₀ y)
lhs = (βᵗ ∘ Agen gu ⊗₁ id ∘ βᵗ) ⊗₁ id ∘ βᵗ
      ∘ (α⇐ ∘ id ⊗₁ Agen gv ∘ α⇒) ⊗₁ id ∘ βᵗ
rhs = α⇐ ∘ (midᵗ ∘ Agen gu ⊗₁ Agen gv ∘ midᵗ) ∘ α⇒

open import Categories.APROP.Hypergraph.Solver.Split sig
  using () renaming (solveTerm!ᵀ to solve!)

coh : lhs ≈Term rhs
coh = solve! lhs rhs refl

private module IM = Interp sig

module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (A A′ B B′ X Y : C.Obj)
  where

  ⟦_⟧ᵖ₀ : Fin 6 → C.Obj
  ⟦ 0F ⟧ᵖ₀ = A ; ⟦ 1F ⟧ᵖ₀ = B ; ⟦ 2F ⟧ᵖ₀ = A′
  ⟦ 3F ⟧ᵖ₀ = B′ ; ⟦ 4F ⟧ᵖ₀ = X ; ⟦ 5F ⟧ᵖ₀ = Y

  module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

  module WithGens (u₀ : OI.⟦ a ⊗₀ x ⟧₀ C.⇒ OI.⟦ b ⊗₀ x ⟧₀)
                  (v₀ : OI.⟦ a′ ⊗₀ y ⟧₀ C.⇒ OI.⟦ b′ ⊗₀ y ⟧₀) where

    ⟦_⟧ᵖ₁ : ∀ {p q} → Mor p q → OI.⟦ p ⟧₀ C.⇒ OI.⟦ q ⟧₀
    ⟦ gu ⟧ᵖ₁ = u₀ ; ⟦ gv ⟧ᵖ₁ = v₀

    open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

    TM : ⟦ lhs ⟧₁ C.≈ ⟦ rhs ⟧₁
    TM = Functor.F-resp-≈ freeFunctor coh
