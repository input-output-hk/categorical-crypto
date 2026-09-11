{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The base-level coherence residues of the G-construction's monoidal structure,
-- proven by the APROP solver and transported into an arbitrary SMC.  With the
-- middle-four interchange
--
--   mid : (P ⊗ Q) ⊗ (R ⊗ S) ⇒ (P ⊗ R) ⊗ (Q ⊗ S)
--
-- the tensor of G-morphisms is `f ⊗₁ᴳ g = mid ∘ f ⊗ g ∘ mid` — no trace — so
-- once `absorbˡ`/`absorbʳ` have collapsed the loop of a composite with a
-- structural G-morphism, every obligation below is a base-level equation.
--
--   U.UL / U.UR : the two unitor naturality squares
--   A.AC        : the associator naturality square
--
-- One signature per residue: an interpretation is total on its generators, so
-- a caller may only be asked for the morphisms its own law mentions.
--
-- The third residue, "`⌜_,_⌝` is monoidal", is NOT here: it is
-- `GConstructionMonoidal.⌜⌝-⊗`, proved from `mid`'s upstream interchange
-- lemmas (`GConstructionTrace.mid-σ`/`-natural`/`-involutive`) rather than
-- by a solver call.
--------------------------------------------------------------------------------

module Categories.GConstructionTensorCoherence where

open import Level

open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Data.Fin using (Fin; suc)
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

--------------------------------------------------------------------------------
-- The two unitor naturality squares, absorbed: one generator, and the unit
-- object is the free language's own.

module U where

  open FreeMonoidalHelper Symm (Fin 4) using (ObjTerm; Var; unit; _⊗₀_)

  a⁺ a⁻ b⁺ b⁻ : ObjTerm
  a⁺ = Var 0F ; a⁻ = Var 1F ; b⁺ = Var 2F ; b⁻ = Var 3F

  data Mor : ObjTerm → ObjTerm → Set where
    gf : Mor (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)

  _≟-Mor_ : ∀ {A B} → DecidableEquality (Mor A B)
  gf ≟-Mor gf = yes refl

  sig : APROPSignature
  sig = record { X = Fin 4 ; mor = Mor ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-Mor_ }

  open APROP sig
    using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐; _≈Term_)

  midᵗ : ∀ {P Q R S} → HomTerm ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
  midᵗ = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ ⊗₁ id ∘ α⇐) ∘ α⇒

  lhsL rhsL : HomTerm ((unit ⊗₀ a⁺) ⊗₀ b⁻) ((unit ⊗₀ a⁻) ⊗₀ b⁺)
  lhsL = id ⊗₁ λ⇒ ∘ (midᵗ ∘ σ ⊗₁ Agen gf ∘ midᵗ) ∘ id ⊗₁ λ⇐
  rhsL = λ⇐ ⊗₁ id ∘ Agen gf ∘ λ⇒ ⊗₁ id

  lhsR rhsR : HomTerm ((a⁺ ⊗₀ unit) ⊗₀ b⁻) ((a⁻ ⊗₀ unit) ⊗₀ b⁺)
  lhsR = id ⊗₁ ρ⇒ ∘ (midᵗ ∘ Agen gf ⊗₁ σ ∘ midᵗ) ∘ id ⊗₁ ρ⇐
  rhsR = ρ⇐ ⊗₁ id ∘ Agen gf ∘ ρ⇒ ⊗₁ id

  open import Categories.APROP.Hypergraph.Solver.Split sig
    using () renaming (solveTerm!ᵀ to solve!)

  cohL : lhsL ≈Term rhsL
  cohL = solve! lhsL rhsL refl

  cohR : lhsR ≈Term rhsR
  cohR = solve! lhsR rhsR refl

  private module IM = Interp sig

  module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
    (let module C = SymmetricMonoidalCategory C)
    (A⁺ A⁻ B⁺ B⁻ : C.Obj)
    where

    ⟦_⟧ᵖ₀ : Fin 4 → C.Obj
    ⟦ 0F ⟧ᵖ₀ = A⁺ ; ⟦ 1F ⟧ᵖ₀ = A⁻ ; ⟦ 2F ⟧ᵖ₀ = B⁺ ; ⟦ 3F ⟧ᵖ₀ = B⁻

    module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

    module WithGen (f₀ : OI.⟦ a⁺ ⊗₀ b⁻ ⟧₀ C.⇒ OI.⟦ a⁻ ⊗₀ b⁺ ⟧₀) where

      ⟦_⟧ᵖ₁ : ∀ {x y} → Mor x y → OI.⟦ x ⟧₀ C.⇒ OI.⟦ y ⟧₀
      ⟦ gf ⟧ᵖ₁ = f₀

      open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

      UL : ⟦ lhsL ⟧₁ C.≈ ⟦ rhsL ⟧₁
      UL = Functor.F-resp-≈ freeFunctor cohL

      UR : ⟦ lhsR ⟧₁ C.≈ ⟦ rhsR ⟧₁
      UR = Functor.F-resp-≈ freeFunctor cohR

--------------------------------------------------------------------------------
-- The associator naturality square, absorbed: three generators over the six
-- G-objects they connect.

module A where

  open FreeMonoidalHelper Symm (Fin 12) using (ObjTerm; Var; _⊗₀_)

  pattern 10F = suc 9F
  pattern 11F = suc 10F

  a⁺ a⁻ b⁺ b⁻ d⁺ d⁻ e⁺ e⁻ p⁺ p⁻ q⁺ q⁻ : ObjTerm
  a⁺ = Var 0F  ; a⁻ = Var 1F  ; b⁺ = Var 2F  ; b⁻ = Var 3F
  d⁺ = Var 4F  ; d⁻ = Var 5F  ; e⁺ = Var 6F  ; e⁻ = Var 7F
  p⁺ = Var 8F  ; p⁻ = Var 9F  ; q⁺ = Var 10F ; q⁻ = Var 11F

  data Mor : ObjTerm → ObjTerm → Set where
    gf : Mor (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
    gg : Mor (d⁺ ⊗₀ e⁻) (d⁻ ⊗₀ e⁺)
    gh : Mor (p⁺ ⊗₀ q⁻) (p⁻ ⊗₀ q⁺)

  _≟-Mor_ : ∀ {A B} → DecidableEquality (Mor A B)
  gf ≟-Mor gf = yes refl
  gg ≟-Mor gg = yes refl
  gh ≟-Mor gh = yes refl

  sig : APROPSignature
  sig = record { X = Fin 12 ; mor = Mor ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-Mor_ }

  open APROP sig using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; _≈Term_)

  midᵗ : ∀ {P Q R S} → HomTerm ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
  midᵗ = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ ⊗₁ id ∘ α⇐) ∘ α⇒

  fg : HomTerm ((a⁺ ⊗₀ d⁺) ⊗₀ (b⁻ ⊗₀ e⁻)) ((a⁻ ⊗₀ d⁻) ⊗₀ (b⁺ ⊗₀ e⁺))
  fg = midᵗ ∘ Agen gf ⊗₁ Agen gg ∘ midᵗ

  gh′ : HomTerm ((d⁺ ⊗₀ p⁺) ⊗₀ (e⁻ ⊗₀ q⁻)) ((d⁻ ⊗₀ p⁻) ⊗₀ (e⁺ ⊗₀ q⁺))
  gh′ = midᵗ ∘ Agen gg ⊗₁ Agen gh ∘ midᵗ

  lhs rhs : HomTerm (((a⁺ ⊗₀ d⁺) ⊗₀ p⁺) ⊗₀ (b⁻ ⊗₀ (e⁻ ⊗₀ q⁻)))
                    (((a⁻ ⊗₀ d⁻) ⊗₀ p⁻) ⊗₀ (b⁺ ⊗₀ (e⁺ ⊗₀ q⁺)))
  lhs = id ⊗₁ α⇒ ∘ (midᵗ ∘ fg ⊗₁ Agen gh ∘ midᵗ) ∘ id ⊗₁ α⇐
  rhs = α⇐ ⊗₁ id ∘ (midᵗ ∘ Agen gf ⊗₁ gh′ ∘ midᵗ) ∘ α⇒ ⊗₁ id

  open import Categories.APROP.Hypergraph.Solver.Split sig
    using () renaming (solveTerm!ᵀ to solve!)

  coh : lhs ≈Term rhs
  coh = solve! lhs rhs refl

  private module IM = Interp sig

  module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
    (let module C = SymmetricMonoidalCategory C)
    (A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ : C.Obj)
    where

    ⟦_⟧ᵖ₀ : Fin 12 → C.Obj
    ⟦ 0F ⟧ᵖ₀  = A⁺ ; ⟦ 1F ⟧ᵖ₀  = A⁻ ; ⟦ 2F ⟧ᵖ₀  = B⁺ ; ⟦ 3F ⟧ᵖ₀  = B⁻
    ⟦ 4F ⟧ᵖ₀  = D⁺ ; ⟦ 5F ⟧ᵖ₀  = D⁻ ; ⟦ 6F ⟧ᵖ₀  = E⁺ ; ⟦ 7F ⟧ᵖ₀  = E⁻
    ⟦ 8F ⟧ᵖ₀  = P⁺ ; ⟦ 9F ⟧ᵖ₀  = P⁻ ; ⟦ 10F ⟧ᵖ₀ = Q⁺ ; ⟦ 11F ⟧ᵖ₀ = Q⁻

    module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

    module WithGens (f₀ : OI.⟦ a⁺ ⊗₀ b⁻ ⟧₀ C.⇒ OI.⟦ a⁻ ⊗₀ b⁺ ⟧₀)
                    (g₀ : OI.⟦ d⁺ ⊗₀ e⁻ ⟧₀ C.⇒ OI.⟦ d⁻ ⊗₀ e⁺ ⟧₀)
                    (h₀ : OI.⟦ p⁺ ⊗₀ q⁻ ⟧₀ C.⇒ OI.⟦ p⁻ ⊗₀ q⁺ ⟧₀) where

      ⟦_⟧ᵖ₁ : ∀ {x y} → Mor x y → OI.⟦ x ⟧₀ C.⇒ OI.⟦ y ⟧₀
      ⟦ gf ⟧ᵖ₁ = f₀ ; ⟦ gg ⟧ᵖ₁ = g₀ ; ⟦ gh ⟧ᵖ₁ = h₀

      open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

      AC : ⟦ lhs ⟧₁ C.≈ ⟦ rhs ⟧₁
      AC = Functor.F-resp-≈ freeFunctor coh
