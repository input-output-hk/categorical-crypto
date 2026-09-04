{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The coherence lemmas of the G-construction's two absorption laws, proven by
-- the APROP solver over a 6-atom signature and transported into an arbitrary
-- SMC.  Both say "composing with an embedded pair of base morphisms only
-- decorates the loop body": with `⌜ u , v ⌝ = σ ∘ u ⊗ v`,
--
--   AL :  α ∘ ⌜u,v⌝ ⊗ g ∘ γ  ≈  (id ⊗ u) ⊗ id ∘ (α ∘ σ ⊗ g ∘ γ) ∘ (id ⊗ v) ⊗ id
--   AR :  α ∘ f ⊗ ⌜p,q⌝ ∘ γ  ≈  (q ⊗ id) ⊗ id ∘ (α ∘ f ⊗ σ ∘ γ) ∘ (p ⊗ id) ⊗ id
--
-- The bracketing is the one `trace-∘ˡ`/`trace-∘ʳ` produce, so `absorbˡ`/`absorbʳ`
-- in `Categories.GConstructionEmbedding` read these off without reassociating.
-- The inner loop bodies are `GConstruction`'s `id ∘ g` and `f ∘ id`, which is
-- how the identity laws discharge the residue.
--
-- One signature per law: the interpretation of a signature is total on its
-- generators, and a caller of `absorbˡ` has no morphism of `gp`/`gq`'s type.
--------------------------------------------------------------------------------

module Categories.GConstructionEmbeddingCoherence where

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

X6 : Set
X6 = Fin 6

open FreeMonoidalHelper Symm X6 using (ObjTerm; Var; _⊗₀_)

a⁺ a⁻ b⁺ b⁻ d⁺ d⁻ : ObjTerm
a⁺ = Var 0F ; a⁻ = Var 1F ; b⁺ = Var 2F
b⁻ = Var 3F ; d⁺ = Var 4F ; d⁻ = Var 5F

--------------------------------------------------------------------------------
-- absorbˡ: the embedded morphism is the outer factor (`gu`/`gv` its two legs)

module L where

  data Mor : ObjTerm → ObjTerm → Set where
    gg : Mor (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
    gu : Mor b⁺ d⁺
    gv : Mor d⁻ b⁻

  _≟-Mor_ : ∀ {A B} → DecidableEquality (Mor A B)
  gg ≟-Mor gg = yes refl
  gu ≟-Mor gu = yes refl
  gv ≟-Mor gv = yes refl

  sig : APROPSignature
  sig = record { X = X6 ; mor = Mor ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-Mor_ }

  open APROP sig using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; _≈Term_)

  αᵗ : ∀ {A⁻' B⁺' B⁻' C⁺'}
     → HomTerm ((B⁻' ⊗₀ C⁺') ⊗₀ (A⁻' ⊗₀ B⁺')) ((A⁻' ⊗₀ C⁺') ⊗₀ (B⁻' ⊗₀ B⁺'))
  αᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

  γᵗ : ∀ {A⁺' B⁺' B⁻' C⁻'}
     → HomTerm ((A⁺' ⊗₀ C⁻') ⊗₀ (B⁻' ⊗₀ B⁺')) ((B⁺' ⊗₀ C⁻') ⊗₀ (A⁺' ⊗₀ B⁻'))
  γᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ

  lhs rhs : HomTerm ((a⁺ ⊗₀ d⁻) ⊗₀ (b⁻ ⊗₀ b⁺)) ((a⁻ ⊗₀ d⁺) ⊗₀ (b⁻ ⊗₀ b⁺))
  lhs = αᵗ ∘ (σ ∘ Agen gu ⊗₁ Agen gv) ⊗₁ Agen gg ∘ γᵗ
  rhs = (id ⊗₁ Agen gu) ⊗₁ id ∘ (αᵗ ∘ σ ⊗₁ Agen gg ∘ γᵗ) ∘ (id ⊗₁ Agen gv) ⊗₁ id

  open import Categories.APROP.Hypergraph.Solver.Split sig
    using () renaming (solveTerm!ᵀ to solve!)

  coh : lhs ≈Term rhs
  coh = solve! lhs rhs refl

  private module IM = Interp sig

  module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
    (let module C = SymmetricMonoidalCategory C)
    (A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj)
    where

    ⟦_⟧ᵖ₀ : Fin 6 → C.Obj
    ⟦ 0F ⟧ᵖ₀ = A⁺ ; ⟦ 1F ⟧ᵖ₀ = A⁻ ; ⟦ 2F ⟧ᵖ₀ = B⁺
    ⟦ 3F ⟧ᵖ₀ = B⁻ ; ⟦ 4F ⟧ᵖ₀ = D⁺ ; ⟦ 5F ⟧ᵖ₀ = D⁻

    module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

    module WithGens (g₀ : OI.⟦ a⁺ ⊗₀ b⁻ ⟧₀ C.⇒ OI.⟦ a⁻ ⊗₀ b⁺ ⟧₀)
                    (u₀ : B⁺ C.⇒ D⁺) (v₀ : D⁻ C.⇒ B⁻) where

      ⟦_⟧ᵖ₁ : ∀ {x y} → Mor x y → OI.⟦ x ⟧₀ C.⇒ OI.⟦ y ⟧₀
      ⟦ gg ⟧ᵖ₁ = g₀ ; ⟦ gu ⟧ᵖ₁ = u₀ ; ⟦ gv ⟧ᵖ₁ = v₀

      open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

      AL : ⟦ lhs ⟧₁ C.≈ ⟦ rhs ⟧₁
      AL = Functor.F-resp-≈ freeFunctor coh

--------------------------------------------------------------------------------
-- absorbʳ: the embedded morphism is the inner factor (`gp`/`gq` its two legs)

module R where

  data Mor : ObjTerm → ObjTerm → Set where
    gf : Mor (b⁺ ⊗₀ d⁻) (b⁻ ⊗₀ d⁺)
    gp : Mor a⁺ b⁺
    gq : Mor b⁻ a⁻

  _≟-Mor_ : ∀ {A B} → DecidableEquality (Mor A B)
  gf ≟-Mor gf = yes refl
  gp ≟-Mor gp = yes refl
  gq ≟-Mor gq = yes refl

  sig : APROPSignature
  sig = record { X = X6 ; mor = Mor ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-Mor_ }

  open APROP sig using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; _≈Term_)

  αᵗ : ∀ {A⁻' B⁺' B⁻' C⁺'}
     → HomTerm ((B⁻' ⊗₀ C⁺') ⊗₀ (A⁻' ⊗₀ B⁺')) ((A⁻' ⊗₀ C⁺') ⊗₀ (B⁻' ⊗₀ B⁺'))
  αᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

  γᵗ : ∀ {A⁺' B⁺' B⁻' C⁻'}
     → HomTerm ((A⁺' ⊗₀ C⁻') ⊗₀ (B⁻' ⊗₀ B⁺')) ((B⁺' ⊗₀ C⁻') ⊗₀ (A⁺' ⊗₀ B⁻'))
  γᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ

  lhs rhs : HomTerm ((a⁺ ⊗₀ d⁻) ⊗₀ (b⁻ ⊗₀ b⁺)) ((a⁻ ⊗₀ d⁺) ⊗₀ (b⁻ ⊗₀ b⁺))
  lhs = αᵗ ∘ Agen gf ⊗₁ (σ ∘ Agen gp ⊗₁ Agen gq) ∘ γᵗ
  rhs = (Agen gq ⊗₁ id) ⊗₁ id ∘ (αᵗ ∘ Agen gf ⊗₁ σ ∘ γᵗ) ∘ (Agen gp ⊗₁ id) ⊗₁ id

  open import Categories.APROP.Hypergraph.Solver.Split sig
    using () renaming (solveTerm!ᵀ to solve!)

  coh : lhs ≈Term rhs
  coh = solve! lhs rhs refl

  private module IM = Interp sig

  module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
    (let module C = SymmetricMonoidalCategory C)
    (A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj)
    where

    ⟦_⟧ᵖ₀ : Fin 6 → C.Obj
    ⟦ 0F ⟧ᵖ₀ = A⁺ ; ⟦ 1F ⟧ᵖ₀ = A⁻ ; ⟦ 2F ⟧ᵖ₀ = B⁺
    ⟦ 3F ⟧ᵖ₀ = B⁻ ; ⟦ 4F ⟧ᵖ₀ = D⁺ ; ⟦ 5F ⟧ᵖ₀ = D⁻

    module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

    module WithGens (f₀ : OI.⟦ b⁺ ⊗₀ d⁻ ⟧₀ C.⇒ OI.⟦ b⁻ ⊗₀ d⁺ ⟧₀)
                    (p₀ : A⁺ C.⇒ B⁺) (q₀ : B⁻ C.⇒ A⁻) where

      ⟦_⟧ᵖ₁ : ∀ {x y} → Mor x y → OI.⟦ x ⟧₀ C.⇒ OI.⟦ y ⟧₀
      ⟦ gf ⟧ᵖ₁ = f₀ ; ⟦ gp ⟧ᵖ₁ = p₀ ; ⟦ gq ⟧ᵖ₁ = q₀

      open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

      AR : ⟦ lhs ⟧₁ C.≈ ⟦ rhs ⟧₁
      AR = Functor.F-resp-≈ freeFunctor coh
