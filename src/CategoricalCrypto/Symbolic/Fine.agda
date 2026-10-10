{-# OPTIONS --safe --without-K #-}

-- 𝔻𝕐, the free monoidal category on Dolev–Yao roles, and `Sym≅`, its UC setup
-- with syntactic test equality (docs/uc-setup-symbolic.md §3.4, §4).  A
-- generator's boundaries are unit-free: the semantics reads a role at the
-- tensor of its atoms' interfaces, and `𝔾ᵒ`'s unit is not `ifaceᵒ unitᴵ`
-- (`UC.Model.Observation`'s header).  A test carries its ancilla on the grade
-- side, as in `Machine.UC`.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Fine (𝔖 : Signature) where

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Functor using (_∘F_)
open import Categories.Functor.Construction.LiftSetoids
open import Categories.Functor.Presheaf
open import Data.Empty
open import Data.Product
open import Data.Unit
open import Level

open import CategoricalCrypto.Standard2
open import CategoricalCrypto.Symbolic.Role 𝔖

module _ where
  open FreeMonoidalHelper Mon Atom

  UnitFree : ObjTerm → Set
  UnitFree unit     = ⊥
  UnitFree (A ⊗₀ B) = UnitFree A × UnitFree B
  UnitFree (Var _)  = ⊤

symData : FreeMonoidalData {0ℓ}
symData = record { v = Mon ; X = Atom ; mor = λ x y → UnitFree x × UnitFree y × Role x y }

open FreeMonoidal symData public

𝔻𝕐 : MonoidalCategory 0ℓ 0ℓ 0ℓ
𝔻𝕐 = FMC

------------------------------------------------------------------------
-- Tests, compared as terms

Test : ObjTerm → Set
Test A = Σ[ Y ∈ ObjTerm ] HomTerm (Y ⊗₀ A) (Var verdict)

pullᵗ : {A B : ObjTerm} → HomTerm B A → Test A → Test B
pullᵗ f (Y , T) = Y , T ∘ (id ⊗₁ f)

data SameTerm {A} : Test A → Test A → Set where
  same : ∀ {Y} {T T′ : HomTerm (Y ⊗₀ A) (Var verdict)} → T ≈Term T′ → SameTerm (Y , T) (Y , T′)

ℰᵗ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids 0ℓ 0ℓ)
ℰᵗ = record
  { F₀ = λ A → record
    { Carrier = Test A ; _≈_ = SameTerm
    ; isEquivalence = record
      { refl  = same ≈-Term-refl
      ; sym   = λ { (same e) → same (≈-Term-sym e) }
      ; trans = λ { (same e) (same e′) → same (≈-Term-trans e e′) } } }
  ; F₁ = λ f → record { to = pullᵗ f ; cong = λ { (same e) → same (∘-resp-≈ e ≈-Term-refl) } }
  ; identity     = same (≈-Term-trans (∘-resp-≈ ≈-Term-refl id⊗id≈id) idʳ)
  ; homomorphism = same (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-trans
                     (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist)) (≈-Term-sym assoc))
  ; F-resp-≈     = λ e → same (∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl e))
  }

ℰ≅ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰ≅ = LiftSetoids (suc 0ℓ) (suc 0ℓ) ∘F ℰᵗ

module Sym≅ = StdUC 𝔻𝕐 ℰ≅

private
  _ : {A B C X Y P Q : ObjTerm} {f : HomTerm A (X ⊗₀ B)} {g : HomTerm A (Y ⊗₀ B)}
      {h : HomTerm B (P ⊗₀ C)} {k : HomTerm B (Q ⊗₀ C)}
    → f Sym≅.≤UC g → h Sym≅.≤UC k → h Sym≅.∙ f Sym≅.≤UC k Sym≅.∙ g
  _ = Sym≅.UC-compose
