{-# OPTIONS --safe --without-K #-}

module Categories.FreeMonoidal where

--------------------------------------------------------------------------------
-- Various free monoidal categories. The intended interface to this
-- file is further below, the `FreeMonoidalData` type and
-- `FreeMonoidal` module.
--------------------------------------------------------------------------------

open import Level

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor hiding (id)
open import Categories.Functor.Monoidal
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Variant : Set where
  Mon Symm : Variant

data _≤_ : Variant → Variant → Set where
  v≤v : ∀ {v} → v ≤ v
  M≤S : Mon ≤ Symm

record ⟦_⟧ᵥ (v : Variant) {o ℓ e : Level} : Set (suc (o ⊔ ℓ ⊔ e)) where
  field C : Category o ℓ e
        Monoidal-C : Monoidal C
        Symmetric-C : ⦃ Symm ≤ v ⦄ → Symmetric Monoidal-C

  module Cat where
    open Category C public
    open Monoidal Monoidal-C public
    open import Categories.Category.Monoidal.Utilities Monoidal-C
    open Shorthands public

    module _ ⦃ _ : Symm ≤ v ⦄ where
      open Symmetric Symmetric-C using (commutative; hexagon₁; module braiding) public
      σ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
      σ {X} {Y} = braiding.⇒.η (X , Y)

module FreeMonoidalHelper (v : Variant) (X : Set) where
  infixr 10 _⊗₀_

  data ObjTerm : Set where
    unit : ObjTerm
    _⊗₀_ : ObjTerm → ObjTerm → ObjTerm
    Var : X → ObjTerm

  module Mor (mor : ObjTerm → ObjTerm → Set) where
    infix  4 _≈Term_
    infixr 9 _∘_
    infixr 10 _⊗₁_

    private variable A B C D : ObjTerm

    data HomTerm : ObjTerm → ObjTerm → Set where
      var : mor A B → HomTerm A B
      id : HomTerm A A
      _∘_ : HomTerm B C → HomTerm A B → HomTerm A C
      _⊗₁_ : HomTerm A B → HomTerm C D → HomTerm (A ⊗₀ C) (B ⊗₀ D)
      λ⇒ : HomTerm (unit ⊗₀ A) A
      λ⇐ : HomTerm A (unit ⊗₀ A)
      ρ⇒ : HomTerm (A ⊗₀ unit) A
      ρ⇐ : HomTerm A (A ⊗₀ unit)
      α⇒ : HomTerm ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
      α⇐ : HomTerm (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
      σ : ⦃ Symm ≤ v ⦄ → HomTerm (A ⊗₀ B) (B ⊗₀ A)

    private variable f f' g g' h i : HomTerm A B

    data _≈Term_ : HomTerm A B → HomTerm A B → Set where
      idˡ : id ∘ f ≈Term f
      idʳ : f ∘ id ≈Term f
      assoc : (h ∘ g) ∘ f ≈Term h ∘ (g ∘ f)
      ∘-resp-≈ : f ≈Term h → g ≈Term i → f ∘ g ≈Term h ∘ i
      ≈-Term-refl : f ≈Term f
      ≈-Term-sym : f ≈Term g → g ≈Term f
      ≈-Term-trans : f ≈Term g → g ≈Term h → f ≈Term h
      id⊗id≈id : id ⊗₁ id ≈Term id {A ⊗₀ B}
      ⊗-resp-≈ : f ≈Term f' → g ≈Term g' → f ⊗₁ g ≈Term f' ⊗₁ g'
      ⊗-∘-dist : (g ∘ f) ⊗₁ (g' ∘ f') ≈Term g ⊗₁ g' ∘ f ⊗₁ f'
      λ⇐∘λ⇒≈id : λ⇐ ∘ (λ⇒ {A}) ≈Term id
      λ⇒∘λ⇐≈id : λ⇒ ∘ (λ⇐ {A}) ≈Term id
      ρ⇐∘ρ⇒≈id : ρ⇐ ∘ (ρ⇒ {A}) ≈Term id
      ρ⇒∘ρ⇐≈id : ρ⇒ ∘ (ρ⇐ {A}) ≈Term id
      α⇐∘α⇒≈id : α⇐ ∘ (α⇒ {A} {B} {C}) ≈Term id
      α⇒∘α⇐≈id : α⇒ ∘ (α⇐ {A} {B} {C}) ≈Term id
      λ⇒∘id⊗f≈f∘λ⇒ : λ⇒ ∘ id ⊗₁ f ≈Term f ∘ λ⇒
      ρ⇒∘f⊗id≈f∘ρ⇒ : ρ⇒ ∘ f ⊗₁ id ≈Term f ∘ ρ⇒
      α-comm : α⇒ ∘ (f ⊗₁ g) ⊗₁ h ≈Term f ⊗₁ g ⊗₁ h ∘ α⇒
      triangle : id ⊗₁ λ⇒ ∘ (α⇒ {A} {unit} {B}) ≈Term ρ⇒ ⊗₁ id
      pentagon : id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id ≈Term α⇒ ∘ (α⇒ {A ⊗₀ B} {C} {D})
      σ∘σ≈id : ⦃ _ : Symm ≤ v ⦄ → σ ∘ σ ≈Term id {A ⊗₀ B}
      σ∘[f⊗g]≈[g⊗f]∘σ : ⦃ _ : Symm ≤ v ⦄ {f : HomTerm A B} {g : HomTerm C D} → σ ∘ (f ⊗₁ g) ≈Term (g ⊗₁ f) ∘ σ
      hexagon : ⦃ _ : Symm ≤ v ⦄ → id ⊗₁ σ ∘ α⇒ ∘ σ ⊗₁ id ≈Term α⇒ ∘ σ ∘ α⇒ {A} {B} {C}

    ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
    ≡⇒≈Term refl = ≈-Term-refl

    FreeMonoidal : Category 0ℓ 0ℓ 0ℓ
    FreeMonoidal = categoryHelper record
      { Obj       = ObjTerm
      ; _⇒_       = HomTerm
      ; _≈_       = _≈Term_
      ; id        = id
      ; _∘_       = _∘_
      ; assoc     = assoc
      ; identityˡ = idˡ
      ; identityʳ = idʳ
      ; equiv     = record { refl = ≈-Term-refl ; sym = ≈-Term-sym ; trans = ≈-Term-trans }
      ; ∘-resp-≈  = ∘-resp-≈
      }

    Monoidal-FreeMonoidal : Monoidal FreeMonoidal
    Monoidal-FreeMonoidal = monoidalHelper FreeMonoidal record
      { ⊗               = record
          { F₀           = uncurry _⊗₀_
          ; F₁           = uncurry _⊗₁_
          ; identity     = id⊗id≈id
          ; homomorphism = ⊗-∘-dist
          ; F-resp-≈     = uncurry ⊗-resp-≈
          }
      ; unit            = unit
      ; unitorˡ         = record { from = λ⇒ ; to = λ⇐ ; iso = record { isoˡ = λ⇐∘λ⇒≈id ; isoʳ = λ⇒∘λ⇐≈id } }
      ; unitorʳ         = record { from = ρ⇒ ; to = ρ⇐ ; iso = record { isoˡ = ρ⇐∘ρ⇒≈id ; isoʳ = ρ⇒∘ρ⇐≈id } }
      ; associator      = record { from = α⇒ ; to = α⇐ ; iso = record { isoˡ = α⇐∘α⇒≈id ; isoʳ = α⇒∘α⇐≈id } }
      ; unitorˡ-commute = λ⇒∘id⊗f≈f∘λ⇒
      ; unitorʳ-commute = ρ⇒∘f⊗id≈f∘ρ⇒
      ; assoc-commute   = α-comm
      ; triangle        = triangle
      ; pentagon        = pentagon
      }

    module _ ⦃ _ : Symm ≤ v ⦄ where
      open import Categories.Morphism FreeMonoidal

      σ-iso : A ⊗₀ B ≅ B ⊗₀ A
      σ-iso = record { from = σ ; to = σ ; iso = record { isoˡ = σ∘σ≈id ; isoʳ = σ∘σ≈id } }

      Symmetric-Monoidal : Symmetric Monoidal-FreeMonoidal
      Symmetric-Monoidal = symmetricHelper Monoidal-FreeMonoidal record
        { braiding    = pointwise-iso (λ _ → σ-iso) λ where (f , g) → σ∘[f⊗g]≈[g⊗f]∘σ
        ; commutative = σ∘σ≈id
        ; hexagon     = hexagon
        }

record FreeMonoidalData : Set₁ where
  field v : Variant
        X : Set

  open FreeMonoidalHelper v X

  field mor : ObjTerm → ObjTerm → Set

module FreeMonoidal (d : FreeMonoidalData) where
  open FreeMonoidalData d
  open FreeMonoidalHelper v X hiding (module Mor) public
  open FreeMonoidalHelper.Mor v X mor public

-- This module is a hack, it allows us to 'define' `⟦_⟧₀` in the
-- middle of `FreeFunctorData`. We cannot inline this module, since
-- Agda only allows definitions that can be defined in a let-binding
-- in the middle of a record.
module FreeFunctorHelper (d : FreeMonoidalData) (let open FreeMonoidalData d)
                         {o ℓ e : Level} (⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e}) where
  open FreeMonoidal d public

  module C = ⟦_⟧ᵥ.Cat ⟦v⟧
  module FM = Category FreeMonoidal

  module Go (⟦_⟧ᵖ₀ : X → C.Obj) where
    ⟦_⟧₀ : FM.Obj → C.Obj
    ⟦ unit ⟧₀ = C.unit
    ⟦ x ⊗₀ x₁ ⟧₀ = ⟦ x ⟧₀ C.⊗₀ ⟦ x₁ ⟧₀
    ⟦ Var x ⟧₀ = ⟦ x ⟧ᵖ₀

record FreeFunctorData (d : FreeMonoidalData) {o ℓ e : Level}
                       : Set (suc (o ⊔ ℓ ⊔ e)) where
  open FreeMonoidalData d

  field ⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e}

  open FreeFunctorHelper d ⟦v⟧ public

  field ⟦_⟧ᵖ₀ : X → C.Obj

  open Go ⟦_⟧ᵖ₀ public -- this gives us ⟦_⟧₀

  field ⟦_⟧ᵖ₁ : ∀ {x y} → mor x y → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀

module FreeFunctor {d : FreeMonoidalData} {o ℓ e : Level}
                   (ffd : FreeFunctorData d {o} {ℓ} {e}) where
  open FreeFunctorData ffd

  open ⟦_⟧ᵥ ⟦v⟧

  CM : MonoidalCategory o ℓ e
  CM = record { U = C ; monoidal = Monoidal-C }
  FreeMonoidalM : MonoidalCategory 0ℓ 0ℓ 0ℓ
  FreeMonoidalM = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

  ⟦_⟧₁ : ∀ {A B} → A FM.⇒ B → ⟦ A ⟧₀ C.⇒ ⟦ B ⟧₀
  ⟦ var x ⟧₁ = ⟦ x ⟧ᵖ₁
  ⟦ id ⟧₁ = C.id
  ⟦ f ∘ f₁ ⟧₁ = ⟦ f ⟧₁ C.∘ ⟦ f₁ ⟧₁
  ⟦ f ⊗₁ f₁ ⟧₁ = ⟦ f ⟧₁ C.⊗₁ ⟦ f₁ ⟧₁
  ⟦ λ⇒ ⟧₁ = C.λ⇒
  ⟦ λ⇐ ⟧₁ = C.λ⇐
  ⟦ ρ⇒ ⟧₁ = C.ρ⇒
  ⟦ ρ⇐ ⟧₁ = C.ρ⇐
  ⟦ α⇒ ⟧₁ = C.α⇒
  ⟦ α⇐ ⟧₁ = C.α⇐
  ⟦ σ ⟧₁ = C.σ

  ⟦⟧-resp-≈ : ∀ {A B} {f g : A FM.⇒ B} → f FM.≈ g → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  ⟦⟧-resp-≈ idˡ                 = C.identityˡ
  ⟦⟧-resp-≈ idʳ                 = C.identityʳ
  ⟦⟧-resp-≈ assoc               = C.assoc
  ⟦⟧-resp-≈ (∘-resp-≈ h h')     = C.∘-resp-≈ (⟦⟧-resp-≈ h) (⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ ≈-Term-refl         = C.Equiv.refl
  ⟦⟧-resp-≈ (≈-Term-sym h)      = C.Equiv.sym (⟦⟧-resp-≈ h)
  ⟦⟧-resp-≈ (≈-Term-trans h h') = C.Equiv.trans (⟦⟧-resp-≈ h) (⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ id⊗id≈id            = C.⊗.identity
  ⟦⟧-resp-≈ (⊗-resp-≈ h h')     = C.⊗.F-resp-≈ (⟦⟧-resp-≈ h , ⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ ⊗-∘-dist            = C.⊗.homomorphism
  ⟦⟧-resp-≈ λ⇐∘λ⇒≈id            = C.unitorˡ.isoˡ
  ⟦⟧-resp-≈ λ⇒∘λ⇐≈id            = C.unitorˡ.isoʳ
  ⟦⟧-resp-≈ ρ⇐∘ρ⇒≈id            = C.unitorʳ.isoˡ
  ⟦⟧-resp-≈ ρ⇒∘ρ⇐≈id            = C.unitorʳ.isoʳ
  ⟦⟧-resp-≈ α⇐∘α⇒≈id            = C.associator.isoˡ
  ⟦⟧-resp-≈ α⇒∘α⇐≈id            = C.associator.isoʳ
  ⟦⟧-resp-≈ λ⇒∘id⊗f≈f∘λ⇒        = C.unitorˡ-commute-from
  ⟦⟧-resp-≈ ρ⇒∘f⊗id≈f∘ρ⇒        = C.unitorʳ-commute-from
  ⟦⟧-resp-≈ α-comm              = C.assoc-commute-from
  ⟦⟧-resp-≈ triangle            = C.triangle
  ⟦⟧-resp-≈ pentagon            = C.pentagon
  ⟦⟧-resp-≈ σ∘σ≈id              = C.commutative
  ⟦⟧-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ     = C.braiding.⇒.commute _
  ⟦⟧-resp-≈ hexagon             = C.hexagon₁

  freeFunctor : Functor FreeMonoidal C
  freeFunctor = record
    { F₀ = ⟦_⟧₀
    ; F₁ = ⟦_⟧₁
    ; identity = C.Equiv.refl
    ; homomorphism = C.Equiv.refl
    ; F-resp-≈ = ⟦⟧-resp-≈
    }

  isMonoidal-freeFunctor : IsMonoidalFunctor FreeMonoidalM CM freeFunctor
  isMonoidal-freeFunctor = record
    { ε = C.id
    ; ⊗-homo = ntHelper record
      { η       = λ _ → C.id
      ; commute = λ _ → C.identityˡ ○ ⟺ C.identityʳ
      }
    ; associativity = elimʳ (C.identityˡ ○ C.⊗.identity) ○ ⟺ (C.identityˡ ○ elimˡ C.⊗.identity)
    ; unitaryˡ = elimʳ (C.identityˡ ○ C.⊗.identity)
    ; unitaryʳ = elimʳ (C.identityˡ ○ C.⊗.identity)
    }
    where open Category.HomReasoning C
          open import Categories.Morphism.Reasoning C using (elimˡ; elimʳ)
