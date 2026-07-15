{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A variant of `categoryHelper` that does NOT require `_≈_` to be an
-- equivalence.
--------------------------------------------------------------------------------

module Categories.Category.EquivClosureHelper where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Rel)
import Relation.Binary.Construct.Closure.Equivalence as EqC
open EqC using (EqClosure)

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)

private
  variable
    o ℓ e : Level

record CategoryHelperᵉ (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ
    _≈_ : ∀ {A B} → Rel (A ⇒ B) e

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

-- The built category's equality is `EqClosure _≈_`, raising the equality
-- level from `e` to `ℓ ⊔ e` (the closure is a `Star` indexed over the homs).
categoryHelperᵉ : CategoryHelperᵉ o ℓ e → Category o ℓ (ℓ ⊔ e)
categoryHelperᵉ CH = categoryHelper record
  { Obj       = Obj
  ; _⇒_       = _⇒_
  ; _≈_       = EqClosure _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = fwd assoc
  ; identityˡ = fwd identityˡ
  ; identityʳ = fwd identityʳ
  ; equiv     = EqC.isEquivalence _≈_
  ; ∘-resp-≈  = λ {_} {_} {_} {_} {h} {g} {_} p q →
                  EqC.gfold (EqC.isEquivalence _≈_) (_∘ g) whiskerˡ p
                ⟫ EqC.gfold (EqC.isEquivalence _≈_) (h ∘_) whiskerʳ q
  }
  where
    open CategoryHelperᵉ CH

    infixr 5 _⟫_
    _⟫_ : ∀ {A B} {x y z : A ⇒ B} → EqClosure _≈_ x y → EqClosure _≈_ y z → EqClosure _≈_ x z
    _⟫_ = EqC.transitive _≈_

    fwd : ∀ {A B} {x y : A ⇒ B} → x ≈ y → EqClosure _≈_ x y
    fwd = EqC.return

    bwd : ∀ {A B} {x y : A ⇒ B} → x ≈ y → EqClosure _≈_ y x
    bwd p = EqC.symmetric _≈_ (EqC.return p)

    whiskerˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≈ h → EqClosure _≈_ (f ∘ g) (h ∘ g)
    whiskerˡ s = bwd identityʳ ⟫ fwd assoc ⟫ fwd (∘-resp-≈ s identityʳ)

    whiskerʳ : ∀ {A B C} {f : B ⇒ C} {g i : A ⇒ B} → g ≈ i → EqClosure _≈_ (f ∘ g) (f ∘ i)
    whiskerʳ s = bwd identityˡ ⟫ bwd assoc ⟫ fwd (∘-resp-≈ identityˡ s)
