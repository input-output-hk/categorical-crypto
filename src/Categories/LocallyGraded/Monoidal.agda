{-# OPTIONS --safe --without-K #-}

-- Monoidal structure on a locally graded category over a braided ℐ.

-- The braiding is needed for ⊗-homomorphism.

-- `GradedMonoidalFunctor` is the graded analogue of a lax monoidal functor.

module Categories.LocallyGraded.Monoidal where

open import Data.Product
open import Level

open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Interchange.Braided as Interchange
import Categories.Category.Monoidal.Utilities as Utilities
open import Categories.LocallyGraded
open import Categories.LocallyGraded.Trivial

module _ {o ℓ e o′ ℓ′ e′} {ℐ : MonoidalCategory o ℓ e}
  (L : LocallyGradedCategory ℐ o′ ℓ′ e′) where
  open LocallyGradedCategory L
  private
    module ℐ = MonoidalCategory ℐ
    module I = Utilities.Shorthands ℐ.monoidal

  -- an isomorphism at grade unit
  record GradedIso (A B : Obj) : Set (ℓ′ ⊔ e′) where
    field
      from : Hom ℐ.unit A B
      to   : Hom ℐ.unit B A
      isoˡ : sub[ I.λ⇒ ] (to ∙ from) ≈ id
      isoʳ : sub[ I.λ⇒ ] (from ∙ to) ≈ id

record GradedMonoidal {o ℓ e o′ ℓ′ e′} {ℐ : MonoidalCategory o ℓ e}
    (Braided-ℐ : Braided (MonoidalCategory.monoidal ℐ)) (L : LocallyGradedCategory ℐ o′ ℓ′ e′)
    : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module ℐ = MonoidalCategory ℐ
    module I = Utilities.Shorthands ℐ.monoidal
  open LocallyGradedCategory L
  open Interchange Braided-ℐ using (module swapInner)

  infixr 10 _⊗₀_ _⊗₁_

  field
    _⊗₀_ : Obj → Obj → Obj
    unit : Obj
    _⊗₁_ : ∀ {X Y A B C D} → Hom X A B → Hom Y C D → Hom (X ℐ.⊗₀ Y) (A ⊗₀ C) (B ⊗₀ D)
    ⊗-resp-≈ : ∀ {X Y A B C D} {f f′ : Hom X A B} {g g′ : Hom Y C D}
             → f ≈ f′ → g ≈ g′ → f ⊗₁ g ≈ f′ ⊗₁ g′
    ⊗-sub : ∀ {X X′ Y Y′ A B C D} {a : X ℐ.⇒ X′} {b : Y ℐ.⇒ Y′} {f : Hom X A B}
            {g : Hom Y C D} → sub[ a ] f ⊗₁ sub[ b ] g ≈ sub[ a ℐ.⊗₁ b ] (f ⊗₁ g)
    ⊗-identity : ∀ {A B} → sub[ I.λ⇒ ] (id {A} ⊗₁ id {B}) ≈ id
    ⊗-homomorphism : ∀ {X Y X′ Y′ A B C A′ B′ C′} {f : Hom X A B} {g : Hom Y B C}
                     {h : Hom X′ A′ B′} {k : Hom Y′ B′ C′}
                   → (g ⊗₁ k) ∙ (f ⊗₁ h) ≈ sub[ swapInner.from ] ((g ∙ f) ⊗₁ (k ∙ h))

    associator : ∀ {A B C} → GradedIso L ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
    unitorˡ    : ∀ {A} → GradedIso L (unit ⊗₀ A) A
    unitorʳ    : ∀ {A} → GradedIso L (A ⊗₀ unit) A

  α⇒ = λ {A B C} → GradedIso.from (associator {A} {B} {C})
  α⇐ = λ {A B C} → GradedIso.to (associator {A} {B} {C})
  λ⇒ = λ {A} → GradedIso.from (unitorˡ {A})
  λ⇐ = λ {A} → GradedIso.to (unitorˡ {A})
  ρ⇒ = λ {A} → GradedIso.from (unitorʳ {A})
  ρ⇐ = λ {A} → GradedIso.to (unitorʳ {A})

  field
    assoc-commute : ∀ {X Y Z A A′ B B′ C C′} {f : Hom X A A′} {g : Hom Y B B′}
                    {h : Hom Z C C′} → sub[ I.α⇒ ℐ.∘ I.ρ⇒ ] (α⇒ ∙ ((f ⊗₁ g) ⊗₁ h))
                                     ≈ sub[ I.λ⇒ ] ((f ⊗₁ (g ⊗₁ h)) ∙ α⇒)
    unitorˡ-commute : ∀ {X A B} {f : Hom X A B}
                    → sub[ I.λ⇒ ℐ.∘ I.ρ⇒ ] (λ⇒ ∙ (id ⊗₁ f)) ≈ sub[ I.λ⇒ ] (f ∙ λ⇒)
    unitorʳ-commute : ∀ {X A B} {f : Hom X A B}
                    → sub[ I.ρ⇒ ℐ.∘ I.ρ⇒ ] (ρ⇒ ∙ (f ⊗₁ id)) ≈ sub[ I.λ⇒ ] (f ∙ ρ⇒)
    triangle : ∀ {A B} → sub[ ℐ.id ℐ.⊗₁ I.λ⇒ ] ((id ⊗₁ λ⇒) ∙ α⇒) ≈ ρ⇒ {A} ⊗₁ id {B}
    pentagon : ∀ {A B C D} → sub[ (I.λ⇒ ℐ.∘ I.λ⇒ ℐ.⊗₁ ℐ.id) ℐ.⊗₁ I.λ⇒ ]
                               ((id ⊗₁ α⇒) ∙ α⇒ ∙ (α⇒ ⊗₁ id))
             ≈ α⇒ {A} {B} {C ⊗₀ D} ∙ α⇒ {A ⊗₀ B} {C} {D}

-- Every law of the trivial grading is the corresponding law of C.
Trivial-monoidal : ∀ {o ℓ e o′ ℓ′ e′} {ℐ : MonoidalCategory o ℓ e}
                   (Braided-ℐ : Braided (MonoidalCategory.monoidal ℐ)) (C : MonoidalCategory o′ ℓ′ e′)
                 → GradedMonoidal Braided-ℐ (Trivial ℐ (MonoidalCategory.U C))
Trivial-monoidal Braided-ℐ C = record
  { _⊗₀_            = _⊗₀_
  ; unit            = unit
  ; _⊗₁_            = _⊗₁_
  ; ⊗-resp-≈        = λ f≈f′ g≈g′ → ⊗.F-resp-≈ (f≈f′ , g≈g′)
  ; ⊗-sub           = Equiv.refl
  ; ⊗-identity      = ⊗.identity
  ; ⊗-homomorphism  = Equiv.sym ⊗.homomorphism
  ; associator      = record
    { from = associator.from ; to = associator.to ; isoˡ = associator.isoˡ ; isoʳ = associator.isoʳ }
  ; unitorˡ         = record
    { from = unitorˡ.from ; to = unitorˡ.to ; isoˡ = unitorˡ.isoˡ ; isoʳ = unitorˡ.isoʳ }
  ; unitorʳ         = record
    { from = unitorʳ.from ; to = unitorʳ.to ; isoˡ = unitorʳ.isoˡ ; isoʳ = unitorʳ.isoʳ }
  ; assoc-commute   = assoc-commute-from
  ; unitorˡ-commute = unitorˡ-commute-from
  ; unitorʳ-commute = unitorʳ-commute-from
  ; triangle        = triangle
  ; pentagon        = pentagon
  }
  where open MonoidalCategory C

record GradedMonoidalFunctor {o ℓ e o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {ℐ : MonoidalCategory o ℓ e}
    {Braided-ℐ : Braided (MonoidalCategory.monoidal ℐ)} {L : LocallyGradedCategory ℐ o₁ ℓ₁ e₁}
    {M : LocallyGradedCategory ℐ o₂ ℓ₂ e₂} (GL : GradedMonoidal Braided-ℐ L) (GM : GradedMonoidal Braided-ℐ M)
    (F : LocallyGradedFunctor L M) : Set (o ⊔ o₁ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e₂) where
  private
    module ℐ = MonoidalCategory ℐ
    module I = Utilities.Shorthands ℐ.monoidal
    module L = LocallyGradedCategory L
    module GL = GradedMonoidal GL
  open LocallyGradedCategory M
  open GradedMonoidal GM
  open LocallyGradedFunctor F

  field
    ε      : Hom ℐ.unit unit (F₀ GL.unit)
    ⊗-homo : ∀ {A B} → Hom ℐ.unit (F₀ A ⊗₀ F₀ B) (F₀ (A GL.⊗₀ B))
    ⊗-homo-commute : ∀ {X Y A A′ B B′} {f : L.Hom X A A′} {g : L.Hom Y B B′}
                   → sub[ I.ρ⇒ ] (⊗-homo ∙ F₁ f ⊗₁ F₁ g) ≈ sub[ I.λ⇒ ] (F₁ (f GL.⊗₁ g) ∙ ⊗-homo)
    associativity : ∀ {A B C}
                  → sub[ I.α⇒ ℐ.⊗₁ ℐ.id ] (F₁ (GL.α⇒ {A} {B} {C}) ∙ ⊗-homo ∙ ⊗-homo ⊗₁ id)
                  ≈ ⊗-homo ∙ id ⊗₁ ⊗-homo ∙ α⇒
    unitaryˡ : ∀ {A} → sub[ I.λ⇒ ℐ.∘ (I.λ⇒ ℐ.∘ I.λ⇒ ℐ.⊗₁ ℐ.id) ℐ.⊗₁ ℐ.id ]
                         (F₁ (GL.λ⇒ {A}) ∙ ⊗-homo ∙ ε ⊗₁ id) ≈ λ⇒
    unitaryʳ : ∀ {A} → sub[ I.λ⇒ ℐ.∘ (I.λ⇒ ℐ.∘ I.λ⇒ ℐ.⊗₁ ℐ.id) ℐ.⊗₁ ℐ.id ]
                         (F₁ (GL.ρ⇒ {A}) ∙ ⊗-homo ∙ id ⊗₁ ε) ≈ ρ⇒
