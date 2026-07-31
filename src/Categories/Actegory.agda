{-# OPTIONS --safe --without-K #-}

-- Categories with an action of a monoidal category

module Categories.Actegory where

open import Level

open import Categories.Category
open import Categories.Category.Construction.Functors
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Utilities as Utilities
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Monoidal
open import Categories.Functor.Properties
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation hiding (id)
import Categories.NaturalTransformation.NaturalIsomorphism as NI
open import Categories.NaturalTransformation.NaturalIsomorphism.Functors

open import Data.Product

record Actegory {o ℓ e o′ ℓ′ e′} (ℐ : MonoidalCategory o ℓ e)
    (𝒞 : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module ℐ = MonoidalCategory ℐ
    module 𝒞 = Category 𝒞
  open ℐ using (_⊗₀_; _⊗₁_)
  open 𝒞
  open 𝒞.HomReasoning
  open Morphism 𝒞
  open MR 𝒞
  open Utilities.Shorthands ℐ.monoidal

  infix 10 _∗₀_ _∗₁_

  field
    _∗₀_ : ℐ.Obj → 𝒞.Obj → 𝒞.Obj
    _∗₁_ : ∀ {x x′ A B} → x ℐ.⇒ x′ → A ⇒ B → x ∗₀ A ⇒ x′ ∗₀ B
    ∗-resp-≈ : ∀ {x x′ A B} {v v′ : x ℐ.⇒ x′} {f f′ : A ⇒ B}
             → v ℐ.≈ v′ → f ≈ f′ → v ∗₁ f ≈ v′ ∗₁ f′
    ∗-identity : ∀ {x A} → ℐ.id {x} ∗₁ 𝒞.id {A} ≈ 𝒞.id
    ∗-homomorphism : ∀ {x x′ x″ A B C} {v : x ℐ.⇒ x′} {w : x′ ℐ.⇒ x″}
                     {f : A ⇒ B} {g : B ⇒ C}
                   → (w ℐ.∘ v) ∗₁ (g ∘ f) ≈ (w ∗₁ g) ∘ (v ∗₁ f)

    unitor        : ∀ {A} → ℐ.unit ∗₀ A ≅ A
    multiplicator : ∀ {x y A} → (x ⊗₀ y) ∗₀ A ≅ x ∗₀ (y ∗₀ A)

  module unitor {A} = _≅_ (unitor {A})
  module multiplicator {x y A} = _≅_ (multiplicator {x} {y} {A})

  field
    unitor-commute : ∀ {A B} {f : A ⇒ B}
                   → unitor.from ∘ (ℐ.id ∗₁ f) ≈ f ∘ unitor.from
    multiplicator-commute : ∀ {x x′ y y′ A B} {v : x ℐ.⇒ x′} {w : y ℐ.⇒ y′}
                            {f : A ⇒ B}
      → multiplicator.from ∘ ((v ⊗₁ w) ∗₁ f) ≈ (v ∗₁ (w ∗₁ f)) ∘ multiplicator.from

    -- the strong-monoidal-functor coherences
    assoc-coherence : ∀ {x y z A}
      → multiplicator.from ∘ multiplicator.from {x ⊗₀ y} {z} {A}
          ≈ (ℐ.id ∗₁ multiplicator.from) ∘ (multiplicator.from ∘ (α⇒ ∗₁ 𝒞.id))
    unitˡ-coherence : ∀ {y A}
      → unitor.from ∘ multiplicator.from {ℐ.unit} {y} {A} ≈ λ⇒ ∗₁ 𝒞.id
    unitʳ-coherence : ∀ {x A}
      → (ℐ.id ∗₁ unitor.from) ∘ multiplicator.from {x} {ℐ.unit} {A} ≈ ρ⇒ ∗₁ 𝒞.id

  decompˡ : ∀ {x x′ A B} {v : x ℐ.⇒ x′} {f : A ⇒ B}
          → (v ∗₁ 𝒞.id) ∘ (ℐ.id ∗₁ f) ≈ v ∗₁ f
  decompˡ = ⟺ ∗-homomorphism ○ ∗-resp-≈ ℐ.identityʳ 𝒞.identityˡ

  decompʳ : ∀ {x x′ A B} {v : x ℐ.⇒ x′} {f : A ⇒ B}
          → (ℐ.id ∗₁ f) ∘ (v ∗₁ 𝒞.id) ≈ v ∗₁ f
  decompʳ = ⟺ ∗-homomorphism ○ ∗-resp-≈ ℐ.identityˡ 𝒞.identityʳ

  cancel∗ : ∀ {x x′ A B} {v : x ℐ.⇒ x′} {v′ : x′ ℐ.⇒ x} {f : A ⇒ B} {f′ : B ⇒ A}
          → v′ ℐ.∘ v ℐ.≈ ℐ.id → f′ ∘ f ≈ 𝒞.id → (v′ ∗₁ f′) ∘ (v ∗₁ f) ≈ 𝒞.id
  cancel∗ p q = ⟺ ∗-homomorphism ○ ∗-resp-≈ p q ○ ∗-identity

  id∗≅ : ∀ {x A B} → A ≅ B → (x ∗₀ A) ≅ (x ∗₀ B)
  id∗≅ i = record
    { from = ℐ.id ∗₁ _≅_.from i
    ; to   = ℐ.id ∗₁ _≅_.to i
    ; iso  = record
      { isoˡ = cancel∗ ℐ.identity² (_≅_.isoˡ i)
      ; isoʳ = cancel∗ ℐ.identity² (_≅_.isoʳ i) } }

  unitor-commute-to : ∀ {A B} {f : A ⇒ B}
                    → unitor.to ∘ f ≈ (ℐ.id ∗₁ f) ∘ unitor.to
  unitor-commute-to {f = f} = begin
      unitor.to ∘ f
    ≈⟨ refl⟩∘⟨ insertʳ unitor.isoʳ ⟩
      unitor.to ∘ ((f ∘ unitor.from) ∘ unitor.to)
    ≈˘⟨ refl⟩∘⟨ unitor-commute ⟩∘⟨refl ⟩
      unitor.to ∘ ((unitor.from ∘ (ℐ.id ∗₁ f)) ∘ unitor.to)
    ≈⟨ refl⟩∘⟨ assoc ⟩
      unitor.to ∘ (unitor.from ∘ ((ℐ.id ∗₁ f) ∘ unitor.to))
    ≈⟨ cancelˡ unitor.isoˡ ⟩
      (ℐ.id ∗₁ f) ∘ unitor.to ∎

  multiplicator-commute-to : ∀ {x x′ y y′ A B} {v : x ℐ.⇒ x′} {w : y ℐ.⇒ y′} {f : A ⇒ B}
    → multiplicator.to {x′} {y′} {B} ∘ (v ∗₁ (w ∗₁ f))
        ≈ ((v ⊗₁ w) ∗₁ f) ∘ multiplicator.to {x} {y} {A}
  multiplicator-commute-to {v = v} {w} {f} = begin
      multiplicator.to ∘ (v ∗₁ (w ∗₁ f))
    ≈⟨ refl⟩∘⟨ insertʳ multiplicator.isoʳ ⟩
      multiplicator.to ∘ (((v ∗₁ (w ∗₁ f)) ∘ multiplicator.from) ∘ multiplicator.to)
    ≈˘⟨ refl⟩∘⟨ multiplicator-commute ⟩∘⟨refl ⟩
      multiplicator.to ∘ ((multiplicator.from ∘ ((v ⊗₁ w) ∗₁ f)) ∘ multiplicator.to)
    ≈⟨ refl⟩∘⟨ assoc ⟩
      multiplicator.to ∘ (multiplicator.from ∘ (((v ⊗₁ w) ∗₁ f) ∘ multiplicator.to))
    ≈⟨ cancelˡ multiplicator.isoˡ ⟩
      ((v ⊗₁ w) ∗₁ f) ∘ multiplicator.to ∎

  private
    assoc-core : ∀ {x y z A}
               → multiplicator.from {x} {y ⊗₀ z} {A}
                   ∘ ((α⇒ ∗₁ 𝒞.id) ∘ (multiplicator.to {x ⊗₀ y} {z} {A}
                       ∘ multiplicator.to {x} {y} {z ∗₀ A}))
                 ≈ ℐ.id ∗₁ multiplicator.to {y} {z} {A}
    assoc-core = begin
        multiplicator.from ∘ ((α⇒ ∗₁ 𝒞.id) ∘ (multiplicator.to ∘ multiplicator.to))
      ≈⟨ pullˡ (Switch.switch-fromtoˡ (id∗≅ multiplicator) (⟺ assoc-coherence)) ⟩
        ((ℐ.id ∗₁ multiplicator.to) ∘ (multiplicator.from ∘ multiplicator.from))
          ∘ (multiplicator.to ∘ multiplicator.to)
      ≈⟨ assoc ⟩
        (ℐ.id ∗₁ multiplicator.to)
          ∘ ((multiplicator.from ∘ multiplicator.from) ∘ (multiplicator.to ∘ multiplicator.to))
      ≈⟨ refl⟩∘⟨ cancelInner multiplicator.isoʳ ⟩
        (ℐ.id ∗₁ multiplicator.to) ∘ (multiplicator.from ∘ multiplicator.to)
      ≈⟨ elimʳ multiplicator.isoʳ ⟩
        ℐ.id ∗₁ multiplicator.to ∎

  assoc-coherence-to : ∀ {x y z A}
    → (α⇒ ∗₁ 𝒞.id) ∘ (multiplicator.to {x ⊗₀ y} {z} {A} ∘ multiplicator.to {x} {y} {z ∗₀ A})
        ≈ multiplicator.to {x} {y ⊗₀ z} {A} ∘ (ℐ.id ∗₁ multiplicator.to {y} {z} {A})
  assoc-coherence-to = Switch.switch-fromtoˡ multiplicator assoc-core

  unitˡ-coherence-to : ∀ {y A}
    → (λ⇒ ∗₁ 𝒞.id) ∘ (multiplicator.to {ℐ.unit} {y} {A} ∘ unitor.to) ≈ 𝒞.id
  unitˡ-coherence-to =
    (⟺ unitˡ-coherence ⟩∘⟨refl) ○ cancelInner multiplicator.isoʳ ○ unitor.isoʳ

  unitʳ-coherence-to : ∀ {x A}
    → (ρ⇒ ∗₁ 𝒞.id) ∘ (multiplicator.to {x} {ℐ.unit} {A} ∘ (ℐ.id ∗₁ unitor.to)) ≈ 𝒞.id
  unitʳ-coherence-to =
    (⟺ unitʳ-coherence ⟩∘⟨refl) ○ cancelInner multiplicator.isoʳ
      ○ cancel∗ ℐ.identity² unitor.isoʳ

--------------------------------------------------------------------------------
-- An actegory is the same thing as a strong monoidal functor into the
-- endofunctor category under composition.
--------------------------------------------------------------------------------

module _ {o ℓ e o′ ℓ′ e′} {ℐ : MonoidalCategory o ℓ e} {𝒞 : Category o′ ℓ′ e′} where
  private
    module ℐ = MonoidalCategory ℐ

  open Category 𝒞
  open HomReasoning
  open MR 𝒞
  open Morphism 𝒞
  open ℐ using (_⊗₀_; _⊗₁_)
  open Utilities.Shorthands ℐ.monoidal
  open Functor
  open NaturalTransformation

  open import Categories.Category.Monoidal.Construction.Endofunctors 𝒞

  private module MFs = Morphism (Functors 𝒞 𝒞)

  Actegory⇒StrongMonoidal : Actegory ℐ 𝒞 → StrongMonoidalFunctor ℐ Endofunctors
  Actegory⇒StrongMonoidal Act = record
    { F = ∗F
    ; isStrongMonoidal = record
      { ε      = NI⇒Functors-iso (NI.sym (NI.niHelper (record
          { η       = λ _ → unitor.from
          ; η⁻¹     = λ _ → unitor.to
          ; commute = λ _ → unitor-commute
          ; iso     = λ _ → record { isoˡ = unitor.isoˡ ; isoʳ = unitor.isoʳ } })))
      ; ⊗-homo = NI.sym (NI.niHelper (record
          { η       = λ (x , y) → mult-from-NT x y
          ; η⁻¹     = λ (x , y) → mult-to-NT x y
          ; commute = λ (v , w) →
              multiplicator-commute ○ ∘-resp-≈ˡ (⟺ decompʳ)
          ; iso     = λ _ → record
              { isoˡ = multiplicator.isoˡ ; isoʳ = multiplicator.isoʳ } }))
      ; associativity = begin
          (α⇒ ∗₁ id) ∘ (multiplicator.to ∘ ((ℐ.id ∗₁ id) ∘ multiplicator.to))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ ∗-identity ⟩
          (α⇒ ∗₁ id) ∘ (multiplicator.to ∘ multiplicator.to)
        ≈⟨ assoc-coherence-to ⟩
          multiplicator.to ∘ (ℐ.id ∗₁ multiplicator.to)
        ≈˘⟨ refl⟩∘⟨ (identityʳ ○ identityʳ) ⟩
          multiplicator.to ∘ (((ℐ.id ∗₁ multiplicator.to) ∘ id) ∘ id) ∎
      ; unitaryˡ = (refl⟩∘⟨ refl⟩∘⟨ elimˡ ∗-identity) ○ unitˡ-coherence-to
      ; unitaryʳ = (refl⟩∘⟨ refl⟩∘⟨ identityʳ) ○ unitʳ-coherence-to
      }
    }
    where
    open Actegory Act

    F₀∗ : ℐ.Obj → Functor 𝒞 𝒞
    F₀∗ x = record
      { F₀           = x ∗₀_
      ; F₁           = ℐ.id ∗₁_
      ; identity     = ∗-identity
      ; homomorphism = ∗-resp-≈ (ℐ.Equiv.sym ℐ.identity²) Equiv.refl ○ ∗-homomorphism
      ; F-resp-≈     = ∗-resp-≈ ℐ.Equiv.refl
      }

    F₁∗ : ∀ {x x′} → x ℐ.⇒ x′ → NaturalTransformation (F₀∗ x) (F₀∗ x′)
    F₁∗ v = ntHelper record
      { η       = λ _ → v ∗₁ id
      ; commute = λ _ → decompˡ ○ ⟺ decompʳ
      }

    ∗F : Functor ℐ.U (Functors 𝒞 𝒞)
    ∗F = record
      { F₀           = F₀∗
      ; F₁           = F₁∗
      ; identity     = ∗-identity
      ; homomorphism = ∗-resp-≈ ℐ.Equiv.refl (⟺ identity²) ○ ∗-homomorphism
      ; F-resp-≈     = λ v≈ → ∗-resp-≈ v≈ Equiv.refl
      }

    fromSq : ∀ {x y A B} {f : A ⇒ B}
           → multiplicator.from ∘ (ℐ.id {x ⊗₀ y} ∗₁ f)
               ≈ (ℐ.id ∗₁ (ℐ.id ∗₁ f)) ∘ multiplicator.from
    fromSq = (refl⟩∘⟨ ∗-resp-≈ (ℐ.Equiv.sym (identity ℐ.⊗)) Equiv.refl) ○ multiplicator-commute

    mult-from-NT : ∀ x y → NaturalTransformation (F₀∗ (x ⊗₀ y)) (F₀∗ x ∘F F₀∗ y)
    mult-from-NT x y = ntHelper record
      { η = λ _ → multiplicator.from ; commute = λ _ → fromSq }

    mult-to-NT : ∀ x y → NaturalTransformation (F₀∗ x ∘F F₀∗ y) (F₀∗ (x ⊗₀ y))
    mult-to-NT x y = ntHelper record
      { η       = λ _ → multiplicator.to
      ; commute = λ _ →
          multiplicator-commute-to ○ (∗-resp-≈ (identity ℐ.⊗) Equiv.refl ⟩∘⟨refl)
      }

  StrongMonoidal⇒Actegory : StrongMonoidalFunctor ℐ Endofunctors → Actegory ℐ 𝒞
  StrongMonoidal⇒Actegory SM = record
    { _∗₀_ = λ x A → F₀ (M.F₀ x) A
    ; _∗₁_ = λ v f → η (M.F₁ v) _ ∘ F₁ (M.F₀ _) f
    ; ∗-resp-≈ = λ v≈ f≈ → M.F-resp-≈ v≈ ⟩∘⟨ F-resp-≈ (M.F₀ _) f≈
    ; ∗-identity = (M.identity ⟩∘⟨ identity (M.F₀ _)) ○ identity²
    ; ∗-homomorphism = λ {x} {x′} {x″} {A} {B} {C} {v} {w} {f} {g} → begin
        η (M.F₁ (w ℐ.∘ v)) C ∘ F₁ (M.F₀ x) (g ∘ f)
      ≈⟨ M.homomorphism ⟩∘⟨ homomorphism (M.F₀ x) ⟩
        (η (M.F₁ w) C ∘ η (M.F₁ v) C) ∘ (F₁ (M.F₀ x) g ∘ F₁ (M.F₀ x) f)
      ≈⟨ center (commute (M.F₁ v) g) ⟩
        η (M.F₁ w) C ∘ ((F₁ (M.F₀ x′) g ∘ η (M.F₁ v) B) ∘ F₁ (M.F₀ x) f)
      ≈⟨ refl⟩∘⟨ assoc ⟩
        η (M.F₁ w) C ∘ (F₁ (M.F₀ x′) g ∘ (η (M.F₁ v) B ∘ F₁ (M.F₀ x) f))
      ≈⟨ sym-assoc ⟩
        (η (M.F₁ w) C ∘ F₁ (M.F₀ x′) g) ∘ (η (M.F₁ v) B ∘ F₁ (M.F₀ x) f) ∎
    ; unitor = record
        { from = η M.ε.to _
        ; to   = η M.ε.from _
        ; iso  = record { isoˡ = M.ε.isoʳ ; isoʳ = M.ε.isoˡ } }
    ; multiplicator = λ {x} {y} {A} → record
        { from = η (M.⊗-homo.⇐.η (x , y)) A
        ; to   = η (M.⊗-homo.⇒.η (x , y)) A
        ; iso  = record
          { isoˡ = MFs.Iso.isoʳ (M.⊗-homo.iso (x , y))
          ; isoʳ = MFs.Iso.isoˡ (M.⊗-homo.iso (x , y)) } }
    ; unitor-commute = λ {A} {B} {f} → begin
        η M.ε.to B ∘ (η (M.F₁ ℐ.id) B ∘ F₁ (M.F₀ ℐ.unit) f)
      ≈⟨ refl⟩∘⟨ elimˡ M.identity ⟩
        η M.ε.to B ∘ F₁ (M.F₀ ℐ.unit) f
      ≈⟨ commute M.ε.to f ⟩
        f ∘ η M.ε.to A ∎
    ; multiplicator-commute = λ {x} {x′} {y} {y′} {A} {B} {v} {w} {f} → begin
        η (M.⊗-homo.⇐.η (x′ , y′)) B ∘ (η (M.F₁ (v ⊗₁ w)) B ∘ F₁ (M.F₀ (x ⊗₀ y)) f)
      ≈⟨ pullˡ (commute M.⊗-homo.F⇐G (v , w)) ⟩
        ((F₁ (M.F₀ x′) (η (M.F₁ w) B) ∘ η (M.F₁ v) (F₀ (M.F₀ y) B))
          ∘ η (M.⊗-homo.⇐.η (x , y)) B) ∘ F₁ (M.F₀ (x ⊗₀ y)) f
      ≈⟨ pullʳ (commute (M.⊗-homo.⇐.η (x , y)) f) ⟩
        (F₁ (M.F₀ x′) (η (M.F₁ w) B) ∘ η (M.F₁ v) (F₀ (M.F₀ y) B))
          ∘ (F₁ (M.F₀ x) (F₁ (M.F₀ y) f) ∘ η (M.⊗-homo.⇐.η (x , y)) A)
      ≈˘⟨ commute (M.F₁ v) (η (M.F₁ w) B) ⟩∘⟨refl ⟩
        (η (M.F₁ v) (F₀ (M.F₀ y′) B) ∘ F₁ (M.F₀ x) (η (M.F₁ w) B))
          ∘ (F₁ (M.F₀ x) (F₁ (M.F₀ y) f) ∘ η (M.⊗-homo.⇐.η (x , y)) A)
      ≈⟨ center (⟺ (homomorphism (M.F₀ x))) ⟩
        η (M.F₁ v) (F₀ (M.F₀ y′) B)
          ∘ (F₁ (M.F₀ x) (η (M.F₁ w) B ∘ F₁ (M.F₀ y) f) ∘ η (M.⊗-homo.⇐.η (x , y)) A)
      ≈⟨ sym-assoc ⟩
        (η (M.F₁ v) (F₀ (M.F₀ y′) B) ∘ F₁ (M.F₀ x) (η (M.F₁ w) B ∘ F₁ (M.F₀ y) f))
          ∘ η (M.⊗-homo.⇐.η (x , y)) A ∎
    ; assoc-coherence = λ {x} {y} {z} {A} → ⟺ (begin
        (η (M.F₁ ℐ.id) _ ∘ F₁ (M.F₀ x) (η (M.⊗-homo.⇐.η (y , z)) A))
          ∘ (η (M.⊗-homo.⇐.η (x , y ⊗₀ z)) A
            ∘ (η (M.F₁ α⇒) A ∘ F₁ (M.F₀ ((x ⊗₀ y) ⊗₀ z)) id))
      ≈⟨ elimˡ M.identity ⟩∘⟨ refl⟩∘⟨ elimʳ (identity (M.F₀ ((x ⊗₀ y) ⊗₀ z))) ⟩
        F₁ (M.F₀ x) (η (M.⊗-homo.⇐.η (y , z)) A)
          ∘ (η (M.⊗-homo.⇐.η (x , y ⊗₀ z)) A ∘ η (M.F₁ α⇒) A)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ E2 ⟩
        F₁ (M.F₀ x) (η (M.⊗-homo.⇐.η (y , z)) A)
          ∘ (η (M.⊗-homo.⇐.η (x , y ⊗₀ z)) A
            ∘ (((η (M.⊗-homo.⇒.η (x , y ⊗₀ z)) A
                  ∘ F₁ (M.F₀ x) (η (M.⊗-homo.⇒.η (y , z)) A))
                ∘ η (M.⊗-homo.⇐.η (x , y)) (F₀ (M.F₀ z) A))
              ∘ η (M.⊗-homo.⇐.η (x ⊗₀ y , z)) A))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
        F₁ (M.F₀ x) (η (M.⊗-homo.⇐.η (y , z)) A)
          ∘ (η (M.⊗-homo.⇐.η (x , y ⊗₀ z)) A
            ∘ ((η (M.⊗-homo.⇒.η (x , y ⊗₀ z)) A
                 ∘ F₁ (M.F₀ x) (η (M.⊗-homo.⇒.η (y , z)) A))
              ∘ (η (M.⊗-homo.⇐.η (x , y)) (F₀ (M.F₀ z) A)
                ∘ η (M.⊗-homo.⇐.η (x ⊗₀ y , z)) A)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
        F₁ (M.F₀ x) (η (M.⊗-homo.⇐.η (y , z)) A)
          ∘ (η (M.⊗-homo.⇐.η (x , y ⊗₀ z)) A
            ∘ (η (M.⊗-homo.⇒.η (x , y ⊗₀ z)) A
              ∘ (F₁ (M.F₀ x) (η (M.⊗-homo.⇒.η (y , z)) A)
                ∘ (η (M.⊗-homo.⇐.η (x , y)) (F₀ (M.F₀ z) A)
                  ∘ η (M.⊗-homo.⇐.η (x ⊗₀ y , z)) A))))
      ≈⟨ refl⟩∘⟨ cancelˡ (MFs.Iso.isoˡ (M.⊗-homo.iso (x , y ⊗₀ z))) ⟩
        F₁ (M.F₀ x) (η (M.⊗-homo.⇐.η (y , z)) A)
          ∘ (F₁ (M.F₀ x) (η (M.⊗-homo.⇒.η (y , z)) A)
            ∘ (η (M.⊗-homo.⇐.η (x , y)) (F₀ (M.F₀ z) A)
              ∘ η (M.⊗-homo.⇐.η (x ⊗₀ y , z)) A))
      ≈⟨ cancelˡ (_≅_.isoˡ ([ M.F₀ x ]-resp-≅ (mult≅ y z))) ⟩
        η (M.⊗-homo.⇐.η (x , y)) (F₀ (M.F₀ z) A)
          ∘ η (M.⊗-homo.⇐.η (x ⊗₀ y , z)) A ∎)
    ; unitˡ-coherence = λ {y} {A} →
        ⟺ (Eˡ y) ○ ⟺ (elimʳ (identity (M.F₀ (ℐ.unit ⊗₀ y))))
    ; unitʳ-coherence = λ {x} {A} →
        (elimˡ M.identity ⟩∘⟨refl) ○ ⟺ (Eʳ x) ○ ⟺ (elimʳ (identity (M.F₀ (x ⊗₀ ℐ.unit))))
    }
    where
    module M = StrongMonoidalFunctor SM

    mult≅ : ∀ x y {A} → F₀ (M.F₀ x) (F₀ (M.F₀ y) A) ≅ F₀ (M.F₀ (x ⊗₀ y)) A
    mult≅ x y = record
      { from = η (M.⊗-homo.⇒.η (x , y)) _
      ; to   = η (M.⊗-homo.⇐.η (x , y)) _
      ; iso  = record
        { isoˡ = MFs.Iso.isoˡ (M.⊗-homo.iso (x , y))
        ; isoʳ = MFs.Iso.isoʳ (M.⊗-homo.iso (x , y)) } }

    ε≅ : ∀ {A} → A ≅ F₀ (M.F₀ ℐ.unit) A
    ε≅ = record
      { from = η M.ε.from _
      ; to   = η M.ε.to _
      ; iso  = record { isoˡ = M.ε.isoˡ ; isoʳ = M.ε.isoʳ } }

    -- to-direction unit laws, extracted from M's coherences by switching isos
    Eˡ : ∀ y {A} → η (M.F₁ λ⇒) A
       ≈ η M.ε.to (F₀ (M.F₀ y) A) ∘ η (M.⊗-homo.⇐.η (ℐ.unit , y)) A
    Eˡ y = Switch.switch-fromtoʳ (mult≅ ℐ.unit y)
      (Switch.switch-fromtoʳ ε≅
        (assoc
          ○ ⟺ (refl⟩∘⟨ refl⟩∘⟨ elimˡ (identity (M.F₀ ℐ.unit)))
          ○ M.unitaryˡ)
        ○ identityˡ)

    Eʳ : ∀ x {A} → η (M.F₁ ρ⇒) A
       ≈ F₁ (M.F₀ x) (η M.ε.to A) ∘ η (M.⊗-homo.⇐.η (x , ℐ.unit)) A
    Eʳ x = Switch.switch-fromtoʳ (mult≅ x ℐ.unit)
      (Switch.switch-fromtoʳ ([ M.F₀ x ]-resp-≅ ε≅)
        (assoc
          ○ ⟺ (refl⟩∘⟨ refl⟩∘⟨ identityʳ)
          ○ M.unitaryʳ)
        ○ identityˡ)

    E2 : ∀ {x y z A} → η (M.F₁ (α⇒ {x} {y} {z})) A
       ≈ ((η (M.⊗-homo.⇒.η (x , y ⊗₀ z)) A
            ∘ F₁ (M.F₀ x) (η (M.⊗-homo.⇒.η (y , z)) A))
          ∘ η (M.⊗-homo.⇐.η (x , y)) (F₀ (M.F₀ z) A))
         ∘ η (M.⊗-homo.⇐.η (x ⊗₀ y , z)) A
    E2 {x} {y} {z} {A} = Switch.switch-fromtoʳ (mult≅ (x ⊗₀ y) z)
      (Switch.switch-fromtoʳ (mult≅ x y)
        (assoc
          ○ ⟺ (refl⟩∘⟨ refl⟩∘⟨ elimˡ (identity (M.F₀ (x ⊗₀ y))))
          ○ M.associativity
          ○ (refl⟩∘⟨ (identityʳ ○ identityʳ))))
