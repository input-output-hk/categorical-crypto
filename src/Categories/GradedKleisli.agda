{-# OPTIONS --safe --without-K #-}

module Categories.GradedKleisli where

open import Level renaming (suc to lsuc)

open import Categories.Category
open import Categories.Category.EquivClosureHelper
open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Coherence.Monoidal.Tactic
open import Categories.Functor
open import Categories.Functor.Presheaf
open import Categories.Monad.Graded
import Categories.Morphism.Reasoning as MR
open import Categories.Tactic.Category

open import Data.Product

record UC-model {o ℓ e o′ ℓ′ e′ ℓs : Level}
              : Set (lsuc (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ ℓs)) where
  field C : Category o′ ℓ′ e′
        I : MonoidalCategory o ℓ e
        M : GradedMonad I C
        ℰ : Presheaf C (Sets ℓs)

module _ {o ℓ e o′ ℓ′ e′ : Level}
         (C : Category o′ ℓ′ e′) (I : MonoidalCategory o ℓ e)
         (M : GradedKleisliTriple I C) where
  module C where
    open Category C public
    open HomReasoning public
    open MR C public

  module I = MonoidalCategory I
  open I using (_⊗₀_; _⊗₁_; -⊗_; _⊗-; associator)
  open MonR (I.monoidal) using (_⟩⊗⟨refl)
  open Functor using (₁)
  open GradedKleisliTriple M
  open import Categories.Category.Monoidal.Utilities (I.monoidal)
  open Shorthands

  private
    μT : ∀ {u v X Y} (k : C [ X , T₀ v Y ]) → C [ μ u v C.∘ T₁ u k ≈ ext u k ]
    μT k = let open C in ext-T-fusion ○ ext-resp-≈ C.identityˡ

    Objᴳ : Set (o ⊔ o′)
    Objᴳ = I.Obj × C.Obj

    _⇒ᴳ_ : Objᴳ → Objᴳ → Set (o ⊔ ℓ ⊔ ℓ′)
    (i , c) ⇒ᴳ (j , d) = ∃[ k ] (C [ c , T₀ k d ]) × (I.U [ i ⊗₀ k , j ])

    _≈ᴳ_ : ∀ {A B} → (A ⇒ᴳ B) → (A ⇒ᴳ B) → Set (ℓ ⊔ e ⊔ e′)
    _≈ᴳ_ {ai , _} (i , f , α) (j , g , β) =
      Σ[ φ ∈ I.U [ i , j ] ] C [ sub φ C.∘ f ≈ g ] × I.U [ β I.∘ (₁ (ai ⊗-) φ) ≈ α ]

    idᴳ : ∀ {A} → A ⇒ᴳ A
    idᴳ = I.unit , return , ρ⇒

    _∘ᴳ_ : ∀ {A B D} → (B ⇒ᴳ D) → (A ⇒ᴳ B) → (A ⇒ᴳ D)
    (j , g , β) ∘ᴳ (i , f , α) =
      i ⊗₀ j , μ i j C.∘ T₁ i g C.∘ f , β I.∘ (₁ (-⊗ j) α) I.∘ α⇐

  GradedKleisli : Category (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)
  GradedKleisli = categoryHelperᵉ record
    { Obj       = Objᴳ
    ; _⇒_       = _⇒ᴳ_
    ; _≈_       = _≈ᴳ_
    ; id        = idᴳ
    ; _∘_       = _∘ᴳ_
    ; assoc     = λ where
      {Xi , _} {Yi , _} {Zi , _} {Wi , _} {a , f₀ , φf} {b , g₀ , φg} {c , h₀ , φh} →
          α⇐
        , (let open C in begin
             sub α⇐ C.∘ μ a (b ⊗₀ c) C.∘ T₁ a (μ b c C.∘ T₁ b h₀ C.∘ g₀) C.∘ f₀
               ≈⟨ refl⟩∘⟨ pullˡ (μT (μ b c C.∘ T₁ b h₀ C.∘ g₀)) ⟩
             sub α⇐ C.∘ ext a (μ b c C.∘ T₁ b h₀ C.∘ g₀) C.∘ f₀
               ≈⟨ refl⟩∘⟨ (ext-resp-≈ (pullˡ (μT h₀)) ⟩∘⟨refl) ⟩
             sub α⇐ C.∘ ext a (ext b h₀ C.∘ g₀) C.∘ f₀
               ≈⟨ refl⟩∘⟨ (ext-assoc ⟩∘⟨refl) ⟩
             sub α⇐ C.∘ (sub α⇒ C.∘ (ext (a ⊗₀ b) h₀ C.∘ ext a g₀)) C.∘ f₀
               ≈⟨ solve C ⟩
             sub α⇐ C.∘ sub α⇒ C.∘ (ext (a ⊗₀ b) h₀ C.∘ ext a g₀) C.∘ f₀
               ≈⟨ cancelˡ (⟺ sub-homomorphism ○ sub-resp-≈ associator.isoˡ ○ sub-identity) ⟩
             (ext (a ⊗₀ b) h₀ C.∘ ext a g₀) C.∘ f₀
               ≈⟨ (⟺ (μT h₀) ⟩∘⟨ ⟺ (μT g₀)) ⟩∘⟨refl ⟩
             ((μ (a ⊗₀ b) c C.∘ T₁ (a ⊗₀ b) h₀) C.∘ (μ a b C.∘ T₁ a g₀)) C.∘ f₀
               ≈⟨ solve C ⟩
             μ (a ⊗₀ b) c C.∘ T₁ (a ⊗₀ b) h₀ C.∘ μ a b C.∘ T₁ a g₀ C.∘ f₀ ∎)
        , solve-mor I
    ; identityˡ = λ where
      {ai , _} {B , _} {i , _ , α} →
          ρ⇒
        , (let open C in assoc²εβ ○ elimˡ μ-identityʳ)
        , solve-mor I
    ; identityʳ = λ where
      {ai , _} {B , _} {i , _ , α} →
          λ⇒
        , (let open C in (refl⟩∘⟨ refl⟩∘⟨ ⟺ return-commute) ○ assoc²εβ ○ elimˡ μ-identityˡ)
        , solve-mor I
    ; ∘-resp-≈ = λ where
      {Ai , _} {Bi , _} {Ci , _}
        {fk , ff , fα} {hk , hf , hα} {gk , gf , gα} {ik , if′ , iα}
        (φ , cf , ifh) (ψ , cg , igi) →
          ψ ⊗₁ φ
        , (let open C in begin
             sub (ψ ⊗₁ φ) C.∘ (μ gk fk C.∘ T₁ gk ff C.∘ gf)  ≈⟨ refl⟩∘⟨ pullˡ (μT ff) ⟩
             sub (ψ ⊗₁ φ) C.∘ (ext gk ff C.∘ gf)             ≈⟨ pullˡ (⟺ sub-commute) ⟩
             (ext ik (sub φ C.∘ ff) C.∘ sub ψ) C.∘ gf        ≈⟨ C.assoc ⟩
             ext ik (sub φ C.∘ ff) C.∘ (sub ψ C.∘ gf)        ≈⟨ ext-resp-≈ cf ⟩∘⟨ cg ⟩
             ext ik hf C.∘ if′                               ≈⟨ ⟺ (pullˡ (μT hf)) ⟩
             μ ik hk C.∘ T₁ ik hf C.∘ if′ ∎)
        , (let open Category.HomReasoning (I.U)
           in begin
             (hα I.∘ (iα ⊗₁ I.id) I.∘ α⇐) I.∘ (I.id ⊗₁ (ψ ⊗₁ φ))
               ≈⟨ solve-mor I ⟩
             (hα I.∘ I.id ⊗₁ φ) I.∘ (iα I.∘ I.id ⊗₁ ψ) ⊗₁ I.id I.∘ α⇐
               ≈⟨ ifh ⟩∘⟨ (igi ⟩⊗⟨refl ⟩∘⟨refl) ⟩
             fα I.∘ (gα ⊗₁ I.id) I.∘ α⇐ ∎)
    }
