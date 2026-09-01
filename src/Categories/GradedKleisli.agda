{-# OPTIONS --safe --without-K #-}

module Categories.GradedKleisli where

open import Level using (Level; _⊔_) renaming (suc to lsuc)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.EquivClosureHelper using (categoryHelperᵉ)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Monoidal using (MonoidalCategory)
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Coherence.Monoidal using (module MorAtoms; module MorSolve)
open import Categories.Functor using (Functor)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Monad.Graded using (GradedMonad; GradedKleisliTriple)
import Categories.Morphism.Reasoning as MR
open import Categories.Tactic.Category using (solve)

open import Data.Fin using (Fin; #_)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; _,_)
open import Data.Vec using (_∷_; [])

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

  GradedKleisli : Category (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)
  GradedKleisli = categoryHelperᵉ record
    { Obj       = I.Obj × C.Obj
    ; _⇒_       = λ where (i , c) (j , d) → ∃[ k ] (C [ c , T₀ k d ]) × (I.U [ i ⊗₀ k , j ])
    ; _≈_       = λ where
      {ai , _} (i , f , α) (j , g , β) →
        Σ[ φ ∈ I.U [ i , j ] ] C [ sub φ C.∘ f ≈ g ] × I.U [ β I.∘ (₁ (ai ⊗-) φ) ≈ α ]
    ; id        = I.unit , return , ρ⇒
    ; _∘_       = λ where
      (j , g , β) (i , f , α) → i ⊗₀ j , μ i j C.∘ T₁ i g C.∘ f , β I.∘ (₁ (-⊗ j) α) I.∘ α⇐
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
        , (let vs = Xi ∷ a ∷ b ∷ c ∷ Yi ∷ Zi ∷ Wi ∷ []
               open MorAtoms I vs
               open MorSolve I vs
                    ( ((V (# 0) ⊗ᵒ V (# 1) , V (# 4)) , φf)
                    ∷ ((V (# 4) ⊗ᵒ V (# 2) , V (# 5)) , φg)
                    ∷ ((V (# 5) ⊗ᵒ V (# 3) , V (# 6)) , φh) ∷ [] )
           in solveMor!
                ((gen (# 2) S.∘ (gen (# 1) S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐) S.⊗₁ S.id S.∘ S.α⇐)
                   S.∘ S.id S.⊗₁ S.α⇐)
                ((gen (# 2) S.∘ gen (# 1) S.⊗₁ S.id S.∘ S.α⇐) S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐))
    ; identityˡ = λ where
      {ai , _} {B , _} {i , _ , α} →
          ρ⇒
        , (let open C in assoc²εβ ○ elimˡ μ-identityʳ)
        , (let vs = ai ∷ i ∷ B ∷ []
               open MorAtoms I vs
               open MorSolve I vs (((V (# 0) ⊗ᵒ V (# 1) , V (# 2)) , α) ∷ [])
           in solveMor! (gen (# 0) S.∘ S.id S.⊗₁ S.ρ⇒) (S.ρ⇒ S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐))
    ; identityʳ = λ where
      {ai , _} {B , _} {i , _ , α} →
          λ⇒
        , (let open C in (refl⟩∘⟨ refl⟩∘⟨ ⟺ return-commute) ○ assoc²εβ ○ elimˡ μ-identityˡ)
        , (let vs = ai ∷ i ∷ B ∷ []
               open MorAtoms I vs
               open MorSolve I vs (((V (# 0) ⊗ᵒ V (# 1) , V (# 2)) , α) ∷ [])
           in solveMor! (gen (# 0) S.∘ S.id S.⊗₁ S.λ⇒) (gen (# 0) S.∘ S.ρ⇒ S.⊗₁ S.id S.∘ S.α⇐))
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
               vs = Ai ∷ Bi ∷ Ci ∷ fk ∷ gk ∷ hk ∷ ik ∷ []
               open MorAtoms I vs
               open MorSolve I vs
                    ( ((V (# 1) ⊗ᵒ V (# 5) , V (# 2)) , hα)
                    ∷ ((V (# 0) ⊗ᵒ V (# 6) , V (# 1)) , iα)
                    ∷ ((V (# 3)             , V (# 5)) , φ)
                    ∷ ((V (# 4)             , V (# 6)) , ψ) ∷ [] )
           in begin
             (hα I.∘ (iα ⊗₁ I.id) I.∘ α⇐) I.∘ (I.id ⊗₁ (ψ ⊗₁ φ))
               ≈⟨ solveMor! ((gen (# 0) S.∘ (gen (# 1) S.⊗₁ S.id) S.∘ S.α⇐)
                               S.∘ S.id S.⊗₁ (gen (# 3) S.⊗₁ gen (# 2)))
                            ((gen (# 0) S.∘ S.id S.⊗₁ gen (# 2))
                               S.∘ (gen (# 1) S.∘ S.id S.⊗₁ gen (# 3)) S.⊗₁ S.id S.∘ S.α⇐) ⟩
             (hα I.∘ I.id ⊗₁ φ) I.∘ (iα I.∘ I.id ⊗₁ ψ) ⊗₁ I.id I.∘ α⇐
               ≈⟨ ifh ⟩∘⟨ (igi ⟩⊗⟨refl ⟩∘⟨refl) ⟩
             fα I.∘ (gα ⊗₁ I.id) I.∘ α⇐ ∎)
    }
