{-# OPTIONS --safe --without-K #-}

-- Change of grading along a (lax) monoidal functor Φ : 𝒥 → ℐ: the functor
-- `Regrade : Kl(Φ*ℳ) → Kl(ℳ)`.  Downstream handles are `Klℐ` and `Kl𝒥` (the
-- source and target categories) together with `Regrade₀`/`Regrade₁`.

module Categories.GradedKleisli.Regrade where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Functor
open import Categories.Functor.Monoidal
open import Categories.Functor.Properties
open import Categories.GradedKleisli
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Pullback using (pullback; pullback-return; pullback-ext)
import Categories.Morphism.Reasoning as MR
open import Categories.Tactic.Category

import Relation.Binary.Construct.Closure.Equivalence as EqC

module _ {o ℓ e oⱼ ℓⱼ eⱼ o′ ℓ′ e′ : Level}
  (𝒞 : Category o′ ℓ′ e′) (𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ) (ℐ : MonoidalCategory o ℓ e)
  (Φ : MonoidalFunctor 𝒥 ℐ) (ℳ : GradedKleisliTriple ℐ 𝒞)
  where
  private
    module 𝒞 = Category 𝒞
    module 𝒥 = MonoidalCategory 𝒥
    module ℐ = MonoidalCategory ℐ
    module Φ = MonoidalFunctor Φ
  open GradedKleisliTriple ℳ
  open ℐ
  open import Categories.Category.Monoidal.Utilities ℐ.monoidal
  open Shorthands
  open MR ℐ.U
  open MonR ℐ.monoidal using (_⟩⊗⟨_)

  Φ₀ = Φ.F₀
  Φ₁ = Φ.F₁
  H  = Φ.⊗-homo.η

  ℳ′ = pullback Φ ℳ

  private
    return-ext = pullback-return Φ ℳ
    ext-ext    = pullback-ext Φ ℳ
    module R  = GradedKleisliTriple ℳ′
    module MC = MR 𝒞

    -- ⊗-homo naturality whiskered by an identity on either side.
    H-commˡ : ∀ {x y z} (φ : 𝒥.U [ x , y ])
            → ℐ.U [ H (y , z) ℐ.∘ (Φ₁ φ ⊗₁ ℐ.id) ≈ Φ₁ (φ 𝒥.⊗₁ 𝒥.id) ℐ.∘ H (x , z) ]
    H-commˡ φ = let open ℐ.HomReasoning in
      (refl⟩∘⟨ (ℐ.Equiv.refl ⟩⊗⟨ ⟺ Φ.identity)) ○ Φ.⊗-homo.commute (φ , 𝒥.id)

    H-commʳ : ∀ {x y z} (φ : 𝒥.U [ x , y ])
            → ℐ.U [ H (z , y) ℐ.∘ (ℐ.id ⊗₁ Φ₁ φ) ≈ Φ₁ (𝒥.id 𝒥.⊗₁ φ) ℐ.∘ H (z , x) ]
    H-commʳ φ = let open ℐ.HomReasoning in
      (refl⟩∘⟨ (⟺ Φ.identity ⟩⊗⟨ ℐ.Equiv.refl)) ○ Φ.⊗-homo.commute (𝒥.id , φ)

  Kl𝒥 = GradedKleisli 𝒞 𝒥 ℳ′
  Klℐ = GradedKleisli 𝒞 ℐ ℳ

  private
    module Klℐ = Category Klℐ
    module Kl𝒥 = Category Kl𝒥

  Regrade₀ : Category.Obj Kl𝒥 → Category.Obj Klℐ
  Regrade₀ (κ , c) = Φ₀ κ , c

  Regrade₁ : ∀ {A B} → Kl𝒥 [ A , B ] → Klℐ [ Regrade₀ A , Regrade₀ B ]
  Regrade₁ {i , _} (κ , f , α) = Φ₀ κ , f , Φ₁ α ℐ.∘ H (i , κ)

  Regrade : Functor Kl𝒥 Klℐ
  Regrade = record
    { F₀           = Regrade₀
    ; F₁           = Regrade₁
    ; identity     = id-law
    ; homomorphism = hom-law
    ; F-resp-≈     = EqC.gmap Regrade₁ λ where
        (φ , cᶠ , cᵅ) → Φ₁ φ , cᶠ , resp-ℐ φ cᵅ
    }
    where
      resp-ℐ : ∀ {Xi Zi} {i j} {β : 𝒥.U [ Xi 𝒥.⊗₀ j , Zi ]}
                 {α : 𝒥.U [ Xi 𝒥.⊗₀ i , Zi ]}
                 (φ : 𝒥.U [ i , j ]) → 𝒥.U [ β 𝒥.∘ (𝒥.id 𝒥.⊗₁ φ) ≈ α ]
               → ℐ.U [ (Φ₁ β ℐ.∘ H (Xi , j)) ℐ.∘ (ℐ.id ⊗₁ Φ₁ φ) ≈ Φ₁ α ℐ.∘ H (Xi , i) ]
      resp-ℐ {Xi} {i = i} {j} {β} {α} φ cᵅ = begin
          (Φ₁ β ℐ.∘ H (Xi , j)) ℐ.∘ (ℐ.id ⊗₁ Φ₁ φ)   ≈⟨ pullʳ (H-commʳ φ) ⟩
          Φ₁ β ℐ.∘ Φ₁ (𝒥.id 𝒥.⊗₁ φ) ℐ.∘ H (Xi , i)   ≈⟨ pullˡ (⟺ Φ.homomorphism) ⟩
          Φ₁ (β 𝒥.∘ (𝒥.id 𝒥.⊗₁ φ)) ℐ.∘ H (Xi , i)    ≈⟨ Φ.F-resp-≈ cᵅ ⟩∘⟨refl ⟩
          Φ₁ α ℐ.∘ H (Xi , i)                        ∎
        where open ℐ.HomReasoning

      id-law : ∀ {A} → Klℐ [ Regrade₁ (Category.id Kl𝒥) ≈ Category.id Klℐ {Regrade₀ A} ]
      id-law = Klℐ.Equiv.sym (EqC.return
        ( Φ.ε
        , 𝒞.Equiv.sym return-ext
        , (let open ℐ.HomReasoning in ℐ.assoc ○ Φ.unitaryʳ) ))

      hom-law : ∀ {A B C} {f : Kl𝒥 [ A , B ]} {g : Kl𝒥 [ B , C ]}
              → Klℐ [ Regrade₁ (Kl𝒥._∘_ g f) ≈ Klℐ._∘_ (Regrade₁ g) (Regrade₁ f) ]
      hom-law {Xi , c} {Yi , d} {Zi , e} {a , f₀ , φf} {b , g₀ , φg} =
        Klℐ.Equiv.sym (EqC.return (H (a , b) , cᶜ , ℐ.Equiv.sym hom-fwd))
        where
          Hab   = H (a , b)
          H-Xa  = H (Xi , a)
          H-Yb  = H (Yi , b)
          H-XaB = H (Xi 𝒥.⊗₀ a , b)
          H-Xab = H (Xi , a 𝒥.⊗₀ b)

          cᶜ : 𝒞 [ sub Hab 𝒞.∘ (ext (Φ₀ a) g₀ 𝒞.∘ f₀) ≈ R.ext a g₀ 𝒞.∘ f₀ ]
          cᶜ = 𝒞.Equiv.sym (MC.pushˡ (ext-ext g₀))

          assoc-step : ℐ.U [ (H-XaB ℐ.∘ (H-Xa ⊗₁ ℐ.id)) ℐ.∘ α⇐
                           ≈ Φ₁ 𝒥.associator.to ℐ.∘ H-Xab ℐ.∘ (ℐ.id ⊗₁ Hab) ]
          assoc-step = let open ℐ.HomReasoning in
            switch-fromtoˡ ([ Φ.F ]-resp-≅ 𝒥.associator)
              (ℐ.sym-assoc ○ flip-iso ℐ.associator (Φ.associativity ○ ℐ.sym-assoc))

          hom-fwd : ℐ.U [ (Φ₁ φg ℐ.∘ H-Yb) ℐ.∘ ((Φ₁ φf ℐ.∘ H-Xa) ⊗₁ ℐ.id) ℐ.∘ α⇐
                        ≈ (Φ₁ (φg 𝒥.∘ (φf 𝒥.⊗₁ 𝒥.id) 𝒥.∘ 𝒥.associator.to) ℐ.∘ H-Xab) ℐ.∘ (ℐ.id ⊗₁ Hab) ]
          hom-fwd = begin
              (Φ₁ φg ℐ.∘ H-Yb) ℐ.∘ ((Φ₁ φf ℐ.∘ H-Xa) ⊗₁ ℐ.id) ℐ.∘ α⇐
                ≈⟨ refl⟩∘⟨ (Functor.homomorphism (-⊗ Φ₀ b) ⟩∘⟨refl) ⟩
              (Φ₁ φg ℐ.∘ H-Yb) ℐ.∘ ((Φ₁ φf ⊗₁ ℐ.id) ℐ.∘ (H-Xa ⊗₁ ℐ.id)) ℐ.∘ α⇐
                ≈⟨ solve ℐ.U ⟩
              Φ₁ φg ℐ.∘ (H-Yb ℐ.∘ (Φ₁ φf ⊗₁ ℐ.id)) ℐ.∘ (H-Xa ⊗₁ ℐ.id) ℐ.∘ α⇐
                ≈⟨ refl⟩∘⟨ (H-commˡ φf ⟩∘⟨refl) ⟩
              Φ₁ φg ℐ.∘ (Φ₁ (φf 𝒥.⊗₁ 𝒥.id) ℐ.∘ H-XaB) ℐ.∘ (H-Xa ⊗₁ ℐ.id) ℐ.∘ α⇐
                ≈⟨ solve ℐ.U ⟩
              Φ₁ φg ℐ.∘ Φ₁ (φf 𝒥.⊗₁ 𝒥.id) ℐ.∘ (H-XaB ℐ.∘ (H-Xa ⊗₁ ℐ.id)) ℐ.∘ α⇐
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-step ⟩
              Φ₁ φg ℐ.∘ Φ₁ (φf 𝒥.⊗₁ 𝒥.id) ℐ.∘ Φ₁ 𝒥.associator.to ℐ.∘ H-Xab ℐ.∘ (ℐ.id ⊗₁ Hab)
                ≈⟨ refl⟩∘⟨ pullˡ (⟺ Φ.homomorphism) ⟩
              Φ₁ φg ℐ.∘ Φ₁ ((φf 𝒥.⊗₁ 𝒥.id) 𝒥.∘ 𝒥.associator.to) ℐ.∘ H-Xab ℐ.∘ (ℐ.id ⊗₁ Hab)
                ≈⟨ pullˡ (⟺ Φ.homomorphism) ⟩
              Φ₁ (φg 𝒥.∘ (φf 𝒥.⊗₁ 𝒥.id) 𝒥.∘ 𝒥.associator.to) ℐ.∘ H-Xab ℐ.∘ (ℐ.id ⊗₁ Hab)
                ≈⟨ ℐ.sym-assoc ⟩
              (Φ₁ (φg 𝒥.∘ (φf 𝒥.⊗₁ 𝒥.id) 𝒥.∘ 𝒥.associator.to) ℐ.∘ H-Xab) ℐ.∘ (ℐ.id ⊗₁ Hab) ∎
            where open ℐ.HomReasoning
