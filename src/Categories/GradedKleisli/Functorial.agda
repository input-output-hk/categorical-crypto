{-# OPTIONS --safe --without-K #-}

-- `Kl` as a functor into `Cats`, for regular 1-categories.
--
-- Fix 𝒞 and grading levels o ℓ e.  The intended domain `GMon` is the lax slice
-- of monoidal-lax Cat over End(𝒞) — the category of graded monads on 𝒞:
--
--   * objects       `Obj`      : a grading ℐ together with a graded Kleisli
--                                triple M over it;
--   * morphisms     `Hom`      : (𝒥, N) → (ℐ, M) is a lax monoidal Φ : 𝒥 → ℐ
--                                with a filler ρ : N ⇒ Φ* M — an
--                                `IsGradedKleisliMorphism` at F = Id (the
--                                on-the-nose triangle relaxed to an honest
--                                2-cell);
--   * identity/∘    `idG`/`∘G` : Φ = idℐ with `idFiller`, resp. Φ∘Ψ with
--                                `composeFillerId`.
--
-- `Kl` sends (ℐ, M) to its graded Kleisli category (`Kl₀`, the F₀) and (Φ, ρ)
-- to the change-of-grading `Regrade Φ` after the change-of-monad `induced ρ`
-- (`KlMap`, the F₁) — so "`Kl` on morphisms is exactly `Regrade`", generalised
-- to an abstract source triple.  Keeping the source triple abstract makes the
-- induced functors share domain/codomain definitionally, avoiding the
-- identity-on-data bridges of the opening sections.
--
-- The file opens with `Regrade`'s own functoriality in Φ (pointwise laws and
-- the `_≡F_` bridges — the compositor cells of the pseudofunctor `Kl`); the
-- `GMon` data and the functor laws `Kl-identity`/`Kl-homomorphism` follow.
--
-- The bundled `Category GMon` and `Functor Kl (Cats …)` live in
-- `Categories.GradedKleisli.Functorial.Category`.

module Categories.GradedKleisli.Functorial where

open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Equivalence
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.GradedKleisli using (GradedKleisli; ≈-components)
open import Categories.GradedKleisli.Regrade
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Morphism
open import Categories.Monad.Graded.Pullback
import Categories.Morphism.Reasoning as MR

-- Functoriality of `Regrade` in Φ

module _ {o ℓ e o′ ℓ′ e′ : Level}
  (𝒞 : Category o′ ℓ′ e′) (ℐ : MonoidalCategory o ℓ e) (ℳ : GradedKleisliTriple ℐ 𝒞)
  where
  private
    module 𝒞 = Category 𝒞
    module ℐ = MonoidalCategory ℐ
    idℐ = idF-Monoidal ℐ
    ℳid  = pullback idℐ ℳ
    Klℳ  = Klℐ 𝒞 ℐ ℐ idℐ ℳ
    Klid = Kl𝒥 𝒞 ℐ ℐ idℐ ℳ
    module Klℳ  = Category Klℳ
    module Klid = Category Klid

  Regrade-identity : ∀ {A B} (h : A Klid.⇒ B) → Klℳ [ Regrade₁ 𝒞 ℐ ℐ idℐ ℳ h ≈ h ]
  Regrade-identity (κ , f , α) = ≈-components 𝒞 ℐ ℳ 𝒞.Equiv.refl ℐ.identityʳ

  bridge-id : Functor Klℳ Klid
  bridge-id = record
    { F₀           = λ A → A
    ; F₁           = λ h → h
    ; identity     = ≈-components 𝒞 ℐ ℳid (𝒞.Equiv.sym (pullback-id-return 𝒞 ℐ ℳ)) ℐ.Equiv.refl
    ; homomorphism = λ where
        {f = _} {g = _ , g₀ , _} → ≈-components 𝒞 ℐ ℳid
          (𝒞.∘-resp-≈ˡ (𝒞.Equiv.sym (pullback-id-ext 𝒞 ℐ ℳ g₀))) ℐ.Equiv.refl
    ; F-resp-≈     = λ p → p
    }

  -- `Regrade idℐ ℳ` and `bridge-id` are mutually inverse isomorphisms
  Regrade-identityF : Regrade 𝒞 ℐ ℐ idℐ ℳ ∘F bridge-id ≡F idF
  Regrade-identityF = record
    { eq₀ = λ _ → refl
    ; eq₁ = λ h → let open Klℳ.HomReasoning in
        Klℳ.identityˡ ○ Regrade-identity h ○ ⟺ Klℳ.identityʳ
    }

  bridge-id-inverseF : bridge-id ∘F Regrade 𝒞 ℐ ℐ idℐ ℳ ≡F idF
  bridge-id-inverseF = record
    { eq₀ = λ _ → refl
    ; eq₁ = λ h → let open Klid.HomReasoning in
        Klid.identityˡ ○ Regrade-identity h ○ ⟺ Klid.identityʳ
    }

module _ {o ℓ e oⱼ ℓⱼ eⱼ oₖ ℓₖ eₖ o′ ℓ′ e′ : Level}
  (𝒞 : Category o′ ℓ′ e′) (𝒦 : MonoidalCategory oₖ ℓₖ eₖ)
  (𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ) (ℐ : MonoidalCategory o ℓ e)
  (Ψ : MonoidalFunctor 𝒦 𝒥) (Φ : MonoidalFunctor 𝒥 ℐ) (ℳ : GradedKleisliTriple ℐ 𝒞)
  where
  private
    module 𝒞 = Category 𝒞
    module 𝒦 = MonoidalCategory 𝒦
    module ℐ = MonoidalCategory ℐ
    module Φ = MonoidalFunctor Φ
    open MR ℐ.U
    ΦΨ  = ∘-Monoidal Φ Ψ
    ℳ²  = pullback Ψ (ℳ′ 𝒞 𝒥 ℐ Φ ℳ)
    ℳ∘  = pullback ΦΨ ℳ
    Kl² = Kl𝒥 𝒞 𝒦 𝒥 Ψ (ℳ′ 𝒞 𝒥 ℐ Φ ℳ)
    Kl∘ = Kl𝒥 𝒞 𝒦 ℐ ΦΨ ℳ
    module Kl²  = Category Kl²
    module Kl∘  = Category Kl∘
    module Klℐ′ = Category (Klℐ 𝒞 𝒥 ℐ Φ ℳ)

  Regrade-homomorphism
    : ∀ {A B} (h : A Kl².⇒ B)
    → GradedKleisli 𝒞 ℐ ℳ [ Regrade₁ 𝒞 𝒥 ℐ Φ ℳ (Regrade₁ 𝒞 𝒦 𝒥 Ψ (ℳ′ 𝒞 𝒥 ℐ Φ ℳ) h)
                          ≈ Regrade₁ 𝒞 𝒦 ℐ ΦΨ ℳ h ]
  Regrade-homomorphism (κ , f , α) =
    ≈-components 𝒞 ℐ ℳ 𝒞.Equiv.refl (pushˡ Φ.homomorphism)

  -- The identity-on-data bridge and its inverse: an isomorphism of categories.
  bridge-∘ : Functor Kl² Kl∘
  bridge-∘ = record
    { F₀           = λ A → A
    ; F₁           = λ h → h
    ; identity     = ≈-components 𝒞 𝒦 ℳ∘ (pullback-∘-return 𝒞 𝒦 𝒥 ℐ Ψ Φ ℳ) 𝒦.Equiv.refl
    ; homomorphism = λ where
        {f = _} {g = _ , g₀ , _} → ≈-components 𝒞 𝒦 ℳ∘
          (𝒞.∘-resp-≈ˡ (pullback-∘-ext 𝒞 𝒦 𝒥 ℐ Ψ Φ ℳ g₀)) 𝒦.Equiv.refl
    ; F-resp-≈     = λ p → p
    }

  bridge-∘⁻¹ : Functor Kl∘ Kl²
  bridge-∘⁻¹ = record
    { F₀           = λ A → A
    ; F₁           = λ h → h
    ; identity     = ≈-components 𝒞 𝒦 ℳ² (𝒞.Equiv.sym (pullback-∘-return 𝒞 𝒦 𝒥 ℐ Ψ Φ ℳ)) 𝒦.Equiv.refl
    ; homomorphism = λ where
        {f = _} {g = _ , g₀ , _} → ≈-components 𝒞 𝒦 ℳ²
          (𝒞.∘-resp-≈ˡ (𝒞.Equiv.sym (pullback-∘-ext 𝒞 𝒦 𝒥 ℐ Ψ Φ ℳ g₀))) 𝒦.Equiv.refl
    ; F-resp-≈     = λ p → p
    }

  bridge-∘-isoˡ : bridge-∘⁻¹ ∘F bridge-∘ ≡F idF
  bridge-∘-isoˡ = record
    { eq₀ = λ _ → refl
    ; eq₁ = λ h → let open Kl².HomReasoning in Kl².identityˡ ○ ⟺ Kl².identityʳ
    }

  bridge-∘-isoʳ : bridge-∘ ∘F bridge-∘⁻¹ ≡F idF
  bridge-∘-isoʳ = record
    { eq₀ = λ _ → refl
    ; eq₁ = λ h → let open Kl∘.HomReasoning in Kl∘.identityˡ ○ ⟺ Kl∘.identityʳ
    }

  -- The functor-level homomorphism law, across the bridge.
  Regrade-homomorphismF :
    Regrade 𝒞 𝒥 ℐ Φ ℳ ∘F Regrade 𝒞 𝒦 𝒥 Ψ (ℳ′ 𝒞 𝒥 ℐ Φ ℳ) ≡F Regrade 𝒞 𝒦 ℐ ΦΨ ℳ ∘F bridge-∘
  Regrade-homomorphismF = record
    { eq₀ = λ _ → refl
    ; eq₁ = λ h → let open Klℐ′.HomReasoning in
        Klℐ′.identityˡ ○ Regrade-homomorphism h ○ ⟺ Klℐ′.identityʳ
    }

module _ {o ℓ e o′ ℓ′ e′ : Level} (𝒞 : Category o′ ℓ′ e′) where
  private module 𝒞 = Category 𝒞

  Obj : Set (suc (o ⊔ ℓ ⊔ e) ⊔ o′ ⊔ ℓ′ ⊔ e′)
  Obj = Σ[ ℐ ∈ MonoidalCategory o ℓ e ] GradedKleisliTriple ℐ 𝒞

  Hom : Obj → Obj → Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′)
  Hom (𝒥 , N) (ℐ , M) =
    Σ[ Φ ∈ MonoidalFunctor 𝒥 ℐ ]
    Σ[ κ ∈ Components N M idF Φ ] IsGradedKleisliMorphism N M idF Φ κ

  -- `idG`/`∘G`/`KlMap` are `opaque` for typechecking performance
  opaque
    idG : ∀ {A} → Hom A A
    idG {ℐ , M} = idF-Monoidal ℐ , 𝒞.id , idFiller 𝒞 ℐ M

    ∘G : ∀ {A B D} → Hom B D → Hom A B → Hom A D
    ∘G {𝒦 , P} {𝒥 , N} {ℐ , M} (Φ , κρ , ρ) (Ψ , κπ , π) =
      ∘-Monoidal Φ Ψ , κρ 𝒞.∘ κπ
      , composeFillerId {P = P} {N = N} {M = M} {Ψ = Ψ} {Φ = Φ} {κρ = κρ} {κπ = κπ} ρ π

  Kl₀ : Obj → Category (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)
  Kl₀ (ℐ , M) = GradedKleisli 𝒞 ℐ M

  opaque
    KlMap : ∀ {A B} → Hom A B → Functor (Kl₀ A) (Kl₀ B)
    KlMap {𝒥 , N} {ℐ , M} (Φ , _ , ρ) = record
      { F₀           = λ A → I.F₀ (Ind.F₀ A)
      ; F₁           = λ h → I.F₁ (Ind.F₁ h)
      ; identity     = K.Equiv.trans (I.F-resp-≈ Ind.identity) I.identity
      ; homomorphism = K.Equiv.trans (I.F-resp-≈ Ind.homomorphism) I.homomorphism
      ; F-resp-≈     = λ p → I.F-resp-≈ (Ind.F-resp-≈ p)
      }
      where
        module I   = Functor (Regrade 𝒞 𝒥 ℐ Φ M)
        module Ind = Functor (induced record { isGradedKleisliMorphism = ρ })
        module K   = Category (GradedKleisli 𝒞 ℐ M)

  opaque
    unfolding idG ∘G KlMap

    Kl-identity : ∀ {A} → _≡F_ {C = Kl₀ A} {D = Kl₀ A} (KlMap {A} {A} (idG {A})) (idF {C = Kl₀ A})
    Kl-identity {ℐ , M} = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ h → let open Category (Kl₀ (ℐ , M)); open HomReasoning in
          identityˡ
            ○ Equiv.trans (Regrade-identity 𝒞 ℐ M (Ind.F₁ h))
                          (≈-components 𝒞 ℐ M 𝒞.identityˡ ℐ.Equiv.refl)
            ○ ⟺ identityʳ
      }
      where
        module ℐ = MonoidalCategory ℐ
        module Ind = Functor (induced record { isGradedKleisliMorphism = idFiller 𝒞 ℐ M })

    Kl-homomorphism
      : ∀ {A B D} {g : Hom B D} {f : Hom A B}
      → _≡F_ {C = Kl₀ A} {D = Kl₀ D}
          (KlMap {A} {D} (∘G {A} {B} {D} g f))
          (_∘F_ {C = Kl₀ A} {D = Kl₀ B} {E = Kl₀ D} (KlMap {B} {D} g) (KlMap {A} {B} f))
    Kl-homomorphism {𝒦 , P} {𝒥 , N} {ℐ , M} {Φ , _ , ρ} {Ψ , _ , π} = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ where
          (kx , fx , αx) →
            let open Category (Kl₀ (ℐ , M)); open HomReasoning in
            identityˡ
              ○ ≈-components 𝒞 ℐ M 𝒞.assoc (ℐ.Equiv.sym (pushˡ Φ.homomorphism))
              ○ ⟺ identityʳ
      }
      where
        module ℐ = MonoidalCategory ℐ
        module Φ = MonoidalFunctor Φ
        open MR ℐ.U
