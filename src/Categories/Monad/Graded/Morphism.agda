{-# OPTIONS --safe --without-K #-}

-- Morphisms of graded Kleisli triples.
--
-- `IsGradedKleisliMorphism ℳ ℳ′ F Φ κ`: the return/ext/sub laws of a change of
-- computation model F : 𝒞 → 𝒞′ along a lax monoidal change of grading
-- Φ : ℐ → ℐ′, with component κ : F (T X A) ⇒ T′ (Φ X) (F A).
-- `GradedKleisliMorphism ℳ ℳ′` bundles (F , Φ , κ) with those laws.
-- `Categories.Monad.Graded.Uncurried` shows the three laws to be exactly a
-- 2-cell filling the uncurried square, compatibly with unit and multiplication.

module Categories.Monad.Graded.Morphism where

open import Level
open import Data.Product
open import Relation.Binary.Construct.Closure.Equivalence

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.GradedKleisli using (GradedKleisli; ≈-components)
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Pullback
import Categories.Morphism.Reasoning as MR

module _ {oᵢ ℓᵢ eᵢ oⱼ ℓⱼ eⱼ o ℓ e o′ ℓ′ e′ : Level}
  {ℐ : MonoidalCategory oᵢ ℓᵢ eᵢ} {ℐ′ : MonoidalCategory oⱼ ℓⱼ eⱼ}
  {𝒞 : Category o ℓ e} {𝒞′ : Category o′ ℓ′ e′}
  (ℳ : GradedKleisliTriple ℐ 𝒞) (ℳ′ : GradedKleisliTriple ℐ′ 𝒞′)
  where
  private
    module ℐ = MonoidalCategory ℐ
    module 𝒞′ = Category 𝒞′
    module ℳ = GradedKleisliTriple ℳ
    module ℳ′ = GradedKleisliTriple ℳ′

  module _ (F : Functor 𝒞 𝒞′) (Φ : MonoidalFunctor ℐ ℐ′) where
    private
      module F = Functor F
      module Φ = MonoidalFunctor Φ

    Components : Set (oᵢ ⊔ o ⊔ ℓ′)
    Components = ∀ {X A} → 𝒞′ [ F.₀ (ℳ.T₀ X A) , ℳ′.T₀ (Φ.₀ X) (F.₀ A) ]

    record IsGradedKleisliMorphism (κ : Components) : Set (oᵢ ⊔ ℓᵢ ⊔ o ⊔ ℓ ⊔ e′) where
      no-eta-equality
      field
        κ-return : ∀ {A} → 𝒞′ [ κ 𝒞′.∘ F.₁ (ℳ.return {A}) ≈ ℳ′.sub Φ.ε 𝒞′.∘ ℳ′.return ]
        κ-ext : ∀ {X Y A B} (f : 𝒞 [ A , ℳ.T₀ Y B ])
              → 𝒞′ [ κ 𝒞′.∘ F.₁ (ℳ.ext X f)
                   ≈ ℳ′.sub (Φ.⊗-homo.η (X , Y))
                       𝒞′.∘ ℳ′.ext (Φ.₀ X) (κ 𝒞′.∘ F.₁ f) 𝒞′.∘ κ ]
        κ-sub : ∀ {X Y A} (c : X ℐ.⇒ Y)
              → 𝒞′ [ κ {Y} {A} 𝒞′.∘ F.₁ (ℳ.sub c) ≈ ℳ′.sub (Φ.₁ c) 𝒞′.∘ κ ]

  record GradedKleisliMorphism
    : Set (oᵢ ⊔ ℓᵢ ⊔ eᵢ ⊔ oⱼ ⊔ ℓⱼ ⊔ eⱼ ⊔ o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    no-eta-equality
    field F : Functor 𝒞 𝒞′
          Φ : MonoidalFunctor ℐ ℐ′
          κ : Components F Φ
          isGradedKleisliMorphism : IsGradedKleisliMorphism F Φ κ

    module F = Functor F
    module Φ = MonoidalFunctor Φ

    open IsGradedKleisliMorphism isGradedKleisliMorphism public

module _ {oᵢ ℓᵢ eᵢ oⱼ ℓⱼ eⱼ o ℓ e o′ ℓ′ e′ : Level}
  {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ} {ℐ : MonoidalCategory oᵢ ℓᵢ eᵢ}
  {𝒞 : Category o ℓ e} {𝒞′ : Category o′ ℓ′ e′}
  {ℳ : GradedKleisliTriple 𝒥 𝒞} {ℳ′ : GradedKleisliTriple ℐ 𝒞′}
  (ρ : GradedKleisliMorphism ℳ ℳ′)
  where
  private
    open GradedKleisliMorphism ρ
    module 𝒥 = MonoidalCategory 𝒥
    module 𝒞′ = Category 𝒞′
    module ℳ = GradedKleisliTriple ℳ
    R = pullback Φ ℳ′
    module R = GradedKleisliTriple R
    open 𝒞′.HomReasoning

  κ-ext-pullback : ∀ {u v A B} (f : 𝒞 [ A , ℳ.T₀ v B ])
                 → 𝒞′ [ κ 𝒞′.∘ F.₁ (ℳ.ext u f) ≈ R.ext u (κ 𝒞′.∘ F.₁ f) 𝒞′.∘ κ ]
  κ-ext-pullback f =
    κ-ext f ○ 𝒞′.sym-assoc ○ (⟺ (pullback-ext Φ ℳ′ (κ 𝒞′.∘ F.₁ f)) ⟩∘⟨refl)

  induced : Functor (GradedKleisli 𝒞 𝒥 ℳ) (GradedKleisli 𝒞′ 𝒥 R)
  induced = record
    { F₀           = λ where (u , A) → u , F.₀ A
    ; F₁           = λ where (u , f , α) → u , κ 𝒞′.∘ F.₁ f , α
    ; identity     = ≈-components 𝒞′ 𝒥 R κ-return 𝒥.Equiv.refl
    ; homomorphism = λ where
        {f = _ , f₀ , _} {g = _ , g₀ , _} → ≈-components 𝒞′ 𝒥 R
          ((refl⟩∘⟨ F.homomorphism) ○ 𝒞′.sym-assoc
            ○ (κ-ext-pullback g₀ ⟩∘⟨refl) ○ 𝒞′.assoc) 𝒥.Equiv.refl
    ; F-resp-≈     = gmap (λ where (u , f , α) → u , κ 𝒞′.∘ F.₁ f , α) λ where
        (φ , cf , cα) → φ
          , (𝒞′.sym-assoc ○ (⟺ (κ-sub φ) ⟩∘⟨refl) ○ 𝒞′.assoc
              ○ (refl⟩∘⟨ (⟺ F.homomorphism ○ F.F-resp-≈ cf))) , cα
    }

module _ {o ℓ e o′ ℓ′ e′ : Level}
  (𝒞 : Category o′ ℓ′ e′) (ℐ : MonoidalCategory o ℓ e) (ℳ : GradedKleisliTriple ℐ 𝒞)
  where
  private
    module 𝒞 = Category 𝒞
    module ℳ = GradedKleisliTriple ℳ
    open 𝒞.HomReasoning
    open MR 𝒞

  idFiller : IsGradedKleisliMorphism ℳ ℳ idF (idF-Monoidal ℐ) 𝒞.id
  idFiller = record
    { κ-return = 𝒞.identityˡ ○ ⟺ (elimˡ ℳ.sub-identity)
    ; κ-ext    = λ f → 𝒞.identityˡ
                     ○ ⟺ (elimˡ ℳ.sub-identity ○ 𝒞.identityʳ ○ ℳ.ext-resp-≈ 𝒞.identityˡ)
    ; κ-sub    = λ _ → 𝒞.identityˡ ○ ⟺ 𝒞.identityʳ
    }

  idMorphism : GradedKleisliMorphism ℳ ℳ
  idMorphism = record
    { F = idF ; Φ = idF-Monoidal ℐ ; κ = 𝒞.id ; isGradedKleisliMorphism = idFiller }

module _ {oᵢ ℓᵢ eᵢ oⱼ ℓⱼ eⱼ oₖ ℓₖ eₖ o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level}
  {𝒦 : MonoidalCategory oₖ ℓₖ eₖ} {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ}
  {ℐ : MonoidalCategory oᵢ ℓᵢ eᵢ}
  {𝒞 : Category o ℓ e} {𝒞′ : Category o′ ℓ′ e′} {𝒞″ : Category o″ ℓ″ e″}
  {P : GradedKleisliTriple 𝒦 𝒞} {N : GradedKleisliTriple 𝒥 𝒞′}
  {M : GradedKleisliTriple ℐ 𝒞″}
  {G : Functor 𝒞 𝒞′} {F : Functor 𝒞′ 𝒞″}
  {Ψ : MonoidalFunctor 𝒦 𝒥} {Φ : MonoidalFunctor 𝒥 ℐ}
  {κρ : Components N M F Φ} {κπ : Components P N G Ψ}
  where
  private
    module 𝒞′ = Category 𝒞′
    module 𝒞″ = Category 𝒞″
    module ℐ = MonoidalCategory ℐ
    module Ψ = MonoidalFunctor Ψ
    module Φ = MonoidalFunctor Φ
    module F = Functor F
    module G = Functor G
    module P = GradedKleisliTriple P
    module N = GradedKleisliTriple N
    module M = GradedKleisliTriple M
    open 𝒞″.HomReasoning

  composeFiller : IsGradedKleisliMorphism N M F Φ κρ
                → IsGradedKleisliMorphism P N G Ψ κπ
                → IsGradedKleisliMorphism P M (F ∘F G) (∘-Monoidal Φ Ψ) (κρ 𝒞″.∘ F.₁ κπ)
  composeFiller ρ π = record
    { κ-return = begin
        (κρ 𝒞″.∘ F.₁ κπ) 𝒞″.∘ F.₁ (G.₁ P.return)          ≈⟨ 𝒞″.assoc ⟩
        κρ 𝒞″.∘ (F.₁ κπ 𝒞″.∘ F.₁ (G.₁ P.return))          ≈⟨ refl⟩∘⟨ Fπ π.κ-return ⟩
        κρ 𝒞″.∘ (F.₁ (N.sub Ψ.ε) 𝒞″.∘ F.₁ N.return)       ≈⟨ 𝒞″.sym-assoc ⟩
        (κρ 𝒞″.∘ F.₁ (N.sub Ψ.ε)) 𝒞″.∘ F.₁ N.return       ≈⟨ ρ.κ-sub Ψ.ε ⟩∘⟨refl ⟩
        (M.sub (Φ.₁ Ψ.ε) 𝒞″.∘ κρ) 𝒞″.∘ F.₁ N.return       ≈⟨ 𝒞″.assoc ⟩
        M.sub (Φ.₁ Ψ.ε) 𝒞″.∘ (κρ 𝒞″.∘ F.₁ N.return)       ≈⟨ refl⟩∘⟨ ρ.κ-return ⟩
        M.sub (Φ.₁ Ψ.ε) 𝒞″.∘ (M.sub Φ.ε 𝒞″.∘ M.return)    ≈⟨ 𝒞″.sym-assoc ⟩
        (M.sub (Φ.₁ Ψ.ε) 𝒞″.∘ M.sub Φ.ε) 𝒞″.∘ M.return    ≈⟨ ⟺ M.sub-homomorphism ⟩∘⟨refl ⟩
        M.sub (Φ.₁ Ψ.ε ℐ.∘ Φ.ε) 𝒞″.∘ M.return             ∎
    ; κ-ext    = λ {u} {v} f →
        let HΨ = Ψ.⊗-homo.η (u , v)
            HΦ = Φ.⊗-homo.η (Ψ.₀ u , Ψ.₀ v)
            πf = κπ 𝒞′.∘ G.₁ f
            h  = κρ 𝒞″.∘ F.₁ πf
        in begin
        (κρ 𝒞″.∘ F.₁ κπ) 𝒞″.∘ F.₁ (G.₁ (P.ext u f))
          ≈⟨ 𝒞″.assoc ⟩
        κρ 𝒞″.∘ (F.₁ κπ 𝒞″.∘ F.₁ (G.₁ (P.ext u f)))
          ≈⟨ refl⟩∘⟨ (Fπ (π.κ-ext f) ○ (refl⟩∘⟨ F.homomorphism)) ⟩
        κρ 𝒞″.∘ (F.₁ (N.sub HΨ) 𝒞″.∘ (F.₁ (N.ext (Ψ.₀ u) πf) 𝒞″.∘ F.₁ κπ))
          ≈⟨ 𝒞″.sym-assoc ⟩
        (κρ 𝒞″.∘ F.₁ (N.sub HΨ)) 𝒞″.∘ (F.₁ (N.ext (Ψ.₀ u) πf) 𝒞″.∘ F.₁ κπ)
          ≈⟨ ρ.κ-sub HΨ ⟩∘⟨refl ⟩
        (M.sub (Φ.₁ HΨ) 𝒞″.∘ κρ) 𝒞″.∘ (F.₁ (N.ext (Ψ.₀ u) πf) 𝒞″.∘ F.₁ κπ)
          ≈⟨ 𝒞″.assoc ○ (refl⟩∘⟨ 𝒞″.sym-assoc) ⟩
        M.sub (Φ.₁ HΨ) 𝒞″.∘ ((κρ 𝒞″.∘ F.₁ (N.ext (Ψ.₀ u) πf)) 𝒞″.∘ F.₁ κπ)
          ≈⟨ refl⟩∘⟨ (ρ.κ-ext πf ⟩∘⟨refl) ⟩
        M.sub (Φ.₁ HΨ) 𝒞″.∘ ((M.sub HΦ 𝒞″.∘ (M.ext (Φ.₀ (Ψ.₀ u)) h 𝒞″.∘ κρ)) 𝒞″.∘ F.₁ κπ)
          ≈⟨ (refl⟩∘⟨ 𝒞″.assoc) ○ 𝒞″.sym-assoc ⟩
        (M.sub (Φ.₁ HΨ) 𝒞″.∘ M.sub HΦ)
          𝒞″.∘ ((M.ext (Φ.₀ (Ψ.₀ u)) h 𝒞″.∘ κρ) 𝒞″.∘ F.₁ κπ)
          ≈⟨ ⟺ M.sub-homomorphism ⟩∘⟨ 𝒞″.assoc ⟩
        M.sub (Φ.₁ HΨ ℐ.∘ HΦ) 𝒞″.∘ (M.ext (Φ.₀ (Ψ.₀ u)) h 𝒞″.∘ (κρ 𝒞″.∘ F.₁ κπ))
          ≈⟨ refl⟩∘⟨ (M.ext-resp-≈ ((refl⟩∘⟨ F.homomorphism) ○ 𝒞″.sym-assoc) ⟩∘⟨refl) ⟩
        M.sub (Φ.₁ HΨ ℐ.∘ HΦ)
          𝒞″.∘ (M.ext (Φ.₀ (Ψ.₀ u)) ((κρ 𝒞″.∘ F.₁ κπ) 𝒞″.∘ F.₁ (G.₁ f))
                 𝒞″.∘ (κρ 𝒞″.∘ F.₁ κπ))
          ∎
    ; κ-sub    = λ φ →
        𝒞″.assoc ○ (refl⟩∘⟨ Fπ (π.κ-sub φ)) ○ 𝒞″.sym-assoc
        ○ (ρ.κ-sub (Ψ.₁ φ) ⟩∘⟨refl) ○ 𝒞″.assoc
    }
    where
      module ρ = IsGradedKleisliMorphism ρ
      module π = IsGradedKleisliMorphism π

      Fπ : ∀ {X A B C} {f : 𝒞 [ A , P.T₀ X B ]}
             {g₁ : 𝒞′ [ C , N.T₀ (Ψ.₀ X) (G.₀ B) ]} {g₂ : 𝒞′ [ G.₀ A , C ]}
         → 𝒞′ [ κπ 𝒞′.∘ G.₁ f ≈ g₁ 𝒞′.∘ g₂ ]
         → 𝒞″ [ F.₁ κπ 𝒞″.∘ F.₁ (G.₁ f) ≈ F.₁ g₁ 𝒞″.∘ F.₁ g₂ ]
      Fπ p = ⟺ F.homomorphism ○ F.F-resp-≈ p ○ F.homomorphism

module _ {oᵢ ℓᵢ eᵢ oⱼ ℓⱼ eⱼ oₖ ℓₖ eₖ o′ ℓ′ e′ : Level}
  {𝒦 : MonoidalCategory oₖ ℓₖ eₖ} {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ}
  {ℐ : MonoidalCategory oᵢ ℓᵢ eᵢ} {𝒞 : Category o′ ℓ′ e′}
  {P : GradedKleisliTriple 𝒦 𝒞} {N : GradedKleisliTriple 𝒥 𝒞}
  {M : GradedKleisliTriple ℐ 𝒞}
  {Ψ : MonoidalFunctor 𝒦 𝒥} {Φ : MonoidalFunctor 𝒥 ℐ}
  {κρ : Components N M idF Φ} {κπ : Components P N idF Ψ}
  where
  private
    module 𝒞 = Category 𝒞

  -- The F = Id case, which `composeFiller` does NOT give: `idF ∘F idF` is not
  -- convertible to `idF` (its `identity` field is a `trans` of reflexivities).
  -- Repacking field by field does work, since the laws mention F only through
  -- F₀/F₁, which do agree.
  composeFillerId : IsGradedKleisliMorphism N M idF Φ κρ
                  → IsGradedKleisliMorphism P N idF Ψ κπ
                  → IsGradedKleisliMorphism P M idF (∘-Monoidal Φ Ψ) (κρ 𝒞.∘ κπ)
  composeFillerId ρ π = record { κ-return = κ-return ; κ-ext = κ-ext ; κ-sub = κ-sub }
    where open IsGradedKleisliMorphism (composeFiller ρ π)

module _ {oᵢ ℓᵢ eᵢ oⱼ ℓⱼ eⱼ oₖ ℓₖ eₖ o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level}
  {𝒦 : MonoidalCategory oₖ ℓₖ eₖ} {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ}
  {ℐ : MonoidalCategory oᵢ ℓᵢ eᵢ}
  {𝒞 : Category o ℓ e} {𝒞′ : Category o′ ℓ′ e′} {𝒞″ : Category o″ ℓ″ e″}
  {P : GradedKleisliTriple 𝒦 𝒞} {N : GradedKleisliTriple 𝒥 𝒞′}
  {M : GradedKleisliTriple ℐ 𝒞″}
  where

  composeMorphism : GradedKleisliMorphism N M → GradedKleisliMorphism P N
                  → GradedKleisliMorphism P M
  composeMorphism ρ π = record
    { F = ρ.F ∘F π.F
    ; Φ = ∘-Monoidal ρ.Φ π.Φ
    ; κ = ρ.κ 𝒞″.∘ ρ.F.₁ π.κ
    ; isGradedKleisliMorphism =
        composeFiller {G = π.F} {F = ρ.F} {Ψ = π.Φ} {Φ = ρ.Φ} {κρ = ρ.κ} {κπ = π.κ}
          ρ.isGradedKleisliMorphism π.isGradedKleisliMorphism
    }
    where
      module 𝒞″ = Category 𝒞″
      module ρ = GradedKleisliMorphism ρ
      module π = GradedKleisliMorphism π
