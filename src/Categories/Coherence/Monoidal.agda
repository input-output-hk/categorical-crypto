{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal where

open import Level renaming (zero to ℓ0)

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Properties
open import Categories.Category.Product
open import Categories.Functor as F hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Morphism
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

open import Categories.Discrete
open import Categories.FreeMonoidal
open import Categories.NaturalTransformationHelper
open import Categories.Properties

open import Data.Empty
open import Data.Fin using (Fin)
import Data.Fin.Properties as FinP
open import Data.List hiding ([_] ; lookup)
open import Data.List.Properties using (≡-dec)
open import Data.Product
open import Data.Vec using (Vec ; lookup)

open import Relation.Binary.Definitions using (DecidableEquality; Irrelevant)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

module CoherenceThm (X : Set) (_≟X_ : DecidableEquality X) where
  open FreeMonoidal (record { v = Mon ; X = X ; mor = λ _ _ → ⊥ })

  open Commutation FreeMonoidal
  open Discrete (List X)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)

  -- UIP for the discrete-category objects `List X`, derived from decidable
  -- equality of `X` (Hedberg).
  uipL : Irrelevant {A = List X} _≡_
  uipL = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)
  open import Categories.NaturalTransformation.NaturalIsomorphism as NI hiding (refl; trans; unitorˡ; unitorʳ; associator)

  module FM where
    open Category FreeMonoidal public
    open Monoidal Monoidal-FreeMonoidal public
    open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal public
    open Shorthands public
    open Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal public

  module FMReasoning where
    open import Categories.Category.Monoidal.Reasoning Monoidal-FreeMonoidal public

  import Relation.Binary.Reasoning.Setoid as SetoidR

  ⟦_⟧ : ObjTerm → List X → List X
  ⟦ unit ⟧ n = n
  ⟦ t ⊗₀ t₁ ⟧ n = ⟦ t ⟧ (⟦ t₁ ⟧ n)
  ⟦ Var x ⟧ n = x ∷ n

  hom⇒≡⟦⟧' : ∀ {A B x y} → HomTerm A B → x ≡ y → ⟦ A ⟧ x ≡ ⟦ B ⟧ y
  hom⇒≡⟦⟧' id refl = refl
  hom⇒≡⟦⟧' {x} {y} (h ∘ h') eq = trans (hom⇒≡⟦⟧' h' eq) (hom⇒≡⟦⟧' h refl)
  hom⇒≡⟦⟧' {A ⊗₀ B} {C ⊗₀ D} {x} {y} (h ⊗₁ h') eq = hom⇒≡⟦⟧' h (hom⇒≡⟦⟧' h' eq)
  hom⇒≡⟦⟧' λ⇒ refl = refl
  hom⇒≡⟦⟧' λ⇐ refl = refl
  hom⇒≡⟦⟧' ρ⇒ refl = refl
  hom⇒≡⟦⟧' ρ⇐ refl = refl
  hom⇒≡⟦⟧' α⇒ refl = refl
  hom⇒≡⟦⟧' α⇐ refl = refl

  ⟦_⟧₀ = uncurry ⟦_⟧
  ⟦_⟧₁ : ∀ {A B x y} → HomTerm A B × x ≡ y → ⟦ A ⟧ x ≡ ⟦ B ⟧ y
  ⟦_⟧₁ = uncurry hom⇒≡⟦⟧'

  ι₀ : Discrete .Category.Obj → FreeMonoidal .Category.Obj
  ι₀ [] = unit
  ι₀ (x ∷ []) = Var x
  ι₀ (x ∷ x₁ ∷ x₂) = Var x ⊗₀ ι₀ (x₁ ∷ x₂)

  ι₁ : ∀ {A B} → Discrete [ A , B ] → FreeMonoidal [ ι₀ A , ι₀ B ]
  ι₁ refl = id

  opaque
    ⟦_⟧F : Bifunctor FreeMonoidal Discrete Discrete
    ⟦_⟧F = record
      { F₀ = ⟦_⟧₀
      ; F₁ = ⟦_⟧₁
      ; identity = _
      ; homomorphism = _
      ; F-resp-≈ = λ _ → _
      }

    ι : Functor Discrete FreeMonoidal
    ι = record
      { F₀ = ι₀
      ; F₁ = ι₁
      ; identity = FM.Equiv.refl
      ; homomorphism = λ where {_} {_} {_} {refl} {refl} → FM.HomReasoning.⟺ FM.identityˡ
      ; F-resp-≈ = λ {_} {_} {f} {g} _ →
          subst (λ h → FM._≈_ (ι₁ f) (ι₁ h)) (uipL f g) FM.Equiv.refl
      }

  Nf : Functor FreeMonoidal Discrete
  Nf = appʳ ⟦_⟧F []

  module C where
    open import Categories.Category.Construction.Core FreeMonoidal public
    open Category Core public

  P = Product FreeMonoidal Discrete

  -- F1/F2 are defined first-order rather than as the functor compositions
  -- `FM.⊗ ∘F (F.id ⁂ ι)` / `ι ∘F ⟦_⟧F`: conversion against the composition
  -- towers re-normalizes their record stacks at every chain step, which is
  -- what made this module expensive to serialize (15× on natural-α⇒ alone).
  -- The towers are recovered up to NaturalIsomorphism below (F1≅tower /
  -- F2≅tower) for the functor-level reasoning in Nf≅id.
  F1₀ F2₀ : ObjTerm × List X → ObjTerm
  F1₀ (x , d) = x ⊗₀ ι₀ d
  F2₀ (x , d) = ι₀ (⟦ x ⟧ d)

  F1₁ : ∀ {V W} → P [ V , W ] → FreeMonoidal [ F1₀ V , F1₀ W ]
  F1₁ (f , g) = f ⊗₁ ι₁ g

  F2₁ : ∀ {V W} → P [ V , W ] → FreeMonoidal [ F2₀ V , F2₀ W ]
  F2₁ (f , g) = ι₁ (⟦ f , g ⟧₁)

  module _ where
    open FMReasoning

    private
      ι₁-irr : ∀ {a b} {φ γ : a ≡ b} → ι₁ φ FM.≈ ι₁ γ
      ι₁-irr {φ = φ} {γ} = subst (λ h → ι₁ φ FM.≈ ι₁ h) (uipL φ γ) FM.Equiv.refl

      ι₁-glue : ∀ {a b c} (φ : a ≡ b) (γ : b ≡ c) (δ : a ≡ c)
              → ι₁ δ FM.≈ ι₁ γ ∘ ι₁ φ
      ι₁-glue refl refl δ rewrite uipL δ refl = ⟺ FM.identityˡ

      F1-hom : ∀ {U V W} (fp : P [ U , V ]) (gp : P [ V , W ])
             → F1₁ (P [ gp ∘ fp ]) FM.≈ F1₁ gp ∘ F1₁ fp
      F1-hom (f , φ) (g , γ) = begin
        (g ∘ f) ⊗₁ ι₁ (trans φ γ)  ≈⟨ refl⟩⊗⟨ ι₁-glue φ γ (trans φ γ) ⟩
        (g ∘ f) ⊗₁ (ι₁ γ ∘ ι₁ φ)   ≈⟨ FM.⊗.homomorphism ⟩
        (g ⊗₁ ι₁ γ) ∘ (f ⊗₁ ι₁ φ) ∎

      F2-hom : ∀ {U V W} (fp : P [ U , V ]) (gp : P [ V , W ])
             → F2₁ (P [ gp ∘ fp ]) FM.≈ F2₁ gp ∘ F2₁ fp
      F2-hom (f , φ) (g , γ) =
        ι₁-glue ⟦ f , φ ⟧₁ ⟦ g , γ ⟧₁ ⟦ g ∘ f , trans φ γ ⟧₁

      F1-resp : ∀ {V W} (fp gp : P [ V , W ]) → P [ fp ≈ gp ]
              → F1₁ fp FM.≈ F1₁ gp
      F1-resp (f , φ) (g , γ) (e , _) = e ⟩⊗⟨ ι₁-irr

      F2-resp : ∀ {V W} (fp gp : P [ V , W ]) → P [ fp ≈ gp ]
              → F2₁ fp FM.≈ F2₁ gp
      F2-resp (f , φ) (g , γ) _ = ι₁-irr

    F1 F2 : Bifunctor FreeMonoidal Discrete FreeMonoidal
    F1 = record
      { F₀ = F1₀ ; F₁ = F1₁
      ; identity = FM.⊗.identity
      ; homomorphism = λ {_} {_} {_} {fp} {gp} → F1-hom fp gp
      ; F-resp-≈ = F1-resp _ _
      }
    F2 = record
      { F₀ = F2₀ ; F₁ = F2₁
      ; identity = FM.Equiv.refl
      ; homomorphism = λ {_} {_} {_} {fp} {gp} → F2-hom fp gp
      ; F-resp-≈ = F2-resp _ _
      }

  opaque
    unfolding ⟦_⟧F
    -- making the termination checker happy
    iso' : (x : ObjTerm) → (y : List X) → C.Core [ Functor.₀ F1 (x , y) , Functor.₀ F2 (x , y) ]
    iso' unit n = FM.unitorˡ
    iso' (a ⊗₀ b) n = iso' a (⟦ b ⟧ n) C.∘ (≅.refl _ FM.⊗ᵢ iso' b n) C.∘ FM.associator
    iso' (Var x) [] = FM.unitorʳ
    iso' (Var x) (x₁ ∷ n) = ≅.refl _

    iso : (X : ObjTerm × List X) → C.Core [ Functor.₀ F1 X , Functor.₀ F2 X ]
    iso = uncurry iso'

    iso₁ : (X : ObjTerm × List X) → FreeMonoidal [ Functor.₀ F1 X , Functor.₀ F2 X ]
    iso₁ X = _≅_.from (iso X)

    iso₁-assoc-ty : Set
    iso₁-assoc-ty = ∀ {A B d} → iso₁ (A ⊗₀ B , d) ≈Term iso₁ (A , ⟦ B ⟧ d) ∘ (id ⊗₁ iso₁ (B , d)) ∘ FM.α⇒

    -- It's necessary to hide this type behind a definition, otherwise it won't type check in an opaque block
    iso₁-assoc : iso₁-assoc-ty
    iso₁-assoc = ≈-Term-refl

  module _ where opaque
    unfolding ⟦_⟧F ι iso iso₁-assoc iso₁-assoc-ty
    open FMReasoning
    open import Categories.Morphism.Reasoning FreeMonoidal

    iso-comm-ty : Set
    iso-comm-ty = ∀ {A} {d₁} {d₂} {g : d₁ ≡ d₂}
           → iso₁ (A , d₂) ∘ id ⊗₁ ι₁ g
        FM.≈ ι₁ (hom⇒≡⟦⟧' (id {A}) g) ∘ iso₁ (A , d₁)

    iso-comm : iso-comm-ty
    iso-comm {A} {d} {_} {refl} = begin
      iso₁ (A , d) ∘ id ⊗₁ id
        ≈⟨ refl⟩∘⟨ FM.⊗.identity ○ id-comm ⟩
      id ∘ iso₁ (A , d) ∎

    ι-∘ : ∀ {A B C D} d (f : HomTerm A B) (g : HomTerm C D)
        → ι₁ ⟦ f , ⟦ g , refl {x = d} ⟧₁ ⟧₁
          FM.≈ ι₁ ⟦ id {A = B} , ⟦ g , refl {x = d} ⟧₁ ⟧₁ ∘ ι₁ ⟦ f , refl {x = ⟦ C ⟧ d} ⟧₁
    ι-∘ d f g = begin
      ι₁ ⟦ f , ⟦ g , refl ⟧₁ ⟧₁
        ≈⟨ ι.F-resp-≈ _ ⟩
      ι₁ (⟦ id , ⟦ g , refl ⟧₁ ⟧₁ D.∘ ⟦ f , refl ⟧₁)
        ≈⟨ ι.homomorphism ⟩
      ι₁ ⟦ id , ⟦ g , refl ⟧₁ ⟧₁ ∘ ι₁ ⟦ f , refl ⟧₁ ∎
      where module ι = Functor ι
            module D = Category Discrete

    natural-id : ∀ {X} → iso₁ X ∘ id ⊗₁ id FM.≈ id ∘ iso₁ X
    natural-id {X} = begin
      iso₁ X ∘ id ⊗₁ id
        ≈⟨ refl⟩∘⟨ FM.⊗.identity ○ ⟺ id-comm-sym ⟩
      id ∘ iso₁ X ∎

    natural-∘ : ∀ {A B C} d (g : HomTerm B C) (f : HomTerm A B)
      → iso₁ (C , d) ∘ g ⊗₁ id FM.≈ ι₁ ⟦ (g , refl) ⟧₁ ∘ iso₁ (B , d)
      → iso₁ (B , d) ∘ f ⊗₁ id FM.≈ ι₁ ⟦ (f , refl) ⟧₁ ∘ iso₁ (A , d)
      → iso₁ (C , d) ∘ (g ∘ f) ⊗₁ id FM.≈ ι₁ ⟦ (g ∘ f , refl) ⟧₁ ∘ iso₁ (A , d)
    natural-∘ {A} {B} {C} d g f Hg Hf = begin
      iso₁ (C , d) ∘ (g ∘ f) ⊗₁ id
        ≈⟨ refl⟩∘⟨ Functor.homomorphism F1 {f = f , refl} {g , refl} ⟩
      iso₁ (C , d) ∘ g ⊗₁ id ∘ f ⊗₁ id
        ≈⟨ FM.assoc ⟨
      (iso₁ (C , d) ∘ g ⊗₁ id) ∘ f ⊗₁ id
        ≈⟨ Hg ⟩∘⟨refl ⟩
      (ι₁ ⟦ (g , refl) ⟧₁ ∘ iso₁ (B , d)) ∘ f ⊗₁ id
        ≈⟨ FM.assoc ⟩
      ι₁ ⟦ (g , refl) ⟧₁ ∘ iso₁ (B , d) ∘ f ⊗₁ id
        ≈⟨ refl⟩∘⟨ Hf ⟩
      ι₁ ⟦ (g , refl) ⟧₁ ∘ ι₁ ⟦ (f , refl) ⟧₁ ∘ iso₁ (A , d)
        ≈⟨ FM.assoc ⟨
      (ι₁ ⟦ (g , refl) ⟧₁ ∘ ι₁ ⟦ (f , refl) ⟧₁) ∘ iso₁ (A , d)
        ≈⟨ Functor.homomorphism F2 {f = f , refl} {g = g , refl} ⟩∘⟨refl ⟨
      ι₁ ⟦ (g ∘ f , refl) ⟧₁ ∘ iso₁ (A , d) ∎

    natural-⊗ : ∀ {A B C D} d (f : HomTerm A B) (g : HomTerm C D)
      → iso₁ (B , ⟦ C ⟧ d) ∘ f ⊗₁ id FM.≈ ι₁ ⟦ (f , refl) ⟧₁ ∘ iso₁ (A , ⟦ C ⟧ d)
      → iso₁ (D , d) ∘ g ⊗₁ id FM.≈ ι₁ ⟦ (g , refl) ⟧₁ ∘ iso₁ (C , d)
      → iso₁ (B ⊗₀ D , d) ∘ (f ⊗₁ g) ⊗₁ id FM.≈ ι₁ ⟦ (f ⊗₁ g , refl) ⟧₁ ∘ iso₁ (A ⊗₀ C , d)
    natural-⊗ {A} {B} {C} {D} d f g Hf Hg = begin
      (iso₁ (B , ⟦ D ⟧ d) ∘ id ⊗₁ iso₁ (D , d) ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ id
        ≈⟨ assoc²βε ○ refl⟩∘⟨ refl⟩∘⟨ FM.assoc-commute-from ○ refl⟩∘⟨ ⟺ assoc ⟩
      iso₁ (B , ⟦ D ⟧ d) ∘ (id ⊗₁ iso₁ (D , d) ∘ f ⊗₁ g ⊗₁ id) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ FM.⊗.homomorphism ⟩∘⟨refl ⟩
      iso₁ (B , ⟦ D ⟧ d) ∘ (id ∘ f) ⊗₁ (iso₁ (D , d) ∘ g ⊗₁ id) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ Hg ⟩∘⟨refl ⟩
      iso₁ (B , ⟦ D ⟧ d) ∘ (id ∘ f) ⊗₁ (ι₁ ⟦ (g , refl) ⟧₁ ∘ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ FM.⊗.homomorphism ⟩∘⟨refl ⟩
      iso₁ (B , ⟦ D ⟧ d) ∘ (id ⊗₁ ι₁ ⟦ (g , refl) ⟧₁ ∘ f ⊗₁ iso₁ (C , d)) ∘ α⇒
        ≈⟨ assoc²δγ ⟩
      (iso₁ (B , ⟦ D ⟧ d) ∘ id ⊗₁ ι₁ ⟦ (g , refl) ⟧₁) ∘ f ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ iso-comm ⟩∘⟨refl ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ iso₁ (B , ⟦ C ⟧ d)) ∘ f ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ idʳ ⟩⊗⟨ ⟺ idˡ ⟩∘⟨refl ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ iso₁ (B , ⟦ C ⟧ d)) ∘ (f ∘ id) ⊗₁ (id ∘ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ FM.⊗.homomorphism ⟩∘⟨refl ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ iso₁ (B , ⟦ C ⟧ d)) ∘ (f ⊗₁ id ∘ id ⊗₁ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ iso₁ (B , ⟦ C ⟧ d)) ∘ f ⊗₁ id ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ assoc ○ refl⟩∘⟨ ⟺ assoc ⟩
      ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ (iso₁ (B , ⟦ C ⟧ d) ∘ f ⊗₁ id) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ refl⟩∘⟨ Hf ⟩∘⟨refl ⟩
      ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ (ι₁ ⟦ (f , refl) ⟧₁ ∘ iso₁ (A , ⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ assoc²δγ ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ ι₁ ⟦ (f , refl) ⟧₁) ∘ iso₁ (A , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ ⟺ (ι-∘ d f g) ⟩∘⟨refl ⟩
      ι₁ ⟦ (f ⊗₁ g , refl) ⟧₁ ∘ iso₁ (A , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒ ∎

    natural-λ⇒ : ∀ {A d}
               → iso₁ (A , d) ∘ λ⇒ ⊗₁ id
            FM.≈ id ∘ iso₁ (unit ⊗₀ A , d)
    natural-λ⇒ {A} {d} = begin
      iso₁ (A , d) ∘ λ⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ ⟺ FM.coherence₁ ⟩
      iso₁ (A , d) ∘ λ⇒ ∘ α⇒
        ≈⟨ ⟺ assoc ⟩
      (iso₁ (A , d) ∘ λ⇒) ∘ α⇒
        ≈⟨ ⟺ FM.unitorˡ-commute-from ⟩∘⟨refl ⟩
      (λ⇒ ∘ id ⊗₁ iso₁ (A , d)) ∘ α⇒
        ≈⟨ assoc ○ (⟺ idˡ) ⟩
      id ∘ λ⇒ ∘ id ⊗₁ iso₁ (A , d) ∘ α⇒ ∎

    natural-ρ⇒ : ∀ {A d}
               → iso₁ (A , d) ∘ ρ⇒ ⊗₁ id
            FM.≈ id ∘ iso₁ (A ⊗₀ unit , d)
    natural-ρ⇒ {A} {d} = begin
      iso₁ (A , d) ∘ ρ⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ ⟺ FM.triangle ⟩
      iso₁ (A , d) ∘ id ⊗₁ λ⇒ ∘ α⇒
        ≈⟨ ⟺ idˡ ⟩
      id ∘ iso₁ (A , d) ∘ id ⊗₁ λ⇒ ∘ α⇒ ∎

    natural-α⇒ : ∀ {A B C d}
               → iso₁ (A ⊗₀ B ⊗₀ C , d) ∘ α⇒ ⊗₁ id
            FM.≈ id ∘ iso₁ ((A ⊗₀ B) ⊗₀ C , d)
    natural-α⇒ {A} {B} {C} {d} = begin
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒) ∘ α⇒ ⊗₁ id
        ≈⟨ assoc²βε ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒ ∘ α⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ Functor.homomorphism (A FM.⊗-) ⟩∘⟨refl ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ (id ⊗₁ iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ (id ⊗₁ iso₁ (C , d) ∘ α⇒)) ∘ α⇒ ∘ α⇒ ⊗₁ id
        ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Functor.homomorphism (A FM.⊗-)) ⟩∘⟨refl) ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ (id ⊗₁ iso₁ (B , ⟦ C ⟧ d) ∘ (id ⊗₁ id ⊗₁ iso₁ (C , d) ∘ id ⊗₁ α⇒)) ∘ α⇒ ∘ α⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ assoc²βε ○ ⟺ assoc ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ id ⊗₁ id ⊗₁ iso₁ (C , d) ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.pentagon ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ id ⊗₁ id ⊗₁ iso₁ (C , d) ∘ α⇒ ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ assoc ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ (id ⊗₁ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ FM.assoc-commute-from ⟩∘⟨refl ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ (α⇒ ∘ (id ⊗₁ id) ⊗₁ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ FM.⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ (α⇒ ∘ id ⊗₁ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ assoc ○ assoc ○ ⟺ assoc²βε ○ ⟺ idˡ ⟩
      id ∘ (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d) ∘ α⇒) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒ ∎

  -- The ⇐-direction naturality squares are conjugates of the ⇒-direction
  -- ones.  Deriving them via the generic conjugate transport keeps them
  -- outside the `unfolding` block, so they need no new chains.
  module _ where
    open import Categories.Morphism.Reasoning FreeMonoidal using (conjugate-from)
    open import Categories.Functor.Properties using ([_]-resp-≅)
    open FM.HomReasoning using (⟺)

    private
      module MP = Categories.Morphism P

      conj-square : ∀ {V W} (i : MP._≅_ V W)
        → iso₁ W ∘ Functor.F₁ F1 (MP._≅_.from i) FM.≈ Functor.F₁ F2 (MP._≅_.from i) ∘ iso₁ V
        → iso₁ V ∘ Functor.F₁ F1 (MP._≅_.to i) FM.≈ Functor.F₁ F2 (MP._≅_.to i) ∘ iso₁ W
      conj-square i sq = ⟺ (conjugate-from ([ F1 ]-resp-≅ i) ([ F2 ]-resp-≅ i) sq)

    natural-λ⇐ : ∀ {A d}
               → iso₁ (unit ⊗₀ A , d) ∘ λ⇐ ⊗₁ id
            FM.≈ id ∘ iso₁ (A , d)
    natural-λ⇐ {A} {d} = conj-square {unit ⊗₀ A , d} {A , d}
      (record { from = λ⇒ , refl ; to = λ⇐ , refl
              ; iso = record { isoˡ = FM.unitorˡ.isoˡ , _ ; isoʳ = FM.unitorˡ.isoʳ , _ } })
      natural-λ⇒

    natural-ρ⇐ : ∀ {A d}
               → iso₁ (A ⊗₀ unit , d) ∘ ρ⇐ ⊗₁ id
            FM.≈ id ∘ iso₁ (A , d)
    natural-ρ⇐ {A} {d} = conj-square {A ⊗₀ unit , d} {A , d}
      (record { from = ρ⇒ , refl ; to = ρ⇐ , refl
              ; iso = record { isoˡ = FM.unitorʳ.isoˡ , _ ; isoʳ = FM.unitorʳ.isoʳ , _ } })
      natural-ρ⇒

    natural-α⇐ : ∀ {A B C d}
               → iso₁ ((A ⊗₀ B) ⊗₀ C , d) ∘ α⇐ ⊗₁ id
            FM.≈ id ∘ iso₁ (A ⊗₀ B ⊗₀ C , d)
    natural-α⇐ {A} {B} {C} {d} = conj-square {(A ⊗₀ B) ⊗₀ C , d} {A ⊗₀ B ⊗₀ C , d}
      (record { from = α⇒ , refl ; to = α⇐ , refl
              ; iso = record { isoˡ = FM.associator.isoˡ , _ ; isoʳ = FM.associator.isoʳ , _ } })
      natural-α⇒

  natural₁ : ∀ d → Natural (appʳ F1 d) (appʳ F2 d) (λ c → iso₁ (c , d))
  natural₁ d id = natural-id
  natural₁ d (g ∘ f) = natural-∘ _ g f (natural₁ _ g) (natural₁ _ f)
  natural₁ d (_⊗₁_ {A} {B} {C} {D} f g) = natural-⊗ _ f g (natural₁ _ f) (natural₁ _ g)
  natural₁ d λ⇒ = natural-λ⇒
  natural₁ d λ⇐ = natural-λ⇐
  natural₁ d ρ⇒ = natural-ρ⇒
  natural₁ d ρ⇐ = natural-ρ⇐
  natural₁ d α⇒ = natural-α⇒
  natural₁ d α⇐ = natural-α⇐

  opaque
    unfolding iso₁
    ⟦⟧≅⊗ : NaturalIsomorphism F2 F1
    ⟦⟧≅⊗ = NI.sym (pointwise-iso iso natural)
      where
        natural : ∀ {X Y} → (f : P [ X , Y ])
                → FreeMonoidal [ iso₁ Y ∘ Functor.₁ F1 f ≈ Functor.₁ F2 f ∘ iso₁ X ]
        natural = natural-components F1 F2 iso₁ natural₁
          (λ c → Discrete-NaturalD {F = appˡ F1 c} {appˡ F2 c} (λ d → iso₁ (c , d)))

  -- The functor-level chain in Nf≅id reasons about the composition towers,
  -- so we recover them from the first-order F1/F2 up to NaturalIsomorphism
  -- (identity components; the F₁ actions agree definitionally under
  -- unfolding).
  opaque
    unfolding ⟦_⟧F ι
    private
      F1≅tower : NaturalIsomorphism F1 (FM.⊗ ∘F (F.id ⁂ ι))
      F1≅tower = niHelper record
        { η = λ _ → id ; η⁻¹ = λ _ → id
        ; commute = λ _ → FM.identityˡ ○ ⟺ FM.identityʳ
        ; iso = λ _ → record { isoˡ = FM.identity² ; isoʳ = FM.identity² } }
        where open FM.HomReasoning using (⟺; _○_)

      F2≅tower : NaturalIsomorphism (ι ∘F ⟦_⟧F) F2
      F2≅tower = niHelper record
        { η = λ _ → id ; η⁻¹ = λ _ → id
        ; commute = λ _ → FM.identityˡ ○ ⟺ FM.identityʳ
        ; iso = λ _ → record { isoˡ = FM.identity² ; isoʳ = FM.identity² } }
        where open FM.HomReasoning using (⟺; _○_)

  opaque
    unfolding ι
    Nf≅id : NaturalIsomorphism (ι ∘F Nf) F.id
    Nf≅id = begin
      ι ∘F Nf ≈⟨ NI.associator (-× []) ⟦_⟧F ι ⟨
      (ι ∘F ⟦_⟧F) ∘F -× [] ≈⟨ (F1≅tower ⓘᵥ (⟦⟧≅⊗ ⓘᵥ F2≅tower)) ⓘʳ (-× []) ⟩
      (FM.⊗ ∘F (F.id ⁂ ι)) ∘F -× [] ≈⟨ NI.associator (-× []) (F.id ⁂ ι) FM.⊗ ⟩
      FM.⊗ ∘F (F.id ⁂ ι) ∘F (-× []) ≈⟨ FM.⊗ ⓘˡ (⁂-× {C = FreeMonoidal} ι []) ⟩
      FM.⊗ ∘F (-× unit) ≈⟨ NI.refl ⟩
      appʳ FM.⊗ unit ≈⟨ FM.unitorʳ-naturalIsomorphism ⟩
      F.id ∎
      where open SetoidR (Functor-NI-setoid FreeMonoidal FreeMonoidal)

  all-Comm : ∀ {A B} f g → [ A ⇒ B ]⟨ f ≈ g ⟩
  all-Comm f g = push-eq Nf≅id (ι.F-resp-≈ _)
    where module ι = Functor ι

module Solver {o ℓ e} (C : MonoidalCategory o ℓ e)
              {n} (vars : Vec (C .MonoidalCategory.Obj) n) where
  open MonoidalCategory
  d : FreeMonoidalData
  d = record { v = Mon ; X = Fin n ; mor = λ _ _ → ⊥ }
  open FreeMonoidal d public
  open CoherenceThm (Fin n) FinP._≟_ hiding (⟦_⟧₁)
  open FreeFunctor {d = d} record
    { ⟦v⟧ = record { C = C .U ; Monoidal-C = C .monoidal ; Symmetric-C = λ where ⦃ () ⦄ }
    ; ⟦_⟧ᵖ₀ = lookup vars
    ; ⟦_⟧ᵖ₁ = λ ()
    } public

  opaque
    solveM : ∀ {X Y} → (f g : FreeMonoidal [ X , Y ]) → (C .U) [ ⟦ f ⟧₁ ≈ ⟦ g ⟧₁ ]
    solveM f g = Functor.F-resp-≈ freeFunctor (all-Comm f g)
  {-# INJECTIVE_FOR_INFERENCE solveM #-}
