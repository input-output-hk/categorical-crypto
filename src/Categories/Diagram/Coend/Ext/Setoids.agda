{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Concrete coends of Setoids-valued bifunctors.
--
-- The coend of F : Bifunctor C.op C (Setoids c ℓs) is carried by
-- Σ[ X ] F₀ (X , X) with equality the equivalence closure of the one-step
-- dinaturality relation — the Set-valued coend formula of Mac Lane, CWM IX.6,
-- as a quotient rather than a coequalizer.  The carrier computes transparently
-- (unlike the coend recovered from Setoids-Cocomplete via
-- Categories.Diagram.Coend.Colimit), which is what downstream free-actegory /
-- Day constructions need.
--------------------------------------------------------------------------------

module Categories.Diagram.Coend.Ext.Setoids where

open import Level

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Diagram.Coend
open import Categories.Diagram.Cowedge
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.Dinatural
  using (DinaturalTransformation; extranaturalˡ; extranatural-commˡ)
open import Categories.NaturalTransformation.Equivalence

open import Data.Product
open import Data.Product.Function.NonDependent.Setoid
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function.Bundles
open import Function.Construct.Composition
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Equivalence

open Func

-- Constructing a profunctor from one covariant and one contravariant functor
module _ {o ℓ e c ℓs c′ ℓs′} {C : Category o ℓ e} where
  infix 4 _×ᵈ_
  _×ᵈ_ : Functor C (Setoids c ℓs) → Presheaf C (Setoids c′ ℓs′)
       → Bifunctor (Category.op C) C (Setoids (c ⊔ c′) (ℓs ⊔ ℓs′))
  F ×ᵈ P = record
    { F₀           = λ (u , v) → F.F₀ v ×ₛ P.F₀ u
    ; F₁           = λ (φ , ψ) → F.F₁ ψ ×-function P.F₁ φ
    ; identity     = F.identity , P.identity
    ; homomorphism = F.homomorphism , P.homomorphism
    ; F-resp-≈     = λ (φ≈ , ψ≈) → F.F-resp-≈ ψ≈ , P.F-resp-≈ φ≈
    }
    where module F = Functor F
          module P = Functor P

module SetoidCoend {o ℓ e c ℓs} {C : Category o ℓ e}
  (F : Bifunctor (Category.op C) C (Setoids c ℓs)) where

  open Functor F

  private
    module C = Category C

    ∣_∣ : Setoid c ℓs → Set c
    ∣_∣ = Setoid.Carrier

    infix 4 _≈ᶠ_
    _≈ᶠ_ : ∀ {P} → ∣ F₀ P ∣ → ∣ F₀ P ∣ → Set ℓs
    _≈ᶠ_ {P} = Setoid._≈_ (F₀ P)

  Elt : Set (o ⊔ c)
  Elt = Σ[ X ∈ C.Obj ] ∣ F₀ (X , X) ∣

  -- one dinaturality step
  Step : Rel Elt (ℓ ⊔ c ⊔ ℓs)
  Step (X , x) (Y , y) = Σ[ f ∈ X C.⇒ Y ] Σ[ w ∈ ∣ F₀ (Y , X) ∣ ]
    (F₁ (f , C.id) ⟨$⟩ w ≈ᶠ x) × (F₁ (C.id , f) ⟨$⟩ w ≈ᶠ y)

  ∫ : Setoid (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓs)
  ∫ = setoid Step

  ι : ∀ X → Func (F₀ (X , X)) ∫
  ι X = record
    { to   = X ,_
    ; cong = λ {x} x≈y → return (C.id , x , identity , Setoid.trans (F₀ _) identity x≈y)
    }

  dinatural-step : ∀ {X Y} (f : C [ X , Y ]) (w : ∣ F₀ (Y , X) ∣) →
                   Setoid._≈_ ∫ (X , F₁ (f , C.id) ⟨$⟩ w) (Y , F₁ (C.id , f) ⟨$⟩ w)
  dinatural-step f w = return (f , w , Setoid.refl (F₀ _) , Setoid.refl (F₀ _))

  -- Mapping-out principle: a Setoid map out of ∫ is exactly a family of maps
  -- out of the F₀ (X , X) that respects the dinaturality step.
  record Copairing {c′ ℓs′} (S : Setoid c′ ℓs′) : Set (o ⊔ ℓ ⊔ c ⊔ ℓs ⊔ c′ ⊔ ℓs′) where
    private module S = Setoid S
    field at        : ∀ X → Func (F₀ (X , X)) S
          dinatural : ∀ {X Y} (f : X C.⇒ Y) (w : ∣ F₀ (Y , X) ∣) →
                      at X ⟨$⟩ (F₁ (f , C.id) ⟨$⟩ w) S.≈ at Y ⟨$⟩ (F₁ (C.id , f) ⟨$⟩ w)

  copair : ∀ {c′ ℓs′} {S : Setoid c′ ℓs′} → Copairing S → Func ∫ S
  copair {S = S} κ = record { to = ⟦_⟧ ; cong = gfold S.isEquivalence ⟦_⟧ gen }
    where
    open Copairing κ
    module S = Setoid S

    ⟦_⟧ : Elt → Setoid.Carrier S
    ⟦ X , x ⟧ = at X ⟨$⟩ x

    gen : ∀ {p q} → Step p q → ⟦ p ⟧ S.≈ ⟦ q ⟧
    gen {X , x} {Y , y} (f , w , e₁ , e₂) =
      S.trans (S.sym (cong (at X) e₁)) (S.trans (dinatural f w) (cong (at Y) e₂))

  copair-β : ∀ {c′ ℓs′} {S : Setoid c′ ℓs′} (κ : Copairing S) {X x} →
             Setoid._≈_ S (copair κ ⟨$⟩ (ι X ⟨$⟩ x)) (Copairing.at κ X ⟨$⟩ x)
  copair-β {S = S} _ = Setoid.refl S

  restrict : ∀ {c′ ℓs′} {S : Setoid c′ ℓs′} → Func ∫ S → Copairing S
  restrict g = record
    { at        = λ X → function (ι X) g
    ; dinatural = λ f w → cong g (dinatural-step f w)
    }

  copair-restrict : ∀ {c′ ℓs′} {S : Setoid c′ ℓs′} (g : Func ∫ S) {p} →
                    Setoid._≈_ S (copair (restrict g) ⟨$⟩ p) (g ⟨$⟩ p)
  copair-restrict {S = S} _ = Setoid.refl S

  restrict-copair : ∀ {c′ ℓs′} {S : Setoid c′ ℓs′} (κ : Copairing S) {X x} →
                    Setoid._≈_ S (Copairing.at (restrict (copair κ)) X ⟨$⟩ x)
                                 (Copairing.at κ X ⟨$⟩ x)
  restrict-copair {S = S} _ = Setoid.refl S

  copair-unique : ∀ {c′ ℓs′} {S : Setoid c′ ℓs′} (κ : Copairing S) (g : Func ∫ S) →
                  (∀ X {x} → Setoid._≈_ S (g ⟨$⟩ (ι X ⟨$⟩ x)) (Copairing.at κ X ⟨$⟩ x)) →
                  ∀ {p} → Setoid._≈_ S (g ⟨$⟩ p) (copair κ ⟨$⟩ p)
  copair-unique κ g hyp {X , x} = hyp X

-- Two-variable mapping-out principle
module _ {o ℓ e c ℓs c′ ℓs′} {C : Category o ℓ e}
  (F : Bifunctor (Category.op C) C (Setoids c ℓs))
  (G : Bifunctor (Category.op C) C (Setoids c′ ℓs′)) where

  private
    module C = Category C
    module F = Functor F
    module G = Functor G
    module ∫F = SetoidCoend F
    module ∫G = SetoidCoend G

  record Copairing₂ {c″ ℓs″} (S : Setoid c″ ℓs″)
      : Set (o ⊔ ℓ ⊔ c ⊔ ℓs ⊔ c′ ⊔ ℓs′ ⊔ c″ ⊔ ℓs″) where
    private module S = Setoid S
    field
      at : ∀ X Y → Func (F.F₀ (X , X) ×ₛ G.F₀ (Y , Y)) S
      dinaturalˡ : ∀ {X Y} (f : X C.⇒ Y) (w : Setoid.Carrier (F.F₀ (Y , X)))
                   {Z} (z : Setoid.Carrier (G.F₀ (Z , Z))) →
                   at X Z ⟨$⟩ (F.F₁ (f , C.id) ⟨$⟩ w , z)
                     S.≈ at Y Z ⟨$⟩ (F.F₁ (C.id , f) ⟨$⟩ w , z)
      dinaturalʳ : ∀ {X Y} (f : X C.⇒ Y) (w : Setoid.Carrier (G.F₀ (Y , X)))
                   {Z} (z : Setoid.Carrier (F.F₀ (Z , Z))) →
                   at Z X ⟨$⟩ (z , G.F₁ (f , C.id) ⟨$⟩ w)
                     S.≈ at Z Y ⟨$⟩ (z , G.F₁ (C.id , f) ⟨$⟩ w)

  copair₂ : ∀ {c″ ℓs″} {S : Setoid c″ ℓs″} → Copairing₂ S → Func (∫F.∫ ×ₛ ∫G.∫) S
  copair₂ {S = S} κ = record
    { to   = λ ((X , x) , (Y , y)) → at X Y ⟨$⟩ (x , y)
    ; cong = λ {(_ , q)} {(p′ , _)} (p≈ , q≈) →
        S.trans (cong (∫F.copair (fixʳ q)) p≈) (cong (∫G.copair (fixˡ p′)) q≈)
    }
    where
    open Copairing₂ κ
    module S = Setoid S

    -- copairing in one variable with a representative of the other one fixed
    fixʳ : ∫G.Elt → ∫F.Copairing S
    fixʳ (Y , y) = record
      { at        = λ X → record
        { to   = λ x → at X Y ⟨$⟩ (x , y)
        ; cong = λ x≈ → cong (at X Y) (x≈ , Setoid.refl (G.F₀ (Y , Y))) }
      ; dinatural = λ f w → dinaturalˡ f w y
      }

    fixˡ : ∫F.Elt → ∫G.Copairing S
    fixˡ (X , x) = record
      { at        = λ Y → record
        { to   = λ y → at X Y ⟨$⟩ (x , y)
        ; cong = λ y≈ → cong (at X Y) (Setoid.refl (F.F₀ (X , X)) , y≈) }
      ; dinatural = λ f w → dinaturalʳ f w x
      }

-- Functoriality: a natural transformation of bifunctors induces a map of
-- coends, functorially up to ≈.
module _ {o ℓ e c ℓs} {C : Category o ℓ e}
  {F G : Bifunctor (Category.op C) C (Setoids c ℓs)} (η : NaturalTransformation F G) where

  private
    module C = Category C
    module G = Functor G
    module η = NaturalTransformation η
    module ∫F = SetoidCoend F
    module ∫G = SetoidCoend G

  map∫ : Func ∫F.∫ ∫G.∫
  map∫ = record { to = ⟦_⟧ ; cong = gmap ⟦_⟧ gen }
    where
    ⟦_⟧ : ∫F.Elt → ∫G.Elt
    ⟦ X , x ⟧ = X , η.η (X , X) ⟨$⟩ x

    gen : ∀ {p q} → ∫F.Step p q → ∫G.Step ⟦ p ⟧ ⟦ q ⟧
    gen {X , x} {Y , y} (f , w , e₁ , e₂) =
        f , η.η (Y , X) ⟨$⟩ w
      , GX.trans (GX.sym (η.commute (f , C.id))) (cong (η.η (X , X)) e₁)
      , GY.trans (GY.sym (η.commute (C.id , f))) (cong (η.η (Y , Y)) e₂)
      where
      module GX = Setoid (G.F₀ (X , X))
      module GY = Setoid (G.F₀ (Y , Y))

module _ {o ℓ e c ℓs} {C : Category o ℓ e}
  {F : Bifunctor (Category.op C) C (Setoids c ℓs)} where

  map∫-identity : ∀ {p} → Setoid._≈_ (SetoidCoend.∫ F) (map∫ (idN {F = F}) ⟨$⟩ p) p
  map∫-identity = Setoid.refl (SetoidCoend.∫ F)

module _ {o ℓ e c ℓs} {C : Category o ℓ e}
  {F G : Bifunctor (Category.op C) C (Setoids c ℓs)} where

  map∫-homomorphism : ∀ {H : Bifunctor (Category.op C) C (Setoids c ℓs)}
                      (θ : NaturalTransformation G H) (η : NaturalTransformation F G) {p} →
                      Setoid._≈_ (SetoidCoend.∫ H) (map∫ (θ ∘ᵥ η) ⟨$⟩ p) (map∫ θ ⟨$⟩ (map∫ η ⟨$⟩ p))
  map∫-homomorphism {H = H} _ _ = Setoid.refl (SetoidCoend.∫ H)

  map∫-cong : {η θ : NaturalTransformation F G} → η ≃ θ →
              ∀ {p} → Setoid._≈_ (SetoidCoend.∫ G) (map∫ η ⟨$⟩ p) (map∫ θ ⟨$⟩ p)
  map∫-cong η≃θ {X , x} = cong (SetoidCoend.ι G X) η≃θ

-- At matching levels the construction packages into the
-- agda-categories universal-property records.
module _ {o ℓ e} (c ℓs : Level) {C : Category o ℓ e}
  (F : Bifunctor (Category.op C) C (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓs))) where

  open SetoidCoend F

  Setoids-cowedge : Cowedge F
  Setoids-cowedge = record
    { E         = ∫
    ; dinatural = extranaturalˡ ι (λ {X X′ f} {w} → dinatural-step f w)
    }

  Setoids-coend : Coend F
  Setoids-coend = record
    { cowedge   = Setoids-cowedge
    ; factor    = λ W → copair (record
        { at        = DinaturalTransformation.α (Cowedge.dinatural W)
        ; dinatural = λ f w → extranatural-commˡ (Cowedge.dinatural W)
        })
    ; universal = λ {W} → Setoid.refl (Cowedge.E W)
    ; unique    = λ {W} {g} eq {p} → Setoid.sym (Cowedge.E W) eq
    }
