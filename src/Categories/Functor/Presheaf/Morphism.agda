{-# OPTIONS --safe --without-K #-}

-- A morphism of setoid-valued presheaves along a functor: a natural
-- transformation ν : P ⇒ Q ∘ F.op.  Paired with F these are the hom-sets of
-- ∫ [-ᵒᵖ, Setoid], the Grothendieck construction of 𝒞 ↦ [𝒞ᵒᵖ, Setoid]; the
-- record is the fibre over a fixed F.  The library's `Grothendieck` still
-- cannot host it: it wants one pseudofunctor, hence one presheaf category, over
-- a locally thin base, so the pullback would have to ignore which natural iso
-- it transports along.

open import Level

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Presheaf

module Categories.Functor.Presheaf.Morphism where

open import Data.Product
open import Function.Bundles
open import Function.Definitions
open import Relation.Binary.Bundles
import Relation.Binary.Construct.On as On

open import Categories.Category.Instance.Setoids
import Categories.KernelCongruence as KernelCong
open import Categories.NaturalTransformation renaming (id to idN)

private variable
  oc ℓc ec od ℓd ed oe ℓe ee cs ℓs : Level

record PresheafMorphism {C : Category oc ℓc ec} {D : Category od ℓd ed}
                        (F : Functor C D) (P : Presheaf C (Setoids cs ℓs))
                        (Q : Presheaf D (Setoids cs ℓs))
                        : Set (oc ⊔ ℓc ⊔ cs ⊔ ℓs) where
  private
    module C = Category C
    module P = Functor P
    module Q = Functor Q
    module F = Functor F

  field
    ν : NaturalTransformation P (Q ∘F F.op)

  open NaturalTransformation ν public

  Epi : Set (oc ⊔ cs ⊔ ℓs)
  Epi = {A : C.Obj} → StrictlySurjective (Setoid._≈_ (Q.₀ (F.₀ A))) (η A ⟨$⟩_)

  Mono : Set (oc ⊔ cs ⊔ ℓs)
  Mono = {A : C.Obj}
       → Injective (Setoid._≈_ (P.₀ A)) (Setoid._≈_ (Q.₀ (F.₀ A))) (η A ⟨$⟩_)

module _ {C : Category oc ℓc ec} {D : Category od ℓd ed} {F : Functor C D}
         {P : Presheaf C (Setoids cs ℓs)} {Q : Presheaf D (Setoids cs ℓs)}
         (ν : PresheafMorphism F P Q) where
  open PresheafMorphism ν

  private
    module C = Category C
    module D = Category D
    module P = Functor P
    module Q = Functor Q
    module F = Functor F
    module SQ {A : C.Obj} = Setoid (Q.₀ (F.₀ A))
    module KP = KernelCong C.op (Setoids cs ℓs) P
    module KQ = KernelCong D.op (Setoids cs ℓs) Q

  ------------------------------------------------------------------------
  -- The dichotomy: one naturality square, cancelled on either side
  ------------------------------------------------------------------------

  epi⇒preserves : Epi → {A B : C.Obj} {f g : C [ A , B ]} → f KP.∼ g → F.₁ f KQ.∼ F.₁ g
  epi⇒preserves epi {f = f} {g} e = KQ.mk∼ λ {y} →
    let (x , ηx≈y) = epi y in
    SQ.trans (SQ.sym (Func.cong (Q.₁ (F.₁ f)) ηx≈y))
      (SQ.trans (sym-commute f)
        (SQ.trans (Func.cong (η _) (KP.run∼ e))
          (SQ.trans (commute g) (Func.cong (Q.₁ (F.₁ g)) ηx≈y))))

  mono⇒reflects : Mono → {A B : C.Obj} {f g : C [ A , B ]} → F.₁ f KQ.∼ F.₁ g → f KP.∼ g
  mono⇒reflects mono {f = f} {g} e = KP.mk∼ λ {x} →
    mono (SQ.trans (commute f) (SQ.trans (KQ.run∼ e) (sym-commute g)))

  ------------------------------------------------------------------------
  -- The epi/mono factorization
  ------------------------------------------------------------------------

  image : Presheaf C (Setoids cs ℓs)
  image = record
    { F₀ = λ A → On.setoid (Q.₀ (F.₀ A)) (η A ⟨$⟩_)
    ; F₁ = λ f → record
      { to = P.₁ f ⟨$⟩_
      ; cong = λ e → SQ.trans (commute f)
                       (SQ.trans (Func.cong (Q.₁ (F.₁ f)) e) (sym-commute f)) }
    ; identity = Func.cong (η _) P.identity
    ; homomorphism = Func.cong (η _) P.homomorphism
    ; F-resp-≈ = λ e → Func.cong (η _) (P.F-resp-≈ e)
    }

  toImage : PresheafMorphism idF P image
  toImage = record { ν = ntHelper record
    { η = λ A → record { to = λ x → x ; cong = Func.cong (η A) }
    ; commute = λ _ → SQ.refl } }

  toImage-epi : PresheafMorphism.Epi toImage
  toImage-epi y = y , SQ.refl

  fromImage : PresheafMorphism F image Q
  fromImage = record { ν = ntHelper record
    { η = λ A → record { to = η A ⟨$⟩_ ; cong = λ e → e } ; commute = commute } }

  fromImage-mono : PresheafMorphism.Mono fromImage
  fromImage-mono e = e

------------------------------------------------------------------------
-- Pasting along a composite base
------------------------------------------------------------------------

module _ {C : Category oc ℓc ec} {D : Category od ℓd ed} {E : Category oe ℓe ee}
         {G : Functor C D} {F : Functor D E}
         {P : Presheaf C (Setoids cs ℓs)} {Q : Presheaf D (Setoids cs ℓs)}
         {R : Presheaf E (Setoids cs ℓs)} where
  private
    module G = Functor G
    module R = Functor R

  infixr 9 _∘ᵛ_

  _∘ᵛ_ : PresheafMorphism F Q R → PresheafMorphism G P Q
       → PresheafMorphism (F ∘F G) P R
  ν′ ∘ᵛ ν = record { ν = ntHelper record
    { η = λ A → record
      { to = λ x → ν′.η (G.₀ A) ⟨$⟩ (ν.η A ⟨$⟩ x)
      ; cong = λ e → Func.cong (ν′.η (G.₀ A)) (Func.cong (ν.η A) e) }
    ; commute = λ f → Setoid.trans (R.₀ _) (Func.cong (ν′.η _) (ν.commute f))
                                           (ν′.commute (G.₁ f)) } }
    where module ν = PresheafMorphism ν
          module ν′ = PresheafMorphism ν′

------------------------------------------------------------------------
-- The two comparisons that change nothing
------------------------------------------------------------------------

private variable
  C : Category oc ℓc ec
  D : Category od ℓd ed
  P : Presheaf C (Setoids cs ℓs)
  Q : Presheaf D (Setoids cs ℓs)
  F : Functor C D

idᵛ : (P : Presheaf C (Setoids cs ℓs)) → PresheafMorphism idF P P
idᵛ P = record { ν = F⇒F∘id }

idᵛ-epi : PresheafMorphism.Epi (idᵛ P)
idᵛ-epi {P = P} {A = A} y = y , Setoid.refl (Functor.₀ P A)

idᵛ-mono : PresheafMorphism.Mono (idᵛ P)
idᵛ-mono e = e

pullbackᵛ : (F : Functor C D) (Q : Presheaf D (Setoids cs ℓs))
          → PresheafMorphism F (Q ∘F Functor.op F) Q
pullbackᵛ F Q = record { ν = idN }

pullbackᵛ-epi : PresheafMorphism.Epi (pullbackᵛ F Q)
pullbackᵛ-epi {F = F} {Q = Q} {A = A} y = y , Setoid.refl (Functor.₀ Q (Functor.₀ F A))

pullbackᵛ-mono : PresheafMorphism.Mono (pullbackᵛ F Q)
pullbackᵛ-mono e = e
