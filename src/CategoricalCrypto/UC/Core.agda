{-# OPTIONS --safe --without-K #-}

-- The extra structure on a category that the UC models here are generated
-- from.

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor
open import Categories.Functor.Construction.LiftSetoids
open import Categories.Functor.Hom
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation

import Function.Relation.Binary.Setoid.Equality as FuncEq
open import Function using (_∘′_)
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
import Relation.Binary.Construct.On as On
import Relation.Binary.Reasoning.Setoid as SetoidR

module CategoricalCrypto.UC.Core where

-- Categories where morphisms into Ω can be observed. Observation is a
-- natural transformation Θ : hom(-, Ω) => P for some presheaf P.
record Observable {o ℓ e} (𝒞 : Category o ℓ e) (c ℓ′ : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc (c ⊔ ℓ′)) where
  open Category 𝒞

  field
    Ω : Obj
    P : Presheaf 𝒞 (Setoids c ℓ′)

  module P = Functor P

  field
    θ         : {A : Obj} → Func Hom[ 𝒞 ][ A , Ω ] (P.₀ A)
    θ-natural : {A B : Obj} (let module B = Setoid (P.₀ B)) (f : B ⇒ A) (t : A ⇒ Ω)
              → θ ⟨$⟩ (t ∘ f) B.≈ P.₁ f ⟨$⟩ (θ ⟨$⟩ t)

  -- This would have been preferred over the two previous fields, if
  -- the levels could have been made to work nicely
  Θ : NaturalTransformation (LiftSetoids c ℓ′ ∘F Hom[ 𝒞 ][-, Ω ]) (LiftSetoids ℓ e ∘F P)
  Θ = ntHelper record
    { η = λ _ → record
        { to = λ t → lift (θ ⟨$⟩ lower t)
        ; cong = λ eq → lift (Func.cong θ (lower eq))
        }
    ; commute = λ {_} {Y} f → lift (Setoid.trans (P.₀ Y) (Func.cong θ identityˡ) (θ-natural f _))
    }

  private variable A B : Obj

  Test : Obj → Set ℓ
  Test A = A ⇒ Ω

  obs : Test A → Setoid.Carrier (P.₀ A)
  obs t = θ ⟨$⟩ t

  -- Im (obs {A})
  ℰ₀ : Obj → Setoid ℓ ℓ′
  ℰ₀ A = On.setoid (P.₀ A) (obs {A})

  infix 4 _≋_

  _≋_ : Test A → Test A → Set ℓ′
  _≋_ {A} = Setoid._≈_ (ℰ₀ A)

  ≋-isEquivalence : IsEquivalence (_≋_ {A})
  ≋-isEquivalence {A} = Setoid.isEquivalence (ℰ₀ A)

  ≈⇒≋ : {t u : Test A} → t ≈ u → t ≋ u
  ≈⇒≋ = Func.cong θ

  ≋-cast : {t t′ u u′ : Test A} → t ≈ t′ → u ≈ u′ → t ≋ u → t′ ≋ u′
  ≋-cast {A} et eu h = S.trans (S.sym (≈⇒≋ et)) (S.trans h (≈⇒≋ eu))
    where module S = Setoid (ℰ₀ A)

  pull : (f : B ⇒ A) → Test A → Test B
  pull f t = t ∘ f

  pull-cong : {f : B ⇒ A} {t u : Test A} → t ≋ u → pull f t ≋ pull f u
  pull-cong {B} {f = f} {t} {u} h = begin
    obs (pull f t)   ≈⟨ θ-natural f t ⟩
    P.₁ f ⟨$⟩ obs t  ≈⟨ Func.cong (P.₁ f) h ⟩
    P.₁ f ⟨$⟩ obs u  ≈⟨ θ-natural f u ⟨
    obs (pull f u)   ∎
    where open SetoidR (P.₀ B)

  -- This is Im Θ
  ℰᴼ : Presheaf 𝒞 (Setoids ℓ ℓ′)
  ℰᴼ = record
    { F₀           = ℰ₀
    ; F₁           = λ f → record { to = pull f ; cong = pull-cong }
    ; identity     = ≈⇒≋ identityʳ
    ; homomorphism = ≈⇒≋ sym-assoc
    ; F-resp-≈     = λ eq → ≈⇒≋ (∘-resp-≈ʳ eq)
    }

-- Observation by evaluation
record Evaluation {o ℓ e} (𝒞 : Category o ℓ e) (cs ℓs : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc cs ⊔ suc ℓs) where
  open Category 𝒞

  field
    J Ω  : Obj
    S    : Setoid cs ℓs
    eval : Func Hom[ 𝒞 ][ J , Ω ] S

  module S = Setoid S

  Closure : Obj → Set ℓ
  Closure A = J ⇒ A

  read : Closure Ω → S.Carrier
  read = Func.to eval

  read-resp : {u v : Closure Ω} → u ≈ v → read u S.≈ read v
  read-resp = Func.cong eval

  read-cast : {u u′ v v′ : Closure Ω} → u ≈ u′ → v ≈ v′
            → read u S.≈ read v → read u′ S.≈ read v′
  read-cast eu ev h = S.trans (S.sym (read-resp eu)) (S.trans h (read-resp ev))

  observe : {A : Obj} → A ⇒ Ω → Closure A → S.Carrier
  observe t m = read (t ∘ m)

  -- This is `Hom[ Setoids ][-, S ] ∘F Hom[ 𝒞 ][ J ,-]` up to level issues
  Pᴱ : Presheaf 𝒞 (Setoids (ℓ ⊔ e ⊔ cs ⊔ ℓs) (ℓ ⊔ ℓs))
  Pᴱ = record
    { F₀ = λ A → FuncEq.setoid Hom[ 𝒞 ][ J , A ] S
    ; F₁ = λ f → record
        { to   = λ k → record { to = λ m → k ⟨$⟩ (f ∘ m) ; cong = Func.cong k ∘′ ∘-resp-≈ʳ }
        ; cong = λ h m → h (f ∘ m)
        }
    ; identity     = λ {_} {k} m → Func.cong k identityˡ
    ; homomorphism = λ {_} {_} {_} {_} {_} {k} m → Func.cong k assoc
    ; F-resp-≈     = λ f≈g {k} m → Func.cong k (f≈g ⟩∘⟨refl)
    }
    where open HomReasoning

  transpose : {A : Obj} → A ⇒ Ω → Func Hom[ 𝒞 ][ J , A ] S
  transpose t = record { to = observe t ; cong = read-resp ∘′ ∘-resp-≈ʳ }

  observable : Observable 𝒞 (ℓ ⊔ e ⊔ cs ⊔ ℓs) (ℓ ⊔ ℓs)
  observable = record
    { Ω = Ω ; P = Pᴱ
    ; θ = record { to = transpose ; cong = λ t≈u m → read-resp (t≈u ⟩∘⟨refl) }
    ; θ-natural = λ f t m → read-resp assoc
    }
    where open HomReasoning
