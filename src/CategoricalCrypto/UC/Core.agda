{-# OPTIONS --safe --without-K #-}

-- The extra structure on a category that the UC models here are generated
-- from.

open import categorical-crypto.Prelude using (PredS)

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor.Hom
open import Categories.Functor.Presheaf

import Function.Relation.Binary.Setoid.Equality as FuncEq
open import Function using (_∘′_)
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
import Relation.Binary.Construct.On as On

module CategoricalCrypto.UC.Core where

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

  transpose : {A : Obj} → A ⇒ Ω → Func Hom[ 𝒞 ][ J , A ] S
  transpose t = record { to = observe t ; cong = read-resp ∘′ ∘-resp-≈ʳ }

  Test : Obj → Set ℓ
  Test A = A ⇒ Ω

  -- Tests up to what they observe: the image of `Hom[ 𝒞 ][-, Ω ]` in
  -- `Hom[ Setoids ][-, S ] ∘F Hom[ 𝒞 ][ J ,-]`.
  ℰ₀ : Obj → Setoid ℓ (ℓ ⊔ ℓs)
  ℰ₀ A = On.setoid (FuncEq.setoid Hom[ 𝒞 ][ J , A ] S) transpose

  private variable A B : Obj

  infix 4 _≋_

  _≋_ : Test A → Test A → Set (ℓ ⊔ ℓs)
  _≋_ {A} = Setoid._≈_ (ℰ₀ A)

  ≋-isEquivalence : IsEquivalence (_≋_ {A})
  ≋-isEquivalence {A} = Setoid.isEquivalence (ℰ₀ A)

  ≈⇒≋ : {t u : Test A} → t ≈ u → t ≋ u
  ≈⇒≋ t≈u m = read-resp (∘-resp-≈ˡ t≈u)

  pull : (f : B ⇒ A) → Test A → Test B
  pull f t = t ∘ f

  pull-cong : {f : B ⇒ A} {t u : Test A} → t ≋ u → pull f t ≋ pull f u
  pull-cong {f = f} h m = read-cast sym-assoc sym-assoc (h (f ∘ m))

  ℰᴼ : Presheaf 𝒞 (Setoids ℓ (ℓ ⊔ ℓs))
  ℰᴼ = record
    { F₀           = ℰ₀
    ; F₁           = λ f → record { to = pull f ; cong = pull-cong }
    ; identity     = ≈⇒≋ identityʳ
    ; homomorphism = ≈⇒≋ sym-assoc
    ; F-resp-≈     = λ eq → ≈⇒≋ (∘-resp-≈ʳ eq)
    }

  -- always P e :<=> for any closure to run e with, P holds
  always : ∀ {p D} → PredS S p → PredS (ℰ₀ D) (ℓ ⊔ p)
  always {D = D} P = record
    { to   = λ e → (m : Closure D) → P ⟨$⟩ observe e m
    ; cong = λ eq → mk⇔ (λ h m → Equivalence.to (Func.cong P (eq m)) (h m))
                        (λ h m → Equivalence.from (Func.cong P (eq m)) (h m)) }
