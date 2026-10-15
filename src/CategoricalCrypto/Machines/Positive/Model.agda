{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Model where

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor.Monoidal

open import Data.Product.Base
open import Data.Sum.Base using (_⊎_)
open import Level
open import Relation.Binary.PropositionalEquality using (subst₂)

open import CategoricalCrypto.Iface
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Base as Positive
open import CategoricalCrypto.Machines.Positive.Bridge using (repack-compose; repack-tensor)
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Model.Seal as Seal

private
  module G = MonoidalCategory Seal.𝔾ᵒ
  module QG = MonoidalCategory (Positive.𝒢₊ᴹ 0ℓ)
  module QS = Sim (Positive.𝒱₊ 0ℓ) (Positive.𝒫₊ 0ℓ)
  module R = Re.At 0ℓ
  module RG = Raw.At 0ℓ

opaque
  unfolding Seal.𝔾ᵒ

  _≈⁺_ : {A B : G.Obj} → A G.⇒ B → A G.⇒ B → Set₁
  _≈⁺_ {A} {B} f g = QS._≈ᴹ_ {proj₁ A ⊎ proj₂ B} {proj₂ A ⊎ proj₁ B}
    (R.repack {proj₁ A ⊎ proj₂ B} {proj₂ A ⊎ proj₁ B} f)
    (R.repack {proj₁ A ⊎ proj₂ B} {proj₂ A ⊎ proj₁ B} g)

opaque
  unfolding Seal.𝔾ᵒ _≈⁺_

  positive-congruence : MonoidalCongruence Seal.𝔾ᵒ (suc 0ℓ)
  positive-congruence = record
    { _∼_ = _≈⁺_
    ; ∼-equiv = record
      { refl = λ {f} → QS.reflᴹ
      ; sym = λ p → QS.⟺ᴹ p
      ; trans = λ p q → QS._○ᴹ_ p q
      }
    ; ≈⇒∼ = R.repack-resp
    ; ∘-resp-∼ = λ {A} {B} {C} {f} {h} {g} {i} p q →
        QS._○ᴹ_ (R.repack-resp (R.PS.⟺ᴹ (RG.composeₚ-project f g)))
          (QS._○ᴹ_ (repack-compose 0ℓ f g)
            (QS._○ᴹ_ (RG.compose₊-cong p q)
              (QS._○ᴹ_ (QS.⟺ᴹ (repack-compose 0ℓ h i))
                (R.repack-resp (RG.composeₚ-project h i)))))
    ; ⊗-resp-∼ = λ {A} {B} {C} {D} {f} {h} {g} {i} p q →
        QS._○ᴹ_ (R.repack-resp (R.PS.⟺ᴹ (RG.tensorₚ-project f g)))
          (QS._○ᴹ_ (repack-tensor 0ℓ f g)
            (QS._○ᴹ_ (RG.tensor₊-cong p q)
              (QS._○ᴹ_ (QS.⟺ᴹ (repack-tensor 0ℓ h i))
                (R.repack-resp (RG.tensorₚ-project h i)))))
    }

𝔾₊ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝔾₊ = quotient Seal.𝔾ᵒ positive-congruence

forget-probabilities : StrongMonoidalFunctor Seal.𝔾ᵒ 𝔾₊
forget-probabilities = quotientF Seal.𝔾ᵒ positive-congruence

private module T = MonoidalCategory 𝔾₊

pack-positive : {A B : Iface}
  → R.Q.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B) → Seal.ifaceᵒ A T.⇒ Seal.ifaceᵒ B
pack-positive f = Seal.procᵒ (R.unpack f)

-- The seal deliberately hides object computation.  Tensor therefore uses its
-- existing propositional interface equations rather than a second bundle.
tensor-at : {A B C D : Iface}
  → Seal.ifaceᵒ A T.⇒ Seal.ifaceᵒ B → Seal.ifaceᵒ C T.⇒ Seal.ifaceᵒ D
  → Seal.ifaceᵒ (A ⊗ᴵ C) T.⇒ Seal.ifaceᵒ (B ⊗ᴵ D)
tensor-at {A} {B} {C} {D} f g = subst₂ T._⇒_ (Seal.⊗ᵒ A C) (Seal.⊗ᵒ B D) (T._⊗₁_ f g)

opaque
  unfolding Seal.𝔾ᵒ Seal.ifaceᵒ Seal.procᵒ Seal.⊗ᵒ positive-congruence _≈⁺_

  pack-positive-resp : {A B : Iface}
    {f g : R.Q.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)}
    → f QS.≈ᴹ g → pack-positive {A} {B} f T.≈ pack-positive {A} {B} g
  pack-positive-resp {f = f} {g} eq = QS._○ᴹ_ (R.repack-unpack f)
    (QS._○ᴹ_ eq (QS.⟺ᴹ (R.repack-unpack g)))

  pack-positive-compose : {A B C : Iface}
    (g : R.Q.Machine (Pos B ⊎ Neg C) (Neg B ⊎ Pos C))
    (f : R.Q.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B))
    → pack-positive {A} {C} (QG._∘_ {Pos A , Neg A} {Pos B , Neg B} {Pos C , Neg C} g f)
      T.≈ (pack-positive {B} {C} g T.∘ pack-positive {A} {B} f)
  pack-positive-compose {A} {B} {C} g f = QS._○ᴹ_ (R.repack-unpack _)
    (QS._○ᴹ_ (QS.⟺ᴹ (RG.compose₊-project g f))
      (QS._○ᴹ_ (RG.compose₊-cong (QS.⟺ᴹ (R.repack-unpack g)) (QS.⟺ᴹ (R.repack-unpack f)))
        (QS._○ᴹ_ (QS.⟺ᴹ (repack-compose 0ℓ (R.unpack g) (R.unpack f)))
          (R.repack-resp (RG.composeₚ-project (R.unpack g) (R.unpack f))))))

  pack-positive-tensor : {A B C D : Iface}
    (f : R.Q.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B))
    (g : R.Q.Machine (Pos C ⊎ Neg D) (Neg C ⊎ Pos D))
    → pack-positive {A ⊗ᴵ C} {B ⊗ᴵ D}
        (QG._⊗₁_ {Pos A , Neg A} {Pos B , Neg B} {Pos C , Neg C} {Pos D , Neg D} f g)
      T.≈ tensor-at (pack-positive {A} {B} f) (pack-positive {C} {D} g)
  pack-positive-tensor {A} {B} {C} {D} f g = QS._○ᴹ_ (R.repack-unpack _)
    (QS._○ᴹ_ (QS.⟺ᴹ (RG.tensor₊-project f g))
      (QS._○ᴹ_ (RG.tensor₊-cong (QS.⟺ᴹ (R.repack-unpack f)) (QS.⟺ᴹ (R.repack-unpack g)))
        (QS._○ᴹ_ (QS.⟺ᴹ (repack-tensor 0ℓ (R.unpack f) (R.unpack g)))
          (R.repack-resp (RG.tensorₚ-project (R.unpack f) (R.unpack g))))))
