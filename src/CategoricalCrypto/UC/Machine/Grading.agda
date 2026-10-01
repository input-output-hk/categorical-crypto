{-# OPTIONS --safe --without-K --guardedness #-}

-- The machine model's graded subcategory: `UC.QueryBound`'s certificate at a
-- positive rate, `gradingᴹ`.
--
-- Certificates are about the pinned relays; `UC.Machine.Dictionary`'s zigzags
-- carry them to the grading's fields.  At a positive rate the relays' `⊔ 1`
-- guard is `value-positive`.
--
-- The proofs stay in `Iface` vocabulary, where elaboration is cheap.  Their
-- object-indexed wrappers cross through `QBᴳ` only at explicit `⟦_⟧ᴵ` images;
-- opacity then keeps both the predicate and `_⊗₁ᴳ_` nominal while the record
-- checks its dependent fields (at the `Iface` spelling each field re-indexes
-- its objects and pays one `Proc` inversion, measured at >250 s together).

open import Categories.Category
open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Sum.Base using () renaming (assocˡ to ⊎assocˡ; assocʳ to ⊎assocʳ)
open import Level
open import Relation.Binary.PropositionalEquality using (cong₂)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Compose.Laws
open import CategoricalCrypto.UC.QueryBound.Object

module CategoricalCrypto.UC.Machine.Grading where

private
  module Rates = SymmetricMonoidalCategory Rates
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒢 = Category (𝒢ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

-- The two actions on the pinned relays, the spelling a context is built in
-- (`UC.Machine.StateEvent.Lift.stateLift`), and read back at the tensor.
qb-T₁ᴵ : (Y A B : Iface) {c : ℕ} (f : Proc A B) → QB c f → QB (c ℕ.⊔ 1) (T₁ᴵ Y f)
qb-T₁ᴵ Y A B f (N , cert , e) = T₁ᴵ Y N , qbᵢ-T₁ Y A B N cert , T₁-resp-≈ e

qb-subᴵ : (X Y A : Iface) {c : ℕ} (s : Proc X Y) → QB c s → QB (c ℕ.⊔ 1) (subᴵ {A = A} s)
qb-subᴵ X Y A s (N , cert , e) = subᴵ N , qbᵢ-sub X Y A N cert , sub-resp-≈ e

qb-T₁ᴳ : (Y A B : Iface) {c : ℕ} (f : Proc A B)
       → QB c f
       → QB (c ℕ.⊔ 1) (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f)
qb-T₁ᴳ Y A B f q = qb-resp-≈ (T₁-⊗₁ {Y} {A} {B} f) (qb-T₁ᴵ Y A B f q)

qb-subᴳ : (X Y A : Iface) {c : ℕ} (s : Proc X Y)
        → QB c s
        → QB (c ℕ.⊔ 1) (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ A ⟧ᴵ} s (𝒫.id {A}))
qb-subᴳ X Y A s q = qb-resp-≈ (sub-⊗₁ {X} {Y} {A} s) (qb-subᴵ X Y A s q)

qb-a⇒ᴳ : (X Y A : Iface) → QB 1 (𝔾.associator.from {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
qb-a⇒ᴳ X Y A =
  qb-resp-≈ (a⇒-α⇒ {X} {Y} {A})
    (qb-wire {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)} ⊎assocʳ ⊎assocˡ)

opaque
  qb-T₁ᴳ-object : (Y A B : 𝒢.Obj) {c : ℕ} (f : 𝒢ₚ 0ℓ [ A , B ])
                → QBᴳ A B c f
                → QBᴳ (Y 𝔾.⊗₀ A) (Y 𝔾.⊗₀ B) (c ℕ.⊔ 1) (𝔾._⊗₁_ (𝒢.id {Y}) f)
  qb-T₁ᴳ-object Y A B {c} f q =
    qb-to-image (retᴵ Y ⊗ᴵ retᴵ A) (retᴵ Y ⊗ᴵ retᴵ B)
      (qb-T₁ᴳ (retᴵ Y) (retᴵ A) (retᴵ B) {c} f (qb-from-image (retᴵ A) (retᴵ B) q))

  qb-subᴳ-object : (X Y A : 𝒢.Obj) {c : ℕ} (s : 𝒢ₚ 0ℓ [ X , Y ])
                 → QBᴳ X Y c s
                 → QBᴳ (X 𝔾.⊗₀ A) (Y 𝔾.⊗₀ A) (c ℕ.⊔ 1) (𝔾._⊗₁_ s (𝒢.id {A}))
  qb-subᴳ-object X Y A {c} s q =
    qb-to-image (retᴵ X ⊗ᴵ retᴵ A) (retᴵ Y ⊗ᴵ retᴵ A)
      (qb-subᴳ (retᴵ X) (retᴵ Y) (retᴵ A) {c} s (qb-from-image (retᴵ X) (retᴵ Y) q))

  qb-a⇐ᴳ-object : (X Y A : 𝒢.Obj)
                → QBᴳ (X 𝔾.⊗₀ (Y 𝔾.⊗₀ A)) ((X 𝔾.⊗₀ Y) 𝔾.⊗₀ A) 1
                      (𝔾.associator.to {X} {Y} {A})
  qb-a⇐ᴳ-object X Y A =
    qb-to-image (retᴵ X ⊗ᴵ (retᴵ Y ⊗ᴵ retᴵ A)) ((retᴵ X ⊗ᴵ retᴵ Y) ⊗ᴵ retᴵ A)
      (qb-resp-≈ (a⇐-α⇐ {retᴵ X} {retᴵ Y} {retᴵ A})
        (qb-wire {retᴵ X ⊗ᴵ (retᴵ Y ⊗ᴵ retᴵ A)} {(retᴵ X ⊗ᴵ retᴵ Y) ⊗ᴵ retᴵ A} ⊎assocˡ ⊎assocʳ))

  qb-a⇒ᴳ-object : (X Y A : 𝒢.Obj)
                → QBᴳ ((X 𝔾.⊗₀ Y) 𝔾.⊗₀ A) (X 𝔾.⊗₀ (Y 𝔾.⊗₀ A)) 1
                      (𝔾.associator.from {X} {Y} {A})
  qb-a⇒ᴳ-object X Y A =
    qb-to-image ((retᴵ X ⊗ᴵ retᴵ Y) ⊗ᴵ retᴵ A) (retᴵ X ⊗ᴵ (retᴵ Y ⊗ᴵ retᴵ A))
      (qb-a⇒ᴳ (retᴵ X) (retᴵ Y) (retᴵ A))

  qb-λ⇒ᴳ-object : (A : 𝒢.Obj) → QBᴳ (𝔾.unit 𝔾.⊗₀ A) A 1 (𝔾.unitorˡ.from {A})
  qb-λ⇒ᴳ-object A =
    qb-to-image (𝟭ᴵ ⊗ᴵ retᴵ A) (retᴵ A)
      (qb-resp-≈ (λ⇒-λᴳ {retᴵ A}) (qb-wire {𝟭ᴵ ⊗ᴵ retᴵ A} {retᴵ A} drop⇒ˡ inj₂))

  qb-λ⇐ᴳ-object : (A : 𝒢.Obj) → QBᴳ A (𝔾.unit 𝔾.⊗₀ A) 1 (𝔾.unitorˡ.to {A})
  qb-λ⇐ᴳ-object A =
    qb-to-image (retᴵ A) (𝟭ᴵ ⊗ᴵ retᴵ A)
      (qb-resp-≈ (λ⇐-λᴳ {retᴵ A}) (qb-wire {retᴵ A} {𝟭ᴵ ⊗ᴵ retᴵ A} inj₂ drop⇒ˡ))

  qb-ρ⇒ᴳ-object : (A : 𝒢.Obj) → QBᴳ (A 𝔾.⊗₀ 𝔾.unit) A 1 (𝔾.unitorʳ.from {A})
  qb-ρ⇒ᴳ-object A =
    qb-to-image (retᴵ A ⊗ᴵ 𝟭ᴵ) (retᴵ A)
      (qb-resp-≈ (ρ⇒-ρᴳ {retᴵ A}) (qb-wire {retᴵ A ⊗ᴵ 𝟭ᴵ} {retᴵ A} drop⇒ʳ inj₁))

  qb-ρ⇐ᴳ-object : (A : 𝒢.Obj) → QBᴳ A (A 𝔾.⊗₀ 𝔾.unit) 1 (𝔾.unitorʳ.to {A})
  qb-ρ⇐ᴳ-object A =
    qb-to-image (retᴵ A) (retᴵ A ⊗ᴵ 𝟭ᴵ)
      (qb-resp-≈ (ρ⇐-ρᴳ {retᴵ A}) (qb-wire {retᴵ A} {retᴵ A ⊗ᴵ 𝟭ᴵ} inj₁ drop⇒ʳ))

  qb-⊗ᴳ-object : (A B A′ B′ : 𝒢.Obj) {c c′ : ℕ} (f : 𝒢ₚ 0ℓ [ A , B ]) (g : 𝒢ₚ 0ℓ [ A′ , B′ ])
               → QBᴳ A B c f → QBᴳ A′ B′ c′ g
               → QBᴳ (A 𝔾.⊗₀ A′) (B 𝔾.⊗₀ B′) ((c ℕ.⊔ 1) ℕ.* (c′ ℕ.⊔ 1)) (f 𝔾.⊗₁ g)
  qb-⊗ᴳ-object A B A′ B′ f g qf qg =
    qb-resp-≈ᴳ (A 𝔾.⊗₀ A′) (B 𝔾.⊗₀ B′) (𝔾.Equiv.sym (MonR.serialize₁₂ 𝔾.monoidal))
      (qb-∘ᴳ (A 𝔾.⊗₀ A′) (A 𝔾.⊗₀ B′) (B 𝔾.⊗₀ B′) (f 𝔾.⊗₁ 𝒢.id) (𝒢.id 𝔾.⊗₁ g)
        (qb-subᴳ-object A B B′ f qf) (qb-T₁ᴳ-object A A′ B′ g qg))

gradingᴹ : GradedSubCat Rates.monoidalCategory (𝒢ₚᴹ 0ℓ) (suc 0ℓ)
gradingᴹ = record
  { Pred      = λ r {A} {B} → QBᴳ A B (value r)
  ; pred-resp = λ {_} {A} {B} → qb-resp-≈ᴳ A B
  ; pred-sub  = λ {_} {_} {A} {B} → qb-monoᴳ A B
  ; pred-id   = λ {A} → qb-idᴳ A
  ; pred-∘    = λ {r} {s} {A} {B} {D} {g} {f} qg qf →
      qb-monoᴳ A D (≤-reflexive (*-comm (value s) (value r))) (qb-∘ᴳ A B D g f qg qf)
  ; pred-⊗    = λ {r} {s} {A} {B} {A′} {B′} {f} {g} qf qg →
      qb-monoᴳ (A 𝔾.⊗₀ A′) (B 𝔾.⊗₀ B′)
        (≤-reflexive (cong₂ ℕ._*_ (value-positive r) (value-positive s)))
        (qb-⊗ᴳ-object A B A′ B′ f g qf qg)
  ; pred-α⇒   = λ {X} {Y} {A} → qb-a⇒ᴳ-object X Y A
  ; pred-α⇐   = λ {X} {Y} {A} → qb-a⇐ᴳ-object X Y A
  ; pred-λ⇒   = λ {A} → qb-λ⇒ᴳ-object A
  ; pred-λ⇐   = λ {A} → qb-λ⇐ᴳ-object A
  ; pred-ρ⇒   = λ {A} → qb-ρ⇒ᴳ-object A
  ; pred-ρ⇐   = λ {A} → qb-ρ⇐ᴳ-object A
  }
