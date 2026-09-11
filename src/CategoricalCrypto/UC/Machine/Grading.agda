{-# OPTIONS --safe --without-K --guardedness #-}

-- Where the pinned relays meet the derived grading.
--
-- The grading itself is `UC.Machine.gradingᴹ` and comes for free.  What is
-- left is the resource layer: a `UC.QueryBound` certificate is about the pinned
-- relay (`T₁ᴵ`/`subᴵ`/`a⇒ᴵ`/`a⇐ᴵ`) or a bare wire, the grading's action is
-- `_⊗₁_` with an identity and the 𝒢-associator and 𝒢-unitors, and
-- `UC.Machine.Dictionary`'s zigzags carry one to the other through
-- `qb-resp-≈`.  Those eight are the whole content.
--
-- The proofs stay in `Iface` vocabulary, where elaboration is cheap.  Their
-- object-indexed wrappers cross through `QBᴳ` only at explicit `⟦_⟧ᴵ` images;
-- opacity then keeps both the predicate and `_⊗₁ᴳ_` nominal while `Budget`
-- checks its dependent fields.

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚ; 𝒢ₚᴹ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Core using (Grading)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Object using (QBᴳ; qb-from-image; qb-to-image)

module CategoricalCrypto.UC.Machine.Grading where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒢 = Category (𝒢ₚ 0ℓ)
  module G = Grading gradingᴹ
  module 𝒫 = Category 𝒫ᴵ

qb-T₁ᴳ : (Y A B : Iface) {c : ℕ} (f : Proc A B)
       → QB c f
       → QB (c ℕ.⊔ 1) (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f)
qb-T₁ᴳ Y A B f (N , cert , e) =
  T₁ᴵ Y N , qbᵢ-T₁ Y A B N cert ,
    𝒫.Equiv.trans (T₁-⊗₁ {Y} {A} {B} N)
      (𝔾.⊗.F-resp-≈ {⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Y ⟧ᴵ , ⟦ B ⟧ᴵ}
        {𝒫.id {Y} , N} {𝒫.id {Y} , f} (𝔾.Equiv.refl {x = 𝒫.id {Y}} , e))

qb-subᴳ : (X Y A : Iface) {c : ℕ} (s : Proc X Y)
        → QB c s
        → QB (c ℕ.⊔ 1) (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ A ⟧ᴵ} s (𝒫.id {A}))
qb-subᴳ X Y A s (N , cert , e) =
  subᴵ N , qbᵢ-sub X Y A N cert ,
    𝒫.Equiv.trans (sub-⊗₁ {X} {Y} {A} N)
      (𝔾.⊗.F-resp-≈ {⟦ X ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ}
        {N , 𝒫.id {A}} {s , 𝒫.id {A}} (e , 𝔾.Equiv.refl {x = 𝒫.id {A}}))

qb-a⇒ᴳ : (X Y A : Iface) → QB 1 (𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
qb-a⇒ᴳ X Y A =
  qb-resp-≈ (a⇒-α⇐ {X} {Y} {A})
    (certified⇒QB (qbᵢ-wire {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} ⊎assocˡ ⊎assocʳ))

qb-a⇐ᴳ : (X Y A : Iface) → QB 1 (𝔾.associator.from {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
qb-a⇐ᴳ X Y A =
  qb-resp-≈ (a⇐-α⇒ {X} {Y} {A})
    (certified⇒QB (qbᵢ-wire {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)} ⊎assocʳ ⊎assocˡ))

qb-λ⇒ᴳ : (A : Iface) → QB 1 (𝔾.unitorˡ.from {⟦ A ⟧ᴵ})
qb-λ⇒ᴳ A =
  qb-resp-≈ (λ⇒-λᴳ {A})
    (certified⇒QB (qbᵢ-wire {𝟭ᴵ ⊗ᴵ A} {A} drop⇒ˡ inj₂))

qb-λ⇐ᴳ : (A : Iface) → QB 1 (𝔾.unitorˡ.to {⟦ A ⟧ᴵ})
qb-λ⇐ᴳ A =
  qb-resp-≈ (λ⇐-λᴳ {A})
    (certified⇒QB (qbᵢ-wire {A} {𝟭ᴵ ⊗ᴵ A} inj₂ drop⇒ˡ))

qb-ρ⇒ᴳ : (A : Iface) → QB 1 (𝔾.unitorʳ.from {⟦ A ⟧ᴵ})
qb-ρ⇒ᴳ A =
  qb-resp-≈ (ρ⇒-ρᴳ {A})
    (certified⇒QB (qbᵢ-wire {A ⊗ᴵ 𝟭ᴵ} {A} drop⇒ʳ inj₁))

qb-ρ⇐ᴳ : (A : Iface) → QB 1 (𝔾.unitorʳ.to {⟦ A ⟧ᴵ})
qb-ρ⇐ᴳ A =
  qb-resp-≈ (ρ⇐-ρᴳ {A})
    (certified⇒QB (qbᵢ-wire {A} {A ⊗ᴵ 𝟭ᴵ} inj₁ drop⇒ʳ))

opaque
  qb-T₁ᴳ-object : (Y A B : 𝒢.Obj) {c : ℕ} (f : 𝒢ₚ 0ℓ [ A , B ])
                → QBᴳ A B c f → QBᴳ (Y G.⊛ A) (Y G.⊛ B) (c ℕ.⊔ 1) (G.T₁ Y f)
  qb-T₁ᴳ-object (Y⁺ , Y⁻) (A⁺ , A⁻) (B⁺ , B⁻) {c} f q =
    qb-to-image (Y ⊗ᴵ A) (Y ⊗ᴵ B)
      (qb-T₁ᴳ Y A B {c} f (qb-from-image A B q))
    where
    Y : Iface
    Y = retᴵ (Y⁺ , Y⁻)
    A : Iface
    A = retᴵ (A⁺ , A⁻)
    B : Iface
    B = retᴵ (B⁺ , B⁻)

  qb-subᴳ-object : (X Y A : 𝒢.Obj) {c : ℕ} (s : 𝒢ₚ 0ℓ [ X , Y ])
                 → QBᴳ X Y c s → QBᴳ (X G.⊛ A) (Y G.⊛ A) (c ℕ.⊔ 1) (G.sub {A = A} s)
  qb-subᴳ-object (X⁺ , X⁻) (Y⁺ , Y⁻) (A⁺ , A⁻) {c} s q =
    qb-to-image (X ⊗ᴵ A) (Y ⊗ᴵ A)
      (qb-subᴳ X Y A {c} s (qb-from-image X Y q))
    where
    X : Iface
    X = retᴵ (X⁺ , X⁻)
    Y : Iface
    Y = retᴵ (Y⁺ , Y⁻)
    A : Iface
    A = retᴵ (A⁺ , A⁻)

  qb-a⇒ᴳ-object : (X Y A : 𝒢.Obj)
                → QBᴳ (X G.⊛ (Y G.⊛ A)) ((X G.⊛ Y) G.⊛ A) 1 (G.a⇒ {X} {Y} {A})
  qb-a⇒ᴳ-object (X⁺ , X⁻) (Y⁺ , Y⁻) (A⁺ , A⁻) =
    qb-to-image (X ⊗ᴵ (Y ⊗ᴵ A)) ((X ⊗ᴵ Y) ⊗ᴵ A) (qb-a⇒ᴳ X Y A)
    where
    X : Iface
    X = retᴵ (X⁺ , X⁻)
    Y : Iface
    Y = retᴵ (Y⁺ , Y⁻)
    A : Iface
    A = retᴵ (A⁺ , A⁻)

  qb-a⇐ᴳ-object : (X Y A : 𝒢.Obj)
                → QBᴳ ((X G.⊛ Y) G.⊛ A) (X G.⊛ (Y G.⊛ A)) 1 (G.a⇐ {X} {Y} {A})
  qb-a⇐ᴳ-object (X⁺ , X⁻) (Y⁺ , Y⁻) (A⁺ , A⁻) =
    qb-to-image ((X ⊗ᴵ Y) ⊗ᴵ A) (X ⊗ᴵ (Y ⊗ᴵ A)) (qb-a⇐ᴳ X Y A)
    where
    X : Iface
    X = retᴵ (X⁺ , X⁻)
    Y : Iface
    Y = retᴵ (Y⁺ , Y⁻)
    A : Iface
    A = retᴵ (A⁺ , A⁻)

  qb-λ⇒ᴳ-object : (A : 𝒢.Obj) → QBᴳ (G.𝟭 G.⊛ A) A 1 (G.λ⇒ {A})
  qb-λ⇒ᴳ-object (A⁺ , A⁻) = qb-to-image (𝟭ᴵ ⊗ᴵ A) A (qb-λ⇒ᴳ A)
    where
    A : Iface
    A = retᴵ (A⁺ , A⁻)

  qb-λ⇐ᴳ-object : (A : 𝒢.Obj) → QBᴳ A (G.𝟭 G.⊛ A) 1 (G.λ⇐ {A})
  qb-λ⇐ᴳ-object (A⁺ , A⁻) = qb-to-image A (𝟭ᴵ ⊗ᴵ A) (qb-λ⇐ᴳ A)
    where
    A : Iface
    A = retᴵ (A⁺ , A⁻)

  qb-ρ⇒ᴳ-object : (A : 𝒢.Obj) → QBᴳ (A G.⊛ G.𝟭) A 1 (G.ρ⇒ {A})
  qb-ρ⇒ᴳ-object (A⁺ , A⁻) = qb-to-image (A ⊗ᴵ 𝟭ᴵ) A (qb-ρ⇒ᴳ A)
    where
    A : Iface
    A = retᴵ (A⁺ , A⁻)

  qb-ρ⇐ᴳ-object : (A : 𝒢.Obj) → QBᴳ A (A G.⊛ G.𝟭) 1 (G.ρ⇐ {A})
  qb-ρ⇐ᴳ-object (A⁺ , A⁻) = qb-to-image A (A ⊗ᴵ 𝟭ᴵ) (qb-ρ⇐ᴳ A)
    where
    A : Iface
    A = retᴵ (A⁺ , A⁻)
