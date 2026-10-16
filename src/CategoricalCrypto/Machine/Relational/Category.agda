{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Category where

open import Categories.Category
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Category as Old
import CategoricalCrypto.Machine.Iso as Iso
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Isomorphism
open import CategoricalCrypto.Machine.Relational.Wiring
import CategoricalCrypto.Machine.Reindex.Post as Post

private variable A B C D : Channel

opaque

  assoc : {f : Initialized A B} {g : Initialized B C} {h : Initialized C D}
        → ((h ∘ g) ∘ f) ≈ᴿ (h ∘ (g ∘ f))
  assoc = lift-iso Iso.∘-assoc-≅ᴹ
    (λ { (p , q , r) → (p , q) , r })
    (λ { ((p , q) , r) → p , q , r })

opaque
  unfolding Post.∘-identityˡ-Post Post.∘-identityʳ-Post

  identityˡ : {f : Initialized A B} → (id ∘ f) ≈ᴿ f
  identityˡ = lift-iso Old.∘-identityˡ-≅ᴹ proj₁ (λ p → p , refl)

  identityʳ : {f : Initialized A B} → (f ∘ id) ≈ᴿ f
  identityʳ = lift-iso Old.∘-identityʳ-≅ᴹ proj₂ (λ p → refl , p)

𝓡 : Category _ _ _
𝓡 = record
  { Obj = Channel ; _⇒_ = Initialized ; _≈_ = _≈ᴿ_
  ; id = id ; _∘_ = _∘_
  ; assoc = assoc ; sym-assoc = ≈ᴿ-sym assoc
  ; identityˡ = identityˡ ; identityʳ = identityʳ ; identity² = identityˡ
  ; equiv = record { refl = ≈ᴿ-refl ; sym = ≈ᴿ-sym ; trans = ≈ᴿ-trans }
  ; ∘-resp-≈ = ∘-cong
  }
