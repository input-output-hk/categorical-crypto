{-# OPTIONS --safe --without-K #-}

-- Container maps act covariantly on queries, including their channel tags.

open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Iface

module CategoricalCrypto.SSP.Iface.Payload where

private variable A B C D : Iface

Payload : Iface → Set
Payload A = Σ (Ch A) (Q A)

mapᴾ : A ⇒ᴵ B → Payload A → Payload B
mapᴾ m (c , p) = ch m c , qu m p

pack : Payload A ⊎ Payload B → Payload (A ⊗ᴵ B)
pack (inj₁ (c , p)) = inj₁ c , p
pack (inj₂ (c , p)) = inj₂ c , p

unpack : Payload (A ⊗ᴵ B) → Payload A ⊎ Payload B
unpack (inj₁ c , p) = inj₁ (c , p)
unpack (inj₂ c , p) = inj₂ (c , p)

pack-unpack : (p : Payload (A ⊗ᴵ B)) → pack {A} {B} (unpack {A} {B} p) ≡ p
pack-unpack (inj₁ _ , _) = refl
pack-unpack (inj₂ _ , _) = refl

unpack-pack : (p : Payload A ⊎ Payload B) → unpack {A} {B} (pack {A} {B} p) ≡ p
unpack-pack (inj₁ _) = refl
unpack-pack (inj₂ _) = refl

mapᴾ-∘ : (m : B ⇒ᴵ C) (n : A ⇒ᴵ B) (p : Payload A) → mapᴾ (m ∘ᴵ n) p ≡ mapᴾ m (mapᴾ n p)
mapᴾ-∘ _ _ _ = refl

mapᴾ-pack : (m : A ⇒ᴵ B) (n : C ⇒ᴵ D) (p : Payload A ⊎ Payload C)
           → mapᴾ (m ⊗ᴵᴵ n) (pack {A} {C} p) ≡ pack {B} {D} (Sum.map (mapᴾ m) (mapᴾ n) p)
mapᴾ-pack _ _ (inj₁ _) = refl
mapᴾ-pack _ _ (inj₂ _) = refl

unpack-mapᴾ : (m : A ⇒ᴵ B) (n : C ⇒ᴵ D) (p : Payload (A ⊗ᴵ C))
             → unpack {B} {D} (mapᴾ (m ⊗ᴵᴵ n) p) ≡ Sum.map (mapᴾ m) (mapᴾ n) (unpack {A} {C} p)
unpack-mapᴾ _ _ (inj₁ _ , _) = refl
unpack-mapᴾ _ _ (inj₂ _ , _) = refl

unpack-α⁻¹ : (p : Payload (A ⊗ᴵ (B ⊗ᴵ C)))
             → Sum.map (unpack {A} {B}) id (unpack {A ⊗ᴵ B} {C} (mapᴾ (αᴵ⁻¹ {A} {B} {C}) p))
               ≡ Sum.assocˡ (Sum.map id (unpack {B} {C}) (unpack {A} {B ⊗ᴵ C} p))
unpack-α⁻¹ (inj₁ _ , _) = refl
unpack-α⁻¹ (inj₂ (inj₁ _) , _) = refl
unpack-α⁻¹ (inj₂ (inj₂ _) , _) = refl

unpack-α : (p : Payload ((A ⊗ᴵ B) ⊗ᴵ C))
           → Sum.map id (unpack {B} {C}) (unpack {A} {B ⊗ᴵ C} (mapᴾ (αᴵ {A} {B} {C}) p))
             ≡ Sum.assocʳ (Sum.map (unpack {A} {B}) id (unpack {A ⊗ᴵ B} {C} p))
unpack-α (inj₁ (inj₁ _) , _) = refl
unpack-α (inj₁ (inj₂ _) , _) = refl
unpack-α (inj₂ _ , _) = refl
