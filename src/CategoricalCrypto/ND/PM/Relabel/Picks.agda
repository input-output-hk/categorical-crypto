{-# OPTIONS --safe --without-K #-}

open import Data.List.Base using (List; _++_)
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.ND.Relabel
open import CategoricalCrypto.ND.SSP.Choice using (Cᴵ⟦_⟧; join; split)
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Iface.Payload

module CategoricalCrypto.ND.PM.Relabel.Picks where

private variable S⃗ T⃗ U⃗ : List Set

private
  join-unpack : (S⃗ T⃗ : List Set) (p : Payload (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗ ⟧))
               → joinPick S⃗ T⃗ (unpack {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} p) ≡ mapᴾ (join S⃗ T⃗) p
  join-unpack S⃗ T⃗ p = trans (joinPick-payload S⃗ T⃗ _) (cong (mapᴾ (join S⃗ T⃗)) (pack-unpack p))

assoc-picks : (S⃗ T⃗ U⃗ : List Set) (p : Pick (S⃗ ++ (T⃗ ++ U⃗)))
             → mapᴾ (assocᴵ S⃗ T⃗ U⃗) p
               ≡ joinPick (S⃗ ++ T⃗) U⃗ (Sum.map (joinPick S⃗ T⃗) id
                   (Sum.assocˡ (Sum.map id (splitPick T⃗ U⃗) (splitPick S⃗ (T⃗ ++ U⃗) p))))
assoc-picks S⃗ T⃗ U⃗ p =
  trans (cong (mapᴾ (join (S⃗ ++ T⃗) U⃗)) (left-join p₂))
  (trans (cong finish (unpack-α⁻¹ {A} {B} {D} p₁))
  (trans (cong (finish ∘ Sum.assocˡ) (right-split p₀))
         (sym (joinPick-payload (S⃗ ++ T⃗) U⃗ _))))
  where
  A = Cᴵ⟦ S⃗ ⟧
  B = Cᴵ⟦ T⃗ ⟧
  D = Cᴵ⟦ U⃗ ⟧
  p₀ = mapᴾ (split S⃗ (T⃗ ++ U⃗)) p
  p₁ = mapᴾ (idᴵ {A} ⊗ᴵᴵ split T⃗ U⃗) p₀
  p₂ = mapᴾ (αᴵ⁻¹ {A} {B} {D}) p₁
  finish = mapᴾ (join (S⃗ ++ T⃗) U⃗) ∘ pack {Cᴵ⟦ S⃗ ++ T⃗ ⟧} {D} ∘ Sum.map (joinPick S⃗ T⃗) id

  left-join : (x : Payload ((A ⊗ᴵ B) ⊗ᴵ D))
              → mapᴾ (join S⃗ T⃗ ⊗ᴵᴵ idᴵ {D}) x
                ≡ pack {Cᴵ⟦ S⃗ ++ T⃗ ⟧} {D}
                    (Sum.map (joinPick S⃗ T⃗) id (Sum.map (unpack {A} {B}) id (unpack {A ⊗ᴵ B} {D} x)))
  left-join (inj₁ c , q) = cong (λ r → pack {Cᴵ⟦ S⃗ ++ T⃗ ⟧} {D} (inj₁ r)) (sym (join-unpack S⃗ T⃗ (c , q)))
  left-join (inj₂ _ , _) = refl

  right-split : (x : Payload (A ⊗ᴵ Cᴵ⟦ T⃗ ++ U⃗ ⟧))
                → Sum.map id (unpack {B} {D}) (unpack {A} {B ⊗ᴵ D} (mapᴾ (idᴵ {A} ⊗ᴵᴵ split T⃗ U⃗) x))
                  ≡ Sum.map id (splitPick T⃗ U⃗) (unpack {A} {Cᴵ⟦ T⃗ ++ U⃗ ⟧} x)
  right-split (inj₁ _ , _) = refl
  right-split (inj₂ _ , _) = refl

assoc⁻¹-picks : (S⃗ T⃗ U⃗ : List Set) (p : Pick ((S⃗ ++ T⃗) ++ U⃗))
               → mapᴾ (assocᴵ⁻¹ S⃗ T⃗ U⃗) p
                 ≡ joinPick S⃗ (T⃗ ++ U⃗) (Sum.map id (joinPick T⃗ U⃗)
                     (Sum.assocʳ (Sum.map (splitPick S⃗ T⃗) id (splitPick (S⃗ ++ T⃗) U⃗ p))))
assoc⁻¹-picks S⃗ T⃗ U⃗ p =
  trans (cong (mapᴾ (join S⃗ (T⃗ ++ U⃗))) (right-join p₂))
  (trans (cong finish (unpack-α {A} {B} {D} p₁))
  (trans (cong (finish ∘ Sum.assocʳ) (left-split p₀))
         (sym (joinPick-payload S⃗ (T⃗ ++ U⃗) _))))
  where
  A = Cᴵ⟦ S⃗ ⟧
  B = Cᴵ⟦ T⃗ ⟧
  D = Cᴵ⟦ U⃗ ⟧
  p₀ = mapᴾ (split (S⃗ ++ T⃗) U⃗) p
  p₁ = mapᴾ (split S⃗ T⃗ ⊗ᴵᴵ idᴵ {D}) p₀
  p₂ = mapᴾ (αᴵ {A} {B} {D}) p₁
  finish = mapᴾ (join S⃗ (T⃗ ++ U⃗)) ∘ pack {A} {Cᴵ⟦ T⃗ ++ U⃗ ⟧} ∘ Sum.map id (joinPick T⃗ U⃗)

  right-join : (x : Payload (A ⊗ᴵ (B ⊗ᴵ D)))
               → mapᴾ (idᴵ {A} ⊗ᴵᴵ join T⃗ U⃗) x
                 ≡ pack {A} {Cᴵ⟦ T⃗ ++ U⃗ ⟧}
                     (Sum.map id (joinPick T⃗ U⃗) (Sum.map id (unpack {B} {D}) (unpack {A} {B ⊗ᴵ D} x)))
  right-join (inj₁ _ , _) = refl
  right-join (inj₂ c , q) = cong (λ r → pack {A} {Cᴵ⟦ T⃗ ++ U⃗ ⟧} (inj₂ r)) (sym (join-unpack T⃗ U⃗ (c , q)))

  left-split : (x : Payload (Cᴵ⟦ S⃗ ++ T⃗ ⟧ ⊗ᴵ D))
               → Sum.map (unpack {A} {B}) id (unpack {A ⊗ᴵ B} {D} (mapᴾ (split S⃗ T⃗ ⊗ᴵᴵ idᴵ {D}) x))
                 ≡ Sum.map (splitPick S⃗ T⃗) id (unpack {Cᴵ⟦ S⃗ ++ T⃗ ⟧} {D} x)
  left-split (inj₁ _ , _) = refl
  left-split (inj₂ _ , _) = refl
