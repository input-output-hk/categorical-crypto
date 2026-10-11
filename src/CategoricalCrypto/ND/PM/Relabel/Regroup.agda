{-# OPTIONS --safe --without-K --guardedness #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle

open import Data.Empty.Polymorphic as Empty using ()
open import Data.List.Base using (List; []; _++_)
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
import CategoricalCrypto.ND.A as A
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.PM.Factor.Read
open import CategoricalCrypto.ND.PM.Read
open import CategoricalCrypto.ND.PM.Relabel.Picks
open import CategoricalCrypto.ND.PM.Relabel.Wire
open import CategoricalCrypto.ND.Relabel
open import CategoricalCrypto.ND.SSP.Choice using (Cᴵ⟦_⟧; join; split)
import CategoricalCrypto.SSP.Iface as SSP
open import CategoricalCrypto.SSP.Iface.Payload
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Wire.Algebra
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.ND.PM.Relabel.Regroup where

private
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module P = Category 𝒫ᴵ
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module N = A 𝔾ˢ C
  variable S⃗ T⃗ U⃗ : List Set

open G.HomReasoning

private
  compose : (A B D : Iface) → Proc B D → Proc A B → Proc A D
  compose A B D = P._∘_ {A} {B} {D}

  unit⇒ᴾ : (S⃗ : List Set) → Proc (Cᶠ (S⃗ ++ [])) (Cᶠ S⃗)
  unit⇒ᴾ S⃗ = compose (Cᶠ (S⃗ ++ [])) (Cᶠ S⃗ ⊗ᴵ 𝟭ᴵ) (Cᶠ S⃗) (wireᴹ drop⇒ʳ inj₁)
    (compose (Cᶠ (S⃗ ++ [])) (Cᶠ S⃗ ⊗ᴵ Cᶠ []) (Cᶠ S⃗ ⊗ᴵ 𝟭ᴵ) (T₁ᴵ (Cᶠ S⃗) nilᶠ⁻¹) (splitᶠ S⃗ []))

  unit⇐ᴾ : (S⃗ : List Set) → Proc (Cᶠ S⃗) (Cᶠ (S⃗ ++ []))
  unit⇐ᴾ S⃗ = compose (Cᶠ S⃗) (Cᶠ S⃗ ⊗ᴵ Cᶠ []) (Cᶠ (S⃗ ++ [])) (joinᶠ S⃗ [])
    (compose (Cᶠ S⃗) (Cᶠ S⃗ ⊗ᴵ 𝟭ᴵ) (Cᶠ S⃗ ⊗ᴵ Cᶠ []) (T₁ᴵ (Cᶠ S⃗) nilᶠ) (wireᴹ inj₁ drop⇒ʳ))

  unit⇒-wire : (S⃗ : List Set) → P._≈_ {Cᶠ (S⃗ ++ [])} {Cᶠ S⃗}
    (unit⇒ᴾ S⃗) (wireᴹ (SSP.ch (unitʳᴵ⁻¹ S⃗)) (mapᴾ (unitʳᴵ S⃗)))
  unit⇒-wire S⃗ = ∘-wire {Cᶠ (S⃗ ++ [])} {Cᶠ S⃗ ⊗ᴵ 𝟭ᴵ} {Cᶠ S⃗} S.reflᴹ
    (∘-wire {Cᶠ (S⃗ ++ [])} {Cᶠ S⃗ ⊗ᴵ Cᶠ []} {Cᶠ S⃗ ⊗ᴵ 𝟭ᴵ}
      (T₁-wire {Cᶠ []} {𝟭ᴵ} {Cᶠ S⃗} _ _) S.reflᴹ)
    S.○ᴹ wire-cong (λ c → up₀ (SSP.ch (split S⃗ []) c)) (λ p → sym (joinPick-payload S⃗ [] (inj₁ p)))
    where
    up₀ : (x : SSP.Ch Cᴵ⟦ S⃗ ⟧ ⊎ SSP.Ch SSP.unitᴵ)
         → drop⇒ʳ (Sum.map id (λ ()) x) ≡ SSP.ch (SSP.ρᴵ {Cᴵ⟦ S⃗ ⟧}) x
    up₀ (inj₁ _) = refl
    up₀ (inj₂ ())

  unit⇐-wire : (S⃗ : List Set) → P._≈_ {Cᶠ S⃗} {Cᶠ (S⃗ ++ [])}
    (unit⇐ᴾ S⃗) (wireᴹ (SSP.ch (unitʳᴵ S⃗)) (mapᴾ (unitʳᴵ⁻¹ S⃗)))
  unit⇐-wire S⃗ = ∘-wire {Cᶠ S⃗} {Cᶠ S⃗ ⊗ᴵ Cᶠ []} {Cᶠ (S⃗ ++ [])} S.reflᴹ
    (∘-wire {Cᶠ S⃗} {Cᶠ S⃗ ⊗ᴵ 𝟭ᴵ} {Cᶠ S⃗ ⊗ᴵ Cᶠ []} (T₁-wire {𝟭ᴵ} {Cᶠ []} {Cᶠ S⃗} _ _) S.reflᴹ)
    S.○ᴹ wire-cong (λ _ → refl) (λ p → down₀ (mapᴾ (split S⃗ []) p))
    where
    down₀ : (x : Payload (Cᴵ⟦ S⃗ ⟧ SSP.⊗ᴵ SSP.unitᴵ))
           → drop⇒ʳ (Sum.map id (λ { (() , _) }) (unpack {Cᴵ⟦ S⃗ ⟧} {SSP.unitᴵ} x)) ≡ mapᴾ (SSP.ρᴵ {Cᴵ⟦ S⃗ ⟧}) x
    down₀ (inj₁ _ , _) = refl
    down₀ (inj₂ () , _)

  assoc⇒ᴾ : (S⃗ T⃗ U⃗ : List Set) → Proc (Cᶠ ((S⃗ ++ T⃗) ++ U⃗)) (Cᶠ (S⃗ ++ (T⃗ ++ U⃗)))
  assoc⇒ᴾ S⃗ T⃗ U⃗ = compose L (Cᶠ S⃗ ⊗ᴵ Cᶠ (T⃗ ++ U⃗)) R (joinᶠ S⃗ (T⃗ ++ U⃗))
    (compose L (Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗)) (Cᶠ S⃗ ⊗ᴵ Cᶠ (T⃗ ++ U⃗)) (T₁ᴵ (Cᶠ S⃗) (joinᶠ T⃗ U⃗))
    (compose L ((Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ Cᶠ U⃗) (Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗)) a⇒ᴵ
    (compose L (Cᶠ (S⃗ ++ T⃗) ⊗ᴵ Cᶠ U⃗) ((Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ Cᶠ U⃗) (subᴵ (splitᶠ S⃗ T⃗)) (splitᶠ (S⃗ ++ T⃗) U⃗))))
    where L = Cᶠ ((S⃗ ++ T⃗) ++ U⃗)
          R = Cᶠ (S⃗ ++ (T⃗ ++ U⃗))

  assoc⇐ᴾ : (S⃗ T⃗ U⃗ : List Set) → Proc (Cᶠ (S⃗ ++ (T⃗ ++ U⃗))) (Cᶠ ((S⃗ ++ T⃗) ++ U⃗))
  assoc⇐ᴾ S⃗ T⃗ U⃗ = compose R (Cᶠ (S⃗ ++ T⃗) ⊗ᴵ Cᶠ U⃗) L (joinᶠ (S⃗ ++ T⃗) U⃗)
    (compose R ((Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ Cᶠ U⃗) (Cᶠ (S⃗ ++ T⃗) ⊗ᴵ Cᶠ U⃗) (subᴵ (joinᶠ S⃗ T⃗))
    (compose R (Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗)) ((Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ Cᶠ U⃗) a⇐ᴵ
    (compose R (Cᶠ S⃗ ⊗ᴵ Cᶠ (T⃗ ++ U⃗)) (Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗)) (T₁ᴵ (Cᶠ S⃗) (splitᶠ T⃗ U⃗)) (splitᶠ S⃗ (T⃗ ++ U⃗)))))
    where L = Cᶠ ((S⃗ ++ T⃗) ++ U⃗)
          R = Cᶠ (S⃗ ++ (T⃗ ++ U⃗))

  assoc⇒-wire : (S⃗ T⃗ U⃗ : List Set) → P._≈_ {Cᶠ ((S⃗ ++ T⃗) ++ U⃗)} {Cᶠ (S⃗ ++ (T⃗ ++ U⃗))}
    (assoc⇒ᴾ S⃗ T⃗ U⃗) (wireᴹ (SSP.ch (assocᴵ⁻¹ S⃗ T⃗ U⃗)) (mapᴾ (assocᴵ S⃗ T⃗ U⃗)))
  assoc⇒-wire S⃗ T⃗ U⃗ = ∘-wire {L} {Cᶠ S⃗ ⊗ᴵ Cᶠ (T⃗ ++ U⃗)} {R} S.reflᴹ
    (∘-wire {L} {Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗)} {Cᶠ S⃗ ⊗ᴵ Cᶠ (T⃗ ++ U⃗)}
      (T₁-wire {Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗} {Cᶠ (T⃗ ++ U⃗)} {Cᶠ S⃗} _ _)
      (∘-wire {L} {(Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ Cᶠ U⃗} {Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗)} S.reflᴹ
        (∘-wire {L} {Cᶠ (S⃗ ++ T⃗) ⊗ᴵ Cᶠ U⃗} {(Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ Cᶠ U⃗}
          (sub-wire {Cᶠ (S⃗ ++ T⃗)} {Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗} {Cᶠ U⃗} _ _) S.reflᴹ)))
    S.○ᴹ wire-cong (λ _ → refl) (λ p → sym (assoc-picks S⃗ T⃗ U⃗ p))
    where L = Cᶠ ((S⃗ ++ T⃗) ++ U⃗)
          R = Cᶠ (S⃗ ++ (T⃗ ++ U⃗))

  assoc⇐-wire : (S⃗ T⃗ U⃗ : List Set) → P._≈_ {Cᶠ (S⃗ ++ (T⃗ ++ U⃗))} {Cᶠ ((S⃗ ++ T⃗) ++ U⃗)}
    (assoc⇐ᴾ S⃗ T⃗ U⃗) (wireᴹ (SSP.ch (assocᴵ S⃗ T⃗ U⃗)) (mapᴾ (assocᴵ⁻¹ S⃗ T⃗ U⃗)))
  assoc⇐-wire S⃗ T⃗ U⃗ = ∘-wire {R} {Cᶠ (S⃗ ++ T⃗) ⊗ᴵ Cᶠ U⃗} {L} S.reflᴹ
    (∘-wire {R} {(Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ Cᶠ U⃗} {Cᶠ (S⃗ ++ T⃗) ⊗ᴵ Cᶠ U⃗}
      (sub-wire {Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗} {Cᶠ (S⃗ ++ T⃗)} {Cᶠ U⃗} _ _)
      (∘-wire {R} {Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗)} {(Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ Cᶠ U⃗} S.reflᴹ
        (∘-wire {R} {Cᶠ S⃗ ⊗ᴵ Cᶠ (T⃗ ++ U⃗)} {Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗)}
          (T₁-wire {Cᶠ (T⃗ ++ U⃗)} {Cᶠ T⃗ ⊗ᴵ Cᶠ U⃗} {Cᶠ S⃗} _ _) S.reflᴹ)))
    S.○ᴹ wire-cong (λ _ → refl) (λ p → sym (assoc⁻¹-picks S⃗ T⃗ U⃗ p))
    where L = Cᶠ ((S⃗ ++ T⃗) ++ U⃗)
          R = Cᶠ (S⃗ ++ (T⃗ ++ U⃗))

reads-unit⇒ : (S⃗ : List Set) → Reads (flat (S⃗ ++ [])) (flat S⃗) (N.unit++.from S⃗) (wireᴾ (unit⇒ʳ S⃗))
reads-unit⇒ S⃗ = reads-resp {x = flat (S⃗ ++ [])} {y = flat S⃗}
  (refl⟩∘⟨ (G.⊗.identity ⟩∘⟨refl ○ G.identityˡ))
  (unit⇒-wire S⃗ S.○ᴹ S.⟺ᴹ (wireᴾ-total {S⃗} {S⃗ ++ []} (unitʳᴵ S⃗) (SSP.ch (unitʳᴵ⁻¹ S⃗)) (unitʳ-inv S⃗) (unitʳ⁻¹-inv S⃗)))
  (reads-∘ {x = flat (S⃗ ++ [])} {y = flat S⃗ ⊗ᶠ unitᶠ} {z = flat S⃗} (reads-ρ (flat S⃗))
    (reads-∘ {x = flat (S⃗ ++ [])} {y = flat S⃗ ⊗ᶠ flat []} {z = flat S⃗ ⊗ᶠ unitᶠ}
      (reads-T₁ {x = flat S⃗} {y = flat []} {z = unitᶠ} reads-nil⁻¹) (reads-C++⁻¹ S⃗ [])))

reads-unit⇐ : (S⃗ : List Set) → Reads (flat S⃗) (flat (S⃗ ++ [])) (N.unit++.to S⃗) (wireᴾ (unit⇐ʳ S⃗))
reads-unit⇐ S⃗ = reads-resp {x = flat S⃗} {y = flat (S⃗ ++ [])}
  (refl⟩∘⟨ (G.⊗.identity ⟩∘⟨refl ○ G.identityˡ))
  (unit⇐-wire S⃗ S.○ᴹ S.⟺ᴹ (wireᴾ-total {S⃗ ++ []} {S⃗} (unitʳᴵ⁻¹ S⃗) (SSP.ch (unitʳᴵ S⃗)) (unitʳ⁻¹-inv S⃗) (unitʳ-inv S⃗)))
  (reads-∘ {x = flat S⃗} {y = flat S⃗ ⊗ᶠ flat []} {z = flat (S⃗ ++ [])} (reads-C++ S⃗ [])
    (reads-∘ {x = flat S⃗} {y = flat S⃗ ⊗ᶠ unitᶠ} {z = flat S⃗ ⊗ᶠ flat []}
      (reads-T₁ {x = flat S⃗} {y = unitᶠ} {z = flat []} reads-nil) (reads-ρ⁻¹ (flat S⃗))))

reads-assoc⇒ : (S⃗ T⃗ U⃗ : List Set) → Reads (flat ((S⃗ ++ T⃗) ++ U⃗)) (flat (S⃗ ++ (T⃗ ++ U⃗)))
  (N.assoc++.from S⃗ T⃗ U⃗) (wireᴾ (assoc⇒ʳ S⃗ T⃗ U⃗))
reads-assoc⇒ S⃗ T⃗ U⃗ = reads-resp {x = flat ((S⃗ ++ T⃗) ++ U⃗)} {y = flat (S⃗ ++ (T⃗ ++ U⃗))} G.Equiv.refl
  (assoc⇒-wire S⃗ T⃗ U⃗ S.○ᴹ S.⟺ᴹ (wireᴾ-total {S⃗ ++ (T⃗ ++ U⃗)} {(S⃗ ++ T⃗) ++ U⃗}
    (assocᴵ S⃗ T⃗ U⃗) (SSP.ch (assocᴵ⁻¹ S⃗ T⃗ U⃗)) (assoc-inv S⃗ T⃗ U⃗) (assoc⁻¹-inv S⃗ T⃗ U⃗)))
  (reads-∘ {x = flat ((S⃗ ++ T⃗) ++ U⃗)} {y = flat S⃗ ⊗ᶠ flat (T⃗ ++ U⃗)} {z = flat (S⃗ ++ (T⃗ ++ U⃗))} (reads-C++ S⃗ (T⃗ ++ U⃗))
    (reads-∘ {x = flat ((S⃗ ++ T⃗) ++ U⃗)} {y = flat S⃗ ⊗ᶠ (flat T⃗ ⊗ᶠ flat U⃗)} {z = flat S⃗ ⊗ᶠ flat (T⃗ ++ U⃗)}
      (reads-T₁ {x = flat S⃗} {y = flat T⃗ ⊗ᶠ flat U⃗} {z = flat (T⃗ ++ U⃗)} (reads-C++ T⃗ U⃗))
      (reads-∘ {x = flat ((S⃗ ++ T⃗) ++ U⃗)} {y = (flat S⃗ ⊗ᶠ flat T⃗) ⊗ᶠ flat U⃗} {z = flat S⃗ ⊗ᶠ (flat T⃗ ⊗ᶠ flat U⃗)}
        (reads-α (flat S⃗) (flat T⃗) (flat U⃗))
        (reads-∘ {x = flat ((S⃗ ++ T⃗) ++ U⃗)} {y = flat (S⃗ ++ T⃗) ⊗ᶠ flat U⃗} {z = (flat S⃗ ⊗ᶠ flat T⃗) ⊗ᶠ flat U⃗}
          (reads-sub {x = flat (S⃗ ++ T⃗)} {y = flat S⃗ ⊗ᶠ flat T⃗} {z = flat U⃗} (reads-C++⁻¹ S⃗ T⃗)) (reads-C++⁻¹ (S⃗ ++ T⃗) U⃗)))))

reads-assoc⇐ : (S⃗ T⃗ U⃗ : List Set) → Reads (flat (S⃗ ++ (T⃗ ++ U⃗))) (flat ((S⃗ ++ T⃗) ++ U⃗))
  (N.assoc++.to S⃗ T⃗ U⃗) (wireᴾ (assoc⇐ʳ S⃗ T⃗ U⃗))
reads-assoc⇐ S⃗ T⃗ U⃗ = reads-resp {x = flat (S⃗ ++ (T⃗ ++ U⃗))} {y = flat ((S⃗ ++ T⃗) ++ U⃗)} (G.sym-assoc ○ G.sym-assoc ○ G.sym-assoc)
  (assoc⇐-wire S⃗ T⃗ U⃗ S.○ᴹ S.⟺ᴹ (wireᴾ-total {(S⃗ ++ T⃗) ++ U⃗} {S⃗ ++ (T⃗ ++ U⃗)}
    (assocᴵ⁻¹ S⃗ T⃗ U⃗) (SSP.ch (assocᴵ S⃗ T⃗ U⃗)) (assoc⁻¹-inv S⃗ T⃗ U⃗) (assoc-inv S⃗ T⃗ U⃗)))
  (reads-∘ {x = flat (S⃗ ++ (T⃗ ++ U⃗))} {y = flat (S⃗ ++ T⃗) ⊗ᶠ flat U⃗} {z = flat ((S⃗ ++ T⃗) ++ U⃗)} (reads-C++ (S⃗ ++ T⃗) U⃗)
    (reads-∘ {x = flat (S⃗ ++ (T⃗ ++ U⃗))} {y = (flat S⃗ ⊗ᶠ flat T⃗) ⊗ᶠ flat U⃗} {z = flat (S⃗ ++ T⃗) ⊗ᶠ flat U⃗}
      (reads-sub {x = flat S⃗ ⊗ᶠ flat T⃗} {y = flat (S⃗ ++ T⃗)} {z = flat U⃗} (reads-C++ S⃗ T⃗))
      (reads-∘ {x = flat (S⃗ ++ (T⃗ ++ U⃗))} {y = flat S⃗ ⊗ᶠ (flat T⃗ ⊗ᶠ flat U⃗)} {z = (flat S⃗ ⊗ᶠ flat T⃗) ⊗ᶠ flat U⃗}
        (reads-α⁻¹ (flat S⃗) (flat T⃗) (flat U⃗))
        (reads-∘ {x = flat (S⃗ ++ (T⃗ ++ U⃗))} {y = flat S⃗ ⊗ᶠ flat (T⃗ ++ U⃗)} {z = flat S⃗ ⊗ᶠ (flat T⃗ ⊗ᶠ flat U⃗)}
          (reads-T₁ {x = flat S⃗} {y = flat (T⃗ ++ U⃗)} {z = flat T⃗ ⊗ᶠ flat U⃗} (reads-C++⁻¹ T⃗ U⃗)) (reads-C++⁻¹ S⃗ (T⃗ ++ U⃗))))))
