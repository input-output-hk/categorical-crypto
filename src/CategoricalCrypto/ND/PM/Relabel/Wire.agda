{-# OPTIONS --safe --without-K --guardedness #-}

-- Requests travel through the partial inverse; picks travel through the
-- relabelling itself. An absent route diverges on either polarity.

open import Categories.Category using (Category)

open import Data.List.Base using (List; _++_)
open import Data.Maybe.Base as Maybe using (just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Function.Base using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Det
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.PM.Read using (tensorᴵ)
open import CategoricalCrypto.ND.Relabel
open import CategoricalCrypto.ND.SSP.Choice using (Cᴵ⟦_⟧; join; split)
open import CategoricalCrypto.SSP.Iface as SSP using (Ch; ch)
import CategoricalCrypto.SSP.Iface.Payload as Payload
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire.Kleisli

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.ND.PM.Relabel.Wire where

private
  module P = Category 𝒫ᴵ
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  variable S⃗ T⃗ U⃗ S⃗′ T⃗′ : List Set

wireᴾ : S⃗ ⇝ T⃗ → Proc (Cᶠ T⃗) (Cᶠ S⃗)
wireᴾ ρ = kwireᴹ (detₚ ∘ preimage ρ) (detₚ ∘ routePick ρ)

wireᴾ-id : P._≈_ {Cᶠ S⃗} {Cᶠ S⃗} (wireᴾ (idʳ {S⃗})) (P.id {Cᶠ S⃗})
wireᴾ-id {S⃗} = kwire-cong (λ c → ≡⇒≈ₚ (cong detₚ (preimage-id {S⃗} c))) (λ _ → ≈refl) S.○ᴹ kwire-id

wireᴾ-resp : {ρ ρ′ : S⃗ ⇝ T⃗} → ρ ≈ʳ ρ′ → P._≈_ {Cᶠ T⃗} {Cᶠ S⃗} (wireᴾ ρ) (wireᴾ ρ′)
wireᴾ-resp e = kwire-cong (λ c → ≡⇒≈ₚ (cong detₚ (preimage-resp e c))) (λ p → ≡⇒≈ₚ (cong detₚ (routePick-resp e p)))

wireᴾ-∘ : (ρ′ : T⃗ ⇝ U⃗) (ρ : S⃗ ⇝ T⃗)
         → P._≈_ {Cᶠ U⃗} {Cᶠ S⃗} (wireᴾ (ρ′ ∘ʳ ρ)) (P._∘_ {Cᶠ U⃗} {Cᶠ T⃗} {Cᶠ S⃗} (wireᴾ ρ) (wireᴾ ρ′))
wireᴾ-∘ ρ′ ρ = kwire-cong
  (λ c → ≡⇒≈ₚ (cong detₚ (preimage-∘ ρ′ ρ c)) ⟨≈⟩ ≈sym (detₚ->>= (preimage ρ′ c) (preimage ρ)))
  (λ p → ≡⇒≈ₚ (cong detₚ (routePick-∘ ρ′ ρ p)) ⟨≈⟩ ≈sym (detₚ->>= (routePick ρ p) (routePick ρ′)))
  S.○ᴹ S.⟺ᴹ (kwire-∘ (detₚ ∘ preimage ρ) (detₚ ∘ routePick ρ) (detₚ ∘ preimage ρ′) (detₚ ∘ routePick ρ′))

wireᴾ-total : (m : Cᴵ⟦ S⃗ ⟧ SSP.⇒ᴵ Cᴵ⟦ T⃗ ⟧) (back : Ch Cᴵ⟦ T⃗ ⟧ → Ch Cᴵ⟦ S⃗ ⟧)
              (inv : ∀ i → back (ch m i) ≡ i) (inv′ : ∀ k → ch m (back k) ≡ k)
            → P._≈_ {Cᶠ T⃗} {Cᶠ S⃗} (wireᴾ (wireʳ {S⃗} {T⃗} m back inv)) (wireᴹ {Cᶠ T⃗} {Cᶠ S⃗} back (Payload.mapᴾ m))
wireᴾ-total {S⃗} {T⃗} m back inv inv′ = kwire-cong {Cᶠ T⃗} {Cᶠ S⃗}
  (λ c → ≡⇒≈ₚ (cong detₚ (preimage-wireʳ {S⃗} {T⃗} m back inv inv′ c))) (λ _ → ≈refl)
  S.○ᴹ S.⟺ᴹ (wire-kwire {Cᶠ T⃗} {Cᶠ S⃗} back (Payload.mapᴾ m))

module _ {S⃗ T⃗ S⃗′ T⃗′ : List Set} (ρ : S⃗ ⇝ T⃗) (ρ′ : S⃗′ ⇝ T⃗′) where
  private
    up = [ Maybe.map inj₁ ∘ preimage ρ , Maybe.map inj₂ ∘ preimage ρ′ ]′
    down = [ Maybe.map inj₁ ∘ routePick ρ , Maybe.map inj₂ ∘ routePick ρ′ ]′

    tensor-wire : P._≈_ {Cᶠ T⃗ ⊗ᴵ Cᶠ T⃗′} {Cᶠ S⃗ ⊗ᴵ Cᶠ S⃗′}
      (tensorᴵ (wireᴾ ρ) (wireᴾ ρ′)) (kwireᴹ (detₚ ∘ up) (detₚ ∘ down))
    tensor-wire = kwire-⊗ (detₚ ∘ preimage ρ) (detₚ ∘ routePick ρ) (detₚ ∘ preimage ρ′) (detₚ ∘ routePick ρ′)
      S.○ᴹ kwire-cong
        (λ { (inj₁ c) → detₚ-map inj₁ (preimage ρ c) ; (inj₂ c) → detₚ-map inj₂ (preimage ρ′ c) })
        (λ { (inj₁ p) → detₚ-map inj₁ (routePick ρ p) ; (inj₂ p) → detₚ-map inj₂ (routePick ρ′ p) })

  wireᴾ-++ : P._≈_ {Cᶠ (T⃗ ++ T⃗′)} {Cᶠ (S⃗ ++ S⃗′)}
    (wireᴾ (ρ ++ʳ ρ′))
    (P._∘_ {Cᶠ (T⃗ ++ T⃗′)} {Cᶠ S⃗ ⊗ᴵ Cᶠ S⃗′} {Cᶠ (S⃗ ++ S⃗′)} (joinᶠ S⃗ S⃗′)
      (P._∘_ {Cᶠ (T⃗ ++ T⃗′)} {Cᶠ T⃗ ⊗ᴵ Cᶠ T⃗′} {Cᶠ S⃗ ⊗ᴵ Cᶠ S⃗′}
        (tensorᴵ (wireᴾ ρ) (wireᴾ ρ′)) (splitᶠ T⃗ T⃗′)))
  wireᴾ-++ = kwire-cong
    (λ c → ≡⇒≈ₚ (cong detₚ (preimage-++ ρ ρ′ c)) ⟨≈⟩ ≈sym (detₚ-map (ch (join S⃗ S⃗′)) (up (ch (split T⃗ T⃗′) c))))
    (λ p → ≡⇒≈ₚ (cong detₚ (routePick-++ ρ ρ′ p)) ⟨≈⟩ ≈sym (detₚ-map (joinPick T⃗ T⃗′) (down (splitPick S⃗ S⃗′ p))))
    S.○ᴹ S.⟺ᴹ (kwire-frame (ch (join S⃗ S⃗′)) (splitPick S⃗ S⃗′) (ch (split T⃗ T⃗′)) (joinPick T⃗ T⃗′) (detₚ ∘ up) (detₚ ∘ down))
    S.○ᴹ P.∘-resp-≈ {Cᶠ (T⃗ ++ T⃗′)} {Cᶠ S⃗ ⊗ᴵ Cᶠ S⃗′} {Cᶠ (S⃗ ++ S⃗′)} S.reflᴹ
      (P.∘-resp-≈ {Cᶠ (T⃗ ++ T⃗′)} {Cᶠ T⃗ ⊗ᴵ Cᶠ T⃗′} {Cᶠ S⃗ ⊗ᴵ Cᶠ S⃗′} (S.⟺ᴹ tensor-wire) S.reflᴹ)
