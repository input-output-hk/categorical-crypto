{-# OPTIONS --safe --without-K --guardedness #-}

-- The monoidal category `𝒲ᴹ` of well-bracketed machines and its strong
-- monoidal inclusion `ιᴹ` into the sealed bundle `𝔾ᵒ` (`docs/uc-setup-ssp.md`
-- §4.2): `𝔾ᵒ` transported along the relabellings `φʷ` to `SSP.Iface` objects
-- (`Categories.Category.Monoidal.Construction.Transport`), restricted to the
-- maps equal to a well-bracketed machine (`Wᵒ`).  A structural map of the
-- transport is a composite of wires, hence a wire (`UC.Machine.Wire.Algebra`),
-- and a wire that returns on the queried channel is well-bracketed (`wire-W`).
--
-- The seal is crossed in one `opaque` block exporting the isos and the closure
-- facts, `UC.Model.Seal`'s discipline.  `ι⇒prot` is the inclusion as a morphism
-- of UC setups, `𝔾ᵒ`'s tests pulled back.

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.Morphism.Notation
open import Categories.NaturalTransformation

open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Base using () renaming (assocˡ to ⊎assocˡ; assocʳ to ⊎assocʳ)
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Bracket.Category
open import CategoricalCrypto.UC.Bracket.Tensor
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Wire.Algebra
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup using (ℰᵒ)
open import CategoricalCrypto.UCSetup.Morphism

import Categories.Category.Monoidal.Construction.Transport as Transport
import Categories.Morphism as Mor
import CategoricalCrypto.Iface as Flat
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Model.Setup as Prot
import Data.Empty.Polymorphic as P

module CategoricalCrypto.UC.Bracket.Monoidal where

private
  module G  = MonoidalCategory 𝔾ᵒ
  module Gᴹ = Mor G.U
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫  = Category 𝒫ᴵ

private variable
  A B C : Iface
  X Y Z : Set

------------------------------------------------------------------------
-- The structural wires

dropΣˡ : {K : ⊥ → Set} {L : X → Set} → Σ (⊥ ⊎ X) [ K , L ]′ → Σ X L
dropΣˡ (inj₁ () , _)
dropΣˡ (inj₂ x , u) = x , u

addΣˡ : {K : ⊥ → Set} {L : X → Set} → Σ X L → Σ (⊥ ⊎ X) [ K , L ]′
addΣˡ (x , u) = inj₂ x , u

dropΣʳ : {K : X → Set} {L : ⊥ → Set} → Σ (X ⊎ ⊥) [ K , L ]′ → Σ X K
dropΣʳ (inj₁ x , u) = x , u
dropΣʳ (inj₂ () , _)

addΣʳ : {K : X → Set} {L : ⊥ → Set} → Σ X K → Σ (X ⊎ ⊥) [ K , L ]′
addΣʳ (x , u) = inj₁ x , u

assocΣʳ : {K : X → Set} {L : Y → Set} {M : Z → Set}
        → Σ ((X ⊎ Y) ⊎ Z) [ [ K , L ]′ , M ]′ → Σ (X ⊎ (Y ⊎ Z)) [ K , [ L , M ]′ ]′
assocΣʳ (inj₁ (inj₁ x) , u) = inj₁ x , u
assocΣʳ (inj₁ (inj₂ y) , u) = inj₂ (inj₁ y) , u
assocΣʳ (inj₂ z , u)        = inj₂ (inj₂ z) , u

assocΣˡ : {K : X → Set} {L : Y → Set} {M : Z → Set}
        → Σ (X ⊎ (Y ⊎ Z)) [ K , [ L , M ]′ ]′ → Σ ((X ⊎ Y) ⊎ Z) [ [ K , L ]′ , M ]′
assocΣˡ (inj₁ x , u)        = inj₁ (inj₁ x) , u
assocΣˡ (inj₂ (inj₁ y) , u) = inj₁ (inj₂ y) , u
assocΣˡ (inj₂ (inj₂ z) , u) = inj₂ z , u

λʷ : Proc (flat (unitᴵ ⊗ᴵ A)) (flat A)
λʷ = wireᴹ dropΣˡ addΣˡ

λʷ⁻¹ : Proc (flat A) (flat (unitᴵ ⊗ᴵ A))
λʷ⁻¹ = wireᴹ addΣˡ dropΣˡ

ρʷ : Proc (flat (A ⊗ᴵ unitᴵ)) (flat A)
ρʷ = wireᴹ dropΣʳ addΣʳ

ρʷ⁻¹ : Proc (flat A) (flat (A ⊗ᴵ unitᴵ))
ρʷ⁻¹ = wireᴹ addΣʳ dropΣʳ

αʷ : Proc (flat ((A ⊗ᴵ B) ⊗ᴵ C)) (flat (A ⊗ᴵ (B ⊗ᴵ C)))
αʷ = wireᴹ assocΣʳ assocΣˡ

αʷ⁻¹ : Proc (flat (A ⊗ᴵ (B ⊗ᴵ C))) (flat ((A ⊗ᴵ B) ⊗ᴵ C))
αʷ⁻¹ = wireᴹ assocΣˡ assocΣʳ

λʷ-W : W {unitᴵ ⊗ᴵ A} {A} (λʷ {A})
λʷ-W {A} = wire-W {A = unitᴵ ⊗ᴵ A} {B = A} {up = dropΣˡ} {down = addΣˡ} λ _ _ _ → refl

λʷ⁻¹-W : W {A} {unitᴵ ⊗ᴵ A} (λʷ⁻¹ {A})
λʷ⁻¹-W {A} = wire-W {A = A} {B = unitᴵ ⊗ᴵ A} {up = addΣˡ} {down = dropΣˡ} λ where
  (inj₁ ()) _ _
  (inj₂ _)  _ _ → refl

ρʷ-W : W {A ⊗ᴵ unitᴵ} {A} (ρʷ {A})
ρʷ-W {A} = wire-W {A = A ⊗ᴵ unitᴵ} {B = A} {up = dropΣʳ} {down = addΣʳ} λ _ _ _ → refl

ρʷ⁻¹-W : W {A} {A ⊗ᴵ unitᴵ} (ρʷ⁻¹ {A})
ρʷ⁻¹-W {A} = wire-W {A = A} {B = A ⊗ᴵ unitᴵ} {up = addΣʳ} {down = dropΣʳ} λ where
  (inj₁ _)  _ _ → refl
  (inj₂ ()) _ _

αʷ-W : W {(A ⊗ᴵ B) ⊗ᴵ C} {A ⊗ᴵ (B ⊗ᴵ C)} (αʷ {A} {B} {C})
αʷ-W {A} {B} {C} = wire-W {A = (A ⊗ᴵ B) ⊗ᴵ C} {B = A ⊗ᴵ (B ⊗ᴵ C)} {up = assocΣʳ} {down = assocΣˡ} λ where
  (inj₁ _)        _ _ → refl
  (inj₂ (inj₁ _)) _ _ → refl
  (inj₂ (inj₂ _)) _ _ → refl

αʷ⁻¹-W : W {A ⊗ᴵ (B ⊗ᴵ C)} {(A ⊗ᴵ B) ⊗ᴵ C} (αʷ⁻¹ {A} {B} {C})
αʷ⁻¹-W {A} {B} {C} = wire-W {A = A ⊗ᴵ (B ⊗ᴵ C)} {B = (A ⊗ᴵ B) ⊗ᴵ C} {up = assocΣˡ} {down = assocΣʳ} λ where
  (inj₁ (inj₁ _)) _ _ → refl
  (inj₁ (inj₂ _)) _ _ → refl
  (inj₂ _)        _ _ → refl

------------------------------------------------------------------------
-- Across the seal

Uᵂ : Iface → G.Obj
Uᵂ A = ifaceᵒ (flat A)

opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ

  φ : G.U [ Uᵂ A G.⊗₀ Uᵂ C ≅ Uᵂ (A ⊗ᴵ C) ]
  φ {A} {C} = record
    { from = φʷ {A} {C}
    ; to   = φʷ⁻¹ {A} {C}
    ; iso  = record
      { isoˡ = wire∘wire splitΣ joinΣ joinΣ splitΣ S.○ᴹ wire-cong split-join split-join S.○ᴹ wire-id
      ; isoʳ = wire∘wire joinΣ splitΣ splitΣ joinΣ S.○ᴹ wire-cong join-split join-split S.○ᴹ wire-id
      }
    }

  υ : G.U [ G.unit ≅ Uᵂ unitᴵ ]
  υ = record
    { from = wireᴹ {𝟭ᴵ} {flat unitᴵ} P.⊥-elim λ { (() , _) }
    ; to   = wireᴹ {flat unitᴵ} {𝟭ᴵ} (λ { (() , _) }) P.⊥-elim
    ; iso  = record
      { isoˡ = wire∘wire {flat unitᴵ} (λ { (() , _) }) P.⊥-elim P.⊥-elim (λ { (() , _) })
          S.○ᴹ wire-cong (λ p → P.⊥-elim p) (λ n → P.⊥-elim n) S.○ᴹ wire-id
      ; isoʳ = wire∘wire {𝟭ᴵ} P.⊥-elim (λ { (() , _) }) (λ { (() , _) }) P.⊥-elim
          S.○ᴹ wire-cong (λ { (() , _) }) (λ { (() , _) }) S.○ᴹ wire-id
      }
    }

  procᵒ-id : {X : Flat.Iface} → G.id {ifaceᵒ X} G.≈ procᵒ {X} {X} (𝒫.id {X})
  procᵒ-id = S.reflᴹ

  ⊗-conj : {A B C D : Iface} (f : Proc (flat A) (flat B)) (g : Proc (flat C) (flat D))
         → Gᴹ._≅_.from (φ {B} {D}) G.∘ (procᵒ f G.⊗₁ procᵒ g) G.∘ Gᴹ._≅_.to (φ {A} {C})
           G.≈ procᵒ (_⊗ʷ_ {A} {B} {C} {D} f g)
  ⊗-conj f g = conj≈⊗ʷ f g

  λ-wire : G.unitorˡ.from G.∘ (Gᴹ._≅_.to υ G.⊗₁ G.id) G.∘ Gᴹ._≅_.to (φ {unitᴵ} {A}) G.≈ procᵒ (λʷ {A})
  λ-wire {A} =
         ∘-wire {flat (unitᴵ ⊗ᴵ A)} {𝟭ᴵ Flat.⊗ᴵ flat A} {flat A} (S.⟺ᴹ (λ⇒-λᴳ {flat A}))
           (∘-wire {flat (unitᴵ ⊗ᴵ A)} {flat unitᴵ Flat.⊗ᴵ flat A} {𝟭ᴵ Flat.⊗ᴵ flat A}
             (S.⟺ᴹ (sub-⊗₁ {flat unitᴵ} {𝟭ᴵ} {flat A} (Gᴹ._≅_.to υ)) S.○ᴹ sub-wire _ _) S.reflᴹ)
    S.○ᴹ wire-cong (λ { (inj₁ () , _) ; (inj₂ _ , _) → refl }) (λ _ → refl)

  λ⇐-wire : Gᴹ._≅_.from (φ {unitᴵ} {A}) G.∘ (Gᴹ._≅_.from υ G.⊗₁ G.id) G.∘ G.unitorˡ.to G.≈ procᵒ (λʷ⁻¹ {A})
  λ⇐-wire {A} =
         ∘-wire {flat A} {flat unitᴵ Flat.⊗ᴵ flat A} {flat (unitᴵ ⊗ᴵ A)} S.reflᴹ
           (∘-wire {flat A} {𝟭ᴵ Flat.⊗ᴵ flat A} {flat unitᴵ Flat.⊗ᴵ flat A}
             (S.⟺ᴹ (sub-⊗₁ {𝟭ᴵ} {flat unitᴵ} {flat A} (Gᴹ._≅_.from υ)) S.○ᴹ sub-wire _ _)
             (S.⟺ᴹ (λ⇐-λᴳ {flat A})))
    S.○ᴹ wire-cong (λ _ → refl) (λ { (inj₁ () , _) ; (inj₂ _ , _) → refl })

  ρ-wire : G.unitorʳ.from G.∘ (G.id G.⊗₁ Gᴹ._≅_.to υ) G.∘ Gᴹ._≅_.to (φ {A} {unitᴵ}) G.≈ procᵒ (ρʷ {A})
  ρ-wire {A} =
         ∘-wire {flat (A ⊗ᴵ unitᴵ)} {flat A Flat.⊗ᴵ 𝟭ᴵ} {flat A} (S.⟺ᴹ (ρ⇒-ρᴳ {flat A}))
           (∘-wire {flat (A ⊗ᴵ unitᴵ)} {flat A Flat.⊗ᴵ flat unitᴵ} {flat A Flat.⊗ᴵ 𝟭ᴵ}
             (S.⟺ᴹ (T₁-⊗₁ {flat A} {flat unitᴵ} {𝟭ᴵ} (Gᴹ._≅_.to υ)) S.○ᴹ T₁-wire _ _) S.reflᴹ)
    S.○ᴹ wire-cong (λ { (inj₁ _ , _) → refl ; (inj₂ () , _) }) (λ _ → refl)

  ρ⇐-wire : Gᴹ._≅_.from (φ {A} {unitᴵ}) G.∘ (G.id G.⊗₁ Gᴹ._≅_.from υ) G.∘ G.unitorʳ.to G.≈ procᵒ (ρʷ⁻¹ {A})
  ρ⇐-wire {A} =
         ∘-wire {flat A} {flat A Flat.⊗ᴵ flat unitᴵ} {flat (A ⊗ᴵ unitᴵ)} S.reflᴹ
           (∘-wire {flat A} {flat A Flat.⊗ᴵ 𝟭ᴵ} {flat A Flat.⊗ᴵ flat unitᴵ}
             (S.⟺ᴹ (T₁-⊗₁ {flat A} {𝟭ᴵ} {flat unitᴵ} (Gᴹ._≅_.from υ)) S.○ᴹ T₁-wire _ _)
             (S.⟺ᴹ (ρ⇐-ρᴳ {flat A})))
    S.○ᴹ wire-cong (λ _ → refl) (λ { (inj₁ _ , _) → refl ; (inj₂ () , _) })

  α-wire : Gᴹ._≅_.from (φ {A} {B ⊗ᴵ C}) G.∘ (G.id G.⊗₁ Gᴹ._≅_.from (φ {B} {C})) G.∘ G.associator.from
           G.∘ (Gᴹ._≅_.to (φ {A} {B}) G.⊗₁ G.id) G.∘ Gᴹ._≅_.to (φ {A ⊗ᴵ B} {C})
           G.≈ procᵒ (αʷ {A} {B} {C})
  α-wire {A} {B} {C} =
         ∘-wire {X₀} {flat A Flat.⊗ᴵ flat (B ⊗ᴵ C)} {flat (A ⊗ᴵ (B ⊗ᴵ C))} S.reflᴹ
           (∘-wire {X₀} {flat A Flat.⊗ᴵ (flat B Flat.⊗ᴵ flat C)} {flat A Flat.⊗ᴵ flat (B ⊗ᴵ C)}
             (S.⟺ᴹ (T₁-⊗₁ {flat A} {flat B Flat.⊗ᴵ flat C} {flat (B ⊗ᴵ C)} (Gᴹ._≅_.from (φ {B} {C})))
               S.○ᴹ T₁-wire _ _)
             (∘-wire {X₀} {(flat A Flat.⊗ᴵ flat B) Flat.⊗ᴵ flat C} {flat A Flat.⊗ᴵ (flat B Flat.⊗ᴵ flat C)}
               (S.⟺ᴹ (a⇒-α⇒ {flat A} {flat B} {flat C}))
               (∘-wire {X₀} {flat (A ⊗ᴵ B) Flat.⊗ᴵ flat C} {(flat A Flat.⊗ᴵ flat B) Flat.⊗ᴵ flat C}
                 (S.⟺ᴹ (sub-⊗₁ {flat (A ⊗ᴵ B)} {flat A Flat.⊗ᴵ flat B} {flat C} (Gᴹ._≅_.to (φ {A} {B})))
                   S.○ᴹ sub-wire _ _)
                 S.reflᴹ)))
    S.○ᴹ wire-cong (λ { (inj₁ (inj₁ _) , _) → refl ; (inj₁ (inj₂ _) , _) → refl ; (inj₂ _ , _) → refl })
                   (λ { (inj₁ _ , _) → refl ; (inj₂ (inj₁ _) , _) → refl ; (inj₂ (inj₂ _) , _) → refl })
    where
    X₀ : Flat.Iface
    X₀ = flat ((A ⊗ᴵ B) ⊗ᴵ C)

  α⇐-wire : Gᴹ._≅_.from (φ {A ⊗ᴵ B} {C}) G.∘ (Gᴹ._≅_.from (φ {A} {B}) G.⊗₁ G.id) G.∘ G.associator.to
            G.∘ (G.id G.⊗₁ Gᴹ._≅_.to (φ {B} {C})) G.∘ Gᴹ._≅_.to (φ {A} {B ⊗ᴵ C})
            G.≈ procᵒ (αʷ⁻¹ {A} {B} {C})
  α⇐-wire {A} {B} {C} =
         ∘-wire {Y₀} {flat (A ⊗ᴵ B) Flat.⊗ᴵ flat C} {flat ((A ⊗ᴵ B) ⊗ᴵ C)} S.reflᴹ
           (∘-wire {Y₀} {(flat A Flat.⊗ᴵ flat B) Flat.⊗ᴵ flat C} {flat (A ⊗ᴵ B) Flat.⊗ᴵ flat C}
             (S.⟺ᴹ (sub-⊗₁ {flat A Flat.⊗ᴵ flat B} {flat (A ⊗ᴵ B)} {flat C} (Gᴹ._≅_.from (φ {A} {B})))
               S.○ᴹ sub-wire _ _)
             (∘-wire {Y₀} {flat A Flat.⊗ᴵ (flat B Flat.⊗ᴵ flat C)} {(flat A Flat.⊗ᴵ flat B) Flat.⊗ᴵ flat C}
               (S.⟺ᴹ (a⇐-α⇐ {flat A} {flat B} {flat C}))
               (∘-wire {Y₀} {flat A Flat.⊗ᴵ flat (B ⊗ᴵ C)} {flat A Flat.⊗ᴵ (flat B Flat.⊗ᴵ flat C)}
                 (S.⟺ᴹ (T₁-⊗₁ {flat A} {flat (B ⊗ᴵ C)} {flat B Flat.⊗ᴵ flat C} (Gᴹ._≅_.to (φ {B} {C})))
                   S.○ᴹ T₁-wire _ _)
                 S.reflᴹ)))
    S.○ᴹ wire-cong (λ { (inj₁ _ , _) → refl ; (inj₂ (inj₁ _) , _) → refl ; (inj₂ (inj₂ _) , _) → refl })
                   (λ { (inj₁ (inj₁ _) , _) → refl ; (inj₁ (inj₂ _) , _) → refl ; (inj₂ _ , _) → refl })
    where
    Y₀ : Flat.Iface
    Y₀ = flat (A ⊗ᴵ (B ⊗ᴵ C))

------------------------------------------------------------------------
-- The monoidal category

-- Equal to a well-bracketed machine.
Wᵒ : {A B : Iface} → Uᵂ A G.⇒ Uᵂ B → Set₁
Wᵒ {A} {B} h = Σ[ f ∈ Proc (flat A) (flat B) ] W {A} {B} f × h G.≈ procᵒ f

Wᵒ-id : Wᵒ {A} {A} (G.id {Uᵂ A})
Wᵒ-id {A} = 𝒫.id {flat A} , id-W , procᵒ-id

Wᵒ-∘ : ∀ {A B C} {g : Uᵂ B G.⇒ Uᵂ C} {f : Uᵂ A G.⇒ Uᵂ B} → Wᵒ {B} {C} g → Wᵒ {A} {B} f → Wᵒ {A} {C} (g G.∘ f)
Wᵒ-∘ {A} {B} {C} (g′ , wg , eg) (f′ , wf , ef) =
    _⊙_ {B = B} {C = C} {A = A} g′ f′
  , ⊙-W {B = B} {C = C} {A = A} wg wf
  , G.Equiv.trans (G.∘-resp-≈ eg ef)
      (G.Equiv.trans (G.Equiv.sym (procᵒ-∘ g′ f′)) (≈ᴹ⇒≈ᵒ (S.⟺ᴹ (⊙≈∘ {B = B} {C = C} {A = A} g′ f′))))

Wᵒ-⊗ : ∀ {A B C D} {f : Uᵂ A G.⇒ Uᵂ B} {g : Uᵂ C G.⇒ Uᵂ D} → Wᵒ {A} {B} f → Wᵒ {C} {D} g
     → Wᵒ {A ⊗ᴵ C} {B ⊗ᴵ D} (Gᴹ._≅_.from (φ {B} {D}) G.∘ (f G.⊗₁ g) G.∘ Gᴹ._≅_.to (φ {A} {C}))
Wᵒ-⊗ {A} {B} {C} {D} (f′ , wf , ef) (g′ , wg , eg) =
    _⊗ʷ_ {A} {B} {C} {D} f′ g′
  , ⊗ʷ-W wf wg
  , G.Equiv.trans (G.∘-resp-≈ʳ (G.∘-resp-≈ˡ (G.⊗.F-resp-≈ (ef , eg)))) (⊗-conj f′ g′)

private
  module 𝕋 = Transport 𝔾ᵒ Uᵂ _⊗ᴵ_ unitᴵ (λ {a} {b} → φ {a} {b}) υ
  module 𝕎 = 𝕋.Restriction (λ {a} {b} → Wᵒ {a} {b}) (λ {a} → Wᵒ-id {a}) Wᵒ-∘ Wᵒ-⊗
    (λ {a} → λʷ {a} , λʷ-W , λ-wire) (λ {a} → λʷ⁻¹ {a} , λʷ⁻¹-W , λ⇐-wire)
    (λ {a} → ρʷ {a} , ρʷ-W , ρ-wire) (λ {a} → ρʷ⁻¹ {a} , ρʷ⁻¹-W , ρ⇐-wire)
    (λ {a} {b} {c} → αʷ {a} {b} {c} , αʷ-W , α-wire) (λ {a} {b} {c} → αʷ⁻¹ {a} {b} {c} , αʷ⁻¹-W , α⇐-wire)

𝒲ᴹ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝒲ᴹ = 𝕎.transport

ιᴹ : StrongMonoidalFunctor 𝒲ᴹ 𝔾ᵒ
ιᴹ = 𝕎.transportF

------------------------------------------------------------------------
-- The inclusion as a morphism of UC setups

ι*ℰᵒ : Presheaf (MonoidalCategory.U 𝒲ᴹ) (Setoids (suc 0ℓ) (suc 0ℓ))
ι*ℰᵒ = ℰᵒ ∘F Functor.op (StrongMonoidalFunctor.F ιᴹ)

-- `pullbackᵛ`, written out, for `ITM.Setup.νᵀ`'s reason.
νι : PresheafMorphism (StrongMonoidalFunctor.F ιᴹ) ι*ℰᵒ ℰᵒ
νι = record { ν = ntHelper record
  { η = λ _ → record { to = λ x → x ; cong = λ e → e } ; commute = λ _ → Setoid.refl (Functor.₀ ℰᵒ _) } }

νι-epi : PresheafMorphism.Epi νι
νι-epi y = y , Setoid.refl (Functor.₀ ℰᵒ _)

νι-mono : PresheafMorphism.Mono νι
νι-mono e = e

ι⇒prot : UCSetupMorphism (StdUC.StdSetup 𝒲ᴹ ι*ℰᵒ) Prot.StdSetup
ι⇒prot = StdUCMorphism 𝒲ᴹ 𝔾ᵒ ι*ℰᵒ ℰᵒ ιᴹ νι
