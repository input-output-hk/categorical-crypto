{-# OPTIONS --safe --without-K --guardedness #-}

-- Commuting squares read sealed structural composites as processes, without
-- asking conversion to invert the interface sums hidden by `Proc`.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Interchange.Braided as BI
import Categories.Category.Monoidal.Utilities as MU
import Categories.Morphism as Mor

open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂; swap)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.Model.Wire

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.ND.PM.Read where

private
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module P = Category 𝒫ᴵ
  module M = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

open Mor G.U
open MU G.monoidal using (_⊗ᵢ_)
open import Categories.Morphism.Reasoning G.U
open G.HomReasoning

record Flat (X : G.Obj) : Set₁ where
  field iface : Iface
        iso : X ≅ ifaceᵒ iface
open Flat public

infixr 7 _⊗ᶠ_
_⊗ᶠ_ : ∀ {X Y} → Flat X → Flat Y → Flat (X G.⊗₀ Y)
x ⊗ᶠ y = record { iface = iface x ⊗ᴵ iface y ; iso = ≅.trans (iso x ⊗ᵢ iso y) (⊗ᵒ≅ (iface x) (iface y)) }

unitᶠ : Flat G.unit
unitᶠ = record { iface = 𝟭ᴵ ; iso = 𝟭ᵒ≅ }

private variable
  X Y Z W : G.Obj
  A B C D : Iface

ifaceᶠ : (A : Iface) → Flat (ifaceᵒ A)
ifaceᶠ A = record { iface = A ; iso = ≅.refl }

Reads : (x : Flat X) (y : Flat Y) → X G.⇒ Y → Proc (iface x) (iface y) → Set₁
Reads x y f p = _≅_.from (iso y) G.∘ f G.≈ procᵒ p G.∘ _≅_.from (iso x)

reads-id : (x : Flat X) → Reads x x G.id (P.id {iface x})
reads-id x = G.identityʳ ○ ⟺ (procᵒ-id ⟩∘⟨refl ○ G.identityˡ)

reads-proc : (p : Proc A B) → Reads (ifaceᶠ A) (ifaceᶠ B) (procᵒ p) p
reads-proc p = G.identityˡ ○ ⟺ G.identityʳ

reads-∘ : {x : Flat X} {y : Flat Y} {z : Flat Z}
          {f : X G.⇒ Y} {g : Y G.⇒ Z} {p : Proc (iface x) (iface y)} {q : Proc (iface y) (iface z)}
        → Reads y z g q → Reads x y f p → Reads x z (g G.∘ f) (P._∘_ {iface x} {iface y} {iface z} q p)
reads-∘ {p = p} {q} eg ef = pullˡ eg ○ G.assoc ○ refl⟩∘⟨ ef ○ G.sym-assoc ○ ⟺ (procᵒ-∘ q p) ⟩∘⟨refl

reads-resp : {x : Flat X} {y : Flat Y} {f g : X G.⇒ Y} {p q : Proc (iface x) (iface y)}
           → f G.≈ g → P._≈_ {iface x} {iface y} p q → Reads x y f p → Reads x y g q
reads-resp ef ep r = refl⟩∘⟨ ⟺ ef ○ r ○ ≈ᴹ⇒≈ᵒ ep ⟩∘⟨refl

tensorᴵ : Proc A B → Proc C D → Proc (A ⊗ᴵ C) (B ⊗ᴵ D)
tensorᴵ {A} {B} {C} {D} = M._⊗₁_ {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ} {⟦ D ⟧ᴵ}

private
  tensor-square : (p : Proc A B) (q : Proc C D)
                → procᵒ (tensorᴵ p q) G.∘ _≅_.from (⊗ᵒ≅ A C)
                  G.≈ _≅_.from (⊗ᵒ≅ B D) G.∘ (procᵒ p G.⊗₁ procᵒ q)
  tensor-square {A} {B} {C} {D} p q = procᵒ-⊗ p q ⟩∘⟨refl ○ G.assoc ○ refl⟩∘⟨ cancelʳ (_≅_.isoˡ (⊗ᵒ≅ A C))

reads-⊗ : {x : Flat X} {y : Flat Y} {z : Flat Z} {w : Flat W}
          {f : X G.⇒ Y} {g : Z G.⇒ W} {p : Proc (iface x) (iface y)} {q : Proc (iface z) (iface w)}
        → Reads x y f p → Reads z w g q → Reads (x ⊗ᶠ z) (y ⊗ᶠ w) (f G.⊗₁ g) (tensorᴵ p q)
reads-⊗ {x = x} {y} {z} {w} {p = p} {q} ef eg =
  G.assoc ○ refl⟩∘⟨ ⟺ G.⊗.homomorphism
  ○ refl⟩∘⟨ G.⊗.F-resp-≈ (ef , eg)
  ○ refl⟩∘⟨ G.⊗.homomorphism ○ G.sym-assoc
  ○ ⟺ (tensor-square p q) ⟩∘⟨refl ○ G.assoc

reads⇒≈ : {x : Flat X} {y : Flat Y} {f g : X G.⇒ Y} {p : Proc (iface x) (iface y)}
         → Reads x y f p → Reads x y g p → f G.≈ g
reads⇒≈ {y = y} rf rg = cancel-fromˡ (iso y) (rf ○ ⟺ rg)

conjugate : (x : Flat X) (y : Flat Y) → Proc (iface x) (iface y) → X G.⇒ Y
conjugate x y p = _≅_.to (iso y) G.∘ procᵒ p G.∘ _≅_.from (iso x)

reads-conjugate : (x : Flat X) (y : Flat Y) (p : Proc (iface x) (iface y)) → Reads x y (conjugate x y p) p
reads-conjugate x y p = cancelˡ (_≅_.isoʳ (iso y))

opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ ⊗ᵒ≅ 𝟭ᵒ≅ symmetricᵒ

  reads-λ : (x : Flat X) → Reads (unitᶠ ⊗ᶠ x) x G.unitorˡ.from (λᴵ {iface x})
  reads-λ x = ⟺ G.unitorˡ-commute-from ○ S.⟺ᴹ (λ⇒-λᴳ {iface x}) ⟩∘⟨refl ○ refl⟩∘⟨ ⟺ G.identityˡ

  reads-λ⁻¹ : (x : Flat X) → Reads x (unitᶠ ⊗ᶠ x) G.unitorˡ.to (wireᴹ {iface x} {𝟭ᴵ ⊗ᴵ iface x} inj₂ drop⇒ˡ)
  reads-λ⁻¹ x = G.identityˡ ⟩∘⟨refl ○ ⟺ G.unitorˡ-commute-to ○ S.⟺ᴹ (λ⇐-λᴳ {iface x}) ⟩∘⟨refl

  reads-ρ : (x : Flat X) → Reads (x ⊗ᶠ unitᶠ) x G.unitorʳ.from (wireᴹ {iface x ⊗ᴵ 𝟭ᴵ} {iface x} drop⇒ʳ inj₁)
  reads-ρ x = ⟺ G.unitorʳ-commute-from ○ S.⟺ᴹ (ρ⇒-ρᴳ {iface x}) ⟩∘⟨refl ○ refl⟩∘⟨ ⟺ G.identityˡ

  reads-ρ⁻¹ : (x : Flat X) → Reads x (x ⊗ᶠ unitᶠ) G.unitorʳ.to (wireᴹ {iface x} {iface x ⊗ᴵ 𝟭ᴵ} inj₁ drop⇒ʳ)
  reads-ρ⁻¹ x = G.identityˡ ⟩∘⟨refl ○ ⟺ G.unitorʳ-commute-to ○ S.⟺ᴹ (ρ⇐-ρᴳ {iface x}) ⟩∘⟨refl

  reads-α : (x : Flat X) (y : Flat Y) (z : Flat Z)
          → Reads ((x ⊗ᶠ y) ⊗ᶠ z) (x ⊗ᶠ (y ⊗ᶠ z)) G.associator.from (a⇒ᴵ {iface x} {iface y} {iface z})
  reads-α x y z =
    (G.identityˡ ○ G.⊗.F-resp-≈ (G.Equiv.refl , G.identityˡ)) ⟩∘⟨refl
    ○ ⟺ G.assoc-commute-from ○ S.⟺ᴹ (a⇒-α⇒ {iface x} {iface y} {iface z}) ⟩∘⟨refl
    ○ refl⟩∘⟨ ⟺ (G.identityˡ ○ G.⊗.F-resp-≈ (G.identityˡ , G.Equiv.refl))

  reads-α⁻¹ : (x : Flat X) (y : Flat Y) (z : Flat Z)
            → Reads (x ⊗ᶠ (y ⊗ᶠ z)) ((x ⊗ᶠ y) ⊗ᶠ z) G.associator.to (a⇐ᴵ {iface x} {iface y} {iface z})
  reads-α⁻¹ x y z =
    (G.identityˡ ○ G.⊗.F-resp-≈ (G.identityˡ , G.Equiv.refl)) ⟩∘⟨refl
    ○ ⟺ G.assoc-commute-to ○ S.⟺ᴹ (a⇐-α⇐ {iface x} {iface y} {iface z}) ⟩∘⟨refl
    ○ refl⟩∘⟨ ⟺ (G.identityˡ ○ G.⊗.F-resp-≈ (G.Equiv.refl , G.identityˡ))

  reads-σ : (x : Flat X) (y : Flat Y) → Reads (x ⊗ᶠ y) (y ⊗ᶠ x) (G.braiding.⇒.η (X , Y))
    (wireᴹ {iface x ⊗ᴵ iface y} {iface y ⊗ᴵ iface x} swap swap)
  reads-σ x y = G.identityˡ ⟩∘⟨refl
    ○ ⟺ (G.braiding.⇒.commute (_≅_.from (iso x) , _≅_.from (iso y)))
    ○ (σ-wireᵒ {iface x} {iface y} ○ G.identityˡ ○ G.identityʳ) ⟩∘⟨refl
    ○ refl⟩∘⟨ ⟺ G.identityˡ

  reads-⊗ᵒ : (A B : Iface) → Reads (ifaceᶠ A ⊗ᶠ ifaceᶠ B) (ifaceᶠ (A ⊗ᴵ B))
    (_≅_.from (⊗ᵒ≅ A B)) (P.id {A ⊗ᴵ B})
  reads-⊗ᵒ A B = G.identity² ○ ⟺ (procᵒ-id ⟩∘⟨refl ○ G.identityˡ ○ G.identityˡ ○ G.⊗.identity)

  reads-⊗ᵒ⁻¹ : (A B : Iface) → Reads (ifaceᶠ (A ⊗ᴵ B)) (ifaceᶠ A ⊗ᶠ ifaceᶠ B)
    (_≅_.to (⊗ᵒ≅ A B)) (P.id {A ⊗ᴵ B})
  reads-⊗ᵒ⁻¹ A B = G.identityʳ ○ G.identityˡ ○ G.⊗.identity ○ ⟺ (procᵒ-id ⟩∘⟨refl ○ G.identity²)

reads-T₁ : {x : Flat X} {y : Flat Y} {z : Flat Z} {f : Y G.⇒ Z} {p : Proc (iface y) (iface z)}
           → Reads y z f p → Reads (x ⊗ᶠ y) (x ⊗ᶠ z) (G.id G.⊗₁ f) (T₁ᴵ (iface x) p)
reads-T₁ {x = x} {y} {z} {p = p} e = reads-resp {x = x ⊗ᶠ y} {y = x ⊗ᶠ z} G.Equiv.refl
  (S.⟺ᴹ (T₁-⊗₁ {iface x} {iface y} {iface z} p))
  (reads-⊗ {x = x} {y = x} {z = y} {w = z} (reads-id x) e)

reads-sub : {x : Flat X} {y : Flat Y} {z : Flat Z} {f : X G.⇒ Y} {p : Proc (iface x) (iface y)}
            → Reads x y f p → Reads (x ⊗ᶠ z) (y ⊗ᶠ z) (f G.⊗₁ G.id) (subᴵ {A = iface z} p)
reads-sub {x = x} {y} {z} {p = p} e = reads-resp {x = x ⊗ᶠ z} {y = y ⊗ᶠ z} G.Equiv.refl
  (S.⟺ᴹ (sub-⊗₁ {iface x} {iface y} {iface z} p))
  (reads-⊗ {x = x} {y = y} {z = z} {w = z} e (reads-id z))

swapInnerᴵ : (A B C D : Iface) → Proc ((A ⊗ᴵ B) ⊗ᴵ (C ⊗ᴵ D)) ((A ⊗ᴵ C) ⊗ᴵ (B ⊗ᴵ D))
swapInnerᴵ A B C D = P._∘_ {L} {A ⊗ᴵ (C ⊗ᴵ (B ⊗ᴵ D))} {R} (a⇐ᴵ {A} {C} {B ⊗ᴵ D})
  (P._∘_ {L} {A ⊗ᴵ (B ⊗ᴵ (C ⊗ᴵ D))} {A ⊗ᴵ (C ⊗ᴵ (B ⊗ᴵ D))} (T₁ᴵ A inner) (a⇒ᴵ {A} {B} {C ⊗ᴵ D}))
  where
  L = (A ⊗ᴵ B) ⊗ᴵ (C ⊗ᴵ D)
  R = (A ⊗ᴵ C) ⊗ᴵ (B ⊗ᴵ D)
  inner = P._∘_ {B ⊗ᴵ (C ⊗ᴵ D)} {(C ⊗ᴵ B) ⊗ᴵ D} {C ⊗ᴵ (B ⊗ᴵ D)} (a⇒ᴵ {C} {B} {D})
    (P._∘_ {B ⊗ᴵ (C ⊗ᴵ D)} {(B ⊗ᴵ C) ⊗ᴵ D} {(C ⊗ᴵ B) ⊗ᴵ D}
      (subᴵ {A = D} (wireᴹ {B ⊗ᴵ C} {C ⊗ᴵ B} swap swap)) (a⇐ᴵ {B} {C} {D}))

reads-swapInner : (x : Flat X) (y : Flat Y) (z : Flat Z) (w : Flat W)
  → Reads ((x ⊗ᶠ y) ⊗ᶠ (z ⊗ᶠ w)) ((x ⊗ᶠ z) ⊗ᶠ (y ⊗ᶠ w)) (BI.swapInner.from G.braided)
      (swapInnerᴵ (iface x) (iface y) (iface z) (iface w))
reads-swapInner x y z w =
  reads-∘ {x = (x ⊗ᶠ y) ⊗ᶠ (z ⊗ᶠ w)} {y = x ⊗ᶠ (z ⊗ᶠ (y ⊗ᶠ w))} {z = (x ⊗ᶠ z) ⊗ᶠ (y ⊗ᶠ w)}
    (reads-α⁻¹ x z (y ⊗ᶠ w))
    (reads-∘ {x = (x ⊗ᶠ y) ⊗ᶠ (z ⊗ᶠ w)} {y = x ⊗ᶠ (y ⊗ᶠ (z ⊗ᶠ w))} {z = x ⊗ᶠ (z ⊗ᶠ (y ⊗ᶠ w))}
      (reads-T₁ {x = x} {y = y ⊗ᶠ (z ⊗ᶠ w)} {z = z ⊗ᶠ (y ⊗ᶠ w)}
        (reads-∘ {x = y ⊗ᶠ (z ⊗ᶠ w)} {y = (z ⊗ᶠ y) ⊗ᶠ w} {z = z ⊗ᶠ (y ⊗ᶠ w)}
          (reads-α z y w)
          (reads-∘ {x = y ⊗ᶠ (z ⊗ᶠ w)} {y = (y ⊗ᶠ z) ⊗ᶠ w} {z = (z ⊗ᶠ y) ⊗ᶠ w}
            (reads-sub {x = y ⊗ᶠ z} {y = z ⊗ᶠ y} {z = w} (reads-σ y z)) (reads-α⁻¹ y z w))))
      (reads-α x y (z ⊗ᶠ w)))
