{-# OPTIONS --safe --without-K #-}

-- `Protᴹ`: `Prot` with `_⊗ᵖ_` and relabelling wires (`docs/uc-setup-ssp.md`
-- §3.4).  `⌜_⌝` is contravariant, so each structural iso is the wire of the
-- inverse container map: `λ⇒ = ⌜ ι₂ ⌝`, `ρ⇒ = ⌜ ι₁ ⌝`, `α⇒ = ⌜ αᴵ⁻¹ ⌝`.
--
-- Every law is one simulation.  Interchange (brzuska2018 Lemma 4) pairs the
-- states middle-four and runs one factor's `graft`/`serve` inside the tensor;
-- naturality slides a wire through one factor's step tree; the iso laws,
-- triangle and pentagon are wires against wires, equal by computation once
-- the channel is split.

open import Categories.Category.Core
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor.Bifunctor

open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Level
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category

module CategoricalCrypto.SSP.Protocol.Monoidal where

private variable
  A A′ B B′ C C′ D E F : Iface

------------------------------------------------------------------------
-- The tensor is a bifunctor

⊗ᵖ-identity : wireᵖ {A} ⊗ᵖ wireᵖ {B} ≲ᵖ wireᵖ
⊗ᵖ-identity = ≲ᵖ-const λ where
  _ (inj₁ _) _ → ≈ᶜ-refl
  _ (inj₂ _) _ → ≈ᶜ-refl

module _ (f₂ : Protocol B C) (f₁ : Protocol A B) (g₂ : Protocol B′ C′) (g₁ : Protocol A′ B′) where

  private
    θ⁴ : (St f₂ × St f₁) × (St g₂ × St g₁) → (St f₂ × St g₂) × (St f₁ × St g₁)
    θ⁴ ((a , b) , c , d) = (a , c) , b , d

    module Left (c : St g₂) (d : St g₁) where
      mutual
        graft₁ : {V : Set} (t : Calls B (St f₂ × V)) (b : St f₁)
               → mapᶜ (map₁ θ⁴) (mapᶜ (map₁ (_, c , d)) (reindex ι₁ (graft f₂ f₁ t b)))
                 ≈ᶜ graft (f₂ ⊗ᵖ g₂) (f₁ ⊗ᵖ g₁) (mapᶜ (map₁ (_, c)) (reindex ι₁ t)) (b , d)
        graft₁ (ret _)      b = ret refl
        graft₁ (call y q k) b = serve₁ k (step f₁ b y q)
        graft₁ (coin _ k)   b = coin λ x → graft₁ (k x) b
        graft₁ dead         b = dead

        serve₁ : {V : Set} {y : Ch B} (k : R B y → Calls B (St f₂ × V)) (u : Calls A (St f₁ × R B y))
               → mapᶜ (map₁ θ⁴) (mapᶜ (map₁ (_, c , d)) (reindex ι₁ (serve f₂ f₁ k u)))
                 ≈ᶜ serve (f₂ ⊗ᵖ g₂) (f₁ ⊗ᵖ g₁) {b = inj₁ y}
                      (λ r → mapᶜ (map₁ (_, c)) (reindex ι₁ (k r))) (mapᶜ (map₁ (_, d)) (reindex ι₁ u))
        serve₁ k (ret (b , r))  = graft₁ (k r) b
        serve₁ k (call _ _ k′) = call λ r → serve₁ k (k′ r)
        serve₁ k (coin _ k′)   = coin λ x → serve₁ k (k′ x)
        serve₁ k dead          = dead

    module Right (a : St f₂) (b : St f₁) where
      mutual
        graft₂ : {V : Set} (t : Calls B′ (St g₂ × V)) (d : St g₁)
               → mapᶜ (map₁ θ⁴) (mapᶜ (map₁ ((a , b) ,_)) (reindex ι₂ (graft g₂ g₁ t d)))
                 ≈ᶜ graft (f₂ ⊗ᵖ g₂) (f₁ ⊗ᵖ g₁) (mapᶜ (map₁ (a ,_)) (reindex ι₂ t)) (b , d)
        graft₂ (ret _)      d = ret refl
        graft₂ (call y q k) d = serve₂ k (step g₁ d y q)
        graft₂ (coin _ k)   d = coin λ x → graft₂ (k x) d
        graft₂ dead         d = dead

        serve₂ : {V : Set} {y : Ch B′} (k : R B′ y → Calls B′ (St g₂ × V))
                 (u : Calls A′ (St g₁ × R B′ y))
               → mapᶜ (map₁ θ⁴) (mapᶜ (map₁ ((a , b) ,_)) (reindex ι₂ (serve g₂ g₁ k u)))
                 ≈ᶜ serve (f₂ ⊗ᵖ g₂) (f₁ ⊗ᵖ g₁) {b = inj₂ y}
                      (λ r → mapᶜ (map₁ (a ,_)) (reindex ι₂ (k r))) (mapᶜ (map₁ (b ,_)) (reindex ι₂ u))
        serve₂ k (ret (d , r))  = graft₂ (k r) d
        serve₂ k (call _ _ k′) = call λ r → serve₂ k (k′ r)
        serve₂ k (coin _ k′)   = coin λ x → serve₂ k (k′ x)
        serve₂ k dead          = dead

  ⊗ᵖ-homomorphism : (f₂ ∘ᵖ f₁) ⊗ᵖ (g₂ ∘ᵖ g₁) ≲ᵖ (f₂ ⊗ᵖ g₂) ∘ᵖ (f₁ ⊗ᵖ g₁)
  ⊗ᵖ-homomorphism = record
    { θ = θ⁴ ; θ-init = refl
    ; θ-step = λ where
        ((a , b) , c , d) (inj₁ x) q → Left.graft₁ c d (step f₂ a x q) b
        ((a , b) , c , d) (inj₂ y) q → Right.graft₂ a b (step g₂ c y q) d }

module _ {f f′ : Protocol A B} {g g′ : Protocol C D} (u : f ≲ᵖ f′) (v : g ≲ᵖ g′) where

  ⊗ᵖ-resp-≲ᵖ : f ⊗ᵖ g ≲ᵖ f′ ⊗ᵖ g′
  ⊗ᵖ-resp-≲ᵖ = record
    { θ = map (θ u) (θ v) ; θ-init = cong₂ _,_ (θ-init u) (θ-init v)
    ; θ-step = λ where
        (s , t) (inj₁ b) q → reindex-sim ι₁ (λ _ → refl) (step f s b q) (θ-step u s b q)
        (s , t) (inj₂ d) q → reindex-sim ι₂ (λ _ → refl) (step g t d q) (θ-step v t d q) }

⊗ᵖ-resp-≈ᵖ : {f f′ : Protocol A B} {g g′ : Protocol C D} → f ≈ᵖ f′ → g ≈ᵖ g′ → f ⊗ᵖ g ≈ᵖ f′ ⊗ᵖ g′
⊗ᵖ-resp-≈ᵖ {f′ = f′} {g = g} e₁ e₂ = EqC.transitive _≲ᵖ_
  (EqC.gmap (_⊗ᵖ g) (λ u → ⊗ᵖ-resp-≲ᵖ u ≲ᵖ-refl) e₁) (EqC.gmap (f′ ⊗ᵖ_) (⊗ᵖ-resp-≲ᵖ ≲ᵖ-refl) e₂)

⊗ᵖ-bifunctor : Bifunctor Prot Prot Prot
⊗ᵖ-bifunctor = record
  { F₀           = uncurry _⊗ᴵ_
  ; F₁           = uncurry _⊗ᵖ_
  ; identity     = ≲⇒≈ᵖ ⊗ᵖ-identity
  ; homomorphism = λ {f = f} {g = g} → ≲⇒≈ᵖ (⊗ᵖ-homomorphism (proj₁ g) (proj₁ f) (proj₂ g) (proj₂ f))
  ; F-resp-≈     = uncurry ⊗ᵖ-resp-≈ᵖ
  }

------------------------------------------------------------------------
-- Naturality of the structural wires

module _ (f : Protocol A B) where

  ⌜⌝-natˡ : ⌜ ι₂ {A = C} ⌝ ∘ᵖ (wireᵖ ⊗ᵖ f) ≲ᵖ f ∘ᵖ ⌜ ι₂ ⌝
  ⌜⌝-natˡ = record { θ = θˡ ; θ-init = refl ; θ-step = λ (_ , _ , s) c q → go (step f s c q) }
    where
    θˡ : ⊤ × ⊤ × St f → St f × ⊤
    θˡ (_ , _ , s) = s , tt
    go : {c : Ch B} (t : Calls A (St f × R B c))
       → mapᶜ (map₁ θˡ) (serve ⌜ ι₂ ⌝ (wireᵖ ⊗ᵖ f) {b = inj₂ c} (λ r → ret (tt , r))
                          (mapᶜ (map₁ (tt ,_)) (reindex ι₂ t)))
         ≈ᶜ graft f ⌜ ι₂ ⌝ t tt
    go (ret _)      = ret refl
    go (call _ _ k) = call λ r → go (k r)
    go (coin _ k)   = coin λ b → go (k b)
    go dead         = dead

  ⌜⌝-natʳ : ⌜ ι₁ {B = C} ⌝ ∘ᵖ (f ⊗ᵖ wireᵖ) ≲ᵖ f ∘ᵖ ⌜ ι₁ ⌝
  ⌜⌝-natʳ = record { θ = θʳ ; θ-init = refl ; θ-step = λ (_ , s , _) c q → go (step f s c q) }
    where
    θʳ : ⊤ × St f × ⊤ → St f × ⊤
    θʳ (_ , s , _) = s , tt
    go : {c : Ch B} (t : Calls A (St f × R B c))
       → mapᶜ (map₁ θʳ) (serve ⌜ ι₁ ⌝ (f ⊗ᵖ wireᵖ) {b = inj₁ c} (λ r → ret (tt , r))
                          (mapᶜ (map₁ (_, tt)) (reindex ι₁ t)))
         ≈ᶜ graft f ⌜ ι₁ ⌝ t tt
    go (ret _)      = ret refl
    go (call _ _ k) = call λ r → go (k r)
    go (coin _ k)   = coin λ b → go (k b)
    go dead         = dead

module _ (f : Protocol A B) (g : Protocol C D) (h : Protocol E F) where

  private
    θα : ⊤ × (St f × St g) × St h → (St f × St g × St h) × ⊤
    θα (_ , (a , b) , c) = (a , b , c) , tt

    module Slide (a : St f) (b : St g) (c : St h) where
      go₁ : {x : Ch B} (t : Calls A (St f × R B x))
          → mapᶜ (map₁ θα) (serve ⌜ αᴵ⁻¹ ⌝ ((f ⊗ᵖ g) ⊗ᵖ h) {b = inj₁ (inj₁ x)} (λ r → ret (tt , r))
                              (mapᶜ (map₁ (_, c)) (reindex ι₁ (mapᶜ (map₁ (_, b)) (reindex ι₁ t)))))
            ≈ᶜ graft (f ⊗ᵖ g ⊗ᵖ h) ⌜ αᴵ⁻¹ ⌝ (mapᶜ (map₁ (_, b , c)) (reindex ι₁ t)) tt
      go₁ (ret _)      = ret refl
      go₁ (call _ _ k) = call λ r → go₁ (k r)
      go₁ (coin _ k)   = coin λ x → go₁ (k x)
      go₁ dead         = dead

      go₂ : {y : Ch D} (t : Calls C (St g × R D y))
          → mapᶜ (map₁ θα) (serve ⌜ αᴵ⁻¹ ⌝ ((f ⊗ᵖ g) ⊗ᵖ h) {b = inj₁ (inj₂ y)} (λ r → ret (tt , r))
                              (mapᶜ (map₁ (_, c)) (reindex ι₁ (mapᶜ (map₁ (a ,_)) (reindex ι₂ t)))))
            ≈ᶜ graft (f ⊗ᵖ g ⊗ᵖ h) ⌜ αᴵ⁻¹ ⌝
                 (mapᶜ (map₁ (a ,_)) (reindex ι₂ (mapᶜ (map₁ (_, c)) (reindex ι₁ t)))) tt
      go₂ (ret _)      = ret refl
      go₂ (call _ _ k) = call λ r → go₂ (k r)
      go₂ (coin _ k)   = coin λ x → go₂ (k x)
      go₂ dead         = dead

      go₃ : {z : Ch F} (t : Calls E (St h × R F z))
          → mapᶜ (map₁ θα) (serve ⌜ αᴵ⁻¹ ⌝ ((f ⊗ᵖ g) ⊗ᵖ h) {b = inj₂ z} (λ r → ret (tt , r))
                              (mapᶜ (map₁ ((a , b) ,_)) (reindex ι₂ t)))
            ≈ᶜ graft (f ⊗ᵖ g ⊗ᵖ h) ⌜ αᴵ⁻¹ ⌝
                 (mapᶜ (map₁ (a ,_)) (reindex ι₂ (mapᶜ (map₁ (b ,_)) (reindex ι₂ t)))) tt
      go₃ (ret _)      = ret refl
      go₃ (call _ _ k) = call λ r → go₃ (k r)
      go₃ (coin _ k)   = coin λ x → go₃ (k x)
      go₃ dead         = dead

  ⌜⌝-natα : ⌜ αᴵ⁻¹ ⌝ ∘ᵖ ((f ⊗ᵖ g) ⊗ᵖ h) ≲ᵖ (f ⊗ᵖ g ⊗ᵖ h) ∘ᵖ ⌜ αᴵ⁻¹ ⌝
  ⌜⌝-natα = record
    { θ = θα ; θ-init = refl
    ; θ-step = λ where
        (_ , (a , b) , c) (inj₁ x)        q → Slide.go₁ a b c (step f a x q)
        (_ , (a , b) , c) (inj₂ (inj₁ y)) q → Slide.go₂ a b c (step g b y q)
        (_ , (a , b) , c) (inj₂ (inj₂ z)) q → Slide.go₃ a b c (step h c z q) }

------------------------------------------------------------------------
-- The monoidal category

Protᴹ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
Protᴹ = record
  { U        = Prot
  ; monoidal = monoidalHelper Prot record
    { ⊗               = ⊗ᵖ-bifunctor
    ; unit            = unitᴵ
    ; unitorˡ         = record
      { from = ⌜ ι₂ ⌝ ; to = ⌜ λᴵ ⌝
      ; iso  = record
        { isoˡ = ≲⇒≈ᵖ (≲ᵖ-const λ where
            _ (inj₁ ()) _
            _ (inj₂ _)  _ → ≈ᶜ-refl)
        ; isoʳ = ≲⇒≈ᵖ (≲ᵖ-const λ _ _ _ → ≈ᶜ-refl) } }
    ; unitorʳ         = record
      { from = ⌜ ι₁ ⌝ ; to = ⌜ ρᴵ ⌝
      ; iso  = record
        { isoˡ = ≲⇒≈ᵖ (≲ᵖ-const λ where
            _ (inj₁ _)  _ → ≈ᶜ-refl
            _ (inj₂ ()) _)
        ; isoʳ = ≲⇒≈ᵖ (≲ᵖ-const λ _ _ _ → ≈ᶜ-refl) } }
    ; associator      = record
      { from = ⌜ αᴵ⁻¹ ⌝ ; to = ⌜ αᴵ ⌝
      ; iso  = record
        { isoˡ = ≲⇒≈ᵖ (≲ᵖ-const λ where
            _ (inj₁ (inj₁ _)) _ → ≈ᶜ-refl
            _ (inj₁ (inj₂ _)) _ → ≈ᶜ-refl
            _ (inj₂ _)        _ → ≈ᶜ-refl)
        ; isoʳ = ≲⇒≈ᵖ (≲ᵖ-const λ where
            _ (inj₁ _)        _ → ≈ᶜ-refl
            _ (inj₂ (inj₁ _)) _ → ≈ᶜ-refl
            _ (inj₂ (inj₂ _)) _ → ≈ᶜ-refl) } }
    ; unitorˡ-commute = λ {f = f} → ≲⇒≈ᵖ (⌜⌝-natˡ f)
    ; unitorʳ-commute = λ {f = f} → ≲⇒≈ᵖ (⌜⌝-natʳ f)
    ; assoc-commute   = λ {f = f} {g = g} {h = h} → ≲⇒≈ᵖ (⌜⌝-natα f g h)
    ; triangle        = ≲⇒≈ᵖ (≲ᵖ-const λ where
        _ (inj₁ _) _ → ≈ᶜ-refl
        _ (inj₂ _) _ → ≈ᶜ-refl)
    ; pentagon        = ≲⇒≈ᵖ (≲ᵖ-const λ where
        _ (inj₁ _)               _ → ≈ᶜ-refl
        _ (inj₂ (inj₁ _))        _ → ≈ᶜ-refl
        _ (inj₂ (inj₂ (inj₁ _))) _ → ≈ᶜ-refl
        _ (inj₂ (inj₂ (inj₂ _))) _ → ≈ᶜ-refl)
    }
  }
