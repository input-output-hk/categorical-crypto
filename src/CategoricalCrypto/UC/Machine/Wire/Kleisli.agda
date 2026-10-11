{-# OPTIONS --safe --without-K --guardedness #-}

-- Kleisli wires: stateless processes routing each letter through a Kleisli map
-- of the base, `Pos A → Dₚ (Pos B)` upwards and `Neg B → Dₚ (Neg A)` downwards.
-- `wireᴹ` is the case of pure maps (`wire-kwire`); a routing that may refuse is
-- `detₚ ∘ f`, which diverges where `f` is undefined.  A Kleisli wire is the G
-- construction's embedding ⌜ pureᴹ u , pureᴹ v ⌝ (`kwire-⌜⌝`), so it composes
-- and tensors by the embedding's laws, applied through qualified names for the
-- reason given in `UC.Machine.Wire`'s header.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Distributive as MD
import Categories.GConstructionEmbedding as GE
import Categories.GConstructionMonoidal as GM

open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (_∘_)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire.Algebra using (wire-id)

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.UC.Machine.Wire.Kleisli where

private
  module ℳ = SymmetricMonoidalCategory (ℳₚ 0ℓ)
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ
  module 𝒢 = Category (𝒢ₚ 0ℓ)
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open MD.MonoidalDistributive (distₚ 0ℓ) using (i₁; i₂; [_,_])
open MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)

private variable A B C D X Y : Iface

kwireStep : (Pos A → Dₚ (Pos B)) → (Neg B → Dₚ (Neg A)) → ⊤ᵛ × (Pos A ⊎ Neg B) → Dₚ (⊤ᵛ × (Neg A ⊎ Pos B))
kwireStep u v (s , inj₁ p) = mapₚ (λ b → s , inj₂ b) (u p)
kwireStep u v (s , inj₂ n) = mapₚ (λ a → s , inj₁ a) (v n)

kwireᴹ : (Pos A → Dₚ (Pos B)) → (Neg B → Dₚ (Neg A)) → Proc A B
kwireᴹ u v = mk Iˢ (kwireStep u v)

------------------------------------------------------------------------
-- The embedding

private
  -- `UC.Machine.Wire`'s reading of the embedding laws at `𝒢ₚ`'s own `_∘_`.
  ⌜⌝-∘ᵂ : {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Set} {u : Machine B⁺ D⁺} {v : Machine D⁻ B⁻}
          {p : Machine A⁺ B⁺} {q : Machine B⁻ A⁻}
        → 𝒢._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} (σᴹ ∘ᴹ (u ⊗ᵉ v)) (σᴹ ∘ᴹ (p ⊗ᵉ q))
          ≈ᴹ (σᴹ ∘ᴹ ((u ∘ᴹ p) ⊗ᵉ (q ∘ᴹ v)))
  ⌜⌝-∘ᵂ = GE.Embed.WithTrace.⌜⌝-∘ ℳ.U ℳ.monoidal (Tracedₚ 0ℓ) (TraceLawsₚ 0ℓ)

  ⌜⌝-⊗ᵂ : {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Set}
          {u : Machine A⁺ B⁺} {v : Machine B⁻ A⁻} {p : Machine D⁺ E⁺} {q : Machine E⁻ D⁻}
        → 𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} {E⁺ , E⁻} (σᴹ ∘ᴹ (u ⊗ᵉ v)) (σᴹ ∘ᴹ (p ⊗ᵉ q))
          ≈ᴹ (σᴹ ∘ᴹ ((u ⊗ᵉ p) ⊗ᵉ (v ⊗ᵉ q)))
  ⌜⌝-⊗ᵂ = GM.⌜⌝-⊗ ℳ.U ℳ.monoidal (Tracedₚ 0ℓ)

  ⌜⌝-resp : {A⁺ A⁻ B⁺ B⁻ : Set} {u u′ : Machine A⁺ B⁺} {v v′ : Machine B⁻ A⁻}
          → u ≈ᴹ u′ → v ≈ᴹ v′ → (σᴹ ∘ᴹ (u ⊗ᵉ v)) ≈ᴹ (σᴹ ∘ᴹ (u′ ⊗ᵉ v′))
  ⌜⌝-resp e₁ e₂ = ∘ᴹ-resp-≈ᴹ reflᴹ (⊗ᵉ-resp-≈ᴹ e₁ e₂)

  kwireStep-copair : (u : Pos A → Dₚ (Pos B)) (v : Neg B → Dₚ (Neg A))
                   → 𝒱._≈_ (kwireStep u v) (𝒱._⊗₁_ 𝒱.id [ 𝒱._∘_ i₂ u , 𝒱._∘_ i₁ v ])
  kwireStep-copair u v (s , inj₁ p) =
    ≈sym (>>=ₚ-identityˡ s _ ⟨≈⟩ >>=ₚ-assoc (u p) _ _ ⟨≈⟩ bindᶠ λ b → >>=ₚ-identityˡ (inj₂ b) _)
  kwireStep-copair u v (s , inj₂ n) =
    ≈sym (>>=ₚ-identityˡ s _ ⟨≈⟩ >>=ₚ-assoc (v n) _ _ ⟨≈⟩ bindᶠ λ a → >>=ₚ-identityˡ (inj₁ a) _)

kwire-⌜⌝ : (u : Pos A → Dₚ (Pos B)) (v : Neg B → Dₚ (Neg A))
         → 𝒫._≈_ {A} {B} (kwireᴹ u v) (σᴹ ∘ᴹ (pureᴹ u ⊗ᵉ pureᴹ v))
kwire-⌜⌝ u v = ≲⇒≈ᴹ (mk-cong (kwireStep-copair u v ○ ⟺ (refl⟩⊗⟨ swap-copair u v))) ○ᴹ ≲⇒≈ᴹ˘ (⌜⌝-pureᴹ u v)
  where open import Categories.Category.Monoidal.Reasoning 𝒱.monoidal using (refl⟩⊗⟨_)
        open 𝒱.HomReasoning using (_○_; ⟺)

------------------------------------------------------------------------
-- The laws

kwire-cong : {u u′ : Pos A → Dₚ (Pos B)} {v v′ : Neg B → Dₚ (Neg A)}
           → (∀ p → u p ≈ₚ u′ p) → (∀ n → v n ≈ₚ v′ n) → 𝒫._≈_ {A} {B} (kwireᴹ u v) (kwireᴹ u′ v′)
kwire-cong eu ev = ≲⇒≈ᴹ (mk-cong λ where
  (s , inj₁ p) → bindˣ (eu p)
  (s , inj₂ n) → bindˣ (ev n))

wire-kwire : (up : Pos A → Pos B) (down : Neg B → Neg A)
           → 𝒫._≈_ {A} {B} (wireᴹ up down) (kwireᴹ (λ p → returnₚ (up p)) (λ n → returnₚ (down n)))
wire-kwire up down = ≲⇒≈ᴹ (mk-cong λ where
  (s , inj₁ p) → ≈sym (>>=ₚ-identityˡ (up p) _)
  (s , inj₂ n) → ≈sym (>>=ₚ-identityˡ (down n) _))

kwire-id : 𝒫._≈_ {A} {A} (kwireᴹ returnₚ returnₚ) (𝒫.id {A})
kwire-id {A} = ⟺ᴹ (wire-kwire {A} {A} (λ p → p) (λ n → n)) ○ᴹ wire-id

kwire-∘ : (u : Pos B → Dₚ (Pos C)) (v : Neg C → Dₚ (Neg B)) (u′ : Pos A → Dₚ (Pos B)) (v′ : Neg B → Dₚ (Neg A))
        → 𝒫._≈_ {A} {C} (𝒫._∘_ {A} {B} {C} (kwireᴹ u v) (kwireᴹ u′ v′))
                        (kwireᴹ (λ a → u′ a >>=ₚ u) (λ n → v n >>=ₚ v′))
kwire-∘ {B} {C} {A} u v u′ v′ =
     𝒫.∘-resp-≈ {A} {B} {C} (kwire-⌜⌝ u v) (kwire-⌜⌝ u′ v′)
  ○ᴹ ⌜⌝-∘ᵂ
  ○ᴹ ⌜⌝-resp (≲⇒≈ᴹ (pureᴹ-∘ u u′)) (≲⇒≈ᴹ (pureᴹ-∘ v′ v))
  ○ᴹ ⟺ᴹ (kwire-⌜⌝ (λ a → u′ a >>=ₚ u) (λ n → v n >>=ₚ v′))

kwire-⊗ : (u : Pos A → Dₚ (Pos B)) (v : Neg B → Dₚ (Neg A)) (p : Pos C → Dₚ (Pos D)) (q : Neg D → Dₚ (Neg C))
        → 𝒫._≈_ {A ⊗ᴵ C} {B ⊗ᴵ D}
            (𝔾._⊗₁_ {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ} {⟦ D ⟧ᴵ} (kwireᴹ u v) (kwireᴹ p q))
            (kwireᴹ [ mapₚ inj₁ ∘ u , mapₚ inj₂ ∘ p ]′ [ mapₚ inj₁ ∘ v , mapₚ inj₂ ∘ q ]′)
kwire-⊗ {A} {B} {C} {D} u v p q =
     𝔾.⊗.F-resp-≈ {(⟦ A ⟧ᴵ , ⟦ C ⟧ᴵ)} {(⟦ B ⟧ᴵ , ⟦ D ⟧ᴵ)} (kwire-⌜⌝ u v , kwire-⌜⌝ p q)
  ○ᴹ ⌜⌝-⊗ᵂ
  ○ᴹ ⌜⌝-resp (≲⇒≈ᴹ (⊗ᵉ-pureᴹ u p)) (≲⇒≈ᴹ (⊗ᵉ-pureᴹ v q))
  ○ᴹ ⟺ᴹ (kwire-⌜⌝ {A ⊗ᴵ C} {B ⊗ᴵ D} [ mapₚ inj₁ ∘ u , mapₚ inj₂ ∘ p ]′ [ mapₚ inj₁ ∘ v , mapₚ inj₂ ∘ q ]′)

------------------------------------------------------------------------
-- Relays of a Kleisli wire

T₁-kwire : (Y : Iface) (u : Pos A → Dₚ (Pos B)) (v : Neg B → Dₚ (Neg A))
         → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y (kwireᴹ u v))
             (kwireᴹ [ returnₚ ∘ inj₁ , mapₚ inj₂ ∘ u ]′ [ returnₚ ∘ inj₁ , mapₚ inj₂ ∘ v ]′)
T₁-kwire Y u v = ≲⇒≈ᴹ (mk-cong λ where
  (s , inj₁ (inj₁ y)) → ≈sym (>>=ₚ-identityˡ (inj₁ y) _)
  (s , inj₁ (inj₂ a)) → map-map (u a) _ _ ⟨≈⟩ ≈sym (map-map (u a) _ _)
  (s , inj₂ (inj₁ y)) → ≈sym (>>=ₚ-identityˡ (inj₁ y) _)
  (s , inj₂ (inj₂ b)) → map-map (v b) _ _ ⟨≈⟩ ≈sym (map-map (v b) _ _))

sub-kwire : (u : Pos X → Dₚ (Pos Y)) (v : Neg Y → Dₚ (Neg X))
          → 𝒫._≈_ {X ⊗ᴵ A} {Y ⊗ᴵ A} (subᴵ {A = A} (kwireᴹ u v))
              (kwireᴹ [ mapₚ inj₁ ∘ u , returnₚ ∘ inj₂ ]′ [ mapₚ inj₁ ∘ v , returnₚ ∘ inj₂ ]′)
sub-kwire u v = ≲⇒≈ᴹ (mk-cong λ where
  (t , inj₁ (inj₁ x)) → map-map (u x) _ _ ⟨≈⟩ ≈sym (map-map (u x) _ _)
  (t , inj₁ (inj₂ a)) → ≈sym (>>=ₚ-identityˡ (inj₂ a) _)
  (t , inj₂ (inj₁ y)) → map-map (v y) _ _ ⟨≈⟩ ≈sym (map-map (v y) _ _)
  (t , inj₂ (inj₂ a)) → ≈sym (>>=ₚ-identityˡ (inj₂ a) _))

kwire-frame : {A′ B′ : Iface} (up : Pos B → Pos B′) (down : Neg B′ → Neg B)
              (up′ : Pos A′ → Pos A) (down′ : Neg A → Neg A′)
              (u : Pos A → Dₚ (Pos B)) (v : Neg B → Dₚ (Neg A))
            → 𝒫._≈_ {A′} {B′}
                (𝒫._∘_ {A′} {B} {B′} (wireᴹ up down)
                  (𝒫._∘_ {A′} {A} {B} (kwireᴹ u v) (wireᴹ up′ down′)))
                (kwireᴹ (λ a → mapₚ up (u (up′ a))) (λ b → mapₚ down′ (v (down b))))
kwire-frame {B = B} {A = A} {A′} {B′} up down up′ down′ u v =
  𝒫.∘-resp-≈ {A′} {B} {B′} (wire-kwire up down)
    (𝒫.∘-resp-≈ {A′} {A} {B} reflᴹ (wire-kwire up′ down′)
      ○ᴹ kwire-∘ u v (returnₚ ∘ up′) (returnₚ ∘ down′))
  ○ᴹ kwire-∘ (returnₚ ∘ up) (returnₚ ∘ down)
       (λ a → returnₚ (up′ a) >>=ₚ u) (λ b → v b >>=ₚ (returnₚ ∘ down′))
  ○ᴹ kwire-cong
    (λ a → bindˣ (>>=ₚ-identityˡ (up′ a) u))
    (λ b → >>=ₚ-identityˡ (down b) (λ n → v n >>=ₚ (returnₚ ∘ down′)))
