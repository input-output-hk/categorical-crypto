{-# OPTIONS --safe --without-K --guardedness #-}

-- G-homs related along interface maps (`Machines.Sim.Relational` at the G
-- construction over `Kl(Dₚ)`): `HSim μA μB f g` says that, up to `_≈ᴹ_` at
-- both ends, a simulation carries `f` to `g` relabelling every letter forwards
-- — positive and negative alike, so the maps are not G-homs.  It is closed
-- under the G composite, a trace whose loop letters are relabelled too
-- (`trace-resp-≲[]`), the G tensor, the identities and the structural isos:
-- `Machines.Collapse`, `Machines.Pure` and `UC.Machine.Dictionary` present each
-- wiring as a relabelling natural in the letters.  Every object implicit is
-- passed, for `UC.Machine.𝒫ᴵ`'s reason.

module CategoricalCrypto.UC.Machine.Relational where

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MU
import Categories.GConstructionMonoidal as GM

open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Base using () renaming (assocˡ to ⊎assocˡ; assocʳ to ⊎assocʳ)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (module MC; module S; module Cat; module T; module K; module KP)
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Behaviour.Congruence
open import CategoricalCrypto.UC.Machine.Dictionary

import CategoricalCrypto.Machines.Collapse as Col

private
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

open MD.MonoidalDistributive (distₚ 0ℓ) using (_+₁_)
open 𝒱.HomReasoning using (_○_; ⟺; refl⟩∘⟨_; _⟩∘⟨refl)

------------------------------------------------------------------------
-- Interface maps and the relation

-- Forward on both polarities.
Map : Set × Set → Set × Set → Set
Map (A⁺ , A⁻) (A′⁺ , A′⁻) = (A⁺ → A′⁺) × (A⁻ → A′⁻)

idᵐ : {A : Set × Set} → Map A A
idᵐ = (λ a → a) , (λ a → a)

infixr 10 _⊗ᵐ_

_⊗ᵐ_ : {A A′ C C′ : Set × Set} → Map A A′ → Map C C′
     → Map ((proj₁ A ⊎ proj₁ C) , (proj₂ A ⊎ proj₂ C)) ((proj₁ A′ ⊎ proj₁ C′) , (proj₂ A′ ⊎ proj₂ C′))
(a⁺ , a⁻) ⊗ᵐ (c⁺ , c⁻) = Sum.map a⁺ c⁺ , Sum.map a⁻ c⁻

private variable
  A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ D⁺ D⁻ A′⁺ A′⁻ B′⁺ B′⁻ C′⁺ C′⁻ D′⁺ D′⁻ V V′ W W′ : Set

-- A G-hom reads `A⁺` and `B⁻` and writes `A⁻` and `B⁺`.
inᵐ : Map (A⁺ , A⁻) (A′⁺ , A′⁻) → Map (B⁺ , B⁻) (B′⁺ , B′⁻) → A⁺ ⊎ B⁻ → A′⁺ ⊎ B′⁻
inᵐ μA μB = Sum.map (proj₁ μA) (proj₂ μB)

outᵐ : Map (A⁺ , A⁻) (A′⁺ , A′⁻) → Map (B⁺ , B⁻) (B′⁺ , B′⁻) → A⁻ ⊎ B⁺ → A′⁻ ⊎ B′⁺
outᵐ μA μB = Sum.map (proj₂ μA) (proj₁ μB)

record HSim (μA : Map (A⁺ , A⁻) (A′⁺ , A′⁻)) (μB : Map (B⁺ , B⁻) (B′⁺ , B′⁻))
            (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : MC.Machine (A′⁺ ⊎ B′⁻) (A′⁻ ⊎ B′⁺)) : Set₁ where
  constructor hsim
  field
    {f₀} : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)
    {g₀} : MC.Machine (A′⁺ ⊎ B′⁻) (A′⁻ ⊎ B′⁺)
    f≈f₀ : f S.≈ᴹ f₀
    sim  : f₀ RS.≲[ K.pureᵏ (inᵐ μA μB) ∣ K.pureᵏ (outᵐ μA μB) ] g₀
    g₀≈g : g₀ S.≈ᴹ g

module _ {μA : Map (A⁺ , A⁻) (A′⁺ , A′⁻)} {μB : Map (B⁺ , B⁻) (B′⁺ , B′⁻)} where

  ≲[]⇒HSim : {f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)} {g : MC.Machine (A′⁺ ⊎ B′⁻) (A′⁻ ⊎ B′⁺)}
           → f RS.≲[ K.pureᵏ (inᵐ μA μB) ∣ K.pureᵏ (outᵐ μA μB) ] g → HSim μA μB f g
  ≲[]⇒HSim s = hsim S.reflᴹ s S.reflᴹ

  HSim-resp : {f f′ : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)} {g g′ : MC.Machine (A′⁺ ⊎ B′⁻) (A′⁻ ⊎ B′⁺)}
            → f′ S.≈ᴹ f → HSim μA μB f g → g S.≈ᴹ g′ → HSim μA μB f′ g′
  HSim-resp e (hsim e₁ s e₂) e′ = hsim (e S.○ᴹ e₁) s (e₂ S.○ᴹ e′)

-- Along identities the relation is the hom equality.
HSim⇒≈ᴹ : {f g : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)} → HSim (idᵐ {A⁺ , A⁻}) (idᵐ {B⁺ , B⁻}) f g → f S.≈ᴹ g
HSim⇒≈ᴹ (hsim e s e′) = e S.○ᴹ S.≲⇒≈ᴹ (RS.≲[id]⇒≲ (RS.≲[]-resp-≈ ids ids s)) S.○ᴹ e′
  where
  ids : {X Y : Set} → 𝒱._≈_ {X ⊎ Y} {X ⊎ Y} (K.pureᵏ (Sum.map (λ a → a) (λ b → b))) 𝒱.id
  ids = K.pureᵏ-cong (λ { (inj₁ _) → refl ; (inj₂ _) → refl }) ○ ⟺ pure-idᵏ

-- Relationally simulated machines run alike against every distinguisher.
relsim⇒≈ᴿ : {X Y : Set} {f g : MC.Machine X Y} → RS.RelSim 𝒱.id 𝒱.id 𝒱.id 𝒱.id f g → f ≈ᴿ g
relsim⇒≈ᴿ r = ≈ᴹ⇒≈ᴿ (RS.relsim⇒≈ᴹ r)

------------------------------------------------------------------------
-- Relabellings

private
  natural : {h : V → W} {h′ : V′ → W′} {μ : V → V′} {ν : W → W′}
          → (∀ v → ν (h v) ≡ h′ (μ v))
          → 𝒱._≈_ (𝒱._∘_ (K.pureᵏ ν) (K.pureᵏ h)) (𝒱._∘_ (K.pureᵏ h′) (K.pureᵏ μ))
  natural {h = h} {h′} {μ} {ν} sq = K.pureᵏ-∘ ν h ○ K.pureᵏ-cong sq ○ ⟺ (K.pureᵏ-∘ h′ μ)

  pure-sim : {h : V → W} {μ : V → V′} {ν : W → W′} {h′ : V′ → W′}
           → (∀ v → ν (h v) ≡ h′ (μ v)) → pureᶠ h RS.≲[ K.pureᵏ μ ∣ K.pureᵏ ν ] pureᶠ h′
  pure-sim sq = RS.pureᴹ-≲[] (natural sq)

  sums : {u : V → V′} {v : W → W′} → 𝒱._≈_ (K.pureᵏ u +₁ K.pureᵏ v) (K.pureᵏ (Sum.map u v))
  sums = +₁-pureᵏ 𝒱.Equiv.refl 𝒱.Equiv.refl

-- A wire commuting with the letter maps.
wire-HSim : {A B A′ B′ : Iface} {up : Pos A → Pos B} {down : Neg B → Neg A}
            {up′ : Pos A′ → Pos B′} {down′ : Neg B′ → Neg A′}
            (μA : Map ⟦ A ⟧ᴵ ⟦ A′ ⟧ᴵ) (μB : Map ⟦ B ⟧ᴵ ⟦ B′ ⟧ᴵ)
          → (∀ a → proj₁ μB (up a) ≡ up′ (proj₁ μA a)) → (∀ b → proj₂ μA (down b) ≡ down′ (proj₂ μB b))
          → HSim μA μB (wireᴹ up down) (wireᴹ up′ down′)
wire-HSim μA μB eu ed = ≲[]⇒HSim (simFn[] (λ s → s) _ _ (λ x → >>=ₚ-identityʳ _) λ where
  (s , inj₁ a) → >>=ₚ-identityˡ _ _ ⟨≈⟩ ≡⇒≈ₚ (cong (λ b → returnₚ (s , inj₂ b)) (eu a))
  (s , inj₂ b) → >>=ₚ-identityˡ _ _ ⟨≈⟩ ≡⇒≈ₚ (cong (λ a → returnₚ (s , inj₁ a)) (ed b)))

------------------------------------------------------------------------
-- Identities and structural isos: wires natural in the letters

HSim-id : (μ : Map (A⁺ , A⁻) (A′⁺ , A′⁻)) → HSim μ μ (𝔾.id {A⁺ , A⁻}) (𝔾.id {A′⁺ , A′⁻})
HSim-id μ = ≲[]⇒HSim (RS.pureᴹ-≲[] ((refl⟩∘⟨ swapᵏ) ○ natural sq ○ (⟺ swapᵏ ⟩∘⟨refl)))
  where
  sq : ∀ v → Sum.map (proj₂ μ) (proj₁ μ) (Sum.swap v) ≡ Sum.swap (Sum.map (proj₁ μ) (proj₂ μ) v)
  sq (inj₁ _) = refl
  sq (inj₂ _) = refl

HSim-λ⇒ : (μ : Map (A⁺ , A⁻) (A′⁺ , A′⁻))
        → HSim (idᵐ {𝔾.unit} ⊗ᵐ μ) μ (𝔾.unitorˡ.from {A⁺ , A⁻}) (𝔾.unitorˡ.from {A′⁺ , A′⁻})
HSim-λ⇒ μ = HSim-resp (S.⟺ᴹ λ⇒-λᴳ) (wire-HSim (idᵐ ⊗ᵐ μ) μ eu (λ _ → refl)) λ⇒-λᴳ
  where
  eu : ∀ x → proj₁ μ (drop⇒ˡ x) ≡ drop⇒ˡ (Sum.map (λ a → a) (proj₁ μ) x)
  eu (inj₁ x) = ⊥-elim x
  eu (inj₂ _) = refl

HSim-λ⇐ : (μ : Map (A⁺ , A⁻) (A′⁺ , A′⁻))
        → HSim μ (idᵐ {𝔾.unit} ⊗ᵐ μ) (𝔾.unitorˡ.to {A⁺ , A⁻}) (𝔾.unitorˡ.to {A′⁺ , A′⁻})
HSim-λ⇐ μ = HSim-resp (S.⟺ᴹ λ⇐-λᴳ) (wire-HSim μ (idᵐ ⊗ᵐ μ) (λ _ → refl) ed) λ⇐-λᴳ
  where
  ed : ∀ x → proj₂ μ (drop⇒ˡ x) ≡ drop⇒ˡ (Sum.map (λ a → a) (proj₂ μ) x)
  ed (inj₁ x) = ⊥-elim x
  ed (inj₂ _) = refl

HSim-ρ⇒ : (μ : Map (A⁺ , A⁻) (A′⁺ , A′⁻))
        → HSim (μ ⊗ᵐ idᵐ {𝔾.unit}) μ (𝔾.unitorʳ.from {A⁺ , A⁻}) (𝔾.unitorʳ.from {A′⁺ , A′⁻})
HSim-ρ⇒ μ = HSim-resp (S.⟺ᴹ ρ⇒-ρᴳ) (wire-HSim (μ ⊗ᵐ idᵐ) μ eu (λ _ → refl)) ρ⇒-ρᴳ
  where
  eu : ∀ x → proj₁ μ (drop⇒ʳ x) ≡ drop⇒ʳ (Sum.map (proj₁ μ) (λ a → a) x)
  eu (inj₁ _) = refl
  eu (inj₂ x) = ⊥-elim x

HSim-ρ⇐ : (μ : Map (A⁺ , A⁻) (A′⁺ , A′⁻))
        → HSim μ (μ ⊗ᵐ idᵐ {𝔾.unit}) (𝔾.unitorʳ.to {A⁺ , A⁻}) (𝔾.unitorʳ.to {A′⁺ , A′⁻})
HSim-ρ⇐ μ = HSim-resp (S.⟺ᴹ ρ⇐-ρᴳ) (wire-HSim μ (μ ⊗ᵐ idᵐ) (λ _ → refl) ed) ρ⇐-ρᴳ
  where
  ed : ∀ x → proj₂ μ (drop⇒ʳ x) ≡ drop⇒ʳ (Sum.map (proj₂ μ) (λ a → a) x)
  ed (inj₁ _) = refl
  ed (inj₂ x) = ⊥-elim x

module _ (μA : Map (A⁺ , A⁻) (A′⁺ , A′⁻)) (μB : Map (B⁺ , B⁻) (B′⁺ , B′⁻))
         (μC : Map (C⁺ , C⁻) (C′⁺ , C′⁻)) where

  HSim-α⇒ : HSim ((μA ⊗ᵐ μB) ⊗ᵐ μC) (μA ⊗ᵐ (μB ⊗ᵐ μC))
                 (𝔾.associator.from {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻})
                 (𝔾.associator.from {A′⁺ , A′⁻} {B′⁺ , B′⁻} {C′⁺ , C′⁻})
  HSim-α⇒ = HSim-resp (S.⟺ᴹ a⇒-α⇒) (wire-HSim ((μA ⊗ᵐ μB) ⊗ᵐ μC) (μA ⊗ᵐ (μB ⊗ᵐ μC)) eu ed) a⇒-α⇒
    where
    eu : ∀ x → proj₁ (μA ⊗ᵐ (μB ⊗ᵐ μC)) (⊎assocʳ x) ≡ ⊎assocʳ (proj₁ ((μA ⊗ᵐ μB) ⊗ᵐ μC) x)
    eu (inj₁ (inj₁ _)) = refl
    eu (inj₁ (inj₂ _)) = refl
    eu (inj₂ _)        = refl
    ed : ∀ x → proj₂ ((μA ⊗ᵐ μB) ⊗ᵐ μC) (⊎assocˡ x) ≡ ⊎assocˡ (proj₂ (μA ⊗ᵐ (μB ⊗ᵐ μC)) x)
    ed (inj₁ _)        = refl
    ed (inj₂ (inj₁ _)) = refl
    ed (inj₂ (inj₂ _)) = refl

  HSim-α⇐ : HSim (μA ⊗ᵐ (μB ⊗ᵐ μC)) ((μA ⊗ᵐ μB) ⊗ᵐ μC)
                 (𝔾.associator.to {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻})
                 (𝔾.associator.to {A′⁺ , A′⁻} {B′⁺ , B′⁻} {C′⁺ , C′⁻})
  HSim-α⇐ = HSim-resp (S.⟺ᴹ a⇐-α⇐) (wire-HSim (μA ⊗ᵐ (μB ⊗ᵐ μC)) ((μA ⊗ᵐ μB) ⊗ᵐ μC) eu ed) a⇐-α⇐
    where
    eu : ∀ x → proj₁ ((μA ⊗ᵐ μB) ⊗ᵐ μC) (⊎assocˡ x) ≡ ⊎assocˡ (proj₁ (μA ⊗ᵐ (μB ⊗ᵐ μC)) x)
    eu (inj₁ _)        = refl
    eu (inj₂ (inj₁ _)) = refl
    eu (inj₂ (inj₂ _)) = refl
    ed : ∀ x → proj₂ (μA ⊗ᵐ (μB ⊗ᵐ μC)) (⊎assocʳ x) ≡ ⊎assocʳ (proj₂ ((μA ⊗ᵐ μB) ⊗ᵐ μC) x)
    ed (inj₁ (inj₁ _)) = refl
    ed (inj₁ (inj₂ _)) = refl
    ed (inj₂ _)        = refl

------------------------------------------------------------------------
-- The composite and the tensor

private
  unfold∘ : (g : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
          → 𝔾._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f
            S.≈ᴹ Col.MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                   (pureᶠ (Col.αᶠ {B⁻} {C⁺} {A⁻} {B⁺}) MC.∘ᴹ ((g T.⊗ᵉ f) MC.∘ᴹ pureᶠ (Col.γᶠ {A⁺} {C⁻} {B⁻} {B⁺})))
  unfold∘ {B⁺ = B⁺} {C⁻ = C⁻} {B⁻ = B⁻} {C⁺ = C⁺} {A⁺ = A⁺} {A⁻ = A⁻} g f =
    S.⟺ᴹ (Col.compose-raw≈∘ᴳ {A⁺} {A⁻} {B⁺} {B⁻} {C⁺} {C⁻} g f)
    S.○ᴹ Col.TC.trace-resp-≈ᴹ {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺} {B⁻ ⊎ B⁺}
           (Cat.∘ᴹ-resp-≈ᴹ (Col.α-pure B⁻ C⁺ A⁻ B⁺) (Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ (Col.γ-pure A⁺ C⁻ B⁻ B⁺)))

  unfold⊗ : (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : MC.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
          → 𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f g
            S.≈ᴹ (pureᶠ (midfn {A⁻} {B⁺} {C⁻} {D⁺}) MC.∘ᴹ ((f T.⊗ᵉ g) MC.∘ᴹ pureᶠ (midfn {A⁺} {C⁺} {B⁻} {D⁻})))
  unfold⊗ {A⁺ = A⁺} {B⁻ = B⁻} {A⁻ = A⁻} {B⁺ = B⁺} {C⁺ = C⁺} {D⁻ = D⁻} {C⁻ = C⁻} {D⁺ = D⁺} f g =
    S.⟺ᴹ (⊗₁ᴳ-raw {A⁺} {A⁻} {B⁺} {B⁻} {C⁺} {C⁻} {D⁺} {D⁻} f g)
    S.○ᴹ Cat.∘ᴹ-resp-≈ᴹ midᴹ-pure (Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ midᴹ-pure)

module _ {μA : Map (A⁺ , A⁻) (A′⁺ , A′⁻)} {μB : Map (B⁺ , B⁻) (B′⁺ , B′⁻)}
         {μC : Map (C⁺ , C⁻) (C′⁺ , C′⁻)} where

  private
    loop : B⁻ ⊎ B⁺ → B′⁻ ⊎ B′⁺
    loop = Sum.map (proj₂ μB) (proj₁ μB)

    γ-sim : pureᶠ (Col.γᶠ {A⁺} {C⁻} {B⁻} {B⁺})
            RS.≲[ K.pureᵏ (Sum.map (inᵐ μA μC) loop) ∣ K.pureᵏ (Sum.map (inᵐ μB μC) (inᵐ μA μB)) ]
            pureᶠ (Col.γᶠ {A′⁺} {C′⁻} {B′⁻} {B′⁺})
    γ-sim = pure-sim λ where
      (inj₁ (inj₁ _)) → refl
      (inj₁ (inj₂ _)) → refl
      (inj₂ (inj₁ _)) → refl
      (inj₂ (inj₂ _)) → refl

    α-sim : pureᶠ (Col.αᶠ {B⁻} {C⁺} {A⁻} {B⁺})
            RS.≲[ K.pureᵏ (Sum.map (outᵐ μB μC) (outᵐ μA μB)) ∣ K.pureᵏ (Sum.map (outᵐ μA μC) loop) ]
            pureᶠ (Col.αᶠ {B′⁻} {C′⁺} {A′⁻} {B′⁺})
    α-sim = pure-sim λ where
      (inj₁ (inj₁ _)) → refl
      (inj₁ (inj₂ _)) → refl
      (inj₂ (inj₁ _)) → refl
      (inj₂ (inj₂ _)) → refl

  HSim-∘ : {g : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)} {g′ : MC.Machine (B′⁺ ⊎ C′⁻) (B′⁻ ⊎ C′⁺)}
           {f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)} {f′ : MC.Machine (A′⁺ ⊎ B′⁻) (A′⁻ ⊎ B′⁺)}
         → HSim μB μC g g′ → HSim μA μB f f′
         → HSim μA μC (𝔾._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f)
                      (𝔾._∘_ {A′⁺ , A′⁻} {B′⁺ , B′⁻} {C′⁺ , C′⁻} g′ f′)
  HSim-∘ {g} {g′} {f} {f′} (hsim {g₀} {g₀′} eg sg eg′) (hsim {f₀} {f₀′} ef sf ef′) = hsim
    (𝔾.∘-resp-≈ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {g} {g₀} {f} {f₀} eg ef S.○ᴹ unfold∘ g₀ f₀)
    (RS.trace-resp-≲[] (KP.structural (outᵐ μA μC)) (KP.structural loop)
      (RS.≲[]-resp-≈ (⟺ sums) (⟺ sums)
        (RS.∘ᴹ-resp-≲[] α-sim (RS.∘ᴹ-resp-≲[] (RS.≲[]-resp-≈ sums sums (RS.⊗ᵉ-resp-≲[] sg sf)) γ-sim))))
    (S.⟺ᴹ (unfold∘ g₀′ f₀′)
     S.○ᴹ 𝔾.∘-resp-≈ {A′⁺ , A′⁻} {B′⁺ , B′⁻} {C′⁺ , C′⁻} {g₀′} {g′} {f₀′} {f′} eg′ ef′)

module _ {μA : Map (A⁺ , A⁻) (A′⁺ , A′⁻)} {μB : Map (B⁺ , B⁻) (B′⁺ , B′⁻)}
         {μC : Map (C⁺ , C⁻) (C′⁺ , C′⁻)} {μD : Map (D⁺ , D⁻) (D′⁺ , D′⁻)} where

  private
    mid-in : pureᶠ (midfn {A⁺} {C⁺} {B⁻} {D⁻})
             RS.≲[ K.pureᵏ (Sum.map (Sum.map (proj₁ μA) (proj₁ μC)) (Sum.map (proj₂ μB) (proj₂ μD)))
                 ∣ K.pureᵏ (Sum.map (inᵐ μA μB) (inᵐ μC μD)) ]
             pureᶠ (midfn {A′⁺} {C′⁺} {B′⁻} {D′⁻})
    mid-in = pure-sim λ where
      (inj₁ (inj₁ _)) → refl
      (inj₁ (inj₂ _)) → refl
      (inj₂ (inj₁ _)) → refl
      (inj₂ (inj₂ _)) → refl

    mid-out : pureᶠ (midfn {A⁻} {B⁺} {C⁻} {D⁺})
              RS.≲[ K.pureᵏ (Sum.map (outᵐ μA μB) (outᵐ μC μD))
                  ∣ K.pureᵏ (Sum.map (Sum.map (proj₂ μA) (proj₂ μC)) (Sum.map (proj₁ μB) (proj₁ μD))) ]
              pureᶠ (midfn {A′⁻} {B′⁺} {C′⁻} {D′⁺})
    mid-out = pure-sim λ where
      (inj₁ (inj₁ _)) → refl
      (inj₁ (inj₂ _)) → refl
      (inj₂ (inj₁ _)) → refl
      (inj₂ (inj₂ _)) → refl

  HSim-⊗ : {f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)} {f′ : MC.Machine (A′⁺ ⊎ B′⁻) (A′⁻ ⊎ B′⁺)}
           {g : MC.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺)} {g′ : MC.Machine (C′⁺ ⊎ D′⁻) (C′⁻ ⊎ D′⁺)}
         → HSim μA μB f f′ → HSim μC μD g g′
         → HSim (μA ⊗ᵐ μC) (μB ⊗ᵐ μD) (𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f g)
                                      (𝔾._⊗₁_ {A′⁺ , A′⁻} {B′⁺ , B′⁻} {C′⁺ , C′⁻} {D′⁺ , D′⁻} f′ g′)
  HSim-⊗ {f} {f′} {g} {g′} (hsim {f₀} {f₀′} ef sf ef′) (hsim {g₀} {g₀′} eg sg eg′) = hsim
    (𝔾.⊗.F-resp-≈ {((A⁺ , A⁻) , (C⁺ , C⁻))} {((B⁺ , B⁻) , (D⁺ , D⁻))} {f , g} {f₀ , g₀} (ef , eg)
     S.○ᴹ unfold⊗ f₀ g₀)
    (RS.∘ᴹ-resp-≲[] mid-out (RS.∘ᴹ-resp-≲[] (RS.≲[]-resp-≈ sums sums (RS.⊗ᵉ-resp-≲[] sf sg)) mid-in))
    (S.⟺ᴹ (unfold⊗ f₀′ g₀′)
     S.○ᴹ 𝔾.⊗.F-resp-≈ {((A′⁺ , A′⁻) , (C′⁺ , C′⁻))} {((B′⁺ , B′⁻) , (D′⁺ , D′⁻))}
                       {f₀′ , g₀′} {f′ , g′} (ef′ , eg′))
