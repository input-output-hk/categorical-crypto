{-# OPTIONS --safe --without-K #-}

-- The coherence library the machine layer runs on: how the two actions of a
-- paired state (`onL`/`onR`) interact with the state shuffles, with each other,
-- and with the point and discard of a paired state.
--
-- Two facts carry almost everything below.  `swp` is natural in all three of
-- its factors (`swp-natural`, `swp-natural′`, `swp-nat`), which is why an
-- action on the interface alone slides through `onL` untouched.  And the state
-- braiding exchanges the two actions (`σ-onL`/`σ-onR`); its proof is the one
-- place genuinely braided content appears, since the braiding there crosses a
-- whole block and has to be split by the hexagon (`σ-splitˡ`/`σ-splitʳ`).

open import Categories.Category.Monoidal.Bundle
  using (MonoidalCategory; SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Product.Base using (_,_)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Machines.Frame {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open Core 𝒱
open Equiv
open MonoidalUtilities.Shorthands monoidal

open import Categories.Category.Monoidal.Properties monoidal
  using (coherence₁; coherence₂; coherence₃)
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U
open BraidedProps braided using (braiding-coherence)
open MonoidalUtilities monoidal using (triangle-inv)

private variable A B K₁ K₂ L P Q R S W W′ X Y Z : Obj

-- The reflection frontend wants the `MonoidalCategory` bundle.
𝕄 : MonoidalCategory o ℓ e
𝕄 = record { U = U ; monoidal = monoidal }

------------------------------------------------------------------------
-- Shuffles and paddings

-- `id ⊗₁ _` preserves invertibility.
pad-inv : {h : X ⇒ Y} {h⁻ : Y ⇒ X} → h ∘ h⁻ ≈ id → id {L} ⊗₁ h ∘ id ⊗₁ h⁻ ≈ id
pad-inv e = merge₂ˡ ○ refl⟩⊗⟨ e ○ ⊗.identity

σ-pad-inv : id {L} ⊗₁ σ⇒ ∘ id ⊗₁ σ⇒ ≈ id {L ⊗₀ (Q ⊗₀ X)}
σ-pad-inv = pad-inv commutative

swp-swp : swp ∘ swp ≈ id {(P ⊗₀ Q) ⊗₀ X}
swp-swp = center (cancelʳ associator.isoʳ) ○ refl⟩∘⟨ cancelˡ σ-pad-inv ○ associator.isoˡ

σ⊗-inv : σ⇒ {P} {Q} ⊗₁ id {A} ∘ σ⇒ {Q} {P} ⊗₁ id ≈ id
σ⊗-inv = merge₁ˡ ○ (commutative ⟩⊗⟨refl) ○ ⊗.identity

-- Both sides are `h ⊗₁ s`: a generator never sees its padding.
pad-transport : (h : K₁ ⇒ K₂) (s : W ⇒ W′) → id ⊗₁ s ∘ h ⊗₁ id ≈ h ⊗₁ id ∘ id ⊗₁ s
pad-transport _ _ = parallel id-comm-sym id-comm

-- A left padding is a braided right padding, so a left-padded conjugate is a
-- right-padded one.
pad-braid : (L : Obj) (h : K₁ ⇒ K₂) → id {L} ⊗₁ h ≈ σ⇒ ∘ h ⊗₁ id ∘ σ⇒
pad-braid L h = insertˡ commutative ○ (refl⟩∘⟨ braiding.⇒.commute (id , h))

unbraid : (h : K₁ ⇒ K₂) {i : A ⇒ L ⊗₀ K₁} {o : L ⊗₀ K₂ ⇒ B}
        → o ∘ id ⊗₁ h ∘ i ≈ (o ∘ σ⇒) ∘ h ⊗₁ id ∘ (σ⇒ ∘ i)
unbraid {L = L} h = (refl⟩∘⟨ pad-braid L h ⟩∘⟨refl) ○ (refl⟩∘⟨ assoc) ○ sym-assoc
                  ○ (refl⟩∘⟨ assoc)

-- The hexagon, solved for a *block* crossing: a crossing block is the only
-- genuinely braided content the interchanges below need.
σ-splitˡ : σ⇒ {P} {Q ⊗₀ X} ≈ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐
σ-splitˡ {P} {Q} {X} = insertʳ associator.isoʳ
                     ○ (⟺ (cancelˡ associator.isoˡ) ⟩∘⟨refl)
                     ○ ((refl⟩∘⟨ ⟺ (hexagon₁ {P} {Q} {X})) ⟩∘⟨refl)

σ-splitʳ : σ⇒ {P ⊗₀ Q} {X} ≈ α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)
σ-splitʳ {P} {Q} {X} = insertˡ associator.isoʳ
                     ○ (refl⟩∘⟨ insertʳ associator.isoˡ)
                     ○ (refl⟩∘⟨ (⟺ (hexagon₂ {P} {Q} {X}) ⟩∘⟨refl))

------------------------------------------------------------------------
-- `swp` is natural in all three factors

swp-natural : (g : X ⇒ Y) → swp {P} {Q} ∘ id ⊗₁ g ≈ (id ⊗₁ g) ⊗₁ id ∘ swp
swp-natural g = begin
  (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ id ⊗₁ g              ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ id ⊗₁ g))              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ step-α ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (id ⊗₁ (id ⊗₁ g) ∘ α⇒))      ≈⟨ refl⟩∘⟨ pullˡ step-σ ⟩
  α⇐ ∘ ((id ⊗₁ (g ⊗₁ id) ∘ id ⊗₁ σ⇒) ∘ α⇒)      ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ (g ⊗₁ id) ∘ (id ⊗₁ σ⇒ ∘ α⇒))      ≈⟨ pullˡ assoc-commute-to ⟩
  ((id ⊗₁ g) ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ σ⇒ ∘ α⇒)      ≈⟨ assoc ⟩
  (id ⊗₁ g) ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒))      ∎
  where
    step-α : α⇒ ∘ id ⊗₁ g ≈ id ⊗₁ (id ⊗₁ g) ∘ α⇒
    step-α = (refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from

    step-σ : id ⊗₁ σ⇒ ∘ id ⊗₁ (id ⊗₁ g) ≈ id ⊗₁ (g ⊗₁ id) ∘ id ⊗₁ σ⇒
    step-σ = merge₂ʳ ○ refl⟩⊗⟨ braiding.⇒.commute (id , g) ○ split₂ʳ

swp-natural′ : (g : X ⇒ Y) → swp {P} {Y} {Q} ∘ (id ⊗₁ g) ⊗₁ id ≈ id ⊗₁ g ∘ swp
swp-natural′ g = begin
  swp ∘ (id ⊗₁ g) ⊗₁ id                 ≈⟨ refl⟩∘⟨ insertʳ swp-swp ⟩
  swp ∘ (((id ⊗₁ g) ⊗₁ id ∘ swp) ∘ swp) ≈˘⟨ refl⟩∘⟨ swp-natural g ⟩∘⟨refl ⟩
  swp ∘ ((swp ∘ id ⊗₁ g) ∘ swp)         ≈⟨ refl⟩∘⟨ assoc ⟩
  swp ∘ (swp ∘ (id ⊗₁ g ∘ swp))         ≈⟨ cancelˡ swp-swp ⟩
  id ⊗₁ g ∘ swp                         ∎

swp-nat : (u : P ⇒ R) (v : Q ⇒ Z) (t : X ⇒ Y)
        → (u ⊗₁ t) ⊗₁ v ∘ swp ≈ swp ∘ (u ⊗₁ v) ⊗₁ t
swp-nat u v t = begin
  (u ⊗₁ t) ⊗₁ v ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ○ assoc ⟩
  α⇐ ∘ (u ⊗₁ (t ⊗₁ v) ∘ (id ⊗₁ σ⇒ ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm (⟺ (braiding.⇒.commute (v , t)))) ⟩
  α⇐ ∘ ((id ⊗₁ σ⇒ ∘ u ⊗₁ (v ⊗₁ t)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (u ⊗₁ (v ⊗₁ t) ∘ α⇒))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ (u ⊗₁ v) ⊗₁ t))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ (u ⊗₁ v) ⊗₁ t  ∎

------------------------------------------------------------------------
-- The two state actions: functoriality and congruence

onL-∘ : {h₂ : P ⊗₀ Y ⇒ P ⊗₀ B} {h₁ : P ⊗₀ X ⇒ P ⊗₀ Y}
      → onL {Q = Q} (h₂ ∘ h₁) ≈ onL h₂ ∘ onL h₁
onL-∘ = (refl⟩∘⟨ split₁ˡ ⟩∘⟨refl) ○ (refl⟩∘⟨ insertInner swp-swp ⟩∘⟨refl)
      ○ (refl⟩∘⟨ assoc) ○ sym-assoc ○ (refl⟩∘⟨ assoc)

onRᵍ-∘ : {T V : Obj} {h₂ : R ⊗₀ Y ⇒ T ⊗₀ V} {h₁ : Q ⊗₀ X ⇒ R ⊗₀ Y}
       → onRᵍ {P = P} (h₂ ∘ h₁) ≈ onRᵍ h₂ ∘ onRᵍ h₁
onRᵍ-∘ = (refl⟩∘⟨ split₂ʳ ⟩∘⟨refl) ○ (refl⟩∘⟨ insertInner associator.isoʳ ⟩∘⟨refl)
       ○ (refl⟩∘⟨ assoc) ○ sym-assoc ○ (refl⟩∘⟨ assoc)

onL-cong : {h h′ : P ⊗₀ X ⇒ P ⊗₀ Y} → h ≈ h′ → onL {Q = Q} h ≈ onL h′
onL-cong e = refl⟩∘⟨ e ⟩⊗⟨refl ⟩∘⟨refl

onR-cong : {h h′ : Q ⊗₀ X ⇒ Q ⊗₀ Y} → h ≈ h′ → onR {P = P} h ≈ onR h′
onR-cong e = refl⟩∘⟨ refl⟩⊗⟨ e ⟩∘⟨refl

onL-id : onL {Q = Q} (id {P ⊗₀ A}) ≈ id
onL-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ swp-swp

onR-id : onR {P = P} (id {Q ⊗₀ A}) ≈ id
onR-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoˡ

-- An action on the interface alone passes through either action untouched.
onL-str : (g : X ⇒ Y) → onL {Q = Q} (id {P} ⊗₁ g) ≈ id ⊗₁ g
onL-str g = (refl⟩∘⟨ (⟺ (swp-natural g))) ○ pullˡ swp-swp ○ identityˡ

onRᵍ-id⊗ : (h : W ⇒ W′) → onRᵍ {Q = Q} {P = P} (id ⊗₁ h) ≈ id ⊗₁ h
onRᵍ-id⊗ h = pullˡ assoc-commute-to ○ cancelʳ associator.isoˡ ○ (⊗.identity ⟩⊗⟨refl)

-- An action on one factor of a paired state passes through `onRᵍ` as itself.
onRᵍ-⊗id : (h : W ⇒ W′) → onRᵍ {P = P} (h ⊗₁ id {X}) ≈ (id ⊗₁ h) ⊗₁ id
onRᵍ-⊗id _ = pullˡ assoc-commute-to ○ cancelʳ associator.isoˡ

------------------------------------------------------------------------
-- Both actions carry a square natural in the interface

onL-branch : {k : P ⊗₀ A ⇒ P ⊗₀ B} {t : P ⊗₀ X ⇒ P ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k
           → onL {Q = Q} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onL k
onL-branch {j = j} {j′} e = begin
  (swp ∘ (_ ⊗₁ id ∘ swp)) ∘ id ⊗₁ j        ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  swp ∘ (_ ⊗₁ id ∘ (swp ∘ id ⊗₁ j))        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swp-natural j ⟩
  swp ∘ (_ ⊗₁ id ∘ ((id ⊗₁ j) ⊗₁ id ∘ swp))
    ≈⟨ refl⟩∘⟨ pullˡ (merge₁ˡ ○ e ⟩⊗⟨refl ○ split₁ˡ) ⟩
  swp ∘ (((id ⊗₁ j′) ⊗₁ id ∘ _ ⊗₁ id) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ○ pullˡ (swp-natural′ j′) ○ assoc ⟩
  id ⊗₁ j′ ∘ (swp ∘ (_ ⊗₁ id ∘ swp))       ∎

onR-branch : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} {t : Q ⊗₀ X ⇒ Q ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k
           → onR {P = P} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onR k
onR-branch {j = j} {j′} e = begin
  (α⇐ ∘ (id ⊗₁ _ ∘ α⇒)) ∘ id ⊗₁ j          ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (α⇒ ∘ id ⊗₁ j))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from) ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (id ⊗₁ (id ⊗₁ j) ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ e ○ split₂ʳ) ⟩
  α⇐ ∘ ((id ⊗₁ (id ⊗₁ j′) ∘ id ⊗₁ _) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc
       ○ pullˡ (assoc-commute-to ○ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl) ○ assoc ⟩
  id ⊗₁ j′ ∘ (α⇐ ∘ (id ⊗₁ _ ∘ α⇒))         ∎

------------------------------------------------------------------------
-- A state map on each factor conjugates both actions

onL-sim : {v : P ⇒ R} {w : Q ⇒ Z} {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X ⇒ R ⊗₀ Y}
        → v ⊗₁ id ∘ k ≈ k′ ∘ v ⊗₁ id
        → (v ⊗₁ w) ⊗₁ id {Y} ∘ onL k ≈ onL k′ ∘ (v ⊗₁ w) ⊗₁ id {X}
onL-sim {v = v} {w} e = begin
  (v ⊗₁ w) ⊗₁ id ∘ (swp ∘ (_ ⊗₁ id ∘ swp))
    ≈⟨ pullˡ (swp-nat v id w) ○ assoc ⟩
  swp ∘ ((v ⊗₁ id) ⊗₁ w ∘ (_ ⊗₁ id ∘ swp))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel e id-comm) ⟩
  swp ∘ ((_ ⊗₁ id ∘ (v ⊗₁ id) ⊗₁ w) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  swp ∘ (_ ⊗₁ id ∘ ((v ⊗₁ id) ⊗₁ w ∘ swp))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swp-nat v w id ⟩
  swp ∘ (_ ⊗₁ id ∘ (swp ∘ (v ⊗₁ w) ⊗₁ id))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (swp ∘ (_ ⊗₁ id ∘ swp)) ∘ (v ⊗₁ w) ⊗₁ id  ∎

onR-sim : {v : P ⇒ R} {w : Q ⇒ Z} {k : Q ⊗₀ X ⇒ Q ⊗₀ Y} {k′ : Z ⊗₀ X ⇒ Z ⊗₀ Y}
        → w ⊗₁ id ∘ k ≈ k′ ∘ w ⊗₁ id
        → (v ⊗₁ w) ⊗₁ id {Y} ∘ onR k ≈ onR k′ ∘ (v ⊗₁ w) ⊗₁ id {X}
onR-sim {v = v} {w} e = begin
  (v ⊗₁ w) ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ _ ∘ α⇒))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ○ assoc ⟩
  α⇐ ∘ (v ⊗₁ (w ⊗₁ id) ∘ (id ⊗₁ _ ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm e) ⟩
  α⇐ ∘ ((id ⊗₁ _ ∘ v ⊗₁ (w ⊗₁ id)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (v ⊗₁ (w ⊗₁ id) ∘ α⇒))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (α⇒ ∘ (v ⊗₁ w) ⊗₁ id))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ _ ∘ α⇒)) ∘ (v ⊗₁ w) ⊗₁ id  ∎

------------------------------------------------------------------------
-- The state braiding exchanges the two actions

σ-onR : {k : Q ⊗₀ A ⇒ Q ⊗₀ B}
      → σ⇒ {P} {Q} ⊗₁ id {B} ∘ onR {P = P} k ≈ onL {Q = P} k ∘ σ⇒ ⊗₁ id {A}
σ-onR {k = k} = begin
  σ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))              ≈⟨ sym-assoc ⟩
  (σ⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ k ∘ α⇒)              ≈⟨ unbraid k ⟩
  ((σ⇒ ⊗₁ id ∘ α⇐) ∘ σ⇒) ∘ (k ⊗₁ id ∘ (σ⇒ ∘ α⇒))
    ≈⟨ out ⟩∘⟨ (refl⟩∘⟨ inn) ⟩
  swp ∘ (k ⊗₁ id ∘ (swp ∘ σ⇒ ⊗₁ id))            ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  swp ∘ ((k ⊗₁ id ∘ swp) ∘ σ⇒ ⊗₁ id)            ≈⟨ sym-assoc ⟩
  (swp ∘ (k ⊗₁ id ∘ swp)) ∘ σ⇒ ⊗₁ id            ∎
  where
    out : (σ⇒ {P} {Q} ⊗₁ id {B} ∘ α⇐) ∘ σ⇒ ≈ swp
    out = (refl⟩∘⟨ σ-splitʳ) ○ cancelInner associator.isoˡ
        ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ assoc) ○ cancelˡ σ⊗-inv

    inn : σ⇒ {P} {Q ⊗₀ A} ∘ α⇒ ≈ swp ∘ σ⇒ ⊗₁ id
    inn = (σ-splitˡ ⟩∘⟨refl) ○ cancelʳ associator.isoˡ
        ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc

σ-onL : {k : P ⊗₀ A ⇒ P ⊗₀ B}
      → σ⇒ {P} {Q} ⊗₁ id {B} ∘ onL {Q = Q} k ≈ onR {P = Q} k ∘ σ⇒ ⊗₁ id {A}
σ-onL = (refl⟩∘⟨ ⟺ (cancelʳ σ⊗-inv)) ○ (refl⟩∘⟨ ⟺ σ-onR ⟩∘⟨refl)
      ○ (refl⟩∘⟨ assoc) ○ cancelˡ σ⊗-inv

-- The braiding is trivial on the unit, so it leaves a paired point and a
-- paired discard alone.
σ-unit : σ⇒ {unit} {unit} ≈ id
σ-unit = insertˡ unitorˡ.isoˡ ○ (refl⟩∘⟨ (braiding-coherence ○ ⟺ coherence₃))
       ○ unitorˡ.isoˡ

------------------------------------------------------------------------
-- Collapsing a trivial state factor

ρα-λ : ρ⇒ {P} ⊗₁ id {A} ∘ α⇐ ≈ id ⊗₁ λ⇒
ρα-λ = ((⟺ triangle) ⟩∘⟨refl) ○ cancelʳ associator.isoʳ

αρ-λ : α⇒ ∘ ρ⇐ {P} ⊗₁ id {A} ≈ id ⊗₁ λ⇐
αρ-λ = (refl⟩∘⟨ (⟺ triangle-inv)) ○ cancelˡ associator.isoʳ

ρ-swp : ρ⇒ {P} ⊗₁ id {A} ∘ swp ≈ ρ⇒
ρ-swp = pullˡ ρα-λ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ braiding-coherence) ○ coherence₂

-- Discarding the second factor of a paired state.
dsc : (Q ⇒ unit) → P ⊗₀ Q ⇒ P
dsc d = ρ⇒ ∘ id ⊗₁ d

dsc-swp : {d : Q ⇒ unit} → dsc {P = P} d ⊗₁ id {A} ∘ swp ≈ ρ⇒ ∘ id ⊗₁ d
dsc-swp {d = d} = (split₁ˡ ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ ⟺ (swp-natural d))
                ○ pullˡ ρ-swp

-- `onL` does not see the second state factor, so closing it passes through.
discard-onL : {d : Q ⇒ unit} {k : P ⊗₀ A ⇒ P ⊗₀ B}
            → dsc d ⊗₁ id {B} ∘ onL k ≈ k ∘ dsc d ⊗₁ id {A}
discard-onL {d = d} {k} = begin
  dsc d ⊗₁ id ∘ (swp ∘ (k ⊗₁ id ∘ swp))  ≈⟨ pullˡ dsc-swp ⟩
  (ρ⇒ ∘ id ⊗₁ d) ∘ (k ⊗₁ id ∘ swp)       ≈⟨ assoc ⟩
  ρ⇒ ∘ (id ⊗₁ d ∘ (k ⊗₁ id ∘ swp))       ≈⟨ refl⟩∘⟨ pullˡ (pad-transport k d) ⟩
  ρ⇒ ∘ ((k ⊗₁ id ∘ id ⊗₁ d) ∘ swp)       ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ∘ (k ⊗₁ id ∘ (id ⊗₁ d ∘ swp))       ≈⟨ pullˡ unitorʳ-commute-from ⟩
  (k ∘ ρ⇒) ∘ (id ⊗₁ d ∘ swp)             ≈⟨ assoc ⟩
  k ∘ (ρ⇒ ∘ (id ⊗₁ d ∘ swp))             ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  k ∘ ((ρ⇒ ∘ id ⊗₁ d) ∘ swp)             ≈˘⟨ refl⟩∘⟨ dsc-swp ⟩∘⟨refl ⟩
  k ∘ ((dsc d ⊗₁ id ∘ swp) ∘ swp)        ≈⟨ refl⟩∘⟨ cancelʳ swp-swp ⟩
  k ∘ dsc d ⊗₁ id                        ∎

-- A trivial left state factor sees an `onR` action as the action itself…
onR-collapseˡ : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} → λ⇒ ⊗₁ id ∘ onR k ≈ k ∘ λ⇒ ⊗₁ id
onR-collapseˡ {k = k} = begin
  λ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))   ≈˘⟨ coherence₁ ⟩∘⟨refl ⟩
  (λ⇒ ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))  ≈⟨ cancelInner associator.isoʳ ⟩
  λ⇒ ∘ (id ⊗₁ k ∘ α⇒)                ≈⟨ pullˡ unitorˡ-commute-from ○ assoc ⟩
  k ∘ (λ⇒ ∘ α⇒)                      ≈⟨ refl⟩∘⟨ coherence₁ ⟩
  k ∘ λ⇒ ⊗₁ id                       ∎

-- …and a trivial right one an `onL` action, which is `discard-onL` at `id`.
onL-collapseʳ : {k : P ⊗₀ A ⇒ P ⊗₀ B} → ρ⇒ ⊗₁ id ∘ onL k ≈ k ∘ ρ⇒ ⊗₁ id
onL-collapseʳ {P = P} =
    ((⟺ dsc-id) ⟩⊗⟨refl ⟩∘⟨refl) ○ discard-onL ○ (refl⟩∘⟨ dsc-id ⟩⊗⟨refl)
  where
    dsc-id : dsc (id {unit}) ≈ ρ⇒ {P}
    dsc-id = elimʳ ⊗.identity

------------------------------------------------------------------------
-- The point and the discard of a paired state

⊛-discard₂ : (S T S′ T′ : State) {u : obj S ⇒ obj T} {v : obj S′ ⇒ obj T′}
           → discard T ∘ u ≈ discard S → discard T′ ∘ v ≈ discard S′
           → discard (T ⊛ T′) ∘ u ⊗₁ v ≈ discard (S ⊛ S′)
⊛-discard₂ _ _ _ _ e₁ e₂ = assoc ○ (refl⟩∘⟨ (⟺ ⊗.homomorphism ○ (e₁ ⟩⊗⟨ e₂)))

⊛-point₂ : (S T S′ T′ : State) {u : obj S ⇒ obj T} {v : obj S′ ⇒ obj T′}
         → u ∘ point S ≈ point T → v ∘ point S′ ≈ point T′
         → u ⊗₁ v ∘ point (S ⊛ S′) ≈ point (T ⊛ T′)
⊛-point₂ _ _ _ _ e₁ e₂ = pullˡ (⟺ ⊗.homomorphism ○ (e₁ ⟩⊗⟨ e₂))

⊛-discard : (S T R : State) {u : obj S ⇒ obj T} → discard T ∘ u ≈ discard S
          → discard (T ⊛ R) ∘ u ⊗₁ id ≈ discard (S ⊛ R)
⊛-discard S T R e = ⊛-discard₂ S T R R e identityʳ

⊛-point : (S T R : State) {u : obj S ⇒ obj T} → u ∘ point S ≈ point T
        → u ⊗₁ id ∘ point (S ⊛ R) ≈ point (T ⊛ R)
⊛-point S T R e = ⊛-point₂ S T R R e identityˡ

⊛-discardʳ : (R S T : State) {u : obj S ⇒ obj T} → discard T ∘ u ≈ discard S
           → discard (R ⊛ T) ∘ id ⊗₁ u ≈ discard (R ⊛ S)
⊛-discardʳ R S T e = ⊛-discard₂ R R S T identityʳ e

⊛-pointʳ : (R S T : State) {u : obj S ⇒ obj T} → u ∘ point S ≈ point T
         → id ⊗₁ u ∘ point (R ⊛ S) ≈ point (R ⊛ T)
⊛-pointʳ R S T e = ⊛-point₂ R R S T identityˡ e

λ-discard : (S : State) → discard S ∘ λ⇒ ≈ discard (Iˢ ⊛ S)
λ-discard S = ⟺ unitorˡ-commute-from

λ-point : (S : State) → λ⇒ ∘ point (Iˢ ⊛ S) ≈ point S
λ-point S = pullˡ unitorˡ-commute-from ○ cancelʳ unitorˡ.isoʳ

ρ-discard : (S : State) → discard S ∘ ρ⇒ ≈ discard (S ⊛ Iˢ)
ρ-discard S = ⟺ unitorʳ-commute-from ○ ((⟺ coherence₃) ⟩∘⟨refl)

ρ-point : (S : State) → ρ⇒ ∘ point (S ⊛ Iˢ) ≈ point S
ρ-point S = pullˡ unitorʳ-commute-from
          ○ cancelʳ ((⟺ coherence₃) ⟩∘⟨refl ○ unitorˡ.isoʳ)

private
  -- The generator-free residue of the two laws below, at all-unit objects.
  λλ-α : α⇒ ∘ (λ⇐ {unit} ⊗₁ id ∘ λ⇐) ≈ id ⊗₁ λ⇐ ∘ λ⇐ {unit}
  λλ-α = insertˡ unitorˡ.isoˡ ○ (refl⟩∘⟨ lhs) ○ (refl⟩∘⟨ ⟺ rhs)
       ○ ⟺ (insertˡ unitorˡ.isoˡ)
    where
      lhs : λ⇒ ∘ (α⇒ ∘ (λ⇐ {unit} ⊗₁ id ∘ λ⇐)) ≈ λ⇐
      lhs = pullˡ coherence₁
          ○ pullˡ (merge₁ˡ ○ (unitorˡ.isoʳ ⟩⊗⟨refl) ○ ⊗.identity) ○ identityˡ

      rhs : λ⇒ ∘ (id ⊗₁ λ⇐ ∘ λ⇐ {unit}) ≈ λ⇐
      rhs = pullˡ unitorˡ-commute-from ○ cancelʳ unitorˡ.isoʳ

⊛-assoc-discard : (S T R : State)
                → discard (S ⊛ (T ⊛ R)) ∘ α⇒ ≈ discard ((S ⊛ T) ⊛ R)
⊛-assoc-discard S T R = begin
  (λ⇒ ∘ discard S ⊗₁ (λ⇒ ∘ discard T ⊗₁ discard R)) ∘ α⇒
    ≈⟨ ((refl⟩∘⟨ split₂ˡ) ○ pullˡ unitorˡ-commute-from) ⟩∘⟨refl ⟩
  ((λ⇒ ∘ λ⇒) ∘ discard S ⊗₁ (discard T ⊗₁ discard R)) ∘ α⇒
    ≈⟨ assoc ○ (refl⟩∘⟨ ⟺ assoc-commute-from) ○ sym-assoc ⟩
  ((λ⇒ ∘ λ⇒) ∘ α⇒) ∘ (discard S ⊗₁ discard T) ⊗₁ discard R
    ≈⟨ (assoc ○ (refl⟩∘⟨ coherence₁)) ⟩∘⟨refl ⟩
  (λ⇒ ∘ λ⇒ ⊗₁ id) ∘ (discard S ⊗₁ discard T) ⊗₁ discard R
    ≈⟨ assoc ○ (refl⟩∘⟨ merge₁ˡ) ⟩
  λ⇒ ∘ (λ⇒ ∘ discard S ⊗₁ discard T) ⊗₁ discard R  ∎

⊛-assoc-point : (S T R : State)
              → α⇒ ∘ point ((S ⊛ T) ⊛ R) ≈ point (S ⊛ (T ⊛ R))
⊛-assoc-point S T R = begin
  α⇒ ∘ ((point S ⊗₁ point T ∘ λ⇐) ⊗₁ point R ∘ λ⇐)
    ≈⟨ refl⟩∘⟨ (split₁ʳ ⟩∘⟨refl) ○ (refl⟩∘⟨ assoc) ⟩
  α⇒ ∘ ((point S ⊗₁ point T) ⊗₁ point R ∘ (λ⇐ ⊗₁ id ∘ λ⇐))
    ≈⟨ sym-assoc ○ (assoc-commute-from ⟩∘⟨refl) ○ assoc ⟩
  point S ⊗₁ (point T ⊗₁ point R) ∘ (α⇒ ∘ (λ⇐ ⊗₁ id ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ λλ-α ⟩
  point S ⊗₁ (point T ⊗₁ point R) ∘ (id ⊗₁ λ⇐ ∘ λ⇐)
    ≈⟨ sym-assoc ○ (⟺ split₂ʳ ⟩∘⟨refl) ⟩
  point S ⊗₁ (point T ⊗₁ point R ∘ λ⇐) ∘ λ⇐  ∎
