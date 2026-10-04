{-# OPTIONS --safe --without-K --guardedness #-}

-- The base `𝒱ₚ` is a Kleisli category, so every structural map of the machine
-- layer is a FUNCTION: `pureᵏ` of a relabelling.  This module is that reading
-- for base maps (`…ᵏ`), the junctions a pure factor spends (`…ᴵ`), and
-- machines (`pureᶠ`).

open import Categories.Category.Monoidal.Bundle
open import Categories.Monad.Discrete
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MU

open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Base using () renaming (assocˡ to ⊎assocˡ; assocʳ to ⊎assocʳ)
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality using (refl)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Machines.Base

import CategoricalCrypto.Machines.Frame as Frame

module CategoricalCrypto.Machines.Pure where

open MC
open MD.MonoidalDistributive (distₚ 0ℓ)
open CE V.U cocartesian
open DiscreteMonad (Dₚ-DiscreteMonad {0ℓ})
  renaming (_≈ᴹ_ to _≈ᵈ_; module ≈ᴹ to ≈ᵈ)
open Frame (𝒱ₚ 0ℓ)
open K
open Cat
open MU.Shorthands V.monoidal
open MS
open T

open import Categories.Category.Monoidal.Properties.Ext V.monoidal
open import Categories.Category.Monoidal.Reasoning V.monoidal

private
  variable P Q R S V W V′ W′ X : V.Obj

------------------------------------------------------------------------
-- The base is a Kleisli category: its structural maps are functions

pure-idᵏ : V._≈_ (V.id {V}) (pureᵏ (λ v → v))
pure-idᵏ _ = ≈ᵈ.refl

swapᵏ : V._≈_ (+-swap {V} {W}) (pureᵏ Sum.swap)
swapᵏ (inj₁ _) = ≈ᵈ.refl
swapᵏ (inj₂ _) = ≈ᵈ.refl

assocˡᵏ : V._≈_ (α+⇐ {P} {Q} {R}) (pureᵏ ⊎assocˡ)
assocˡᵏ (inj₁ _)        = >>=-identityˡ-≈
assocˡᵏ (inj₂ (inj₁ _)) = >>=-identityˡ-≈
assocˡᵏ (inj₂ (inj₂ _)) = ≈ᵈ.refl

assocʳᵏ : V._≈_ (α+⇒ {P} {Q} {R}) (pureᵏ ⊎assocʳ)
assocʳᵏ (inj₁ (inj₁ _)) = ≈ᵈ.refl
assocʳᵏ (inj₁ (inj₂ _)) = >>=-identityˡ-≈
assocʳᵏ (inj₂ _)        = >>=-identityˡ-≈

∘-pureᵏ : {u : V._⇒_ V W} {v : V._⇒_ V′ V} {h : V → W} {k : V′ → V}
        → V._≈_ u (pureᵏ h) → V._≈_ v (pureᵏ k)
        → V._≈_ (V._∘_ u v) (pureᵏ (λ x → h (k x)))
∘-pureᵏ {h = h} {k} e₁ e₂ = (e₁ ⟩∘⟨ e₂) ○ pureᵏ-∘ h k

+₁-pureᵏ : {u : V._⇒_ V W} {v : V._⇒_ V′ W′} {h : V → W} {k : V′ → W′}
         → V._≈_ u (pureᵏ h) → V._≈_ v (pureᵏ k)
         → V._≈_ (u +₁ v) (pureᵏ (Sum.map h k))
+₁-pureᵏ {h = h} {k} e₁ e₂ = +₁-cong₂ e₁ e₂ ○ leaves
  where
  leaves : V._≈_ (pureᵏ h +₁ pureᵏ k) (pureᵏ (Sum.map h k))
  leaves (inj₁ _) = >>=-identityˡ-≈
  leaves (inj₂ _) = >>=-identityˡ-≈

-- A pure interface relabelling spends two junctions and keeps the state.
pureᴵ : (h : V → W) (r : X × V)
      → V._⊗₁_ V.id (pureᵏ h) r ≈ᵈ returnₚ (proj₁ r , h (proj₂ r))
pureᴵ h = pureᵏ-⊗ (λ x → x) h

enter-pure : {A : V.Obj} (h : V → W) (K : X × W → Dₚ A) (x : X) (v : V)
           → (V._⊗₁_ V.id (pureᵏ h) (x , v) >>= K) ≈ᵈ K (x , h v)
enter-pure h K x v = ≈ᵈ.trans (>>=-cong-x (pureᴵ h (x , v))) >>=-identityˡ-≈

-- Entering a `tstep` on one summand runs that arm and retags its answer.
tstep-inj₁ : {A B C D : V.Obj} (k : X × A → Dₚ (W × B)) (l : X × C → Dₚ (W × D))
             (x : X) (a : A)
           → tstep k l (x , inj₁ a)
             ≈ᵈ (k (x , a) >>= λ r → returnₚ (proj₁ r , inj₁ (proj₂ r)))
tstep-inj₁ k l x a =
  ≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈)
    (≈ᵈ.trans (>>=-assoc-≈ (k (x , a)))
      (>>=-cong-f λ r → ≈ᵈ.trans >>=-identityˡ-≈ (pureᵏ-⊗ (λ y → y) inj₁ r)))

tstep-inj₂ : {A B C D : V.Obj} (k : X × A → Dₚ (W × B)) (l : X × C → Dₚ (W × D))
             (x : X) (c : C)
           → tstep k l (x , inj₂ c)
             ≈ᵈ (l (x , c) >>= λ r → returnₚ (proj₁ r , inj₂ (proj₂ r)))
tstep-inj₂ k l x c =
  ≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈)
    (≈ᵈ.trans (>>=-assoc-≈ (l (x , c)))
      (>>=-cong-f λ r → ≈ᵈ.trans >>=-identityˡ-≈ (pureᵏ-⊗ (λ y → y) inj₂ r)))

------------------------------------------------------------------------
-- Machines that are functions

∘-pureᴹ : {M : Machine W V′} {N : Machine V W} {u : V._⇒_ W V′} {v : V._⇒_ V W}
        → M ≈ᴹ pureᴹ u → N ≈ᴹ pureᴹ v → (M ∘ᴹ N) ≈ᴹ pureᴹ (V._∘_ u v)
∘-pureᴹ e₁ e₂ = ∘ᴹ-resp-≈ᴹ e₁ e₂ ○ᴹ ≲⇒≈ᴹ (pureᴹ-∘ _ _)

⊗-pureᴹ : {M : Machine V W} {N : Machine V′ W′} {u : V._⇒_ V W} {v : V._⇒_ V′ W′}
        → M ≈ᴹ pureᴹ u → N ≈ᴹ pureᴹ v → (M ⊗ᵉ N) ≈ᴹ pureᴹ (u +₁ v)
⊗-pureᴹ e₁ e₂ = ⊗ᵉ-resp-≈ᴹ e₁ e₂ ○ᴹ ≲⇒≈ᴹ (⊗ᵉ-pureᴹ _ _)

pureᶠ : (V → W) → Machine V W
pureᶠ h = pureᴹ (pureᵏ h)

idᶠ : (V : V.Obj) → idᴹ {V} ≈ᴹ pureᶠ (λ v → v)
idᶠ _ = ≲⇒≈ᴹ˘ pureᴹ-id

∘ᶠ : {f : Machine V W} {g : Machine W V′} {h : V → W} {k : W → V′}
   → f ≈ᴹ pureᶠ h → g ≈ᴹ pureᶠ k → (g ∘ᴹ f) ≈ᴹ pureᶠ (k ∘′ h)
∘ᶠ {h = h} {k} e₁ e₂ = ∘-pureᴹ e₂ e₁ ○ᴹ ≲⇒≈ᴹ (pureᴹ-cong (pureᵏ-∘ k h))

⊗ᶠ : {f : Machine V W} {g : Machine V′ W′} {h : V → W} {k : V′ → W′}
   → f ≈ᴹ pureᶠ h → g ≈ᴹ pureᶠ k → (f ⊗ᵉ g) ≈ᴹ pureᶠ (Sum.map h k)
⊗ᶠ {h = h} e₁ e₂ = ⊗-pureᴹ e₁ e₂
  ○ᴹ ≲⇒≈ᴹ (pureᴹ-cong (+₁-pureᵏ V.Equiv.refl V.Equiv.refl))

α⇒ᶠ : (P Q R : V.Obj) → α⇒ᴹ {P} {Q} {R} ≈ᴹ pureᶠ ⊎assocʳ
α⇒ᶠ _ _ _ = ≲⇒≈ᴹ (pureᴹ-cong assocʳᵏ)

α⇐ᶠ : (P Q R : V.Obj) → α⇐ᴹ {P} {Q} {R} ≈ᴹ pureᶠ ⊎assocˡ
α⇐ᶠ _ _ _ = ≲⇒≈ᴹ (pureᴹ-cong assocˡᵏ)

σᶠ : (V W : V.Obj) → σᴹ {V} {W} ≈ᴹ pureᶠ Sum.swap
σᶠ _ _ = ≲⇒≈ᴹ (pureᴹ-cong swapᵏ)
