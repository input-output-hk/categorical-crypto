{-# OPTIONS --safe --without-K --guardedness #-}

-- The base `𝒱ₚ` is a Kleisli category, so every structural map of the machine
-- layer is a FUNCTION: `pureᵏ` of a relabelling.  This module is that reading —
-- the base half (`pure-idᵏ`/`swapᵏ`/`assocˡᵏ`/`assocʳᵏ` and the two
-- congruences), the junction calculus a pure factor spends
-- (`pureᴵ`/`enter-pure`/`exit-pure`/`tstep-inj₁`/`tstep-inj₂`), and the machine
-- half (`pureᴹ` congruences, the interchange `midᴹ`, and `⌜⌝-pureᴹ`).
--
-- `midᴹ` is kept nominal by `opaque`: its expansion is proved once, in
-- `midᴹ-pure`, and consumers that need the composite say `unfolding midᴹ`.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Monad.Discrete using (DiscreteMonad)
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MU

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)

open import ProbabilisticLogic.Dp using (Dₚ; returnₚ)

open import CategoricalCrypto.Machines.Base
  using (Dₚ-DiscreteMonad; 𝒱ₚ; distₚ; 𝒫ₚ)

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Pure where

private
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open MD.MonoidalDistributive (distₚ 0ℓ)
open CE 𝒱.U cocartesian
open DiscreteMonad (Dₚ-DiscreteMonad {0ℓ})
  renaming (_≈ᴹ_ to _≈ᵈ_; module ≈ᴹ to ≈ᵈ)
open Frame (𝒱ₚ 0ℓ)
open KD (Dₚ-DiscreteMonad {0ℓ})
open MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open MU.Shorthands 𝒱.monoidal
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)

open import Categories.Category.Monoidal.Reasoning 𝒱.monoidal

private
  variable P Q R S V W V′ W′ X : 𝒱.Obj

------------------------------------------------------------------------
-- The base is a Kleisli category: its structural maps are functions

pure-idᵏ : 𝒱._≈_ (𝒱.id {V}) (pureᵏ (λ v → v))
pure-idᵏ _ = ≈ᵈ.refl

swapᵏ : 𝒱._≈_ (+-swap {V} {W}) (pureᵏ Sum.swap)
swapᵏ (inj₁ _) = ≈ᵈ.refl
swapᵏ (inj₂ _) = ≈ᵈ.refl

assocˡᵏ : 𝒱._≈_ (α+⇐ {P} {Q} {R}) (pureᵏ ⊎assocˡ)
assocˡᵏ (inj₁ _)        = >>=-identityˡ-≈
assocˡᵏ (inj₂ (inj₁ _)) = >>=-identityˡ-≈
assocˡᵏ (inj₂ (inj₂ _)) = ≈ᵈ.refl

assocʳᵏ : 𝒱._≈_ (α+⇒ {P} {Q} {R}) (pureᵏ ⊎assocʳ)
assocʳᵏ (inj₁ (inj₁ _)) = ≈ᵈ.refl
assocʳᵏ (inj₁ (inj₂ _)) = >>=-identityˡ-≈
assocʳᵏ (inj₂ _)        = >>=-identityˡ-≈

∘-pureᵏ : {u : 𝒱._⇒_ V W} {v : 𝒱._⇒_ V′ V} {h : V → W} {k : V′ → V}
        → 𝒱._≈_ u (pureᵏ h) → 𝒱._≈_ v (pureᵏ k)
        → 𝒱._≈_ (𝒱._∘_ u v) (pureᵏ (λ x → h (k x)))
∘-pureᵏ {h = h} {k} e₁ e₂ = (e₁ ⟩∘⟨ e₂) ○ pureᵏ-∘ h k

+₁-pureᵏ : {u : 𝒱._⇒_ V W} {v : 𝒱._⇒_ V′ W′} {h : V → W} {k : V′ → W′}
         → 𝒱._≈_ u (pureᵏ h) → 𝒱._≈_ v (pureᵏ k)
         → 𝒱._≈_ (u +₁ v) (pureᵏ (Sum.map h k))
+₁-pureᵏ {h = h} {k} e₁ e₂ = +₁-cong₂ e₁ e₂ ○ leaves
  where
  leaves : 𝒱._≈_ (pureᵏ h +₁ pureᵏ k) (pureᵏ (Sum.map h k))
  leaves (inj₁ _) = >>=-identityˡ-≈
  leaves (inj₂ _) = >>=-identityˡ-≈

-- A pure interface relabelling spends two junctions and keeps the state.
pureᴵ : (h : V → W) (r : X × V)
      → 𝒱._⊗₁_ (𝒱.id {X}) (pureᵏ h) r ≈ᵈ returnₚ (proj₁ r , h (proj₂ r))
pureᴵ h = pureᵏ-⊗ (λ x → x) h

swapᴵ : (r : X × (V ⊎ W))
      → 𝒱._⊗₁_ (𝒱.id {X}) +-swap r ≈ᵈ returnₚ (proj₁ r , Sum.swap (proj₂ r))
swapᴵ {X = X} {V} {W} r = ≈ᵈ.trans (padded r) (pureᴵ Sum.swap r)
  where
  padded : 𝒱._≈_ {X × (V ⊎ W)} {X × (W ⊎ V)}
                 (𝒱._⊗₁_ 𝒱.id +-swap) (𝒱._⊗₁_ 𝒱.id (pureᵏ Sum.swap))
  padded = refl⟩⊗⟨ swapᵏ

enter-pure : {A : 𝒱.Obj} (h : V → W) (K : X × W → Dₚ A) (x : X) (v : V)
           → (𝒱._⊗₁_ (𝒱.id {X}) (pureᵏ h) (x , v) >>= K) ≈ᵈ K (x , h v)
enter-pure h K x v = ≈ᵈ.trans (>>=-cong-x (pureᴵ h (x , v))) >>=-identityˡ-≈

exit-pure : (h : V → W) (x : X) (v : V)
          → (returnₚ (x , v) >>= 𝒱._⊗₁_ (𝒱.id {X}) (pureᵏ h)) ≈ᵈ returnₚ (x , h v)
exit-pure h x v = ≈ᵈ.trans >>=-identityˡ-≈ (pureᴵ h (x , v))

-- Entering a `tstep` on one summand runs that arm and retags its answer.
tstep-inj₁ : {A B C D : 𝒱.Obj} (k : X × A → Dₚ (W × B)) (l : X × C → Dₚ (W × D))
             (x : X) (a : A)
           → tstep k l (x , inj₁ a)
             ≈ᵈ (k (x , a) >>= λ r → returnₚ (proj₁ r , inj₁ (proj₂ r)))
tstep-inj₁ k l x a =
  ≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈)
    (≈ᵈ.trans (>>=-assoc-≈ (k (x , a)))
      (>>=-cong-f λ r → ≈ᵈ.trans >>=-identityˡ-≈ (pureᵏ-⊗ (λ y → y) inj₁ r)))

tstep-inj₂ : {A B C D : 𝒱.Obj} (k : X × A → Dₚ (W × B)) (l : X × C → Dₚ (W × D))
             (x : X) (c : C)
           → tstep k l (x , inj₂ c)
             ≈ᵈ (l (x , c) >>= λ r → returnₚ (proj₁ r , inj₂ (proj₂ r)))
tstep-inj₂ k l x c =
  ≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈)
    (≈ᵈ.trans (>>=-assoc-≈ (l (x , c)))
      (>>=-cong-f λ r → ≈ᵈ.trans >>=-identityˡ-≈ (pureᵏ-⊗ (λ y → y) inj₂ r)))

------------------------------------------------------------------------
-- `mid` and the pure machines it is built from

-- The interchange the G-tensor conjugates by, as a function on sums.
midfn : (P ⊎ Q) ⊎ (R ⊎ S) → (P ⊎ R) ⊎ (Q ⊎ S)
midfn (inj₁ (inj₁ p)) = inj₁ (inj₁ p)
midfn (inj₁ (inj₂ q)) = inj₂ (inj₁ q)
midfn (inj₂ (inj₁ r)) = inj₁ (inj₂ r)
midfn (inj₂ (inj₂ s)) = inj₂ (inj₂ s)

-- Keep the nested structural composite nominal after proving its expansion
-- once.
opaque
  midᴹ : Machine ((P + Q) + (R + S)) ((P + R) + (Q + S))
  midᴹ = α⇐ᴹ ∘ᴹ ((idᴹ ⊗ᵉ (α⇒ᴹ ∘ᴹ ((σᴹ ⊗ᵉ idᴹ) ∘ᴹ α⇐ᴹ))) ∘ᴹ α⇒ᴹ)

id-pureᴹ : idᴹ {V} ≈ᴹ pureᴹ (𝒱.id {V})
id-pureᴹ = ≲⇒≈ᴹ˘ pureᴹ-id

∘-pureᴹ : {M : Machine W V′} {N : Machine V W} {u : 𝒱._⇒_ W V′} {v : 𝒱._⇒_ V W}
        → M ≈ᴹ pureᴹ u → N ≈ᴹ pureᴹ v → (M ∘ᴹ N) ≈ᴹ pureᴹ (𝒱._∘_ u v)
∘-pureᴹ e₁ e₂ = ∘ᴹ-resp-≈ᴹ e₁ e₂ ○ᴹ ≲⇒≈ᴹ (pureᴹ-∘ _ _)

⊗-pureᴹ : {M : Machine V W} {N : Machine V′ W′} {u : 𝒱._⇒_ V W} {v : 𝒱._⇒_ V′ W′}
        → M ≈ᴹ pureᴹ u → N ≈ᴹ pureᴹ v → (M ⊗ᵉ N) ≈ᴹ pureᴹ (u +₁ v)
⊗-pureᴹ e₁ e₂ = ⊗ᵉ-resp-≈ᴹ e₁ e₂ ○ᴹ ≲⇒≈ᴹ (⊗ᵉ-pureᴹ _ _)

-- Every factor of `mid` is a structural machine, hence `pureᴹ`; what it
-- collapses to is the interchange on sums.
opaque
  unfolding midᴹ

  midᴹ-pure : midᴹ {P} {Q} {R} {S} ≈ᴹ pureᴹ (pureᵏ midfn)
  midᴹ-pure =
      ∘-pureᴹ reflᴹ
        (∘-pureᴹ
          (⊗-pureᴹ id-pureᴹ
            (∘-pureᴹ reflᴹ (∘-pureᴹ (⊗-pureᴹ reflᴹ id-pureᴹ) reflᴹ)))
          reflᴹ)
    ○ᴹ ≲⇒≈ᴹ (pureᴹ-cong
      (∘-pureᵏ assocˡᵏ
        (∘-pureᵏ (+₁-pureᵏ pure-idᵏ
                   (∘-pureᵏ assocʳᵏ
                     (∘-pureᵏ (+₁-pureᵏ swapᵏ pure-idᵏ) assocˡᵏ)))
                 assocʳᵏ)
       ○ pureᵏ-cong λ where
           (inj₁ (inj₁ _)) → refl
           (inj₁ (inj₂ _)) → refl
           (inj₂ (inj₁ _)) → refl
           (inj₂ (inj₂ _)) → refl))

-- Tensoring with a pure machine keeps the other factor's state.  The mirror
-- pair in `Machines.Tensor.Structural` puts the pure factor on the other side.
pure⊗-stateˡ : (h : 𝒱._⇒_ V W) (M : Machine V′ W′)
             → (pureᴹ h ⊗ᵉ M) ≲ mk (state M) (tstep (𝒱._⊗₁_ 𝒱.id h) (step M))
pure⊗-stateˡ h M = collapseˡ ((refl⟩∘⟨ tstep-cong (onL-str h) 𝒱.Equiv.refl)
                              ○ tstep-sim (⟺ (pad-transport λ⇒ h)) onR-collapseˡ)

pure⊗-stateʳ : (M : Machine V W) (h : 𝒱._⇒_ V′ W′)
             → (M ⊗ᵉ pureᴹ h) ≲ mk (state M) (tstep (step M) (𝒱._⊗₁_ 𝒱.id h))
pure⊗-stateʳ M h = collapseʳ ((refl⟩∘⟨ tstep-cong 𝒱.Equiv.refl (onRᵍ-id⊗ h))
                              ○ tstep-sim onL-collapseʳ (⟺ (pad-transport ρ⇒ h)))

------------------------------------------------------------------------
-- Every wire is an embedding

-- The base half of the embedding `⌜ u , v ⌝`: swapping after relabelling each
-- summand is the copairing that routes each summand to the other side.
swap-copair : (u : 𝒱._⇒_ V W) (v : 𝒱._⇒_ V′ W′)
            → 𝒱._≈_ (𝒱._∘_ +-swap (u +₁ v)) [ 𝒱._∘_ i₂ u , 𝒱._∘_ i₁ v ]
swap-copair u v = +-unique₂
  (𝒱.assoc ○ (refl⟩∘⟨ +₁∘i₁) ○ 𝒱.sym-assoc ○ (+-swap-i₁ ⟩∘⟨refl) ○ ⟺ inject₁)
  (𝒱.assoc ○ (refl⟩∘⟨ +₁∘i₂) ○ 𝒱.sym-assoc ○ (+-swap-i₂ ⟩∘⟨refl) ○ ⟺ inject₂)

-- …and the machine half: an embedding of two pure machines is pure.
⌜⌝-pureᴹ : (u : 𝒱._⇒_ V W) (v : 𝒱._⇒_ V′ W′)
         → (σᴹ ∘ᴹ (pureᴹ u ⊗ᵉ pureᴹ v)) ≲ pureᴹ (𝒱._∘_ +-swap (u +₁ v))
⌜⌝-pureᴹ u v = ≲-trans (∘ᴹ-resp-≲ ≲-refl (⊗ᵉ-pureᴹ u v)) (pureᴹ-∘ +-swap (u +₁ v))
