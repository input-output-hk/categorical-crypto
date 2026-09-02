{-# OPTIONS --safe --without-K #-}

-- SPIKE: the distributive hypothesis for the `𝒱` of `Spike.Instance.Setoid`, the
-- full Kleisli category of `Spike.CommutativeMaybe`'s `Maybe` monad.
--
-- Nothing is proved here.  `Setoids` is distributive because it is extensive and
-- cartesian — one upstream line — and `Spike.KleisliDistributive` carries that
-- through `pure`.  The pins say what the interface coproduct and the distributor
-- unfold to: a coproduct of setoids, and a `just`-valued map.

open import Categories.Category.Distributive using (Distributive)
open import Categories.Category.Instance.Properties.Setoids.Extensive using (Setoids-Extensive)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)

open import Data.Maybe.Base using (just)
import Data.Maybe.Relation.Binary.Pointwise as Pw
open import Data.Product.Base using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Categories.Category.Extensive.Properties.Distributive as ExtDist

open import CategoricalCrypto.SFunM.Spike.CommutativeMaybe 0ℓ
open import CategoricalCrypto.SFunM.Spike.KleisliDistributive
import CategoricalCrypto.SFunM.Spike.Instance.Setoid as S
import CategoricalCrypto.SFunM.Spike.MonoidalDistributive as MD

module CategoricalCrypto.SFunM.Spike.Instance.SetoidDist where

module MDS = MD S.𝒱

open Setoid using (Carrier)
open SymmetricMonoidalCategory S.𝒱 using (Obj; _⇒_; _⊗₀_)

-- `Setoids` is extensive and cartesian, hence distributive.
Setoids-Distributive : Distributive (Setoids 0ℓ 0ℓ)
Setoids-Distributive =
  ExtDist.Extensive×Cartesian⇒Distributive (Setoids 0ℓ 0ℓ) (Setoids-Extensive 0ℓ) Setoids-Cartesian

MDist : MDS.MonoidalDistributive
MDist = MonoidalDistributive-Kleisli Setoids-Symmetric Maybe-CommutativeMonad
  (MonoidalDistributive-Cartesian Setoids-Distributive)

open MDS.MonoidalDistributive MDist

private variable X A B : Obj

------------------------------------------------------------------------
-- What the interface tensor's ingredients are

coproduct-on-Setoids : (A + B) ≡ (A ⊎ₛ B)
coproduct-on-Setoids = refl

-- The distributor is a *pure* Kleisli map — a setoid map into `Maybe`, always
-- landing in `just`.
distributeˡ-on-Setoids : ((X ⊗₀ A) + (X ⊗₀ B) ⇒ X ⊗₀ (A + B))
                       ≡ Func ((X ×ₛ A) ⊎ₛ (X ×ₛ B)) (Pw.setoid (X ×ₛ (A ⊎ₛ B)))
distributeˡ-on-Setoids = refl

δ⇒-inj₁ : {x : Carrier X} {a : Carrier A} → δ⇒ {X} {A} {B} ⟨$⟩ inj₁ (x , a) ≡ just (x , inj₁ a)
δ⇒-inj₁ = refl

δ⇒-inj₂ : {x : Carrier X} {b : Carrier B} → δ⇒ {X} {A} {B} ⟨$⟩ inj₂ (x , b) ≡ just (x , inj₂ b)
δ⇒-inj₂ = refl

δ⇐-inj₁ : {x : Carrier X} {a : Carrier A} → δ⇐ {X} {A} {B} ⟨$⟩ (x , inj₁ a) ≡ just (inj₁ (x , a))
δ⇐-inj₁ = refl

δ⇐-inj₂ : {x : Carrier X} {b : Carrier B} → δ⇐ {X} {A} {B} ⟨$⟩ (x , inj₂ b) ≡ just (inj₂ (x , b))
δ⇐-inj₂ = refl
