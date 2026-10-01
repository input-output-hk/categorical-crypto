{-# OPTIONS --safe --without-K #-}

-- The finite possibility monad on `Setoids`: `List` under set equality, taken
-- up to the element setoid's own equality.  At `≡-setoid` that is the stdlib's
-- `_∼[ set ]_`, which is what the machine layer computes with.
-- Finer than `ProbabilisticLogic.Distribution.Possibility`'s `Bool`-test `_≈𝒫_`;
-- the two agree only at decidable element equality.

open import categorical-crypto.Prelude

open import Categories.Category.Instance.Setoids
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Discrete
import Categories.Monad.Setoids.Discrete as Discrete

import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.List.Relation.Binary.BagAndSetEquality
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.Any.Properties.Ext
open import Function.Bundles
open import Function.Related.Propositional using (InducedEquivalence₂; module EquationalReasoning)
open import Relation.Binary
open import Relation.Binary.Bundles.Ext
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

module ProbabilisticLogic.Distribution.Possibility.Setoids where

open Setoid using (Carrier; reflexive)

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ

module 𝒫 {ℓ} {A : Type ℓ} = Setoid ([ set ]-Equality A)

------------------------------------------------------------------------
-- Set equality up to the element setoid
------------------------------------------------------------------------

𝒫ˢ : (S : Setoid ℓ ℓ) → Setoid ℓ ℓ
𝒫ˢ S = InducedEquivalence₂ set (Membership._∈_ S)

_ : {σ τ : List A} → (σ ∼[ set ] τ) ≡ (𝒫ˢ (≡-setoid A) ⟨ σ ≈ τ ⟩)
_ = refl

module _ {S : Setoid ℓ ℓ} where

  private module S≈ = Setoid S

  return-cong𝒫 : {a b : Carrier S} → S ⟨ a ≈ b ⟩ → 𝒫ˢ S ⟨ (a ∷ []) ≈ (b ∷ []) ⟩
  return-cong𝒫 a≈b = mk⇔
    (λ where (Any.here z≈a) → Any.here (S≈.trans z≈a a≈b)
             (Any.there ()))
    (λ where (Any.here z≈b) → Any.here (S≈.trans z≈b (S≈.sym a≈b))
             (Any.there ()))

module _ {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} where

  >>=𝒫-cong : {σ τ : List (Carrier S)} {f g : Carrier S → List (Carrier S′)}
            → 𝒫ˢ S ⟨ σ ≈ τ ⟩ → (∀ {a b} → S ⟨ a ≈ b ⟩ → 𝒫ˢ S′ ⟨ f a ≈ g b ⟩)
            → 𝒫ˢ S′ ⟨ concatMap f σ ≈ concatMap g τ ⟩
  >>=𝒫-cong {f = f} {g} σ≈τ f≈g {z} = mk⇔
    (∈-concatMap⁺ S S′ ∘ Equivalence.to   cong-Any ∘ ∈-concatMap⁻ S S′)
    (∈-concatMap⁺ S S′ ∘ Equivalence.from cong-Any ∘ ∈-concatMap⁻ S S′)
    where cong-Any = Any-congˢ S (λ a≈b → f≈g a≈b) σ≈τ

module _ {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} {S″ : Setoid ℓ″ ℓ″} where

  -- Membership only ever asks "some `a`, some `b`", so `swap↔` is the whole
  -- content: no congruence of `f` is needed.
  >>=𝒫-comm : (σ : List (Carrier S)) (τ : List (Carrier S′))
              (f : Carrier S → Carrier S′ → List (Carrier S″))
            → 𝒫ˢ S″ ⟨ concatMap (λ a → concatMap (f a) τ) σ
                    ≈ concatMap (λ b → concatMap (λ a → f a b) σ) τ ⟩
  >>=𝒫-comm σ τ f {z} = begin
    z ∈″ concatMap (λ a → concatMap (f a) τ) σ
      ∼⟨ mk⇔ (∈-concatMap⁻ S S″) (∈-concatMap⁺ S S″) ⟩
    Any (λ a → z ∈″ concatMap (f a) τ) σ
      ∼⟨ mk⇔ (Any.map (∈-concatMap⁻ S′ S″)) (Any.map (∈-concatMap⁺ S′ S″)) ⟩
    Any (λ a → Any (λ b → z ∈″ f a b) τ) σ
      ↔⟨ swap↔ ⟩
    Any (λ b → Any (λ a → z ∈″ f a b) σ) τ
      ∼⟨ mk⇔ (Any.map (∈-concatMap⁺ S S″)) (Any.map (∈-concatMap⁻ S S″)) ⟩
    Any (λ b → z ∈″ concatMap (λ a → f a b) σ) τ
      ∼⟨ mk⇔ (∈-concatMap⁺ S′ S″) (∈-concatMap⁻ S′ S″) ⟩
    z ∈″ concatMap (λ b → concatMap (λ a → f a b) σ) τ ∎
    where
    open EquationalReasoning
    open Membership S″ using () renaming (_∈_ to _∈″_)

------------------------------------------------------------------------
-- The monad on `Setoids`
------------------------------------------------------------------------

𝒫-KleisliTriple : KleisliTriple (Setoids ℓ ℓ)
𝒫-KleisliTriple = record
  { F₀        = 𝒫ˢ
  ; unit      = λ {S} → record { to = _∷ [] ; cong = return-cong𝒫 {S = S} }
  ; extend    = λ {S} {S′} f → record
      { to   = concatMap (f ⟨$⟩_)
      ; cong = λ σ≈τ → >>=𝒫-cong {S = S} {S′ = S′} σ≈τ (Func.cong f)
      }
  ; identityʳ = λ {S} {S′} {k} {a} → reflexive (𝒫ˢ S′) (++-identityʳ (k ⟨$⟩ a))
  ; identityˡ = λ {S} {σ} → reflexive (𝒫ˢ S) (concatMap-pure σ)
  ; assoc     = λ {S} {S′} {S″} {k} {l} {σ} →
      reflexive (𝒫ˢ S″) (sym (concatMap-assoc σ (k ⟨$⟩_) (l ⟨$⟩_)))
  ; sym-assoc = λ {S} {S′} {S″} {k} {l} {σ} → reflexive (𝒫ˢ S″) (concatMap-assoc σ (k ⟨$⟩_) (l ⟨$⟩_))
  ; extend-≈  = λ {S} {S′} {k} {h} k≈h {σ} →
      >>=𝒫-cong {S = S} {S′ = S′} {τ = σ} (Setoid.refl (𝒫ˢ S)) λ a≈b →
        Setoid.trans (𝒫ˢ S′) k≈h (Func.cong h a≈b)
  }

𝒫-DiscreteMonad : DiscreteMonad ℓ
𝒫-DiscreteMonad = record
  { elementwise = Discrete.elementwise 𝒫-KleisliTriple
  ; >>=-comm    = λ {A} {B} {σ} {τ} →
      >>=𝒫-comm {S = ≡-setoid A} {S′ = ≡-setoid B} {S″ = ≡-setoid (A × B)} σ τ _
  }
