{-# OPTIONS --safe --without-K #-}

-- The finite possibility monad: `List` under set equality, taken up to the
-- element setoid's own equality.  At `≡-setoid` that is the stdlib's
-- `_∼[ set ]_`, so `Discrete` recovers the `MonadSetoid` structure verbatim.

open import categorical-crypto.Prelude

open import Class.Monad.Ext.Setoid

import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.List.Relation.Binary.BagAndSetEquality using (_∼[_]_; set; [_]-Equality)
open import Data.List.Relation.Unary.Any as Any using (Any)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.Any.Properties.Ext
open import Function.Bundles
open import Function.Related.Propositional using (InducedEquivalence₂; module EquationalReasoning)
open import Relation.Binary
open import Relation.Binary.Bundles.Ext
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

module ProbabilisticLogic.Distribution.Possibility where

open Setoid using (Carrier; reflexive)

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ

module 𝒫 {ℓ} {A : Type ℓ} = Setoid ([ set ]-Equality A)

------------------------------------------------------------------------
-- Set equality up to the element setoid
------------------------------------------------------------------------

-- The stdlib's induced-equivalence machinery at *setoid* membership, so at
-- `≡-setoid` it is `[ set ]-Equality` on the nose.
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
    (∈-concatMap⁺ S S′ {f = g} ∘ Equivalence.to   cong-Any ∘ ∈-concatMap⁻ S S′ {f = f})
    (∈-concatMap⁺ S S′ {f = f} ∘ Equivalence.from cong-Any ∘ ∈-concatMap⁻ S S′ {f = g})
    where cong-Any = Any-congˢ S (λ a≈b → f≈g a≈b {z}) σ≈τ

  >>=𝒫-identityˡ : (a : Carrier S) (h : Carrier S → List (Carrier S′))
                 → 𝒫ˢ S′ ⟨ concatMap h (a ∷ []) ≈ h a ⟩
  >>=𝒫-identityˡ a h = reflexive (𝒫ˢ S′) (++-identityʳ (h a))

module _ {S : Setoid ℓ ℓ} where

  >>=𝒫-identityʳ : (σ : List (Carrier S)) → 𝒫ˢ S ⟨ concatMap (_∷ []) σ ≈ σ ⟩
  >>=𝒫-identityʳ σ = reflexive (𝒫ˢ S) (concatMap-pure σ)

module _ {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} {S″ : Setoid ℓ″ ℓ″} where

  >>=𝒫-assoc : (σ : List (Carrier S)) (g : Carrier S → List (Carrier S′))
               (h : Carrier S′ → List (Carrier S″))
             → 𝒫ˢ S″ ⟨ concatMap h (concatMap g σ)
                     ≈ concatMap (λ a → concatMap h (g a)) σ ⟩
  >>=𝒫-assoc σ g h = reflexive (𝒫ˢ S″) (concatMap-assoc σ g h)

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
-- Setoid monad structure
------------------------------------------------------------------------

instance
  SetoidMonad-List : SetoidMonad List
  SetoidMonad-List = record
    { _⟨_≈ˢ_⟩          = λ S → Setoid._≈_ (𝒫ˢ S)
    ; ≈ˢ-isEquivalence = λ {S = S} → Setoid.isEquivalence (𝒫ˢ S)
    ; return-congˢ     = λ {S = S} → return-cong𝒫 {S = S}
    ; >>=-congˢ        = λ {S = S} {S′ = S′} → >>=𝒫-cong {S = S} {S′ = S′}
    }

  SetoidMonadLaws-List : SetoidMonadLaws List
  SetoidMonadLaws-List = record
    { >>=-identityˡ-≈ˢ = λ {S = S} {S′ = S′} {a = a} {h = h} →
        >>=𝒫-identityˡ {S = S} {S′ = S′} a h
    ; >>=-identityʳ-≈ˢ = λ {S = S} → >>=𝒫-identityʳ {S = S}
    ; >>=-assoc-≈ˢ     = λ {S = S} {S′ = S′} {S″ = S″} m {g = g} {h = h} →
        >>=𝒫-assoc {S = S} {S′ = S′} {S″ = S″} m g h
    }

  CommutativeSetoidMonad-List : CommutativeSetoidMonad List
  CommutativeSetoidMonad-List = record
    { >>=-comm-≈ˢ = λ {S = S} {S′ = S′} {S″ = S″} {x = σ} {y = τ} {f = f} _ →
        >>=𝒫-comm {S = S} {S′ = S′} {S″ = S″} σ τ f
    }

-- The carrier-indexed structure the machine layer consumes is the ≡-discrete
-- case of the above.
open Discrete {List}

instance
  MonadSetoid-List : MonadSetoid List
  MonadSetoid-List = Discrete-MonadSetoid

  MonadLawsSetoid-List : MonadLawsSetoid List
  MonadLawsSetoid-List = Discrete-MonadLawsSetoid

  CommutativeMonadSetoid-List : CommutativeMonadSetoid List
  CommutativeMonadSetoid-List = Discrete-CommutativeMonadSetoid

-- Definitionally the same relation: the adapter only pins the index.
_ : {σ τ : List A} → MonadSetoid._≈ᴹ_ MonadSetoid-List σ τ ≡ (𝒫ˢ (≡-setoid A) ⟨ σ ≈ τ ⟩)
_ = refl
