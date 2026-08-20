{-# OPTIONS --safe --without-K #-}

-- SPIKE: the distributive hypothesis at `Spike.KleisliDiscrete`'s `Klᴹ` — the
-- possibilistic story, which is what replaces `Rel` as a base.
--
-- Written elementwise, and that is the point: `Spike.KleisliDistributive` proves
-- both gifts in general, but at this base they are one-liners — a map out of `_⊎_`
-- *is* a case split, so the coproduct's uniqueness is two clauses, and the
-- distributor is `return` of the pure `X × (A ⊎ B) ↔ X × A ⊎ X × B` shuffle, so
-- both iso laws are `>>=-identityˡ-≈` chains.  Nothing here touches the monad
-- beyond the left unit law.
--
-- The pins at the end are the ergonomics check: a `do`-notation kernel still
-- elaborates, a closed `eval` still reduces by `refl`, and the distributor itself
-- reduces to a literal list.

open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Monad.Construction.Kleisli using (KleisliTriple)

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Algebra using (×-distribˡ-⊎)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Polymorphic using (tt)
open import Function.Base using (const)
open import Function.Bundles using (Inverse)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Categories.Monad.Setoids.Discrete as Discrete
import CategoricalCrypto.SFunM.Spike.KleisliDiscrete as KD
import CategoricalCrypto.SFunM.Spike.Mealy as Mealy
import CategoricalCrypto.SFunM.Spike.MonoidalDistributive as MD
import CategoricalCrypto.SFunM.Spike.Tensor as Tensor

open import ProbabilisticLogic.Distribution.Possibility using (𝒫-KleisliTriple; 𝒫-commutative)

module CategoricalCrypto.SFunM.Spike.Instance.TypeDist where

------------------------------------------------------------------------
-- The construction, at an arbitrary commutative `Setoids` monad

module _ {ℓ} (K : KleisliTriple (Setoids ℓ ℓ)) (K-Comm : Discrete.Commutative K) where
  open Discrete K
  open KD K K-Comm

  private variable A B X : Set ℓ

  module MDᵏ = MD Klᴹ-SymmetricMonoidal

  -- The pure shuffle the distributor inverts.
  undistribute : X × (A ⊎ B) → (X × A) ⊎ (X × B)
  undistribute = Inverse.to (×-distribˡ-⊎ ℓ _ _ _)

  -- Gift (a) elementwise: `[_,_]` is `Data.Sum`'s case split and uniqueness is
  -- two clauses, because a Kleisli hom out of `A ⊎ B` is just a function out of
  -- `A ⊎ B`.
  Cocartesianᵏ : Cocartesian Klᴹ
  Cocartesianᵏ = record
    { initial    = record { ⊥ = ⊥ ; ⊥-is-initial = record { ! = ⊥-elim ; !-unique = λ _ → ⊥-elim } }
    ; coproducts = record
        { coproduct = λ {A} {B} → record
            { A+B     = A ⊎ B
            ; i₁      = pureᵏ inj₁
            ; i₂      = pureᵏ inj₂
            ; [_,_]   = [_,_]
            ; inject₁ = λ _ → >>=-identityˡ-≈
            ; inject₂ = λ _ → >>=-identityˡ-≈
            ; unique  = λ h∘i₁≈f h∘i₂≈g → λ where
                (inj₁ a) → ≈ᴹ.trans (≈ᴹ.sym (h∘i₁≈f a)) >>=-identityˡ-≈
                (inj₂ b) → ≈ᴹ.trans (≈ᴹ.sym (h∘i₂≈g b)) >>=-identityˡ-≈
            }
        }
    }

  private
    δᵏ : (X × A) ⊎ (X × B) → M (X × (A ⊎ B))
    δᵏ = [ return ⊗ᵏ pureᵏ inj₁ , return ⊗ᵏ pureᵏ inj₂ ]

    δᵏ-isoˡ : (pureᵏ undistribute <=< δᵏ {X} {A} {B}) ≈ᵏ return
    δᵏ-isoˡ (inj₁ (x , a)) = ≈ᴹ.trans (⊗ᵏ-expand return (pureᵏ inj₁) _ (x , a))
      (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈)
    δᵏ-isoˡ (inj₂ (x , b)) = ≈ᴹ.trans (⊗ᵏ-expand return (pureᵏ inj₂) _ (x , b))
      (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈)

    δᵏ-isoʳ : (δᵏ <=< pureᵏ (undistribute {X} {A} {B})) ≈ᵏ return
    δᵏ-isoʳ (_ , inj₁ _) = ≈ᴹ.trans >>=-identityˡ-≈ (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈)
    δᵏ-isoʳ (_ , inj₂ _) = ≈ᴹ.trans >>=-identityˡ-≈ (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈)

  MonoidalDistributiveᵏ : MDᵏ.MonoidalDistributive
  MonoidalDistributiveᵏ = record
    { cocartesian       = Cocartesianᵏ
    ; distributeˡ-isIso = record
        { inv = pureᵏ undistribute
        ; iso = record { isoˡ = δᵏ-isoˡ ; isoʳ = δᵏ-isoʳ }
        }
    }

------------------------------------------------------------------------
-- The possibility monad

open Discrete (𝒫-KleisliTriple {0ℓ})
open KD (𝒫-KleisliTriple {0ℓ}) 𝒫-commutative
open Mealy Klᴹ-SymmetricMonoidal
open Machine
open State
open SymmetricMonoidalCategory Klᴹ-SymmetricMonoidal using (_⇒_; _⊗₀_)

module MD𝒫 = MD Klᴹ-SymmetricMonoidal

MDist : MD𝒫.MonoidalDistributive
MDist = MonoidalDistributiveᵏ (𝒫-KleisliTriple {0ℓ}) 𝒫-commutative

open MD𝒫.MonoidalDistributive MDist

private variable A B Msg X : Set

------------------------------------------------------------------------
-- What the interface tensor's ingredients are on TYPES

coproduct-on-Types : (A + B) ≡ (A ⊎ B)
coproduct-on-Types = refl

distributor-on-Types : ((X ⊗₀ A) + (X ⊗₀ B) ⇒ X ⊗₀ (A + B))
                     ≡ ((X × A) ⊎ (X × B) → List (X × (A ⊎ B)))
distributor-on-Types = refl

δ⇒-on-Types : {x : X} {a : A} → δ⇒ {X} {A} {B} (inj₁ (x , a)) ≡ ((x , inj₁ a) ∷ [])
δ⇒-on-Types = refl

δ⇐-on-Types : {x : X} {a : A} → δ⇐ {X} {A} {B} (x , inj₁ a) ≡ (inj₁ (x , a) ∷ [])
δ⇐-on-Types = refl

------------------------------------------------------------------------
-- Ergonomics: `do`-notation kernels and closed `eval`

-- `Spike.Instance.Type`'s `Cutᴹ`, with the kernel written in `do`-notation: the
-- adversary commits once and for all to forwarding or dropping.
Cutᴹ : Machine (Maybe Msg) (Maybe Msg)
Cutᴹ = record
  { state = record { obj = Maybe Bool ; point = pureᵏ (const nothing) ; discard = pureᵏ (const tt) }
  ; step  = λ where
      (nothing    , m) → do
        forward ← true ∷ false ∷ []
        return (just forward , (if forward then m else nothing))
      (just true  , m) → return (just true , m)
      (just false , _) → return (just false , nothing)
  }

eval-Cutᴹ : {m₁ m₂ : Msg} → eval Cutᴹ 2 (just m₁ , just m₂ , tt)
          ≡ ((just m₁ , just m₂ , tt) ∷ (nothing , nothing , tt) ∷ [])
eval-Cutᴹ = refl

-- …and the whole interface tensor instantiates at the possibilistic base too,
-- the word split included.
module 𝒫-Tensor = Tensor Klᴹ-SymmetricMonoidal MDist
