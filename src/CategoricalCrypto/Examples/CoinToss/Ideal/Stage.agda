{-# OPTIONS --safe --without-K --guardedness #-}

-- What both coin-toss corruptions compose (`Ideal.Hybrid`,
-- `Ideal.Receiver.Hybrid`): `T₁ᴵ Lk toss` after the ideal wire over the
-- commitment's resource, its pointwise unfolding, and the reading of the
-- composite as one machine `c′` under the boundary's reassociation.

open import Data.Bool.Base using (Bool)
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base as Sum

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import Categories.Category

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire

import CategoricalCrypto.Examples.ROCommitment as RO
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.UC.Machine.Composite as CS

module CategoricalCrypto.Examples.CoinToss.Ideal.Stage
  (k : ℕ) (Lk Hon Adv Honᶜ : Iface) (toss : Proc Hon (Adv ⊗ᴵ Honᶜ))
  (downᶠ : Neg (Lk ⊗ᴵ Hon) → Neg (RO.Resᴵ k)) (upᶠ : Pos (RO.Resᴵ k) → Pos (Lk ⊗ᴵ Hon)) where

open import CategoricalCrypto.Examples.ROCommitment k hiding (downᶠ; upᶠ)
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open MC

private
  module S  = Pw.S
  module 𝒫  = Category 𝒫ᴵ

  Cⁱ Cᵗ : Iface
  Cⁱ = Lk ⊗ᴵ (Adv ⊗ᴵ Honᶜ)
  Cᵗ = (Lk ⊗ᴵ Adv) ⊗ᴵ Honᶜ

resᴵᵈ : Proc unitᴵ (Lk ⊗ᴵ Hon)
resᴵᵈ = sandwichᴹ resource (Sum.map₂ downᶠ) (Sum.map₂ upᶠ)

stageᴴ : Proc (Lk ⊗ᴵ Hon) Cⁱ
stageᴴ = T₁ᴵ Lk toss

-- The hybrid as `UC.Graded.ext-graded`/`graded₂-∘` leave it.
hybridᴹ : Proc unitᴵ Cᵗ
hybridᴹ = 𝒫._∘_ {unitᴵ} {Resᴵ} {Cᵗ}
            (𝒫._∘_ {Resᴵ} {Cⁱ} {Cᵗ} a⇐ᴵ (𝒫._∘_ {Resᴵ} {Lk ⊗ᴵ Hon} {Cⁱ} stageᴴ (wireᴹ upᶠ downᶠ)))
            resource

module Hᶜ = CS.CP unitᴵ (Lk ⊗ᴵ Hon) Cⁱ stageᴴ resᴵᵈ
module Hᵁ = Hᶜ.Unfolding (CS.unfoldᶜ unitᴵ (Lk ⊗ᴵ Hon) Cⁱ stageᴴ resᴵᵈ)
module Hᵂ = Hᶜ.Walk (CS.unfoldᶜ unitᴵ (Lk ⊗ᴵ Hon) Cⁱ stageᴴ resᴵᵈ)

Hᴺ : Proc unitᴵ Cⁱ
Hᴺ = CS.Nᶜ unitᴵ (Lk ⊗ᴵ Hon) Cⁱ stageᴴ resᴵᵈ

stepᴴ = CS.stepᶜ unitᴵ (Lk ⊗ᴵ Hon) Cⁱ stageᴴ resᴵᵈ

hearᴴ : (sg : obj (state toss)) (t : Tbl) (m : Maybe Bool) (q : Neg Lk)
        {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}
      → step resource ((t , m) , inj₂ (downᶠ (inj₁ q))) ≈ₚ D
      → stepᴴ ((sg , (t , m)) , inj₂ (inj₁ q))
      ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map₂ upᶠ (proj₂ w)))
hearᴴ sg t m q eq =
      Hᵂ.R-down sg (t , m) (inj₁ q) sg (inj₁ q) ≈refl (bindˣ eq)
  ⟨≈⟩ >>=ₚ-assoc _ _ _
  ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)

hybrid-eq : (c′ : Proc unitᴵ Cⁱ) → c′ S.≲ Hᴺ
          → 𝒫._≈_ {unitᴵ} {Cᵗ} hybridᴹ (sandwichᴹ c′ (Sum.map₂ Sum.assocʳ) (Sum.map₂ Sum.assocˡ))
hybrid-eq c′ sim =
       𝒫.assoc
  S.○ᴹ 𝒫.∘-resp-≈ʳ (𝒫.assoc S.○ᴹ 𝒫.∘-resp-≈ʳ (wire-∘ᴹ upᶠ downᶠ resource))
  S.○ᴹ 𝒫.∘-resp-≈ʳ (S.⟺ᴹ (CS.eq-∘ᶜ unitᴵ (Lk ⊗ᴵ Hon) Cⁱ stageᴴ resᴵᵈ) S.○ᴹ S.≲⇒≈ᴹ˘ sim)
  S.○ᴹ wire-∘ᴹ Sum.assocˡ Sum.assocʳ c′
