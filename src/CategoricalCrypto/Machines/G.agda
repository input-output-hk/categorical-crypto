{-# OPTIONS --safe --without-K #-}

-- The machine layer as a traced symmetric monoidal category, and the
-- G construction over it.
--
-- Nothing here is a hypothesis: `Machines.Trace.Remaining`'s four laws are
-- theorems (`Machines.Trace.Laws`), and both records below are assembled from
-- terms.  What they certify is that the shapes line up — that `traceᴹ` inhabits
-- `Traced`'s `trace` field at *this* interface tensor, that `vanishing₁ᴹ` and
-- `yankingᴹ` are `Traced`'s own laws rather than lookalikes, and that the two
-- step-level naturalities are the ones `GConstruction` asks for.  In
-- particular, `GConstruction`'s `β` reduces to `Machines.Trace.βᴹ`.

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
open import Categories.Category.Monoidal.Traced
open import Categories.GConstruction
import Categories.Category.Monoidal.Distributive as MD

open import Level

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Laws as Laws
import CategoricalCrypto.Machines.Trace.Naturality as Naturality

module CategoricalCrypto.Machines.G
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open Bundle 𝒱 dist 𝒫
open Laws 𝒱 dist 𝒫 E
open MCat 𝒱 𝒫
open Naturality 𝒱 dist 𝒫 E
open Sim 𝒱 𝒫
open Trace 𝒱 dist 𝒫 E
open Trace.Remaining Remainingᴹ

Mealy-Traced : Traced Mealy-Monoidal
Mealy-Traced = record
  { symmetric   = Mealy-Symmetric
  ; trace       = λ {X} {A} {B} → traceᴹ A B X
  ; vanishing₁  = ≲⇒≈ᴹ (vanishing₁ᴹ _)
  ; vanishing₂  = vanishing₂ _
  ; superposing = superposing _
  ; yanking     = ≲⇒≈ᴹ yankingᴹ
  }

Mealy-G : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-G = GConstruction Mealy-Category Mealy-Monoidal Mealy-Traced
            trace-resp-≈ᴹ (trace-∘ˡ _ _) (trace-∘ʳ _ _) (trace-comm _)
