{-# OPTIONS --safe --without-K --guardedness #-}

-- The two empty objects of `𝒢ₚ`, canonically isomorphic.
--
-- `⟦ unitᴵ ⟧ᴵ` is `(⊥ , ⊥)` at `Data.Empty.⊥`; `𝒢ₚᴹ`'s monoidal unit is `(⊥ , ⊥)`
-- at the BASE's initial object.  Three steps, each generic:
--
--   1. `Data.Empty.⊥` is initial in the base too (a Kleisli map out of it is
--      `⊥-elim`, and so is every other), so `Initial.up-to-iso` compares them.
--   2. `pureᴹ` is a functor, so it carries the base iso to the machine layer.
--   3. `GConstructionEmbedding.⌜⌝-≅` carries a pair of machine isos to a G-iso.
--      This is where the ⊕-trace is absorbed, and it is absorbed GENERICALLY —
--      inside `absorbˡ`/`absorbʳ`, which is what those lemmas exist for.  No
--      trace is evaluated at this instance.
--
-- Quarantined in its own module because it is the only place in the Model cone
-- that names the TRANSPARENT machine bundle, and that is measured: instantiating
-- `Embed.WithTrace` as a MODULE (`module _ = GE.Embed.WithTrace …`, or the
-- `open … using (⌜⌝-≅)` that desugars to one) copies every sibling definition,
-- whose types mention `G._∘_` — hence the trace — and exhausts 8 GiB.  Applying
-- the one lemma through its qualified name instead never forms those types.

open import Categories.Category.Monoidal.Bundle
  using (MonoidalCategory; SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Distributive as MD
import Categories.GConstructionEmbedding as GE
import Categories.Morphism as Mor
import Categories.Object.Initial as Init

open import Data.Empty as Empty using (⊥-elim)
open import Data.Product.Base using (_,_)
open import Level using (0ℓ)

open import CategoricalCrypto.Machines.Base
  using (Elgotₚ; Remainingₚ; distₚ; 𝒫ₚ; 𝒢ₚ; 𝒢ₚᴹ; 𝒱ₚ)

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.G as MG
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Naturality as Naturality

module CategoricalCrypto.UC.Model.Unit.Empty where

private
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)

  open MD.MonoidalDistributive (distₚ 0ℓ) using (initial; ⊥)
  open Bundle (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) using (Mealy-Monoidal)
  open MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ) using (Mealy-Category)
  open Naturality (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ) using (trace-∘ˡ; trace-∘ʳ)
  open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ) using (_○ᴹ_; ≲⇒≈ᴹ)
  open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) using (pureᴹ; pureᴹ-cong; pureᴹ-id; pureᴹ-∘)
  open Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ) using (Remaining)
  open Remaining (Remainingₚ 0ℓ) using (trace-comm; trace-resp-≈ᴹ)

  𝟎-initial : Init.Initial 𝒱.U
  𝟎-initial = record
    { ⊥ = Empty.⊥
    ; ⊥-is-initial = record { ! = λ x → ⊥-elim x ; !-unique = λ _ x → ⊥-elim x }
    }

  empty-≅ : Mor._≅_ 𝒱.U Empty.⊥ ⊥
  empty-≅ = Init.up-to-iso 𝒱.U 𝟎-initial initial

  pure-≅ : {V W : 𝒱.Obj} → Mor._≅_ 𝒱.U V W → Mor._≅_ Mealy-Category V W
  pure-≅ i = record
    { from = pureᴹ i.from
    ; to   = pureᴹ i.to
    ; iso  = record
      { isoˡ = ≲⇒≈ᴹ (pureᴹ-∘ i.to i.from)
             ○ᴹ ≲⇒≈ᴹ (pureᴹ-cong i.isoˡ) ○ᴹ ≲⇒≈ᴹ pureᴹ-id
      ; isoʳ = ≲⇒≈ᴹ (pureᴹ-∘ i.from i.to)
             ○ᴹ ≲⇒≈ᴹ (pureᴹ-cong i.isoʳ) ○ᴹ ≲⇒≈ᴹ pureᴹ-id
      }
    }
    where module i = Mor._≅_ i

  empty-≅ᴹ : Mor._≅_ Mealy-Category Empty.⊥ ⊥
  empty-≅ᴹ = pure-≅ empty-≅

unit-≅ᴳ : Mor._≅_ (𝒢ₚ 0ℓ) (Empty.⊥ , Empty.⊥) (MonoidalCategory.unit (𝒢ₚᴹ 0ℓ))
unit-≅ᴳ =
  GE.Embed.WithTrace.⌜⌝-≅ Mealy-Category Mealy-Monoidal
    (MG.Mealy-Traced (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ))
    trace-resp-≈ᴹ (trace-∘ˡ _ _) (trace-∘ʳ _ _) (trace-comm _)
    empty-≅ᴹ (Mor.≅.sym Mealy-Category empty-≅ᴹ)
