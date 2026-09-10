{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Seam.Grounding`'s statements, discharged at the trivial grade.
--
-- The grade is 𝒢's OWN monoidal unit read back as an interface
-- (`retᴵ 𝔾.unit`), not `unitᴵ`.  The two are the empty interface spelled with
-- two different empty types — `Data.Empty.⊥` against the base's initial object
-- — and `UC.Model.Unit` prices the iso between them at over the perf bar.  At
-- `retᴵ 𝔾.unit` no iso is needed: `T₁ ⟦ retᴵ 𝔾.unit ⟧ᴵ w` IS `id ⊗₁ w` at the
-- unit, so the unitor's naturality and its own iso — two fields of the monoidal
-- record, hence free — are all that is spent.  Nothing here reduces a machine.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
import Categories.Morphism.Reasoning as MR

open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚ; 𝒢ₚᴹ)
open import CategoricalCrypto.UC.Machine using (Proc; retᴵ; ucBaseᴹ)
open import CategoricalCrypto.UC.Seam.Grounding

import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Seam.Grounded where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module E = Em ucBaseᴹ

open 𝔾.HomReasoning
open E using (≈ℰ-congˡ; ≈ℰ-trans; ≈⇒≈ℰ; _∘_; _≈_)
open MR (𝒢ₚ 0ℓ) using (cancelˡ)

------------------------------------------------------------------------
-- The trivial grade

𝟘ᴳ : Iface
𝟘ᴳ = retᴵ 𝔾.unit

ιᴳ : (B : Iface) → Proc B (𝟘ᴳ ⊗ᴵ B)
ιᴳ B = 𝔾.unitorˡ.to

module TG = TrivialGrade 𝟘ᴳ ιᴳ

iotaBlind : TG.IotaBlind
iotaBlind B u v h =
  ≈ℰ-trans (≈⇒≈ℰ (⟺ (cancel u)))
           (≈ℰ-trans (≈ℰ-congˡ 𝔾.unitorˡ.from h) (≈⇒≈ℰ (cancel v)))
  where
  cancel : (w : Proc unitᴵ B) → (𝔾.unitorˡ.from ∘ (ιᴳ B ∘ w)) ≈ w
  cancel w = cancelˡ 𝔾.unitorˡ.isoʳ
