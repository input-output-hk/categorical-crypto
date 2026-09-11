{-# OPTIONS --safe --without-K --guardedness #-}

-- The two enrichment data `UC.Audit` asks of a base, at the sealed model: a
-- query budget for its grading and a mass for its observation.
--
-- `massᵒ` needs no coercion — `Mass` mentions only `Obs` and `_∼_`, both of
-- which `observationᵒ` shares with `Observationᴹ` on the nose.  `budgetᵒ` does:
-- `Budget` is stated over the grading, whose action is the sealed bundle's
-- tensor, so `Budget ∣𝔾ᵒ∣ (gradingᵗ 𝔾ᵒ)` is not `Budget (𝒢ₚ 0ℓ) gradingᴹ`
-- outside the block where `𝔾ᵒ` reduces.  It is the same record, so the
-- coercion is `p = p` exported from inside — `UC.Model.Seal`'s third
-- discipline, and the reason `UC.Machine.Grading`'s owed assembly is CHEAPER
-- here than at the transparent grading: under the seal there is nothing to
-- re-index.
--
-- Its own module because it is the one place in the Model cone that unfolds
-- the seal, and nothing here opens `StdUC`: `unfolding 𝔾ᵒ` in a module that
-- does is the 12 GiB configuration `docs/stduc-supersession-plan.md` finding
-- F5 records.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Bool.Base using (true)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁)
open import Level using (0ℓ; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ProbabilisticLogic.Dp.Advantage using (Pr≤)

open import CategoricalCrypto.Iface using (Iface)
open import CategoricalCrypto.UC.Approximate using (Mass)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Budget using (budgetᴹ)
open import CategoricalCrypto.UC.Model.Observation using (observationᵒ)
open import CategoricalCrypto.UC.Model.Seal using (∣𝔾ᵒ∣; 𝔾ᵒ; procᵒ; sealᵒ)
open import CategoricalCrypto.UC.QueryBound using (QB)
open import CategoricalCrypto.UC.QueryBound.Object using (qb-to-image)

import CategoricalCrypto.UC.Core.Standard as Std

module CategoricalCrypto.UC.Model.Enrichment where

budgetᵒ : Budget ∣𝔾ᵒ∣ (Std.gradingᵗ 𝔾ᵒ) (suc 0ℓ)
budgetᵒ = subst (λ M → Budget (MonoidalCategory.U M) (Std.gradingᵗ M) (suc 0ℓ))
                (sym sealᵒ) budgetᴹ

opaque
  unfolding sealᵒ

  -- …and the certificates that budget accepts, at the machine-layer spelling a
  -- consumer builds them in (`UC.Seam.Budget`).  Where the seal is transparent
  -- the transport above is `refl`, so this is `UC.Model.Seal`'s third
  -- discipline once more and nothing downstream needs an `unfolding`.
  qbᵒ : {A B : Iface} {c : ℕ} {f : Proc A B} → QB c f → Budget.QB budgetᵒ c (procᵒ f)
  qbᵒ {A} {B} = qb-to-image A B

-- The reading `Observation` deliberately lacks: a mass at a budget, and the
-- ε-domination that `_≈ₚ[_]_`'s left half already is, read off the agreement at
-- the slack asked for.  `Mass` is one-sided — an audit bound is a probability
-- of an event — so it takes the `true` half of the two-sided domination.
massᵒ : Mass observationᵒ
massᵒ = record { at = Pr≤ ; dominate = λ h δ δ>0 → proj₁ (h δ δ>0) true }
