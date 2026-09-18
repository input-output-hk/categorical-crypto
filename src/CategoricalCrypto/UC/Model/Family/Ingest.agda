{-# OPTIONS --safe --without-K --guardedness #-}

-- Family ingestion: a machine-layer advantage bound, level by level, read as
-- `UC.Model.Family`'s graded ℰ-agreement — and collapsed
-- (`docs/end-to-end.md`'s continuation spec item 1).
--
-- The premise is the shape a concrete security theorem has and the one
-- `UC.Machine.Bridge`'s domination consumes: at each level, no strategy of a
-- given budget separates the two direct runs by more than `ε` of that budget.
-- `UC.Model.Dominated.dominatedᵒ` turns it into closeness under every ancilla
-- CONTEXT, at seal objects, which is exactly what `_≈ℰ[_]_` quantifies over,
-- and the budget both sides read `ε` at is the one the context's two legs
-- CARRY.  So the whole ingestion is that theorem plus the family layer's own
-- bookkeeping; nothing here is quantitative.
--
-- The slack `δ` is a parameter and the conclusion is at `ε + δ`, because the
-- domination is (its `δ` is arbitrary but positive, and `_≈ℰ[_]_` has no
-- ambient quantifier to hide it in).  It costs the consumer nothing: the two
-- collapses below ask for the SUM to be negligible, and negligibility is closed
-- under sums (`UC.Approximate.GradedBound-+[_]`), so any positive negligible `δ`
-- will do — `UC.Approximate.Decay.negligible-slack` is one, and the same
-- parameter appears for the same reason at layer 1 (`UC.Asymptotic.uc-≈negl`).
--
-- With the agreement in hand the inherited metatheory applies to a concrete
-- family: `≈ℰ⇒≤UC` puts it in the core's order at the identity simulator, where
-- `≤UC-trans` and `dummy-complete` are `UC.Family`'s own, and `≈ℰ^ω⇒≤UC` puts
-- it in the INHERITED one, where `UC-compose` is — that identification is
-- `UC.Core.Bridge`, generic in the base, applied at the family by
-- `UC.Family.Vanishing`.

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate
  using (GradedBound-+[_]; Negligible; Negligible-+; NegligibleBound)
open import CategoricalCrypto.UC.Budget using (ctxBudget)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Bridge using (conjᴵ)
open import CategoricalCrypto.UC.Model.Dominated using (dominatedᵒ; qb-gradedᵒ)
open import CategoricalCrypto.UC.Model.Family
  using ( Obj^ω; Δ; _⇒^ω_; _⊛ω_; _≈ℰ[_]_; _≈ℰ_; _≈ℰⁿ_; _≤UC_; module Canonical^ω
        ; absorb-negl; carried-negligible; ≈ℰ⇒≤UC; ≈ℰ^ω⇒≤UC )
open import CategoricalCrypto.UC.Model.Observation using (𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ)
open import CategoricalCrypto.UC.QueryBound using (QB)

module CategoricalCrypto.UC.Model.Family.Ingest where

module _ (B : ℕ → Iface) where

  -- The interfaces as an object family of the seal, and the hom family a
  -- level-indexed closed process is: `conjᴵ` inflates it to the trivial grade
  -- (`UC.Machine.Bridge`), where the empty summand can never fire, and the
  -- polynomial it carries is its own query bound.
  ifaceᶠ : Obj^ω
  ifaceᶠ n = ifaceᵒ (B n)

  conjᶠ : (u : (n : ℕ) → Proc unitᴵ (B n)) {p : ℕ → ℕ} → Poly p
        → ((n : ℕ) → QB (p n) (conjᴵ (u n))) → Δ 𝟘ᵒ ⇒^ω (Δ 𝟘ᵒ ⊛ω ifaceᶠ)
  conjᶠ u {p} Pp w = (λ n → gradedᵒ (conjᴵ (u n))) , p , Pp , λ n → qb-gradedᵒ (w n)

  infix 4 _≈advᴹ[_]_

  -- The premise: layer 1's `_≈adv[_]_` in the machine vocabulary the
  -- domination is stated at, and at every level.
  _≈advᴹ[_]_ : ((n : ℕ) → Proc unitᴵ (B n)) → (ℕ → ℕ → ℚ)
             → ((n : ℕ) → Proc unitᴵ (B n)) → Set
  u ≈advᴹ[ ε ] v = (n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
                 → runᴹ (u n) d ≈ₚ[ ε n q ] runᴹ (v n) d

  module _ {u v : (n : ℕ) → Proc unitᴵ (B n)} {p p′ : ℕ → ℕ}
           (Pp : Poly p) (Pp′ : Poly p′)
           (wu : (n : ℕ) → QB (p n) (conjᴵ (u n)))
           (wv : (n : ℕ) → QB (p′ n) (conjᴵ (v n)))
           {ε δ : ℕ → ℕ → ℚ} (pos : (n q : ℕ) → 0ℚ ℚ.< δ n q)
           (adv : u ≈advᴹ[ ε ] v) where

    -- The two compared families, and the bound the ingestion lands at: the
    -- premise's, widened by the slack the domination charges.
    real ideal : Δ 𝟘ᵒ ⇒^ω (Δ 𝟘ᵒ ⊛ω ifaceᶠ)
    real  = conjᶠ u Pp wu
    ideal = conjᶠ v Pp′ wv

    εδ : ℕ → ℕ → ℚ
    εδ n q = ε n q ℚ.+ δ n q

    ingest : real ≈ℰ[ εδ ] ideal
    ingest Y (Et , pE , _ , wE) (m , pm , _ , wm) n =
      dominatedᵒ (B n) (Y n) (Et n) (m n) (wE n) (wm n) (u n) (v n)
                 (ε n (ctxBudget (pE n) (pm n))) (δ n (ctxBudget (pE n) (pm n)))
                 (pos n (ctxBudget (pE n) (pm n)))
                 (adv n (ctxBudget (pE n) (pm n)))

    -- The collapses, at the §3 discipline: `absorb-negl` spends only vanishing,
    -- `_≈ℰⁿ_` keeps the witness a negligible-graded consumer needs
    -- (`UC.Family`'s header), and the order is where the metatheory is read.
    module _ (nε : NegligibleBound ε) (nδ : NegligibleBound δ) where

      ingest-negligible : NegligibleBound εδ
      ingest-negligible = GradedBound-+[ Negligible ] Negligible-+ ε δ nε nδ

      -- The bound and the two families are passed rather than inferred, for
      -- `GradedBound-+[_]`'s reason: `_≈ℰ[_]_`, `_≈ℰ_` and `CarriedNegligible`
      -- all read their arguments under an application, which is no pattern.
      ingest-≈ℰ : real ≈ℰ ideal
      ingest-≈ℰ = absorb-negl {f = real} {ideal} {εδ} ingest ingest-negligible

      ingest-≈ℰⁿ : real ≈ℰⁿ ideal
      ingest-≈ℰⁿ = εδ , carried-negligible {ε = εδ} ingest-negligible , ingest

      ingest-≤UC : real ≤UC ideal
      ingest-≤UC = ≈ℰ⇒≤UC {f = real} {ideal} ingest-≈ℰ

      -- …and in the INHERITED order, which is where `UC-compose` is
      -- (`UC.Family.Vanishing`, over the generic `UC.Core.Bridge`).
      ingest-≤UCᵁ : real Canonical^ω.≤UC ideal
      ingest-≤UCᵁ = ≈ℰ^ω⇒≤UC real ideal ingest-≈ℰ
