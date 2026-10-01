{-# OPTIONS --safe --without-K --guardedness #-}

-- Family ingestion: a machine-layer advantage bound, level by level, read as
-- `UC.Model.Family`'s graded ℰ-agreement — and collapsed.
--
-- The premise is the shape a concrete security theorem has, and
-- `UC.Model.Dominated.dominatedᵒ` turns it into closeness under every ancilla
-- context at seal objects — what `_≈ℰ[_]_` quantifies over, at the budget the
-- context's two legs CARRY; the rest is the family layer's bookkeeping.
--
-- The slack `δ` is a parameter and the conclusion is at `ε + δ`, because the
-- domination is (its `δ` is arbitrary but positive, and `_≈ℰ[_]_` has no
-- ambient quantifier to hide it in).  It costs the consumer nothing: the two
-- collapses below ask for the SUM to be negligible, and negligibility is closed
-- under sums (`UC.Approximate.GradedBound-+[_]`), so any positive negligible `δ`
-- will do — `UC.Approximate.Decay.negligible-slack` is one.

open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.Model.Family.Ingest where

open GradedSubCat gradingᵒ
private module G = MonoidalCategory 𝔾ᵒ

module _ (B : ℕ → Iface) where

  -- The hom family a level-indexed closed process is: `conjᴵ` inflates it to
  -- the trivial grade (`UC.Machine.Bridge`), where the empty summand can never
  -- fire, and the polynomial it carries is its own query bound.
  conjᶠ : (u : (n : ℕ) → Proc unitᴵ (B n)) {p : ℕ → ℕ⁺} → Poly⁺ p
        → ((n : ℕ) → QB (value (p n)) (conjᴵ (u n))) → Δ 𝟘ᵒ ⇒^ω (Δ 𝟘ᵒ ⊛ω ifaceᶠ B)
  conjᶠ u {p} Pp w = p , Pp , λ n → gradedᵒ (conjᴵ (u n)) , qb-gradedᵒ {r = p n} (w n)

  infix 4 _≈advᴹ[_]_

  -- The premise: layer 1's `_≈adv[_]_` in the machine vocabulary the
  -- domination is stated at, and at every level.
  _≈advᴹ[_]_ : ((n : ℕ) → Proc unitᴵ (B n)) → (ℕ → ℕ → ℚ)
             → ((n : ℕ) → Proc unitᴵ (B n)) → Set
  u ≈advᴹ[ ε ] v = (n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
                 → runᴹ (u n) d ≈ₚ[ ε n q ] runᴹ (v n) d

  module _ {u v : (n : ℕ) → Proc unitᴵ (B n)} {p p′ : ℕ → ℕ⁺}
           (Pp : Poly⁺ p) (Pp′ : Poly⁺ p′)
           (wu : (n : ℕ) → QB (value (p n)) (conjᴵ (u n)))
           (wv : (n : ℕ) → QB (value (p′ n)) (conjᴵ (v n)))
           {ε δ : ℕ → ℕ → ℚ} (pos : (n q : ℕ) → 0ℚ ℚ.< δ n q)
           (adv : u ≈advᴹ[ ε ] v) where

    real ideal : Δ 𝟘ᵒ ⇒^ω (Δ 𝟘ᵒ ⊛ω ifaceᶠ B)
    real  = conjᶠ u {p} Pp wu
    ideal = conjᶠ v {p′} Pp′ wv

    εδ : ℕ → ℕ → ℚ
    εδ n q = ε n q ℚ.+ δ n q

    ingest : real ≈ℰ[ εδ ] ideal
    ingest Y Et m {pc} _ cE n =
      dominatedᵒ (B n) (Y n) ⌊ hom Et n ⌋ ⌊ hom m n ⌋ (cE n) (hom m n , G.Equiv.refl)
                 (u n) (v n) (ε n k) (δ n k) (pos n k) (adv n k)
      where k = value (pc n · schedOf m n)

    -- The collapses: `absorb-negl` spends only vanishing, `_≈ℰⁿ_` keeps the
    -- witness a negligible-graded consumer needs (`UC.Family`'s header), and the
    -- order is where the metatheory is read.
    module _ (nε : NegligibleBound ε) (nδ : NegligibleBound δ) where

      ingest-negligible : NegligibleBound εδ
      ingest-negligible = GradedBound-+[ Negligible ] Negligible-+ ε δ nε nδ

      -- The bound and the two families are passed rather than inferred, for
      -- `GradedBound-+[_]`'s reason: `_≈ℰ[_]_` and `CarriedNegligible` both
      -- read their arguments under an application, which is no pattern.
      ingest-≈ᵁ : real ≈ᵁ ideal
      ingest-≈ᵁ = absorb-negl {f = real} {ideal} {εδ} ingest ingest-negligible

      ingest-≈ℰⁿ : real ≈ℰⁿ ideal
      ingest-≈ℰⁿ = εδ , carried-negligible {ε = εδ} ingest-negligible , ingest

      ingest-≤UCᵁ : real Canonical^ω.≤UC ideal
      ingest-≤UCᵁ = Canonical^ω.≈ᵁ⇒≤UC {f = real} {ideal} ingest-≈ᵁ
