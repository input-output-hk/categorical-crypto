{-# OPTIONS --safe --without-K --guardedness #-}

-- `ContextDominated`, reduced to the two-machine skeleton.
--
-- `UC.Machine.Slide` turns the bridge's ancilla context into a plain closed
-- context `Kctx` carrying `ctxBudget c c′`, so what is left of the obligation
-- is the same statement at a CLOSED context and one process — the shape
-- `Adequacy` and `Counting` are already written at.  That is `Skeleton`, and
-- the reduction below is all the ancilla, the closure and the grade cost.
--
-- The δ is spent here and nowhere else: the skeleton is an ε-statement, and
-- `≈ₚ[]-mono` widens it to `ε + δ` because δ is positive.  That is the sense in
-- which the bridge's arbitrary positive slack "costs a consumer nothing" — no
-- step of the reduction needs it.
--
-- What `Skeleton` still asks for is the branchwise decomposition itself: read
-- the context's activation sequence off its certificate as a `Strat` — a
-- crossing into the hole is an `ask`, a coin is a `coin`, a verdict is an
-- `out` — and reassemble the per-branch bounds by convexity of `Pr≤`.  It is
-- an ε-statement about two `iterₚ` loops that differ only in their context
-- factor, so what it needs and the layer does not have is a ONE-SIDED,
-- budget-indexed transfer for `iterₚ`: `Dp.Iter.Transfer` supplies the
-- two-sided one along a pure state map, and a strategy tree is finite while a
-- `Dₚ` context's coin tree is not, so no pure state map exists.

open import Categories.Category using (Category)

open import Data.Nat.Base using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties as ℚP
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (sym)

open import ProbabilisticLogic.Dp using (≈ₚ-sym)
open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_; ≈ₚ[]-mono; ≈ₚ[]-resp)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; ⟦_⟧ᴼ)
open import CategoricalCrypto.UC.Machine.Bridge using (ContextDominated)
open import CategoricalCrypto.UC.Machine.Slide using (Kctx; ctxRun-slide; qb-Kctx)
open import CategoricalCrypto.UC.QueryBound using (QB)

module CategoricalCrypto.UC.Machine.Dominated where

private module 𝒫 = Category 𝒫ᴵ

-- The obligation at a closed context: if no strategy of the context's budget
-- separates the two processes by more than ε, neither does the context.
Skeleton : Set₁
Skeleton = (B : Iface) (K : Proc B Ωᴵ) {q : ℕ} → QB q K
         → (u v : Proc unitᴵ B) (ε : ℚ)
         → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
         → ⟦ K 𝒫.∘ u ⟧ᴼ ≈ₚ[ ε ] ⟦ K 𝒫.∘ v ⟧ᴼ

skeleton⇒dominated : Skeleton → ContextDominated
skeleton⇒dominated sk B Y E m qE qm u v ε δ 0<δ h =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (ctxRun-slide E m u)) (≈ₚ-sym _ _ (ctxRun-slide E m v))
    (≈ₚ[]-mono ε≤ε+δ (sk B (Kctx E m) (qb-Kctx E m qE qm) u v ε h))
  where
  ε≤ε+δ : ε ℚ.≤ ε ℚ.+ δ
  ε≤ε+δ = ℚP.≤-trans (ℚP.≤-reflexive (sym (ℚP.+-identityʳ ε)))
                     (ℚP.+-monoʳ-≤ ε (ℚP.<⇒≤ 0<δ))
