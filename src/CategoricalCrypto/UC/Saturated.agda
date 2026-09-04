{-# OPTIONS --safe --without-K #-}

-- The saturated form of a concrete safety bound.
--
-- What the UC core carries is what its observational equivalence cannot see, so
-- the shape a concrete statement should have is one INVARIANT under that
-- equivalence.  At the asymptotic instance the equivalence is vanishing
-- advantage, and the exact bound is not invariant under it: a system
-- negligibly different from `P` at every polynomial budget can exceed `ε q` by
-- that negligible amount, so `Bounded P bad ε` holds while `Bounded Q bad ε`
-- fails, for a `Q` the layer above declares equal to `P`.  The cure is not a
-- weaker bound but an existentially quantified negligible slack: `ε q + ν n`
-- for SOME negligible `ν`, which absorbs the difference between any two
-- observationally-equal systems while still forbidding a constant loss.  That
-- is the notes' `POV-modulo-negligible`.
--
-- The two forms below are the same shape over layer 1's two observables, and
-- they behave differently on purpose:
--
--   `SaturatedBounded` reads the system's own ANSWERS (`Pr`, an
--   interface-observable event), and its invariance is `transfer` plus
--   negligibility arithmetic — stated as `SaturatedRespects`, priced.
--
--   `SaturatedHit` reads the STATE TRAJECTORY (`PrHit`), which no environment
--   sees, so it is saturated in the slack but NOT invariant: a simulator's
--   state is not the ideal system's.  That asymmetry is why the ledger example
--   states the trajectory bound and carries the audit bound, the two tied by
--   its own `TrajectoryFromAudit` — the concrete face of
--   `UC.Audit.audit-carry`'s interface-observability restriction.

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_)
open import Data.Rational as ℚ using (ℚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol; St)
open import CategoricalCrypto.Protocol.Observe using (Pr; PrHit; _≈adv[_]_)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (VanishingBound; _→0)

module CategoricalCrypto.UC.Saturated where

private variable B : ℕ → Iface

-- A family of closed systems indexed by the security parameter: a negligible
-- slack needs a parameter to vanish in, and the exact-versus-saturated
-- distinction only exists asymptotically.
Systems : (ℕ → Iface) → Set₁
Systems B = (n : ℕ) → Protocol unitᴵ (B n)

Bad : Systems B → Set
Bad {B} P = (n : ℕ) → St (P n) → Bool

Watch : (B : ℕ → Iface) → Set
Watch B = (n : ℕ) → Strat (Neg (B n)) (Pos (B n))
        → Strat (Neg (B n)) (Pos (B n))

-- The audit form, saturated: no budget-`q` strategy makes the watched event's
-- probability exceed `ε n q`, up to one negligible `ν` chosen once for the
-- whole family.
SaturatedBounded : (P : Systems B) → Watch B → (ℕ → ℕ → ℚ) → Set
SaturatedBounded {B} P bad ε = Σ[ ν ∈ (ℕ → ℚ) ] ν →0
  × ((n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
     → Pr (P n) (bad n d) ℚ.≤ ε n q ℚ.+ ν n)

-- The trajectory form, saturated the same way — and see the header for why the
-- invariance below is stated for the audit form only.
SaturatedHit : (P : Systems B) → Bad P → (ℕ → ℕ → ℚ) → Set
SaturatedHit {B} P bad ε = Σ[ ν ∈ (ℕ → ℚ) ] ν →0
  × ((n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
     → PrHit (P n) (bad n) d ℚ.≤ ε n q ℚ.+ ν n)

-- Invariance, stated and priced at ~60–100 LOC: `transfer` at each `n` moves
-- the bound to `ε n q + (ν n + δ n (…))`, so the work is arithmetic — that the
-- sum of a negligible function and a vanishing bound evaluated at the
-- strategy's own polynomial budget is again negligible, which is `_→0` closed
-- under `+` and under precomposition with a polynomial.  Both closure lemmas
-- are ℚ/ℕ facts with no UC content; neither exists yet.
SaturatedRespects : Set₁
SaturatedRespects = {B : ℕ → Iface} (P Q : Systems B) (bad : Watch B)
                    (ε δ : ℕ → ℕ → ℚ)
                  → ((n : ℕ) → P n ≈adv[ δ n ] Q n) → VanishingBound δ
                  → ((n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n)))
                     → asks≤ q d → asks≤ q (bad n d))
                  → SaturatedBounded P bad ε → SaturatedBounded Q bad ε
