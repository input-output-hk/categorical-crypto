{-# OPTIONS --safe --without-K --guardedness #-}

-- The graded carry, run at `X = ifaceᵒ Advᴵ`.
--
-- `UC.Audit.audit-carry` is generic in the grade and always was; what was
-- missing was an application at one that is not `unit`.  Here the simulator it
-- absorbs into the test is `procᵒ simulator`, a three-state machine with an
-- inhabited interface, and its two queries per `peekᴬ` are what
-- `absorbed-budget` charges — the same certificate `audit-carry` builds
-- internally, stated so that the accounting is visible.
--
-- NO prefix tolerance is spent anywhere here.  `UC.Seam.Audit.TrivialGrade`'s
-- `watchedᵖ` widening exists because a trivial-grade simulator's contribution
-- to a context is an initialization one hopes is silent; this simulator's
-- contribution is its actual interaction, it is retained in the ideal
-- experiment, and `Examples.HashForward.UC.sim-hash-count` says exactly how
-- much of it there is.
--
-- The designated event is `UC.Audit.pinned`, at a designation the toy can
-- supply: the ideal monitored experiment reports `false`, so its bound is `0`.
-- That half is deliberately trivial — `docs/hash-forward.md` says what a
-- non-trivial designation would cost.

open import Data.Bool.Base using (Bool; false; true)
open import Data.Nat.Base using (ℕ; suc; zero; _*_; _⊔_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive)

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp using (Dₚ; returnₚ; returnₚ-cum)
open import ProbabilisticLogic.Dp.Advantage using (Pr≤)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Model.Bridge using (ucBaseᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; qbᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Seam.Audit
open import CategoricalCrypto.UC.Seam.Graded using (≤UC[]ᵍ)

module CategoricalCrypto.Examples.HashForward.Audit (Msg Dig : Set) where

open import CategoricalCrypto.Examples.HashForward Msg Dig
  using (Advᴵ; Honᴵ; Lkᴵ; Resᴵ; real-factors)
open import CategoricalCrypto.Examples.HashForward.UC Msg Dig
  using (idealᵒ; realᵒ; simQB; simᵒ)
open import CategoricalCrypto.UC.Emulation ucBaseᵒ
  using (Obj; Test; T₁; sub; _⊛_; _∘_)

private module Bud = Budget budgetᵒ

------------------------------------------------------------------------
-- The budgeted emulation

-- The simulator's allowance is 2 — one `peekᴬ` buys the leak fetch and the
-- hash query — and `Examples.HashForward.UC.simExactAll` says that is not
-- merely a ceiling.  A polynomial allowance for a FAMILY is this constant
-- read at every level; the toy has no security parameter, so there is nothing
-- for the polynomial to grow in.
hf-emul : realᵒ ≤UC[ 2 ] idealᵒ
hf-emul = ≤UC[]ᵍ simQB real-factors

------------------------------------------------------------------------
-- The monitoring context with the simulator absorbed

-- `audit-carry` tests the ideal side through `Et ∘ T₁ W (sub simᵒ)` — the real
-- side's context with the simulator in front of it — and this is the budget
-- that context carries: `qb-sub` and `qb-T₁` each guard at `⊔ 1`, and `qb-∘`
-- multiplies.  Read through `ctxBudget` it is `simCost` of the original.
absorbed-budget : (W : Obj) {c : ℕ} (Et : Test (W ⊛ (ifaceᵒ Advᴵ ⊛ ifaceᵒ Honᴵ)))
                → Bud.QB c Et → Bud.QB (c * ((2 ⊔ 1) ⊔ 1)) (Et ∘ T₁ W (sub simᵒ))
absorbed-budget W Et q = Bud.qb-∘ q (Bud.qb-T₁ (Bud.qb-sub (qbᵒ simQB)))

------------------------------------------------------------------------
-- The carry

-- At an arbitrary designation of the ideal experiment's observation.
hf-audit-carry : (μ : ℕ → Dₚ Bool) (ε : ℕ → ℚ) (δ η : ℚ) → 0ℚ ℚ.< δ → 0ℚ ℚ.< η
               → ((q n : ℕ) → Pr≤ n (μ q) ℚ.≤ ε q)
               → AuditBound realᵒ (absorb simᵒ 2 (pinned idealᵒ μ))
                   (λ q → (ε (simCost q 2) ℚ.+ δ) ℚ.+ η)
hf-audit-carry μ ε δ η δ>0 η>0 bnd =
  audit-carry realᵒ idealᵒ {2} hf-emul
              {absorb simᵒ 2 (pinned idealᵒ μ)} {pinned idealᵒ μ}
              (absorb-absorbs {s = simᵒ} {cs = 2} {𝔉 = pinned idealᵒ μ})
              (λ q → ε q ℚ.+ δ) η η>0 (pinned-bound idealᵒ μ ε δ δ>0 bnd)

-- …and at the one the toy supplies: an ideal monitored experiment that reports
-- `false` carries the bound `0`, so the real side's is the two slacks.
silent : ℕ → Dₚ Bool
silent _ = returnₚ false

silent-bound : (q n : ℕ) → Pr≤ n (silent q) ℚ.≤ 0ℚ
silent-bound q zero    = ≤-refl
silent-bound q (suc n) = ≤-reflexive (returnₚ-cum n false (indᵇ true))

hf-audit-silent : (δ η : ℚ) → 0ℚ ℚ.< δ → 0ℚ ℚ.< η
                → AuditBound realᵒ (absorb simᵒ 2 (pinned idealᵒ silent))
                    (λ _ → (0ℚ ℚ.+ δ) ℚ.+ η)
hf-audit-silent δ η δ>0 η>0 =
  hf-audit-carry silent (λ _ → 0ℚ) δ η δ>0 η>0 silent-bound
