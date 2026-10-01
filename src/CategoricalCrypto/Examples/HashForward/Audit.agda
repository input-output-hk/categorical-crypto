{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Audit.audit-carry` at the nontrivial grade `X = ifaceᵒ Advᴵ`.  The
-- simulator it absorbs into the test is `procᵒ simulator`, a three-state
-- machine with an inhabited interface, whose two queries per `peekᴬ` are what
-- `absorbed-budget` charges.
--
-- No prefix tolerance is spent: the simulator's contribution is its actual
-- interaction, retained in the ideal experiment and counted by
-- `Examples.HashForward.UC.sim-hash-count`.  `docs/hash-forward.md` says what
-- a non-trivial designation of `UC.Audit.pinned` would cost.

open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Positive
import Data.Nat.Properties as ℕₚ
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Graded
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Audit
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using () renaming (QB to QBᴹ)
open import CategoricalCrypto.UC.Seam.Audit.Context
open import CategoricalCrypto.UC.Seam.Grounded

module CategoricalCrypto.Examples.HashForward.Audit (Msg Dig : Set) where

open import CategoricalCrypto.Examples.HashForward Msg Dig
open import CategoricalCrypto.Examples.HashForward.UC Msg Dig
open GradedSubCat gradingᵒ

2⁺ : ℕ⁺
2⁺ = positive 2

------------------------------------------------------------------------
-- The budgeted emulation

hf-emul : realᵒ ≤UC[ 2⁺ ] idealᵒ
hf-emul = ≤UC[]ᵍ simQB real-factors

simᶜ : LocallyGradedCategory.Hom L 2⁺ (ifaceᵒ Lkᴵ) (ifaceᵒ Advᴵ)
simᶜ = proj₁ hf-emul

-- `audit-carry` tests the ideal side through `Et ∘ id ⊗₁ (simᵒ ⊗₁ id)` — the
-- real side's context with the simulator in front of it — and this is the
-- rate that context carries: the tensor with identities is at `1⁺`, and
-- composition multiplies by the simulator's `2⁺`.
absorbed-budget : (W : Channel) {c : ℕ⁺} (Et : Test (W ⊗₀ (ifaceᵒ Advᴵ ⊗₀ ifaceᵒ Honᴵ)))
                → Image forget c Et → Image forget (2⁺ · c) (Et ∘ id ⊗₁ (simᵒ ⊗₁ id))
absorbed-budget W {c} Et ((ê , qe) , ê≈Et) =
    ( ê ∘ id ⊗₁ (simᵒ ⊗₁ id)
    , pred-sub ℕₚ.≤-refl (pred-∘ qe (pred-⊗ pred-id (pred-⊗ (qbᵒ {r = 2⁺} simQB) pred-id))))
  , ∘-resp-≈ˡ ê≈Et

------------------------------------------------------------------------
-- The carry

hf-audit-carry : (μ : ℕ → Dₚ Bool) (ε : ℕ → ℚ) (δ η : ℚ) → 0ℚ ℚ.< δ → 0ℚ ℚ.< η
               → ((q n : ℕ) → Pr≤ n (μ q) ℚ.≤ ε q)
               → AuditBound realᵒ (absorb simᶜ (pinned idealᵒ μ))
                   (λ q → (ε (scale q 2⁺) ℚ.+ δ) ℚ.+ η)
hf-audit-carry μ ε δ η δ>0 η>0 bnd =
  audit-carry realᵒ idealᵒ hf-emul
              {absorb simᶜ (pinned idealᵒ μ)} {pinned idealᵒ μ}
              (λ ev → ev)
              (λ q → ε q ℚ.+ δ) η η>0 (pinned-bound idealᵒ μ ε δ δ>0 bnd)

-- At the designation the toy supplies: an ideal monitored experiment that
-- reports `false` carries the bound `0`, so the real side's is the two slacks.
silent : ℕ → Dₚ Bool
silent _ = returnₚ false

silent-bound : (q n : ℕ) → Pr≤ n (silent q) ℚ.≤ 0ℚ
silent-bound q zero    = ≤-refl
silent-bound q (suc n) = ≤-reflexive (returnₚ-cum n false (indᵇ true))

hf-audit-silent : (δ η : ℚ) → 0ℚ ℚ.< δ → 0ℚ ℚ.< η
                → AuditBound realᵒ (absorb simᶜ (pinned idealᵒ silent))
                    (λ _ → (0ℚ ℚ.+ δ) ℚ.+ η)
hf-audit-silent δ η δ>0 η>0 = hf-audit-carry silent (λ _ → 0ℚ) δ η δ>0 η>0 silent-bound

-- `scale _ 2⁺` is the simulator's cost to the context's allowance (see
-- `absorbed-budget`).  The `Pr` is `Dₚ`'s: `real` is a raw machine, so
-- layer 1's `Bounded` is not available to it.
hf-pr-bound : (μ : ℕ → Dₚ Bool) (ε : ℕ → ℚ) (δ η : ℚ) → 0ℚ ℚ.< δ → 0ℚ ℚ.< η
            → ((q n : ℕ) → Pr≤ n (μ q) ℚ.≤ ε q)
            → (e : Strat (Neg Honᴵ) (Pos Honᴵ)) (a : Proc Advᴵ 𝟭ᴵ) (w : Proc unitᴵ Resᴵ)
              {q c c′ : ℕ⁺} (ae : asks≤ (value q) e) (ca : QBᴹ (value c) a) (cw : QBᴹ (value c′) w)
            → absorb simᶜ (pinned idealᵒ μ) (auditCtxᵍ Honᴵ e a real w {q} {c} {c′} ae ca cw)
            → (n : ℕ)
            → Pr≤ n (runᴹ (closedᵍ Honᴵ e a real w) e)
              ℚ.≤ (ε (scale (value (c · q · c′)) 2⁺) ℚ.+ δ) ℚ.+ η
hf-pr-bound μ ε δ η δ>0 η>0 bnd e a w {q} {c} {c′} ae ca cw mem =
  extractᵍ Honᴵ e a real w
    {ε = λ q → (ε (scale q 2⁺) ℚ.+ δ) ℚ.+ η} {𝔈 = absorb simᶜ (pinned idealᵒ μ)} {q} {c} {c′}
    ae ca cw mem (hf-audit-carry μ ε δ η δ>0 η>0 bnd)
