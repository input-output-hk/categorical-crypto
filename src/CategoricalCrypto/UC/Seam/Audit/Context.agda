{-# OPTIONS --safe --without-K --guardedness #-}

-- The context an audit bound is extracted at, and what a graded bound at any
-- class permitting it gives back.
--
-- The context is the one `UC.Seam.Grounded` already builds — an embedded
-- strategy behind the two unitors that kill the grade and the ancilla.  Three
-- things make it one of the contexts an audit event can permit, and all three
-- are theorems elsewhere:
--
--   budget  `UC.Seam.Budget.qb-strategyEnv` at the strategy's own ask-depth, the
--           two unitors at `Budget`'s own certificates, hence `ctxBudget q 1 = q`
--   run     `UC.Seam.Grounded.plug-run` and `UC.Seam.Adequacy.adequacy` identify
--           the context's observation with layer 1's run
--   mass    `Protocol.Machine.Agree.prAgree` reads `Pr` off that run at a budget
--           the `_≼ₚ_` half of the identification reaches
--
-- `extract` spends those once with the event class as a PARAMETER and the
-- membership as a hypothesis, which is what lets the same three ingredients
-- serve `watched` (`UC.Seam.Audit.Bounded`), its prefix-tolerant widening, and
-- the simulator-absorbed pullback (`UC.Seam.Audit.Prefix`) alike.  The class a
-- bound is stated at need not be a statement about the process the bound is
-- about — the absorbed class is a statement about the IDEAL process while the
-- bound is about the real one — so keeping it a parameter is not generality for
-- its own sake but the shape review §2's inclusion obligation has.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗)
import Categories.Morphism.Reasoning as MR

open import Data.Bool.Base using (Bool; true)
open import Data.Nat.Base using (ℕ; _*_; _+_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-trans)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp using (Dₚ; _≈ₚ_; ≈ₚ-sym; ≈ₚ-trans)
open import ProbabilisticLogic.Dp.Advantage using (Pr≤; indᵇ-nn)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Machine.Agree using (prAgree)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ)
open import CategoricalCrypto.UC.Model.Bridge using (ucBaseᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; qbᵒ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ; obs-resp)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam using (strategyEnv)
open import CategoricalCrypto.UC.Seam.Adequacy using (adequacy)
open import CategoricalCrypto.UC.Seam.Audit using (AuditBound; AuditEvent)
open import CategoricalCrypto.UC.Seam.Budget using (qb-strategyEnv)
open import CategoricalCrypto.UC.Seam.Grounded using (𝟘ᴳ; ιᴳ; plug-λ; plug-run)

module CategoricalCrypto.UC.Seam.Audit.Context where

open import CategoricalCrypto.UC.Emulation ucBaseᵒ using (obs; tv₁)

open HomReasoning
open Budget budgetᵒ using (QB; qb-∘; qb-mono; qb-λ⇒; qb-λ⇐)
open MR ∣machines∣ using (cancelInner)

-- The ancilla is deflated away, whatever the interface below it.
auditClose : 𝟘ᵒ ⇒ T₀ 𝟘ᴳ 𝟘ᵒ
auditClose = unitorˡ.to

module _ (B : Iface) (e : Strat (Neg B) (Pos B)) where

  private
    env : Proc B Ωᴵ
    env = strategyEnv B e

    test : T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ
    test = procᵒ env ∘ unitorˡ.from

  -- The context: the embedded strategy with the grade and the ancilla deflated.
  auditTest : T₀ 𝟘ᴳ (T₀ 𝟘ᴳ (ifaceᵒ B)) ⇒ Ωᵒ
  auditTest = test ∘ unitorˡ.from

  audit-qb : (q : ℕ) → asks≤ q e → QB q auditTest
  audit-qb q a =
    qb-mono (ℕP.≤-reflexive (trans (ℕP.*-identityʳ (q * 1)) (ℕP.*-identityʳ q)))
      (qb-∘ (qb-∘ (qbᵒ (qb-strategyEnv B q e a)) qb-λ⇒) qb-λ⇒)

  -- Both wires cancel, what is left is the plugged strategy, and its
  -- observation is layer 1's run of `e`.
  audit-run : (w : Proc unitᴵ B)
            → obs (tv₁ 𝟘ᴳ (ιᴳ B ∘ procᵒ w) auditTest) auditClose ≈ₚ runᴹ w e
  audit-run w =
    ≈ₚ-trans _ _ _ (obs-resp reduce)
      (≈ₚ-trans _ _ _ (≈ₚ-sym _ _ (plug-run B e w)) (adequacy B w e))
    where
    reduce : ((auditTest ∘ id ⊗₁ (ιᴳ B ∘ procᵒ w)) ∘ auditClose) ≈ procᵒ env ∘ procᵒ w
    reduce = ((refl⟩∘⟨ ⟺ (T₁-⊗ 𝔾ᵒ 𝟘ᴳ (ιᴳ B ∘ procᵒ w))) ⟩∘⟨refl)
           ○ plug-λ test (ιᴳ B ∘ procᵒ w) ○ cancelInner unitorˡ.isoʳ

-- A graded bound at any class this context inhabits IS layer 1's `Bounded`.
-- The `bad`-budget hypothesis is what lets the run and the mass meet: `Bounded`
-- charges `ε` at the budget of `d` while the context is built from `bad d`.
extract : {B : Iface} (P : Protocol unitᴵ B)
          (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
          {𝔈 : AuditEvent 0ℓ 𝟘ᵒ 𝟘ᴳ (ifaceᵒ B)}
        → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
        → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d
           → 𝔈 𝟘ᴳ (auditTest B (bad d)) auditClose (q * 1))
        → AuditBound (ιᴳ B ∘ procᵒ (morphism P)) 𝔈 ε
        → Bounded P bad ε
extract {B} P bad ε bad-asks mem bnd q d a =
  subst (λ z → z ℚ.≤ ε q) (reads 0) chain
  where
  run : Dₚ Bool
  run = runᴹ (morphism P) (bad d)

  obsv : Dₚ Bool
  obsv = obs (tv₁ 𝟘ᴳ (ιᴳ B ∘ procᵒ (morphism P)) (auditTest B (bad d))) auditClose

  near : obsv ≈ₚ run
  near = audit-run B (bad d) (morphism P)

  pa = prAgree true P (bad d)
  reads = proj₂ pa

  reach = proj₂ near (indᵇ true) (indᵇ-nn true) (proj₁ pa + 0)

  chain : Pr≤ (proj₁ pa + 0) run ℚ.≤ ε q
  chain = ≤-trans (proj₂ reach)
            (subst (λ k → Pr≤ (proj₁ reach) obsv ℚ.≤ ε k) (ℕP.*-identityʳ q)
                   (bnd 𝟘ᴳ (auditTest B (bad d)) auditClose
                        (audit-qb B (bad d) q (bad-asks q d a)) qb-λ⇐
                        (mem q d a) (proj₁ reach)))
