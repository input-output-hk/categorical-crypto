{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Seam.Audit.TrivialGrade`'s two statements discharged: at the trivial
-- grade the graded bound at the designated event and layer 1's own `Bounded`
-- imply each other.
--
-- The context is the one `UC.Seam.Grounded` already builds — an embedded
-- strategy behind the two unitors that kill the grade and the ancilla — read
-- here as one of the contexts the event permits.  Three things make it one,
-- and all three are theorems elsewhere:
--
--   budget  `UC.Seam.Budget.qb-strategyEnv` at `bad d`'s own ask-depth, the two
--           unitors at `Budget`'s own certificates, hence `ctxBudget q 1 = q`
--   run     `UC.Seam.Grounded.plug-run` and `UC.Seam.Adequacy.adequacy` identify
--           the context's observation with layer 1's run
--   mass    `Protocol.Machine.Agree.prAgree` reads `Pr` off that run at a budget
--           the `_≼ₚ_` half of the identification reaches
--
-- The `bad`-budget hypothesis is what lets the second and third meet: `Bounded`
-- charges `ε` at `d`'s budget while the context is built from `bad d`.  It is
-- owed in the extracting direction only — a permitted context comes with the
-- adversary its own budget affords, so the supply spends no budget law.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗)
import Categories.Morphism.Reasoning as MR

open import Data.Bool.Base using (Bool; true)
open import Data.Nat.Base using (_*_; _+_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp using (Dₚ; _≈ₚ_; ≈ₚ-sym; ≈ₚ-trans)
open import ProbabilisticLogic.Dp.Advantage using (Pr≤; Pr≤-mono; indᵇ-nn)

open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Machine.Agree using (prAgree)
open import CategoricalCrypto.Strategy using (asks≤)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; qbᵒ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ; obs-resp)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam using (strategyEnv)
open import CategoricalCrypto.UC.Seam.Adequacy using (adequacy)
open import CategoricalCrypto.UC.Seam.Audit using (module TrivialGrade)
open import CategoricalCrypto.UC.Seam.Budget using (qb-strategyEnv)
open import CategoricalCrypto.UC.Seam.Grounded using (𝟘ᴳ; ιᴳ; plug-λ; plug-run)

module CategoricalCrypto.UC.Seam.Audit.Bounded where

open HomReasoning
open Budget budgetᵒ using (QB; qb-∘; qb-mono; qb-λ⇒; qb-λ⇐)
open MR ∣machines∣ using (cancelInner)

private module TG = TrivialGrade 𝟘ᴳ ιᴳ

auditIsBounded : TG.AuditIsBounded
auditIsBounded {B} P bad ε bad-asks bnd q d a =
  subst (λ z → z ℚ.≤ ε q) (reads 0) chain
  where
  w : 𝟘ᵒ ⇒ ifaceᵒ B
  w = procᵒ (morphism P)

  env : Proc B Ωᴵ
  env = strategyEnv B (bad d)

  -- The context: the embedded strategy with the grade and the ancilla deflated.
  test : T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ
  test = procᵒ env ∘ unitorˡ.from

  Et : T₀ 𝟘ᴳ (T₀ 𝟘ᴳ (ifaceᵒ B)) ⇒ Ωᵒ
  Et = test ∘ unitorˡ.from

  close : 𝟘ᵒ ⇒ T₀ 𝟘ᴳ 𝟘ᵒ
  close = unitorˡ.to

  -- Both wires cancel, and what is left is the plugged strategy.
  reduce : ((Et ∘ id ⊗₁ (ιᴳ B ∘ w)) ∘ close) ≈ procᵒ env ∘ w
  reduce = ((refl⟩∘⟨ ⟺ (T₁-⊗ 𝔾ᵒ 𝟘ᴳ (ιᴳ B ∘ w))) ⟩∘⟨refl)
         ○ plug-λ test (ιᴳ B ∘ w) ○ cancelInner unitorˡ.isoʳ

  obsv : Dₚ Bool
  obsv = Obs ((Et ∘ id ⊗₁ (ιᴳ B ∘ w)) ∘ close)

  -- …whose observation is layer 1's run of `bad d`.
  run : Dₚ Bool
  run = runᴹ (morphism P) (bad d)

  near : obsv ≈ₚ run
  near = ≈ₚ-trans _ _ _ (obs-resp reduce)
           (≈ₚ-trans _ _ _ (≈ₚ-sym _ _ (plug-run B (bad d) (morphism P)))
                           (adequacy B (morphism P) (bad d)))

  qEt : QB q Et
  qEt = qb-mono (ℕP.≤-reflexive (trans (ℕP.*-identityʳ (q * 1)) (ℕP.*-identityʳ q)))
          (qb-∘ (qb-∘ (qbᵒ (qb-strategyEnv B q (bad d) (bad-asks q d a))) qb-λ⇒) qb-λ⇒)

  pa = prAgree true P (bad d)
  reads = proj₂ pa

  reach = proj₂ near (indᵇ true) (indᵇ-nn true) (proj₁ pa + 0)

  -- …so the context reads the event `P` designates, at `d` itself.
  ev : TG.watched P bad 𝟘ᴳ Et close (q * 1)
  ev = d , subst (λ k → asks≤ k d) (sym (ℕP.*-identityʳ q)) a , near

  chain : Pr≤ (proj₁ pa + 0) run ℚ.≤ ε q
  chain = ≤-trans (proj₂ reach)
            (subst (λ k → Pr≤ (proj₁ reach) obsv ℚ.≤ ε k) (ℕP.*-identityʳ q)
                   (bnd 𝟘ᴳ Et close qEt qb-λ⇐ ev (proj₁ reach)))

------------------------------------------------------------------------
-- …and the supply

-- The same identification read the other way: an ideal bound on the monitor's
-- verdict IS the graded premise at the designated event.  Only the `≼ₚ` half
-- of the context's identification is spent, and `Pr≤-mono` pays the difference
-- between the budget it lands at and the one past which `prAgree` reads layer
-- 1's probability off the machine run.
boundedIsAudit : TG.BoundedIsAudit
boundedIsAudit P bad ε bnd Y Et m qEt qm (d , a , near) n =
  ≤-trans (proj₂ reach)
    (≤-trans (Pr≤-mono true run (ℕP.m≤n+m (proj₁ reach) (proj₁ pa)))
             (≤-trans (≤-reflexive (reads (proj₁ reach))) (bnd _ d a)))
  where
  run : Dₚ Bool
  run = runᴹ (morphism P) (bad d)

  pa = prAgree true P (bad d)
  reads = proj₂ pa

  reach = proj₁ near (indᵇ true) (indᵇ-nn true) n
