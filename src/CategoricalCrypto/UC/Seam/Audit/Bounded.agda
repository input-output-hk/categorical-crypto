{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Seam.Audit.TrivialGrade`'s four statements discharged: at the trivial
-- grade the graded bound at the designated event — and the one at its
-- prefix-tolerant widening — and layer 1's own `Bounded` imply each other.
--
-- The extraction context and the three theorems that make it one of the
-- contexts an event can permit are `UC.Seam.Audit.Context`; what is left here
-- is the membership witness at each class and the probability arithmetic of the
-- supply.
--
-- The `bad`-budget hypothesis is owed in the extracting direction only — a
-- permitted context comes with the adversary its own budget affords, so the
-- supply spends no budget law.

open import Data.Bool.Base using (Bool; true)
open import Data.Nat.Base using (ℕ; _*_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-identityʳ; ≤-refl; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ProbabilisticLogic.Dp using (Dₚ; ≼ₚ-refl)
open import ProbabilisticLogic.Dp.Advantage
  using (_≼ₚ[_]_; Pr≤; Pr≤-mono; ≼ₚ⇒≼ₚ[0]; ≼ₚ[]-resp)
open import ProbabilisticLogic.Dp.Mass using (const-bind-≼)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Machine.Agree using (prAgree)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Seam.Audit using (module TrivialGrade)
open import CategoricalCrypto.UC.Seam.Audit.Context
  using (audit-run; auditClose; auditTest; extract)
open import CategoricalCrypto.UC.Seam.Grounded using (𝟘ᴳ; ιᴳ)

module CategoricalCrypto.UC.Seam.Audit.Bounded where

private module TG = TrivialGrade 𝟘ᴳ ιᴳ

-- The extraction context reads the event `P` designates, at the adversary the
-- context's own budget affords: `UC.Seam.Audit.Context.audit-run` is that, and
-- the budget is `ctxBudget q 1 = q`.
ctx-watched : {B : Iface} (P : Protocol unitᴵ B)
              (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
              (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d
            → TG.watched P bad 𝟘ᴳ (auditTest B (bad d)) auditClose (q * 1)
ctx-watched P bad q d a = d
  , subst (λ k → asks≤ k d) (sym (ℕP.*-identityʳ q)) a
  , audit-run _ (bad d) (morphism P)

auditIsBounded : TG.AuditIsBounded
auditIsBounded P bad ε bad-asks =
  extract P bad ε {𝔈 = TG.watched P bad} bad-asks (ctx-watched P bad)

-- …and at the widened class, which asks strictly less of the context: the
-- extraction witness is the same one past `watched⇒watchedᵖ`.
auditIsBoundedᵖ : TG.AuditIsBoundedᵖ
auditIsBoundedᵖ P bad ε bad-asks bnd = auditIsBounded P bad ε bad-asks
  λ Y Et m qEt qm ev → bnd Y Et m qEt qm (TG.watched⇒watchedᵖ P bad Y Et m _ ev)

------------------------------------------------------------------------
-- …and the supply

-- The arithmetic both supply directions share: a budget of the context's
-- observation is reached by the monitor's run, `Pr≤-mono` paying the difference
-- between that budget and the one past which `prAgree` reads layer 1's
-- probability off the machine run.  Only a ZERO-SLACK domination is asked of
-- the identification, which is what lets a prefix-tolerant witness supply it
-- (`Dp.Mass.const-bind-≼`: a prefix is never seen to add mass).
supply : {B : Iface} (P : Protocol unitᴵ B)
         (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
         (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → Bounded P bad ε
       → (x : Dₚ Bool) → x ≼ₚ[ 0ℚ ] runᴹ (morphism P) (bad d)
       → (n : ℕ) → Pr≤ n x ℚ.≤ ε q
supply P bad ε q d a bnd x dom n =
  ≤-trans (≤-trans (proj₂ reach) (≤-reflexive (+-identityʳ _)))
    (≤-trans (Pr≤-mono true run (ℕP.m≤n+m (proj₁ reach) (proj₁ pa)))
             (≤-trans (≤-reflexive (reads (proj₁ reach))) (bnd q d a)))
  where
  run : Dₚ Bool
  run = runᴹ (morphism P) (bad d)

  pa = prAgree true P (bad d)
  reads = proj₂ pa

  reach = dom true n

-- An ideal bound on the monitor's verdict IS the graded premise at the
-- designated event: the same identification read the other way.
boundedIsAudit : TG.BoundedIsAudit
boundedIsAudit P bad ε bnd Y Et m qEt qm (d , a , near) =
  supply P bad ε _ d a bnd _ (≼ₚ⇒≼ₚ[0] (proj₁ near))

-- …and at the widened class, which is the direction that GAINS: the same ideal
-- bound covers the prefix-tolerant contexts, a prefix being unable to add mass.
-- This is what a simulator-fronted extraction context needs supplied of it.
boundedIsAuditᵖ : TG.BoundedIsAuditᵖ
boundedIsAuditᵖ P bad ε bnd Y Et m qEt qm (d , p , a , tot , near) =
  supply P bad ε _ d a bnd _
    (≼ₚ[]-resp (proj₁ near) (≼ₚ-refl _) (const-bind-≼ p _ 0ℚ ≤-refl))
