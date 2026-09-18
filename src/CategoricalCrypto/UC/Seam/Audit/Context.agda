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
-- `extract-obs` spends those three and nothing else — no event class in it
-- (review §4.1) — and `extract-bounded` is it in the shape layer 1 states its
-- bound, which is what `UC.Seam.Audit.Prefix`'s route consumes.
--
-- `extractᵍ` is the same extraction at a NONTRIVIAL grade, where the class does
-- stay a parameter: there the bound is `Dₚ`-valued, because the process below
-- an adversary is a raw machine rather than a protocol image.

import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗)
import Categories.Morphism.Reasoning as MR

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; true)
open import Data.Nat.Base using (ℕ; _*_; _+_; _⊔_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-trans)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp using (Dₚ; _≈ₚ_; ≈ₚ-sym; ≈ₚ-trans)
open import ProbabilisticLogic.Dp.Advantage using (Pr≤; indᵇ-nn)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Machine.Agree using (prAgree)
open import CategoricalCrypto.Protocol.Observe using (Bounded; Pr)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Budget using (Budget; ctxBudget)
open import CategoricalCrypto.UC.Graded using (plug-graded)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ)
open import CategoricalCrypto.UC.Machine.Dictionary using (𝟭ᴵ)
open import CategoricalCrypto.UC.Machine.Plug using (plugᴹ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; procᵘ; qbᵒ; qbᵘ)
open import CategoricalCrypto.UC.Model.Graded using (procᵘ-∘)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ; obs-resp)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; gradedᵒ; ifaceᵒ; procᵒ; procᵒ-∘)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using () renaming (QB to QBᴹ)
open import CategoricalCrypto.UC.Seam using (ctxRunˢ; strategyEnv)
open import CategoricalCrypto.UC.Seam.Adequacy using (adequacy)
open import CategoricalCrypto.UC.Seam.Audit using (AuditBound; AuditEvent)
open import CategoricalCrypto.UC.Seam.Budget using (qb-strategyEnv)
open import CategoricalCrypto.UC.Seam.Grounded using (closedᵒ; 𝟘ᴳ; plug-λ; plug-run)
open import CategoricalCrypto.UC.Seam.Slide using (slide⊗)

module CategoricalCrypto.UC.Seam.Audit.Context where

open C using (obs; tv₁)

open MonR monoidal
open Budget budgetᵒ using (QB; qb-∘; qb-mono; qb-sub; qb-T₁; qb-λ⇒; qb-λ⇐)
open MR ∣machines∣ using (cancelInner)

private module 𝒫 = Category 𝒫ᴵ

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
            → obs (tv₁ 𝟘ᴳ (closedᵒ w) auditTest) auditClose ≈ₚ runᴹ w e
  audit-run w =
    ≈ₚ-trans _ _ _ (obs-resp reduce)
      (≈ₚ-trans _ _ _ (≈ₚ-sym _ _ (plug-run B e w)) (adequacy B w e))
    where
    reduce : ((auditTest ∘ id ⊗₁ closedᵒ w) ∘ auditClose) ≈ procᵒ env ∘ procᵒ w
    reduce = ((refl⟩∘⟨ ⟺ (T₁-⊗ 𝔾ᵒ 𝟘ᴳ (closedᵒ w))) ⟩∘⟨refl)
           ○ plug-λ test (closedᵒ w) ○ cancelInner unitorˡ.isoʳ

------------------------------------------------------------------------
-- …and at a NONTRIVIAL grade

-- The same context with the grade FILLED by an adversary machine.  Its shape
-- is `UC.Audit.absorb`'s — a test precomposed with `id ⊗₁ (_ ⊗₁ id)` — at an
-- adversary instead of at a simulator, so the closed system is three-party and
-- the grade the strategy sees is again the trivial one.
module _ (B : Iface) (e : Strat (Neg B) (Pos B)) {X : Iface} (a : Proc X 𝟭ᴵ) where

  auditTestᵍ : T₀ 𝟘ᴳ (T₀ (ifaceᵒ X) (ifaceᵒ B)) ⇒ Ωᵒ
  auditTestᵍ = auditTest B e ∘ id ⊗₁ (procᵘ a ⊗₁ id)

  -- The adversary's own allowance, charged exactly as `absorbed-budget` charges
  -- a simulator's: `qb-sub` and `qb-T₁` guard at `⊔ 1`, `qb-∘` multiplies.
  audit-qbᵍ : (q c : ℕ) → asks≤ q e → QBᴹ c a → QB (q * ((c ⊔ 1) ⊔ 1)) auditTestᵍ
  audit-qbᵍ q c h cert = qb-∘ (audit-qb B e q h) (qb-T₁ (qb-sub (qbᵘ cert)))

  module _ {A : Iface} (f : Proc A (X ⊗ᴵ B)) (w : Proc unitᴵ A) where

    -- The system with its adversary plugged and its resource below.
    closedᵍ : Proc unitᴵ B
    closedᵍ = (plugᴹ a 𝒫.∘ f) 𝒫.∘ w

    -- `unprocᵒ-∘` twice — once for the adversary at the grade
    -- (`UC.Graded.plug-graded`), once for the resource below — with the two
    -- unitors cancelling exactly as at the trivial grade.
    plug-runᵍ : obs (tv₁ 𝟘ᴳ (gradedᵒ f) auditTestᵍ) (closedᵒ w) ≈ₚ ctxRunˢ B e closedᵍ
    plug-runᵍ =
      ≈ₚ-trans _ _ _ (obs-resp reduceᵍ) (≈ₚ-sym _ _ (plug-run B e closedᵍ))
      where
      reduceᵍ : ((auditTestᵍ ∘ id ⊗₁ gradedᵒ f) ∘ closedᵒ w)
              ≈ procᵒ (strategyEnv B e) ∘ procᵒ closedᵍ
      reduceᵍ = ((assoc ○ (refl⟩∘⟨ merge)) ⟩∘⟨refl)
              ○ sym-assoc
              ○ (plug-λ (procᵒ (strategyEnv B e) ∘ unitorˡ.from) _ ⟩∘⟨refl)
              ○ ((assoc ○ (refl⟩∘⟨ plug-graded a f)) ⟩∘⟨refl)
              ○ assoc ○ (refl⟩∘⟨ ⟺ (procᵒ-∘ (plugᴹ a 𝒫.∘ f) w))
        where
        merge : (id ⊗₁ (procᵘ a ⊗₁ id)) ∘ (id ⊗₁ gradedᵒ f)
              ≈ T₁ 𝟘ᴳ (sub (procᵘ a) ∘ gradedᵒ f)
        merge = ⟺ (slide⊗ 𝟘ᴳ (procᵘ a ⊗₁ id) (gradedᵒ f))
              ○ ⟺ (T₁-⊗ 𝔾ᵒ 𝟘ᴳ (sub (procᵘ a) ∘ gradedᵒ f))

    -- …and the observation IS layer 1's run of the strategy against it.
    audit-runᵍ : obs (tv₁ 𝟘ᴳ (gradedᵒ f) auditTestᵍ) (closedᵒ w) ≈ₚ runᴹ closedᵍ e
    audit-runᵍ = ≈ₚ-trans _ _ _ plug-runᵍ (adequacy B closedᵍ e)

    -- A graded bound at any class this context inhabits is a `Pr` bound on that
    -- run, stopping in `Dₚ`: the process is a RAW machine, so layer 1's
    -- `Bounded` — which is about a protocol image — is not what the bound can
    -- be about (`docs/hash-forward.md` item 5).
    extractᵍ : {v : Level} {ε : ℕ → ℚ}
               {𝔈 : AuditEvent v (ifaceᵒ A) (ifaceᵒ X) (ifaceᵒ B)} {q c c′ : ℕ}
             → asks≤ q e → QBᴹ c a → QBᴹ c′ w
             → 𝔈 𝟘ᴳ auditTestᵍ (closedᵒ w) (ctxBudget (q * ((c ⊔ 1) ⊔ 1)) c′)
             → AuditBound (gradedᵒ f) 𝔈 ε
             → (n : ℕ) → Pr≤ n (runᴹ closedᵍ e) ℚ.≤ ε (ctxBudget (q * ((c ⊔ 1) ⊔ 1)) c′)
    extractᵍ {q = q} {c} {c′} ae ca cw mem bnd n =
      ≤-trans (proj₂ reach)
              (bnd 𝟘ᴳ auditTestᵍ (closedᵒ w) (audit-qbᵍ q c ae ca) qbʷ mem (proj₁ reach))
      where
      reach = proj₂ audit-runᵍ (indᵇ true) (indᵇ-nn true) n

      qbʷ : QB c′ (closedᵒ w)
      qbʷ = qb-mono (ℕP.≤-reflexive (ℕP.*-identityˡ c′)) (qb-∘ qb-λ⇐ (qbᵒ cw))

-- Absorbing a simulator into this context is composing it with the adversary:
-- the tensor's left action is functorial, so the two merge.  This is what
-- keeps the IDEAL side of an absorbed event class (`UC.Audit.absorb`) one of
-- these contexts too.
absorb-plugᵍ : (B : Iface) (e : Strat (Neg B) (Pos B)) {X Y : Iface}
               (a : Proc X 𝟭ᴵ) (s : Proc Y X)
             → auditTestᵍ B e a ∘ id ⊗₁ (procᵒ s ⊗₁ id) ≈ auditTestᵍ B e (a 𝒫.∘ s)
absorb-plugᵍ B e a s =
  assoc ○ (refl⟩∘⟨ (⟺ split₂ʳ
                   ○ refl⟩⊗⟨ (⟺ split₁ʳ ○ (⟺ (procᵘ-∘ a s) ⟩⊗⟨refl))))

------------------------------------------------------------------------
-- Extraction

-- What the extraction context observes: the embedded strategy behind the two
-- deflating unitors, closed on `P`'s machine image.
ctxObs : {B : Iface} → Protocol unitᴵ B → Strat (Neg B) (Pos B) → Dₚ Bool
ctxObs {B} P e = obs (tv₁ 𝟘ᴳ (closedᵒ (morphism P)) (auditTest B e)) auditClose

-- The numerical extraction, with no event class in it (review §4.1): a bound on
-- what THIS context observes is a bound on layer 1's own probability.
-- `audit-run` identifies the two runs and `prAgree` reads the probability off
-- the machine one past a budget, and neither step asks WHY the bound holds.
extract-obs : {B : Iface} (P : Protocol unitᴵ B) (e : Strat (Neg B) (Pos B)) (c : ℚ)
            → ((n : ℕ) → Pr≤ n (ctxObs P e) ℚ.≤ c) → Pr P e ℚ.≤ c
extract-obs {B} P e c bnd = subst (λ z → z ℚ.≤ c) (proj₂ pa 0) chain
  where
  pa = prAgree true P e

  reach = proj₂ (audit-run B e (morphism P)) (indᵇ true) (indᵇ-nn true) (proj₁ pa + 0)

  chain : Pr≤ (proj₁ pa + 0) (runᴹ (morphism P) e) ℚ.≤ c
  chain = ≤-trans (proj₂ reach) (bnd (proj₁ reach))

-- …in the shape layer 1 states its bound, which is what the consumer wants.
extract-bounded : {B : Iface} (P : Protocol unitᴵ B)
                  (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
                → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d
                   → (n : ℕ) → Pr≤ n (ctxObs P (bad d)) ℚ.≤ ε q)
                → Bounded P bad ε
extract-bounded P bad ε bnd q d a = extract-obs P (bad d) (ε q) (bnd q d a)
