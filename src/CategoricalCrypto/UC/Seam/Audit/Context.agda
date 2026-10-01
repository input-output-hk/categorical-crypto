{-# OPTIONS --safe --without-K --guardedness #-}

-- The context an audit bound is extracted at, and what a graded bound at any
-- class permitting it gives back.

open import Categories.Category
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory
import Categories.Morphism.Reasoning as MR

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Positive
import Data.Nat.Properties as ℕP
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Graded
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Audit
open import CategoricalCrypto.UC.Model.Graded
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using () renaming (QB to QBᴹ)
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy
open import CategoricalCrypto.UC.Seam.Budget
open import CategoricalCrypto.UC.Seam.Grounded

module CategoricalCrypto.UC.Seam.Audit.Context where

open MonR monoidal
open GradedSubCat gradingᵒ
open MR ∣machines∣

private module 𝒫 = Category 𝒫ᴵ

auditClose : 𝟘ᵒ ⇒ T₀ 𝟘ᴳ 𝟘ᵒ
auditClose = ιᴳ unitᴵ

module _ (B : Iface) (e : Strat (Neg B) (Pos B)) where

  private
    env : Proc B Ωᴵ
    env = strategyEnv B e

    test : T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ
    test = procᵒ env ∘ unitorˡ.from

  auditTest : T₀ 𝟘ᴳ (T₀ 𝟘ᴳ (ifaceᵒ B)) ⇒ Ωᵒ
  auditTest = test ∘ unitorˡ.from

  audit-qb : (q : ℕ⁺) → asks≤ (value q) e → Pred q auditTest
  audit-qb q a =
    pred-sub (ℕP.≤-reflexive (trans (ℕP.*-identityˡ _) (ℕP.*-identityˡ (value q))))
      (pred-∘ (pred-∘ (qbᵒ {r = q} (qb-strategyEnv B (value q) e a)) pred-λ⇒) pred-λ⇒)

  audit-run : (w : Proc unitᴵ B)
            → observe (auditTest ∘ id ⊗₁ closedᵒ w) auditClose ≈ₚ runᴹ w e
  audit-run w =
    ≈ₚ-trans _ _ _ (obs-resp (plug-λ test (closedᵒ w) ○ cancelInner unitorˡ.isoʳ))
      (≈ₚ-trans _ _ _ (≈ₚ-sym _ _ (plug-run B e w)) (adequacy B w e))

------------------------------------------------------------------------
-- …and at a NONTRIVIAL grade

-- The same context with the grade FILLED by an adversary machine.  Its shape
-- is `UC.Audit.absorb`'s — a test precomposed with `id ⊗₁ (_ ⊗₁ id)` — at an
-- adversary instead of at a simulator, so the closed system is three-party and
-- the grade the strategy sees is again the trivial one.
module _ (B : Iface) (e : Strat (Neg B) (Pos B)) {X : Iface} (a : Proc X 𝟭ᴵ) where

  auditTestᵍ : T₀ 𝟘ᴳ (T₀ (ifaceᵒ X) (ifaceᵒ B)) ⇒ Ωᵒ
  auditTestᵍ = auditTest B e ∘ id ⊗₁ (procᵘ a ⊗₁ id)

  -- The adversary's own rate, charged exactly as
  -- `Examples.HashForward.Audit.absorbed-budget` charges a simulator's: the
  -- tensor with identities at `1⁺`, and composition multiplies.
  audit-qbᵍ : (q c : ℕ⁺) → asks≤ (value q) e → QBᴹ (value c) a → Pred (c · q) auditTestᵍ
  audit-qbᵍ q c h cert =
    pred-sub (ℕP.≤-reflexive
               (cong (_* value q) (trans (ℕP.*-identityˡ _) (ℕP.*-identityʳ (value c)))))
      (pred-∘ (audit-qb B e q h) (pred-⊗ pred-id (pred-⊗ (qbᵘ {r = c} cert) pred-id)))

  module _ {A : Iface} (f : Proc A (X ⊗ᴵ B)) (w : Proc unitᴵ A) where

    closedᵍ : Proc unitᴵ B
    closedᵍ = (plugᴹ a 𝒫.∘ f) 𝒫.∘ w

    plug-runᵍ : observe (auditTestᵍ ∘ id ⊗₁ gradedᵒ f) (closedᵒ w) ≈ₚ ⟦ strategyEnv B e 𝒫.∘ closedᵍ ⟧ᴼ
    plug-runᵍ =
      ≈ₚ-trans _ _ _ (obs-resp reduceᵍ) (≈ₚ-sym _ _ (plug-run B e closedᵍ))
      where
      reduceᵍ : ((auditTestᵍ ∘ id ⊗₁ gradedᵒ f) ∘ closedᵒ w)
              ≈ procᵒ (strategyEnv B e) ∘ procᵒ closedᵍ
      reduceᵍ = ((assoc ○ (refl⟩∘⟨ merge₂ʳ)) ⟩∘⟨refl)
              ○ sym-assoc
              ○ (plug-λ (procᵒ (strategyEnv B e) ∘ unitorˡ.from) _ ⟩∘⟨refl)
              ○ ((assoc ○ (refl⟩∘⟨ plug-graded a f)) ⟩∘⟨refl)
              ○ assoc ○ (refl⟩∘⟨ ⟺ (procᵒ-∘ (plugᴹ a 𝒫.∘ f) w))

    audit-runᵍ : observe (auditTestᵍ ∘ id ⊗₁ gradedᵒ f) (closedᵒ w) ≈ₚ runᴹ closedᵍ e
    audit-runᵍ = ≈ₚ-trans _ _ _ plug-runᵍ (adequacy B closedᵍ e)

    -- A graded bound at any class this context inhabits is a `Pr` bound on that
    -- run, stopping in `Dₚ`: the process is a RAW machine, so layer 1's
    -- `Bounded` — which is about a protocol image — is not what the bound can
    -- be about (`docs/hash-forward.md` item 5).
    -- The certified context the run is read at, of budget `value (c · q · c′)`.
    auditCtxᵍ : {q c c′ : ℕ⁺} → asks≤ (value q) e → QBᴹ (value c) a → QBᴹ (value c′) w
              → Certified (ifaceᵒ A) (ifaceᵒ X) (ifaceᵒ B)
    auditCtxᵍ {q} {c} {c′} ae ca cw = record
      { ctx = record { Y = 𝟘ᴳ ; Et = auditTestᵍ ; m = closedᵒ w } ; c = c · q ; r′ = c′
      ; Êt  = auditTestᵍ , audit-qbᵍ q c ae ca ; Êt≈ = Equiv.refl
      ; m̂   = closedᵒ w , pred-sub (ℕP.≤-reflexive (ℕP.*-identityʳ (value c′)))
                                   (pred-∘ pred-λ⇐ (qbᵒ {r = c′} cw))
      ; m̂≈  = Equiv.refl }

    extractᵍ : {v : Level} {ε : ℕ → ℚ}
               {𝔈 : Permitted v (ifaceᵒ A) (ifaceᵒ X) (ifaceᵒ B)} {q c c′ : ℕ⁺}
             → (ae : asks≤ (value q) e) (ca : QBᴹ (value c) a) (cw : QBᴹ (value c′) w)
             → 𝔈 (auditCtxᵍ {q} {c} {c′} ae ca cw)
             → AuditBound (gradedᵒ f) 𝔈 ε
             → (n : ℕ) → Pr≤ n (runᴹ closedᵍ e) ℚ.≤ ε (value (c · q · c′))
    extractᵍ {q = q} {c} {c′} ae ca cw mem bnd n =
      ≤-trans (proj₂ reach) (bnd (auditCtxᵍ {q} {c} {c′} ae ca cw) mem (proj₁ reach))
      where reach = proj₂ audit-runᵍ (indᵇ true) (indᵇ-nn true) n
