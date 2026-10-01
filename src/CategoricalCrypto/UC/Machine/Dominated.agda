{-# OPTIONS --safe --without-K --guardedness #-}

-- `dominated`, the bridge's (`UC.Machine.Bridge`) context domination, via the
-- two-machine skeleton.
--
-- `UC.Machine.Slide` turns the bridge's ancilla context into a plain closed
-- context `Kctx` carrying `scale c (positive c′)`, so what is left of the obligation
-- is the same statement at a CLOSED context and one process — the shape
-- `UC.Seam.Adequacy.adequacy` is already written at.  That is `skeleton`, and
-- `dominated` below is all the ancilla, the closure and the grade cost.
--
-- `skeleton` assembles the ε-arithmetic of the branchwise decomposition whose
-- moving parts are `UC.Seam.Plug`, `UC.Seam.Extract` and `UC.Seam.Transfer`;
-- the extraction is chosen once the observation's budget is known.
--
-- The hypothesis forces `0 ℚ.≤ ε` on its own (`0≤hyp`), so the statement need
-- not ask for it.

open import Categories.Category

open import Data.Bool.Base
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties as ℚP
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level
open import Relation.Binary.PropositionalEquality

import Data.Nat.Positive as ℕ⁺
import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Dominate
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Machine.Slide
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.Seam.Plug

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Seam.Extract as Ext
import CategoricalCrypto.UC.Seam.Transfer as Tr

module CategoricalCrypto.UC.Machine.Dominated where

private
  module 𝒫 = Category 𝒫ᴵ
  module MC = Core (𝒱ₚ 0ℓ)
  module Sm = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- The decomposition

-- Everything the decomposition does before a slack is chosen, shared with
-- `UC.Machine.StateEvent.Lift.flagSkeleton`.
module Refine (B : Iface) (K N : Proc B Ωᴵ) (q : ℕ) (cert : Certified q N)
              (e : N Sm.≈ᴹ K) where

  open Ext B N q cert public

  dstrat : Bool → ℕ → AtMost Φ 0 → Strat (Neg B) (Pos B)
  dstrat b f z = extract b f (Φ (proj₁ z) ℕ.+ q) (onRᵍ (proj₁ z) tt)

  dstrat-asks : (b : Bool) (f : ℕ) (z : AtMost Φ 0) → asks≤ q (dstrat b f z)
  dstrat-asks b f (s , le) = subst (λ k → asks≤ (k ℕ.+ q) (dstrat b f (s , le)))
                                   (ℕP.n≤0⇒n≡0 le)
                                   (extract-asks b f (Φ s ℕ.+ q) (onRᵍ s tt))

  module _ (u : Proc unitᴵ B) (b : Bool) where
    private module T = Tr B N q cert u b

    -- The observation, with the point refined as well: the certificate's
    -- initial states are the machine's, and it is over those that the
    -- strategy is chosen.
    obsᵍ : AtMost Φ 0 → Dₚ Bool
    obsᵍ z = MC.point (MC.state u) ttᵛ >>=ₚ T.obsᴿ (proj₁ z)

    private
      refine : ⟦ K 𝒫.∘ u ⟧ᴼ ≈ₚ (pointᵍ >>=ₚ obsᵍ)
      refine = ≈sym (obs-resp B u N K e)
         ⟨≈⟩ T.observe-≈
         ⟨≈⟩ bindˣ (≈sym coh₀)
         ⟨≈⟩ bind-map pointᵍ proj₁ _

    to-obs : Cofinal (indᵇ b) (indᵇ b) ⟦ K 𝒫.∘ u ⟧ᴼ (pointᵍ >>=ₚ obsᵍ)
    to-obs = proj₁ refine (indᵇ b) (indᵇ-nn b)

    from-obs : Cofinal (indᵇ b) (indᵇ b) (pointᵍ >>=ₚ obsᵍ) ⟦ K 𝒫.∘ u ⟧ᴼ
    from-obs = proj₂ refine (indᵇ b) (indᵇ-nn b)

    plays : (f : ℕ) → Dₚ Bool
    plays f = pointᵍ >>=ₚ λ z → runᴹ u (dstrat b f z)

    fwd : (f : ℕ) → Dom≤ (indᵇ b) f (pointᵍ >>=ₚ obsᵍ) (plays f)
    fwd f = dom≤-bind (indᵇ b) (indᵇ-nn b) f pointᵍ obsᵍ _
                      λ z → T.runFwd f (proj₁ z)

    bwd : (f : ℕ) → Cofinal (indᵇ b) (indᵇ b) (plays f) (pointᵍ >>=ₚ obsᵍ)
    bwd f = cofinal-bind (indᵇ b) (indᵇ-nn b) pointᵍ _ obsᵍ
                         λ z → T.runBwd f (proj₁ z)

private
  module Decompose (B : Iface) (K N : Proc B Ωᴵ) (q : ℕ) (cert : Certified q N)
                   (e : N Sm.≈ᴹ K) (ε : ℚ) (0≤ε : 0ℚ ℚ.≤ ε) where

    open Refine B K N q cert e

    half : (u v : Proc unitᴵ B)
         → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
         → (b : Bool) → Dom (indᵇ b) ε ⟦ K 𝒫.∘ u ⟧ᴼ ⟦ K 𝒫.∘ v ⟧ᴼ
    half u v h b n = n₅ , ≤-trans (proj₂ (to-obs u b n)) (≤-trans le₂ (≤-trans le₃
                              (+-monoˡ-≤ ε (≤-trans (proj₂ (bwd v b n₁ n₃)) le₅))))
      where
      n₁ = proj₁ (to-obs u b n)
      -- The fuel is the budget the observation has just been read at, so the
      -- truncation is never reached.
      n₂ = proj₁ (fwd u b n₁ n₁ ℕP.≤-refl)
      le₂ = proj₂ (fwd u b n₁ n₁ ℕP.≤-refl)

      spend : Dom (indᵇ b) ε (plays u b n₁) (plays v b n₁)
      spend = dom-bind (indᵇ b) (indᵇ-nn b) 0≤ε pointᵍ _ _
                       λ z → proj₁ (h (dstrat b n₁ z) (dstrat-asks b n₁ z)) b

      n₃ = proj₁ (spend n₂)
      le₃ = proj₂ (spend n₂)

      n₄ = proj₁ (bwd v b n₁ n₃)
      n₅ = proj₁ (from-obs v b n₄)
      le₅ = proj₂ (from-obs v b n₄)

-- A strategy that never asks is affordable at any budget, and neither run
-- ever answers `false` against it; the hypothesis at that one strategy is
-- therefore `0 ≤ 0 + ε`.
private
  0≤hyp : {B : Iface} {q : ℕ} (u v : Proc unitᴵ B) (ε : ℚ)
        → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
        → 0ℚ ℚ.≤ ε
  0≤hyp u v ε h = ≤-trans (proj₂ bound)
                          (≤-trans (+-monoˡ-≤ ε zero-mass) (≤-reflexive (+-identityˡ ε)))
    where
    bound = proj₁ (h (out true) tt) false 0

    zero-mass : cum (proj₁ bound) (runᴹ v (out true)) (indᵇ false) ℚ.≤ 0ℚ
    zero-mass = bind-const-zero (indᵇ false) (indᵇ-nn false) true (indᵇ-not false)
                                (MC.point (MC.state v) ttᵛ) (proj₁ bound)

skeleton : (B : Iface) (K : Proc B Ωᴵ) {q : ℕ} → QB q K
         → (u v : Proc unitᴵ B) (ε : ℚ)
         → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
         → ⟦ K 𝒫.∘ u ⟧ᴼ ≈ₚ[ ε ] ⟦ K 𝒫.∘ v ⟧ᴼ
skeleton B K (N , cert , e) u v ε h =
    (λ b → D.half u v h b)
  , (λ b → D.half v u (λ d a → ≈ₚ[]-sym (h d a)) b)
  where
  module D = Decompose B K N _ cert e ε (0≤hyp u v ε h)

------------------------------------------------------------------------
-- …and the obligation it discharges

dominated : (B Y : Iface)
            (E : Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
            {c c′ : ℕ} → QB c E → QB c′ m
          → (u v : Proc unitᴵ B) (ε δ : ℚ) → 0ℚ ℚ.< δ
          → ((d : Strat (Neg B) (Pos B)) → asks≤ (ℕ⁺.scale c (ℕ⁺.positive c′)) d
             → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
          → ctxRun Y E m (conjᴵ u) ≈ₚ[ ε ℚ.+ δ ] ctxRun Y E m (conjᴵ v)
dominated B Y E m qE qm u v ε δ 0<δ h =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (ctxRun-slide E m u)) (≈ₚ-sym _ _ (ctxRun-slide E m v))
    (≈ₚ[]-mono ε≤ε+δ (skeleton B (Kctx E m) (qb-Kctx E m qE qm) u v ε h))
  where
  ε≤ε+δ : ε ℚ.≤ ε ℚ.+ δ
  ε≤ε+δ = ℚP.≤-trans (ℚP.≤-reflexive (sym (ℚP.+-identityʳ ε)))
                     (ℚP.+-monoʳ-≤ ε (ℚP.<⇒≤ 0<δ))
