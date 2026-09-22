{-# OPTIONS --safe --without-K --guardedness #-}

-- `ContextDominated`, via the two-machine skeleton.
--
-- `UC.Machine.Slide` turns the bridge's ancilla context into a plain closed
-- context `Kctx` carrying `ctxBudget c c′`, so what is left of the obligation
-- is the same statement at a CLOSED context and one process — the shape
-- `Adequacy` and `Counting` are already written at.  That is `Skeleton`, and
-- `skeleton⇒dominated` below is all the ancilla, the closure and the grade
-- cost.
--
-- The δ is spent there and nowhere else: the skeleton is an ε-statement, and
-- `≈ₚ[]-mono` widens it to `ε + δ` because δ is positive.  That is the sense in
-- which the bridge's arbitrary positive slack "costs a consumer nothing" — no
-- step of the reduction needs it.
--
-- `skeleton` is the branchwise decomposition, and its three moving parts live
-- next door: `UC.Seam.Plug`, `UC.Seam.Extract`, `UC.Seam.Transfer`.  What is
-- assembled here is the ε-arithmetic — the extraction is chosen ONCE the
-- observation's budget is known, so a truncation past it never shows; the
-- hypothesis is spent at that one strategy per initial state; and the
-- branchwise ε's are averaged back into one by convexity (`cum-shift`).
--
-- The hypothesis forces `0 ℚ.≤ ε` on its own (`0≤hyp`), so the statement need
-- not ask for it.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; _∨_; true; false)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties as ℚP
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Distribution.RationalDist using (Dist-ℚ)
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Dominate
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy using (Strat; ask; asks≤; coin; out)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; ⟦_⟧ᴼ)
open import CategoricalCrypto.UC.Machine.Bridge using (ContextDominated)
open import CategoricalCrypto.UC.Machine.Slide using (Kctx; ctxRun-slide; qb-Kctx)
open import CategoricalCrypto.UC.QueryBound using (QB; Certified; AtMost)
open import CategoricalCrypto.UC.Seam.Plug using (obs-resp)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Seam.Extract as Ext
import CategoricalCrypto.UC.Seam.EventTransfer as ET
import CategoricalCrypto.UC.Seam.Transfer as Tr

module CategoricalCrypto.UC.Machine.Dominated where

private
  module 𝒫 = Category 𝒫ᴵ
  module MC = Core (𝒱ₚ 0ℓ)
  module Sm = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

-- The obligation at a closed context: if no strategy of the context's budget
-- separates the two processes by more than ε, neither does the context.
Skeleton : Set₁
Skeleton = (B : Iface) (K : Proc B Ωᴵ) {q : ℕ} → QB q K
         → (u v : Proc unitᴵ B) (ε : ℚ)
         → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
         → ⟦ K 𝒫.∘ u ⟧ᴼ ≈ₚ[ ε ] ⟦ K 𝒫.∘ v ⟧ᴼ

------------------------------------------------------------------------
-- The decomposition

-- The context, the representative its certificate lives on, and the
-- extraction: everything the decomposition does before a slack is chosen.
module Refine (B : Iface) (K N : Proc B Ωᴵ) (q : ℕ) (cert : Certified q N)
              (e : N Sm.≈ᴹ K) where

  open Ext B N q cert public

  -- The context's activation sequence, read off the certificate: one
  -- strategy per initial state and fuel, and the potential bounds its asks.
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

    to-obs : Dom₀ (indᵇ b) ⟦ K 𝒫.∘ u ⟧ᴼ (pointᵍ >>=ₚ obsᵍ)
    to-obs = ≈⇒dom₀ (indᵇ b) (indᵇ-nn b) _ _ refine

    from-obs : Dom₀ (indᵇ b) (pointᵍ >>=ₚ obsᵍ) ⟦ K 𝒫.∘ u ⟧ᴼ
    from-obs = ≈⇒dom₀ (indᵇ b) (indᵇ-nn b) _ _ (≈sym refine)

    plays : (f : ℕ) → Dₚ Bool
    plays f = pointᵍ >>=ₚ λ z → runᴹ u (dstrat b f z)

    fwd : (f : ℕ) → Dom≤ (indᵇ b) f (pointᵍ >>=ₚ obsᵍ) (plays f)
    fwd f = dom≤-bind (indᵇ b) (indᵇ-nn b) f pointᵍ obsᵍ _
                      λ z → T.runFwd f (proj₁ z)

    bwd : (f : ℕ) → Dom₀ (indᵇ b) (plays f) (pointᵍ >>=ₚ obsᵍ)
    bwd f = dom₀-bind (indᵇ b) (indᵇ-nn b) pointᵍ _ obsᵍ
                      λ z → T.runBwd f (proj₁ z)

-- Everything but the two processes is fixed here: the extraction, and the
-- slack.
private
  module Decompose (B : Iface) (K N : Proc B Ωᴵ) (q : ℕ) (cert : Certified q N)
                   (e : N Sm.≈ᴹ K) (ε : ℚ) (0≤ε : 0ℚ ℚ.≤ ε) where

    open Refine B K N q cert e

    -- Half the conclusion; the other half is this one with the pair swapped.
    half : (u v : Proc unitᴵ B)
         → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
         → (b : Bool) → Dom (indᵇ b) ε ⟦ K 𝒫.∘ u ⟧ᴼ ⟦ K 𝒫.∘ v ⟧ᴼ
    half u v h b n = n₅ , ≤-trans le₁ (≤-trans le₂ (≤-trans le₃
                              (+-monoˡ-≤ ε (≤-trans le₄ le₅))))
      where
      n₁ = proj₁ (to-obs u b n)
      le₁ = proj₂ (to-obs u b n)

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
      le₄ = proj₂ (bwd v b n₁ n₃)

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

skeleton : Skeleton
skeleton B K (N , cert , e) u v ε h =
    (λ b → D.half u v h b)
  , (λ b → D.half v u (λ d a → ≈ₚ[]-sym (h d a)) b)
  where
  module D = Decompose B K N _ cert e ε (0≤hyp u v ε h)

------------------------------------------------------------------------
-- …and the obligation it discharges

skeleton⇒dominated : Skeleton → ContextDominated
skeleton⇒dominated sk B Y E m qE qm u v ε δ 0<δ h =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (ctxRun-slide E m u)) (≈ₚ-sym _ _ (ctxRun-slide E m v))
    (≈ₚ[]-mono ε≤ε+δ (sk B (Kctx E m) (qb-Kctx E m qE qm) u v ε h))
  where
  ε≤ε+δ : ε ℚ.≤ ε ℚ.+ δ
  ε≤ε+δ = ℚP.≤-trans (ℚP.≤-reflexive (sym (ℚP.+-identityʳ ε)))
                     (ℚP.+-monoʳ-≤ ε (ℚP.<⇒≤ 0<δ))

dominated : ContextDominated
dominated = skeleton⇒dominated skeleton

------------------------------------------------------------------------
-- The event-sensitive half

-- `UC.Seam.EventTransfer`'s accumulator invariant, read at the context's
-- initial activation, where the watch has accumulated nothing yet.
CovCtx : (B : Iface) {K : Proc B Ωᴵ} (q : ℕ) → (Neg B → Pos B → Bool) → QB q K → Set
CovCtx B q report (N , cert , _) =
  (f : ℕ) (z : AtMost Φ 0) → Cov false f (Φ (proj₁ z) ℕ.+ q) (onRᵍ (proj₁ z) tt)
  where
  open Ext B N q cert
  open ET B N q cert report

-- One-sided and event-sensitive: an ordinary domination loses the connection
-- between a verdict and the event that produced it, and `CovCtx` is that
-- connection.  The hypothesis bounds the WATCHED event of every affordable
-- strategy, `w` being any transformer satisfying the three equations
-- `UC.Quantitative.Hits.IsWatch` asks for.  No slack is spent: the extraction
-- is chosen once the observation's budget is known, as in `skeleton`.
EventSkeleton : Set₁
EventSkeleton =
    (B : Iface) (K : Proc B Ωᴵ) {q : ℕ} (report : Neg B → Pos B → Bool)
    (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
  → ((acc v : Bool) → w acc (out v) ≡ out acc)
  → ((acc : Bool) (n : Neg B) (k : Pos B → Strat (Neg B) (Pos B))
     → w acc (ask n k) ≡ ask n λ p → w (acc ∨ report n p) (k p))
  → ((acc : Bool) (ν : Dist-ℚ Bool) (k : Bool → Strat (Neg B) (Pos B))
     → w acc (coin ν k) ≡ coin ν λ c → w acc (k c))
  → (kb : QB q K) → CovCtx B q report kb
  → (u : Proc unitᴵ B) (r : ℚ)
  → ((d : Strat (Neg B) (Pos B)) → asks≤ q d
     → (n : ℕ) → Pr≤ n (runᴹ u (w false d)) ℚ.≤ r)
  → (n : ℕ) → Pr≤ n ⟦ K 𝒫.∘ u ⟧ᴼ ℚ.≤ r

eventSkeleton : EventSkeleton
eventSkeleton B K {q} report w wo wa wc (N , cert , e) cov u r h n =
  ≤-trans le₁ (≤-trans le₂ (bound n₁ n₂))
  where
  open Refine B K N q cert e
  open ET.Watched B N q cert report u w wo wa wc

  playsᵂ : (f : ℕ) → Dₚ Bool
  playsᵂ f = pointᵍ >>=ₚ λ z → runᴹ u (w false (dstrat true f z))

  fwdᵂ : (f : ℕ) → Dom≤ (indᵇ true) f (pointᵍ >>=ₚ obsᵍ u true) (playsᵂ f)
  fwdᵂ f = dom≤-bind (indᵇ true) (indᵇ-nn true) f pointᵍ (obsᵍ u true) _
                     λ z → runFwdᵂ f (proj₁ z) (cov f z)

  0≤r : 0ℚ ℚ.≤ r
  0≤r = h (out false) tt 0

  -- A bound holding at every initial state and every budget survives the
  -- average, the divergent mass counting for nothing.
  bound : (f i : ℕ) → cum i (playsᵂ f) (indᵇ true) ℚ.≤ r
  bound f i =
    ≤-trans (>>=ₚ-boundA i pointᵍ _ (indᵇ true) (indᵇ-nn true))
    (≤-trans (cum-mono-P i pointᵍ _ (λ _ → 0ℚ ℚ.+ r)
               λ z → ≤-trans (h (dstrat true f z) (dstrat-asks true f z) i)
                             (≤-reflexive (sym (+-identityˡ r))))
    (≤-trans (cum-shift i pointᵍ (λ _ → 0ℚ) r 0≤r)
    (≤-trans (+-monoˡ-≤ r (≤-reflexive (cum-zero i pointᵍ)))
             (≤-reflexive (+-identityˡ r)))))

  n₁ = proj₁ (to-obs u true n)
  le₁ = proj₂ (to-obs u true n)

  n₂ = proj₁ (fwdᵂ n₁ n₁ ℕP.≤-refl)
  le₂ = proj₂ (fwdᵂ n₁ n₁ ℕP.≤-refl)
