{-# OPTIONS --safe --without-K --guardedness #-}

-- The extracted strategy's verdict is dominated by the WATCHED verdict of the
-- same strategy — the event-sensitive half of `UC.Seam.Transfer`.
--
-- `UC.Seam.Transfer.runFwd` bounds a context's observation by the run of the
-- strategy extracted from its certificate, at that strategy's OWN verdict.  An
-- event bound cannot use that: the hypothesis available is a bound on the
-- watched event, and a verdict carries no connection to the event that produced
-- it (`docs/event-bounds-in-setup.md`, "Acceptance is semantic agreement").
-- `Cov` is that connection — the accumulator invariant — and the forward
-- induction below re-runs `Transfer`'s against `w acc (extract …)` instead of
-- `extract …`, so the target IS a watched run and the hypothesis applies.
--
-- `Cov acc f r X` reads "every verdict this emission tree can still reach
-- within `f` steps is already covered by `acc`", and it is indexed exactly as
-- `UC.Seam.Extract.extract` recurses, one `br` per `Supp` level and the
-- accumulator advanced by `report` at each query leaf.  The four cases the
-- induction decides are the four the extraction has: a coin node passes `acc`
-- through unchanged, a query leaf advances it by `report n p`, a verdict leaf
-- spends the invariant, and the truncation is never reached — the fuel is the
-- budget the observation has already been read at (`Dom≤`).
--
-- The watch is a PARAMETER with its three defining equations rather than a
-- fixed transformer: `UC.Quantitative.Hits.IsWatch` is that triple, and
-- identifying two transformers satisfying it would want funext.

open import Data.Bool.Base using (Bool; _∨_; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s; _⊔_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Distribution.RationalDist using (Dist-ℚ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (indᵇ-not)
open import ProbabilisticLogic.Dp.Dominate
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Stable using (coin-bind-cum)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ; resumeᴹ)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ)
open import CategoricalCrypto.UC.QueryBound using (Certified)
open import CategoricalCrypto.UC.Seam.Plug

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.UC.Seam.Extract as Ext
import CategoricalCrypto.UC.Seam.Transfer as Tr

module CategoricalCrypto.UC.Seam.EventTransfer
  (B : Iface) (K : Proc B Ωᴵ) (q : ℕ) (cert : Certified q K)
  (report : Neg B → Pos B → Bool) where

private module MC = Core (𝒱ₚ 0ℓ)

open Ext B K q cert

------------------------------------------------------------------------
-- The accumulator invariant

-- The `Loop` case split of `Cov`, at the two positions the transfer enters it:
-- a pending query still to be answered, and an answer already accumulated.
mutual
  Cov : Bool → ℕ → (r : ℕ) → Dₚ (Ansᶜ r) → Set
  Cov acc zero    r X = ⊤
  Cov acc (suc f) r X = CovL acc f r (br X true) × CovL acc f r (br X false)

  CovL : Bool → ℕ → (r : ℕ) → Ansᶜ r ⊎ Dₚ (Ansᶜ r) → Set
  CovL acc f r (inj₁ (inj₁ ((s , _) , n))) =
    (p : Pos B) → Cov (acc ∨ report n p) f (Φ s) (onLᵍ s p)
  CovL acc f r (inj₁ (inj₂ (_ , v)))       = v ≡ true → acc ≡ true
  CovL acc f r (inj₂ X′)                   = Cov acc f r X′

-- Once the watch has fired nothing is left to cover, which is also the base
-- case of any discharge: the invariant is a real predicate, not an empty one.
mutual
  cov-true : (f r : ℕ) (X : Dₚ (Ansᶜ r)) → Cov true f r X
  cov-true zero    r X = tt
  cov-true (suc f) r X = covL-true f r (br X true) , covL-true f r (br X false)

  covL-true : (f r : ℕ) (y : Ansᶜ r ⊎ Dₚ (Ansᶜ r)) → CovL true f r y
  covL-true f r (inj₁ (inj₁ ((s , _) , n))) p = cov-true f (Φ s) (onLᵍ s p)
  covL-true f r (inj₁ (inj₂ _))             _ = refl
  covL-true f r (inj₂ X′)                     = cov-true f r X′

------------------------------------------------------------------------
-- The watched forward transfer

-- The watch is `w`, pinned only by the three equations
-- `UC.Quantitative.Hits.IsWatch` asks for.
module Watched (u : Proc unitᴵ B)
               (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
               (w-out : (acc v : Bool) → w acc (out v) ≡ out acc)
               (w-ask : (acc : Bool) (n : Neg B) (k : Pos B → Strat (Neg B) (Pos B))
                      → w acc (ask n k) ≡ ask n λ p → w (acc ∨ report n p) (k p))
               (w-coin : (acc : Bool) (ν : Dist-ℚ Bool) (k : Bool → Strat (Neg B) (Pos B))
                       → w acc (coin ν k) ≡ coin ν λ c → w acc (k c))
               where

  open Plugged B K u
  open Tr B K q cert u true

  -- The one place the invariant is spent: a verdict the test scores is one the
  -- accumulator has already reached.
  cov-ind : {v acc : Bool} → (v ≡ true → acc ≡ true) → Q v ℚ.≤ Q acc
  cov-ind {false} {acc} h = ≤-trans (≤-reflexive (indᵇ-not true)) (nnQ acc)
  cov-ind {true}        h = ≤-reflexive (cong Q (sym (h refl)))

  -- `Transfer.resume` with the answer accumulated into the watch.
  resumeᵂ : Bool → Neg B → ℕ → SK → SU × (⊥ ⊎ Pos B) → Dₚ Bool
  resumeᵂ acc n f s = resumeᴹ u λ su′ p → run su′ (w (acc ∨ report n p) (tgtᴷ f s p))

  -- What the invariant reads at each position of the loop.
  CovX : Bool → ℕ → SK → Loop → Set
  CovX acc f s (inj₁ n) = (p : Pos B) → Cov (acc ∨ report n p) f (Φ s) (onLᵍ s p)
  CovX acc f s (inj₂ p) = Cov acc f (Φ s) (onLᵍ s p)

  mutual
    loopFwdᵂ : (acc : Bool) (f : ℕ) (s : SK) (su : SU) (x : Loop) → CovX acc f s x
             → (j : ℕ) → j ℕ.≤ f
             → Σ[ m ∈ ℕ ] (cum j (Runᴿ ((s , su) , x)) Q
                           ℚ.≤ cum m (run su (w acc (strat f s x))) Q)
    loopFwdᵂ acc f s su (inj₁ n) cx j le =
      let m , bd = uFwdᵂ acc n f s (MC.step u (su , inj₂ n)) cx j le
      in m , ≤-trans bd (≤-reflexive (cong (λ d → cum m (run su d) Q)
                                           (sym (w-ask acc n (tgtᴷ f s)))))
    loopFwdᵂ acc f s su (inj₂ p) cx j le = treeFwdᵂ acc f (Φ s) (onLᵍ s p) cx su j le

    treeFwdᵂ : (acc : Bool) (f r : ℕ) (X : Dₚ (Ansᶜ r)) → Cov acc f r X
             → (su : SU) (j : ℕ) → j ℕ.≤ f
             → Σ[ m ∈ ℕ ] (cum j (Stepᴿ (mapₚ (hᴷ su r) X)) Q
                           ℚ.≤ cum m (run su (w acc (extract true f r X))) Q)
    treeFwdᵂ acc f       r X cov su zero    le      = 0 , ≤-refl
    treeFwdᵂ acc zero    r X cov su (suc j) ()
    treeFwdᵂ acc (suc f) r X cov su (suc j) (s≤s le) =
      suc (suc i)
      , ≤-trans (node-mono (wt X true) (wt X false) (wt-nn X true) (wt-nn X false)
                  (≤-trans (proj₂ w₁) (cum-mono (ℕP.m≤m⊔n i₁ i₂) (g true) Q nnQ))
                  (≤-trans (proj₂ w₂) (cum-mono (ℕP.m≤n⊔m i₁ i₂) (g false) Q nnQ)))
        (≤-trans (≤-reflexive (trans (sym (E-coinᵈ X λ c → cum i (g c) Q))
                                     (sym (coin-bind-cum (coinᵈ X) g i Q))))
                 (≤-reflexive (cong (λ d → cum (suc (suc i)) (run su d) Q)
                                    (sym (w-coin acc (coinᵈ X)
                                           λ c → extractL true f r (br X c))))))
      where
      g : Bool → Dₚ Bool
      g c = run su (w acc (extractL true f r (br X c)))

      w₁ = treeFwdLᵂ acc f r su (br X true) (proj₁ cov) j le
      w₂ = treeFwdLᵂ acc f r su (br X false) (proj₂ cov) j le
      i₁ = proj₁ w₁
      i₂ = proj₁ w₂
      i  = i₁ ⊔ i₂

    treeFwdLᵂ : (acc : Bool) (f r : ℕ) (su : SU) (y : Ansᶜ r ⊎ Dₚ (Ansᶜ r))
              → CovL acc f r y → (j : ℕ) → j ℕ.≤ f
              → Σ[ m ∈ ℕ ] (leafₚ j (tagₚ (tagᵢ bodyᴿ (tagₚ y (returnₚ ∘′ hᴷ su r))) verdict) Q
                            ℚ.≤ cum m (run su (w acc (extractL true f r y))) Q)
    treeFwdLᵂ acc f r su (inj₂ X′) cl j le = treeFwdᵂ acc f r X′ cl su j le
    treeFwdLᵂ acc f r su (inj₁ (inj₁ ((s , _) , n))) cl zero    le = 0 , ≤-refl
    treeFwdLᵂ acc f r su (inj₁ (inj₁ ((s , _) , n))) cl (suc j) le =
      let m , bd = loopFwdᵂ acc f s su (inj₁ n) cl j (ℕP.≤-trans (ℕP.n≤1+n j) le)
      in m , ≤-trans (≤-reflexive (dirac-node _)) bd
    treeFwdLᵂ acc f r su (inj₁ (inj₂ (_ , v))) cl zero    le =
      1 , cum-nn 1 (run su (w acc (out v))) Q nnQ
    treeFwdLᵂ acc f r su (inj₁ (inj₂ (_ , v))) cl (suc j) le =
      1 , ≤-trans (≤-reflexive (dirac-node _))
            (≤-trans (returnₚ-cum-≤ j v Q nnQ)
              (≤-trans (cov-ind cl)
                (≤-trans (≤-reflexive (sym (returnₚ-cum 0 acc Q)))
                         (≤-reflexive (cong (λ d → cum 1 d Q)
                                            (sym (cong (run su) (w-out acc v))))))))

    uFwdᵂ : (acc : Bool) (n : Neg B) (f : ℕ) (s : SK) (W : Dₚ (SU × (⊥ ⊎ Pos B)))
          → ((p : Pos B) → Cov (acc ∨ report n p) f (Φ s) (onLᵍ s p))
          → (j : ℕ) → j ℕ.≤ f
          → Σ[ m ∈ ℕ ] (cum j (Stepᴿ (mapₚ (ρᵁ s) W)) Q
                        ℚ.≤ cum m (W >>=ₚ resumeᵂ acc n f s) Q)
    uFwdᵂ acc n f s W cx zero    le = 0 , ≤-refl
    uFwdᵂ acc n f s W cx (suc j) le =
      suc i
      , node-mono (wt W true) (wt W false) (wt-nn W true) (wt-nn W false)
          (≤-trans (proj₂ w₁)
            (leafₚ-mono (ℕP.m≤m⊔n i₁ i₂) (tagₚ (br W true) (resumeᵂ acc n f s)) Q nnQ))
          (≤-trans (proj₂ w₂)
            (leafₚ-mono (ℕP.m≤n⊔m i₁ i₂) (tagₚ (br W false) (resumeᵂ acc n f s)) Q nnQ))
      where
      le′ = ℕP.≤-trans (ℕP.n≤1+n j) le
      w₁ = uFwdLᵂ acc n f s (br W true) cx j le′
      w₂ = uFwdLᵂ acc n f s (br W false) cx j le′
      i₁ = proj₁ w₁
      i₂ = proj₁ w₂
      i  = i₁ ⊔ i₂

    uFwdLᵂ : (acc : Bool) (n : Neg B) (f : ℕ) (s : SK)
             (y : (SU × (⊥ ⊎ Pos B)) ⊎ Dₚ (SU × (⊥ ⊎ Pos B)))
           → ((p : Pos B) → Cov (acc ∨ report n p) f (Φ s) (onLᵍ s p))
           → (j : ℕ) → j ℕ.≤ f
           → Σ[ m ∈ ℕ ] (leafₚ j (tagₚ (tagᵢ bodyᴿ (tagₚ y (returnₚ ∘′ ρᵁ s))) verdict) Q
                         ℚ.≤ leafₚ m (tagₚ y (resumeᵂ acc n f s)) Q)
    uFwdLᵂ acc n f s (inj₂ W′)             cx j       le = uFwdᵂ acc n f s W′ cx j le
    uFwdLᵂ acc n f s (inj₁ (su′ , inj₁ e)) cx j       le = ⊥-elim e
    uFwdLᵂ acc n f s (inj₁ (su′ , inj₂ p)) cx zero    le = 0 , ≤-refl
    uFwdLᵂ acc n f s (inj₁ (su′ , inj₂ p)) cx (suc j) le =
      let m , bd = loopFwdᵂ (acc ∨ report n p) f s su′ (inj₂ p) (cx p) j
                            (ℕP.≤-trans (ℕP.n≤1+n j) le)
      in m , ≤-trans (≤-reflexive (dirac-node _)) bd

  -- `Transfer.runFwd` at the watched target: the process's own run, against the
  -- watch of the strategy the certificate's activation sequence extracts to.
  runFwdᵂ : (f : ℕ) (sk : SK) → Cov false f (Φ sk ℕ.+ q) (onRᵍ sk tt)
          → Dom≤ Q f (MC.point (MC.state u) ttᵛ >>=ₚ obsᴿ sk)
                     (runᴹ u (w false (extract true f (Φ sk ℕ.+ q) (onRᵍ sk tt))))
  runFwdᵂ f sk cov = dom≤-bind Q nnQ f (MC.point (MC.state u) ttᵛ) (obsᴿ sk) _
                               (treeFwdᵂ false f (Φ sk ℕ.+ q) (onRᵍ sk tt) cov)
