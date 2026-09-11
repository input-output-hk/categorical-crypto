{-# OPTIONS --safe --without-K --guardedness #-}

-- The extracted strategy observes what the context observes, at one verdict.
--
-- Both directions are inductions over the SAME trees, with the budget tied to
-- the depth: a `cum` of a bind decomposes branchwise, so a leaf reached at
-- depth `d` of a budget-`n` observation is scored at budget `n - d`, which is
-- exactly the fuel the extraction has left there.  That tie is why the
-- packaged bounds (`>>=ₚ-boundA`, `stepᵢ-boundA`) are NOT used here: they
-- re-measure every leaf at the outer budget, and the extraction cannot afford
-- that.
--
-- The two directions are not symmetric.  Forwards, the context's own
-- observation is dominated only UP TO the fuel (`Dom≤`): past it the strategy
-- has been truncated away.  Backwards the truncation scores zero under
-- `indᵇ b`, so the strategy is dominated at every budget.  That asymmetry is
-- the whole reason the transfer is one-sided and `b`-indexed.
--
-- The loop runs against the REFINED body `bodyᴿ`, built from the
-- certificate's `onLᵍ` rather than from the step itself: the two agree only
-- up to `_≈ₚ_` (`cohL`), whose budget map is arbitrary, and an arbitrary
-- budget map inside the induction would break the tie above.  The refinement
-- is undone once, at the top, where the fuel is still free to be chosen.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s; _⊔_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (indᵇ-nn; indᵇ-not)
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Dp.Dominate
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Stable using (coin-bind-cum)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ; runᴹFrom; resumeᴹ)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ; ⟦_⟧ᴼ; 𝒫ᴵ)
open import CategoricalCrypto.UC.QueryBound using (Certified; forget)
open import CategoricalCrypto.UC.Seam.Plug

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.UC.Seam.Extract as Ext

module CategoricalCrypto.UC.Seam.Transfer
  (B : Iface) (K : Proc B Ωᴵ) (q : ℕ) (cert : Certified q K)
  (u : Proc unitᴵ B) (b : Bool) where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Ext B K q cert
open Plugged B K u

SK : Set
SK = MC.St K

SU : Set
SU = MC.St u

St : Set
St = MC.obj Sᴷ

Loop : Set
Loop = Neg B ⊎ Pos B

-- The one test the transfer is valid at.
Q : Bool → ℚ
Q = indᵇ b

nnQ : NNF Q
nnQ = indᵇ-nn b

-- A `returnₚ` node's two branches are the same, so the average is that
-- branch; spelled with one subject because `_*_` is not injective and a
-- second `_` would be left for unification.
private
  dirac-node : (x : ℚ) → 1ℚ ℚ.* x ℚ.+ 0ℚ ℚ.* x ≡ x
  dirac-node x = node-dirac x x

------------------------------------------------------------------------
-- The refined loop

-- Where the context's emission goes: a query re-enters the loop, a verdict
-- leaves.  This is `Machines.Collapse`'s `outᵍ`, paired with the process's
-- state and case-split so that the loop reduces.
ρᴷ : SU → SK × (Neg B ⊎ Bool) → St × ((⊥ ⊎ Bool) ⊎ Loop)
ρᴷ su (s , inj₁ n) = (s , su) , inj₂ (inj₁ n)
ρᴷ su (s , inj₂ v) = (s , su) , inj₁ (inj₂ v)

hᴷ : SU → (r : ℕ) → Ansᶜ r → St × ((⊥ ⊎ Bool) ⊎ Loop)
hᴷ su r y = ρᴷ su (forget y)

-- …and the process's, whose external summand is empty.
ρᵁ : SK → SU × (⊥ ⊎ Pos B) → St × ((⊥ ⊎ Bool) ⊎ Loop)
ρᵁ s (su , inj₁ e) = ⊥-elim e
ρᵁ s (su , inj₂ p) = (s , su) , inj₂ (inj₂ p)

bodyᴿ : Body St Loop (⊥ ⊎ Bool)
bodyᴿ ((s , su) , inj₁ n) = mapₚ (ρᵁ s) (MC.step u (su , inj₂ n))
bodyᴿ ((s , su) , inj₂ p) = mapₚ (hᴷ su (Φ s)) (onLᵍ s p)

Runᴿ : St × Loop → Dₚ Bool
Runᴿ sa = iterₚ bodyᴿ sa >>=ₚ verdict

Stepᴿ : Dₚ (St × ((⊥ ⊎ Bool) ⊎ Loop)) → Dₚ Bool
Stepᴿ Y = stepᵢ bodyᴿ Y >>=ₚ verdict

------------------------------------------------------------------------
-- …and the strategy it is compared against

run : SU → Strat (Neg B) (Pos B) → Dₚ Bool
run = runᴹFrom u

tgtᴷ : ℕ → SK → Pos B → Strat (Neg B) (Pos B)
tgtᴷ f s p = extract b f (Φ s) (onLᵍ s p)

strat : ℕ → SK → Loop → Strat (Neg B) (Pos B)
strat f s (inj₁ n) = ask n (tgtᴷ f s)
strat f s (inj₂ p) = tgtᴷ f s p

resume : ℕ → SK → SU × (⊥ ⊎ Pos B) → Dₚ Bool
resume f s = resumeᴹ u λ su′ p → run su′ (tgtᴷ f s p)

------------------------------------------------------------------------
-- The context is dominated by the strategy, up to the fuel

mutual
  loopFwd : (f : ℕ) (s : SK) (su : SU) (x : Loop) (j : ℕ) → j ℕ.≤ f
          → Σ[ m ∈ ℕ ] (cum j (Runᴿ ((s , su) , x)) Q ℚ.≤ cum m (run su (strat f s x)) Q)
  loopFwd f s su (inj₁ n) j le = uFwd f s (MC.step u (su , inj₂ n)) j le
  loopFwd f s su (inj₂ p) j le = treeFwd f (Φ s) (onLᵍ s p) su j le

  treeFwd : (f r : ℕ) (X : Dₚ (Ansᶜ r)) (su : SU) (j : ℕ) → j ℕ.≤ f
          → Σ[ m ∈ ℕ ] (cum j (Stepᴿ (mapₚ (hᴷ su r) X)) Q
                        ℚ.≤ cum m (run su (extract b f r X)) Q)
  treeFwd f       r X su zero    le      = 0 , ≤-refl
  treeFwd zero    r X su (suc j) ()
  treeFwd (suc f) r X su (suc j) (s≤s le) =
    suc (suc i)
    , ≤-trans (node-mono (wt X true) (wt X false) (wt-nn X true) (wt-nn X false)
                (≤-trans (proj₂ w₁) (cum-mono (ℕP.m≤m⊔n i₁ i₂) (g true) Q nnQ))
                (≤-trans (proj₂ w₂) (cum-mono (ℕP.m≤n⊔m i₁ i₂) (g false) Q nnQ)))
              (≤-reflexive (trans (sym (E-coinᵈ X λ c → cum i (g c) Q))
                                  (sym (coin-bind-cum (coinᵈ X) g i Q))))
    where
    g : Bool → Dₚ Bool
    g c = run su (extractL b f r (br X c))

    w₁ = treeFwdL f r su (br X true) j le
    w₂ = treeFwdL f r su (br X false) j le
    i₁ = proj₁ w₁
    i₂ = proj₁ w₂
    i  = i₁ ⊔ i₂

  treeFwdL : (f r : ℕ) (su : SU) (y : Ansᶜ r ⊎ Dₚ (Ansᶜ r)) (j : ℕ) → j ℕ.≤ f
           → Σ[ m ∈ ℕ ] (leafₚ j (tagₚ (tagᵢ bodyᴿ (tagₚ y (returnₚ ∘′ hᴷ su r))) verdict) Q
                         ℚ.≤ cum m (run su (extractL b f r y)) Q)
  treeFwdL f r su (inj₂ X′) j le = treeFwd f r X′ su j le
  treeFwdL f r su (inj₁ (inj₁ ((s , _) , n))) zero    le = 0 , ≤-refl
  treeFwdL f r su (inj₁ (inj₁ ((s , _) , n))) (suc j) le =
    let m , bd = loopFwd f s su (inj₁ n) j (ℕP.≤-trans (ℕP.n≤1+n j) le)
    in m , ≤-trans (≤-reflexive (dirac-node _)) bd
  treeFwdL f r su (inj₁ (inj₂ (_ , v))) zero    le = 1 , cum-nn 1 (returnₚ v) Q nnQ
  treeFwdL f r su (inj₁ (inj₂ (_ , v))) (suc j) le =
    1 , ≤-trans (≤-reflexive (dirac-node _))
                (≤-trans (returnₚ-cum-≤ j v Q nnQ)
                         (≤-reflexive (sym (returnₚ-cum 0 v Q))))

  uFwd : (f : ℕ) (s : SK) (W : Dₚ (SU × (⊥ ⊎ Pos B))) (j : ℕ) → j ℕ.≤ f
       → Σ[ m ∈ ℕ ] (cum j (Stepᴿ (mapₚ (ρᵁ s) W)) Q ℚ.≤ cum m (W >>=ₚ resume f s) Q)
  uFwd f s W zero    le = 0 , ≤-refl
  uFwd f s W (suc j) le =
    suc i
    , node-mono (wt W true) (wt W false) (wt-nn W true) (wt-nn W false)
        (≤-trans (proj₂ w₁)
                 (leafₚ-mono (ℕP.m≤m⊔n i₁ i₂) (tagₚ (br W true) (resume f s)) Q nnQ))
        (≤-trans (proj₂ w₂)
                 (leafₚ-mono (ℕP.m≤n⊔m i₁ i₂) (tagₚ (br W false) (resume f s)) Q nnQ))
    where
    le′ = ℕP.≤-trans (ℕP.n≤1+n j) le
    w₁ = uFwdL f s (br W true) j le′
    w₂ = uFwdL f s (br W false) j le′
    i₁ = proj₁ w₁
    i₂ = proj₁ w₂
    i  = i₁ ⊔ i₂

  uFwdL : (f : ℕ) (s : SK) (y : (SU × (⊥ ⊎ Pos B)) ⊎ Dₚ (SU × (⊥ ⊎ Pos B))) (j : ℕ)
        → j ℕ.≤ f
        → Σ[ m ∈ ℕ ] (leafₚ j (tagₚ (tagᵢ bodyᴿ (tagₚ y (returnₚ ∘′ ρᵁ s))) verdict) Q
                      ℚ.≤ leafₚ m (tagₚ y (resume f s)) Q)
  uFwdL f s (inj₂ W′)             j       le = uFwd f s W′ j le
  uFwdL f s (inj₁ (su′ , inj₁ e)) j       le = ⊥-elim e
  uFwdL f s (inj₁ (su′ , inj₂ p)) zero    le = 0 , ≤-refl
  uFwdL f s (inj₁ (su′ , inj₂ p)) (suc j) le =
    let m , bd = loopFwd f s su′ (inj₂ p) j (ℕP.≤-trans (ℕP.n≤1+n j) le)
    in m , ≤-trans (≤-reflexive (dirac-node _)) bd

------------------------------------------------------------------------
-- …and dominates it at every budget

mutual
  loopBwd : (f : ℕ) (s : SK) (su : SU) (x : Loop) (j : ℕ)
          → Σ[ m ∈ ℕ ] (cum j (run su (strat f s x)) Q ℚ.≤ cum m (Runᴿ ((s , su) , x)) Q)
  loopBwd f s su (inj₁ n) j = uBwd f s (MC.step u (su , inj₂ n)) j
  loopBwd f s su (inj₂ p) j = treeBwd f (Φ s) (onLᵍ s p) su j

  treeBwd : (f r : ℕ) (X : Dₚ (Ansᶜ r)) (su : SU) (j : ℕ)
          → Σ[ m ∈ ℕ ] (cum j (run su (extract b f r X)) Q
                        ℚ.≤ cum m (Stepᴿ (mapₚ (hᴷ su r) X)) Q)
  treeBwd zero    r X su j =
    0 , ≤-trans (returnₚ-cum-≤ j (not b) Q nnQ) (≤-reflexive (indᵇ-not b))
  treeBwd (suc f) r X su zero          = 0 , ≤-refl
  treeBwd (suc f) r X su (suc zero)    =
    0 , ≤-reflexive (cum-1-bind (coinₚ (coinᵈ X)) (λ c → run su (extractL b f r (br X c))) Q)
  treeBwd (suc f) r X su (suc (suc j)) =
    suc i
    , ≤-trans (≤-reflexive (trans (coin-bind-cum (coinᵈ X) g j Q)
                                  (E-coinᵈ X λ c → cum j (g c) Q)))
              (node-mono (wt X true) (wt X false) (wt-nn X true) (wt-nn X false)
                (≤-trans (proj₂ w₁)
                  (leafₚ-mono (ℕP.m≤m⊔n i₁ i₂)
                    (tagₚ (tagᵢ bodyᴿ (tagₚ (br X true) (returnₚ ∘′ hᴷ su r))) verdict) Q nnQ))
                (≤-trans (proj₂ w₂)
                  (leafₚ-mono (ℕP.m≤n⊔m i₁ i₂)
                    (tagₚ (tagᵢ bodyᴿ (tagₚ (br X false) (returnₚ ∘′ hᴷ su r))) verdict) Q nnQ)))
    where
    g : Bool → Dₚ Bool
    g c = run su (extractL b f r (br X c))

    w₁ = treeBwdL f r su (br X true) j
    w₂ = treeBwdL f r su (br X false) j
    i₁ = proj₁ w₁
    i₂ = proj₁ w₂
    i  = i₁ ⊔ i₂

  treeBwdL : (f r : ℕ) (su : SU) (y : Ansᶜ r ⊎ Dₚ (Ansᶜ r)) (j : ℕ)
           → Σ[ m ∈ ℕ ] (cum j (run su (extractL b f r y)) Q
                         ℚ.≤ leafₚ m (tagₚ (tagᵢ bodyᴿ (tagₚ y (returnₚ ∘′ hᴷ su r))) verdict) Q)
  treeBwdL f r su (inj₂ X′) j = treeBwd f r X′ su j
  treeBwdL f r su (inj₁ (inj₁ ((s , _) , n))) j =
    let m , bd = loopBwd f s su (inj₁ n) j
    in suc m , ≤-trans bd (≤-reflexive (sym (dirac-node _)))
  treeBwdL f r su (inj₁ (inj₂ (_ , v))) j =
    2 , ≤-trans (returnₚ-cum-≤ j v Q nnQ)
                (≤-reflexive (sym (trans (dirac-node _) (returnₚ-cum 0 v Q))))

  uBwd : (f : ℕ) (s : SK) (W : Dₚ (SU × (⊥ ⊎ Pos B))) (j : ℕ)
       → Σ[ m ∈ ℕ ] (cum j (W >>=ₚ resume f s) Q ℚ.≤ cum m (Stepᴿ (mapₚ (ρᵁ s) W)) Q)
  uBwd f s W zero    = 0 , ≤-refl
  uBwd f s W (suc j) =
    suc i
    , node-mono (wt W true) (wt W false) (wt-nn W true) (wt-nn W false)
        (≤-trans (proj₂ w₁)
          (leafₚ-mono (ℕP.m≤m⊔n i₁ i₂)
            (tagₚ (tagᵢ bodyᴿ (tagₚ (br W true) (returnₚ ∘′ ρᵁ s))) verdict) Q nnQ))
        (≤-trans (proj₂ w₂)
          (leafₚ-mono (ℕP.m≤n⊔m i₁ i₂)
            (tagₚ (tagᵢ bodyᴿ (tagₚ (br W false) (returnₚ ∘′ ρᵁ s))) verdict) Q nnQ))
    where
    w₁ = uBwdL f s (br W true) j
    w₂ = uBwdL f s (br W false) j
    i₁ = proj₁ w₁
    i₂ = proj₁ w₂
    i  = i₁ ⊔ i₂

  uBwdL : (f : ℕ) (s : SK) (y : (SU × (⊥ ⊎ Pos B)) ⊎ Dₚ (SU × (⊥ ⊎ Pos B))) (j : ℕ)
        → Σ[ m ∈ ℕ ] (leafₚ j (tagₚ y (resume f s)) Q
                      ℚ.≤ leafₚ m (tagₚ (tagᵢ bodyᴿ (tagₚ y (returnₚ ∘′ ρᵁ s))) verdict) Q)
  uBwdL f s (inj₂ W′)             j = uBwd f s W′ j
  uBwdL f s (inj₁ (su′ , inj₁ e)) j = ⊥-elim e
  uBwdL f s (inj₁ (su′ , inj₂ p)) j =
    let m , bd = loopBwd f s su′ (inj₂ p) j
    in suc m , ≤-trans bd (≤-reflexive (sym (dirac-node _)))

------------------------------------------------------------------------
-- Undoing the refinement, once

-- The certificate's emissions are the step's up to `_≈ₚ_`, and `cont` is the
-- loop read as an observation.  Both conversions happen HERE, outside the
-- inductions, because the fuel is still free to be chosen at this point.

obsᴿ : SK → SU → Dₚ Bool
obsᴿ sk su = Stepᴿ (mapₚ (hᴷ su (Φ sk ℕ.+ q)) (onRᵍ sk tt))

private
  body-red : (sa : St × Loop) → bodyᴿ sa ≈ₚ body sa
  body-red ((s , su) , inj₁ n) = bindᶠ λ where
    (su′ , inj₁ e) → ⊥-elim e
    (su′ , inj₂ p) → ≈refl
  body-red ((s , su) , inj₂ p) =
      ≈sym (map-map (onLᵍ s p) forget (ρᴷ su))
    ⟨≈⟩ map-arg (ρᴷ su) (cohL s p)
    ⟨≈⟩ bindᶠ λ where (s′ , inj₁ n) → ≈refl
                      (s′ , inj₂ v) → ≈refl

  cont-redᴿ : (z : St × ((⊥ ⊎ Bool) ⊎ Loop)) → (contᵢ bodyᴿ z >>=ₚ verdict) ≈ₚ cont z
  cont-redᴿ (st , inj₁ o) = >>=ₚ-identityˡ (st , o) verdict
  cont-redᴿ (st , inj₂ x) = bindˣ (iterₚ-cong bodyᴿ body body-red (st , x))

  step-cont : (Y : Dₚ (St × ((⊥ ⊎ Bool) ⊎ Loop))) → Stepᴿ Y ≈ₚ (Y >>=ₚ cont)
  step-cont Y = bindˣ (stepᵢ-unfold bodyᴿ Y)
          ⟨≈⟩ >>=ₚ-assoc Y (contᵢ bodyᴿ) verdict
          ⟨≈⟩ bindᶠ cont-redᴿ

  tick-red : (sk : SK) (su : SU)
           → (kᴷ ((sk , su) , inj₁ (inj₂ tt)) >>=ₚ cont) ≈ₚ obsᴿ sk su
  tick-red sk su = bindˣ ( bindᶠ (λ where (s′ , inj₁ n) → ≈refl
                                          (s′ , inj₂ v) → ≈refl)
                     ⟨≈⟩ map-arg (ρᴷ su) (≈sym (cohR sk tt))
                     ⟨≈⟩ map-map (onRᵍ sk tt) forget (ρᴷ su))
             ⟨≈⟩ ≈sym (step-cont (mapₚ (hᴷ su (Φ sk ℕ.+ q)) (onRᵍ sk tt)))

observe-≈ : ⟦ K 𝒫.∘ u ⟧ᴼ
          ≈ₚ (MC.point (MC.state K) ttᵛ >>=ₚ λ sk →
              MC.point (MC.state u) ttᵛ >>=ₚ obsᴿ sk)
observe-≈ = collapse
      ⟨≈⟩ observe
      ⟨≈⟩ bindˣ point-red
      ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state K) ttᵛ) _ _
      ⟨≈⟩ bindᶠ λ sk → >>=ₚ-assoc (MC.point (MC.state u) ttᵛ) _ _
                 ⟨≈⟩ bindᶠ λ su → >>=ₚ-identityˡ (sk , su) _ ⟨≈⟩ tick-red sk su

------------------------------------------------------------------------
-- …and the two dominations, at the process's own run

runFwd : (f : ℕ) (sk : SK)
       → Dom≤ Q f (MC.point (MC.state u) ttᵛ >>=ₚ obsᴿ sk)
                  (runᴹ u (extract b f (Φ sk ℕ.+ q) (onRᵍ sk tt)))
runFwd f sk = dom≤-bind Q nnQ f (MC.point (MC.state u) ttᵛ) (obsᴿ sk) _
                        (treeFwd f (Φ sk ℕ.+ q) (onRᵍ sk tt))

runBwd : (f : ℕ) (sk : SK)
       → Dom₀ Q (runᴹ u (extract b f (Φ sk ℕ.+ q) (onRᵍ sk tt)))
                (MC.point (MC.state u) ttᵛ >>=ₚ obsᴿ sk)
runBwd f sk = dom₀-bind Q nnQ (MC.point (MC.state u) ttᵛ) _ (obsᴿ sk)
                        (treeBwd f (Φ sk ℕ.+ q) (onRᵍ sk tt))
