{-# OPTIONS --safe --without-K --guardedness #-}

-- Compiled SSP distinguishers are dense among well-bracketed tests
-- (`tests-dense`): well-bracketed closures that every compiled distinguisher
-- reads alike are read alike by every well-bracketed test.  With
-- `SSP.Dense.games-dense`, compilation preserves `≈ℰ` (`preserves-≈ℰ`), so
-- `SSP→PM[wb]` preserves `≤UC` (`preserves-≤UC`).
--
-- A test over a closure is a traced machine whose loop alternates the two
-- steps (`Machines.Collapse.Loop`, `obs-comp`).  Its steps cut at depth `c` and
-- at most `r` calls allowed, the test from a state is an SSP distinguisher
-- (`trunc`).  Its readout is below the test's at every depth (`tree-below`, by
-- induction on `r`), and at depth `m` the test's is below the distinguisher's
-- once `m ≤ c, r` (`loop-below`, by induction on `m`).  There the closure's
-- well-bracketedness is spent: the distinguisher checks a reply's channel and
-- the test need not, but a well-bracketed closure answers on the queried one.

open import Categories.Category.Monoidal.Bundle

open import Class.DecEq
open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties hiding (_≟_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter hiding (flat)
open import ProbabilisticLogic.Dp.Mass
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol using () renaming (Calls to Callsᶠ)
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Oracle renaming (answer to answerᴼ)
open import CategoricalCrypto.SSP.Compile
open import CategoricalCrypto.SSP.Cut
open import CategoricalCrypto.SSP.Dense
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Semantics
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Bracket.Category using (⊙≈∘) renaming (_⊙_ to _⊙ʷ_)
open import CategoricalCrypto.UC.Bracket.Monitor
open import CategoricalCrypto.UC.Bracket.Setup
open import CategoricalCrypto.UC.Machine hiding (Ωᴵ)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.SSP.Setup as SSP
import Data.Nat.Properties as ℕP

module CategoricalCrypto.SSP.Dense.Tests where

private
  module G  = MonoidalCategory 𝔾ᵒ
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

private variable B : Iface

------------------------------------------------------------------------
-- A test, truncated

private
  tick : Σ (Ch Ωᴵ) (Q Ωᴵ)
  tick = tt , tt

module _ (T̂ : Proc (flat B) (flat Ωᴵ)) where

  -- From the state `s`, each step cut at depth `c`, at most `r` calls; its
  -- verdicts carry the state `s★`.
  mutual
    treeT : {S : Set} → S → ℕ → ℕ → MC.St T̂ → Σ (Ch B) (R B) ⊎ Σ (Ch Ωᴵ) (Q Ωᴵ) → Calls B (S × Bool)
    treeT s★ c zero    s x = dead
    treeT s★ c (suc r) s x = cutᵏ c (MC.step T̂ (s , x)) (leafT s★ c r)

    leafT : {S : Set} → S → ℕ → ℕ → MC.St T̂ × (Σ (Ch B) (Q B) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)) → Calls B (S × Bool)
    leafT s★ c r (s′ , inj₁ (a , q)) = call a q λ ans → treeT s★ c r s′ (inj₁ (a , ans))
    leafT s★ c r (s′ , inj₂ (_ , b)) = ret (s★ , b)

  trunc : ℕ → ℕ → MC.St T̂ → Protocol B Ωᴵ
  trunc c r s = record { St = ⊤ ; init = tt ; step = λ _ _ _ → treeT tt c r s (inj₂ tick) }

------------------------------------------------------------------------
-- A compiled cut tree against a closure

private
  dbl : ℕ → ℕ
  dbl zero    = zero
  dbl (suc n) = suc (suc (dbl n))

module _ (X̂ : Proc (flat unitᴵ) (flat B)) (D′ : Protocol B Ωᴵ) (V : Bool → ℚ) (nnV : NNF V) where

  private
    P = toProtocol ⦃ Ch-dec B ⦄ D′

    O : Calls B (St D′ × Bool) → MC.St X̂ → Dₚ ((MSt P × MC.St X̂) × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)))
    O t = orun e⁺ e⁻ P X̂ (compiled t)

    Vᵛ : (MSt P × MC.St X̂) × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)) → ℚ
    Vᵛ y = V (verd y)

    nnVᵛ : NNF Vᵛ
    nnVᵛ y = nnV (verd y)

  -- Each node of a cut costs the compiled run a coin's two steps.
  mutual
    cut-below : {Y : Set} (n j : ℕ) (d : Dₚ Y) (K : Y → Calls B (St D′ × Bool)) (sX : MC.St X̂)
              → cum n d (λ y → cum j (O (K y) sX) Vᵛ) ℚ.≤ cum (dbl n ℕ.+ j) (O (cutᵏ n d K) sX) Vᵛ
    cut-below zero    j d K sX = cum-nn j (O (cutᵏ zero d K) sX) Vᵛ nnVᵛ
    cut-below (suc n) j d K sX =
      ≤-trans (node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
                         (cutL-below n j (br d true) K sX) (cutL-below n j (br d false) K sX))
              (≤-reflexive (sym (trans (coin-bind-cum (nodeᴰ d) (λ b → O (cutLᵏ n (br d b) K) sX) (dbl n ℕ.+ j) Vᵛ)
                                       (cong (wt d true ℚ.* cum (dbl n ℕ.+ j) (O (cutLᵏ n (br d true) K) sX) Vᵛ ℚ.+_)
                                             (+-identityʳ _)))))

    cutL-below : {Y : Set} (n j : ℕ) (x : Y ⊎ Dₚ Y) (K : Y → Calls B (St D′ × Bool)) (sX : MC.St X̂)
               → leafₚ n x (λ y → cum j (O (K y) sX) Vᵛ) ℚ.≤ cum (dbl n ℕ.+ j) (O (cutLᵏ n x K) sX) Vᵛ
    cutL-below n j (inj₁ y)  K sX = cum-mono (ℕP.m≤n+m j (dbl n)) (O (K y) sX) Vᵛ nnVᵛ
    cutL-below n j (inj₂ d′) K sX = cut-below n j d′ K sX

  mutual
    cut-above : {Y : Set} (n j : ℕ) (d : Dₚ Y) (K : Y → Calls B (St D′ × Bool)) (sX : MC.St X̂)
              → cum j (O (cutᵏ n d K) sX) Vᵛ ℚ.≤ cum n d (λ y → cum j (O (K y) sX) Vᵛ)
    cut-above zero    j d K sX = ≤-reflexive (botₚ-cum j Vᵛ)
    cut-above (suc n) j d K sX =
      ≤-trans (coin-bind-≤E (nodeᴰ d) (λ b → O (cutLᵏ n (br d b) K) sX) j Vᵛ nnVᵛ)
      (≤-trans (≤-reflexive (cong (wt d true ℚ.* cum j (O (cutLᵏ n (br d true) K) sX) Vᵛ ℚ.+_) (+-identityʳ _)))
               (node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
                          (cutL-above n j (br d true) K sX) (cutL-above n j (br d false) K sX)))

    cutL-above : {Y : Set} (n j : ℕ) (x : Y ⊎ Dₚ Y) (K : Y → Calls B (St D′ × Bool)) (sX : MC.St X̂)
               → cum j (O (cutLᵏ n x K) sX) Vᵛ ℚ.≤ leafₚ n x (λ y → cum j (O (K y) sX) Vᵛ)
    cutL-above n j (inj₁ y)  K sX = ≤-refl
    cutL-above n j (inj₂ d′) K sX = cut-above n j d′ K sX

------------------------------------------------------------------------
-- A test over a closure

module _ (T̂ : Proc (flat B) (flat Ωᴵ)) (X̂ : Proc (flat unitᴵ) (flat B)) where

  private
    Out Lpᵗ St² : Set
    Out = Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)
    Lpᵗ = Σ (Ch B) (Q B) ⊎ Σ (Ch B) (R B)
    St² = MC.St T̂ × MC.St X̂

    open Col.Loop (Σ (Ch unitᴵ) (R unitᴵ) ⊎ Σ (Ch Ωᴵ) (Q Ωᴵ)) Out Lpᵗ (Col.Sᴳ T̂ X̂)
                  (Col.kᴳ {Σ (Ch unitᴵ) (R unitᴵ)} {Σ (Ch unitᴵ) (Q unitᴵ)} {Σ (Ch B) (R B)} {Σ (Ch B) (Q B)}
                          {Σ (Ch Ωᴵ) (R Ωᴵ)} {Σ (Ch Ωᴵ) (Q Ωᴵ)} T̂ X̂)

    -- Where an emission goes: the test's out or to the closure, the closure's back.
    gT : MC.St X̂ → MC.St T̂ × (Σ (Ch B) (Q B) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)) → St² × (Out ⊎ Lpᵗ)
    gT sX y = (proj₁ y , sX) , Col.outᵍ (proj₂ y)

    gX : MC.St T̂ → MC.St X̂ × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch B) (R B)) → St² × (Out ⊎ Lpᵗ)
    gX s′ z = (s′ , proj₁ z) , Col.outᶠ (proj₂ z)

  -- The composite's loop, from the test's step at `x`.
  Lp : MC.St T̂ → Σ (Ch B) (R B) ⊎ Σ (Ch Ωᴵ) (Q Ωᴵ) → MC.St X̂ → Dₚ (St² × Out)
  Lp s x sX = stepᵢ body (MC.step T̂ (s , x) >>=ₚ λ y → returnₚ (gT sX y))

  step≈Lp : (s : MC.St T̂) (sX : MC.St X̂)
          → MC.step (_⊙ʷ_ {B = B} {C = Ωᴵ} {A = unitᴵ} T̂ X̂) ((s , sX) , inj₂ tick) ≈ₚ Lp s (inj₂ tick) sX
  step≈Lp s sX = step-red (s , sX) (inj₂ tick) ⟨≈⟩ ≈sym (stepᵢ-unfold body (MC.step T̂ (s , inj₂ tick) >>=ₚ λ y → returnₚ (gT sX y)))

  private
    -- Into the loop, at a cost in depth.
    into-loop : {Y : Set} (F : St² × Out → ℚ) → NNF F → (n : ℕ) (d : Dₚ Y) (g : Y → St² × (Out ⊎ Lpᵗ))
              → cum n (d >>=ₚ λ y → contᵢ body (g y)) F ℚ.≤ cum (n ℕ.+ suc n) (stepᵢ body (d >>=ₚ λ y → returnₚ (g y))) F
    into-loop F nn n d g =
      ≤-trans (>>=ₚ-boundA n d (λ y → contᵢ body (g y)) F nn)
     (≤-trans (≤-reflexive (cum-cong-P n d _ _ λ y → sym (>>=ₚ-identityˡ-cum n (g y) (contᵢ body) F)))
     (≤-trans (>>=ₚ-boundB n (suc n) d (λ y → returnₚ (g y) >>=ₚ contᵢ body) F nn)
     (≤-trans (≤-reflexive (sym (>>=ₚ-assoc-cum (n ℕ.+ suc n) d (λ y → returnₚ (g y)) (contᵢ body) F)))
              (unfold-≤-stepᵢ (n ℕ.+ suc n) body (d >>=ₚ λ y → returnₚ (g y)) F nn))))

  module _ (D′ : Protocol B Ωᴵ) (s★ : St D′) (c : ℕ) (V : Bool → ℚ) (nnV : NNF V) where

    private
      P = toProtocol ⦃ Ch-dec B ⦄ D′

      O : Calls B (St D′ × Bool) → MC.St X̂ → Dₚ ((MSt P × MC.St X̂) × Out)
      O t = orun e⁺ e⁻ P X̂ (compiled t)

      Vᵛ : (MSt P × MC.St X̂) × Out → ℚ
      Vᵛ y = V (verd y)

      nnVᵛ : NNF Vᵛ
      nnVᵛ y = nnV (verd y)

      Vᶜ : St² × Out → ℚ
      Vᶜ y = V (verd y)

      nnVᶜ : NNF Vᶜ
      nnVᶜ y = nnV (verd y)

      -- The continuation a compiled call of the truncated test waits on.
      Kc : ℕ → MC.St T̂ → (a : Ch B) → Σ (Ch B) (R B) → Callsᶠ (flat B) (St D′ × Σ (Ch Ωᴵ) (R Ωᴵ))
      Kc r s′ a = resume B {c = a} λ ans → mapᶜ (map₂ (tt ,_)) (treeT {B} T̂ s★ c r s′ (inj₁ (a , ans)))

    -- The truncated test's readout is below the test's.
    mutual
      tree-below : (r : ℕ) (s : MC.St T̂) (x : Σ (Ch B) (R B) ⊎ Σ (Ch Ωᴵ) (Q Ωᴵ)) (sX : MC.St X̂) (j : ℕ)
                 → Σ[ k ∈ ℕ ] cum j (O (treeT {B} T̂ s★ c r s x) sX) Vᵛ ℚ.≤ cum k (Lp s x sX) Vᶜ
      tree-below zero    s x sX j = 0 , ≤-reflexive (botₚ-cum j Vᵛ)
      tree-below (suc r) s x sX j =
        let K , sp = uniformize (λ y i → cum j (O (leafT {B} T̂ s★ c r y) sX) Vᵛ ℚ.≤ cum i (contᵢ body (gT sX y)) Vᶜ)
                                (λ y le h → ≤-trans h (cum-mono le (contᵢ body (gT sX y)) Vᶜ nnVᶜ))
                                (leaf-below r sX j) c d
        in c ℕ.+ K ℕ.+ suc (c ℕ.+ K)
         , ≤-trans (cut-above {B} X̂ D′ V nnV c j d (leafT {B} T̂ s★ c r) sX)
           (≤-trans (cum-mono-Supp c d (λ y → cum j (O (leafT {B} T̂ s★ c r y) sX) Vᵛ) (λ y → cum K (contᵢ body (gT sX y)) Vᶜ) sp)
           (≤-trans (>>=ₚ-boundB c K d (λ y → contᵢ body (gT sX y)) Vᶜ nnVᶜ)
                    (into-loop Vᶜ nnVᶜ (c ℕ.+ K) d (gT sX))))
        where d = MC.step T̂ (s , x)

      leaf-below : (r : ℕ) (sX : MC.St X̂) (j : ℕ) (y : MC.St T̂ × (Σ (Ch B) (Q B) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)))
                 → Σ[ i ∈ ℕ ] cum j (O (leafT {B} T̂ s★ c r y) sX) Vᵛ ℚ.≤ cum i (contᵢ body (gT sX y)) Vᶜ
      leaf-below r sX j (s′ , inj₂ (u , b)) =
        1 , ≤-trans (returnₚ-cum-≤ j ((idle s★ , sX) , inj₂ (u , b)) Vᵛ nnVᵛ)
                    (≤-reflexive (sym (returnₚ-cum 0 ((s′ , sX) , inj₂ (u , b)) Vᶜ)))
      leaf-below r sX j (s′ , inj₁ (a , q)) =
        let K , sp = uniformize (λ z i → cum j (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a) z) Vᵛ ℚ.≤ cum i (contᵢ body (gX s′ z)) Vᶜ)
                                (λ z le h → ≤-trans h (cum-mono le (contᵢ body (gX s′ z)) Vᶜ nnVᶜ))
                                (answer-below r s′ a j) j dX
        in j ℕ.+ K ℕ.+ suc (j ℕ.+ K)
         , ≤-trans (>>=ₚ-boundA j dX (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a)) Vᵛ nnVᵛ)
           (≤-trans (cum-mono-Supp j dX (λ z → cum j (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a) z) Vᵛ)
                                       (λ z → cum K (contᵢ body (gX s′ z)) Vᶜ) sp)
           (≤-trans (>>=ₚ-boundB j K dX (λ z → contᵢ body (gX s′ z)) Vᶜ nnVᶜ)
                    (into-loop Vᶜ nnVᶜ (j ℕ.+ K) dX (gX s′))))
        where dX = MC.step X̂ (sX , inj₂ (a , q))

      answer-below : (r : ℕ) (s′ : MC.St T̂) (a : Ch B) (j : ℕ) (z : MC.St X̂ × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch B) (R B)))
                   → Σ[ i ∈ ℕ ] cum j (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a) z) Vᵛ ℚ.≤ cum i (contᵢ body (gX s′ z)) Vᶜ
      answer-below r s′ a j (_   , inj₁ e)          = ⊥-elim (e⁻ e)
      answer-below r s′ a j (sX′ , inj₂ (a′ , ans)) = reply-below r s′ j (_≟_ ⦃ Ch-dec B ⦄ a′ a) sX′ ans

      reply-below : (r : ℕ) (s′ : MC.St T̂) (j : ℕ) {a a′ : Ch B} (dec : Dec (a′ ≡ a)) (sX′ : MC.St X̂) (ans : R B a′)
                  → Σ[ i ∈ ℕ ] cum j (orun e⁺ e⁻ P X̂ (reply {B} ⦃ Ch-dec B ⦄ dec ans λ ans →
                                         compiled (treeT {B} T̂ s★ c r s′ (inj₁ (a , ans)))) sX′) Vᵛ
                               ℚ.≤ cum i (contᵢ body ((s′ , sX′) , inj₂ (inj₂ (a′ , ans)))) Vᶜ
      reply-below r s′ j (yes refl) sX′ ans = tree-below r s′ (inj₁ (_ , ans)) sX′ j
      reply-below r s′ j (no _)     sX′ ans = 0 , ≤-reflexive (botₚ-cum j Vᵛ)

    -- At depth `m ≤ c, r`, the test's readout is below the truncated test's,
    -- against a well-bracketed closure.
    module _ (wX : W {unitᴵ} {B} X̂) where

      open W wX

      mutual
        loop-below : (m r : ℕ) → m ℕ.≤ c → m ℕ.≤ r
                   → (s : MC.St T̂) (x : Σ (Ch B) (R B) ⊎ Σ (Ch Ωᴵ) (Q Ωᴵ)) (sX : MC.St X̂) → I sX idle
                   → Σ[ j ∈ ℕ ] cum m (Lp s x sX) Vᶜ ℚ.≤ cum j (O (treeT {B} T̂ s★ c r s x) sX) Vᵛ
        loop-below zero    r       _   _         s x sX i = 0 , ≤-refl
        loop-below (suc m) zero    _   ()
        loop-below (suc m) (suc r) m≤c (s≤s m≤r) s x sX i =
          let J , sp = uniformize (λ y j → Tᵗ body Vᶜ m (gT sX y) ℚ.≤ cum j (O (leafT {B} T̂ s★ c r y) sX) Vᵛ)
                                  (λ y le h → ≤-trans h (cum-mono le (O (leafT {B} T̂ s★ c r y) sX) Vᵛ nnVᵛ))
                                  (turn-below m r (ℕP.≤-trans (ℕP.n≤1+n m) m≤c) m≤r sX i) c d
          in dbl c ℕ.+ J
           , ≤-trans (stepᵢ-boundA m body (d >>=ₚ λ y → returnₚ (gT sX y)) Vᶜ nnVᶜ)
             (≤-trans (>>=ₚ-boundA (suc m) d (λ y → returnₚ (gT sX y)) (Tᵗ body Vᶜ m) (Tᵗ-nn body Vᶜ m nnVᶜ))
             (≤-trans (cum-mono-P (suc m) d (λ y → cum (suc m) (returnₚ (gT sX y)) (Tᵗ body Vᶜ m))
                                            (λ y → Tᵗ body Vᶜ m (gT sX y))
                                            (λ y → returnₚ-cum-≤ (suc m) (gT sX y) (Tᵗ body Vᶜ m) (Tᵗ-nn body Vᶜ m nnVᶜ)))
             (≤-trans (cum-mono m≤c d (λ y → Tᵗ body Vᶜ m (gT sX y)) (λ y → Tᵗ-nn body Vᶜ m nnVᶜ (gT sX y)))
             (≤-trans (cum-mono-Supp c d (λ y → Tᵗ body Vᶜ m (gT sX y)) (λ y → cum J (O (leafT {B} T̂ s★ c r y) sX) Vᵛ) sp)
                      (cut-below {B} X̂ D′ V nnV c J d (leafT {B} T̂ s★ c r) sX)))))
          where d = MC.step T̂ (s , x)

        turn-below : (m r : ℕ) → m ℕ.≤ c → m ℕ.≤ r → (sX : MC.St X̂) → I sX idle
                   → (y : MC.St T̂ × (Σ (Ch B) (Q B) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)))
                   → Σ[ j ∈ ℕ ] Tᵗ body Vᶜ m (gT sX y) ℚ.≤ cum j (O (leafT {B} T̂ s★ c r y) sX) Vᵛ
        turn-below m       r _   _   sX i (s′ , inj₂ (u , b)) =
          1 , ≤-reflexive (sym (returnₚ-cum 0 ((idle s★ , sX) , inj₂ (u , b)) Vᵛ))
        turn-below zero    r _   _   sX i (s′ , inj₁ (a , q)) = 0 , ≤-refl
        turn-below (suc m) r m≤c m≤r sX i (s′ , inj₁ (a , q)) =
          let K , sp = uniformizeˢ (λ z j → Tᵗ body Vᶜ m (gX s′ z) ℚ.≤ cum j (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a) z) Vᵛ)
                                   (λ z le h → ≤-trans h (cum-mono le (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a) z) Vᵛ nnVᵛ))
                                   (suc m) dX
                                   (Supp-map (Legal I (serving a)) _
                                             (legal-below m r (ℕP.≤-trans (ℕP.n≤1+n m) m≤c) (ℕP.≤-trans (ℕP.n≤1+n m) m≤r) s′ a)
                                             (suc m) dX (I-step {s = sX} i (query {b = a} {q = q}) (suc m)))
          in suc m ℕ.+ K
           , ≤-trans (stepᵢ-boundA m body (dX >>=ₚ λ z → returnₚ (gX s′ z)) Vᶜ nnVᶜ)
             (≤-trans (>>=ₚ-boundA (suc m) dX (λ z → returnₚ (gX s′ z)) (Tᵗ body Vᶜ m) (Tᵗ-nn body Vᶜ m nnVᶜ))
             (≤-trans (cum-mono-P (suc m) dX (λ z → cum (suc m) (returnₚ (gX s′ z)) (Tᵗ body Vᶜ m))
                                             (λ z → Tᵗ body Vᶜ m (gX s′ z))
                                             (λ z → returnₚ-cum-≤ (suc m) (gX s′ z) (Tᵗ body Vᶜ m) (Tᵗ-nn body Vᶜ m nnVᶜ)))
             (≤-trans (cum-mono-Supp (suc m) dX (λ z → Tᵗ body Vᶜ m (gX s′ z))
                                                (λ z → cum K (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a) z) Vᵛ) sp)
                      (>>=ₚ-boundB (suc m) K dX (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a)) Vᵛ nnVᵛ))))
          where dX = MC.step X̂ (sX , inj₂ (a , q))

        legal-below : (m r : ℕ) → m ℕ.≤ c → m ℕ.≤ r → (s′ : MC.St T̂) (a : Ch B)
                    → (z : MC.St X̂ × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch B) (R B))) → Legal I (serving a) z
                    → Σ[ j ∈ ℕ ] Tᵗ body Vᶜ m (gX s′ z) ℚ.≤ cum j (answerᴼ e⁺ e⁻ P X̂ (Kc r s′ a) z) Vᵛ
        legal-below m r m≤c m≤r s′ a (_   , inj₁ e)         _                = ⊥-elim (e⁻ e)
        legal-below m r m≤c m≤r s′ a (sX′ , inj₂ (_ , ans)) (_ , answer , i′) =
          let j , h = loop-below m r m≤c m≤r s′ (inj₁ (a , ans)) sX′ i′
          in j , ≤-trans h (≤-reflexive (cong (λ t → cum j (orun e⁺ e⁻ P X̂ t sX′) Vᵛ)
                                              (sym (reply-refl {B} ⦃ Ch-dec B ⦄ ans λ ans →
                                                      compiled (treeT {B} T̂ s★ c r s′ (inj₁ (a , ans)))))))

------------------------------------------------------------------------
-- The readout of a test over a closure

module _ (T : B 𝒲ᵂ.⇒ Ωᴵ) (X : unitᴵ 𝒲ᵂ.⇒ B) where

  private
    T̂ : Proc (flat B) (flat Ωᴵ)
    T̂ = proj₁ (proj₂ T)

    X̂ : Proc (flat unitᴵ) (flat B)
    X̂ = proj₁ (proj₂ X)

  comp-run : Dₚ Bool
  comp-run = MC.point (MC.state T̂) ttᵛ >>=ₚ λ s → MC.point (MC.state X̂) ttᵛ >>=ₚ λ sX → mapₚ verd (Lp {B} T̂ X̂ s (inj₂ tick) sX)

  -- Opaque for `SSP.Dense.obs-proc`'s reason.
  opaque
    obs-comp : Obsᵂ (T 𝒲ᵂ.∘ X) ≈ₚ comp-run
    obs-comp =
          obs-proc (T 𝒲ᵂ.∘ X) (_⊙ʷ_ {B = B} {C = Ωᴵ} {A = unitᴵ} T̂ X̂)
            ( (proj₂ (proj₂ (proj₂ T)) ⟩∘⟨ proj₂ (proj₂ (proj₂ X)))
            ○ ⟺ (procᵒ-∘ {flat unitᴵ} {flat B} {flat Ωᴵ} T̂ X̂)
            ○ ≈ᴹ⇒≈ᵒ {flat unitᴵ} {flat Ωᴵ} (S.⟺ᴹ (⊙≈∘ {B = B} {C = Ωᴵ} {A = unitᴵ} T̂ X̂)))
      ⟨≈⟩ bindˣ {k = k} (Pw.point-⊛ (MC.state T̂) (MC.state X̂) ttᵛ)
      ⟨≈⟩ >>=ₚ-assoc ptT (λ s → ptX >>=ₚ λ sX → returnₚ (s , sX)) k
      ⟨≈⟩ bindᶠ (λ s → >>=ₚ-assoc ptX (λ sX → returnₚ (s , sX)) k
                     ⟨≈⟩ bindᶠ λ sX → >>=ₚ-identityˡ (s , sX) k ⟨≈⟩ map-arg verd (step≈Lp {B} T̂ X̂ s sX))
      where
      open G.HomReasoning

      ptT : Dₚ (MC.St T̂)
      ptT = MC.point (MC.state T̂) ttᵛ

      ptX : Dₚ (MC.St X̂)
      ptX = MC.point (MC.state X̂) ttᵛ

      k : MC.St T̂ × MC.St X̂ → Dₚ Bool
      k st = mapₚ verd (MC.step (_⊙ʷ_ {B = B} {C = Ωᴵ} {A = unitᴵ} T̂ X̂) (st , inj₂ tick))

------------------------------------------------------------------------
-- Density

module _ (T : B 𝒲ᵂ.⇒ Ωᴵ) {X Y : unitᴵ 𝒲ᵂ.⇒ B}
         (agree : (D : Protocol B Ωᴵ) (ε : ℚ) → 0ℚ ℚ.< ε → Obsᵂ (⟦ D ⟧ᵂ 𝒲ᵂ.∘ X) ≈ₚ[ ε ] Obsᵂ (⟦ D ⟧ᵂ 𝒲ᵂ.∘ Y))
         (ε : ℚ) (pos : 0ℚ ℚ.< ε) (b : Bool) where

  private
    T̂ : Proc (flat B) (flat Ωᴵ)
    T̂ = proj₁ (proj₂ T)

    X̂ Ŷ : Proc (flat unitᴵ) (flat B)
    X̂ = proj₁ (proj₂ X)
    Ŷ = proj₁ (proj₂ Y)

    ptT : Dₚ (MC.St T̂)
    ptT = MC.point (MC.state T̂) ttᵛ

    Pb : Bool → ℚ
    Pb = indᵇ b

    nnPb : NNF Pb
    nnPb = indᵇ-nn b

    Z : (M : Proc (flat unitᴵ) (flat B)) → MC.St T̂ → Dₚ Bool
    Z M s = MC.point (MC.state M) ttᵛ >>=ₚ λ sM → mapₚ verd (Lp {B} T̂ M s (inj₂ tick) sM)

    -- Through the truncated test at `k₁`, which the two closures agree on.
    per-state : (k₁ : ℕ) (s : MC.St T̂) → Σ[ K ∈ ℕ ] cum k₁ (Z X̂ s) Pb ℚ.≤ cum K (Z Ŷ s) Pb ℚ.+ ε
    per-state k₁ s =
      let J  , sp  = uniformizeˢ (λ sX j → cum k₁ (mapₚ verd (Lp {B} T̂ X̂ s (inj₂ tick) sX)) Pb ℚ.≤ cum j (mapₚ verd (Oᴰ X̂ sX)) Pb)
                                 (λ sX le h → ≤-trans h (cum-mono le (mapₚ verd (Oᴰ X̂ sX)) Pb nnPb))
                                 k₁ ptX
                                 (Supp-map (λ sX → W.I wX sX idle) _ step-below k₁ ptX (W.I-init wX k₁))
          j₁ , le₁ = proj₂ (obs-oracle Dₛ X) Pb nnPb (k₁ ℕ.+ J)
          j₂ , le₂ = proj₁ (agree Dₛ ε pos) b j₁
          j₃ , le₃ = proj₁ (obs-oracle Dₛ Y) Pb nnPb j₂
          K  , sq  = uniformize (λ sY k → cum j₃ (mapₚ verd (Oᴰ Ŷ sY)) Pb ℚ.≤ cum k (mapₚ verd (Lp {B} T̂ Ŷ s (inj₂ tick) sY)) Pb)
                                (λ sY le h → ≤-trans h (cum-mono le (mapₚ verd (Lp {B} T̂ Ŷ s (inj₂ tick) sY)) Pb nnPb))
                                (tree-step j₃) j₃ ptY
      in j₃ ℕ.+ K
       , ≤-trans (>>=ₚ-boundA k₁ ptX (λ sX → mapₚ verd (Lp {B} T̂ X̂ s (inj₂ tick) sX)) Pb nnPb)
         (≤-trans (cum-mono-Supp k₁ ptX (λ sX → cum k₁ (mapₚ verd (Lp {B} T̂ X̂ s (inj₂ tick) sX)) Pb)
                                        (λ sX → cum J (mapₚ verd (Oᴰ X̂ sX)) Pb) sp)
         (≤-trans (>>=ₚ-boundB k₁ J ptX (λ sX → mapₚ verd (Oᴰ X̂ sX)) Pb nnPb)
         (≤-trans le₁
         (≤-trans le₂
                  (+-monoˡ-≤ ε
                    (≤-trans le₃
                    (≤-trans (>>=ₚ-boundA j₃ ptY (λ sY → mapₚ verd (Oᴰ Ŷ sY)) Pb nnPb)
                    (≤-trans (cum-mono-Supp j₃ ptY (λ sY → cum j₃ (mapₚ verd (Oᴰ Ŷ sY)) Pb)
                                                   (λ sY → cum K (mapₚ verd (Lp {B} T̂ Ŷ s (inj₂ tick) sY)) Pb) sq)
                             (>>=ₚ-boundB j₃ K ptY (λ sY → mapₚ verd (Lp {B} T̂ Ŷ s (inj₂ tick) sY)) Pb nnPb)))))))))
      where
      Dₛ : Protocol B Ωᴵ
      Dₛ = trunc {B} T̂ k₁ k₁ s

      wX : W {unitᴵ} {B} X̂
      wX = proj₁ (proj₂ (proj₂ X))

      ptX : Dₚ (MC.St X̂)
      ptX = MC.point (MC.state X̂) ttᵛ

      ptY : Dₚ (MC.St Ŷ)
      ptY = MC.point (MC.state Ŷ) ttᵛ

      Oᴰ : (M : Proc (flat unitᴵ) (flat B)) → MC.St M → Dₚ _
      Oᴰ M = orun e⁺ e⁻ (toProtocol ⦃ Ch-dec B ⦄ Dₛ) M (compiled (treeT {B} T̂ tt k₁ k₁ s (inj₂ tick)))

      step-below : (sX : MC.St X̂) → W.I wX sX idle
                 → Σ[ j ∈ ℕ ] cum k₁ (mapₚ verd (Lp {B} T̂ X̂ s (inj₂ tick) sX)) Pb ℚ.≤ cum j (mapₚ verd (Oᴰ X̂ sX)) Pb
      step-below sX i =
        let j , h = loop-below {B} T̂ X̂ Dₛ tt k₁ Pb nnPb wX k₁ k₁ ℕP.≤-refl ℕP.≤-refl s (inj₂ tick) sX i
        in suc j , ≤-trans (mapₚ-≤ k₁ verd _ Pb nnPb) (≤-trans h (≤-reflexive (sym (mapₚ-cum j verd _ Pb))))

      tree-step : (j : ℕ) (sY : MC.St Ŷ)
                → Σ[ k ∈ ℕ ] cum j (mapₚ verd (Oᴰ Ŷ sY)) Pb ℚ.≤ cum k (mapₚ verd (Lp {B} T̂ Ŷ s (inj₂ tick) sY)) Pb
      tree-step j sY =
        let k , h = tree-below {B} T̂ Ŷ Dₛ tt k₁ Pb nnPb k₁ s (inj₂ tick) sY j
        in suc k , ≤-trans (mapₚ-≤ j verd _ Pb nnPb) (≤-trans h (≤-reflexive (sym (mapₚ-cum k verd _ Pb))))

  tests≼ : Dom (indᵇ b) ε (Obsᵂ (T 𝒲ᵂ.∘ X)) (Obsᵂ (T 𝒲ᵂ.∘ Y))
  tests≼ k =
    let k₁ , le₁ = proj₁ (obs-comp T X) Pb nnPb k
        K  , sp  = uniformize (λ s K → cum k₁ (Z X̂ s) Pb ℚ.≤ cum K (Z Ŷ s) Pb ℚ.+ ε)
                              (λ s le h → ≤-trans h (+-monoˡ-≤ ε (cum-mono le (Z Ŷ s) Pb nnPb)))
                              (per-state k₁) k₁ ptT
        k₂ , le₂ = proj₂ (obs-comp T Y) Pb nnPb (k₁ ℕ.+ K)
    in k₂
     , ≤-trans le₁
       (≤-trans (>>=ₚ-boundA k₁ ptT (Z X̂) Pb nnPb)
       (≤-trans (cum-mono-Supp k₁ ptT (λ s → cum k₁ (Z X̂ s) Pb) (λ s → cum K (Z Ŷ s) Pb ℚ.+ ε) sp)
       (≤-trans (≤-reflexive (cum-add k₁ ptT (λ s → cum K (Z Ŷ s) Pb) (λ _ → ε)))
       (≤-trans (+-monoʳ-≤ (cum k₁ ptT (λ s → cum K (Z Ŷ s) Pb)) (cum-const-≤ k₁ ptT (<⇒≤ pos)))
                (+-monoˡ-≤ ε (≤-trans (>>=ₚ-boundB k₁ K ptT (Z Ŷ) Pb nnPb) le₂))))))

tests-dense : (T : B 𝒲ᵂ.⇒ Ωᴵ) {X Y : unitᴵ 𝒲ᵂ.⇒ B}
            → ((D : Protocol B Ωᴵ) (ε : ℚ) → 0ℚ ℚ.< ε → Obsᵂ (⟦ D ⟧ᵂ 𝒲ᵂ.∘ X) ≈ₚ[ ε ] Obsᵂ (⟦ D ⟧ᵂ 𝒲ᵂ.∘ Y))
            → (ε : ℚ) → 0ℚ ℚ.< ε → Obsᵂ (T 𝒲ᵂ.∘ X) ≈ₚ[ ε ] Obsᵂ (T 𝒲ᵂ.∘ Y)
tests-dense T {X} {Y} agree ε pos =
  (λ b → tests≼ T {X} {Y} agree ε pos b) , (λ b → tests≼ T {Y} {X} (λ D δ p → ≈ₚ[]-sym (agree D δ p)) ε pos b)

------------------------------------------------------------------------
-- The transfer

private
  obsᵂ-resp : (t u : unitᴵ 𝒲ᵂ.⇒ Ωᴵ) → proj₁ t G.≈ proj₁ u → Obsᵂ t ≈ₚ Obsᵂ u
  obsᵂ-resp _ _ e = obs-resp (refl⟩∘⟨ (e ⟩∘⟨refl))
    where open G.HomReasoning

preserves-≈ℰ : Transfer.Preserves-≈ℰ SSP→PM[wb]
preserves-≈ℰ {A} {B} {f} {g} e = KE.mk∼ λ {T} m ε pos →
  ≈ₚ[]-resp (obsᵂ-resp (T 𝒲ᵂ.∘ (⟦ f ⟧ᵂ 𝒲ᵂ.∘ m)) ((T 𝒲ᵂ.∘ ⟦ f ⟧ᵂ) 𝒲ᵂ.∘ m) G.sym-assoc)
            (obsᵂ-resp (T 𝒲ᵂ.∘ (⟦ g ⟧ᵂ 𝒲ᵂ.∘ m)) ((T 𝒲ᵂ.∘ ⟦ g ⟧ᵂ) 𝒲ᵂ.∘ m) G.sym-assoc)
    (tests-dense T {⟦ f ⟧ᵂ 𝒲ᵂ.∘ m} {⟦ g ⟧ᵂ 𝒲ᵂ.∘ m} (λ D δ p →
      ≈ₚ[]-resp (obsᵂ-resp (⟦ D ∘ᵖ f ⟧ᵂ 𝒲ᵂ.∘ m) (⟦ D ⟧ᵂ 𝒲ᵂ.∘ (⟦ f ⟧ᵂ 𝒲ᵂ.∘ m)) (assoc⟦⟧ D f m))
                (obsᵂ-resp (⟦ D ∘ᵖ g ⟧ᵂ 𝒲ᵂ.∘ m) (⟦ D ⟧ᵂ 𝒲ᵂ.∘ (⟦ g ⟧ᵂ 𝒲ᵂ.∘ m)) (assoc⟦⟧ D g m))
                (games-dense (SSP.KE.run∼ e {D}) m δ p)) ε pos)
  where
  open G.HomReasoning
  assoc⟦⟧ : (D : Protocol B Ωᴵ) (h : Protocol A B) (m : unitᴵ 𝒲ᵂ.⇒ A)
          → proj₁ (⟦ D ∘ᵖ h ⟧ᵂ 𝒲ᵂ.∘ m) G.≈ proj₁ (⟦ D ⟧ᵂ 𝒲ᵂ.∘ (⟦ h ⟧ᵂ 𝒲ᵂ.∘ m))
  assoc⟦⟧ D h m = (⟦⟧ᵂ-∘ D h ⟩∘⟨refl) ○ G.assoc

-- `P ≤UC Q ⇒ Fᵂ P ≤UC Fᵂ Q`.
preserves-≤UC : Transfer.Preserves-≤UC SSP→PM[wb]
preserves-≤UC = ≤UC-transfer preserves-≈ℰ
