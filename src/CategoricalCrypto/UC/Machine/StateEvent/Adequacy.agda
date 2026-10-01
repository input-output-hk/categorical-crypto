{-# OPTIONS --safe --without-K --guardedness #-}

-- `Strat` as an adequacy instance of the state-event reading: at a protocol
-- image, the reading at an embedded strategy is `Protocol.Observe.PrHit`
-- EXACTLY past a depth, and `BoundedHit` at cap `q` is `StateBoundedAt` at cap
-- `q`, in both directions and with no slack.
--
-- The boundary interpretation is any machine test that is the source test on
-- `idle`: a `B`-answer of `morphism P` only ever comes from `drive` returning
-- to `idle`, so a suspended `wait` state is never sampled and its value is
-- irrelevant.  The kernel-level reading (`flagRun`) is generic over any closed
-- machine with a step kernel (`Protocol.Machine.Raw`).

open import Data.Bool.Base
open import Data.Nat.Base as ℕ
open import Data.Nat.Poly
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ)
open import Data.Sum.Base hiding (map₁)
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])

import Data.Nat.Properties as ℕP
import Data.Rational.Properties as ℚP

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Settle

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Machine.Raw
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Machine.Monitor.Agree
open import CategoricalCrypto.UC.Machine.StateEvent
open import CategoricalCrypto.UC.Machine.StateEvent.Agree
open import CategoricalCrypto.UC.Machine.StateEvent.Lift
open import CategoricalCrypto.UC.Machine.StateEvent.Read
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.Quantitative.EventLift

module CategoricalCrypto.UC.Machine.StateEvent.Adequacy where

------------------------------------------------------------------------
-- The completed-run reading, at a closed machine with a step kernel

module _ {B : Iface} (M : Proc unitᴵ B) (K : MC.St M → Neg B → Dist⊥ (MC.St M × Pos B))
         (P : StateTest M) where

  -- `PrHit`'s `hitFrom` over an arbitrary step kernel.
  hitK : Bool → MC.St M → Strat (Neg B) (Pos B) → Dist⊥ Bool
  hitK acc m (out _)    = return⊥ acc
  hitK acc m (ask q k)  = K m q >>=⊥ λ mr → hitK (acc ∨ P (proj₁ mr)) (proj₁ mr) (k (proj₂ mr))
  hitK acc m (coin μ k) = μ >>=ᴹ λ b → hitK acc m (k b)

  private
    bump : Bool → MC.St M × Pos B → (MC.St M × Bool) × (Pos B ⊎ Bool)
    bump f mr = (proj₁ mr , f ∨ P (proj₁ mr)) , inj₁ (proj₂ mr)

    K▷ : MC.St M × Bool → Neg B ⊎ ⊤ → Dist⊥ ((MC.St M × Bool) × (Pos B ⊎ Bool))
    K▷ (m , f) (inj₁ q) = Dmap⊥ (bump f) (K m q)
    K▷ (m , f) (inj₂ _) = return⊥ ((m , f) , inj₂ f)

    resume : (Pos B ⊎ Bool → Strat (Neg B ⊎ ⊤) (Pos B ⊎ Bool)) → (MC.St M × Bool) × (Pos B ⊎ Bool) → Dist⊥ Bool
    resume κ sr = runWith⊥ K▷ (proj₁ sr) (κ (proj₂ sr))

    flag-hit : (m : MC.St M) (acc : Bool) (d : Strat (Neg B) (Pos B)) (G : Bool → ℚ)
             → E⊥ (runWith⊥ K▷ (m , acc) (flagStrat d)) G ≡ E⊥ (hitK acc m d) G
    flag-hit m acc (out _) G =
      trans (E⊥-bind (return⊥ ((m , acc) , inj₂ acc)) (resume [ (λ _ → out false) , out ]) G)
            (E⊥-return ((m , acc) , inj₂ acc) (λ sr → E⊥ (resume [ (λ _ → out false) , out ] sr) G))
    flag-hit m acc (ask q k) G =
      trans (E⊥-map-bind (bump acc) (K m q) cont G)
      (trans (E⊥-bind (K m q) (cont ∘ bump acc) G)
      (trans (E⊥-cong-P (K m q) _ _ λ mr → flag-hit (proj₁ mr) (acc ∨ P (proj₁ mr)) (k (proj₂ mr)) G)
             (sym (E⊥-bind (K m q) (λ mr → hitK (acc ∨ P (proj₁ mr)) (proj₁ mr) (k (proj₂ mr))) G))))
      where
      cont : (MC.St M × Bool) × (Pos B ⊎ Bool) → Dist⊥ Bool
      cont = resume [ flagStrat ∘ k , (λ _ → out false) ]
    flag-hit m acc (coin μ k) G =
      trans (E-bind μ (λ b → runWith⊥ K▷ (m , acc) (flagStrat (k b))) (maybeℚ G))
      (trans (lookupᴰℚ-cong-P (entries μ) λ b → flag-hit m acc (k b) G)
             (sym (E-bind μ (λ b → hitK acc m (k b)) (maybeℚ G))))

  module _ (ker : StepSettles M K) where

    private
      ker▷ : StepSettles (M ▷ P) K▷
      ker▷ (m , f) (inj₁ q) =
        let n , s = Settles-map⋆ (sample M P f) (ker m q)
        in n , Settles-resp _ _
                 (λ G → trans (E⊥-map-bind ansᴹ (K m q) (return⊥ ∘ sample M P f) G)
                        (trans (E⊥-bind (K m q) (return⊥ ∘ sample M P f ∘ ansᴹ) G)
                        (trans (E⊥-cong-P (K m q) (λ p → E⊥ (return⊥ (sample M P f (ansᴹ p))) G)
                                          (λ p → G (ansᴹ (bump f p)))
                                          λ p → E⊥-return (sample M P f (ansᴹ p)) G)
                               (sym (trans (E⊥-map ansᴹ (Dmap⊥ (bump f) (K m q)) G)
                                           (E⊥-map (bump f) (K m q) (λ p → G (ansᴹ p))))))))
                 s
      ker▷ (m , f) (inj₂ _) =
        1 , Settles-resp _ _
              (λ G → trans (E⊥-return ((m , f) , inj₂ (inj₂ f)) G)
                     (sym (trans (E⊥-map ansᴹ (return⊥ ((m , f) , inj₂ f)) G)
                                 (E⊥-return ((m , f) , inj₂ f) (λ p → G (ansᴹ p))))))
              (Settles-return ((m , f) , inj₂ (inj₂ f)))

    -- Past a depth, the flag read at completion is the kernel-level hit, at
    -- either verdict: the initial state is sampled, divergence scores nothing.
    module _ (σ₀ : Dist⊥ (MC.St M)) (n₀ : ℕ)
             (pt : Settles n₀ (MC.point (MC.state M) ttᵛ) σ₀) where

      flagRun : (b : Bool) (d : Strat (Neg B) (Pos B))
              → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n ℕ.+ i) (runᴹ (M ▷ P) (flagStrat d)) (indᵇ b)
                                     ≡ E⊥ (σ₀ >>=⊥ λ m → hitK (P m) m d) (indᵇ b))
      flagRun b d =
        let n₁ , pt▷ = Settles-map⋆ (λ s → s , P s) (n₀ , pt)
            n , h = rawPr (M ▷ P) K▷ ker▷ _ n₁ pt▷ b (flagStrat d)
        in n , λ i → trans (h i)
             (trans (E⊥-bind (σ₀ >>=⊥ λ s → return⊥ (s , P s)) _ (indᵇ b))
             (trans (E⊥-bind σ₀ (λ s → return⊥ (s , P s)) (λ a → E⊥ (runWith⊥ K▷ a (flagStrat d)) (indᵇ b)))
             (trans (E⊥-cong-P σ₀ (λ s → E⊥ (return⊥ (s , P s)) (λ a → E⊥ (runWith⊥ K▷ a (flagStrat d)) (indᵇ b)))
                                  (λ s → E⊥ (hitK (P s) s d) (indᵇ b))
                               λ s → trans (E⊥-return (s , P s) (λ a → E⊥ (runWith⊥ K▷ a (flagStrat d)) (indᵇ b)))
                                           (flag-hit s (P s) d (indᵇ b)))
                    (sym (E⊥-bind σ₀ _ (indᵇ b))))))

------------------------------------------------------------------------
-- …at a protocol image, where it IS `PrHit`

module _ {B : Iface} (P : Protocol unitᴵ B) (Bad : St P → Bool) where

  -- The default boundary interpretation.
  idleTest : StateTest (morphism P)
  idleTest (idle s) = Bad s
  idleTest (wait _) = false

  module _ (T : StateTest (morphism P)) (bd : (s : St P) → T (idle s) ≡ Bad s) where

    private
      hitK-idle : (acc : Bool) (s : St P) (d : Strat (Neg B) (Pos B)) (G : Bool → ℚ)
                → E⊥ (hitK (morphism P) (Kᴾ P) T acc (idle s) d) G ≡ E⊥ (hitFrom P Bad acc s d) G
      hitK-idle acc s (out _) G = refl
      hitK-idle acc s (ask q k) G =
        trans (E⊥-map-bind (map₁ idle) (kernel P s q) κ G)
        (trans (E⊥-bind (kernel P s q) (κ ∘ map₁ idle) G)
        (trans (E⊥-cong-P (kernel P s q) _ _ λ sr →
                  trans (hitK-idle (acc ∨ T (idle (proj₁ sr))) (proj₁ sr) (k (proj₂ sr)) G)
                        (cong (λ a → E⊥ (hitFrom P Bad (acc ∨ a) (proj₁ sr) (k (proj₂ sr))) G)
                              (bd (proj₁ sr))))
               (sym (E⊥-bind (kernel P s q) _ G))))
        where
        κ : MSt P × Pos B → Dist⊥ Bool
        κ mr = hitK (morphism P) (Kᴾ P) T (acc ∨ T (proj₁ mr)) (proj₁ mr) (k (proj₂ mr))
      hitK-idle acc s (coin μ k) G =
        trans (E-bind μ (λ b → hitK (morphism P) (Kᴾ P) T acc (idle s) (k b)) (maybeℚ G))
        (trans (lookupᴰℚ-cong-P (entries μ) λ b → hitK-idle acc s (k b) G)
               (sym (E-bind μ (λ b → hitFrom P Bad acc s (k b)) (maybeℚ G))))

    run-hit : (d : Strat (Neg B) (Pos B))
            → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n ℕ.+ i) (runᴹ (morphism P ▷ T) (flagStrat d)) (indᵇ true)
                                   ≡ PrHit P Bad d)
    run-hit d =
      let n , h = flagRun (morphism P) (Kᴾ P) T (ker P) (return⊥ (idle (init P))) 1 (Settles-return _) true d
      in n , λ i → trans (h i)
           (trans (E⊥-bind (return⊥ (idle (init P))) (λ m → hitK (morphism P) (Kᴾ P) T (T m) m d) (indᵇ true))
           (trans (E⊥-return (idle (init P)) (λ m → E⊥ (hitK (morphism P) (Kᴾ P) T (T m) m d) (indᵇ true)))
           (trans (hitK-idle (T (idle (init P))) (init P) d (indᵇ true))
                  (cong (λ a → E⊥ (hitFrom P Bad a (init P) d) (indᵇ true)) (bd (init P))))))

    stateRead-hit : (d : Strat (Neg B) (Pos B))
                  → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n ℕ.+ i) (stateRead unitᴵ (morphism P) T (stratTest B d) m₀)
                                                    (indᵇ true)
                                         ≡ PrHit P Bad d)
    stateRead-hit d =
      let n , h = run-hit d
      in cum-settled-≈ₚ _ _ (indᵇ true) (indᵇ-nn true) (PrHit P Bad d) n h
                        (≈ₚ-sym _ _ (stateRead-agree (morphism P) T d))

    -- `BoundedHit` at cap `q`, from the model reading at the same cap…
    stateBounded⇒hit : (q : ℕ) {r : ℚ} → StateBoundedAt q r (morphism P) T
                     → (d : Strat (Neg B) (Pos B)) → asks≤ q d → PrHit P Bad d ℚ.≤ r
    stateBounded⇒hit q h d a =
      let n , eq = stateRead-hit d
          up = h unitᴵ (stratTest B d) m₀ (qb-stratTest B d a) (qb-closed m₀) (ℕP.≤-reflexive (scale-unit q))
      in ℚP.≤-trans (ℚP.≤-reflexive (sym (eq 0))) (up (n ℕ.+ 0))

    -- …and lifted to every admitted experiment at the same cap.
    hit⇒stateBounded : (q : ℕ) {r : ℚ}
                     → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → PrHit P Bad d ℚ.≤ r)
                     → StateBoundedAt q r (morphism P) T
    hit⇒stateBounded q h = stateLift (morphism P) T q λ d a k →
      let n , eq = run-hit d
      in ℚP.≤-trans (Pr≤-mono true (runᴹ (morphism P ▷ T) (flagStrat d)) (ℕP.m≤n+m k n))
                    (ℚP.≤-trans (ℚP.≤-reflexive (eq k)) (h d a))

------------------------------------------------------------------------
-- Families

module _ {B : ℕ → Iface} (P : (n : ℕ) → Protocol unitᴵ (B n)) (Bad : (n : ℕ) → St (P n) → Bool) where

  BoundedHitᴺ : (ℕ → ℕ → ℚ) → Set
  BoundedHitᴺ = Saturated λ n q r → (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d → PrHit (P n) (Bad n) d ℚ.≤ r

  module _ (T : (n : ℕ) → StateTest (morphism (P n)))
           (bd : (n : ℕ) (s : St (P n)) → T n (idle s) ≡ Bad n s) where

    boundedHit⇒stateᶠ : (ε : ℕ → ℕ → ℚ) → ((n : ℕ) → BoundedHit (P n) (Bad n) (ε n))
                      → StateBoundedᶠ (λ n → morphism (P n)) T ε
    boundedHit⇒stateᶠ ε h n q = hit⇒stateBounded (P n) (Bad n) (T n) (bd n) q (h n q)

    stateᶠ⇒boundedHit : (ε : ℕ → ℕ → ℚ) → StateBoundedᶠ (λ n → morphism (P n)) T ε
                      → (n : ℕ) → BoundedHit (P n) (Bad n) (ε n)
    stateᶠ⇒boundedHit ε h n q = stateBounded⇒hit (P n) (Bad n) (T n) (bd n) q (h n q)

    hitᴺ⇒stateᴺ : (ε : ℕ → ℕ → ℚ) → BoundedHitᴺ ε → StateBoundedᴺ (λ n → morphism (P n)) T ε
    hitᴺ⇒stateᴺ ε = saturated-map {Y = λ n q r → StateBoundedAt q r (morphism (P n)) (T n)} {ε = ε} λ n q →
      hit⇒stateBounded (P n) (Bad n) (T n) (bd n) q

    stateᴺ⇒hitᴺ : (ε : ℕ → ℕ → ℚ) → StateBoundedᴺ (λ n → morphism (P n)) T ε → BoundedHitᴺ ε
    stateᴺ⇒hitᴺ ε = saturated-map {X = λ n q r → StateBoundedAt q r (morphism (P n)) (T n)} {ε = ε} λ n q →
      stateBounded⇒hit (P n) (Bad n) (T n) (bd n) q
