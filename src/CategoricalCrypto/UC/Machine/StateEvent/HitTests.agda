{-# OPTIONS --safe --without-K --guardedness #-}

-- The distinguishing cases of the state-event reading, through its public
-- entry points (`stateRead-hit`, `stateBounded⇒hit`): each value is the
-- eventual finite approximant of `stateRead` at an embedded strategy.  The
-- last section pins test annotations along simulations (`EventSim`), among
-- them the no-descent counterexample `ghost-no-descent`.

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.EventBounds.Transport
open import CategoricalCrypto.UC.Machine.Monitor.Agree
open import CategoricalCrypto.UC.Machine.StateEvent
open import CategoricalCrypto.UC.Machine.StateEvent.Adequacy
open import CategoricalCrypto.UC.Machine.StateEvent.Read

module CategoricalCrypto.UC.Machine.StateEvent.HitTests where

Go : Iface
Go = Bool ⇿ ⊤

-- The reading of the test `T` at `d` eventually equals `v`.
Reads : (P : Protocol unitᴵ Go) → (MSt P → Bool) → Strat ⊤ Bool → ℚ → Set
Reads P T d v =
  Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n ℕ.+ i) (stateRead unitᴵ (morphism P) T (stratTest Go d) m₀) (indᵇ true) ≡ v)

private
  reads : (P : Protocol unitᴵ Go) (Bad : St P → Bool) (d : Strat ⊤ Bool) {v : ℚ}
        → PrHit P Bad d ≡ v → Reads P (idleTest P Bad) d v
  reads P Bad d eq = let n , h = stateRead-hit P Bad (idleTest P Bad) (λ _ → refl) d
                     in n , λ i → trans (h i) eq

  ask₁ ask₂ : Strat ⊤ Bool
  ask₁ = ask tt λ _ → out false
  ask₂ = ask tt λ _ → ask₁

------------------------------------------------------------------------
-- Initially bad, and a strategy that finishes at once

initBad : Protocol unitᴵ Go
initBad = record { St = Bool ; init = true ; step = λ s _ → ret (s , true) }

initially-bad : Reads initBad (idleTest initBad id) (out false) 1ℚ
initially-bad = reads initBad id (out false) refl

-- …so no bound below 1 holds even at cap 0: the zero-query experiment is
-- admitted, and it reads the initial state.
initially-bad-cap₀ : {r : ℚ} → StateBoundedAt 0 r (morphism initBad) (idleTest initBad id) → 1ℚ ℚ.≤ r
initially-bad-cap₀ h = stateBounded⇒hit initBad id _ (λ _ → refl) 0 h (out false) tt

------------------------------------------------------------------------
-- Badness after one completed activation

becomesBad : Protocol unitᴵ Go
becomesBad = record { St = Bool ; init = false ; step = λ _ _ → ret (true , true) }

bad-after-one : Reads becomesBad (idleTest becomesBad id) ask₁ 1ℚ
bad-after-one = reads becomesBad id ask₁ refl

good-before : Reads becomesBad (idleTest becomesBad id) (out false) 0ℚ
good-before = reads becomesBad id (out false) refl

------------------------------------------------------------------------
-- A suspended compiler state satisfying the test is not an activation boundary

onWait : MSt becomesBad → Bool
onWait (idle s) = s
onWait (wait _) = true

wait-irrelevant : Reads becomesBad onWait (out false) 0ℚ
wait-irrelevant = stateRead-hit becomesBad id onWait (λ _ → refl) (out false)

------------------------------------------------------------------------
-- A bad activation, then a deadlocked one: completed-run, not prefix, hits

badThenDead : Protocol unitᴵ Go
badThenDead = record
  { St = Bool ; init = false ; step = λ where false _ → ret (true , true) ; true _ → dead }

hit-then-deadlock : Reads badThenDead (idleTest badThenDead id) ask₂ 0ℚ
hit-then-deadlock = reads badThenDead id ask₂ refl

-- …although the prefix that stops after the bad activation reads the hit.
hit-prefix : Reads badThenDead (idleTest badThenDead id) ask₁ 1ℚ
hit-prefix = reads badThenDead id ask₁ refl

------------------------------------------------------------------------
-- Adaptive and randomized experiments

-- Each activation flips a fair coin, answers it, and turns bad on `true`.
flips : Protocol unitᴵ Go
flips = record { St = Bool ; init = false ; step = λ s _ → coin uniform-Bool λ b → ret (s ∨ b , b) }

-- Ask again only after a `false`.
adaptive : Strat ⊤ Bool
adaptive = ask tt λ where true → out false ; false → ask₁

adaptive-reads : Reads flips (idleTest flips id) adaptive (½ ℚ.+ ½ ℚ.* ½)
adaptive-reads = reads flips id adaptive refl

-- A branch of weight zero still counts against the syntactic ask bound.
zero-branch : Strat ⊤ Bool
zero-branch = coin (return-ℚ true) λ where true → ask₁ ; false → ask₂

zero-branch-counts : ¬ asks≤ 1 zero-branch
zero-branch-counts h = h false true

zero-branch-reads : Reads flips (idleTest flips id) zero-branch ½
zero-branch-reads = reads flips id zero-branch refl

------------------------------------------------------------------------
-- Annotations along simulations

module _ {A B : Iface} where

  -- A simulation carries a test back by inverse image, compatibly.
  rename : {M N : Proc A B} (σ : M S.≲ N) (Q : StateTest N) → EventSim (M , pullTest σ Q) (N , Q)
  rename σ Q = record { sim = σ ; compat = λ _ → refl }

  -- An unused state component, carried along untouched.
  padᴹ : (T : Set) → T → Proc A B → Proc A B
  padᴹ T t M = MC.mk (record { obj = MC.St M × T ; point = λ x → mapₚ (_, t) (MC.point (MC.state M) x) })
                     λ p → mapₚ (λ r → (proj₁ r , proj₂ (proj₁ p)) , proj₂ r) (MC.step M (proj₁ (proj₁ p) , proj₂ p))

  -- …preserves every test pulled back from the original state.
  unused : (T : Set) (t : T) (M : Proc A B) (Q : StateTest M) → EventSim (padᴹ T t M , Q ∘ proj₁) (M , Q)
  unused T t M Q = record
    { sim    = simFn proj₁ (λ x → bind-map (MC.point (MC.state M) x) _ _ ⟨≈⟩ >>=ₚ-identityʳ _)
                     λ ((s , _) , x) → bind-map (MC.step M (s , x)) _ _ ⟨≈⟩ >>=ₚ-identityʳ _
    ; compat = λ _ → refl
    }

-- A ghost bit: flipped at every activation, never observed.  Erasing it is a
-- simulation, and the two states it identifies disagree on the bit.
ghost : Proc unitᴵ Ωᴵ
ghost = MC.mk (initˢ Bool false) λ where
  (_ , inj₁ ())
  (b , inj₂ _) → returnₚ (not b , inj₂ true)

erased : Proc unitᴵ Ωᴵ
erased = MC.mk (initˢ ⊤ tt) λ where
  (_ , inj₁ ())
  (_ , inj₂ _) → returnₚ (tt , inj₂ true)

erase : ghost S.≲ erased
erase = simFn (λ _ → tt) (λ _ → >>=ₚ-identityˡ false _) λ where
  (_ , inj₁ ())
  (b , inj₂ _) → >>=ₚ-identityˡ (not b , inj₂ true) _

ghost-no-descent : ¬ (Σ[ Q ∈ StateTest erased ] EventSim (ghost , λ b → b) (erased , Q))
ghost-no-descent (Q , e) = case trans (compat e true) (sym (compat e false)) of λ ()

-- …while a test that ignores the bit descends, and its bounds transport back.
erase-transport : {q : ℕ} {r : ℚ} → StateBoundedAt q r erased (λ _ → false) → StateBoundedAt q r ghost (λ _ → false)
erase-transport = transportᵉ (record { sim = erase ; compat = λ _ → refl })

pullTest-id : {A B : Iface} {M : Proc A B} (Q : StateTest M) (s : MC.St M) → pullTest (S.≲-refl {f = M}) Q s ≡ Q s
pullTest-id Q s = refl

pullTest-∘ : {A B : Iface} {M N L : Proc A B} (σ : M S.≲ N) (τ : N S.≲ L) (Q : StateTest L) (s : MC.St M)
           → pullTest (S.≲-trans σ τ) Q s ≡ pullTest σ (pullTest τ Q) s
pullTest-∘ σ τ Q s = refl
