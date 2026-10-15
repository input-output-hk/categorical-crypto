{-# OPTIONS --safe --without-K --guardedness #-}

-- This algebraic raw extension operator uses the native trace domain: tick
-- may occur only last. It is not a characterization of standard FD healthiness
-- or the pinned native FD preorder, and asserts no hiding theorem.
module CategoricalCrypto.CSP.FloodedObservation (E B R : Set) where

open import Data.Empty
open import Data.List.Base
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product.Base hiding (map)
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.CSP.Process E B R

private variable
  p q : Tree
  xs ys : List Visible
  refusal : Visible → Set

-- In particular, extension closure below is conditional on the WHOLE
-- concatenation being legal; an already completed trace cannot be extended.
data Legal : List Visible → Set where
  empty : Legal []
  event-tail : ∀ {e xs} → Legal xs → Legal (event e ∷ xs)
  tick-last : ∀ {r} → Legal (√ r ∷ [])

stop-executes-empty : Executes stop xs q → xs ≡ []
stop-executes-empty done = refl
stop-executes-empty (silent-step step rest) = ⊥-elim (stop-no-step step)
stop-executes-empty (visible-step step rest) = ⊥-elim (stop-no-step step)

execute-legal : Executes p xs q → Legal xs
execute-legal done = empty
execute-legal (silent-step step rest) = execute-legal rest
execute-legal (visible-step (sRet eq) rest) with stop-executes-empty rest
... | refl = tick-last
execute-legal (visible-step (sVis eq offered) rest) = event-tail (execute-legal rest)

trace-legal : Trace p xs → Legal xs
trace-legal (_ , path) = execute-legal path

DivergenceClosure : (List Visible → Set) → List Visible → Set
DivergenceClosure D xs = Σ (List Visible) λ prefix → Σ (List Visible) λ suffix →
  xs ≡ prefix ++ suffix × D prefix × Legal xs

FloodedDivergence : Tree → List Visible → Set
FloodedDivergence p = DivergenceClosure (Divergence p)

FloodedTrace : Tree → List Visible → Set
FloodedTrace p xs = Trace p xs ⊎ FloodedDivergence p xs

FloodedFailure : Tree → List Visible → (Visible → Set) → Set
FloodedFailure p xs refusal = Failure p xs refusal ⊎ FloodedDivergence p xs

flooded-divergence-legal : FloodedDivergence p xs → Legal xs
flooded-divergence-legal (_ , _ , _ , _ , legal) = legal

flooded-trace-legal : FloodedTrace p xs → Legal xs
flooded-trace-legal (inj₁ trace) = trace-legal trace
flooded-trace-legal (inj₂ d) = flooded-divergence-legal d

flooded-failure-legal : FloodedFailure p xs refusal → Legal xs
flooded-failure-legal (inj₁ (_ , path , _)) = execute-legal path
flooded-failure-legal (inj₂ d) = flooded-divergence-legal d

raw-divergence : Divergence p xs → FloodedDivergence p xs
raw-divergence {xs = xs} d@(_ , path , _) = xs , [] , sym (++-identityʳ xs) , d , execute-legal path

raw-trace : Trace p xs → FloodedTrace p xs
raw-trace = inj₁

raw-failure : Failure p xs refusal → FloodedFailure p xs refusal
raw-failure = inj₁

closure-extend : ∀ {D} → DivergenceClosure D xs → Legal (xs ++ ys) → DivergenceClosure D (xs ++ ys)
closure-extend {ys = ys} (prefix , suffix , eq , d , legal) extended = prefix , suffix ++ ys ,
  trans (cong (_++ ys) eq) (++-assoc prefix suffix ys) , d , extended

-- The domain premise is indispensable, including when xs already ends in tick.
flooded-divergence-extend : FloodedDivergence p xs → Legal (xs ++ ys) → FloodedDivergence p (xs ++ ys)
flooded-divergence-extend = closure-extend

after-divergence-trace : FloodedDivergence p xs → Legal (xs ++ ys) → FloodedTrace p (xs ++ ys)
after-divergence-trace d legal = inj₂ (closure-extend d legal)

after-divergence-failure : FloodedDivergence p xs → Legal (xs ++ ys) → FloodedFailure p (xs ++ ys) refusal
after-divergence-failure d legal = inj₂ (closure-extend d legal)

closure-embed : ∀ {D} → D xs → Legal xs → DivergenceClosure D xs
closure-embed {xs = xs} d legal = xs , [] , sym (++-identityʳ xs) , d , legal

closure-idempotent : ∀ {D} → DivergenceClosure (DivergenceClosure D) xs → DivergenceClosure D xs
closure-idempotent (prefix , suffix , eq , (origin , middle , prefix-eq , d , prefix-legal) , legal) =
  origin , middle ++ suffix ,
  trans eq (trans (cong (_++ suffix) prefix-eq) (++-assoc origin middle suffix)) , d , legal

closure-map : ∀ {D D′} → (∀ xs → D xs → D′ xs) → DivergenceClosure D xs → DivergenceClosure D′ xs
closure-map inclusion (prefix , suffix , eq , d , legal) = prefix , suffix , eq , inclusion prefix d , legal

flooded-divergence-inclusion : (∀ xs → Divergence q xs → Divergence p xs)
  → ∀ xs → FloodedDivergence q xs → FloodedDivergence p xs
flooded-divergence-inclusion inclusion xs = closure-map inclusion

flooded-trace-inclusion : (∀ xs → Trace q xs → Trace p xs)
  → (∀ xs → Divergence q xs → Divergence p xs)
  → ∀ xs → FloodedTrace q xs → FloodedTrace p xs
flooded-trace-inclusion traces divergences xs (inj₁ trace) = inj₁ (traces xs trace)
flooded-trace-inclusion traces divergences xs (inj₂ d) = inj₂ (closure-map divergences d)

flooded-failure-inclusion : (∀ xs refusal → Failure q xs refusal → Failure p xs refusal)
  → (∀ xs → Divergence q xs → Divergence p xs)
  → ∀ xs refusal → FloodedFailure q xs refusal → FloodedFailure p xs refusal
flooded-failure-inclusion failures divergences xs refusal (inj₁ failure) = inj₁ (failures xs refusal failure)
flooded-failure-inclusion failures divergences xs refusal (inj₂ d) = inj₂ (closure-map divergences d)

no-event-after-tick : ∀ {r e xs} → ¬ (Legal (√ r ∷ event e ∷ xs))
no-event-after-tick ()

no-flooding-after-tick : ∀ {p r e xs} → ¬ (FloodedDivergence p (√ r ∷ event e ∷ xs))
no-flooding-after-tick (_ , _ , _ , _ , legal) = no-event-after-tick legal
