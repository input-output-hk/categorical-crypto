{-# OPTIONS --safe --without-K #-}

-- Local selection is deterministic and owned; randomness changes persistent
-- state, not the selected action. Boundary delivery has its own activation.
module CategoricalCrypto.TaskPIOA.NativeSSP.Core where

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (_∘_; id)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Coins
open import CategoricalCrypto.SSP.Dist.Kernel using (Coins; done; toss; sample; coins; _>>=ᶜ_)
open import CategoricalCrypto.SSP.Dist.Sampling
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation using (evalC; evalC-cong)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core using
  (Finite; ⟨_⟩; Signature; Input; Output; Local; Task; taskOf; Schedule; emit; prepend; inputs; tasks; _⊕_)
import CategoricalCrypto.TaskPIOA.Core as Source
open import CategoricalCrypto.TaskPIOA.SSPAdapter using (finite-dec)
open import CategoricalCrypto.TaskPIOA.Simulation
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Product

record Machine (S : Signature) : Set where
  field memory : Finite
        start : ⟨ memory ⟩
        deliver : Input S → ⟨ memory ⟩ → Coins ⟨ memory ⟩
        select : ⟨ memory ⟩ → Task S → Maybe (Local S)
        owned : ∀ q t a → select q t ≡ just a → taskOf S a ≡ t
        transition : Local S → ⟨ memory ⟩ → Coins ⟨ memory ⟩
open Machine public

State : ∀ {S} → Machine S → Set
State M = ⟨ memory M ⟩

activate : ∀ {S} (M : Machine S) → State M → Maybe (Local S) → Coins (Maybe (Output S) × State M)
activate M q nothing = done (nothing , q)
activate {S} M q (just a) = mapCoins (emit {S} a ,_) (transition M a q)

tick : ∀ {S} (M : Machine S) → Task S → State M → Coins (Maybe (Output S) × State M)
tick M t q = activate M q (select M q t)

receive : ∀ {S} (M : Machine S) → Maybe (Input S) → State M → Coins (State M)
receive M nothing q = done q
receive M (just i) q = deliver M i q

Boundary : Signature → Iface
Boundary S = record
  { Ch = Input S ⊎ Task S ; Q = λ _ → ⊤ ; R = λ _ → Maybe (Output S)
  ; Ch-dec = finite-dec (inputs S ⊕ tasks S) }

protocol : ∀ {S} (M : Machine S) → P.Protocol unitᴵ (Boundary S)
protocol M = record
  { St = State M ; init = start M
  ; step = λ where
      q (inj₁ i) _ → coins (mapCoins (_, nothing) (deliver M i q))
      q (inj₂ t) _ → coins (mapCoins swap (tick M t q)) }

run : ∀ {S} (M : Machine S) → Schedule S → State M → Coins (List (Output S))
run M [] q = done []
run M (t ∷ ρ) q = tick M t q >>=ᶜᵒ λ (o , q′) → mapCoins (prepend o) (run M ρ q′)

trace : ∀ {S} (M : Machine S) → Schedule S → Dist-ℚ (List (Output S))
trace M ρ = sample (run M ρ (start M))

compile : ∀ {S} → Source.Automaton S → Machine S
compile M = record
  { memory = Source.states M ; start = Source.initial M
  ; deliver = λ i q → rationalCoins (Source.input M i q)
  ; select = Source.choose M ; owned = Source.owns M
  ; transition = λ a q → rationalCoins (Source.kernel M a q) }

sampleMachine : ∀ {S} → Machine S → Source.Automaton S
sampleMachine M = record
  { states = memory M ; initial = start M
  ; input = λ i q → sample (deliver M i q)
  ; choose = select M ; owns = owned M
  ; kernel = λ a q → sample (transition M a q) }

compile-simulation : ∀ {S} (M : Source.Automaton S) → Simulation (sampleMachine (compile M)) M
compile-simulation M = record
  { stateMap = id ; starts = refl ; choices = λ _ _ → refl
  ; inputs-match = λ i q P → trans (Dmap-id (sample (rationalCoins (Source.input M i q))) P)
      (rationalCoins-correct (Source.input M i q) P)
  ; local-match = λ a q P → trans (Dmap-id (sample (rationalCoins (Source.kernel M a q))) P)
      (rationalCoins-correct (Source.kernel M a q) P) }

sample-compile-simulation : ∀ {S} (M : Source.Automaton S) → Simulation M (sampleMachine (compile M))
sample-compile-simulation M = record
  { stateMap = id ; starts = refl ; choices = λ _ _ → refl
  ; inputs-match = λ i q P → trans (Dmap-id (Source.input M i q) P)
      (sym (rationalCoins-correct (Source.input M i q) P))
  ; local-match = λ a q P → trans (Dmap-id (Source.kernel M a q) P)
      (sym (rationalCoins-correct (Source.kernel M a q) P)) }

activation-sample : ∀ {S} (M : Machine S) q a
  → sample (activate M q a) ≈Mℚ Source.step (sampleMachine M) q a
activation-sample M q nothing P = refl
activation-sample {S} M q (just a) = sample-map (emit {S} a ,_) (transition M a q)

run-sample : ∀ {S} (M : Machine S) ρ q
  → sample (run M ρ q) ≈Mℚ Source.runFrom (sampleMachine M) ρ q
run-sample M [] q P = refl
run-sample M (t ∷ ρ) q P = trans
  (sample-bind (tick M t q) (λ (o , q′) → mapCoins (prepend o) (run M ρ q′)) P)
  (>>=ᴹ-cong {μ = sample (tick M t q)} {ν = Source.tick (sampleMachine M) t q}
    {f = λ (o , q′) → sample (mapCoins (prepend o) (run M ρ q′))}
    {g = λ (o , q′) → Dmap (prepend o) (Source.runFrom (sampleMachine M) ρ q′)}
    (activation-sample M q (select M q t))
    (λ (o , q′) R → trans (sample-map (prepend o) (run M ρ q′) R)
      (map-cong (prepend o) (sample (run M ρ q′)) (Source.runFrom (sampleMachine M) ρ q′)
        (run-sample M ρ q′) R)) P)

trace-sample : ∀ {S} (M : Machine S) ρ → trace M ρ ≈Mℚ Source.traceDist (sampleMachine M) ρ
trace-sample M ρ = run-sample M ρ (start M)

compile-trace : ∀ {S} (M : Source.Automaton S) ρ → trace (compile M) ρ ≈Mℚ Source.traceDist M ρ
compile-trace M ρ P = trans (trace-sample (compile M) ρ P) (trace-match (compile-simulation M) ρ P)

protocol-input : ∀ {S} (M : Machine S) i q
  → evalC (P.step (protocol M) q (inj₁ i) tt)
    ≈Mℚ Dmap just (Dmap (_, nothing) (sample (deliver M i q)))
protocol-input M i q P = trans (eval-coins (mapCoins (_, nothing) (deliver M i q)) P)
  (map-cong just (sample (mapCoins (_, nothing) (deliver M i q)))
    (Dmap (_, nothing) (sample (deliver M i q))) (sample-map (_, nothing) (deliver M i q)) P)

protocol-tick : ∀ {S} (M : Machine S) t q
  → evalC (P.step (protocol M) q (inj₂ t) tt)
    ≈Mℚ Dmap just (Dmap swap (sample (tick M t q)))
protocol-tick M t q P = trans (eval-coins (mapCoins swap (tick M t q)) P)
  (map-cong just (sample (mapCoins swap (tick M t q)))
    (Dmap swap (sample (tick M t q))) (sample-map swap (tick M t q)) P)

scheduledTree : ∀ {S} (M : Machine S) → Schedule S → State M → P.Calls unitᴵ (List (Output S))
scheduledTree M [] q = P.ret []
scheduledTree M (t ∷ ρ) q = P.step (protocol M) q (inj₂ t) tt >>=ᶜ λ (q′ , o) →
  P.mapᶜ (prepend o) (scheduledTree M ρ q′)

run-calls : ∀ {S} (M : Machine S) ρ q
  → coins (run M ρ q) P.≈ᶜ scheduledTree M ρ q
run-calls M [] q = P.ret refl
run-calls M (t ∷ ρ) q = P.≈ᶜ-trans
  (coins-bind-through (tick M t q) (λ (o , q′) → mapCoins (prepend o) (run M ρ q′))
    (λ (o , q′) → P.mapᶜ (prepend o) (scheduledTree M ρ q′))
    (λ (o , q′) → P.≈ᶜ-trans (P.≈ᶜ-sym (map-coins (prepend o) (run M ρ q′)))
      (P.mapᶜ-cong (prepend o) (run-calls M ρ q′))))
  (P.≈ᶜ-sym (coins-map-bind swap (tick M t q)
    (λ (q′ , o) → P.mapᶜ (prepend o) (scheduledTree M ρ q′))))

execution : ∀ {S} (M : Machine S) → Schedule S → P.Calls unitᴵ (List (Output S))
execution M ρ = scheduledTree M ρ (start M)

execution-trace : ∀ {S} (M : Machine S) ρ → evalC (execution M ρ) ≈Mℚ Dmap just (trace M ρ)
execution-trace M ρ P = trans (evalC-cong (P.≈ᶜ-sym (run-calls M ρ (start M))) P)
  (eval-coins (run M ρ (start M)) P)

compile-execution : ∀ {S} (M : Source.Automaton S) ρ
  → evalC (execution (compile M) ρ) ≈Mℚ Dmap just (Source.traceDist M ρ)
compile-execution M ρ P = trans (execution-trace (compile M) ρ P)
  (map-cong just (trace (compile M) ρ) (Source.traceDist M ρ) (compile-trace M ρ) P)
