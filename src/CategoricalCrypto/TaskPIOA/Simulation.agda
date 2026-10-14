{-# OPTIONS --safe --without-K #-}

-- A state-map/lumping simulation checks one transition at a time. Its map
-- and task translation (identity) are fixed before choosing an environment.
module CategoricalCrypto.TaskPIOA.Simulation where

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product.Base as Pair
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_∘_; id)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Product
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Product

record Simulation {S : Signature} (M N : Automaton S) : Set where
  field stateMap : State M → State N
        starts : stateMap (initial M) ≡ initial N
        choices : ∀ q t → choose M q t ≡ choose N (stateMap q) t
        inputs-match : ∀ i q → Dmap stateMap (input M i q) ≈Mℚ input N i (stateMap q)
        local-match : ∀ a q → Dmap stateMap (kernel M a q) ≈Mℚ kernel N a (stateMap q)
open Simulation public

identity-simulation : ∀ {S} (M : Automaton S) → Simulation M M
identity-simulation M = record
  { stateMap = id ; starts = refl ; choices = λ _ _ → refl
  ; inputs-match = λ i q → Dmap-id (input M i q)
  ; local-match = λ a q → Dmap-id (kernel M a q) }

receive-match : ∀ {S} {M N : Automaton S} (s : Simulation M N) i q
  → Dmap (stateMap s) (receive M i q) ≈Mℚ receive N i (stateMap s q)
receive-match s nothing q = map-return (stateMap s) q
receive-match s (just i) q = inputs-match s i q

module _ {S} {M N : Automaton S} (s : Simulation M N) where
  private h = stateMap s

  step-match : ∀ q a → Dmap (Pair.map id h) (step M q a) ≈Mℚ step N (h q) a
  step-match q nothing = map-return (Pair.map id h) (nothing , q)
  step-match q (just a) P = trans (sym (Dmap-∘ (emit {S} a ,_) (Pair.map id h) (kernel M a q) P))
    (trans (Dmap-∘ h (emit {S} a ,_) (kernel M a q) P)
      (map-cong (emit {S} a ,_) (Dmap h (kernel M a q)) (kernel N a (h q)) (local-match s a q) P))

  tick-match : ∀ q t → Dmap (Pair.map id h) (tick M t q) ≈Mℚ tick N t (h q)
  tick-match q t rewrite sym (choices s q t) = step-match q (choose M q t)

  run-match : ∀ ρ q → runFrom M ρ q ≈Mℚ runFrom N ρ (h q)
  run-match [] q P = refl
  run-match (t ∷ ρ) q = mapped-bind (Pair.map id h) (tick M t q) (tick N t (h q))
    (λ (o , q′) → Dmap (prepend o) (runFrom M ρ q′))
    (λ (o , q′) → Dmap (prepend o) (runFrom N ρ q′))
    (tick-match q t) (λ (o , q′) → map-cong (prepend o) (runFrom M ρ q′) (runFrom N ρ (h q′)) (run-match ρ q′))

  trace-match : ∀ ρ → traceDist M ρ ≈Mℚ traceDist N ρ
  trace-match ρ P = trans (run-match ρ (initial M) P)
    (cong (λ q → lookupᴰℚ (entries (runFrom N ρ q)) P) (starts s))

module _ {A B J} {M M′ : Automaton A} {N N′ : Automaton B}
  (w : Wiring A B J) (s : Simulation M M′) (r : Simulation N N′) where
  private
    h = stateMap s
    k = stateMap r
    joint : ∀ μ ν μ′ ν′ → Dmap h μ ≈Mℚ μ′ → Dmap k ν ≈Mℚ ν′
      → Dmap (Pair.map h k) (independent μ ν) ≈Mℚ independent μ′ ν′
    joint μ ν μ′ ν′ e f P = trans (map-independent h k μ ν P)
      (independent-cong (Dmap h μ) μ′ (Dmap k ν) ν′ e f P)

  product-simulation : Simulation (product w M N) (product w M′ N′)
  product-simulation = record
    { stateMap = Pair.map h k
    ; starts = cong₂ _,_ (starts s) (starts r)
    ; choices = λ where
        (q , v) (inj₁ t) → cong (Maybe.map (leftAction {A} {B})) (choices s q t)
        (q , v) (inj₂ t) → cong (Maybe.map (rightAction {A} {B})) (choices r v t)
    ; inputs-match = λ i (q , v) → joint
        (receive M (find (left w) (inj₁ i)) q) (receive N (find (right w) (inj₁ i)) v)
        (receive M′ (find (left w) (inj₁ i)) (h q)) (receive N′ (find (right w) (inj₁ i)) (k v))
        (receive-match s (find (left w) (inj₁ i)) q) (receive-match r (find (right w) (inj₁ i)) v)
    ; local-match = λ where
        (inj₁ (inj₁ o)) (q , v) → joint
          (kernel M (inj₁ o) q) (receive N (find (right w) (inj₂ o)) v)
          (kernel M′ (inj₁ o) (h q)) (receive N′ (find (right w) (inj₂ o)) (k v))
          (local-match s (inj₁ o) q) (receive-match r (find (right w) (inj₂ o)) v)
        (inj₁ (inj₂ o)) (q , v) → joint
          (receive M (find (left w) (inj₂ o)) q) (kernel N (inj₁ o) v)
          (receive M′ (find (left w) (inj₂ o)) (h q)) (kernel N′ (inj₁ o) (k v))
          (receive-match s (find (left w) (inj₂ o)) q) (local-match r (inj₁ o) v)
        (inj₂ (inj₁ a)) (q , v) → joint
          (kernel M (inj₂ a) q) (return-ℚ v) (kernel M′ (inj₂ a) (h q)) (return-ℚ (k v))
          (local-match s (inj₂ a) q) (map-return k v)
        (inj₂ (inj₂ a)) (q , v) → joint
          (return-ℚ q) (kernel N (inj₂ a) v) (return-ℚ (h q)) (kernel N′ (inj₂ a) (k v))
          (map-return h q) (local-match r (inj₂ a) v)
    }
