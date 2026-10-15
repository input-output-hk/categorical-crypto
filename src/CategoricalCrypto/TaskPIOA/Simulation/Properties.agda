{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.Simulation.Properties where

open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Simulation
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Product

compose-simulation : ∀ {S} {L M N : Automaton S}
  → Simulation M N → Simulation L M → Simulation L N
compose-simulation {L = L} {M} {N} r s = record
  { stateMap = stateMap r ∘ stateMap s
  ; starts = trans (cong (stateMap r) (starts s)) (starts r)
  ; choices = λ q t → trans (choices s q t) (choices r (stateMap s q) t)
  ; inputs-match = λ i q P → trans (Dmap-∘ (stateMap s) (stateMap r) (input L i q) P)
      (trans (map-cong (stateMap r) (Dmap (stateMap s) (input L i q)) (input M i (stateMap s q))
        (inputs-match s i q) P) (inputs-match r i (stateMap s q) P))
  ; local-match = λ a q P → trans (Dmap-∘ (stateMap s) (stateMap r) (kernel L a q) P)
      (trans (map-cong (stateMap r) (Dmap (stateMap s) (kernel L a q)) (kernel M a (stateMap s q))
        (local-match s a q) P) (local-match r a (stateMap s q) P)) }
