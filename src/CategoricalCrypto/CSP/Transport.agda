{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Transport (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.Product.Base

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Operational Sort Payload
open import CategoricalCrypto.CSP.Observation Sort Payload

record OperationalTransport {A B : Interface} (F G : Network A B) : Set₁ where
  module F = Execution F
  module G = Execution G
  field
    Related : F.Configuration → G.Configuration → Set
    initial : Related F.initial-configuration G.initial-configuration
    forward : ∀ {p q p′ l} → Related p q → F._─[_]→_ p l p′
            → Σ G.Configuration (λ q′ → G._─[_]→_ q l q′ × Related p′ q′)
    backward : ∀ {p q q′ l} → Related p q → G._─[_]→_ q l q′
             → Σ F.Configuration (λ p′ → F._─[_]→_ p l p′ × Related p′ q′)

module Soundness {A B : Interface} {F G : Network A B} (transport : OperationalTransport F G) where
  open OperationalTransport transport
  module EF = Execution F
  module EG = Execution G
  module OF = Observe F
  module OG = Observe G

  execute-forward : ∀ {p q p′ xs} → Related p q → OF.Executes p xs p′
                  → Σ EG.Configuration (λ q′ → OG.Executes q xs q′ × Related p′ q′)
  execute-forward related OF.done = _ , OG.done , related
  execute-forward related (OF.silent-step step rest) =
    let q′ , matched , related′ = forward related step
        q″ , continuation , final = execute-forward related′ rest
    in q″ , OG.silent-step matched continuation , final
  execute-forward related (OF.visible-step step rest) =
    let q′ , matched , related′ = forward related step
        q″ , continuation , final = execute-forward related′ rest
    in q″ , OG.visible-step matched continuation , final

  execute-backward : ∀ {p q q′ xs} → Related p q → OG.Executes q xs q′
                   → Σ EF.Configuration (λ p′ → OF.Executes p xs p′ × Related p′ q′)
  execute-backward related OG.done = _ , OF.done , related
  execute-backward related (OG.silent-step step rest) =
    let p′ , matched , related′ = backward related step
        p″ , continuation , final = execute-backward related′ rest
    in p″ , OF.silent-step matched continuation , final
  execute-backward related (OG.visible-step step rest) =
    let p′ , matched , related′ = backward related step
        p″ , continuation , final = execute-backward related′ rest
    in p″ , OF.visible-step matched continuation , final

  stable-forward : ∀ {p q} → Related p q → OF.Stable p → OG.Stable q
  stable-forward related (noτ , no√) =
    (λ q′ step → let p′ , matched , _ = backward related step in noτ p′ matched) ,
    (λ q′ step → let p′ , matched , _ = backward related step in no√ p′ matched)

  stable-backward : ∀ {p q} → Related p q → OG.Stable q → OF.Stable p
  stable-backward related (noτ , no√) =
    (λ p′ step → let q′ , matched , _ = forward related step in noτ q′ matched) ,
    (λ p′ step → let q′ , matched , _ = forward related step in no√ q′ matched)

  refusal-forward : ∀ {p q refusal} → Related p q → OF.Refuses p refusal → OG.Refuses q refusal
  refusal-forward related (stable , refuses) = stable-forward related stable ,
    (λ e member q′ step → let p′ , matched , _ = backward related step in refuses e member p′ matched)

  refusal-backward : ∀ {p q refusal} → Related p q → OG.Refuses q refusal → OF.Refuses p refusal
  refusal-backward related (stable , refuses) = stable-backward related stable ,
    (λ e member p′ step → let q′ , matched , _ = forward related step in refuses e member q′ matched)

  divergence-forward : ∀ {p q} → Related p q → EF.Diverges p → EG.Diverges q
  EG.Diverges.next (divergence-forward related d) = proj₁ (forward related (EF.Diverges.step d))
  EG.Diverges.step (divergence-forward related d) = proj₁ (proj₂ (forward related (EF.Diverges.step d)))
  EG.Diverges.rest (divergence-forward related d) = divergence-forward
    (proj₂ (proj₂ (forward related (EF.Diverges.step d)))) (EF.Diverges.rest d)

  divergence-backward : ∀ {p q} → Related p q → EG.Diverges q → EF.Diverges p
  EF.Diverges.next (divergence-backward related d) = proj₁ (backward related (EG.Diverges.step d))
  EF.Diverges.step (divergence-backward related d) = proj₁ (proj₂ (backward related (EG.Diverges.step d)))
  EF.Diverges.rest (divergence-backward related d) = divergence-backward
    (proj₂ (proj₂ (backward related (EG.Diverges.step d)))) (EG.Diverges.rest d)

  trace-forward : ∀ xs → OF.Trace EF.initial-configuration xs → OG.Trace EG.initial-configuration xs
  trace-forward xs (p , path) = let q , target , _ = execute-forward initial path in q , target

  trace-backward : ∀ xs → OG.Trace EG.initial-configuration xs → OF.Trace EF.initial-configuration xs
  trace-backward xs (q , path) = let p , source , _ = execute-backward initial path in p , source

  failure-forward : ∀ xs refusal → OF.Failure EF.initial-configuration xs refusal
                  → OG.Failure EG.initial-configuration xs refusal
  failure-forward xs refusal (p , path , refuses) =
    let q , target , related = execute-forward initial path in q , target , refusal-forward related refuses

  failure-backward : ∀ xs refusal → OG.Failure EG.initial-configuration xs refusal
                   → OF.Failure EF.initial-configuration xs refusal
  failure-backward xs refusal (q , path , refuses) =
    let p , source , related = execute-backward initial path in p , source , refusal-backward related refuses

  silent-divergence-forward : ∀ xs → OF.Divergence EF.initial-configuration xs
                            → OG.Divergence EG.initial-configuration xs
  silent-divergence-forward xs (p , path , d) =
    let q , target , related = execute-forward initial path in q , target , divergence-forward related d

  silent-divergence-backward : ∀ xs → OG.Divergence EG.initial-configuration xs
                             → OF.Divergence EF.initial-configuration xs
  silent-divergence-backward xs (q , path , d) =
    let p , source , related = execute-backward initial path in p , source , divergence-backward related d
