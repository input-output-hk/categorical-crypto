{-# OPTIONS --safe --without-K --guardedness #-}

-- Quantification is over represented native single-input consumers, not all
-- networks. Mutual refinement gives their actual raw observation equality;
-- a one-way refinement is not equality-based U or UC.
module CategoricalCrypto.CSP.NativeContextRefinement (X B : Set) where

open import Data.Empty
open import Data.List.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
import Relation.Nullary

open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Network ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Observation ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.ObservationRefinement ⊤ (λ _ → X) using (_⊑ᴼ_; mutual-equality)
open import CategoricalCrypto.CSP.Plugging ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.SemanticInvariance ⊤ (λ _ → X) (λ { tt tt → Relation.Nullary.yes refl })
open import CategoricalCrypto.CSP.SingleBox ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Structure ⊤ (λ _ → X)
import CategoricalCrypto.CSP.NativeFamilyObservation as FamilyObservation

module F = FamilyObservation X B
module C = F.C
open C.L
open F.R using (_⊑_; reflexive)

out inp : Interface
out = interface singleton (λ _ → port tt output)
inp = interface singleton (λ _ → port tt input)

consumer : Tree → Network out I
consumer q = record
  { components = boxes singleton (λ _ → record { boundary = inp ; Branch = C.O.Index ; initial = q })
  ; private-shape = empty ; private-sort = λ ()
  ; local-wire = λ { (tt , tt) → inj₂ (inj₁ tt) } ; wire-type = λ { (tt , tt) → refl }
  ; aliases = [] ; alias-type = λ () }

producer : Tree → Network I out
producer = Embed.network out C.O.Index

pol : ⟨ C.shape+ (C.one C.∙ C.one) ⟩ → Polarity
pol (inj₁ tt) = output
pol (inj₂ tt) = input

only-producer : ∀ k → pol k ≡ output → k ≡ inj₁ tt
only-producer (inj₁ tt) eq = refl
only-producer (inj₂ tt) ()

module A = F.Admissible (C.one C.∙ C.one) pol (inj₁ tt) (inj₂ tt) refl only-producer refl (λ ())

module Plugged (p q : Tree) where
  family : C.Family (C.one C.∙ C.one)
  family = [ (λ _ → p) , (λ _ → q) ]′
  module Closed = A.Closed family
  network = consumer q ∘ producer p
  module W = Wiring Closed.network
  module V = Wiring network

  forward-name : W.Name → V.Name
  forward-name (inj₁ tt) = inj₁ (inj₁ (inj₂ tt))
  forward-name (inj₂ (inj₁ ()))
  forward-name (inj₂ (inj₂ ()))

  backward-name : V.Name → W.Name
  backward-name (inj₁ (inj₁ (inj₁ ())))
  backward-name (inj₁ (inj₁ (inj₂ tt))) = inj₁ tt
  backward-name (inj₁ (inj₂ ()))
  backward-name (inj₂ (inj₁ ()))
  backward-name (inj₂ (inj₂ ()))

  forward-connected : ∀ {u v} → W.Connected u v → V.Connected (forward-name u) (forward-name v)
  forward-connected W.same = V.same
  forward-connected (W.alias ())
  forward-connected (W.reverse conn) = V.reverse (forward-connected conn)
  forward-connected (W.join a b) = V.join (forward-connected a) (forward-connected b)

  backward-connected : ∀ {u v} → V.Connected u v → W.Connected (backward-name u) (backward-name v)
  backward-connected V.same = W.same
  backward-connected (V.alias ())
  backward-connected (V.reverse conn) = W.reverse (backward-connected conn)
  backward-connected (V.join a b) = W.join (backward-connected a) (backward-connected b)

  flattening : Closed.network ≅ network
  flattening = record
    { forward = record
      { box-map = λ k → k ; box-label = λ { (inj₁ tt) → refl ; (inj₂ tt) → refl }
      ; name-map = forward-name ; name-type = λ { (inj₁ tt) → refl ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }
      ; connected = forward-connected ; external = λ { (inj₁ ()) ; (inj₂ ()) }
      ; local = λ { (inj₁ tt) tt → V.same ; (inj₂ tt) tt → V.same } }
    ; backward = record
      { box-map = λ k → k ; box-label = λ { (inj₁ tt) → refl ; (inj₂ tt) → refl }
      ; name-map = backward-name
      ; name-type = λ { (inj₁ (inj₁ (inj₁ ()))) ; (inj₁ (inj₁ (inj₂ tt))) → refl ; (inj₁ (inj₂ ())) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }
      ; connected = backward-connected ; external = λ { (inj₁ ()) ; (inj₂ ()) }
      ; local = λ { (inj₁ tt) tt → W.same ; (inj₂ tt) tt → W.same } }
    ; boxes-left = λ _ → refl ; boxes-right = λ _ → refl
    ; names-left = λ { (inj₁ tt) → W.same ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }
    ; names-right = λ { (inj₁ (inj₁ (inj₁ ()))) ; (inj₁ (inj₁ (inj₂ tt))) → V.same ; (inj₁ (inj₂ ())) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) } }

  flattening-observations : observations Closed.network ≈ᴼ observations network
  flattening-observations = observations-respect flattening

context-refinement : ∀ {p p′ q q′} → p ⊑ p′ → q ⊑ q′
  → observations (consumer q ∘ producer p) ⊑ᴼ observations (consumer q′ ∘ producer p′)
context-refinement {p} {p′} {q} {q′} rp rq = record
  { traces = λ xs path → proj₁ (_≈ᴼ_.traces S.flattening-observations xs)
      (_⊑ᴼ_.traces middle xs (proj₂ (_≈ᴼ_.traces T.flattening-observations xs) path))
  ; failures = λ xs refusal failure → proj₁ (_≈ᴼ_.failures S.flattening-observations xs refusal)
      (_⊑ᴼ_.failures middle xs refusal (proj₂ (_≈ᴼ_.failures T.flattening-observations xs refusal) failure))
  ; divergences = λ xs divergence → proj₁ (_≈ᴼ_.divergences S.flattening-observations xs)
      (_⊑ᴼ_.divergences middle xs (proj₂ (_≈ᴼ_.divergences T.flattening-observations xs) divergence)) }
  where
  module S = Plugged p q
  module T = Plugged p′ q′
  middle = A.refinement (λ { (inj₁ tt) → rp ; (inj₂ tt) → rq })

consumer-refinement : ∀ {p p′} → p ⊑ p′ → ∀ q
  → observations (consumer q ∘ producer p) ⊑ᴼ observations (consumer q ∘ producer p′)
consumer-refinement ref q = context-refinement ref reflexive

mutual-context-equality : ∀ {p p′} → p ⊑ p′ → p′ ⊑ p → ∀ q
  → observations (consumer q ∘ producer p) ≈ᴼ observations (consumer q ∘ producer p′)
mutual-context-equality forward backward q = mutual-equality (consumer-refinement forward q) (consumer-refinement backward q)
