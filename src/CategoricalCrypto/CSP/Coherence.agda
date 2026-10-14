{-# OPTIONS --safe --without-K --guardedness #-}

open import Relation.Binary.Definitions using (DecidableEquality)

-- Only code/index paths are made proof-irrelevant. Payload values, functions,
-- process states, and arbitrary internal branch types retain their equality.
module CategoricalCrypto.CSP.Coherence (Sort : Set) (Payload : Sort → Set)
  (_≟Sort_ : DecidableEquality Sort) where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no)

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload

open Interface
open Component
open Decidable⇒UIP _≟Sort_ using () renaming (≡-irrelevant to sort-paths)

payload-coherent : ∀ {s t} (p q : s ≡ t) x → subst Payload p x ≡ subst Payload q x
payload-coherent p q x = cong (λ eq → subst Payload eq x) (sort-paths p q)

payload-compose : ∀ {a b c} (p : a ≡ b) (q : b ≡ c) x
                → subst Payload q (subst Payload p x) ≡ subst Payload (trans p q) x
payload-compose refl refl x = refl

shape-equality : DecidableEquality Shape
shape-equality empty empty = yes refl
shape-equality empty singleton = no (λ ())
shape-equality empty (_ ⊕ _) = no (λ ())
shape-equality singleton empty = no (λ ())
shape-equality singleton singleton = yes refl
shape-equality singleton (_ ⊕ _) = no (λ ())
shape-equality (_ ⊕ _) empty = no (λ ())
shape-equality (_ ⊕ _) singleton = no (λ ())
shape-equality (a ⊕ b) (c ⊕ d) with shape-equality a c | shape-equality b d
... | yes refl | yes refl = yes refl
... | no neq | _ = no (λ { refl → neq refl })
... | yes _ | no neq = no (λ { refl → neq refl })

open Decidable⇒UIP shape-equality using () renaming (≡-irrelevant to shape-paths)

cast-port-subst : ∀ {c d} (eq : c ≡ d) i
  → cast-port eq i ≡ subst ⟨_⟩ (cong (λ c → shape (boundary c)) eq) i
cast-port-subst refl i = refl

cast-port-coherent : ∀ {c d} (p q : c ≡ d) i → cast-port p i ≡ cast-port q i
cast-port-coherent p q i = trans (cast-port-subst p i)
  (trans (cong (λ eq → subst ⟨_⟩ eq i)
    (shape-paths (cong (λ c → shape (boundary c)) p) (cong (λ c → shape (boundary c)) q)))
    (sym (cast-port-subst q i)))
