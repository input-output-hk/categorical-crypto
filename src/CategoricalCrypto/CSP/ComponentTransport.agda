{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.ComponentTransport (Sort : Set) (Payload : Sort → Set) where

open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
import CategoricalCrypto.CSP.Process as P

open Component
open Interface
open Port

TreeOf : Component → Set
TreeOf c = P.Tree (Event (boundary c)) (Branch c) ⊤

module Native (c : Component) = P (Event (boundary c)) (Branch c) ⊤

cast-tree : ∀ {c d} → c ≡ d → TreeOf c → TreeOf d
cast-tree refl p = p

cast-tree-compose : ∀ {a b c} (p : a ≡ b) (q : b ≡ c) t
                  → cast-tree (trans p q) t ≡ cast-tree q (cast-tree p t)
cast-tree-compose refl refl t = refl

cast-tree-inverse : ∀ {c d} (eq : c ≡ d) t → cast-tree (sym eq) (cast-tree eq t) ≡ t
cast-tree-inverse refl t = refl

cast-tree-inverse′ : ∀ {c d} (eq : c ≡ d) t → cast-tree eq (cast-tree (sym eq) t) ≡ t
cast-tree-inverse′ refl t = refl

cast-initial : ∀ {c d} (eq : c ≡ d) → cast-tree eq (initial c) ≡ initial d
cast-initial refl = refl

port-sort : ∀ {c d} (eq : c ≡ d) i
           → sort (ports (boundary c) i) ≡ sort (ports (boundary d) (cast-port eq i))
port-sort refl i = refl

port-polarity : ∀ {c d} (eq : c ≡ d) i
               → polarity (ports (boundary c) i) ≡ polarity (ports (boundary d) (cast-port eq i))
port-polarity refl i = refl

cast-event : ∀ {c d} → c ≡ d → Event (boundary c) → Event (boundary d)
cast-event refl e = e

cast-event-payload : ∀ {c d} (eq : c ≡ d) i x
  → cast-event eq (i , x) ≡ (cast-port eq i , subst Payload (port-sort eq i) x)
cast-event-payload refl i x = refl

cast-offer : ∀ {c d p q i x} (eq : c ≡ d)
  → Native._─[_]→_ c p (Native.visible {c = c} (Native.event {c = c} (i , x))) q
  → Native._─[_]→_ d (cast-tree eq p)
      (Native.visible {c = d} (Native.event {c = d} (cast-port eq i , subst Payload (port-sort eq i) x))) (cast-tree eq q)
cast-offer refl step = step

cast-silent : ∀ {c d p q} (eq : c ≡ d)
  → Native._─[_]→_ c p (Native.τ {c = c}) q → Native._─[_]→_ d (cast-tree eq p) (Native.τ {c = d}) (cast-tree eq q)
cast-silent refl step = step

cast-ret : ∀ {c d p} (eq : c ≡ d)
  → Native.Tree.force {c = c} p ≡ Native.ret {c = c} tt
  → Native.Tree.force {c = d} (cast-tree eq p) ≡ Native.ret {c = d} tt
cast-ret refl eq = eq

indexed-cast : ∀ {K : Boxes} (q : (k : ⟨ Boxes.shape K ⟩) → TreeOf (Boxes.label K k))
              {i j} (eq : i ≡ j) → cast-tree (cong (Boxes.label K) eq) (q i) ≡ q j
indexed-cast q refl = refl
