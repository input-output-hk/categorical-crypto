{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.ClassTransport (Sort : Set) (Payload : Sort → Set) where

open import Data.Product.Base
open import Data.Sum.Base

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Operational Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload

module Classes {A B : Interface} {F G : Network A B} (iso : F ≅ G) where
  module I = _≅_ iso
  module P = Embedding I.forward
  module Q = Embedding I.backward
  module WF = Wiring F
  module WG = Wiring G
  module EF = Execution F
  module EG = Execution G

  forward-incidence : ∀ {k p n} → WF.Connected (Network.local-wire F (k , p)) n
    → WG.Connected (Network.local-wire G (P.box-map k , cast-port (P.box-label k) p)) (P.name-map n)
  forward-incidence {k} {p} conn = WG.join (WG.reverse (P.local k p)) (P.connected conn)

  backward-incidence : ∀ {k p n} → WG.Connected (Network.local-wire G (k , p)) n
    → WF.Connected (Network.local-wire F (Q.box-map k , cast-port (Q.box-label k) p)) (Q.name-map n)
  backward-incidence {k} {p} conn = WF.join (WF.reverse (Q.local k p)) (Q.connected conn)

  private-forward : ∀ {n} → EF.Private n → EG.Private (P.name-map n)
  private-forward {n} confined e conn = confined e
    (WF.join (WF.reverse (I.names-left n)) (WF.join (Q.connected conn) (Q.external e)))

  private-backward : ∀ {n} → EG.Private n → EF.Private (Q.name-map n)
  private-backward {n} confined e conn = confined e
    (WG.join (WG.reverse (I.names-right n)) (WG.join (P.connected conn) (P.external e)))

  boundary-forward : ∀ {k p e} → WF.Connected (Network.local-wire F (k , p)) (inj₂ e)
    → WG.Connected (Network.local-wire G (P.box-map k , cast-port (P.box-label k) p)) (inj₂ e)
  boundary-forward {e = e} conn = WG.join (forward-incidence conn) (P.external e)

  boundary-backward : ∀ {k p e} → WG.Connected (Network.local-wire G (k , p)) (inj₂ e)
    → WF.Connected (Network.local-wire F (Q.box-map k , cast-port (Q.box-label k) p)) (inj₂ e)
  boundary-backward {e = e} conn = WF.join (backward-incidence conn) (Q.external e)
