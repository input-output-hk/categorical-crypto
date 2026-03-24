{-# OPTIONS --safe #-}

module CategoricalCrypto.Examples.Basic where

open import categorical-crypto.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)
import categorical-crypto.Prelude as P

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core

--------------------------------------------------------------------------------
-- Example functionalities

module TemplateChannel (M : Type) {M' : Type} (f : M → M') where

  open Channel

  A B E : Channel

  -- can receive messages from Alice
  A = ⊥ ⇿ M

  -- can send messages to Bob
  B = M ⇿ ⊥

  -- upon request, can send next message to Eve
  E = M' ⇿ ⊤

  open Machine

  data WithState_receive_return_newState_ : MachineType I ((A ⊗ B) ⊗ E) (List M) where

    Send : ∀ {m s} → WithState s
                     receive L⊗ ((ϵ ᵗ¹ ⊗R) ⊗R) ᵗ¹ ↑ᵢ m
                     return just $ L⊗ ((L⊗ ϵ ᵗ¹) ⊗R) ᵗ¹ ↑ₒ m
                     newState (s ∷ʳ m)

    Req  : ∀ {m s} → WithState m ∷ s
                     receive L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ tt
                     return just $ L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ f m
                     newState s

  Functionality : Machine I ((A ⊗ B) ⊗ E)
  Functionality .State = List M -- queue of messages
  Functionality .stepRel = WithState_receive_return_newState_
  
-- authenticated, non-lossy, leaks all messages
module LeakyChannel (M : Type) = TemplateChannel M P.id

-- authenticated, non-lossy, leaks only message length
module SecureChannel (M : Type) = TemplateChannel M {ℕ}

module Encryption (PlainText CipherText PubKey PrivKey : Type)
                  ⦃ _ : DecEq CipherText ⦄
                  ⦃ _ : DecEq PubKey ⦄
                  (genCT : ℕ → CipherText)
                  (getPubKey : PrivKey → PubKey) where

  open Channel
  open Machine

  C : Channel
  C = (CipherText ⊎ Maybe PlainText) ⇿ (PlainText × PubKey ⊎ CipherText × PrivKey)

  S : Type
  S = List (PubKey × PlainText × CipherText)

  lookupPlainText : S → CipherText × PubKey → Maybe PlainText
  lookupPlainText s (c , k) = proj₁ <$> (proj₂ <$> flip findᵇ s λ where (k' , _ , c') → ¿ k ≡ k' × c ≡ c' ¿ᵇ)

  data WithState_receive_return_newState_ : MachineType I C S where

    Enc : ∀ {p k s} → let c = genCT (length s) in WithState s
                                                  receive L⊗ ϵ ↑ᵢ inj₁ (p , k)
                                                  return just $ L⊗ ϵ ↑ₒ inj₁ c
                                                  newState ((k , p , c) ∷ s)

    Dec : ∀ {c k s} → let p = lookupPlainText s (c , getPubKey k) in WithState s
                                                                     receive L⊗ ϵ ↑ᵢ inj₂ (c , k)
                                                                     return just $ L⊗ ϵ ↑ₒ inj₁ c
                                                                     newState s

  Functionality : Machine I C
  Functionality .State   = S
  Functionality .stepRel = WithState_receive_return_newState_

-- Note: it's a bad idea to do this as a wrapper, just make a shim to
-- compose with Encryption & the channel instead
module EncryptionShim (PlainText CipherText PubKey PrivKey : Type)
                      ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                      (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                      (pubKey : PubKey) (privKey : PrivKey) (msgLength : PlainText → ℕ) where
  open Channel
  open Machine

  module L = LeakyChannel CipherText
  module S = SecureChannel PlainText msgLength
  module E = Encryption PlainText CipherText PubKey PrivKey genCT getPubKey

  data WithState_receive_return_newState_ : MachineType ((L.A ⊗ L.B) ⊗ L.E) ((S.A ⊗ S.B) ⊗ S.E) (E.Functionality .State) where
  
    EncSend : ∀ {m m' s s'} → E.WithState s
                              receive L⊗ ϵ ↑ᵢ inj₁ (m , pubKey)
                              return just $ L⊗ ϵ ↑ₒ inj₁ m'
                              newState s'
                            → WithState s
                              receive L⊗ ((ϵ ᵗ¹ ⊗R) ⊗R) ᵗ¹ ↑ᵢ m
                              return just $ ((ϵ ⊗R) ⊗R) ⊗R ↑ₒ m'
                              newState s'

    DecRcv  : ∀ {m m' s s'} → E.WithState s
                              receive L⊗ ϵ ↑ᵢ inj₂ (m , privKey)
                              return just $ L⊗ ϵ ↑ₒ inj₂ (just m')
                              newState s'
                            → WithState s
                              receive ((L⊗ ϵ) ⊗R) ⊗R ↑ᵢ m
                              return just $ L⊗ ((L⊗ ϵ ᵗ¹) ⊗R) ᵗ¹ ↑ₒ m'
                              newState s'

  Functionality : Machine ((L.A ⊗ L.B) ⊗ L.E) ((S.A ⊗ S.B) ⊗ S.E)
  Functionality .State   = E.Functionality .State
  Functionality .stepRel = WithState_receive_return_newState_

module SecureFromAuthenticated (PlainText CipherText PubKey PrivKey : Type)
                               ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                               (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                               (pubKey : PubKey) (privKey : PrivKey)
                               (msgLength : PlainText → ℕ) where

  module L  = LeakyChannel CipherText
  module S  = SecureChannel PlainText msgLength
  module SH = EncryptionShim PlainText CipherText PubKey PrivKey genCT getPubKey pubKey privKey msgLength

  Functionality : Machine I ((S.A ⊗ S.B) ⊗ S.E)
  Functionality = SH.Functionality ∘ L.Functionality

  -- F≤Secure : Functionality ≤'UC S.Functionality msgLength
  -- F≤Secure = {!!}
