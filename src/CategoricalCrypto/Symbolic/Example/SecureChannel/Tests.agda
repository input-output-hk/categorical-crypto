{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Symbolic.Example.SecureChannel.Tests where

open import Data.Bool.Base
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no; does)

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀ using (Var)
open import CategoricalCrypto.Symbolic.Role Σ₀
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Protocol hiding (drop)

open Terms Σ₀
open EqTheory E₀
open Run E₀

selected other : Msg
selected = app pair (app (cst 11) [] ∷ app (cst 12) [] ∷ [])
other = app (cst 23) []

ciphertext dummy-ciphertext : Msg
ciphertext = app enc (selected ∷ name (7 , 0) ∷ name (7 , 1) ∷ [])
dummy-ciphertext = app enc (app (cst 0) [] ∷ name (7 , 0) ∷ name (7 , 1) ∷ [])

accepts-environment-plaintext : step 7 real-role (init real-role) (there (here refl) ↦ selected)
  ≡ (config pending (name (7 , 0) ∷ ciphertext ∷ selected ∷ []) 2 , here refl ↦ ciphertext)
accepts-environment-plaintext = refl

accepts-different-environment-plaintext : proj₂ (step 7 real-role (init real-role) (there (here refl) ↦ other))
  ≡ here refl ↦ app enc (other ∷ name (7 , 0) ∷ name (7 , 1) ∷ [])
accepts-different-environment-plaintext = refl

delivery-trace : (suffix : List (Input (Var void) ports))
  → run-terminal 7 real-role (channel-terminal false false) (init real-role)
      ((there (here refl) ↦ selected) ∷ (here refl ↦ ciphertext) ∷ suffix)
    ≡ (config finished [] 2 , (here refl ↦ ciphertext) ∷ (there (here refl) ↦ selected) ∷ [])
delivery-trace suffix rewrite terminal-no-further-behavior 7 real-role (channel-terminal false false)
  (config finished [] 2) suffix refl = refl

drop-trace : (suffix : List (Input (Var void) ports))
  → run-terminal 7 real-role (channel-terminal false false) (init real-role)
      ((there (here refl) ↦ selected) ∷ (here refl ↦ app (cst 1) []) ∷ suffix)
    ≡ (config finished [] 2 , (here refl ↦ ciphertext) ∷ (there (here refl) ↦ app (cst 2) []) ∷ [])
drop-trace suffix rewrite terminal-no-further-behavior 7 real-role (channel-terminal false false)
  (config finished [] 2) suffix refl = refl

no-post-delivery-activation : (suffix : List (Input (Var void) ports))
  → run-terminal 7 real-role (channel-terminal false false) (config finished [] 2) suffix
    ≡ (config finished [] 2 , [])
no-post-delivery-activation suffix = terminal-no-further-behavior 7 real-role (channel-terminal false false)
  (config finished [] 2) suffix refl

simulator-produces-dummy : step 7 simulator-role (init simulator-role) (here refl ↦ app (cst 0) [])
  ≡ (config pending (dummy-ciphertext ∷ []) 2 , there (here refl) ↦ dummy-ciphertext)
simulator-produces-dummy = refl

simulator-delivers-original-ciphertext : step 7 simulator-role (config pending (dummy-ciphertext ∷ []) 2)
  (there (here refl) ↦ dummy-ciphertext)
  ≡ (config finished [] 2 , here refl ↦ app (cst 0) [])
simulator-delivers-original-ciphertext = refl

simulator-drops-modified-ciphertext : step 7 simulator-role (config pending (dummy-ciphertext ∷ []) 2)
  (there (here refl) ↦ app (cst 1) [])
  ≡ (config finished [] 2 , here refl ↦ app (cst 1) [])
simulator-drops-modified-ciphertext = refl

ideal-records-plaintext-without-encryption : step 41 ideal-role (init ideal-role) (there (here refl) ↦ selected)
  ≡ (config pending (selected ∷ []) 0 , here refl ↦ app (cst 0) [])
ideal-records-plaintext-without-encryption = refl

ideal-delivers-recorded-plaintext : step 41 ideal-role (config pending (selected ∷ []) 0) (here refl ↦ app (cst 0) [])
  ≡ (config finished [] 0 , there (here refl) ↦ selected)
ideal-delivers-recorded-plaintext = refl

leaky-exposes-plaintext : proj₂ (step 7 leaky-role (init leaky-role) (there (here refl) ↦ selected))
  ≡ here refl ↦ selected
leaky-exposes-plaintext = refl

real-does-not-expose-plaintext : proj₂ (step 7 real-role (init real-role) (there (here refl) ↦ selected))
  ≢ here refl ↦ selected
real-does-not-expose-plaintext ()

ciphertext-of : ℕ → Msg → Msg
ciphertext-of κ m = nf (app enc (m ∷ name (κ , 0) ∷ name (κ , 1) ∷ []))

accepts-arbitrary-environment-plaintext : ∀ κ m
  → step κ real-role (init real-role) (there (here refl) ↦ m)
    ≡ (config pending (name (κ , 0) ∷ ciphertext-of κ m ∷ nf m ∷ []) 2 , here refl ↦ ciphertext-of κ m)
accepts-arbitrary-environment-plaintext κ m = refl

private
  accepts : ∀ {P : Set} (d : Dec P) → P → does d ≡ true
  accepts (yes _) _ = refl
  accepts (no not-p) p = ⊥-elim (not-p p)

  decrypt-selected : ∀ κ m → nf (app dec (ciphertext-of κ m ∷ name (κ , 0) ∷ [])) ≡ nf m
  decrypt-selected κ m = trans
    (app-cong dec {ts = ciphertext-of κ m ∷ name (κ , 0) ∷ []}
      {us = app enc (m ∷ name (κ , 0) ∷ name (κ , 1) ∷ []) ∷ name (κ , 0) ∷ []}
      (canon-≈E (app enc (m ∷ name (κ , 0) ∷ name (κ , 1) ∷ [])) ∷ refl ∷ []))
    (⟶-nf (root (dec-enc {x = m} {k = name (κ , 0)} {r = name (κ , 1)})))

delivers-arbitrary-selected-plaintext : ∀ κ m
  → step κ real-role (config pending (name (κ , 0) ∷ ciphertext-of κ m ∷ nf m ∷ []) 2)
      (here refl ↦ ciphertext-of κ m)
    ≡ (config finished [] 2 , there (here refl) ↦ nf m)
delivers-arbitrary-selected-plaintext κ m
  rewrite accepts (ciphertext-of κ m ≟E ciphertext-of κ m) refl | decrypt-selected κ m = refl

arbitrary-delivery-trace : ∀ κ m (suffix : List (Input (Var void) ports))
  → run-terminal κ real-role (channel-terminal false false) (init real-role)
      ((there (here refl) ↦ m) ∷ (here refl ↦ ciphertext-of κ m) ∷ suffix)
    ≡ (config finished [] 2 , (here refl ↦ ciphertext-of κ m) ∷ (there (here refl) ↦ nf m) ∷ [])
arbitrary-delivery-trace κ m suffix rewrite delivers-arbitrary-selected-plaintext κ m
  | terminal-no-further-behavior κ real-role (channel-terminal false false) (config finished [] 2) suffix refl = refl
