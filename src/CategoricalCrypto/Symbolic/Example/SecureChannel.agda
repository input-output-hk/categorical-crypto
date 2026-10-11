{-# OPTIONS --safe --without-K --guardedness #-}

-- Eve's view of a secure channel over Σ₀/E₀ (`comonlundhcortier2008` Examples
-- 3.1, 3.3): the channel draws a key and coins and shows Eve the ciphertext of
-- the message, and the simulator shows her `enc(0, k, r)` instead.  The two
-- frames are statically equivalent (`Cipher.cipher-≈ₛ`), so the two channels
-- are kernel-equal (`Static.≈ₛ⇒≈ℰ`) and the real one realizes the simulated
-- one.  The message is a constant of the channel: a message chosen by the
-- environment makes the frame Eve sees depend on the run, which a fixed
-- relation between the two worlds cannot follow (docs/uc-setup-symbolic.md §6
-- step 10).

module CategoricalCrypto.Symbolic.Example.SecureChannel where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (refl)

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Term.PairEnc.Cipher using (cipher-≈ₛ)

open import CategoricalCrypto.Symbolic.Role Σ₀ using (Rcp)
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀ using (module Sym; ≈ᵁ⇔≈ℰ)
open import CategoricalCrypto.Symbolic.Static Σ₀ E₀ using (≈ₛ⇒≈ℰ)
open import CategoricalCrypto.Symbolic.Static.Emitter Σ₀ E₀ using (Emitter)

open Terms Σ₀

-- The key and the coins.
keys : List ⊤
keys = tt ∷ tt ∷ []

-- The ciphertext of the public constant `n`.
ciphertext : ℕ → All (Rcp keys) (tt ∷ [])
ciphertext n = app enc (app (cst n) [] ∷ var (here refl) ∷ var (there (here refl)) ∷ []) ∷ []

real≈simulated : (n : ℕ) → Emitter keys (ciphertext n) Sym.≈ℰ Emitter keys (ciphertext 0)
real≈simulated n = ≈ₛ⇒≈ℰ λ κ →
  cipher-≈ₛ {k = κ , 1} {m = app (cst n) []} {m′ = app (cst 0) []} {r = κ , 0} (λ ()) (λ ())

real≤simulated : (n : ℕ) → Emitter keys (ciphertext n) Sym.≤UC Emitter keys (ciphertext 0)
real≤simulated n = Sym.≈ᵁ⇒≤UC (Equivalence.from ≈ᵁ⇔≈ℰ (real≈simulated n))
