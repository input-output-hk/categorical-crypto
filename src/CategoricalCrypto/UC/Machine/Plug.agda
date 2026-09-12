{-# OPTIONS --safe --without-K --guardedness #-}

-- Closing a grade with an adversary machine.
--
-- A process `A ⇒ X ⊛ B` carries the adversary interface `X` beside its honest
-- one, and an adversary is a machine that CONSUMES `X` and answers to nobody:
-- a `Proc X 𝟭ᴵ`, at the bundle's own unit rather than at `unitᴵ`, because that
-- is the codomain the grading's `sub` lands the closed grade on
-- (`UC.Machine.Dictionary.𝟭ᴵ`, and its header for why the two empty interfaces
-- are not interchangeable).  `plugᴹ a` is `subᴵ a` with that unit deflated, so
-- a system with its adversary plugged is again an ordinary `Proc A B` — which
-- is what layer 1's closed run and `UC.Seam.Adequacy` are stated at.

open import Categories.Category using (Category)

open import Data.Sum.Base using (inj₂)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; subᴵ′; wireᴹ)
open import CategoricalCrypto.UC.Machine.Dictionary using (drop⇒ˡ; 𝟭ᴵ)

module CategoricalCrypto.UC.Machine.Plug where

private module 𝒫 = Category 𝒫ᴵ

-- The left unitor as a machine; `UC.Machine.Dictionary.λ⇒-λᴳ` reads it as the
-- bundle's own.
λᴵ : {A : Iface} → Proc (𝟭ᴵ ⊗ᴵ A) A
λᴵ = wireᴹ drop⇒ˡ inj₂

plugᴹ : {X A : Iface} → Proc X 𝟭ᴵ → Proc (X ⊗ᴵ A) A
plugᴹ a = λᴵ 𝒫.∘ subᴵ′ a
