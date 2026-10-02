{-# OPTIONS --safe --without-K --guardedness #-}

-- The bridge between the environment layer and layer 1's concrete statements.
--
-- It lives under `UC.Machine` because it is a statement about the `Dₚ` MODEL,
-- not about UC: reading "given this answer, the next query" off a context needs
-- an inspectable step, and the budget it charges is that model's resource
-- doctrine.  Nothing in the qualitative core mentions a strategy.

open import Categories.Category using (Category)

open import Data.Bool.Base
open import Data.Empty
open import Data.Sum.Base
open import Function.Base

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.Machine.Bridge where

private module 𝒫 = Category 𝒫ᴵ

-- The unitor wire.  `Proc unitᴵ B` is a closed process at `B`; a graded
-- statement wants it at the degenerate grade `unitᴵ ⊗ᴵ B`, where the empty
-- summand can never fire.
λᴵ⇐ : {B : Iface} → Proc B (unitᴵ ⊗ᴵ B)
λᴵ⇐ = wireᴹ inj₂ [ ⊥-elim , id ]

-- …and its retraction, which closes a hole a graded statement has already
-- opened (`UC.Machine.Slide.unit-cancel`).
λᴵ⇒ : {B : Iface} → Proc (unitᴵ ⊗ᴵ B) B
λᴵ⇒ = wireᴹ [ ⊥-elim , id ] inj₂

qb-λᴵ⇒ : {B : Iface} → QB 1 (λᴵ⇒ {B})
qb-λᴵ⇒ = qb-wire [ ⊥-elim , id ] inj₂

conjᴵ : {B : Iface} → Proc unitᴵ B → Proc unitᴵ (unitᴵ ⊗ᴵ B)
conjᴵ u = λᴵ⇐ 𝒫.∘ u

-- What a budgeted ancilla context observes when a process is plugged into it:
-- exactly the closed run `_≈ℰ_` compares.
ctxRun : {A B : Iface} (Y : Iface)
       → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Proc A B → Dₚ Bool
ctxRun Y E m f = ⟦ (E 𝒫.∘ T₁ᴵ Y f) 𝒫.∘ m ⟧ᴼ
