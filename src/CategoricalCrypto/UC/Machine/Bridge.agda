{-# OPTIONS --safe --without-K --guardedness #-}

-- The bridge between the environment layer and layer 1's concrete statements.
--
-- It lives under `UC.Machine` because it is a statement about the `Dₚ` MODEL,
-- not about UC: reading "given this answer, the next query" off a context needs
-- an inspectable step, and the budget it charges is that model's resource
-- doctrine.  Nothing in the qualitative core mentions a strategy.
--
-- An ℰ-statement quantifies over ancilla CONTEXTS; a hand-written security
-- theorem quantifies over adaptive STRATEGIES.  `UC.Machine.Dominated.dominated`
-- reads the second as the first AT ONE INSTANCE, which is the instance layer 1
-- supplies: the compared processes are CLOSED (`u v : Proc unitᴵ B`, i.e. `A := unitᴵ`)
-- and the hole is at the trivial grade (`conjᴵ` plugs them as
-- `Proc unitᴵ (unitᴵ ⊗ᴵ B)`, where the empty summand can never fire), even
-- though `ctxRun` itself is stated at a general `A`.  At that instance: once
-- every strategy the context's carried budget can afford leaves the two direct
-- runs ε-close, the context itself separates them by no more than ε + δ.  That
-- is what makes an abstract query bound contribute — with no such law, `QB`
-- may as well be `⊤`.  Whether
-- the closed, unit-hole case suffices for a general `f g : Proc A B` at a
-- general hole is not settled here.
--
-- The hypothesis is universal in the strategy, the shape a layer-1 theorem
-- (`_≈adv[_]_`, `Bounded`) already has: it feeds it at budget
-- `scale c (positive c′)`.  Why not one dominating strategy:
-- `docs/rewrite-verdict.md`, external theory review addendum.
--
-- The slack δ is positive rather than zero because the model's readout, hence
-- `_≈ℰ_`, quantifies over every positive slack anyway, so it costs a consumer
-- nothing; the decomposition never needs it (`UC.Machine.Dominated`).

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
