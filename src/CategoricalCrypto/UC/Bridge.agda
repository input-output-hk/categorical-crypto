{-# OPTIONS --safe --without-K --guardedness #-}

-- The bridge between the environment layer and layer 1's concrete statements.
--
-- An ℰ-statement quantifies over ancilla CONTEXTS; a hand-written security
-- theorem quantifies over adaptive STRATEGIES.  `Reflects` is the obligation
-- that lets the second be read as the first: every budgeted context around a
-- closed process is dominated by one strategy whose ask-depth is the context's
-- carried budget.  It is what makes an abstract query bound contribute — with
-- no such law, `QB` may as well be `⊤` (the reference arc records exactly this
-- gap).
--
-- The quantifier order is Σ-before-∀: ONE strategy, for every pair of
-- processes plugged into the context.  That order was REFUTED in the reference
-- arc, where strategies were deterministic — a context flipping a fair coin and
-- asking one of two questions gets advantage ½ against two different pairs,
-- while any deterministic one-ask tree scores zero against one of them, so the
-- averaging argument only ever worked per fixed pair.  Layer 0's `Strat`
-- carries the coin node from the start
-- (`CategoricalCrypto.Strategy`), so the reifier can internalize the context's
-- own coins and the strong order is sound.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using ([_,_]; inj₂)
open import Function.Base using (id)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp using (Dₚ)
open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; ⟦_⟧ᴼ; T₁ᴵ; wireᴹ)
open import CategoricalCrypto.UC.QueryBound using (QB)

module CategoricalCrypto.UC.Bridge where

private module 𝒫 = Category 𝒫ᴵ

-- The unitor wire.  `Proc unitᴵ B` is a closed process at `B`; a graded
-- statement wants it at the degenerate grade `unitᴵ ⊗ᴵ B`, where the empty
-- summand can never fire.
λᴵ⇐ : {B : Iface} → Proc B (unitᴵ ⊗ᴵ B)
λᴵ⇐ = wireᴹ inj₂ [ ⊥-elim , id ]

conjᴵ : {B : Iface} → Proc unitᴵ B → Proc unitᴵ (unitᴵ ⊗ᴵ B)
conjᴵ u = λᴵ⇐ 𝒫.∘ u

-- What a budgeted ancilla context observes when a process is plugged into it:
-- exactly the closed run `_≈ℰ_` compares.
ctxRun : {A B : Iface} (Y : Iface)
       → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Proc A B → Dₚ Bool
ctxRun Y E m f = ⟦ (E 𝒫.∘ T₁ᴵ Y f) 𝒫.∘ m ⟧ᴼ

-- Stated and priced.  The reifier recurses on the context's remaining query
-- potential (from `E`'s and `m`'s certificates): a crossing to the plugged
-- interface becomes an `ask`, a coin becomes a `coin`, a verdict becomes an
-- `out`, and `asks≤` falls out of the measure.  It is instance-specific —
-- reading "given this answer, the next query" needs an inspectable step — so
-- it belongs beside `UC.Machine`, not in the abstract layer.  The reference
-- arc prices the two-machine skeleton at ~250 LOC and recommends spiking it
-- before committing.
Reflects : Set₁
Reflects = (B Y : Iface)
           (E : Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
           {c c′ : ℕ} → QB c E → QB c′ m
         → Σ[ d ∈ Strat (Neg B) (Pos B) ] asks≤ (c ℕ.* c′) d ×
           ((u v : Proc unitᴵ B) (ε : ℚ)
            → runᴹ u d ≈ₚ[ ε ] runᴹ v d
            → ctxRun Y E m (conjᴵ u) ≈ₚ[ ε ] ctxRun Y E m (conjᴵ v))
