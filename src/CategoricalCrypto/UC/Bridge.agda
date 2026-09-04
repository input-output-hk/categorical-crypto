{-# OPTIONS --safe --without-K --guardedness #-}

-- The bridge between the environment layer and layer 1's concrete statements.
--
-- An ℰ-statement quantifies over ancilla CONTEXTS; a hand-written security
-- theorem quantifies over adaptive STRATEGIES.  `Reflects` is the obligation
-- that lets the second be read as the first: a budgeted context around a
-- closed process is dominated, at each pair of processes it compares, by a
-- strategy whose ask-depth is the context's carried budget.  It is what makes
-- an abstract query bound contribute — with no such law, `QB` may as well be
-- `⊤` (the reference arc records exactly this gap).
--
-- The quantifier order is ∀-before-Σ: the reifying strategy may depend on the
-- pair of processes compared.  The uniform order (ONE strategy for every pair)
-- is REFUTED at this level of generality: `Strat` is a finite tree, so it
-- mentions finitely many possible first queries, while a `Dₚ` context may
-- sample a natural number of unbounded support and ask that one question at
-- query bound one — pick two implementations differing only outside the tree's
-- support (external theory review, finding 2).  The uniform form is recoverable
-- only by enlarging strategies to a `Dₚ`-valued or coinductive language, or by
-- restricting UC contexts to a finitary fragment; neither is built here, and
-- the per-pair form is what the consumers below need anyway, each applying it
-- at one pair.
--
-- This is the same refutation one level up from the reference arc's, which
-- killed the uniform order for *deterministic* strategies — a context flipping
-- a fair coin and asking one of two questions gets advantage ½ against two
-- different pairs, while any deterministic one-ask tree scores zero against one
-- of them.  Layer 0's `Strat` carries the coin node from the start
-- (`CategoricalCrypto.Strategy`), which answers that objection; the sampling
-- one it does not.

open import Categories.Category using (Category)

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational using (ℚ)
open import Data.Sum.Base
open import Function.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

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
         → (u v : Proc unitᴵ B)
         → Σ[ d ∈ Strat (Neg B) (Pos B) ] asks≤ (c ℕ.* c′) d ×
           ((ε : ℚ) → runᴹ u d ≈ₚ[ ε ] runᴹ v d
                    → ctxRun Y E m (conjᴵ u) ≈ₚ[ ε ] ctxRun Y E m (conjᴵ v))
