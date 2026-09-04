{-# OPTIONS --safe --without-K --guardedness #-}

-- The one link of the seam that needs the grading: an ℰ-agreement, whose
-- ancilla quantifier ranges over abstract contexts, is seen by the concrete
-- environments `UC.Seam.strategyEnv` builds.
--
-- It lives here rather than in `UC.Seam` because instantiating the environment
-- layer at a `Grading 𝒫ᴵ` costs a heap budget of the same order as the seam's
-- own machine conversions, and nothing else in the seam needs it — the carry
-- (`agree-to-adv`, `pov-carry`) runs on `_≈ℰˢ_` alone.

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Base using (Grading)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; UCBaseᴹ)
open import CategoricalCrypto.UC.Seam using (Agreeˢ)

import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Seam.Grounding (G : Grading 𝒫ᴵ) where

private module E = Em (UCBaseᴹ G)

-- Stated and priced at ~80–120 LOC: instantiate `_≈ℰ_` at `Y = unitᴵ`, at the
-- test `strategyEnv B d 𝒫.∘ λᴵ⇒` and at the closure `λᴵ⇐ 𝒫.∘ u`, and cancel
-- `T₁ᴵ unitᴵ` against the two wires.  The `unitᴵ` summands can never fire
-- (`⊥-unique`), so the cancellation holds; but it is an equation between
-- `𝒫ᴵ`-composites, hence between ⊕-traces, and so needs the trace fusion M2's
-- task 3 left open — the same gate as `Grading 𝒫ᴵ` itself.
StratIsEnv : Set₁
StratIsEnv = (B : Iface) (u v : Proc unitᴵ B) → E._≈ℰ_ u v → Agreeˢ B u v
