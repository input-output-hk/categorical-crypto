{-# OPTIONS --safe --without-K --guardedness #-}

-- A finite strategy embedded as an environment (`strategyEnv`: its state is
-- the remaining tree, an `ask` is a message on the plugged interface, a `coin`
-- is a `Dₚ` coin step), and the two observations of a closed process it gives
-- — `ctxRunˢ` under that environment and `runˢ`, layer 1's own run.
-- `Adequacy` says they agree; `UC.Seam.Adequacy` proves it.
--
-- The seam runs along that EMBEDDING, not along a reflection.  Reading a carry
-- off a reflection — closeness of direct runs into closeness under a machine
-- context — is the wrong way round: a carry needs a contextual hypothesis to
-- imply closeness of the direct runs (external theory review, finding 3).
--
-- Simulator accounting: `f ≤UC g` is `f ≈ℰ sub s ∘ g` at a GRADED codomain
-- `X ⊗₀ B`, so an embedded strategy playing against that agreement sees the
-- adversary interface as well.  At the TRIVIAL grade the simulator collapses
-- and the emulation is the direct agreement (`UC.Seam.Grounded.emulAgreeᵁ`).
-- At a real grade it does not collapse, and what carries is a bound on an
-- INTERFACE-OBSERVABLE event — the audit form, `auditWatch` in
-- `Examples.ChimericLedger.Observable` — with the simulator absorbed into the
-- environment leg (`UC.Audit.audit-carry`, at this instance `UC.Seam.Audit`);
-- the state trajectory comes back from it only under the extra truthfulness
-- hypothesis that example's appendix makes explicit.
--
-- Everything here keeps the machine layer at arm's length, and both reasons are
-- measured.  Interfaces are EXPLICIT in every definition below, and each
-- observation of a process goes through `ctxRunˢ`/`runˢ` and is then used by
-- name: an interface left implicit in a `Proc` argument makes Agda solve a meta
-- *under* the machine tensor, the ~1 GiB inversion `UC.Machine`'s header
-- records.  And the environment layer lives next door, because instantiating
-- it here costs a budget of the same order.

open import Data.Bool.Base
open import Data.Empty using (⊥)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base using (⊤)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Collapse as Col

module CategoricalCrypto.UC.Seam where

private
  module MC = Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- A strategy as an environment

-- Between activations the environment is about to play the rest of its tree,
-- or suspended on the answer to a query it has issued.
data EnvSt (B : Iface) : Set where
  play : Strat (Neg B) (Pos B) → EnvSt B
  susp : (Pos B → Strat (Neg B) (Pos B)) → EnvSt B

module _ (B : Iface) where

  -- Play the tree to its next interface boundary: a query on `B`, or the
  -- verdict on the tick interface.  Structural recursion, as `drive` is.
  playˢ : Strat (Neg B) (Pos B) → Dₚ (EnvSt B × (Neg B ⊎ Bool))
  playˢ (out b)    = returnₚ (play (out b) , inj₂ b)
  playˢ (ask q k)  = returnₚ (susp k , inj₁ q)
  playˢ (coin μ k) = coinₚ μ >>=ₚ λ b → playˢ (k b)

  -- The environment is activated by the verdict interface's tick and by the
  -- process's answers; anything else is off-protocol, hence `botₚ`.
  stepˢ : EnvSt B × (Pos B ⊎ ⊤) → Dₚ (EnvSt B × (Neg B ⊎ Bool))
  stepˢ (play d , inj₂ _) = playˢ d
  stepˢ (susp k , inj₁ p) = playˢ (k p)
  stepˢ (play _ , inj₁ _) = botₚ
  stepˢ (susp _ , inj₂ _) = botₚ

  stateˢ : Strat (Neg B) (Pos B) → MC.State
  stateˢ d = record
    { obj = EnvSt B ; point = λ _ → returnₚ (play d) ; discard = λ _ → returnₚ tt }

  strategyEnv : Strat (Neg B) (Pos B) → Proc B Ωᴵ
  strategyEnv d = MC.mk (stateˢ d) stepˢ

------------------------------------------------------------------------
-- The two runs it compares

-- Under an embedded strategy as an environment, and under layer 1's own run.
plugˢ : (B : Iface) → Strat (Neg B) (Pos B) → Proc unitᴵ B → Proc unitᴵ Ωᴵ
plugˢ B d u =
  Col.MT.traceᴹ (⊥ ⊎ ⊤) (⊥ ⊎ Bool) (Neg B ⊎ Pos B)
    (Col.MC.mk (Col.Sᴳ (strategyEnv B d) u) (Col.kᴳ (strategyEnv B d) u))

ctxRunˢ : (B : Iface) → Strat (Neg B) (Pos B) → Proc unitᴵ B → Dₚ Bool
ctxRunˢ B d u = ⟦ plugˢ B d u ⟧ᴼ

runˢ : (B : Iface) → Proc unitᴵ B → Strat (Neg B) (Pos B) → Dₚ Bool
runˢ B u d = runᴹ u d

-- Stated and priced at ~250–350 LOC, one module: this is `PrAgree`'s unrolling
-- again, over `𝒫ᴵ`'s composition instead of `Dist⊥`'s bind.  The ⊕-trace's
-- `iter` performs one pass per message and `playˢ` against `runᴹFrom` is the
-- induction on the `Strat` tree that matches them, with the junction delays it
-- absorbed by `iter-fix` (`absorbˡ`/`absorbʳ` of the embedding layer).  `_≈ₚ_`
-- and not `≡`: a trace does not compute to a run.
Adequacy : Set₁
Adequacy = (B : Iface) (u : Proc unitᴵ B) (d : Strat (Neg B) (Pos B))
         → ctxRunˢ B d u ≈ₚ runˢ B u d
