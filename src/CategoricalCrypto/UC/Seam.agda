{-# OPTIONS --safe --without-K --guardedness #-}

-- Where layer 1's `POV`/`_≈adv[_]_`/`transfer` sit relative to `_≤UC_`.
--
-- Layer 1 already has the carry: `Protocol.Observe.transfer` turns a safety
-- bound on one system into a bound on an indistinguishable one, with the
-- advantage added, and that is what the ledger example's `pov-transfer` uses.
-- What an emulation at the machine layer buys is the *hypothesis* of that
-- theorem, so the seam is the chain from a UC hypothesis down to it.
--
-- The chain runs along an EMBEDDING, not along a reflection.  An earlier
-- version read the carry off `UC.Bridge.Reflects`, which turns closeness of
-- direct runs into closeness under a machine context — the wrong way round,
-- the carry needing a contextual hypothesis to imply closeness of the direct
-- runs (external theory review, finding 3).  Built the other way, the chain is
--
--   `strategyEnv`  embeds a finite strategy as an environment: its state is the
--                  remaining tree, an `ask` is a message on the plugged
--                  interface, a `coin` is a `Dₚ` coin step.  Constructive.
--   `StratIsEnv`   an ℰ-agreement is visible to those environments — the
--                  ancilla quantifier at a degenerate ancilla.  Stated, in
--                  `UC.Seam.Grounding`, the one part of the seam that needs a
--                  `Grading`.
--   `Adequacy`     the closed run of an embedded strategy is layer 1's own
--                  `runᴹ` at that strategy.  Stated.
--   `AgreeToAdv`   the corollary: those two and `PrAgree` give `_≈adv[_]_`,
--                  hence `pov-carry`, which is proved from it.
--
-- Simulator accounting: `f ≤UC g` is `f ≈ℰ sub s ∘ g` at a GRADED codomain
-- `X ⊛ B`, so an embedded strategy playing against that agreement sees the
-- adversary interface as well.  A bad event carried across an emulation must
-- therefore be interface-observable — the audit form, `POVaudit`/`watch` in
-- `Examples.ChimericLedger.POV`, which is what that gadget is for — and the
-- state trajectory comes back from it through the same example's
-- `TrajectoryFromAudit`.  `pov-carry` is the ungraded end of the chain:
-- agreement of two closed processes, which is what `transfer` consumes.
--
-- Everything here keeps the machine layer at arm's length, and both reasons are
-- measured.  Interfaces are EXPLICIT in every definition below, and each
-- observation of a process goes through `ctxRunˢ`/`runˢ` and is then used by
-- name: an interface left implicit in a `Proc` argument makes Agda solve a meta
-- *under* the machine tensor, the ~1 GiB inversion `UC.Machine`'s header
-- records.  And the `Grading` lives next door, because instantiating the
-- environment layer at it costs a budget of the same order while only
-- `StratIsEnv` needs it.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp using (Dₚ; _>>=ₚ_; returnₚ; botₚ; _≈ₚ_)
open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_; ≈ₚ[]-sym)
open import ProbabilisticLogic.Dp.Coin using (coinₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Observe using (Bounded; _≈adv[_]_; transfer)
open import CategoricalCrypto.Strategy using (Strat; out; ask; coin; asks≤)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; ⟦_⟧ᴼ)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Seam where

private
  module 𝒫 = Category 𝒫ᴵ
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

-- The two observations of a closed process the seam compares — under an
-- embedded strategy as an environment, and under layer 1's own run.
ctxRunˢ : (B : Iface) → Strat (Neg B) (Pos B) → Proc unitᴵ B → Dₚ Bool
ctxRunˢ B d u = ⟦ strategyEnv B d 𝒫.∘ u ⟧ᴼ

runˢ : (B : Iface) → Proc unitᴵ B → Strat (Neg B) (Pos B) → Dₚ Bool
runˢ B u d = runᴹ u d

-- Environment agreement read at the embedded strategies alone: the fragment of
-- an ℰ-statement the carry consumes.  Spelled in the `Dₚ` vocabulary rather
-- than as the environment layer's `_∼_` of the two runs — the same relation by
-- definition, but going through that projection η-expands `Observationᴹ`, whose
-- `⟦⟧-resp-≈` field drags the machine equality in with it.
Agreeˢ : (B : Iface) → Proc unitᴵ B → Proc unitᴵ B → Set
Agreeˢ B u v = (d : Strat (Neg B) (Pos B)) (ε : ℚ) → 0ℚ ℚ.< ε
             → ctxRunˢ B d u ≈ₚ[ ε ] ctxRunˢ B d v

Agreeˢ-sym : (B : Iface) (u v : Proc unitᴵ B) → Agreeˢ B u v → Agreeˢ B v u
Agreeˢ-sym B u v h d ε ε>0 = ≈ₚ[]-sym (h d ε ε>0)

------------------------------------------------------------------------
-- The two obligations

-- Stated and priced at ~250–350 LOC, one module: this is `PrAgree`'s unrolling
-- again, over `𝒫.∘` instead of `Dist⊥`'s bind.  The ⊕-trace's `iter` performs
-- one pass per message and `playˢ` against `runᴹFrom` is the induction on the
-- `Strat` tree that matches them, with the junction delays `𝒫.∘` inserts
-- absorbed by `iter-fix` (`absorbˡ`/`absorbʳ` of the embedding layer).  `_≈ₚ_`
-- and not `≡`: a trace does not compute to a run.
Adequacy : Set₁
Adequacy = (B : Iface) (u : Proc unitᴵ B) (d : Strat (Neg B) (Pos B))
         → ctxRunˢ B d u ≈ₚ runˢ B u d

-- The corollary, stated: environment agreement at the embedded strategies is
-- layer 1's advantage bound at every positive slack.
--
-- Its proof from `Adequacy` and `PrAgree` is ARITHMETIC ONLY, and is written
-- out in `UC.Seam.Carry`: `≈ₚ[]-resp` transports the agreement onto the two
-- runs, each side's `PrAgree` witness reads its verdict probability off a
-- budget the ε-domination reaches (`Pr≤` being monotone), and `∣∣≤` closes the
-- two-sided bound.
AgreeToAdv : Set₁
AgreeToAdv = {B : Iface} (P Q : Protocol unitᴵ B)
           → Agreeˢ B (morphism P) (morphism Q)
           → (ε : ℚ) → 0ℚ ℚ.< ε → P ≈adv[ (λ _ → ε) ] Q

-- The POV carry: a bound on the ideal system's bad event becomes one on the
-- real system's, at `ε + δ` for an arbitrarily small `δ`.
pov-carry : AgreeToAdv → {B : Iface} (P Q : Protocol unitᴵ B)
          → Agreeˢ B (morphism P) (morphism Q)
          → {bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)} {ε : ℕ → ℚ}
          → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
          → (δ : ℚ) → 0ℚ ℚ.< δ
          → Bounded Q bad ε → Bounded P bad (λ q → ε q ℚ.+ δ)
pov-carry a2a {B} P Q em bad-asks δ δ>0 =
  transfer bad-asks (a2a Q P (Agreeˢ-sym B (morphism P) (morphism Q) em) δ δ>0)
