{-# OPTIONS --safe --without-K --guardedness #-}

-- The bridge between the environment layer and layer 1's concrete statements.
--
-- It lives under `UC.Machine` because it is a statement about the `Dₚ` MODEL,
-- not about UC: reading "given this answer, the next query" off a context needs
-- an inspectable step, and the budget it charges is that model's resource
-- doctrine.  Nothing in the qualitative core mentions a strategy.
--
-- An ℰ-statement quantifies over ancilla CONTEXTS; a hand-written security
-- theorem quantifies over adaptive STRATEGIES.  `ContextDominated` reads the
-- second as the first AT ONE INSTANCE, which is the instance layer 1 supplies:
-- the compared processes are CLOSED (`u v : Proc unitᴵ B`, i.e. `A := unitᴵ`)
-- and the hole is at the trivial grade (`conjᴵ` plugs them as
-- `Proc unitᴵ (unitᴵ ⊗ᴵ B)`, where the empty summand can never fire), even
-- though `ctxRun` itself is stated at a general `A`.  At that instance: once
-- every strategy the context's carried budget can afford leaves the two direct
-- runs ε-close, the context itself separates them by no more than ε + δ.  That
-- is what makes an abstract query bound contribute — with no such law, `QB`
-- may as well be `⊤` (the reference arc records exactly this gap).  Whether
-- the closed, unit-hole case suffices for a general `f g : Proc A B` at a
-- general hole is not settled here.
--
-- The statement is UNIVERSAL in the strategy, which is also the shape its
-- consumers have: a layer-1 theorem (`_≈adv[_]_`, `Bounded`) is already
-- quantified over budgeted strategies, so it feeds this hypothesis by
-- instantiating its own budget at `ctxBudget c c′`.  Asking instead for ONE
-- finite strategy that dominates the context is constructively overdemanding
-- twice over: the witness is an
-- optimal deterministic policy of a `Dₚ` context, and it must ATTAIN the
-- context's advantage rather than approximate it.  Its uniform variant (one
-- strategy before the compared pair) is outright refuted: `Strat` is a finite
-- tree, so it mentions finitely many possible first queries, while a `Dₚ`
-- context may sample a question of unbounded support and ask that one at query
-- bound one, and two implementations differing only outside the tree's support
-- separate the context but not the strategy.  Moving the pair in front of the
-- witness answers that refutation but leaves the extraction, so the existential
-- is gone rather than demoted (external theory review, findings 2 and 3).
--
-- The slack δ is arbitrary and positive rather than zero because `_∼_` —
-- hence `_≈ℰ_` — quantifies over every positive slack anyway, so it costs a
-- consumer nothing.  The decomposition does not need it: the extraction is
-- chosen once the observation's budget is known, so no residue is left for a
-- positive δ to absorb, and `skeleton⇒dominated` spends it on `≈ₚ[]-mono`
-- alone.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum.Base using ([_,_]; inj₂)
open import Function.Base using (id)

open import ProbabilisticLogic.Dp using (Dₚ)
open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Budget using (ctxBudget)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; ⟦_⟧ᴼ; T₁ᴵ; wireᴹ)
open import CategoricalCrypto.UC.QueryBound using (QB)

module CategoricalCrypto.UC.Machine.Bridge where

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

-- Proved in `UC.Machine.Dominated`, by decomposing the context's activation
-- sequence against a strategy of that budget: a crossing to the plugged
-- interface is an `ask`, a coin is a `coin`, a verdict is an `out`, and the
-- hypothesis is applied branchwise and reassembled by convexity of `Pr≤` in
-- the branch distribution.  It is instance-specific — reading "given this
-- answer, the next query" needs an inspectable step — so it belongs beside
-- `UC.Machine`, not in the abstract layer.  The decomposition runs once per
-- verdict, `_≈ₚ[_]_` comparing both masses.
ContextDominated : Set₁
ContextDominated = (B Y : Iface)
                   (E : Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
                   {c c′ : ℕ} → QB c E → QB c′ m
                 → (u v : Proc unitᴵ B) (ε δ : ℚ) → 0ℚ ℚ.< δ
                 → ((d : Strat (Neg B) (Pos B)) → asks≤ (ctxBudget c c′) d
                    → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
                 → ctxRun Y E m (conjᴵ u) ≈ₚ[ ε ℚ.+ δ ] ctxRun Y E m (conjᴵ v)
