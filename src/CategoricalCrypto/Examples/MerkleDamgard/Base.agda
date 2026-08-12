{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- What the Merkle–Damgård development assumes of the framework, as ONE record.
--
-- Every open axiom is a record field, so `Examples.MerkleDamgard` — and
-- everything above it — is `--safe`.  Nothing cryptographic is assumed: the
-- fields are the 𝒢-construction primitives, the trace over the shared
-- interface, one standard fact about adaptive runs, and one probability-library
-- order fact.
--------------------------------------------------------------------------------

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_)

open import CategoricalCrypto.Channel.Core using (Channel; _⇿_; _⊗₀_)
open import CategoricalCrypto.Interaction using (TraceDeterminesRun)
open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunPartial
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E-Mono-On)
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

module CategoricalCrypto.Examples.MerkleDamgard.Base where

record MDAssumptions : Type₂ where
  infixr 9 _⊚_
  infixr 10 _⊗ₚ_
  field
    -- ── The probabilistic 𝒢-construction (plan debt 1 + 2) ──────────────────
    -- The machine type and its composition/tensor.  `PMachine` is 𝒢(SFun⊥) and
    -- `⟦_⟧` returns the UNDERLYING SFun⊥ morphism of a 𝒢-hom (partiality via
    -- `Dist⊥ = Dist-ℚ ∘ Maybe`).  No laws are assumed here: the category laws
    -- are `MerkleDamgardUC.MachineCatHyp` and the monoidal structure is
    -- `MachineHyp.mono`, both stated against the observational hom-equality.
    PMachine : Channel → Channel → Type₁
    pid      : ∀ {A}       → PMachine A A
    _⊚_      : ∀ {A B C}   → PMachine B C → PMachine A B → PMachine A C
    _⊗ₚ_     : ∀ {A B C D} → PMachine A B → PMachine C D → PMachine (A ⊗₀ C) (B ⊗₀ D)

    -- Embed a functionality as a *resource*.
    asResource : ∀ {A B} → SFunᵉ {M = Dist-ℚ} A B → SFunᵉ {M = Dist-ℚ} (⊥ ⊎ A) (⊥ ⊎ B)

    -- Lift a stateful functionality `SFunᵉ A B` into a machine, mirroring the
    -- G-construction `F : Kl(Dist) → 𝒢(Kl(Dist))` (cf. `Machine.Core`'s
    -- `Machine I C`: empty subroutine domain `I`).  Two shared copies of the
    -- interface `A ⇿ B` model a *public* random oracle: honest queries plus an
    -- adversary backdoor.
    liftFun : ∀ {A⁺ A⁻ B⁺ B⁻} → SFunᵉ {M = Dist-ℚ} (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺) → PMachine (A⁺ ⇿ A⁻) (B⁺ ⇿ B⁻)

    -- Observable reactive semantics of a machine: a stateful response kernel.
    -- The subroutine (`A`) and environment (`B`) interfaces jointly send on
    -- `inType A ⊎ outType B` and receive `outType A ⊎ inType B` — EXACTLY the
    -- type `liftFun` consumes, so that `⟦_⟧` and `liftFun` are mutually inverse.
    ⟦_⟧ : ∀ {A B : Channel}
        → PMachine A B
        → SFun⊥ (Channel.inType A ⊎ Channel.outType B) (Channel.outType A ⊎ Channel.inType B)

    -- The retraction laws of the two embeddings: `⟦_⟧` inverts `liftFun`, and
    -- embedding a subroutine-free functionality on the environment side and
    -- stripping the empty subroutine side is the identity.
    liftFun-sem    : ∀ {A⁺ A⁻ B⁺ B⁻} (f : SFunᵉ {M = Dist-ℚ} (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
                   → ⟦ liftFun f ⟧ ≡ embed⊥ f
    asResource-sem : ∀ {A B} (g : SFunᵉ {M = Dist-ℚ} A B) → stripᵉ (asResource g) ≡ g

    -- ── The trace over the shared interface (plan debt 1/2, same route) ─────
    -- The trace operator lives on the `g-construction` branch (it depends on the
    -- SMC solver, not merge-ready), so its composition and two laws are assumed
    -- in the shape that branch discharges against the real trace.  Nothing
    -- machine-specific: the per-machine fact `∘ᵍ-MD` is DERIVED from
    -- `∘ᵍ-unfold` in `MerkleDamgard`.

    -- G-composition on underlying morphisms: the trace over the shared middle
    -- interface `B⁻ ⊎ B⁺` of the wiring of `|g| ⊎ |f|`.  Fully general, total.
    _∘ᵍ_ : {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Type}
         → SFun⊥ (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺) → SFun⊥ (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)
         → SFun⊥ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺)

    -- Functoriality of `⟦_⟧` (this IS the composition law): the observable
    -- morphism of a composite machine is the 𝒢-composite of the observable
    -- morphisms.
    ⟦⟧-∘ : ∀ {A B C : Channel} (g : PMachine B C) (f : PMachine A B)
         → (_≈ᵉ_ {M = Dist⊥}) ⟦ g ⊚ f ⟧ (⟦ g ⟧ ∘ᵍ ⟦ f ⟧)

    -- The trace's fuelled UNFOLDING law: `∘ᵍ` is the ⊎-trace over the shared
    -- middle interface, whose fuelled approximants are the `GComp` token
    -- machines (`machineAt`), and the limit of an eventually-constant chain
    -- (`Stable n`, i.e. every deeper approximant already agrees with
    -- `machineAt n`) is its tail `machineAt n`.  Branch-dischargeable: BOUNDED
    -- trace = finite unrolling, so once fuel `n` suffices for every reachable
    -- activation the exact `∘ᵍ` coincides with the `n`-th approximant.
    ∘ᵍ-unfold : ∀ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Type}
                (g : SFun⊥ (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : SFun⊥ (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
                (n : ℕ) → GComp.Stable g f n
              → (_≈ᵉ_ {M = Dist⊥}) (g ∘ᵍ f) (GComp.machineAt g f n)

    -- ── The two layers below, at their own declarations ─────────────────────
    ≈ᵉ⇒run    : TraceDeterminesRun   -- `CategoricalCrypto.Interaction`
    E-mono-on : E-Mono-On            -- `…Distribution.RationalDist.Expectation`
