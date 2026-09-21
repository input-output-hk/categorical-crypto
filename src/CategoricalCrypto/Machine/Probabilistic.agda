{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- The probabilistic machine layer, as a structure.
--
-- A machine is a 𝒢-construction hom over the partial probabilistic stateful
-- functions `SFun⊥`: `PMachine A B` has a subroutine interface `A` and an
-- environment interface `B`, and its observable semantics `⟦_⟧` is the reactive
-- kernel that jointly serves both.  Composition `_⊚_` plugs the environment
-- interface of one machine into the subroutine interface of the next, and its
-- semantics is the TRACE `_∘ᵍ_` over the shared interface (`⟦⟧-∘`).
--
-- The construction itself lives on the `g-construction` branch (it depends on
-- the SMC solver and is not merge-ready), so this module states it rather than
-- builds it: `Machines` is the structure a model must provide, and every theorem
-- above it — the machine category, the UC payoff — is parametric in one.
-- Nothing here is cryptographic, and nothing here is about Merkle–Damgård.
--------------------------------------------------------------------------------

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_)

open import CategoricalCrypto.Channel.Core using (Channel; _⇿_)
open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunPartial
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

module CategoricalCrypto.Machine.Probabilistic where

record Machines : Type₂ where
  infixr 9 _⊚_
  field
    -- The machine type and its composition.  `PMachine` is 𝒢(SFun⊥); `⟦_⟧`
    -- returns the UNDERLYING SFun⊥ morphism of a 𝒢-hom (partiality via
    -- `Dist⊥ = Dist-ℚ ∘ Maybe`).
    PMachine : Channel → Channel → Type₁
    pid      : ∀ {A}     → PMachine A A
    _⊚_      : ∀ {A B C} → PMachine B C → PMachine A B → PMachine A C

    -- Embed a functionality as a *resource*.
    asResource : ∀ {A B} → SFunᵉ {M = Dist-ℚ} A B → SFunᵉ {M = Dist-ℚ} (⊥ ⊎ A) (⊥ ⊎ B)

    -- Lift a stateful functionality `SFunᵉ A B` into a machine, mirroring the
    -- G-construction `F : Kl(Dist) → 𝒢(Kl(Dist))` (cf. `Machine.Core`'s
    -- `Machine I C`: empty subroutine domain `I`).  Two shared copies of the
    -- interface `A ⇿ B` model a *public* random oracle: honest queries plus an
    -- adversary backdoor.
    liftFun : ∀ {A⁺ A⁻ B⁺ B⁻} → SFunᵉ {M = Dist-ℚ} (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺) → PMachine (A⁺ ⇿ A⁻) (B⁺ ⇿ B⁻)

    -- Observable reactive semantics: a stateful response kernel.  The subroutine
    -- (`A`) and environment (`B`) interfaces jointly send on
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
