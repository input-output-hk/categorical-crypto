{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- The vocabulary the Merkle–Damgård development is phrased in, and the framework
-- it assumes, as ONE record.
--
-- `MDAssumptions` is the house-standard form of what used to be seven
-- `postulate` blocks in `Examples.MerkleDamgard`: every open axiom is a record
-- field, so that module — and everything above it — is `--safe`.  Nothing
-- cryptographic is assumed; the fields are the 𝒢-construction primitives, the
-- trace over the shared interface, and one probability-library order fact.  The
-- reactive interaction model above the record is the vocabulary its last two
-- fields are stated in, and lives here for that reason.
--------------------------------------------------------------------------------

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_)

open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
  renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)

open import CategoricalCrypto.Channel.Core using (Channel; _⇿_; _⊗₀_)
open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunPartial
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

module CategoricalCrypto.Examples.MerkleDamgard.Base where

-- Generic expectation on `Dist-ℚ`  (= `lookupᴰℚ` over the entries).
E : ∀ {A : Type} → Dist-ℚ A → (A → ℚ) → ℚ
E μ f = lookupᴰℚ (entries μ) f

-- Drop an empty (`⊥`) interface component on both sides; `strip⊥` is the same
-- construction at `Dist⊥`.
stripᵉ : ∀ {A B : Type} → SFunᵉ {M = Dist-ℚ} (⊥ ⊎ A) (⊥ ⊎ B) → SFunᵉ {M = Dist-ℚ} A B
stripᵉ f = record
  { State = SFunᵉ.State f
  ; init  = SFunᵉ.init f
  ; fun   = λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))
                     >>=ᴹ λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr))
  }

--------------------------------------------------------------------------------
-- Reactive interaction model.  An adaptive distinguisher runs against a stateful
-- response kernel; ε-indistinguishability is *defined* from the resulting bit, and
-- the bridge is the Fundamental Lemma of Game-Playing (adaptive-robust).
--------------------------------------------------------------------------------

-- An adaptive distinguisher: at each node output a guess, or query and branch on
-- the response.
data Dgr (Q R : Type) : Type where
  out : Bool → Dgr Q R
  ask : Q → (R → Dgr Q R) → Dgr Q R

-- "issues at most n queries on every branch"
asks≤ : {Q R : Type} → ℕ → Dgr Q R → Type
asks≤ _       (out _)   = ⊤
asks≤ zero    (ask _ _) = ⊥
asks≤ (suc n) (ask _ k) = ∀ r → asks≤ n (k r)

-- Run a distinguisher against a bare response kernel, returning the output bit, resp.
-- the final state (to read off the bad flag afterwards).
runWith : {Q R St : Type} → (St → Q → Dist-ℚ (St × R)) → St → Dgr Q R → Dist-ℚ Bool
runWith resp s (out b)   = return-ℚ b
runWith resp s (ask q k) = resp s q >>=ᴹ λ sr → runWith resp (proj₁ sr) (k (proj₂ sr))

-- The probability that `bad` fires at some visited state during the run of `d`
-- against `resp` from `s` (1 immediately at a bad state — no monotonicity needed).
badProb : {Q R St : Type} → (St → Q → Dist-ℚ (St × R)) → (St → Bool) → St → Dgr Q R → ℚ
badProb resp bad s (out _)   = bool→ℚ (bad s)
badProb resp bad s (ask q k) with bad s
... | true  = 1ℚ
... | false = E (resp s q) (λ sr → badProb resp bad (proj₁ sr) (k (proj₂ sr)))

-- Run against a stateful system (an `SFunᵉ`), from its initial state.
run : {Q R : Type} → SFunᵉ {M = Dist-ℚ} Q R → Dgr Q R → Dist-ℚ Bool
run f = runWith (λ s q → SFunᵉ.fun f (s , q)) (SFunᵉ.init f)

-- Probability the run outputs `true`, and the distinguishing advantage of `d`.
Pr₁ : Dist-ℚ Bool → ℚ
Pr₁ μ = E μ bool→ℚ

-- ────────────────────────────────────────────────────────────────────────────
-- The partial (`SFun⊥`) run/advantage layer — what the closed-machine semantics
-- `⟦_⟧cl` feeds.  `mb` sends the divergence sink `nothing` to `0`.

mb : Maybe Bool → ℚ
mb (just b) = bool→ℚ b
mb nothing  = 0ℚ

Pr₁⊥ : Dist⊥ Bool → ℚ
Pr₁⊥ μ = E μ mb

runWith⊥ : {Q R St : Type} → (St → Q → Dist⊥ (St × R)) → St → Dgr Q R → Dist⊥ Bool
runWith⊥ resp s (out b)   = return⊥ b
runWith⊥ resp s (ask q k) = resp s q >>=⊥ λ sr → runWith⊥ resp (proj₁ sr) (k (proj₂ sr))

run⊥ : {Q R : Type} → SFun⊥ Q R → Dgr Q R → Dist⊥ Bool
run⊥ f = runWith⊥ (λ s q → SFunᵉ.fun f (s , q)) (SFunᵉ.init f)

adv : {Q R : Type} → SFun⊥ Q R → SFun⊥ Q R → Dgr Q R → ℚ
adv f g d = ∣ Pr₁⊥ (run⊥ f d) -ℚ Pr₁⊥ (run⊥ g d) ∣ℚ

Pr₁⊥-just : ∀ (μ : Dist-ℚ Bool) → Pr₁⊥ (Dmap just μ) ≡ Pr₁ μ
Pr₁⊥-just μ = lookupᴰℚ-Dmap just μ mb

Pr₁⊥-cong : (μ ν : Dist⊥ Bool) → μ ≈Mℚ ν → Pr₁⊥ μ ≡ Pr₁⊥ ν
Pr₁⊥-cong μ ν μ≈ν = μ≈ν mb

--------------------------------------------------------------------------------
-- What Merkle–Damgård assumes of the theory
--------------------------------------------------------------------------------

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

    -- ── Standard mathematics, crypto-free (plan debt 4) ─────────────────────
    -- A fixed-list (trace) equivalence determines adaptive behaviour of stateful
    -- kernels: transcript probabilities decompose prefix-wise into functionals
    -- of fixed-list joint distributions (finite support + DecEq outputs make
    -- this formalizable).
    ≈ᵉ⇒run : {Q R : Type} {f g : SFun⊥ Q R}
           → (_≈ᵉ_ {M = Dist⊥}) f g → ∀ d → run⊥ f d ≈Mℚ run⊥ g d

    -- ── The probability layer's one order fact ──────────────────────────────
    -- Expectation monotonicity on the support — true because weights are
    -- non-negative, which the `Dist-ℚ` library does not track (its invariant is
    -- only mass ≡ 1).  Global monotonicity `E-mono` is DERIVED from it.
    E-mono-on : ∀ {A : Type} (μ : Dist-ℚ A) (f g : A → ℚ)
              → OnSupport (λ a → f a ≤ℚ g a) μ → E μ f ≤ℚ E μ g
