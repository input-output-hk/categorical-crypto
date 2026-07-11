# Plan: partial SFunM + 𝒢-construction machine semantics

Directive (2026-07-09, revised): add partiality to `SFunM` so it becomes a
traced monoidal category, and treat `PMachine` as 𝒢(SFun⊥): composition `⊚`
is the G-construction composition, and machine equality is the 𝒢 hom-setoid
INHERITED FROM `SFunM`'s `_≈ᵉ_`.  Record-level `≡` is unusable on principle:
`⊚` must associate on the nose while state products associate only up to iso,
so hom-equality must be the setoid, not structural equality.  My earlier
run-level `≈Mℚ` statement and the ad-hoc `Handshake` composition are both
superseded by this.  The GConstruction (trace axioms + solver-leaf
architecture) exists on another branch but depends on the SMC solver
machinery, which is not merge-ready — so FOR NOW the 𝒢-layer is postulated,
in a shape the branch can discharge on merge.

## Landed (green, --safe) — kept

* **P1** `ProbabilisticLogic/Distribution/RationalDist/Partial.agda`
  `Dist⊥ = Dist-ℚ ∘ Maybe` with PROVEN Monad/MonadSetoid/MonadLawsSetoid/
  CommutativeMonadSetoid instances + affineness (`>>=ᴹ-const`).  This is the
  partiality `𝒢(SFun⊥)` sits on — unconditionally needed.
  (Gotcha for future work: `_≈Mℚ_` mentions only `entries`, so thread all
  implicits explicitly and use `λ P → refl`, never bare `Eq.refl`.)
* **P2** `CategoricalCrypto/SFunPartial.agda` — keep `SFun⊥`,
  `SFun⊥-Category` (free from `SFunM` genericity), `embed⊥`, `strip⊥`,
  `>>=⊥-embed`, `iterFuel`/`iterGo` (fuelled ⊎-trace approximants; substrate
  for the eventual SFun⊥ trace instance).
  **Demoted/removed**: the `Handshake` module + `compose⊚` — superseded by
  the 𝒢-construction composition.

## Phase A (revised²) — 𝒢-shaped postulate layer in MerkleDamgard

Convention: for a channel `A = A⁺ ⇿ A⁻` (inType = A⁺, outType = A⁻), a 𝒢-hom
`A → B` has underlying morphism `SFun⊥ (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)` — exactly
`liftFun`'s argument type and `⟦_⟧`'s (generalized) result type.

1. Keep `⟦_⟧ : PMachine A B → SFun⊥ (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)` — the underlying
   morphism of a 𝒢-hom.
2. Keep `liftFun-sem : ⟦ liftFun f ⟧ ≡ embed⊥ f` (`liftFun` = `F : 𝒞 → 𝒢(𝒞)`;
   ⟦_⟧ is a retraction of it) and `asResource-sem`.
3. POSTULATE the honest 𝒢-composition on underlying morphisms — fully
   general, total, no closedness restriction (branch-provided later as the
   trace over the middle interface `B⁻ ⊎ B⁺` of the wiring of `|g| ⊎ |f|`):
     `_∘ᵍ_ : SFun⊥ (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺) → SFun⊥ (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)
           → SFun⊥ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺)`
4. POSTULATE FUNCTORIALITY of `⟦_⟧` (this IS the composition law — nothing
   more): `⟦⟧-∘ : ⟦ g ⊚ f ⟧ ≈ᵉ (⟦ g ⟧ ∘ᵍ ⟦ f ⟧)` in `SFunM`'s `_≈ᵉ_` at
   `Dist⊥` (the 𝒢 hom-setoid).  (Identity law `⟦ pid ⟧ ≈ᵉ 𝒢-id` only if the
   file ever needs it — currently it does not.)
5. POSTULATE (marked PROVABLE-standard, crypto-free) the adaptive bridge
   `≈ᵉ⇒run : f ≈ᵉ g → ∀ d → run⊥ f d ≈Mℚ run⊥ g d` — `_≈ᵉ_` is fixed-list
   (trace) equivalence, the security layer runs adaptive distinguishers; for
   stateful kernels transcript probabilities decompose prefix-wise into
   functionals of fixed-list joint distributions (finite support + DecEq
   outputs make it formalizable).  The one new standard-math obligation.
6. `⟦_⟧cl = strip⊥ ∘ ⟦_⟧ : PMachine I C → SFun⊥ (C⁻) (C⁺)` — `strip⊥`
   appears ONLY here, where the run/advantage layer consumes a closed
   machine (`I`-side is `⊥ ⊎ –` padding).  Rewire `run⊥`/`Pr₁⊥`/`adv`/
   `_≈ℰ[_]_` over `⟦_⟧cl`; re-derive `⟦General⟧-sem` from `liftFun-sem` +
   `asResource-sem` + embed/strip commutation.

## Phase B (two options)

Instantiating functoriality: `⟦ MD ⊚ Comp.M ⟧ ≈ᵉ ⟦ MD ⟧ ∘ᵍ ⟦ Comp.M ⟧`, and
via `liftFun-sem` the right side is
`embed⊥ mdArrow ∘ᵍ embed⊥ (asResource Comp.Functionality)`.  The remaining
per-machine content is the pure `SFun⊥` computation fact (no `PMachine`,
no `⟦_⟧`):
   `∘ᵍ-MD : strip⊥ (embed⊥ mdArrow ∘ᵍ embed⊥ (asResource Comp.Functionality))
             ≈ᵉ embed⊥ ⟨respR machine⟩`

* **B-deferred** (default): leave `∘ᵍ-MD` postulated; on merge of the
  g-construction branch, `_∘ᵍ_`, `⟦⟧-∘`, and `∘ᵍ-MD` are all discharged
  against the real trace.
* **B-now** (optional): additionally postulate the trace's characteristic
  unfolding law for `_∘ᵍ_` (generic, branch-provable) and DERIVE `∘ᵍ-MD`
  now by the bounded loop-replay induction (≤ k+1 internal steps per
  activation).  ~1 session.
  **DONE** — `GComp` token-loop approximants in `SFunPartial`, generic
  `∘ᵍ-unfold` postulate (fuel-saturated `machineAt n` = the trace), and
  `∘ᵍ-MD` derived by the `Replay` loop-replay induction (fuel `2k`,
  `stepsFor`; party-irrelevance via `p = 1`); no machine-specific
  postulate remains.

## Phase C — the honest traced structure on SFun⊥ (later, per directive)

Defining the actual trace operator on `SFun⊥` (so `_⊚ᵍ_` and the 𝒢
application become definitions): bounded/partially-traced now vs ω-chains vs
expectation-model carrier (`IterProbMonad` has `iter`+`iter-unfold`; check
Fubini status there first — `∫-swap` was NO-GO on the functional
representation).  To be worked out later; nothing in Phases A–B depends on
the choice.

## Resulting postulate inventory (after A + B-now)

Framework: `PMachine`/`pid`/`_⊚_`/`_⊗ₚ_`/`asResource`/`liftFun`/`⟦_⟧`.
𝒢-layer (branch-dischargeable): `_∘ᵍ_`, `⟦⟧-∘` (functoriality), `∘ᵍ-unfold`
  (fuelled unfolding law; `∘ᵍ-MD` is now a THEOREM)
  (+ `liftFun-sem`, `asResource-sem`).
Standard-math (provable): `≈ᵉ⇒run`, `E-mono-on`, `OnSupport` kit,
  `unique-run`, `take-drop-inj`.
Nothing cryptographic, nothing machine-specific.
