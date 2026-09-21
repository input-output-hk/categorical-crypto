# Event bounds in the setup's own vocabulary

Baseline: `protocol-rewrite` at `9d33f783`. Paths relative to `src/CategoricalCrypto/`.

## Goal

The ledger demo's headline stays a probability bound, not an emulation statement:
"against every polynomially query-bounded environment, the probability that the total
value reported at the end differs from the initial one is at most the birthday bound,
up to negligible slack". What changes is the vocabulary it is stated in. Today it
needs a private closed-system layer (`UC/Saturated.agda`, `UC/Asymptotic.agda`); it
should need nothing but the machine `QUCSetup` and its quantitative theory.

## Vocabulary map

| homegrown (`UC/Saturated.agda`, `UC/Asymptotic.agda`) | setup-native counterpart |
|---|---|
| `Systems B = (n : ℕ) → Protocol unitᴵ (B n)` (`Saturated:71`) | a closed `Homᶠ` at trivial grade; `imgᶠ B R n = closedᵒ (morphism (R n))` already embeds it (`UC/Asymptotic/Family.agda:92`) |
| `Watch B`, a `Strat → Strat` transformer (`:77`) | a monitor PROCESS on the honest interface, `μ : ifaceᵒ B ⇒ ifaceᵒ B ⊗ Flag`, relaying traffic and raising one bit — a morphism of the setup, so the absorption lemmas apply to it |
| `QueryPreserving` (`:86`) | `QB 1 μ`: the monitor asks nothing of its own (`UC/Budget.agda`, `qb-T₁`) |
| `Pr (P n) (bad n d)` (`Protocol/Observe.agda:171`) | `Obs ((E ∘ T₁ᵒ W f) ∘ m)` read at `true` (`UC/Model/Observation.agda:59`) |
| `asks≤ (p n) d` | `QB c E`, `QB c′ m`, allowance `ctxBudget c c′` (`UC/Budget.agda:74`) |
| `SaturatedBounded[ G ]` (`:96`): `∀ p Poly → ∃ ν, G ν × ∀ n d …` | the same quantifier order `GradedBound` fixes (`UC/Approximate.agda:110`); PROPOSED `Hitsᴺ` below |
| `_≈negl_` (`:188`), `≈negl-respects` (`:208`) | `_≈ctx[_]_` at a negligible schedule (`UC/Quantitative/Family.agda`); transport is `≈ctx-ext`/`≈ctx-sub` |
| `boundedᴺ`, `uc-preservesᴺ` (`UC/Asymptotic.agda:73,80`) | PROPOSED `hits-lift`, `hits-transfer` below |
| `≤UC^ωⁿ⇒≈negl` (`UC/Asymptotic/Family.agda:279`) | unnecessary once the transport is stated on `_≈ctx[_]_` |

`_≤UC^ωⁿ_` itself (`Asymptotic/Family.agda:109`) is already `_≈ctxᴬ[_]_` on `imgᶠ` images
plus `NegligibleBound`; it survives, restated on the image type so `Systems` can go.

## The definitions (PROPOSED, schematic)

Single level, in `UC/Quantitative/Contextual.agda` beside `_≈ᵁᵠ[_]_` (`:58`), for a closed
`f : 𝟙 ⇒ X ⊗₀ B` and a monitor `μ : B ⇒ B ⊗₀ Flag`:

```agda
Hits[ ε ] f μ =
    (W : Obj) (E : W ⊗₀ (X ⊗₀ B) ⇒ Ω) (m : 𝟙 ⇒ W ⊗₀ 𝟙) {c c′ : ℕ}
  → QB c E → QB c′ m
  → Pr ⟦ (flag E ∘ id ⊗₁ (id ⊗₁ μ) ∘ id ⊗₁ f) ∘ m ⟧ ≤ ε (ctxBudget c c′)
```

where `flag E` is the environment `E` with its output bit replaced by the monitor's flag
(the spike fixes this spelling: the flag port is threaded past `E` and projected, so `E`
stays an arbitrary test on the honest traffic). `Pr` is the acceptance probability of the
observation, `Obs … ≈ₚ …` at `true`.

Family level, in `UC/Quantitative/Family.agda` beside `_≈ctx[_]_` (`:91`), at a schedule
`ε : ℕ → ℕ → ℚ`, allowance before slack exactly as `GradedBound`:

```agda
Hitsᶠ[ ε ] f μ    = (n : ℕ) → Hits[ ε n ] (f n) (μ n)
Hitsᴺ    f μ ε    = (p : ℕ → ℕ) → Poly p → Σ[ ν ] Negligible ν ×
                    ((n : ℕ) → Hits[ (λ q → ε n (p n) + ν n) ] (f n) (μ n))   -- or via GradedBound
```

## Transport along emulation (PROPOSED)

```agda
hits-transfer : f ≈ctx[ ε ] subᶠ s g → Hitsᶠ[ δ ] g μ
              → Hitsᶠ[ λ n q → ε n q + δ n (simCost q (cost s n)) ] f μ
```

The monitor lives on `B`, the simulator on the grade `X`; both are certified processes
plugged into the test, so the step is `≈ctx-ext`/`≈ctx-sub` (`Family.agda:243`) followed by
one triangle inequality in the observation space. It is the whole of `uc-preservesᴺ`
(`UC/Asymptotic.agda:80`) and the reason `≤UC^ωⁿ⇒≈negl` exists. Estimated proof: under
20 lines. Its `Canonicalᴺ` packaging is not needed for the ledger; `≤UC^ωᵉ⇒≤UCᴺ`
(`Asymptotic/Family.agda:256`) stays for consumers that want the qualitative corollary.

## Lift from the strategy level (the only step with proof risk)

`Birthday.target` is a strategy-level bound: `asks≤ q d → PrHit … ≤ εbirthday q`. The
setup-level bound needs it against every budgeted CONTEXT. `dominatedᵒ`
(`UC/Model/Dominated.agda:127`, type `ContextDominatedᵒ:115`) is exactly that lift for a
two-sided `≈ₚ[ ε ]` between two closed processes at any positive slack `δ`, reading the
strategy budget as `ctxBudget c c′`. What `Hits` needs is the one-sided variant:

```agda
dominated-hitsᵒ : (X E m qE qm) (u : Proc unitᴵ B) (μ) (ε δ) → 0 < δ
                → ((d) → asks≤ (ctxBudget c c′) d → Pr (runᴹ u (μ-watch d)) ≤ ε)
                → Pr (Obs ((flag E ∘ T₁ᵒ X (gradedᵒ (id ⊗ μ ∘ conjᴵ u))) ∘ m)) ≤ ε + δ
```

`dominatedᵒ`'s proof is `dominated` (finite-strategy domination) plus `ctxRunᵒ`
(`Dominated.agda:104`), which rewrites the context run as a strategy run. Both are
one-sided-agnostic: `dominated` bounds the distance to a fixed distribution, and a bound
`Pr ≤ ε` is `≈ₚ[ ε ]` to the point mass at `false` with one direction unused. Expected: a
restatement of `dominatedᵒ` with `v := ⊥-answering` or a direct one-sided proof of the
same size, ~40 lines. The spike must confirm that `μ`'s flag survives `ctxRunᵒ`'s
rewriting; if the flag has to be read off a state instead, the design is wrong and stops.
`Observable.auditWatch-bounded`/`-sound`/`-complete` (`Examples/ChimericLedger/Observable.agda`)
become the ledger's instance of the monitor's soundness and completeness.

## The event, and the ledger restated

The event is "the total reported by an audit at the end differs from the initial total".
An environment observes only answers, so "value at the end of the trace" is read through
the audit query: this is the interface-observable form ruled on 2026-09-21
(`docs/end-to-end.md`). The state-trajectory form stays the flagged appendix. Concretely
`μ` is today's `auditWatch` (`Observable.agda:81`) as a relay process with a flag port.

```agda
PreservesValue R = Hitsᴺ (imgᶠ R) auditMonitor εᴸ                     -- Property.agda
ideal-preserves-value : SerInj → PreservesValue Ideal                  -- via dominated-hitsᵒ + target
preserves-value-transfer : R ≤UC^ωⁿ Ideal → PreservesValue R           -- hits-transfer
ledger-preserves-value-from-hash : hash ≤UC^ωⁿ oracle^ω → PreservesValue (Realᴴ hash …)
chimeric-loses-value : Pr … ≡ 1ℚ                                       -- unchanged event, new spelling
```

## Retirement

| module / block | LOC | fate |
|---|---|---|
| `UC/Saturated.agda` | 212 | delete |
| `UC/Asymptotic.agda` | 101 | delete (`_≤UC^ω_` has no consumer since 2026-09-21) |
| `UC/Asymptotic/Family.agda`: `Systems` import, `≤UC^ωⁿ⇒≈negl`, `imgᶠ`'s `Systems` telescope | ~40 | restate `_≤UC^ωⁿ_` on images; delete the `≈negl` bridge |
| `Examples/ChimericLedger/Observable.agda` | 242 | shrink to the monitor process and its soundness/completeness, ~120 |
| `Examples/ChimericLedger/Property.agda`, `Transfer.agda` | 99 + 193 | restate; the appendix theorem keeps its type via the new vocabulary |
| `Protocol/Observe.agda`: `Pr`, `PrHit`, `_≈adv[_]_`, `transfer-at` | check | keep what `Protocol/Safety` and the game layer use; delete what only `Saturated` used |

Expected net: about −350 in the library, roughly neutral in the example.

## Plan

1. Spike, one agent, read-and-typecheck: fix the spelling of `flag E` and of the monitor
   `μ`; state `Hits[_]` at the single level; prove `dominated-hitsᵒ` (or show that
   `dominatedᵒ` at a `false`-answering `v` gives it). Stop and report if the flag cannot be
   read off the context run.
2. `Hitsᶠ`/`Hitsᴺ` and `hits-transfer` in `UC.Quantitative.Family`; a `Filt`-side reading
   via `Agreeᵠ` only if it falls out for free.
3. Restate `Property`/`Transfer`/`Observable`; statements of the appendix theorem and of
   `chimeric-loses-value` keep their meaning, spelled in the new vocabulary; `docs/end-to-end.md`
   follows.
4. Delete `UC.Saturated`, `UC.Asymptotic`, the `≈negl` bridge; restate `_≤UC^ωⁿ_` on images;
   fix the cross-references (`UC.agda` inventory, `UC/Audit.agda`, `UC/Seam.agda`).
5. Closure: root, `Examples/ChimericLedger/{Transfer,Replay}.agda`, the three test suites;
   hatch grep stays 16; warm times of the touched modules within budget.

Risks: the flag-threading spelling (step 1) is the design's load-bearing detail; `Pr` on
`Dₚ Bool` may need a small `Approximation` instance for one-sided bounds if `≈ₚ[_]` is the
only distance available; `_≤UC^ωⁿ_`'s consumers (`Transfer.agda`, `Ingest`) must not change
type when its telescope moves from `Systems` to images.
