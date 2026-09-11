# Abstraction notes for `protocol-rewrite`

These notes refine the recommendations in `protocol-rewrite-theory-review.md`. The governing constraint is that a general UC setup need not support quantitative observations. Rational advantage, query counts, security parameters, and probability distributions must therefore belong to optional models or enrichments, not to the general UC abstraction.

## Implementation reconciliation (`6256a140`, 2026-09-11)

These are architectural recommendations, not a claim that every displayed
interface has been implemented. The current source comparison and completion
criterion are in [Protocol rewrite implementation review](protocol-implementation-review.md).

The qualitative/quantitative split, machine model, adequacy, resource closure
proofs, and bounded-context domination have landed. The inherited UC model and
the generic family `UCSetup` are constructed. The repaired unit-grade carry
and `AuditIsBounded` also have proofs.

The preservation vision remains incomplete. The generic saturated/robust-property
API below is absent; the concrete `AuditBound` does not distinguish the audit
event from an arbitrary test verdict; and `UC.Saturated` uses vanishing rather
than negligible slack. Its proposed preservation statement additionally asks for
one slack uniform over all query counts from a premise controlling only
polynomial allowances. The family observation itself is vanishing equivalence,
so changing only the slack predicate would not repair negligible preservation.

The sketches below should be read subject to these corrections. In particular,
the target is an end-to-end theorem consuming the actual ideal ledger bound and
a genuine simulator-bearing UC premise, with explicit resource accounting and
a truthful audit-to-trajectory connection, not an assumed direct agreement.

## Diagnosis

The recurring problems occur at boundaries:

- `Strat` describes finite, well-bracketed experiments, while `Proc` permits arbitrary `Dₚ` machines.
- `QB` gives one scalar rate for a whole morphism, while the concrete theorem needs the number of interactions with one distinguished hole.
- UC emulation is qualitative and simulator-based, while the current POV carry is direct and quantitative.
- POV begins as an internal trajectory property, while UC preserves externally observable behaviour.
- The direct protocol evaluator uses `Dist⊥`, while machine semantics uses `Dₚ`.

These do not call for replacing the protocol or machine layers. They suggest separating general UC from model-specific resource, probability, and verification structure.

## 1. A qualitative UC core

The general observation structure should expose only observational equivalence on closed systems:

```agda
record Observation (𝒞 : Category ...) : Set ... where
  field
    𝟙 Ω      : Obj
    _∼_      : (𝟙 ⇒ Ω) → (𝟙 ⇒ Ω) → Set
    isEquiv  : IsEquivalence _∼_
    resp-≈   : f ≈ g → f ∼ g
```

An explicit observation carrier may remain useful, but an ε-indexed rational relation should not be required. Generic environment agreement remains equivalence under every ancilla, test, and closure, and simulator-based emulation remains qualitative:

```agda
f ≤UC g = Σ[ s ] f ≈ℰ sub s ∘ g
```

The grading action belongs here because adversary interfaces and simulators are intrinsic to UC. Quantitative approximation does not. The present observation record should be split into a qualitative `Observation` and an optional `ApproximateObservation` enrichment.

## 2. Preservation of saturated properties

The fundamental UC carry should concern properties invariant under observational equivalence:

```agda
record SaturatedProperty : Set ... where
  field
    Holds : ClosedSystem → Set
    resp  : x ∼ y → Holds x → Holds y
```

For open resources, the property must be robust under admissible closing and adversarial contexts. The generic theorem then has no probability or error term:

```agda
uc-preserves :
  f ≤UC g
  → Robust Φ g
  → Robust Φ f
```

The simulator is handled by robustness of the ideal property: its quantification includes the context obtained by composing with the simulator. This should be the general solution to the missing simulator-aware carry. Numerical POV transfer is a concrete corollary.

## 3. Optional quantitative observation

A probabilistic model can add:

```agda
record ApproximateObservation (O : Observation ...) : Set ... where
  field
    Error    : Set
    _≈[_]_   : Closed → Error → Closed → Set
    zero     : ...
    sym      : ...
    compose  : ...
    weaken   : ...
    induces  : ...
```

The error object should not be fixed by the general interface. The `Dₚ` model may use rational slack; another model may use a different notion or provide no quantitative enrichment.

The asymptotic family should construct the qualitative equivalence consumed by the UC core:

```text
quantitative closeness + negligible error
                    │
                    ▼
       qualitative observational equivalence
```

Cofinality of `κ` remains essential in this asymptotic construction, but is not a requirement of general UC.

A concrete POV property should be formulated in a saturated form, for example:

```text
POV-modulo-negligible P =
  ∀ polynomial allowance p,
  ∃ negligible ν_p,
  ∀ n d, asks≤ p(n) d →
    PrHit (P n) (Bad n) d ≤ birthdayBound n (p(n)) + ν_p(n)
```

The slack is chosen after the polynomial allowance, not uniformly over arbitrary
query counts. This is a target trajectory conclusion, not by itself an
observationally invariant predicate: environments do not observe internal state.
The probabilistic model must prove invariance of the corresponding observable
audit property under a relation strong enough to preserve negligible slack.
Generic UC can then transport that property without mentioning probabilities,
and the real implementation's truthful audit connection recovers the trajectory
conclusion. These preservation and integration results are not yet implemented.

## 4. Optional resource and adversary structure

Natural-number query bounds should also remain outside the general core. UC may be parameterized by an abstract admissible environment class:

```agda
record AdversaryClass (U : UCSetup) : Set ... where
  field
    Admissible : Environment A → Set
    identity   : ...
    compose    : ...
    regrade    : ...
```

Models may instantiate this using polynomial query bounds, syntactic finiteness, time bounds, or all environments.

For the concrete protocol reduction, a whole-morphism scalar `QB` is insufficient. What is needed is specific to the distinguished protocol hole:

```agda
HoleUses≤ : ℕ → Experiment B → Set
```

This prevents a zero-bounded ancillary closure from erasing real queries into the hole. A port-indexed or matrix grade could later derive such bounds compositionally:

```text
tensor       = block sum
composition  = matrix multiplication
bypass       = identity block
hole budget  = selected matrix entry
```

An operational `HoleUses≤` certificate is preferable for the first implementation.

## 5. Experiments as a concrete presentation

Finite experiments are a verification frontend, not the general definition of UC environments:

```text
finite Experiment syntax
        │ compile
        ▼
admissible environment in the Dₚ model
```

The central model theorem is:

```agda
experiment-adequacy :
  directRun e P
    ≈
  machineRun (compileExperiment e) (morphism P)
```

Users can state executable probability bounds over `Protocol` and `Experiment`; compilation and adequacy connect them to the categorical model.

For arbitrary `Dₚ` contexts, either define admissible contexts as compiled experiments and their observational closure, or separately prove a density/completeness theorem for a larger machine class. `Reflects` belongs to the second option, not to the definition of UC.

A universal preservation statement is preferable to an existential maximizing strategy:

```agda
((d : Strat ...) → asks≤ q d →
   runᴹ u d ≈ₚ[ ε ] runᴹ v d)
→ ctxRun C u ≈ₚ[ ε ] ctxRun C v
```

It consumes the statement supplied by a protocol proof and avoids constructive extraction of an exact optimum.

## 6. Relating `Dist⊥` and `Dₚ`

Both probability carriers remain useful:

- `Dist⊥` supports finite exact execution.
- `Dₚ` supports unbounded probabilistic machines and traces.

Their relationship should be an explicit embedding or generic interpreter theorem:

```agda
embed : Dist⊥ A → Dₚ A

run-embed :
  runᴹ (morphism P) d ≈ₚ embed (run P d)
```

Ideally, protocol execution is defined once against a small probabilistic interpreter interface and instantiated at both carriers. `PrAgree` then follows from interpreter naturality.

## Proposed layering

| Layer | Contains | Does not assume |
|---|---|---|
| General UC | category, grading, qualitative observation, environments, simulators, saturated-property preservation | probability, rationals, natural-number bounds, negligible functions |
| Adversary doctrine | abstract admissibility and resource-closure laws | a particular cost algebra |
| Probabilistic UC model | `Dₚ`, approximate observation, polynomial bounds, asymptotic families | finite protocol syntax |
| Verification frontend | `Protocol`, `Strategy`/`Experiment`, exact `Dist⊥` evaluation, compilation and adequacy | completeness for arbitrary machine contexts |

## Consequences for the current findings

- The live-genesis correction remains valid and local.
- Cofinality belongs in the asymptotic probabilistic instance.
- The zero-budget multiplication is a defect in the concrete resource doctrine, not the UC core.
- The finite-`Strat` versus arbitrary-`Dₚ` question becomes an optional model-completeness theorem.
- Simulator-aware carry becomes generic preservation of saturated, robust properties.
- `Agreeˢ` and numerical transfer become concrete corollaries.
- Rational ε-closeness should no longer be required by the general `UCBase`.

The recommended refactor is targeted: preserve direct protocol semantics, the `Dₚ` machine category, simulation equality, grading action, and ledger work; separate qualitative UC from its probabilistic and resource-enriched realizations before proving the expensive bridge obligations.
