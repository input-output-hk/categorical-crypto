# UC preservation through the existing presheaf action

> **Executed; §5's dispositions are historical as of 2026-09-21.** Steps 1–7
> landed ([presheaf-action](presheaf-action.md),
> [direct-extraction](direct-extraction.md),
> [consumer-migration](consumer-migration.md), [retirement](retirement.md)),
> and the retirement arc since deleted several modules §5 asked to keep —
> `UC.Model.Bridge`, `UC.Model.Reading`, `UC.Model.Family.Uniform`,
> `UC.Emulation` — against replacements in `UC.Core.Bridge`.

Implementation plan against `protocol-rewrite` at `d461b1fa`. This covers the
family-premise and property-preservation work discussed in the review, with the
associated simulator-cost and uniformity obligations. It is not a request to
implement a second experiment category or rewrite the machine semantics.

The branch already contains family ingestion, local negligible observation,
qualitative robustness, prefix-tolerant probability extraction, and ledger/hash
factoring. Reuse those proofs. The changes below consolidate their structural
arguments and make the intended generic/model boundary explicit.

All paths are relative to `src/CategoricalCrypto/`, unless prefixed by `src/`
or `docs/`. Signatures omit universe levels and some implicit parameters; names
marked as proposed are not compiler-checked declarations.

## 1. Architectural decisions

1. Use `UCSetup`, `Abstract2.AbstractUC`, and the existing graded Kleisli action
   as the generic theory. Preserve `_≈ᵁ_` and the inherited `_≤UC_` quantifiers.
2. Environments are elements of the setup's existing presheaf. Absorbing a
   simulator is that presheaf's action on `sub`, not an independent operation.
3. Do not introduce generic `Simulator`, `ClosingContext`, `MonitoredExperiment`,
   or `Monitor` records. Simulators remain grade morphisms, tests/closures remain
   the model's existing morphisms, and the ledger monitor remains a concrete
   `Strat → Strat` transformation.
4. Keep `Strat` as executable finite syntax and retain its interpretation and
   adequacy. An arbitrary simulator need not compile back into finite syntax.
5. Quantitative errors and query certificates are optional model enrichment,
   not fields of `UCSetup`. Retain witnesses until the quantitative consumer
   finishes; forgetting them into qualitative agreement is one-way.
6. One semantic family category can support several observation instances.
   Vanishing and negligible observations are different relations, not competing
   operational semantics. Their distinction is not duplication to erase.

## 2. What holds for every UC setup

Make the `UCSetup`-parameterized content the canonical `UC.Robust` API. Preserve
the independently scoped old `UCBase` theorem as described in section 3.1.
Keep the small presheaf-action helpers in that module initially; split them out
only if a second independent consumer needs them.

An arbitrary setup provides `𝒞`, the monoidal grade category `ℐ`, its graded
Kleisli triple, and `ℰ : Presheaf 𝒞 Setoids`. It need not provide a verdict
object, a closed-run observation, an identification of grades with `𝒞`-objects,
or invertible multiplication. None of those may enter the generic proofs.

### 2.1 Reuse the existing action

Use abbreviations, not records:

```text
Env D       = carrier of ℰ(D)
u ≈Env v    = equality in the setoid ℰ(D)
pull h e    = ℰ(h)(e)

A, B : objects of 𝒞
W, X, Y : objects of ℐ
f : A → T_X B
s : Y → X

prefix W f = μ W X ∘ T₁ W f
           : T_W A → T_(W ⊗ X) B

run W f e = pull (prefix W f) e
          : Env (T_W A)
          where e : Env (T_(W ⊗ X) B)

regradeEnv W s e = pull (sub (id_W ⊗ s)) e
                : Env (T_(W ⊗ Y) B)
```

The direction is contravariant: `s : Y → X` changes a grade-`Y` resource into
a grade-`X` resource, while it pulls a grade-`X` environment back to grade `Y`.
`run` is presheaf-valued, not a probability or closed observation.

Prove these proposed lemmas:

| Lemma | Statement/content | Existing proof ingredients |
|---|---|---|
| `run-sub` | `run W (sub s ∘ g) e ≈Env run W g (regradeEnv W s e)` | `Abstract2.sub-decomp`, presheaf equality respect, contravariant composition |
| `run-resp-≈ᵁ` | `f ≈ᵁ g` implies agreement of `run W f e` and `run W g e` for every `W,e` | Evaluate the kernel equality in `Abstract2._≈ᵁ_` at `e` |
| `runs⇒≈ᵁ` | Agreement of all these runs implies `f ≈ᵁ g` | Construct the kernel equality at each `W` |
| `≤UC⇒dummy` | `f ≤UC g → Σ s. f ≈ᵁ sub s ∘ g` | Instantiate at `ℐ.id`, then normalize `sub id ∘ f` with `sub-identity` |

`dummy-complete` already proves the converse of `≤UC⇒dummy`. Put the new
direction beside it in `Abstract2` if it removes the repeated identity-adversary
normalizations there and in consumers. Do not add another dummy-adversary order.

The first law is the proposed `absorbExperiment` correctness theorem with the
unnecessary experiment representation removed. The pair of run-agreement laws
ensures that this presentation retains the full U-kernel: it does not silently
replace `_≈ᵁ_` with the weaker bare kernel `_≈ℰ_`. No `GradeStable` premise is
needed for these statements.

### 2.2 Saturated properties of presheaf elements

Generalize the existing `SaturatedProperty` record to a presheaf fiber:

```agda
record SaturatedProperty (D : 𝒞.Obj) where
  field
    holds     : Env D → Set p
    saturated : u ≈Env v → holds u → holds v
```

For fixed `A,B`, take a property family and an optional admissibility predicate:

```text
P   : (W : ℐ.Obj) → SaturatedProperty (T_W A)
Adm : (W X : ℐ.Obj) → Env (T_(W ⊗ X) B) → Set d

Robust P Adm f =
  ∀ W e, Adm W X e → holds (P W) (run W f e)
```

`P W` deliberately does not depend on the resource grade `X`, which changes
when the simulator moves. A grade-dependent property would require a separate
property-transport premise. Do not hide that premise in the definition.

For one simulator, the closure obligation is a predicate, not a new action:

```text
ClosedUnder Adm s =
  ∀ W e, Adm W X e → Adm W Y (regradeEnv W s e)
```

If admissibility is advertised as a subset of the environment setoid, also
prove it respects `≈Env`. This is representation independence; the preservation
proof itself uses the exact pulled-back element.

Prove:

```text
robust-resp-≈ᵁ :
  f ≈ᵁ g → Robust P Adm g → Robust P Adm f

robust-sub :
  ClosedUnder Adm s → Robust P Adm g → Robust P Adm (sub s ∘ g)

uc-preserves :
  (∀ s, ClosedUnder Adm s)
  → f ≤UC g → Robust P Adm g → Robust P Adm f
```

The proofs are saturation, `run-sub`, and the normalized dummy witness. Also
derive the adversary-attached conclusion by using `le a` directly, keeping
`Abstract2._≤UC_`'s quantifier order.

Export a preservation lemma at an explicit witness `s` as well as the
all-simulators corollary. Fixed-budget context classes will not be closed under
arbitrary simulators; they must not obtain closure merely from `f ≤UC g`.
`Adm = ⊤` recovers unrestricted qualitative robustness, but does not assert
that a nontrivial safety bound holds under all arbitrary verdict tests.

### 2.3 What this does not prove generically

No arbitrary `UCSetup` can establish any of the following:

- a numerical bound or negligibility;
- a query count for a pulled-back environment;
- that a designated ledger test remains a ledger test after simulation;
- a relation between internal trajectories and external observations;
- that an arbitrary simulator is silent or has total initialization.

These are enrichment or instance obligations. The generic theorem makes them
visible instead of encoding them in another experiment category.

## 3. Observation-generated setups and the machine model

### 3.1 Recover the current operational reading

`UC.Environment.Presheaf` remains the constructor of an environment presheaf
from a closed observation. At such an instance, `Env D` is represented by a
test `D → Ω`; its equality quantifies over closing morphisms `𝟙 → D`.

For an observation-invariant predicate `Q`, define the adapter:

```text
holds (P W) t = ∀ m : 𝟙 → T_W A, Q (observe (t ∘ m)).
```

Its saturation is exactly the test-setoid equality, evaluated at each closure.
This adapter is not part of the theorem for all UC setups: some setups have no
such presentation.

This adapter quantifies over all input closures. Environment-only `Adm` does
not automatically express an admissibility condition depending jointly on a
particular test and closure. Preserve such conditions in direct model lemmas,
or prove a suitable encoding for the application; do not silently broaden the
closure quantifier to fit the generic theorem.

At the machine model and its family, use the existing standard-grading
rebracketing to identify `prefix W f` with the operational context expression.
The argument uses the model's associator; do not require `μ` to be invertible
in the generic layer. Reuse `UC.Core.Bridge`, `UC.Model.Reading`, the family
bridge, and the seal transports rather than redoing their machine proofs.

`UC.Robust.Model.uc-preservesᵒ` then becomes a direct instance of the generic
theorem. Its current detour through `≤UC⇒≤UCᶜ` disappears from this proof.
Preserve its meaningful acceptance tests through the adapter. The old ungraded
`⊤-robust` signature is not definitionally the new graded one: either keep it
as an observation-specific consequence or migrate its test explicitly.

Recovering this model instance does not recover the old preservation theorem
for every `UCBase`, or its robustness predicate on arbitrary ungraded homs.
An arbitrary `UCBase` does not supply a graded Kleisli triple, and an arbitrary
`UCSetup` need not supply a closed observation. Keep the old generic proof
content in an observation-specific module unless a scope-preserving replacement
is supplied. This retains an independently scoped result, not another category
or independently implemented UC metatheory.

### 3.2 Keep the existing probability relations distinct

The local negligible observation is already implemented in
`UC.Approximate.Local` and `UC.Family.Negligible`. Keep it and its one-way
bridge. Instantiate inherited `UCSetup`/`Abstract2` for public negligible UC;
avoid making the renamed `UC.Emulation` metatheory another public route.

Use one underlying family category and grading, with appropriately named
observation instances. A second observation on that category is not a second
locally graded operational category. In particular, do not delete the local
negligible observation to make the module count smaller, or claim that its
per-context relation equals the stronger uniform relation.

The quantitative relation remains a relation on concrete runs/context
representatives with explicit evidence. It is not automatically a distance on
the coarse vanishing-observation quotient. Do not assert respect for that
quotient when it would discard the very error rate the relation retains.

### 3.3 Consolidate the quantitative family presentation

Generalize the explicit contextual relation currently in
`UC.Asymptotic.Family._≈ᶠ[_]_` from closed unit-grade protocol images to
families of graded semantic morphisms. Use the generic `prefix` expression and
the model's existing observation and query certificates. The schematic meaning is:

```text
f ≈ctx[ε] g =
  ∀ n W E m c c′,
    QB c E → QB c′ m →
    observe(E ∘ prefix W (f n) ∘ m)
      ≈[ε(n, contextCost(c,c′))]
    observe(E ∘ prefix W (g n) ∘ m).
```

Rebracket the test to the inherited `μ`-shaped endpoint, using the model
dictionary once. The adapter must transport query certificates as well as
observations: prove its actual cost and resulting allowance, rather than infer
preservation of the same `ε`-indexed relation from an uncosted isomorphism.
Use the existing `ctxBudget` with its proved bound unless a sharper operational
bound is separately established.

Make both the packaged `UC.Family._≈ℰ[_]_` presentation and the protocol-image
presentation use this one definition where their context quantifiers coincide.
Where one quantifies all levelwise contexts and the other only polynomial
families, retain a named implication rather than claim definitional equality.

Do not silently add `PolyQB` premises for compared systems. The current
unpackaged relation reads the context budgets, not the resource families' own
certificates. Preserve that domain. Entering the existing budgeted family
category may still require `Imageᶠ` certificates: prove them where possible,
otherwise keep the packaging adapter and its premises explicit. Having a raw
presentation and a certified subcategory is not a second operational semantics.

For an explicit simulator family, quantitative realization is just a witness
using the existing morphisms and relation:

```text
∃ s,
  polynomial query certificate for s
  × NegligibleBound ε
  × f ≈ctx[ε] (sub s ∘ g).
```

Give the witness form and the adversary-quantified form the existing inherited
quantifier discipline. Prove their connection under the budget/action closure
laws; do not simply rename symmetric direct agreement as general emulation.
The present `_≤UC^ωⁿ_` is a useful direct-agreement specialization, not a
general simulator-bearing witness.

Prove model/enrichment lemmas for zero error, symmetry, triangle, and context
pullback with its cost. Then prove witness-retaining sequential and graded
composition by following `Abstract2`'s simulator construction and using these
quantitative lemmas at the comparison steps. Algebraic rearrangements reuse
`sub-decomp`, `∙-decomp`, and existing hom equalities; there is no new graded
category and no change to the qualitative UC theorem.

Separate relational transitivity from plugging other processes around a
relation. For graded composition, moving a continuation into a test or an
earlier process into a closure requires certificates for those actual
morphisms, not only for the simulator. State quantitative congruence lemmas
with those process/continuation certificates and their allowance substitutions.
The raw contextual relation may still compare uncertified resource families;
extra hypotheses on its quantitative composition theorem do not change that
domain. Keep unconditional qualitative `Abstract2.UC-compose` intact.

Error reindexing must be proved. If a new certificate yields only an upper
bound on cost, using `ε(n,q) ≤ ε(n,q′)` requires an explicit monotonicity
premise or a proved monotone envelope; arbitrary `ε` is not monotone by fiat.
Alternatively, retain the exact certificate-derived allowance in the theorem.
Prove negligibility after the polynomial substitutions actually used by
simulator composition and audit instrumentation.

The final property remains allowance-uniform. Derive it from retained uniform
quantitative evidence, not by exchanging `∀ context, ∃ negligible error` for
`∀ allowance, ∃ negligible error, ∀ strategy`. Qualitative forgetting is a
corollary at the end of a quantitative proof, never an intermediate step used
to reconstruct the rate.

## 4. Migrate the audit proof, not the experiment representation

### 4.1 Extract the useful direct model lemmas

Keep `auditClose`, `auditTest`, `audit-qb`, and `audit-run` from
`UC.Seam.Audit.Context`. They already interpret an arbitrary finite strategy
and identify its run and cost. Instantiate them at the ledger's existing
`monitor (audited d)`; no generic monitor record is needed.

Refactor the numerical part of `Context.extract` into a direct observation
lemma: a bound or one-sided domination on this context's observation implies
the desired `Pr` bound. Its statement should not require `AuditEvent`
membership. Keep the `PrAgree`, budget matching, and rational-order arguments
in `Bounded`; these are model-specific and do not disappear by functoriality.

### 4.2 Move structural sliding to the generic action

In the model, `regradeEnv` is represented by precomposition with
`sub (id_W ⊗ s)`. Identify its operational spelling once. Replace repeated
`T₁`/composition slide proofs in qualitative robustness with `run-sub`.
For numerical consumers, retain the representative-level categorical equality
from `sub-decomp` and apply exact observation/advantage transport to it. Equality
in the vanishing or negligible presheaf setoid alone does not retain a specified
error or exact mass bound, so it cannot replace that quantitative transport.

What remains for a designated safety property is not another action. It is
the property-specific statement that the transformed test is acceptable, or
that its bad-event mass is dominated by an acceptable ideal test. State that
lemma directly at the existing test, closure, monitor transformation, and
budget witnesses.

For a qualitative property expressible by environment-only admissibility and
a saturated fiber predicate, this is an instance of `ClosedUnder Adm s` plus
saturation. Joint test/closure conditions need a proved encoding or a direct
model statement. For a bound, retain the explicit allowance change and, if
necessary, an approximation error. A numerical predicate at a fixed bound need
not be saturated under negligible agreement, so the quantitative transfer must
retain the error rather than pretend the qualitative theorem preserves it.

The existing `UC.Audit.audit-carry` is more general than the ledger use: it works
over arbitrary `UCBase`/`Budget`/`Mass` and two test-closure-budget predicates.
The new `UCSetup` qualitative theorem does not subsume that whole statement.
Retain its generic quantitative content, either in place or as a direct
predicate-parameterized transfer with the same scope and implication premise.
Do not delete it merely because the ledger consumers no longer use its names.

### 4.3 Preserve the scalar-prefix theorem

The prefix-tolerant route is now implemented. Reuse `subPrefixedˢ`,
`Prefixedᵒ`, `prefixedᵒ-bind`, `ASTotal`, and the probability extraction
arguments in `UC.Seam.Audit.Prefix`.

Restate their application consequence directly: after the appropriate totality
premise, the simulator-prefixed ideal monitored observation has the needed
one-sided mass bound. Use that consequence with quantitative emulation and
`audit-run`, without passing through `watchedᵖ`, `absorb`, and membership
records in the public probability theorem.

This changes the proof route, not its hypotheses or numerical conclusion.
Keep the present pointwise and family conclusions, including the bound at
`simCost (q + q) (cs n)`, as migration tests. Do not replace it by an uncharged
bound and claim the same theorem, or erase the initialization-totality premise.

### 4.4 Nontrivial grades remain genuine application work

The same generic action handles `s : Y → X` at nontrivial grades. The scalar
lemma does not. Prove separately that the existing ledger/resource interface
and monitored test admit the simulator's actual interaction at the adjusted
budget. If that requires exposing an oracle-facing grade, change the
application interface explicitly; assigning a positive budget to `unit → unit`
does not perform this task.

Prove an example in which a simulator actually issues a query through an
inhabited port. Reuse the ordinary grading action and query certificates.
Neither a new simulator datatype nor a new category is needed.

### 4.5 Finish at the ledger and hash boundary

The ideal supply should be the already-proved birthday-to-monitor bound,
read directly through the model lemma. The real side uses the existing
truthful-audit inequality and `asks≤-audited`. The proof chain becomes:

```text
quantitative family emulation
  → compare real test with simulator-transformed ideal test
  → property-specific ideal-test bound at transformed allowance
  → real monitored probability bound
  → real trajectory bound via truthful auditing.
```

Keep the existing `UC.Factor` and ledger-factor equations. Use the new
quantitative composition theorem to lift a hash-level premise through the
ledger without first forgetting its error into qualitative UC. Preserve
serialization, dead-free/totality, and polynomial-cost premises explicitly.
Proving a particular cryptographic hash realization remains outside this plan.

## 5. Code disposition and retirement gates

Retirement is conditional on replacement proofs and importer migration, not on
the absence of a compiler error in a smaller statement. Do not delete proofs
merely because they are no longer on the main path.

| Current code | Change | Retirement gate |
|---|---|---|
| `Abstract2` and `src/Categories/LocallyGraded/Kleisli` | Retain the category, action, equality, UC relations and metatheorems; add the reusable dummy-witness direction if needed | No wholesale retirement |
| `UC.Robust` | Make preservation over `UCSetup` canonical | Move the independently scoped `UCBase` result to an observation-specific module; delete it only if its whole original scope is recovered, not merely the machine instance |
| `UC.Robust.Model` | Direct instance plus the observation-predicate adapter | Remove its `≤UC⇒≤UCᶜ` detour; move tests only if the remaining module is forwarding-only |
| `UC.Environment.Presheaf` | Retain as the observation-to-environment constructor | Not replaced by the generic theorem |
| `UC.Core.Bridge`, `UC.Model.Bridge`, `UC.Model.Reading` | Reuse for model identifications and migration | Remove individual obsolete wrappers only after all other consumers migrate; these modules still have independent work |
| `UC.Family.Negligible`, `UC.Model.Family.Negligible`, `UC.Approximate.Local` | Retain local negligible observation and one-way bridges; expose inherited UC rather than a parallel renamed `UC.Emulation` API | Retire redundant metatheorem reexports, not the distinct negligible semantics |
| `UC.Model.Family.Uniform` | Keep its real family/core identification until consumers use the canonical inherited presentation | Delete forwarding/conversion wrappers only when generic/model lemmas replace each use |
| `UC.Model.Dominated`, `UC.Model.Family.Ingest` | Retain model domination and ingestion; make outputs use the canonical quantitative relation | Redundant qualitative projections may retire after callers migrate; not the domination proof |
| `UC.Asymptotic.Family` | Specialize the canonical contextual relation and keep acceptance tests and run extraction | Retire duplicate relation algebra after replacing its proof content; do not silently strengthen its domain with image-budget premises |
| `UC.Audit` | Reuse the action laws where applicable; keep its generic quantitative content and resource/error arithmetic | Replace its API only after both importer migration and a direct quantitative theorem at the same `UCBase`/`Budget`/`Mass` scope, with arbitrary joint test-closure-budget predicates and two-class transfer, are supplied; otherwise retain it |
| `UC.Seam.Audit.Context`, `Bounded` | Keep context interpretation, cost, and probability extraction; remove event-class parameters from the direct path | Old membership-based supply/extraction lemmas retire only after equivalent direct statements serve all consumers |
| `UC.Seam.Audit.Prefix` | Keep the scalar-prefix proof and direct mass consequence | Retire `absorb-watchedᵖ`/membership plumbing after the unchanged probability endpoint is recovered |
| `UC.Seam.Audit` | Reduce to necessary direct adapters, or remove if it becomes forwarding-only | `watched`/`watchedᵖ` and `TrivialGrade` retire after exact and prefix consumers migrate |
| `UC.Asymptotic.Audit` | Specialize one quantitative transfer path | Retire `uc-audit-carry` returning only `AuditBound`; keep existing probability results as proved specializations until migrated |
| `UC.Factor` and ledger factoring | Retain actual categorical factor equations; use witness-retaining composition for quantitative lifting | No deletion of factoring or coherence proofs merely to shorten the route |
| `Examples/ChimericLedger/Audit` | State ideal monitored bounds directly through existing source theorems and the new adapter | Remove `auditEvent`/`AuditBound` exports after the final consumers migrate; merge the module only if no distinct proof content remains |
| `Examples/ChimericLedger/EndToEnd`, `Real`, `Factor`, `Carry` | Preserve current conclusions; assemble family, prefix, and factoring results through the reduced API | Delete redundant demonstration/wrapper exports only after importer checks and replacement endpoint checks |

The retirement target is the duplicate structural proofs and the
application-facing pullback-membership detour, not the existence of selected
context predicates or the generic quantitative theorem. Removing type aliases
without removing a conceptual duplication is not a worthwhile migration by
itself.

During migration, temporary wrappers are justified by actual in-repository
callers. Remove them in the final pass unless a concrete external consumer
requires compatibility. Do not retain an entire second metatheory as a wrapper.

The `Dₚ` model, machine simulation/trace/G-construction, finite protocol
interpreter, `Strat`, adequacy, query counting, mass calculus, ledger kernel,
trajectory proof, and birthday proof are retained. This plan changes their
assembly, not their semantics.

## 6. Implementation order and checks

1. **Generic action.** Prove `run-sub`, both directions of run agreement versus
   `_≈ᵁ_`, and the dummy-witness helper. Typecheck a module parameterized only
   by an arbitrary `UCSetup`. Check explicitly that grades and category objects
   remain distinct parameters and no `Observation` or `GradeStable` is imported
   as an assumption.
2. **Generic preservation.** Make the new theorem canonical and recover the
   existing model tests, preserving the independently scoped `UCBase` theorem
   separately. Add one selected-environment example with a real closure proof;
   the top predicate alone is not meaningful acceptance coverage.
3. **Quantitative consolidation.** Generalize one contextual relation; connect
   existing packaged and unpackaged presentations without altering domains.
   Preserve the local-negligible and uniform-negligible distinction. Re-run
   `UC.Approximate.LocalTests` and the `Asymptotic.Family` separation results.
4. **Quantitative action/composition.** Prove the actual allowance substitutions,
   error addition, and negligible closure, retaining explicit simulator
   witnesses and any certificates for processes moved into contexts. Derive
   qualitative forgetting only afterwards.
5. **Direct model extraction.** Refactor `Context`/`Bounded`/`Prefix` while
   preserving ordinary and prefix-tolerant probability conclusions. Reuse the
   already-landed seal transports and domination; do not reprove them as new
   architecture.
6. **Consumer migration.** Preserve `ledger-uc-to-pov-family`,
   `ledger-pov-family-negligible`, `ledger-uc-to-pov-simCost`, and
   `ledger-pov-simCost-negligible`, then migrate the real/hash-level corollaries.
   Add the nontrivial interactive-grade application separately from the scalar
   specialization.
7. **Retirement.** Search importers of every retired name, remove only the
   layers listed above whose gates are satisfied, and check affected test
   suites, `UC`, and `CategoricalCrypto`. Update public entry points and docs.

Each replacement must typecheck the unchanged consumer conclusion with its
existing hypotheses. New stronger or more general results get distinct
statements; do not weaken old statements merely to make migration pass. Follow
the repository's safe-Agda, timeout, heap-pairing, warning, and importer rules.

Completion means the public proof uses one inherited graded action and one
presheaf interpretation, with model-specific probability and cost lemmas where
needed. No proof should need a parallel experiment category, a simulator wrapper
with its own laws, or a pullback event definition standing in for the concrete
property-stability argument.
