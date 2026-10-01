# Chimeric ledger: proof boundaries and concrete acceptance results

## Scope

Four bounded work items strengthen the ledger example independently of the
larger question of which real-hash security assumption is intended:

1. Expose the deterministic conservation argument and its collision boundary.
2. Generalize the replay counterexample and relate it to the family property.
3. Keep observable safety, audit truthfulness, and progress separate.
4. Supply a concrete injective transaction serializer.

The hash-assumption question is explicitly deferred. Preserve the existing
conditional hash-replacement theorem and its premise; these tasks do not
discharge that premise or replace it with a different assumption.

This plan complements `docs/event-bounds-in-setup.md`. Event-sensitive
contextual adequacy remains that plan's work package, not a prerequisite for
the deterministic and strategy-level results here. Use the existing
strategy/watch vocabulary where it supplies the clearest proof interface.

Paths below are relative to `src/CategoricalCrypto/` unless prefixed with
`docs/`. The source entry points were inspected when writing this plan, but
proposed names and signatures are schematic. Recheck current definitions and
callers before implementation, and reuse existing invariant lemmas rather
than building a second proof alongside them.

## 1. Expose conservation separately from collision probability

### Objective

Make the following decomposition explicit at the public proof boundary:

```text
ledger transition rules + appropriate freshness/noncollision conditions
  → conservation of total value

random-oracle sampling
  → the required conditions fail with at most the birthday probability

audit soundness
  → the observable audit-event bound.
```

Start from `Examples/ChimericLedger.agda` and the existing invariant and
probability arguments in `Examples/ChimericLedger/Birthday.agda`. Identify
which part is already proved and expose or factor it at its natural home.
Do not introduce a general invariant framework merely to package the example.

### Work

- State the deterministic conservation lemma with the actual required initial
  well-formedness and transition conditions. Include the treatment of rejected
  transactions and existing output identifiers.
- Identify exactly where `inputConsuming` is used to rule out the replay that
  the chimeric variant permits.
- Distinguish the exceptional cases:
  - Repeating the same transaction or hash query.
  - Distinct transactions with equal serialization.
  - Distinct oracle inputs with equal digests.
  - A generated output identifier coinciding with an existing identifier,
    including identifiers present at genesis where relevant.
- Prove which cases are excluded by the ledger rules, which by `SerInj`, and
  which remain in the probabilistic bad event. Do not describe a repeated
  query as a collision between distinct oracle inputs.
- Have the existing birthday theorem consume the exposed deterministic
  result. Preserve the bound `(q² + q)·2⁻ⁿ` and its actual query convention
  unless a reviewed mathematical correction is needed.

### Acceptance

- The public conservation result can be stated without random-oracle
  probability calculations in its conclusion.
- The ideal probabilistic theorem uses that result rather than maintaining
  another conservation proof.
- The proof and a short explanation pinpoint why the repaired variant avoids
  same-transaction replay and which failures still require the birthday bound.
- Existing public theorem premises and numerical pins are preserved.

## 2. Generalize the replay counterexample

### Starting point

`Examples/ChimericLedger/Replay.agda` already supplies an executable one-bit
instance with constant serialization, an account-funded initial state, two
identical submissions, and an audit. It proves loss with probability one and
rejection by the repaired variant. Keep these readable computation tests.

The positive family theorem instead assumes `SerInj` and uses the specified
UTxO genesis. The existing finite instance is a concrete bug witness, not by
itself an asymptotic refutation under those same assumptions.

### Work

1. Prove the repeated-transaction attack at arbitrary hash width and arbitrary
   serialization where possible. The same transaction is serialized twice;
   the argument must not rely on distinct transactions having equal encodings.
2. Prove the required repeated-query behavior of the concrete lazy oracle,
   rather than replacing it by a constant hash for the general result.
3. Give the attack its query certificate. The two submissions followed by an
   audit have constant strategy query depth; account separately for any
   initialization prefix added below.
4. Resolve initialization explicitly:
   - Prefer a checked prefix reaching a suitable funded-account state from
     the intended genesis if the transition system supports one.
   - Otherwise retain the account-funded initialization in the negative
     theorem and state the distinction from the positive theorem. Do not
     claim that a result at a different initial state refutes the
     genesis-specialized property.
5. Prove loss through the same accumulated `auditWatch` event used by the
   public property. Reuse the result during the eventual monitor migration.
6. Where the attack and property share an initialization, derive failure of
   the corresponding family-level `PreservesValue` statement. Instantiate
   its polynomial allowance with the attack's bound and use negligibility
   of the birthday term and slack to contradict the nonnegligible attack
   probability. A single small-parameter numerical instance is not enough.

### Acceptance

- A family theorem names the actual attack, allowance, initialization, and
  observable event.
- The proof is compatible with injective serialization; it does not exploit
  the old constant serializer.
- The finite `refl` examples remain as regression checks.
- Any asymptotic negation concerns the same initialized family and event as
  its target property. If that cannot yet be established, report the precise
  missing reachability or initialization result instead of changing the
  target silently.

## 3. Separate observable safety, truthfulness, and progress

### Objective

Preserve the distinction already visible in
`Examples/ChimericLedger/Transfer.agda`:

```text
observable audit safety
  + implementation-specific truthful audit instrumentation
  → trajectory safety with its proved allowance transformation.
```

An upper bound on reported failures is not also a theorem that audits are
truthful or that the implementation answers. A flag set before divergence is
not a reported hit under the current event convention.

### Work

- Give the observable headline a precise description: it bounds a discrepant
  audit answer accumulated during an interaction and reported on termination.
  Avoid describing it as unrestricted internal-state conservation.
- Keep `TruthfulAudit` and its concrete ledger proof explicit. Reuse
  `Observable`'s soundness/completeness results rather than assuming a
  correspondence between arbitrary implementations' internal states.
- Preserve the trajectory appendix's `withAudits` instrumentation and the
  resulting doubled allowance. Keep this honest-interface cost distinct from
  the monitor compiler's flag-reading cost in the event-bounds plan.
- Keep useful behavior as a separate result. Generalize the existing
  `Replay.genesis-live` check to the intended parameterized genesis and
  initial spend where practical, proving both the relevant acceptance
  behavior and state effect. Do not infer global liveness from one accepted
  transaction or strengthen every safety theorem with a totality premise.
- Add or reuse focused semantic checks demonstrating that the safety
  predicate does not itself imply responsiveness, and that trajectory
  conclusions require the stated audit connection. Match existing public
  interfaces rather than adding an unrelated model of progress.

### Acceptance

- The observable safety theorem, audit-to-trajectory theorem, and positive
  behavior theorem are separately named and have explicit assumptions.
- Existing counterexamples and behavior checks retain their meaning through
  any event-bound migration.
- No hidden totality, truthfulness, or scheduler assumption is added to the
  headline property.

## 4. Instantiate serialization concretely

### Objective

`Examples/ChimericLedger/Property.agda` states `SerInj` explicitly. Provide
one concrete serializer and its injectivity proof so that the intended
example is not left only as a theorem parameterized by an encoding.

### Work

- Inspect the transaction representation and existing encoding libraries
  before defining another codec.
- Encode every component needed for literal transaction identity: variant
  tags where applicable, lists and their boundaries, natural numbers, hashes,
  indices, and values. Use an unambiguous encoding, not raw concatenation
  without proven boundaries.
- Prove injectivity for each security parameter. A decoder with a checked
  `decode (encode t) = just t` law is one suitable route if it fits the
  existing library.
- Instantiate `SerInj` and the existing ideal preservation theorem with this
  serializer. Keep generic theorems parameterized by serialization where
  useful; the concrete instance is an executable acceptance result.
- Exercise boundary cases that matter for injectivity, such as empty lists,
  component boundaries, and zero-valued fields.

Do not identify transactions modulo an unstated normalization or permutation
equivalence. If the intended encoding is canonical for a quotient, specify
that semantic choice separately; the current `SerInj` asks for literal
transaction equality.

### Acceptance

- A concrete family `ser n` and its `SerInj` witness check.
- A public ideal-ledger result uses that witness rather than accepting it as
  an argument.
- The general replay theorem can be specialized to the same serializer.
- Serialization ambiguity and digest collisions remain separate obligations.

## Sequence and verification

1. Inventory existing conservation and invariant lemmas; expose the smallest
   useful deterministic boundary and make the birthday proof reuse it.
2. Generalize the replay attack and resolve its initialization scope.
3. Clarify the three public claims—observable safety, truthful trajectory
   instrumentation, and positive behavior—and strengthen the concrete
   behavior check where appropriate.
4. Supply the serializer and instantiate the positive and negative results.
   This item can proceed independently once the transaction representation
   is understood.
5. Connect these results to the event-bounds migration when its adequacy
   bridge is available. Keep the existing strategy-level results usable
   throughout.

Follow the shared Agda instructions for edits, escape-hatch baselines,
timeouts, warning checks, and importer/closure verification. Check the
affected `Birthday`, `Observable`, `Property`, `Transfer`, and `Replay`
modules, the relevant ledger and encoding tests, and the root closure.

Preserve exact probability and schedule pins. Do not claim success from
weakening a premise or changing an event, initial state, or allowance
convention without an explicit decision. If the desired replay scope or
positive behavior fails, record the concrete obstruction and retain the
valid narrower theorem.

No new UC setup, general scheduler, hash-security model, or port-sensitive
budget calculus is required by these four tasks. The larger hash-assumption
question remains deferred.
