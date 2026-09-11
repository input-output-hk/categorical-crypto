# Theoretical review of `protocol-rewrite`

> Historical review at `f096c5d5`. The current implementation review is
> [Protocol rewrite implementation review](protocol-implementation-review.md)
> (`f71a2381..6256a140`, 2026-09-11). The findings below retain their original
> scope; they are not the current open-obligation list.

Reviewed at `f096c5d5`, concentrating on the commits after the previous review (`ebb3f2a5..f096c5d5`). This review concerns the mathematical content rather than compilation, tests, or proof completion.

## Reconciliation at `6256a140`

- Finding 1's zero-budget defect is repaired by
  `ctxBudget c c′ = c * (c′ ⊔ 1)`, with operational counting and composition
  proofs supporting the resource interpretation.
- Finding 2 is partially resolved: the generic graded `audit-carry`, the
  repaired total-process `UnitGrade`, and `AuditIsBounded` are proved. However,
  `AuditBound` bounds arbitrary tests rather than a designated audit event, so
  this does not establish the intended graded UC-to-POV application. The
  ledger's own carry still exposes direct `Agreeˢ` as its premise.
- Finding 3's existential reflection requirement was replaced by universal
  bounded-context domination. `UC.Machine.Dominated.dominated` proves that
  result for `QB`-certified contexts; it is no longer an open proof obligation.
- The live-genesis correction and cofinality requirement remain in place.
  The birthday theorem and `TrajectoryFromAudit` are now proved as well.

The current review records four remaining findings, including the false
saturation quantifiers and the vanishing/negligible mismatch, and specifies
the end-to-end theorem needed to demonstrate completion. Read it before using
the historical priorities below as a work list.

## Summary

The new commits materially improve the rewrite. The birthday experiment is now live, the asymptotic family requires a cofinal security-parameter map, and the protocol/UC seam is oriented through an embedding of strategies as environments rather than through the converse reflection theorem.

Two central issues remain. First, the query budget assigned to a context can collapse to zero even when the context makes a real query. Second, the new carry theorem still starts from direct agreement between closed protocol images rather than from simulator-based UC emulation. The bridge statement also retains an avoidable constructive risk by asking for an exactly dominating finite strategy.

## Findings

### 1. Context query budgets can collapse to zero

`UC.Bridge.Reflects` assigns its reified strategy the bound `c * c′`, where `c′` bounds the closure `m`. Take the ancilla to be `unitᴵ`. A closure `m : Proc unitᴵ (unitᴵ ⊗ᴵ unitᴵ)` has no downward port and therefore admits a `QB 0` certificate. A 1-bounded test `E` may nevertheless use its initial tick to query the plugged interface `B` once.

For implementations that answer that query differently, the context distinguishes perfectly, but `1 * 0` requires the witnessing strategy to make no queries. Such a strategy cannot distinguish the implementations, so `Reflects` is false.

The same multiplication appears in `UC.Family._≈ℰ[_]_`. A one-query test paired with a zero-bounded closure is charged budget zero, so a concrete bound is evaluated at `ε (κ i) 0`.

For a closed context, the test controls crossings into the plugged process while the closure only supplies ancillary/input responses. The conservative bound therefore appears to be `c` alone. If both numbers genuinely contribute, the multiplication needs a proved operational justification and at least a `c′ ⊔ 1` guard. A port-specific bound for crossings of the distinguished hole would be the principled formulation.

### 2. The carry is not yet simulator-aware

The new seam has the correct local direction: environment agreement leads to embedded-strategy agreement, then direct-run agreement, and finally protocol advantage. `strategyEnv`, `Adequacy`, `PrAgree`, and `agree-to-adv` form a coherent decomposition of that argument.

However, `pov-carry` assumes `Agreeˢ` directly between two closed protocol images. A UC emulation instead supplies an agreement `f ≈ℰ sub s ∘ g` at a graded codomain, with a simulator `s`. No current theorem turns this graded, simulator-bearing agreement into the premise of `pov-carry`. `StratIsEnv` only grounds an already-direct environment agreement between two closed processes.

The missing result should either be a closed/unit-grade specialization from `conjᴵ (morphism P) ≤UC conjᴵ (morphism Q)` to `Agreeˢ B (morphism P) (morphism Q)`, or, more usefully, a genuinely graded audit theorem carrying an ideal audit bound across `_≤UC_` and its simulator. `TrajectoryFromAudit` can then recover the state-trajectory statement. Until such a theorem is stated, the earlier simulator-accounting concern is only partially resolved.

### 3. `Reflects` still asks for a stronger witness than its consumers need

Moving `u` and `v` before the existential strategy fixes the original uniform finite-support counterexample. It still asks for one finite strategy that exactly dominates a possibly countably supported `Dₚ` context at every slack. Producing that strategy may require constructive extraction of an optimal deterministic policy, including exact attainment rather than approximation.

A safer statement says that if every bounded strategy makes the two direct runs ε-close, then the context runs are ε-close. This directly consumes a protocol theorem quantified over all bounded strategies and can be proved through convexity of probabilistic choice. If exact preservation is unavailable, an arbitrary positive approximation slack is sufficient for the asymptotic layer.

## Resolved findings

- The birthday target is no longer vacuous. Genesis contains a spendable UTxO, and the pins demonstrate acceptance and a state transition.
- The additional `+ q` term correctly accounts for fresh oracle outputs colliding with the genesis hash `h₀`.
- Requiring `κ` to be cofinal prevents eventual equality and the UC preorder from becoming vacuous.
- The old implication-direction error is repaired locally: extraction of protocol advantage now proceeds through the strategy-to-environment embedding.

## Assessment

The rewrite remains the right foundation and is substantially better than `spike/pov-tower`. The live example and cofinal family repair the two clearest semantic defects, while the new seam identifies sensible proof obligations instead of assuming the desired transfer outright.

The next theoretical priorities should be:

1. Correct the context-budget accounting in both `Reflects` and the family-level quantitative relation.
2. Replace or weaken the existential reflection principle before investing in its proof.
3. State and prove the graded, simulator-aware audit carry connecting `_≤UC_` to the protocol-level POV theorem.

No compilation or test checks were run for this theory-focused review.
