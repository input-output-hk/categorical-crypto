# Theoretical review of `protocol-rewrite`

Reviewed at `ebb3f2a5`, over the range `f71a2381..ebb3f2a5`. This review focuses on the mathematical content rather than compilation, tests, or proof completion.

## Summary

The rewrite is a substantially better foundation than `spike/pov-tower`. It replaces clocked towers and stabilization arguments with a direct protocol semantics, makes randomness explicit in the syntax, validates ledger effects sequentially, separates the security parameter from interaction budgets, and gives the UC layer a contentful probabilistic observation.

Two issues currently prevent the advertised POV-to-UC story from going through, however. First, the concrete birthday target is vacuous at the chosen genesis state. Second, the proposed bridge from arbitrary `Dₚ` machine contexts to finite protocol strategies is false at that level of generality. There is also a direction mismatch in the theorem intended to carry protocol agreement into UC advantage, and the indexed asymptotic definition needs a cofinality condition.

## Main findings

### 1. The birthday target is vacuous

`Examples.ChimericLedger.POV.AtBirthday.genesis` starts with an empty UTxO set and all value in an account. But `inputConsuming` requires a transaction to have at least one input, while `checkIns` rejects every input against the empty UTxO set. Therefore no submitted transaction is accepted, the oracle is never queried, and the ledger state never changes. The claimed birthday bound is consequently true for the trivial reason that the bad event has probability zero.

The example needs a nonempty initial UTxO set, or a controlled mint/account-funded transaction rule. If existing UTxO identifiers contribute collision opportunities, their namespace or contribution to the bound must be handled explicitly.

### 2. Finite strategies cannot represent arbitrary `Dₚ` contexts

`CategoricalCrypto.Strategy.Strat` is a finite inductive tree. Even though `Dₚ` supports countably supported computation, a finite strategy can mention only finitely many possible first queries. An unrestricted machine context can sample a natural number with unbounded support and issue that value as its sole query while still satisfying query bound one.

Hence `UC.Bridge.Reflects`, which asks for one finite strategy before quantifying over implementations `u` and `v`, cannot hold for arbitrary `Dₚ` contexts: choose implementations that differ only on a query outside the finite strategy's support.

There are three coherent repairs: restrict UC contexts to a finitary fragment, enlarge strategies to a `Dₚ`-valued or coinductive representation, or weaken/reorder the quantifiers so the witnessing experiment may depend on the compared implementations. The first two preserve a useful uniform reflection theorem; the third changes its meaning.

### 3. The proposed seam has the wrong implication direction

`UC.Bridge.Reflects` turns closeness of direct protocol runs into closeness under a machine context. `UC.Seam.AgreeToAdv` needs the converse kind of step: a UC/contextual hypothesis must imply closeness of the direct protocol observations used by `transfer`.

Reflection alone therefore cannot justify `AgreeToAdv`. A sound seam needs an embedding of each protocol strategy as a UC environment, plus a run-agreement theorem for that embedding. It must also account for the simulator quantified by `_≤UC_`; the present `pov-carry` premise is only a direct environment agreement.

### 4. The security-parameter map must be cofinal

`UC.Family` defines eventual comparison using an arbitrary map `κ : Ix → ℕ`. If `κ` is bounded—for example, constantly zero—then choosing a threshold above its range makes every eventual statement vacuously true. This collapses the UC preorder.

The family construction should require `κ` to be cofinal/unbounded: for every threshold `N`, some index `i` satisfies `N ≤ κ i`. Alternatively, use `ℕ` directly as the security-parameter index.

## Comparison with `spike/pov-tower`

| Aspect | `spike/pov-tower` | `protocol-rewrite` |
|---|---|---|
| Operational semantics | Clocked tower with eventual equality and stabilization | Direct finite protocol execution; no clocks or stabilization |
| Probability | Tower observations conflict with equality that forgets finite prefixes | Direct `Pr`/`PrHit`; avoids that well-definedness problem |
| Random computation | Clocking excludes genuinely unbounded probabilistic work | `Dₚ` supports countably supported computations |
| Ledger validation | Duplicate inputs/withdrawals can create value | Sequential consumption/debit fixes the preservation bug |
| POV observation | Audit transformation plus stabilization machinery | Trajectory observation is direct; audit form is a derived bridge |
| Parameters | Interaction budget and security level are entangled | Indexed families separate security parameters from query bounds |
| Machine equality | Multiple layers of tower/cofinal reasoning | One simulation-zigzag equality |
| UC content | Terminal-presheaf setup is too weak to express the intended experiment | Ticked `Dₚ Bool` observations are meaningful, but the bridge is not yet valid |
| Current result | Some specialized relay/transfer results are proved, but on a flawed base | Better architecture, but central bridge and seam remain specifications |

## Recommendation

Continue with the rewrite rather than repairing the tower. Before investing in the remaining proofs, settle two design choices:

1. Make the ledger experiment nontrivial and state the collision bound for that actual initial state.
2. Decide whether protocol adversaries and UC contexts are both finitary, or both live in a richer `Dₚ` strategy language.

After that, replace `Reflects`/`AgreeToAdv` with a directionally sound strategy-to-environment adequacy theorem, add cofinality to `κ`, and only then prove the trajectory/audit and UC composition obligations. That would preserve the rewrite's cleaner architecture while giving the POV theorem genuine cryptographic content.
