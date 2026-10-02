# Documentation index

What the code does not say by itself: the mathematics of the model, the worked examples'
theorem chains, contracts and inventories, remaining obligations, and the options and
NO-GO verdicts that should not be re-litigated. Every document describes the current tree;
history lives in `git log`.

## Guides

| Document | Purpose |
|---|---|
| [mathematical-guide.md](mathematical-guide.md) | the machine model's mathematics, one `module :: name` per notion; start here |
| [end-to-end.md](end-to-end.md) | the chimeric-ledger worked example: reading order and theorem chain |
| [quantitative-family.md](quantitative-family.md) | the quantitative family layer: the relation, its plugs, witness forms, composition, machine instance, theorem map |
| [state-event-contract.md](state-event-contract.md) | the state-event theorem contract: definitions, quantifier orders, operational counterparts |
| [uc-module-inventory.md](uc-module-inventory.md) | one row per `UC/` module: LOC, importers, root, purpose |
| [soundness-proof.typ](soundness-proof.typ) | the informal proof of the hypergraph soundness theorem for free SMCs |

## Examples

| Document | Purpose |
|---|---|
| [fcom-extraction.md](fcom-extraction.md) | the random-oracle commitment against a corrupted committer: extraction |
| [fcom-hiding.md](fcom-hiding.md) | the same commitment against a corrupted receiver: equivocation, and why the deferred-sampling hop costs ε |
| [fcom-uc.md](fcom-uc.md) | `F_com`'s closed-game bounds: the loop settles, game-playing at a partial kernel, the quantifiers |
| [dp-transport.md](dp-transport.md) | `Dₚ` runs as `Dist-ℚ` kernel runs, and why the transport route is the one taken |
| [rcom-icom-b1.md](rcom-icom-b1.md) | the `Rcom → Icom` boundary the coin-toss headlines assume: what is delivered, what remains |
| [coin-toss.md](coin-toss.md) | Blum coin-tossing over `F_com`, and the second hop to an ideal coin at a closed boundary |
| [hash-forward.md](hash-forward.md) | hash-then-forward, the nontrivial-grade toy and its machine-level event bound |

## Open work and options

| Document | Purpose |
|---|---|
| [open-items.md](open-items.md) | open suggestions from the review rounds and retired plans, one line each, by area |
| [simplification-options.md](simplification-options.md) | the model's size by layer, the options for simplifying it, and the spike verdicts on them |
| [smc-solver-performance.md](smc-solver-performance.md) | where the APROP SMC solver's cost goes, and the call-pattern rules the solver modules follow |
| [findiso-witness-plan.md](findiso-witness-plan.md) | unbuilt plan for proving the `deepFrame` iso (Route B); companion to `spikes/Leg1Carve.agda` |
