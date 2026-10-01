# Documentation index

One line per document in `docs/` and `docs/history/` (subdirectories such as
`docs/stduc-supersession-plan/` are not indexed). **Current** documents describe the
present tree or are standing contracts, guides, inventories or spike verdicts.
**Historical** ones are landing records, superseded or executed plans, and dated notes
whose names predate the tree; they live in `history/`, except those cited from code, which
stay in place so the citation keeps resolving. Classified at `fa45eaf5`.

| Document | Class | Purpose |
|---|---|---|
| [mathematical-guide.md](mathematical-guide.md) | current | the machine model's mathematics, one `module :: name` per notion |
| [end-to-end.md](end-to-end.md) | current | the chimeric-ledger worked example: reading order and theorem chain |
| [uc-module-inventory.md](uc-module-inventory.md) | current | one row per `UC/` module: LOC, importers, root, purpose |
| [state-event-contract.md](state-event-contract.md) | current | the state-event theorem contract: definitions, quantifier orders, operational counterparts |
| [simplification-options.md](simplification-options.md) | current | the model's size by layer and the options for simplifying it |
| [rcom-icom-b1.md](rcom-icom-b1.md) | current | specification of the `Rcom → Icom` boundary the coin-toss headlines still assume |
| [event-bounds-in-setup.md](event-bounds-in-setup.md) | current | plan and audit record for event bounds in the setup's own vocabulary |
| [chimeric-ledger-proof-boundaries-plan.md](chimeric-ledger-proof-boundaries-plan.md) | current | four bounded work items strengthening the ledger example's proof boundaries |
| [retirement-review.md](retirement-review.md) | current | WP11 review of what the quality campaign deleted, with restoration recommendations |
| [quantitative-uc-setup-plan.typ](quantitative-uc-setup-plan.typ) | current | design of quantitative UC from approximate-space-valued presheaves (`Approx.*`, `UC.Quantitative.*`) |
| [soundness-proof.typ](soundness-proof.typ) | current | the informal proof of the hypergraph soundness theorem for free SMCs |
| [state-event-transport-spike.md](state-event-transport-spike.md) | current | spike verdict: transporting a state-event bound along emulation (WP4) |
| [monitor-flag-spike.md](monitor-flag-spike.md) | current | spike verdict: a monitored process is a flag-wire process (GO) |
| [flag-wire-spike.md](flag-wire-spike.md) | current | spike verdict: `M ▷ P` as the state-event construction (WP2) |
| [certified-homs-spike.md](certified-homs-spike.md) | current | spike verdict: certified homs as the objects of comparison (shelved) |
| [lower-real-reading-spike.md](lower-real-reading-spike.md) | current | spike verdict: the reading as a lower real (NO-GO for the cheap version) |
| [one-accounting-theory-spike.md](one-accounting-theory-spike.md) | current | spike verdict: one accounting theory (NO-GO as a deletion package) |
| [coin-toss.md](coin-toss.md) | historical, kept in place: cited from `src/CategoricalCrypto.agda` | landing record of Blum coin-tossing over `F_com` and the hop to an ideal coin |
| [fcom-extraction.md](fcom-extraction.md) | historical, kept in place: cited from `src/CategoricalCrypto.agda` | landing record of the RO commitment's extraction half |
| [fcom-hiding.md](fcom-hiding.md) | historical, kept in place: cited from `src/CategoricalCrypto.agda` | landing record of the RO commitment's hiding / equivocation half |
| [fcom-uc.md](fcom-uc.md) | historical, kept in place: cited from `src/CategoricalCrypto/Protocol/Machine/Trace/Compose.agda` | landing record of `F_com`'s closed-game bounds and the distance to UC-level ε-emulation |
| [dp-transport.md](dp-transport.md) | historical, kept in place: cited from `src/CategoricalCrypto/Examples/CoinToss/Compose.agda` | landing record of the `Dₚ`-to-`Dist-ℚ` kernel-run transport |
| [hash-forward.md](hash-forward.md) | historical, kept in place: cited from `src/CategoricalCrypto/Examples/HashForward.agda` | landing record of the hash-then-forward nontrivial-grade example |
| [ro-game-hop.md](ro-game-hop.md) | historical, kept in place: cited from `src/CategoricalCrypto/Examples/ROCommitment/Game.agda` | landing record of the RO game-hopping toolkit hoisted out of Merkle–Damgård |
| [ledger-factoring.md](ledger-factoring.md) | historical, kept in place: cited from `src/CategoricalCrypto/Examples/ChimericLedger/Transfer.agda` | factoring the ledger as `Ledger ∘ RO` at the UC level; names predate the redesign |
| [ledger-lift-eps.md](ledger-lift-eps.md) | historical, kept in place: cited from `src/CategoricalCrypto/Examples/ChimericLedger/Transfer.agda` | lifting the hash premise through the ledger with its error kept; names predate the redesign |
| [quantitative-family.md](quantitative-family.md) | historical, kept in place: cited from `src/CategoricalCrypto/UC/Quantitative/Family.agda` | landing record of the quantitative family layer (plan steps 3–4) |
| [retirement-negligible-order.md](retirement-negligible-order.md) | historical, kept in place: cited from `src/CategoricalCrypto/UC/Family/Negligible.agda` | landing record: `Abstract2._≤UC_` adopted as the negligible tier's order |
| [graded-observation-redesign.md](graded-observation-redesign.md) | historical, kept in place: cited from `src/CategoricalCrypto/UC/Approximate/Local.agda` | executed proposal for a local negligible observation |
| [discard-audit.md](discard-audit.md) | historical, kept in place: cited from `src/CategoricalCrypto/Machines/Core.agda` | WP7 audit of `State.discard`; decided, `discard` removed |
| [protocol-rewrite.md](protocol-rewrite.md) | historical, kept in place: cited from `src/CategoricalCrypto/UC/Machine.agda` | development log of the protocol rewrite, section by section |
| [rewrite-verdict.md](rewrite-verdict.md) | historical, kept in place: cited from `src/CategoricalCrypto/Examples/ChimericLedger/Replay.agda` | successive verdicts on adopting the rewrite over the old lineage |
| [protocol-implementation-review.md](protocol-implementation-review.md) | historical, kept in place: cited from `src/CategoricalCrypto/UC/Approximate/LocalTests.agda` | follow-up implementation review at `6f48aa5d` |
| [stduc-supersession-plan.md](stduc-supersession-plan.md) | historical, kept in place: cited from `src/CategoricalCrypto/UC/Family.agda` | finished plan superseding the qualitative UC core by `StdUC` |
| [smc-solver-performance.md](smc-solver-performance.md) | historical, kept in place: cited from `src/Categories/APROP/Hypergraph/Solver/Match/FindIso.agda` | campaign record of the APROP SMC solver's cost |
| [findiso-witness-plan.md](findiso-witness-plan.md) | historical, kept in place: cited from `spikes/Leg1Carve.agda` | Route B plan for proving the `deepFrame` iso; superseded |
| [history/uc-presheaf-preservation-plan.md](history/uc-presheaf-preservation-plan.md) | historical | executed plan: UC preservation through the presheaf action, steps 1–7 |
| [history/presheaf-action.md](history/presheaf-action.md) | historical | landing record of plan steps 1–2 (the generic action) |
| [history/direct-extraction.md](history/direct-extraction.md) | historical | landing record of plan step 5 (direct model extraction) |
| [history/consumer-migration.md](history/consumer-migration.md) | historical | landing record of plan step 6 (consumer migration); names predate the redesign |
| [history/retirement.md](history/retirement.md) | historical | landing record of plan step 7 (retirement) |
| [history/graded-bridge.md](history/graded-bridge.md) | historical | landing record of the graded extraction bridge |
| [history/prefix-tolerant-audit-plan.md](history/prefix-tolerant-audit-plan.md) | historical | implemented, then retired, plan for the prefix-tolerant audit event class |
| [history/issue-quantitative-uc-foundation.md](history/issue-quantitative-uc-foundation.md) | historical | landed issue: quantitative UC from an `Approx`-valued presheaf |
| [history/issue-quantitative-uc-resources-and-migration.md](history/issue-quantitative-uc-resources-and-migration.md) | historical | issue: resource-sensitive quantitative UC and migration of the old relations |
| [history/uc-observation-and-relation-consolidation.typ](history/uc-observation-and-relation-consolidation.typ) | historical | consolidation proposal at `92479a3`: one qualitative UC theory and a quantitative refinement |
| [history/controls-allowances-inventory.md](history/controls-allowances-inventory.md) | historical | inventory of controls and allowances before the WP9 change |
| [history/protocol-rewrite-abstraction-notes.md](history/protocol-rewrite-abstraction-notes.md) | historical | architectural recommendations for the rewrite, 2026-09-11 |
| [history/protocol-rewrite-theory-review.md](history/protocol-rewrite-theory-review.md) | historical | theoretical review of the rewrite at `f096c5d5` |
| [history/module-reorg-plan.md](history/module-reorg-plan.md) | historical | executed APROP hypergraph-solver module reorganisation |
| [history/post-reorg-cleanup-findings.md](history/post-reorg-cleanup-findings.md) | historical | archived cleanup findings after the reorganisation (2026-06-17) |
| [history/size-reduction-strategies.md](history/size-reduction-strategies.md) | historical | levers for shrinking the APROP soundness development (pre-campaign census) |
| [history/strictification-migration.md](history/strictification-migration.md) | historical | strictification migration plan and phase log |
| [history/strictification-part2-map.md](history/strictification-part2-map.md) | historical | strictification map for the iso-invariance chain |
| [history/braided-coherence-solver.md](history/braided-coherence-solver.md) | historical | investigation of a direct braided coherence solver (Option 2) |
| [history/proof-carrying-routea-plan.md](history/proof-carrying-routea-plan.md) | historical | plan to make the first `rewriteDeep` gate a theorem (Route A) |
| [history/deepframe-preservation-notes.md](history/deepframe-preservation-notes.md) | historical | spike log de-risking proof-carrying Route A |
| [history/globalphi-verdict-notes.md](history/globalphi-verdict-notes.md) | historical | probe notes on the global-φ direct gate |
| [history/leg1-carve-notes.md](history/leg1-carve-notes.md) | historical | spike log for leg 1 (carve combinatorics) |
| [history/leg3-recomp-notes.md](history/leg3-recomp-notes.md) | historical | spike log for leg 3 (recomposition soundness) |
| [history/k-proof-tactics.md](history/k-proof-tactics.md) | historical | unbuilt proposal: tactics for the K reproofs |
| [history/proposed-tactics.md](history/proposed-tactics.md) | historical | unbuilt proposal: two tactics from the APROP completeness work |
