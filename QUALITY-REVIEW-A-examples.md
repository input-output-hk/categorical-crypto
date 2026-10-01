# Quality review — protocol-rewrite, part A-examples (2026-09-30)

Scope: `src/CategoricalCrypto/Examples/**` (56 modules, the `scope-A-examples.txt` list; the
integration-owned `Examples/{Basic,Commitment,RelSetup,Signatures}` excluded). Branch
`quality-A-examples`, rebased onto `protocol-rewrite` at `4756d24c` (impl-B + impl-D merged).
The review's centre of gravity is the maintainer's question "is `protocol-rewrite` too
complicated?"; the ranked suggestions below are ordered by lines or notions removed.

Verification: every commit re-checked after the rebase (the in-scope leaves reached by the
modules it touches; rc=0 and the rule-6 warning grep empty); the tip additionally checked
module-by-module with a forced single-module elaboration of each of the 56 files (each run's
own `Checking` line present, warn grep empty), plus the root `src/CategoricalCrypto.agda`
(`-M8G -H2G`, `timeout 1800`) and every scope leaf — table at the end. Soundness baseline
over `src`: 16 hits before, 16 after, none in scope. Byte-level NUL check (python
`b'\0' in blob`) over every committed blob: clean.

Sweep tally (toolkit JSONs under `sweeps-A-examples/`):

| class | files | candidates | kept | reverted/red | notes |
|---|---|---|---|---|---|
| using-drop (+ redo) | 56 | 768 | 670 | 98 | first run hit 38 files RED-before-sweep (a broken WIP state), `using-drop-redo.json` re-ran those 38 |
| implicit-drop | 56 | 170 | 70 | 100 | |
| binder-drop | 56 | 29 | 0 | 29 | every binder is needed |
| join-lines | 56 | 117 | 116 | 1 | |
| enum-with (transform) | 56 | 158 | 15 + 7 by hand | 48 red | 95 skipped-shape: 36 phantom (a `with` in a comment), 15 `with … in eq`, 12 multi-scrutinee, 10 nested, 26 non-flat; every flagged single-branch destructuring site spiked by hand (7 kept), 3 two-branch ones spiked and red (`Game.fetch-log`, `Transport.resKᵀ-fetchT`, `Core.callC-marg`: the reduction under `with` is load-bearing) |
| enum-where (transform) | 56 | 276 | 5 | 4 red | 28 declined on width, 239 skipped-shape (multi-use / clause with arguments / own `where`) |
| enum-comments | 56 | 763 blocks (pre-trim tally) | — | — | every block dispositioned in `comments-dispositions-*.json` (461 cut, 331 keep with the named content, 32 reworded) |
| import-drop (EXPERIMENTAL) | 27 / 56 | 689 import lines | 20 pruned | 669 kept | see Suggestions work item W1 |

The canonical `with_case.py` passed a constructor pattern `yes p` as two `λ where` arguments, so
every probe of it came back red; the run used a copy with the pattern parenthesized, and
`where_inline.py` a copy that does not parenthesize an atomic right-hand side (both copies are
described in the tally headers; the canonical scripts were not modified — suggestion W2).


## Committed (you can skim these)

On `4756d24c`; one line each, with its LOC delta.

- `6445e6f0` Comments: trim ChimericLedger narration, fix stale citations (+119/−394) — comment-only; every changed line is a comment (rules 21–24)
- `09feffc1` Comments: trim cointoss narration (+120/−428) — comment-only; every changed line is a comment (rules 21–24)
- `28685b98` Comments: trim rocommitment narration (+163/−525) — comment-only; every changed line is a comment (rules 21–24)
- `734441d0` Comments: trim hash narration (+104/−390) — comment-only; every changed line is a comment (rules 21–24)
- `4747952e` Comments: accuracy fixes after the trim (antecedents, overclaims, restored doc pointers) (+24/−18) — comment-only; restores pointers the trims dropped
- `afa2aaad` ROCommitment.Extraction: ∨-false is stdlib ∨-conicalˡ/ʳ (+4/−9) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `28786496` ROCommitment.Game: inline keep-true; logP/hitP polymorphic in the answer (drop logU/hitU) (+17/−26) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `d532c70f` ROCommitment.Hiding.Game: one erasure relation _≋_ for both bisimulations (+6/−7) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `7c07ad14` ROCommitment.Oracle: fetchT-sup uses OnSupport-⊤ instead of its body (+2/−4) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `47ba84b1` ROCommitment.Hiding.Asymptotic: drop εʰ/hiding-boundⁿ, forwarders of Game.εᴸ/hiding-bound (+1/−9) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `376f974a` ROCommitment.UC: drop a double blank line (+0/−1) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `4f19e48d` MerkleDamgard.QueryBound: enter is advance at block 1; θ-sim via Pointwise.simFn (+13/−53) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `1d576d65` CoinToss.Ideal{,.Receiver}.{Hybrid,Machine}: the four simulations are Pointwise.simFn (+14/−40) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `7aa916a7` ChimericLedger: one ledgerCall, in System, that ledger's step is fromCall of (+11/−24) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `0770ef2d` ChimericLedger.Replay: drop replay-watch-asks (no consumer) (+0/−3) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `4b9e517c` ChimericLedger.Value: one checkIns inversion lemma; +-swap is stdlib x∙yz≈y∙xz (+43/−63) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `9eca0076` HashForward: inline map-ret/map-bot (eta-wrappers of >>=ₚ-identityˡ/bot-bind-≈ₚ) (+6/−12) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `da375854` HashForward.UC: the two exact-ledger refinements are one module at the weights (+28/−49) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `f8109ce2` HashForward.Audit: hf-emul is ≤UC[]ᵍ directly, not a witness round trip (+1/−1) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `7aff20be` ROCommitment.UC: simExactHash/simExactAll project one refinement carrying both witnesses (+18/−50) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `603b6511` MerkleDamgard.Core: lookup-cons-* are RandomOracle.lookup-bs-here/-there; drop dead callC-supp (+13/−45) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `d4173c7f` CoinToss.Ideal{,.Receiver}: Sum.map (λ a → a) is Sum.map₂; drop dead padᴵ; one padʰ (+22/−30) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `5846b5cd` Revert "ROCommitment.Hiding.Asymptotic: drop εʰ/hiding-boundⁿ, forwarders of Game.εᴸ/hiding-bound" (+9/−1) — restores the maintainer-sanctioned forwarders (net zero with the commit it reverts)
- `9f0a0b1a` docs: end-to-end/ledger-lift-eps resynced to the ledger code (+8/−7) — docs only
- `19d957f2` CoinToss.Ideal hash lemmas: one Resource.lazy-bind instead of four hit/miss splits (+48/−87) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `036d56d3` MerkleDamgard.Core: name respB's repeat answer repAns (spelled out seven times) (+13/−22) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `eef6da5e` MerkleDamgard.Core: walk-supp/walk-fk recurse through one-call lemmas, no L/C split (+71/−118) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `355ccfb0` Certificates and refinements: one catch-all botₚ clause instead of enumerating dead transitions (+12/−55) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `0881e820` MerkleDamgard.Pin: its instance opens re-export to nobody; drop public (+2/−2) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `05cb5949` CoinToss.Compose: εᶜᵗ-negligible is composeError-negligible at 1⁺, 1⁺ (+3/−6) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `f3f18978` Sweeps over Examples: bare opens, dropped imports, joined lines (+675/−740) — toolkit class, each site kept only if its file and in-scope importers stayed green
- `6e6683a9` Comments: second trim over Examples, stale names and citations fixed (+51/−146) — comment-only; per-block disposition of the enum-comments tally
- `f5ee86c4` Drop four dead definitions: upᴵ, upᴵʰ, eraseP, bad-bound (+1/−28) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `b08fe6fa` HashForward.UC, ROCommitment.UC: the exact ledgers run on the certificate's potential (+15/−25) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `1db76c8e` MerkleDamgard: MDState lives in QueryBound, its only user (+4/−3) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `3f196153` ChimericLedger: three restatements replaced by what they restate (+6/−20) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `b28cc1e5` ROCommitment.Hiding.Game: off the oracle the coupling is a lift of the deferred step (+37/−155) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `ada02966` MerkleDamgard.Core: detach needs no hit/miss split; cong wrappers inlined (+19/−65) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `405dfe57` CoinToss.Ideal.Receiver.Hybrid: inline outᴴʰ, a one-use alias of Hᵁ.solve-out (+1/−5) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `00a9bde4` ROCommitment.Game: eraseR/eraseI are the erasure ec at digOf and id (+6/−6) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `66244ab7` ROCommitment.Game: the coupled continuations are Dmaps, read by lookupᴰℚ-Dmap (+28/−80) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `a42c2f63` MerkleDamgard.Core: return-continuation binds read by lookupᴰℚ-Dmap (+30/−71) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `a1ff501b` ROCommitment: the remaining return-continuation binds read by lookupᴰℚ-Dmap (+19/−41) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `82c686de` ROCommitment.Transport, Realization.Bound: library lemmas for two hand proofs (+3/−12) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `dde46854` ROCommitment.Hiding: one catch-all botₚ clause for the resource's dead answers (+2/−5) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `e8dee617` Sweep implicit-drop over Examples (rule 15) (+41/−41) — toolkit class, each site kept only if its file and in-scope importers stayed green
- `ab385799` docs: repoint LedgerCall.qb-ledger and hash-hit/hash-miss at what replaced them (+6/−6) — docs only
- `a4e15e46` Sweep enum-with over Examples: 15 clean with → case_of_ swaps (rule 12) (+50/−47) — toolkit class, each site kept only if its file and in-scope importers stayed green
- `dd2ecd18` ChimericLedger: seven single-branch destructuring withs are case_of_ (rule 12) (+10/−14) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green
- `e8687858` Sweep enum-where over Examples: five single-use where-bindings inlined (rule 18) (+5/−16) — toolkit class, each site kept only if its file and in-scope importers stayed green
- `c2103684` Comments: restore two whys the trim cut (Hiding.Defer.Fresh, MerkleDamgard.Core.detach) (+5/−2) — comment-only
- `b5fb24c0` MerkleDamgard.Pin: restore the public instance opens (+2/−2) — no statement changed; every removed or moved name has no remaining consumer in src or docs; importers green

## Suggestions (need your call)

Ranked by lines saved or complexity removed. Every entry gives the concrete replacement and an
estimated LOC delta. "Crux" is the part most likely to fail. Anchors use `file :: identifier`.

### Simplifications not committed (judgment needed), ranked

1. `src/CategoricalCrypto/UC/QueryBound.agda :: qbᵢ-upward` (new), consumed by
   `Examples/CoinToss/Ideal/UC.agda :: simJCert`, `Ideal/Receiver/UC.agda :: simJʰCert`,
   `CoinToss/Hiding/UC.agda :: tossʰCert`, `CoinToss/UC.agda :: recvCert`, `CoinToss/Hiding/UC.agda :: comCert`
   — **about −185 LOC.**
   - At potential 0 and rate 1, the from-above half of a certificate needs no hypothesis. Every
     output of `step (s , inj₂ b)` fits `Ans (λ _ → 0) _ _ 1`: a downward message needs `0 < 1`, an
     upward one `0 ≤ 1`. So `onRᵍ = mapₚ tag ∘ step`, `cohR` is `map-map`/`map-cong`/`>>=ₚ-identityʳ`
     once, and only the from-below half (`onL`, which must never call down) is supplied.
   - This deletes every certificate's `onR`/`cohR` block (15–20 clauses each), plus `hashG`/`cohHash`
     in both Ideal UC files.
   - **Spiked green**: `qbᵢ-upward` (19 lines, using `Dp.Reasoning.map-map`/`map-eq`) plus
     `simJCert′ = qbᵢ-upward _ _ _ up coh`, where `up` has 2 clauses and `coh` 4. That replaces
     `simJCert`'s 55 lines at the same type `Certified 1 simJ`, so it is a drop-in. The spike was a
     scratch module, removed afterwards.
   - Placement: generic, so it goes in `UC/QueryBound` beside `qbᵢ-wire`/`qbᵢ-closed`. That file is
     outside this part's scope, so this is not committed.
   - `tossCert` stays `Certified 0`; moving it to 1 would weaken it.
   - Ledger: the open coin-toss item "Proc-level `qb-oneCall` is now clearly worth having" is this,
     in concrete form.
2. `src/CategoricalCrypto/Examples/ROCommitment/Realization/Machine.agda :: Kⁱ … Kᴵ` (the ideal half,
   from the "ideal functionality, over the same resource" banner to EOF) — **−150 LOC.**
   - Twenty names, zero consumers anywhere in `src`.
   - It is staged for route step B2-M4, which `docs/rcom-icom-b1.md` records as BLOCKED.
   - The unblocking fix there ("`simStep` caches") would change `simStep`, which `Kˢ`/`sub-settles`
     copy clause for clause, so this code would be rewritten anyway.
   - Deleting it means cutting the header's ideal clause, the now-unused imports and B2-M2's doc row.
   - Also dead from the same staging:
     - `Realization/Bisim.agda :: fromQ`, `toQ-fromQ`, `fromQ-toQ`, `fromR-toR` (−19;
       `runWith⊥-bisimʳ` needs only `toQ`/`fromR`).
     - `Realization/Assembly.agda :: Rcomʷ`, `Icomʷ`, `Rcomʰʷ`, `Icomʰʷ` (−14).
     - `Realization/Bisim.agda :: sim-log-repeat`, `extract-relog`, `extract-table` (−17). These are
       deliberate non-bisimilarity witnesses; keep them if they are the obstruction record.
   - **Spiked green**: deleting the ideal half (−148 lines) leaves `Machine`, `Bisim` and `Bound`
     green; the root's import of `Machine` uses none of the names.
   - Your call: keep staged code for a blocked leg, or delete (−200 total).
3. `src/CategoricalCrypto/UC/QueryBound/Exact.agda :: exact⇒certified` (new) — **net about −55 LOC.**
   - A `QEᵢ` exact ledger whose upward cost is 0 and whose downward cost is ≤ c already *is* a
     `QBᵢ … c` with `Φ = Λ`.
   - `ROCommitment/UC.agda :: simCert` (45 lines) and `HashForward/UC.agda :: simCert` then become
     `exact⇒certified simExactAll (λ _ → refl) (λ where …)`.
   - Their `Φˢ`, which after `b08fe6fa` is the ledger's `Λ` itself, stays as the one potential.
   - Sketch in the ROCommitment finding. Out of scope (`UC/QueryBound/Exact`).
4. `src/CategoricalCrypto/UC/QueryBound/Compose.agda :: module Walk (u : Unfolding)` (new), replacing
   `CoinToss/Ideal/Machine.agda :: botᴵ downᴵ backᴵ honᴵ`,
   `Ideal/Receiver/Machine.agda :: botᴵʰ downᴵʰ bypᴵʰ backᴵʰ honᴵʰ` and `Ideal/Hybrid :: lkᴴ`,
   `Receiver/Hybrid :: lkᴴʰ cellᴴʰ` — **about −70 LOC.**
   - `R-out`, `R-bot`, `R-down`, `F-up`: four walks of `Compose.Unfolding` that both corruptions
     hand-roll.
   - The ledger's reason not to hoist them ("the second instance does not exist", `docs/coin-toss.md`)
     no longer holds: the receiver side is that second instance. Out of scope.
5. `src/CategoricalCrypto/Examples/CoinToss/Hop.agda` (new): the shared composite scaffolding of
   `Ideal/*` and `Ideal/Receiver/*` — **−60 to −90 LOC.**
   - Shared parts: `Cⁱ`/`Cᵗ`, `reachᴹ = sandwichᴹ M (map₂ ⊎assocʳ) (map₂ ⊎assocˡ)` (three copies),
     `hybridᴹ`, `hybrid-eq`, `idealᴹ`, `ideal-eq`, `hear`.
   - Build it as top-level functions with explicit arguments, NOT as an applied parameterized module:
     `UC/Machine/Wire.agda`'s header records an 8 GiB blow-up from module application.
   - Crux: the hash lemmas at an abstract `downᶠ` do not reduce. State them with the resource step as
     an `≈ₚ` hypothesis that is `≈ₚ-refl` at each instance.
   - The two protocols, functionalities and simulators genuinely differ and stay two. Only the
     scaffolding merges.
6. `src/CategoricalCrypto/Examples/RandomOracle.agda :: module Lazy` (new) — **net about −30 LOC.**
   - The lazily sampled RO as a call tree is written three times: `MerkleDamgard.agda :: compStep`,
     `:: generalStep` and `ChimericLedger/System.agda :: oracle`.
   - `compStep-eval`/`generalStep-eval` are one 20-line proof at two readings.
   - Proposal: `answer : Table → Input → Maybe Out → Calls …` with the lookup passed as an argument,
     `oracle`, and one `answer-eval`. Then `Birthday.oracle-hit/-miss` fold into `rewrite eo`.
   - Crux: `Birthday`'s `go` rewrites and `Replay.step-shape`'s `refl`s at concrete tables.
   - A fourth oracle kernel, `ROCommitment/Oracle.fetchT`, is at `Dist-ℚ` level; see 7.
7. `src/CategoricalCrypto/Examples/ROCommitment/Transport.agda :: fetchᴰ, resKᵀ, resKᵀ-fetchT` —
   **−20 LOC (small slice).**
   - `resKᵀ (t , m) x = Dmap (λ u → proj₁ u , digᴿ (proj₂ u)) (fetchT (_, m) t x)` deletes
     `fetchᴰ` and `resKᵀ-fetchT`.
   - The oracle kernel is currently spelled three ways: `Resource.lazyₚ` (Dₚ), `Oracle.fetchT` and
     `Transport.fetchᴰ`.
   - Crux: the with-abstraction gotcha documented at `Transport.hash`, and the ledger's "kernel must
     REDUCE under `with lookupPt`" (`fetch-bis`).
8. `src/CategoricalCrypto/GamePlaying/Hop.agda :: prune-bisim` and `GamePlaying/Partial.agda :: prune-map`
   (new) — **−25 LOC here, net −10.**
   - `Realization/Bound.agda :: marginalᴿ`, `bisimᴿᵍ` and `bisimᴵᵍ` are one lemma used three times
     (sink/sink `true` branch, `Eⱼ` `false` branch).
   - `Hop.runWith-bisim`'s local `bis⊥` is the same lemma at `dead = λ _ _ → false`.
   - Out of scope.
9. ChimericLedger restatements (code in the ledger finding):
   - `ChimericLedger/Replay.agda :: chimeric-loses-value` and `:: genesis-live` share one 6-step chain.
     A `Pr₁⊥-uniform-const` beside `Protocol/Observe.evalC-serve-uniformVec` gives −10.
   - `ChimericLedger/Observable.agda :: sound`/`complete` are four copies of bind-monotonicity. A
     `Pr₁⊥-bind-mono` in `RationalDist/Expectation` gives −12.
   - `ChimericLedger/Property.agda :: ledger-hitsᵘ`, `auditWatch-IsWatch` and `auditWatch-preserving`
     (with `Observable.asks≤-auditWatch`) are one-use forwarders and a double forwarder of
     `Strategy.asks≤-watch`. Inlining gives −19; `docs/end-to-end.md` §5 names them.
   - `ChimericLedger.agda :: acctΣ`, `wdrlΣ`, `valΣ` are all `sum ∘ map proj₂` (−4). Judgment: the
     domain names read well.
10. `src/CategoricalCrypto/Examples/ChimericLedger/ReplayFamily.agda` (module) → merge into
    `ChimericLedger/Transfer.agda` — **−28 LOC, −1 module.**
    - Its content is one theorem (`chimeric-not-preserving`), a side condition, an alias and a
      one-use forwarder.
    - Transfer already hosts the other counterexamples (`Mute`, `Liar`) at family level.
    - Docs: the `end-to-end.md` nine-module table becomes eight.
11. ε-arithmetic lemmas that belong in `ProbabilisticLogic` (out of scope):
    - `E-return-cong` (about 20 return/return clauses in `Game`, `Hiding/Game`): −25.
    - `E⊥-nothing` (17 hand-written sink sites): −10.
    - `E-+const`/`E-const+` (`Defer.collect`, `rise-drift`, `inner-drift`, `Potential.rare-cert`): −10.
    - `OnSupport-bind₂` (8 nested `OnSupport-bind … OnSupport-⊤` sites): −10.
    - `fromℕ-+-*` (3 sites): −2.
12. `src/CategoricalCrypto/UC/Machine.agda :: initˢ` (new):
    `initˢ S s = record { obj = S ; point = λ _ → returnₚ s ; discard = λ _ → returnₚ tt }`.
    - It replaces 11 hand-written `stateX` records in scope and 14 more in `src`. −20 in scope.
    - `UC/Machine.agda`'s private `outT` should also go public; `Receiver/Hybrid :: outTʰ` restates it.
13. `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Game.agda :: drift-∧` → public, in
    `GamePlaying/Potential.agda` beside `guess-drift` (rule 27).
    - Then `Game.fetch-hit` is one `with lookupPt` split (−12).
    - `Hiding/Defer :: ∧-mass`/`hit-mass` are `drift-∧`/`hit-drift` at `g = false` (−6).
14. `src/CategoricalCrypto/Examples/CoinToss/Compose.agda :: coin-toss-from-comᵇ`/`coin-toss-from-comʰᵇ`
    — one `toss-overᵇ` at the channel parameters, plus `simᶜᵗ`/`simᶜᵗʰ` as one polymorphic `composeSim`.
    −10 here, −25 with `Assembly.coin-from-Rcom{,ʰ}`. Crux: implicit-channel inference for
    `≤UC[]-compose′` (pass `u`/`v` explicitly).
15. `src/CategoricalCrypto/Examples/CoinToss/Hiding.agda :: CoinAʰ` is `CoinToss.CoinA` again.
    `tossedᶜʰ`/`abortedᶜʰ` are renamed across 7 files. −4.
16. `src/CategoricalCrypto/Examples/ROCommitment/Realization/Machine.agda :: Kʳ, real-settles` —
    deterministic steps as `det ∘ realStepᵈ` with `realStepᵈ : … → Maybe …`.
    - `Kʳ` stops restating `realStep` clause for clause, and `real-settles` becomes `Settles-det`. −36.
    - Crux: keep `realStep`'s input-first clause order so `real-up` still reduces at a neutral state.
17. `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Game.agda` "Deferred sampling at the real game"
    (`_≋P_`, `ask-redᴿ`, `hereP`, `avg-commit`, `defer-commit`) → move into `Hiding/Defer.agda`
    beside its twin `defer-hop` (rule 28; its only consumer is `Defer.defer-hiding`).
    - Size-neutral; `hereP`/`hereD` then merge (−8).
18. `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda`:
    - `x≤x+c`, `x≤c+x` and `pos-sum-≡0` → `Data/Rational/Properties/Ext.agda`. The same open-coding
      appears at 10 more sites repo-wide. That file is integration-owned, so see the last section.
    - `δ-sym` goes beside `δ` in `Uniform`.
    - `respG-hit`/`respG-miss` are generic `RandomOracle.step-hit`/`-miss`: the same shape as
      `Oracle.fetchT-hit/-miss` and `Birthday.oracle-hit/-miss`.
19. `src/CategoricalCrypto/Examples/ROCommitment/Extraction.agda :: Pins` is `All (λ (x , d) → d ≡ c → head x ≡ b)`:
    stdlib `All` in disguise. LOC-neutral; standard construction over ad hoc.
20. Small items, each a few lines:
    - `ChimericLedger/Transfer :: mute-silent`/`mute-never-accepts` share one dead-ask computation (−4).
    - `ChimericLedger/Value :: after` belongs in `ChimericLedger.Step`, where five sites re-spell it (−2).
    - `ChimericLedger/Birthday :: εbirthday` is `Property.εᴸ ℓ` with two spurious parameters (−3).
      Needs a `birthday-bound` in `Uniform/Birthday` (out of scope).
    - `ROCommitment/Realization/Assembly :: Assembly`/`Assemblyʰ` are single-use statement aliases (−3).
    - `ROCommitment/Game :: sL₀ sI₀` are one value under two names (interface: used in `Asymptotic`,
      `Test`, `Defer`).
    - `CoinToss/Ideal/Receiver/Hybrid :: outTʰ` (see 12).
    - `MerkleDamgard/Core :: CState` has one use (−2) and `interior-mem` is a two-use one-liner (−3).
      A public `toBlocks-length` would serve `QueryBound.blk-len` and five Core sites (−3).
    - `ROCommitment/Realization/Bisim :: pre-hit` belongs next to `Extraction.preimages` (rule 27/28).
      `Extraction.memb-pre` needs two `with`s only because `preimages` tests `d ≟ c` and `memb` tests
      `c ≟ d`.
    - `ROCommitment/Hiding/Defer :: fetchR`, `redR` and `tbl-∷` are table algebra that belongs in
      `Oracle`/`Extraction` (`fetchT-transfer`, `lookup-∷-cong`, `lookup-swap`).

### Public API / module layout

21. The test suites (rule 33):
    - `src/CategoricalCrypto/Examples/CoinToss/Test.agda`
      - `attack-bound`, `ideal-bound` and `ideal-boundʳ` are `composed-ε 3 3`, `ideal-ε 3 3` and
        `ideal-εʳ 3 3`. A ∀-lemma's instance cannot fail on its own, and the values (15/8, 15/8,
        10/8) are all ≥ 1, i.e. vacuous.
        - Fresh form: `refl`-pins of the computed ℚ plus a vacuity note, as `MerkleDamgard/Pin`
          does. Or drop them.
      - `coin-round`, `sim-round` and their ʰ versions pin the raw `(FSt, point, coinStep)` triples
        through `behᵍ`/`traceᵍ`, and `coin-round` starts mid-run at `heldᵏ c`.
        - The sanctioned entry points are `Fcoin`/`simJ`/`Fcoinʰ`/`simJʰ`: add
          `behᴾ M = behᵍ (MC.St M) (MC.point (MC.state M) tt) (MC.step M)` to `UC/QueryBound` and
          state the pins over it.
      - The `bias` block (`Startᴵ … bias-round`, about 55 LOC) exercises only the test's own machine.
        No theorem consumes it, because the composed theorems are conditional. Written fresh, the
        suite would not contain it: drop it, or move it to `docs/coin-toss.md`.
    - `src/CategoricalCrypto/Examples/ROCommitment/Test.agda :: bounded`
      - It pins `Game.extraction-bound 3` at `ε 3` = 15/8 (vacuous).
      - The downstream API is `Asymptotic.εᶜ`/`extraction-boundⁿ`, which currently has zero consumers.
      - Retarget: `≤ℚ εᶜ 3 3` via `extraction-boundⁿ 3 3 …`, at `k = 5` so it bites (9/16).
    - `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Test.agda :: bounded, bounded-total, bounded-preq`
      - Retarget to `Hiding.Asymptotic.hiding-boundⁿ`/`hiding-boundᵗ` (`≤ εʰ`, `≤ εᵗ`).
      - This drops the `Hiding.Defer 3` import.
      - `εᵗ 3 3` = 9/8 is vacuous; `k = 4` or `5` makes every bound bite.
    - The three suites disagree on whether to apply the attack to a bound and on vacuity disclosure.
      Both styles are suspect: the proposal above is the fresh form for all three.
22. `src/CategoricalCrypto/Examples/CoinToss/UC.agda :: recvCert`, `CoinToss/Hiding/UC.agda :: comCert`,
    `CoinToss/Ideal/UC.agda :: resourceQBᵒ`
    - These are commitment facts, but `ROCommitment/Realization/Assembly.agda` imports three CoinToss
      UC modules to get them: the dependency runs backwards.
    - Move them to `ROCommitment/UC.agda` and `ROCommitment/Hiding/UC.agda`.
    - Ledger: the `recvCert`/`comCert` half is the open coin-toss "Maintainer call"; `resourceQBᵒ` is new.
23. `src/CategoricalCrypto/Examples/CoinToss/Compose.agda :: comSimʰ` has no consumer.
    - The committer side has `coin-toss-from-comᶜ`/`coin-toss-idealᶜ`; the receiver side lacks
      `coin-toss-idealʳᶜ e = coin-toss-idealʳ (comSimʰ , εᵗ , εᵗ-negligible , e)`.
    - Add it (+4, rule 32) or drop `comSimʰ` (−2). `docs/rcom-icom-b1.md` calls it delivered.
24. `src/CategoricalCrypto/Examples/RandomOracle.agda` is library, not an example. Rule 27: move it to
    the name `CategoricalCrypto/RandomOracle.agda` once that fossil goes (last section). Its consumers
    are three example families plus the root.
    - `Examples/RandomOracle.agda :: Functionality` (the table as an `SFunᵉ`) has no consumer.
      Dropping it also drops the `SFunM` import (−3); keep it only if it is meant as API.
25. `src/CategoricalCrypto/Examples/MerkleDamgard/QueryBound.agda` is reached by no root and no importer.
    CI's per-file check covers it, but `CategoricalCrypto.agda`'s header claims each outside example
    "with its own root". Either wire it into `MerkleDamgard.agda` or say so.
26. `src/CategoricalCrypto/Examples/Possibilistic.agda` is a test in disguise: `eval … ≡ refl` pins plus
    one lemma over SFun at 𝒫, the same opens as `SFunM/Test/Possibility.agda`. Fold it there as a
    section (−15 of header/imports).
27. `src/CategoricalCrypto/Examples/HashForward/Audit.agda :: hf-witness` has no consumer; it is
    `audit⇒witness hf-emul`. It is a named result that `docs/quantitative-family.md` cites. Keep it,
    or define it as `audit⇒witness hf-emul` (−1).
28. `src/CategoricalCrypto/Examples/ChimericLedger/Property.agda :: εᴸ-mono` has no consumer. The doc
    says "keep (rule 32)"; the maintainer's "dead code goes" says cut (−3).
29. `src/CategoricalCrypto/Examples/ChimericLedger/Serialize.agda :: ideal-preserves-value′`: the prime
    is a fossil name. It is the concrete-`ser` instance; rename it `ideal-preserves-valueˢ`.
30. `src/CategoricalCrypto/Examples/MerkleDamgard/Pin.agda`: `a31dced8` dropped a `public` re-export on
    the grounds that it had "no in-repo importer". Under rule 32 that is a downstream-usefulness
    judgment. It is flagged here rather than silently kept, because Pin is a leaf pin module and the
    re-export served nobody.

### Statement audit

31. `src/CategoricalCrypto/Examples/CoinToss/Compose.agda :: coin-toss-from-com{,ʰ}`,
    `Ideal/Compose :: coin-toss-ideal{,ᶜ,ᴺ}`, `Receiver/Compose :: coin-toss-idealʳ{,ᴺ}`
    - Each assumes the commitment's emulation `realᶠ ≤UC^ωᵉ idealᶠ` at the OPEN resource domain.
    - `docs/rcom-icom-b1.md` R2 ("exactly what the OPEN domain does not give") and the `Assembly`
      header suggest that premise may be false. If so, these are vacuous, and
      `Realization/Assembly :: assembly{,ʰ}` are the real statements.
    - Confirm the premise is satisfiable, or demote the open-domain forms.
32. `src/CategoricalCrypto/Examples/ChimericLedger/Property.agda :: PreservesValue a V`
    (`Observable.auditWatch a V`)
    - `total (genesis h₀ a V)` reduces to `(V+0)+0`, so the property is definitionally independent of
      `a`. `ReplayFamily.chimeric-not-preserving`'s `∀ a` is vacuous in `a`.
    - Keying the watch on the total `t : ℕ` would drop the spurious parameter and could fold
      `Attack`'s `(r) (totr)` generalisation. The types are equivalent, so rule 1 is not at issue.
33. `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Game.agda :: hiding-bound-defer` is a
    hypothesis-shaped leftover.
    - Its `ε′` premise was the fcom-hiding placeholder, and `Defer.defer-hiding` now discharges it.
    - Its only consumer is `Defer.hiding-bound-total`. Inline it there as
      `≤-trans (∣-∣-triangle …) (+-mono-≤ (hiding-bound …) (defer-hiding …))`: −10.
    - Ledger: the fcom-hiding entry records it as the typed residual.
34. `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Game.agda :: respRʰ`/`respIʰ` are
    hand-written transcriptions of `realʰ` and `idealʰ ∘ simulatorʰ`, and no theorem connects them.
    `docs/fcom-hiding.md` "Not delivered" 1/3 says so. The `Hiding/Game` and `Hiding/UC` headers
    overstate it: "`respRʰ` is the real protocol", and "its ε is `Hiding.Game`" where the ε against
    the protocol is `Defer.hiding-bound-total`. The wording fix is small; the gap is yours.
35. `src/CategoricalCrypto/Examples/ROCommitment/Realization/Bound.agda :: binding-real` reads as "the
    binding property" but is the extraction-side machine/game bound. Name/doc only.

### Companion docs

36. Resynced in this run: `docs/coin-toss.md` (a dropped `upᴵʰ`), `docs/end-to-end.md`,
    `docs/ledger-lift-eps.md` and `docs/graded-bridge.md` (the `LedgerCall`/`hash-hit` references).
    Still stale:
    - `docs/quantitative-family.md`'s line citations: `ReplayFamily.agda:64`, `Transfer.agda:454`,
      `Property.agda:150`, `hf-emul = witness⇒audit hf-witness`.
    - `docs/rcom-icom-b1.md`'s line numbers (`:155` for `comSimʰ`).
    - `docs/coin-toss.md:498-502`'s "not hoisted" paragraph; see 4.
    - `docs/rewrite-verdict.md` Addendum finding 1 still names `ChimericLedger.Pin`, now `Replay.Genesis`.

### Work items (unfinished sweep classes and tooling)

- W1 `src/CategoricalCrypto/Examples/** :: import-drop` (EXPERIMENTAL `import_prune.py`)
  - Covered: the 27 ChimericLedger/CoinToss files (log `sweeps-A-examples/import-drop-partial.log`,
    20 import lines pruned and committed in `f3f18978`).
  - Remaining: the 29 ROCommitment, MerkleDamgard, HashForward, RandomOracle and Possibilistic
    files, about 700 import lines.
  - Measured cost: one full check per line, about 10 s warm, so roughly 2 h of serial agda time.
  - It is not one of the contract's required automatic classes. It stopped when the previous run
    was killed.
- W2 `.claude/sweeps/with_case.py :: transform` and `.claude/sweeps/where_inline.py :: try_site` —
  two bugs in the canonical scripts (not modified here; rule 3 of the toolkit README):
  - `with_case.py` emits `yes p → …` inside `λ where`, which parses as two patterns. Every
    constructor-with-argument site comes back `[TooFewArgumentsToPatternSynonym]`, 40 of the first
    run's 60 reds. Fix: parenthesize a pattern containing a space.
  - `where_inline.py` parenthesizes even an atomic RHS, turning `h` into `(h)`.
  - The patched copies used for this run were `/tmp/qa-A/{with_case_fixed,where_inline_fixed}.py`,
    one line each.
  - `with_case.py` also counts a `with` inside a comment as a site: 36 phantoms here.
- W3 `src/CategoricalCrypto/UC/QueryBound.agda` private block (`bindᶠ`, `map-map`, `map-cong`,
  `map-arg`, `_⟨≈⟩_`) re-implements `ProbabilisticLogic.Dp.Reasoning` (`bindᶠ`, `map-map`,
  `map-eq`, `map-arg`, `⟨≈⟩`). Found while spiking suggestion 1. Part B's file, so noted only.

## Tried, not worth it

- `src/CategoricalCrypto/Examples/ROCommitment/Game.agda :: fetch-log`,
  `ROCommitment/Transport.agda :: resKᵀ-fetchT`, `MerkleDamgard/Core.agda :: callC-marg`
  - Spiked as two-branch `with` → `case_of_` swaps: all red. The proofs need the goal to reduce
    under the abstracted scrutinee, which a `λ where` does not give (`UnequalTerms`,
    `MetaCannotDependOn`).
- `src/CategoricalCrypto/Examples/ChimericLedger/Value.agda :: lookupU-*`, `uniq-removeIn*`,
  `balance-removeIn`, `acctΣ-subOne` and the other 48 red `enum-with` probes (`with-case.json`)
  - Dependent `with`s whose branch goals mention the scrutinee: red.
- `src/CategoricalCrypto/Examples/** :: binder-drop` — 29 candidate binders, all needed (red).
- `src/CategoricalCrypto/Examples/** :: enum-where` 28 green inlines were declined on width, because
  the inlined line exceeds the file's 100-column prevailing width. The 4 reds need the binding's
  type ascription.
- `src/CategoricalCrypto/Examples/ChimericLedger/Birthday.agda :: tailStales` →
  `All.map tailStale` — landed, but only with `λ {e} → tailStale {e}`: the implicit `e` does not
  generalize.
- `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Game.agda :: hiding-bound-defer` via
  `∣-∣-triangle _ _ _` — landed, but the middle point must be given explicitly: `_` leaves
  unsolved constraints after 154 s.
- `src/CategoricalCrypto/Examples/CoinToss/Ideal/* vs Ideal/Receiver/*` as ONE parameterized
  development
  - The functionalities (`Fcoin` with abort vs `Fcoinʰ` with a wait state), the simulators and the
    state maps genuinely differ, and the receiver side alone carries the deferred-sampling hop.
  - Only the composite scaffolding is shared; that is suggestion 5.
  - Not spiked as a whole, because the scaffolding spike is the crux.
- `src/CategoricalCrypto/Examples/ROCommitment/Hiding/* vs Realization/*`
  - No notion is defined twice: the hiding half has no machine-to-game bridge, and `Realizationʰ` is
    a hypothesis type in `Assembly`.
  - The shared bulk is proof pattern, and suggestions 3, 8, 11 and 16 extract it.
- `src/CategoricalCrypto/Examples/HashForward/* vs MerkleDamgard/*` — not restatements of each
  other. HashForward is a UC-model `Proc` toy with an uninterpreted hash; MD is a layer-1
  `Protocol`/`Dist-ℚ` game hop. They share no structure.
- `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Asymptotic.agda :: εʰ, hiding-boundⁿ` — the
  forwarder drop was reverted by the maintainer (`47ba84b1` then `5846b5cd`). Not re-proposed.

## Integration-owned files

- `src/Data/Rational/Properties/Ext.agda`: `x≤x+c`, `x≤c+x` and `pos-sum-≡0` from
  `MerkleDamgard.Core` belong here. The open-coding
  `≤-trans (≤-reflexive (sym (+-identityʳ x))) (+-monoʳ-≤ x _)` recurs at 10 sites repo-wide.
- `src/CategoricalCrypto/RandomOracle.agda`, `RandomOracle2.agda`: an uninstantiated `ROData`
  hypothesis record. Nothing imports either file and the root does not import them. Their headers
  cite `Examples/MerkleDamgard.agda` fields (`≈ℰ[_]_`, `Comp.M`) that no longer exist, and the
  README §2 claim that they "package a Merkle–Damgård-vs-RO security proof" overstates it: no
  unconditional `MD ≤UC RO` exists. Deleting both (−194) frees the name for suggestion 24 and
  leaves `CategoricalCrypto.Standard` with no importer either.

## Out-of-scope edits

Only docs, all resyncs to renamed or deleted names:

- `docs/coin-toss.md` (a dropped `upᴵʰ`)
- `docs/end-to-end.md`
- `docs/ledger-lift-eps.md`
- `docs/graded-bridge.md`
- `docs/rcom-icom-b1.md`

No `src` file outside the scope list was edited.

## Verification table (tip)

| module | rc | warn grep | wall | elaborated |
|---|---|---|---|---|
| `src/CategoricalCrypto.agda` | 0 | 0 hits | 102s | 34 |
| `src/CategoricalCrypto/Examples/ChimericLedger/ReplayFamily.agda` | 0 | 0 hits | 18s | 1 |
| `src/CategoricalCrypto/Examples/ChimericLedger/Serialize.agda` | 0 | 0 hits | 12s | 1 |
| `src/CategoricalCrypto/Examples/ChimericLedger/Transfer.agda` | 0 | 0 hits | 12s | 1 |
| `src/CategoricalCrypto/Examples/CoinToss/Test.agda` | 0 | 0 hits | 12s | 1 |
| `src/CategoricalCrypto/Examples/HashForward/Audit.agda` | 0 | 0 hits | 12s | 1 |
| `src/CategoricalCrypto/Examples/MerkleDamgard/Pin.agda` | 0 | 0 hits | 8s | 1 |
| `src/CategoricalCrypto/Examples/MerkleDamgard/QueryBound.agda` | 0 | 0 hits | 10s | 1 |
| `src/CategoricalCrypto/Examples/Possibilistic.agda` | 0 | 0 hits | 8s | 1 |
| `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Test.agda` | 0 | 0 hits | 8s | 1 |
| `src/CategoricalCrypto/Examples/ROCommitment/Realization/Assembly.agda` | 0 | 0 hits | 12s | 1 |
| `src/CategoricalCrypto/Examples/ROCommitment/Realization/Bound.agda` | 0 | 0 hits | 24s | 1 |
| `src/CategoricalCrypto/Examples/ROCommitment/Test.agda` | 0 | 0 hits | 6s | 1 |
| `src/CategoricalCrypto/RandomOracle.agda` | 0 | 0 hits | 8s | 0 |
| `src/CategoricalCrypto/RandomOracle2.agda` | 0 | 0 hits | 8s | 0 |

The root line re-elaborated 34 modules on a warm cache (budget: the 1800 s ceiling). Every one of the 56 in-scope modules was also force-elaborated alone after the rebase (all green, warn grep empty), and every rebased commit re-checked at the in-scope leaves reached by its touched modules (48 source commits, 177 leaf checks, all green). Soundness grep over `src`: 16 hits at `4756d24c`, 16 at the tip, 0 in scope.
