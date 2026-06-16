# APROP hypergraph-solver module reorganisation plan

Status: **PLAN ONLY — not executed.** Produced after the WIP-name + comment cleanup
(commits `cf11498`, `f8a8305`). Reviewed by two adversarial passes: the structure is
validated as genuinely clearer (not change-for-change); the safety pass found two
execution blockers (below) to fix before running, plus five owner decisions.

## Organising principles

1. **Separate the three layers** under `Categories/APROP/Hypergraph/`:
   `Model/` (the `Hypergraph` type + translation `⟪_⟫`), `Solver/` (the decision
   procedure / rewrite gates the user calls), `Soundness/` (why a yes-answer is a real
   equation). Each layer typechecks independently; the path tells you which layer a file is in.
2. **Group by role, not build-order.** Drop trailing-digit / `Done` / `Final` stage
   markers and the redundant Strict `…S` twin-suffix; use role sub-directories instead.
3. **No spikes in the library tree.** Orphaned / non-`--safe` scaffolding moves to a
   top-level `spikes/` outside the `agda-lib` include (so `--safe` never depends on it),
   or is deleted if subsumed.
4. **Meaningful names** — a filename states its role (no vacuous `-Safe`, no `Spike` on
   production code, no grab-bag `Lemmas`).
5. **Tests in a `Test/` dir; the public theorem discoverable** (the `soundness` theorem
   becomes the named facade of the `Soundness/` directory).

## Target hierarchy (sketch)

```
Categories/APROP/Hypergraph/
├── Model/      Core, Iso, FromAPROP, Translation, PrunedCompose, Invariant, HomTermInvariant
├── Util/       Prune
├── Solver/     Frontend (was Interpret), Split, Signature, FinSignature, Tabulate,
│   ├── Match/      PBij, Totals, Seed, Match, Search, Verify, FindIso, FindIsoTab
│   ├── Rewrite/    SubMatch, ExtendSig, DecodeLean, Carve, Deep, DeepProv
│   └── Test/       FindIsoTests (was Tests), FrontendTests, SplitTests, SubMatchTests
├── Soundness.agda   ← public theorem (relocated SoundnessFullWired; defines `soundness`)
└── Soundness/
    ├── Base/       Unflatten, UnflattenMonoidal, Permute
    ├── Decode/     Decode, DecodeProperties, DecodeAttempt
    ├── Bridge/     Bridge (extracted), BridgeOps, BridgeCoherence (was DecodeRoundtripSafe), BridgeAlphaForm
    ├── Linearity/  Linearity, LinearityIso
    └── Strict/     Frame/, Decode/, Interchange/, TensorShape/, …  (role sub-dirs; S-suffix + stage digits dropped)
```
Also: `Categories/MonoidalCoherence` → `Categories/Coherence/Monoidal`; `PermuteCoherence/`
gains role sub-dirs (`Base/`, `Inversions/`, `Exchange/`, `Insert/`, `Canonical/`, `Faithfulness/`).

## Concrete cleanups (all grep-verified)

**Deletions (orphans):**
- `Coherence/DecodeSpike.agda` — 0 importers; it is the *only* importer of `Soundness/DecodeRel`.
- `Soundness/DecodeRel.agda` — orphan once `DecodeSpike` is gone (soundness is re-routed
  through `Strict/`). *Notable: `DecodeRel` was once central; the experiments merge re-pointed
  the live proof path through the strict pipeline, leaving it dead.*
- `SymmetricMonoidalCoherence/Matrix.agda` — 0 importers (unless promoted; see decisions).
- (root spikes) `FrobProbe.agda` (dup of the `Test/Frobenius` showcase).

**Dedup:** `bridge-∘` / `bridge-⊗` are defined **verbatim twice** (`BridgeOps.agda` and
`DecodeRoundtripSafe.agda`); canonicalise on `BridgeOps`, repoint the 3 other consumers.

**Renames (role-honest):** `DecodeRoundtripSafe→BridgeCoherence`, `SeparableSpike→SeparableStack`,
`WiringLemmas→NoInvTau`, `PermuteCoherence/Map→FinBijSubst`, `PermuteCoherence/Soundness→EvalSoundness`,
`Interpret→Frontend`, `Tests→FindIsoTests`, `FireMidDone→…/FireMid/Assembly`,
`TensorKBlockFinal→…/KBlock/Close`, `TensorKBlock{,2..6}→KBlock/{Prepend,Stage2,FireSlide,KFacFold,HeadProvider,HeadSlide}`,
`DecodeComposeS{,2,3}→DecodeCompose/{Block,Stage2,Assembly}`, `FireMidS{,2}→FireMid/{Part1,Part2}`,
drop the trailing `S` on ~10 Strict files, `SoundnessFullWired→Soundness.agda`.

## Phased migration (low-risk-first, `--safe`-verifiable per phase)

0. **Baseline** — record green cold-build of the two public roots (`SoundnessFullWired`, `Coherence/Symmetric/Test/Frobenius`) + the import-edge list.
1. **Deletions** — remove the verified orphans; re-grep no importers; both roots green.
2. **Dedup** — collapse `bridge-∘/⊗` to `BridgeOps`; repoint consumers; root green.
3. **In-place renames** — module decl + every importer's import line (no dir change yet); verify the owning root after each.
4. **Spikes out of `src/`** — move `CruxSpike`/`GlobalPhiDirect`/`Leg1Carve`/`Leg3Recomp` to `spikes/` (off the include path).
5. **Leaf-cluster moves** — low-fanout dirs first (PermuteCoherence, Soundness sub-clusters), one cluster per commit.
6. **Model layer move** (highest fanout — `FromAPROP` 82 / `Core` 74 importers) + relocate the `Soundness.agda` facade; verify **both** roots after each file.
7. **Optional** — `MonoidalCoherence→Coherence/Monoidal`; resolve `SoundnessAssembly`/`SoundnessStrict` overlap; owner-deferred items.

## ⚠ Execution blockers to fix before running (from safety review)

1. **File→directory-of-same-name collisions.** Several cluster heads keep their name as
   the new directory: `Match.agda`+`Match/`, `Decode.agda`+`Decode/`,
   `PermuteCoherence/{Canonical,Inversions,Faithfulness}.agda`+same-named dirs. Each must be
   an **atomic** `git mv X.agda X/X.agda` (never mkdir-then-move; the intermediate state is broken).
2. **Unmapped live cluster `src/Categories/Hypergraph/`** (NON-APROP): `ExtractPrefix`,
   `ExtractPrefixEvalPhi`, `ExtractPrefixMapPhi` — load-bearing (imported by `Soundness/Decode`,
   `SeparableSpike`, `FreeSMC/Steps`, several Strict files). The plan's maps omit it; the reorg
   must account for it (it is not part of the APROP `Hypergraph/` subtree being restructured).

## Owner decisions (needed before/within execution)

1. **Route-A provenance gate** — LIVE (`DeepProv`→`Frontend`'s `rewriteDeepProv*`/`findIsoGate2`,
   used by the Frobenius showcase). Recommend KEEP as `Solver/Rewrite/DeepProv`. Open: are the
   witness-plan spikes (`Leg1Carve`/`Leg3Recomp`/`GlobalPhiDirect`) still a useful proof-obligation
   ledger (→ `spikes/`) or folded into Soundness (→ delete)?
2. **`decode-attempt → decode`** tree-wide value rename (~40 modules) — only if the "attempt"
   nomenclature is now misleading; change-for-change otherwise. Decide before Phase 3 to batch it.
3. **Strict staging chains** — keep as role-named files in chain sub-dirs (recommended; the split
   bounds typecheck memory, e.g. `FireMidDone` is ~975 LOC) vs. genuinely consolidate (risks OOM).
4. **`soundness` theorem placement** — confirm `Hypergraph/Soundness.agda` as the public facade,
   and which of `Strict/SoundnessAssembly` vs `Strict/SoundnessStrict` is the canonical strict root.
5. **`Matrix.agda`** — delete (default, 0-importer) vs promote+wire as the braided-coherence substrate.

## Decisions resolved (2026-06-16)

1. **Route-A spikes → `spikes/` (preserve, not delete).** They are 0-importer ledgers of the
   abandoned frame-iso/completeness route (`GlobalPhiDirect` = the machine-checked "frame-iso = the
   kernel" NO-GO; `Leg3Recomp` holds the salvageable `focusAtₙ-sound`/`retract-sound` lemmas). Keep the
   provenance gate itself (`DeepProv` etc.).
2. **Keep `decode-attempt` (no rename).** The "attempt" encodes the genuine `Maybe`-partiality; renaming
   to `decode` would lose information and churn 14 files. Not a WIP artifact.
3. **CONSOLIDATE the heavy sub-chains** (experiment verdict: perf is a clear win — `TensorKBlock 1..6`
   merged = ~4× faster cold typecheck, 1.5 GiB peak, no OOM). Merge the big chains, rename-only the light
   or cycle-blocked ones. **Hard cap:** a full chain cannot be one module where a dependency cycle exists
   (e.g. `TensorKBlock4 → TensorBraidS → TensorKBlockFinal`), so `TensorKBlockFinal` stays separate; max
   unit = `1..6`. The merge is engineering-fragile (recurring Strict re-export name-clashes: needs a
   Decoder-alias + faithful `using`-restriction preservation) — a one-time careful cost per chain.
4. **Public theorem → `Hypergraph/Soundness.agda`.** Trace finding: the two strict roots are a 2-level
   chain, not synonyms — `SoundnessAssembly` is the capstone the public theorem calls, `SoundnessStrict`
   is its sub-step. So unify by role: `SoundnessAssembly → Strict/Soundness.agda` (the strict capstone),
   `SoundnessStrict →` a role name (its decode-iso-invariance sub-step). Final names confirmed at rename time.
5. **Keep `Matrix.agda` for now** (do not delete); it is `--safe` + postulate-free. Give it a tidy home if
   the braided-solver direction stays of interest; revisit deletion later.

## Progress

- **Phase 1 (deletions) — DONE** (`4f8a133`): deleted dead `DecodeRel` + orphan `DecodeSpike`, removed the
  stale back-ref comment; soundness cone re-verified `--safe`.
- Remaining: dedup (folded into the `DecodeRoundtripSafe→BridgeCoherence` rename), the `#3` consolidation
  experiment, the rename phase, and the directory restructure (with the two blocker-fixes). Spikes→`spikes/`
  per decision 1.
