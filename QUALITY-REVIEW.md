# Quality review — leaner-frame-decode-lever1 (2026-07-06)

Scope: the `src/Categories/APROP/` subtree, prioritising the recent-work set —
the `monoidal-coherence-solver` merge (`0ac0b17`, which within APROP renamed the
`Embed.agda` helpers and re-pointed the whole soundness cone at
`Categories.SolverFrontend`) and this branch's perf/decode/cleanup commits. All
four finder passes (Interchange+Tensor, Discharge/Sub, Decode+Base, Solver+Model)
were run read-only; the parent applied, verified, and committed serially.

Verification: `pagda` check run yes — every commit re-verified green (rc=0 AND the
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing` warning-grep empty).
The three maintainer-approved follow-ups (cfee194 essays / d1266d9 dead alias /
5ec2350 Perm.refl no-op) landed and were re-verified: TensorKBlock+TensorBraid green,
Frontend + its Frobenius importer green, LinearityIso green; closure re-run green
(the four `Solver/Test/*Tests` suites + `src/CategoricalCrypto.agda`, all rc=0
warn=0); APROP soundness escape-hatch grep only SHRANK (deleted comment prose
mentioning "postulate"), no category grew, `--safe --without-K` intact.
(Original run:)
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing` warning-grep empty)
under each file's own OPTIONS, importers included. Closure check green: the four
`Solver/Test/*Tests` suites (`FindIsoTests` transitively pulls the whole soundness
cone) + `src/CategoricalCrypto.agda`. Soundness baseline: APROP escape-hatch grep
38→36 lines (only two "zero postulates" comment lines removed + one "postulate-free"
comment reworded — no real `postulate`/hole/`TERMINATING`/`trustMe` added or
removed); no category grew. `--safe --without-K` intact everywhere.
Sweep tally: `using-drop` class only, on 12 recent-work files (JSONs in
`quality-tallies/`): Split 11/12 kept, FromAPROP 5/8, PrunedCompose 7/10, Decode
10/12 (1 skip), DecodeAttempt 10/13, DecodeAttemptLinearP 14/18 (1 skip), ExtendSig
11/13 (1 skip), Verify 13/18 (1 skip); Boundary + DecodeGen aborted (baseline
transiently red under concurrent edits — later verified green, not re-swept). The
`join-lines` / `implicit-drop` / `binder-drop` classes were NOT run (see Remaining).

## Committed (you can skim these)
- 5b6aa0f cleanup(APROP): drop non-clashing using-lists on imports (rule 11) — FromAPROP, PrunedCompose, Split; bare opens, green + warning-clean.
- a40cb77 cleanup(APROP): drop non-clashing using-lists (cont.) — Verify, ExtendSig, Decode, DecodeAttempt, DecodeAttemptLinearP.
- e5db383 cleanup(APROP): remove dead internal helpers — PBij.lookup?, SwapCore.box-residual-split, FireMid.box-unsuffixˢ, IsoInvarianceWiring.ψ-pres-dep (grep-confirmed 0 refs; stale comment mentions updated).
- 3d6e0f6 cleanup(APROP): remove dead helpers in Discharge/Sub — HomTermTransport ×5, StackUnique's dead edge-step-uniqueness subsystem + coh-fin-rigid/residual-recon-unique/-via-rigid, BoxKernel.BoxAssoc.assoc-from/subst-id-{dom,cod}, SeparableStack.coe (−208 LOC).
- 0aa4ef0 cleanup(APROP): fix stale comment references to deleted code — Kahn/DecodeLean (DeepProv/BuildO/EdgeO/pairsO gone), ObjUIP + DecodeAttemptLinearP (DecodeRelRespIsoWired gone), SeparableStack (DecodeTensorShape gone).
- 9d2bf99 cleanup(APROP): trim development-history narration — "now/re-pointed/no longer/kept-stable/TYPE-unchanged" across Soundness.agda, FromAPROP, Invariant, Tabulate, PartI, PartII, DecodeProperties.
- f035365 cleanup(APROP): drop refactor-history from consolidated modules — FireMid + TensorKBlock "CONSOLIDATED/CONSOLIDATION EXPERIMENT / former X → submodule Y / re-derivation of F2's private" history.
- cfee194 cleanup(APROP): drop stale ⊗-shape obstruction-map essays — TensorKBlock's six "THE CHAIN / OBSTRUCTION / RESIDUAL MAP / STATUS — NOT YET unconditional / BLOCKED by module privacy" submodule trailers + TensorBraid's matching "ONE REMAINING WIRING GAP" footer, all false now that TensorKBlockFinal.decodePˢ-⊗-concrete discharges KBlockσ unconditionally into Soundness.soundness. Comment-only (−349 / −56); submodule banners, citations, and TensorBraid's non-false STRATEGY header kept; both modules re-verified green.
- d1266d9 cleanup(APROP): remove dead public alias Frontend.rewriteDeepₙ!ᵀᴮ (0 callers; sibling rewriteDeepTo!ᵀᴮ kept — Frobenius uses it) + fixed the wrong header comment; Frontend + Frobenius importer re-verified green.
- 5ec2350 cleanup(APROP): inline vacuous Perm.refl no-op in LinearityIso.tabulate-bij-↭ (a reflexive endpoint prepended to the trans chain; same statement, verified green).

## Suggestions (need your call)

### Public API / module layout
- `src/Categories/APROP/Hypergraph/Solver/Frontend.agda :: (import of Split)` — `using (solveSplitR?; reassoc; reassocBal)` imports `reassoc`, which Frontend never uses (only `reassocBal`/`solveSplitR?`). Narrowing the `using` here is mechanical, but Frontend is a heavy downstream module I did not re-verify; drop `reassoc` from the list on the next pass.
- `src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/CountCombinatorics.agda :: count-pos→extract-elem` — not dead (internal user `count-≤→extract-prefix`) but 0 external consumers; `private` candidate to shrink the export surface (rule 29 — keep-public unless you agree).
- `src/Categories/APROP/Hypergraph/Soundness/Discharge/CIsoAssocFromCons.agda :: c-iso-assoc-from-cons` — the `-cons` alias has 0 external users (consumers call `c-iso-assoc-from` directly). Removable if nothing downstream imports the alias.

### Test-suite targeting (rule 30)
- `src/Categories/APROP/Hypergraph/Solver/Test/FrontendTests.agda :: Crossings.byHand` — a 10-step manual `HomReasoning` proof of the same equation `Crossings.auto` proves via `solveH!`, with no external reference. Reads as a deliberate "manual vs one-line solver" showcase; if that contrast is not wanted as documentation it is a droppable ~22-line redundancy. (All four suites otherwise correctly pin public entry points — `soundness`/`findIso`, `solveH!`, `solveH!ˢ`, `subMatch`.)

### Simplifications / dedup not committed (judgment needed)
- `Strict/Interchange/SwapCore.agda`, `Strict/Interchange/StackEquiv.agda`, `Strict/Tensor/TensorKBlock.agda` (TKB/TKB2/TKB3) :: `fire-termˢ` — an identical "local copy" re-defined in ~5 modules (the comments themselves flag "identical to TensorKBlock.fire-termˢ"). A shared home (a small `Strict/…` helper module) would dedup it, but the copies each sit under different module parameters; needs a spike to confirm the shared version threads the parameters cleanly. Not attempted.

## Remaining mechanical cleanup (enumerated; deferred for budget, NOT judgment)
These are rule-20/21/23 comment-hygiene commits the contract assigns to me; I ran
out of budget after the accuracy-critical work above. All are located by the four
finder passes; none needs a decision.

- **Stale obstruction-map essays — DONE (cfee194).** TensorKBlock's six submodule
  trailers + TensorBraid's footer cut. TensorBraid's STRATEGY/"WHAT IS GREEN HERE"
  header was reviewed and KEPT: it states no stale "still blocked" claim — it is
  genuine (true) architecture orientation for a hard proof — so it falls outside the
  "remove the false narrative" mandate. It remains a rule-21 (>25-line) trim
  *candidate* if you want the header shortened, but that is a judgment call, not a
  correctness fix.
- **Design-essay headers/trailers (rule 21, >25 lines).** `Strict/Decode/DecodeCompose`
  (84-line header + 50-line trailer "OBSTRUCTION MAP"), `Strict/Decode/DecodeTensor`
  (42 + 44), `Strict/Separability` (36 + 42; keep the genuine "why no term-sepˢ-ˡ"
  impossibility *why*), `Strict/Decode/DecodeSigma` (30 + 28), `Strict/Decode/DecodeShapes`
  (37-line trailer), `Strict/Interchange/SwapCore` (42), `Discharge/FinOrderNoInv` (37),
  `Discharge/Sub/BoxKernel` (29), `Discharge/Sub/FireMidEquivariant` (30),
  `Discharge/Sub/SeparableStack` (header still ~30 after my one-line fix). Trim to
  orientation; move any real essay to `docs/` with a pointer.
- **Comparison / notes-to-self narration.** `Strict/Interchange/{StackEquiv,SwapStep,
  RunInterchangeTail}` (non-strict-vs-strict "DISAPPEARS / REUSED VERBATIM / 1:1 port"
  essays + a self-answering Q&A in `RunInterchangeTail.tail-reservoir`),
  `Strict/Perm/PermDischarge` ("migration brief" + route-not-taken),
  `Strict/Tensor/{TensorKBlockFinal,TensorPVVRelabel}` ("Phase 8 / the false puq is
  GONE" / "verbatim factor-out of the copy inside…").
- **Type-restatement one-liners (rule 20).** `Discharge/FinOrderNoInv` (`NoInvH`,
  `tensor-KK-reflect`, `↑ˡ-↑ʳ-disjoint`), `Discharge/IsoInvarianceWiring.τ↭range`,
  `Discharge/BridgeAlphaFormCompound` (F-/T-decomp block comments + "F-decomp lemmas"
  banner that also heads T-decomp), `Discharge/CIsoAssocFromCons.c-iso-assoc-from`
  (Step 1/2/3/4 per-link), `Sub/BlockNFBraid`, `Sub/BoxKernel.BoxAssoc.box-*`
  (paraphrased solver-setup essay ×3), `Sub/FireMidEquivariant`, `Sub/PermutationTransport`.
- **Per-definition `----` dividers (rule 23).** Pervasive in `Strict/Tensor/*` (`## X`
  headers over a single def) and `Discharge/Sub/*`. Demoting to a one-line comment is a
  whole-family cut (rule 24), not per-site.
- **Not-yet-swept (automatic sweep classes).** `join-lines`, `implicit-drop`,
  `binder-drop` were not run on any file; `using-drop` covers only the 12 recent-work
  files (Boundary + DecodeGen aborted, re-run needed; the broader subtree not swept).

## Tried, not worth it
- `.claude/sweeps/sweep.py` — the `using-drop` sweep crashes with `shutil.SameFileError`
  on a file that yields zero candidates (`copyfile(path, path)` in the "untouched"
  branch); this aborted the first batch mid-run. Worked around by running the remaining
  files one at a time. Flagging per README rule 3 (do not modify a canonical script
  silently) — the maintainer may want to guard that `copyfile`.
