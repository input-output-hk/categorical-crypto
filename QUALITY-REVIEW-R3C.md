# Quality review — protocol-rewrite R3C: machines, protocols, game-playing (2026-10-01)

Scope: the 45 files of `scope-R3C.txt` (Channel/*, Machine/*, Machines/**, GamePlaying*, Protocol*, Interaction,
Strategy, OracleCall) at base `27cda67f`, branch `quality-R3C`. Stopped early at the maintainer's 15:57 deadline.

Verification: root `src/CategoricalCrypto.agda` at the BASE: rc=0, 137 modules, warn grep empty. Every committed
sweep edit was kept by the toolkit oracle (per-file pagda check + warn grep); the implicit-drop survivors were
re-checked at the tip through `Machine.Core`, `Machines.Collapse` and `GamePlaying.Average` (rc=0, warn grep empty; pagda
cache hits, i.e. the exact contents the oracle had checked). The root
closure and the four non-root leaves (`ChimericLedger.{Serialize,Transfer}`, `MerkleDamgard.{Pin,QueryBound}`) were NOT
re-run at the tip. Soundness baseline (rule 3, all `src`): 16 before; no `.agda` change introduces a hatch.
Sweep tally (`QUALITY-REVIEW-R3C.d/`): using-drop complete (12 kept over 45 files, `using-drop.json`); implicit-drop
partial (first 21 files through `Machines/G`, 11 edits kept, no JSON: the tool writes it at the end; killed at the
deadline); enum-with 23 sites, enum-where 126 sites (85 flagged), enum-comments 309 blocks enumerated, NOT dispositioned.

## Committed (you can skim these)

- `6ce473b9` Machines layer: bare opens where no clash (using-drop) — 7 files, +10/−10; oracle-green per file, non-public opens.
- `ee0c0118` Protocol, Strategy: bare opens where no clash (using-drop) — 2 files, +8/−8; same.
- `bcc7b71f` Machines layer: drop inferable implicit arguments (implicit-drop, partial) — 6 files, +21/−21; oracle-green
  per file, use sites only; re-checked at the tip through `Machine.Core` and `Machines.Collapse` (rc=0, warn grep empty).
- `fe3ad1be` GamePlaying.Average: one inferable implicit (implicit-drop) — +1/−1; re-checked (rc=0, warn grep empty).

## Suggestions (need your call), ranked by LOC saved / complexity removed

### Public API / module layout
1. `src/CategoricalCrypto/Machine/Core.agda :: Machine` (with `Channel/*`, `Machine/Constraints`): **a second, legacy
   machine model.** It is `main`'s relational one-message Mealy machine on `A ⊗₀ B ᵀ` with no initial state, no laws and
   no simulation; its `_∘_` is the G/Int composition `Machines.G` builds with all its laws. Consumers: only the root's
   `public` re-exports and `Examples/{Basic,Commitment,Signatures}` (functionality definitions; no `≤UC` theorem uses it).
   `Channel/Category` and `Machine/Constraints` have zero consumers besides the root. Proposal: retire the layer
   (≈ −1,200 LOC with the three examples, R3A's files) or, if kept as `main` heritage, delete the dead half of
   `Machine/Core` (`_∣ʳ`, `_∣^ʳ`, `liftᴷ`, `_⊗ʳ_`, `⊗-assoc*`, `⊗-symₘ`, `idᴷ`, `transpose`, `⨂₁`, `_∘ᴷ_`, `_⊗ᴷ_`, `⨂ᴷ*`,
   `_≡ᴹ_` family, `Trace`/`Invariant*`, `OAP`/`ℰ*`/`_≈ℰ_`/`_≤UC_`/`_≤'UC_`: zero uses, ≈ −90) and of `Channel/Core`
   (`destruct-⊗`, `⊗-*-assoc`, `⊗-*-neutral`, `⊗-*-double-intro`, `⨂*`: ≈ −45). Statement note: `_≈ℰ_` is `≡` of
   composite records (intensional), so `_≤UC_` there is near-trivial and the "equivalent by completeness of the dummy
   adversary" comment is unproved and likely false. Diverges from `main`, hence yours.
2. `src/CategoricalCrypto/Channel/Selection.agda :: ⇒-solver-tactic'`: the "Unique solution required" error is raised
   inside the `catch` that swallows it, so an ambiguous goal silently takes the left solution. Fix by running both
   branches to `Maybe` and erroring on `just , just` (+2). Behaviour change; unspiked.
3. `src/CategoricalCrypto/Protocol/Machine/Trace/Compose.agda :: traceᴳ, outF, outG, Kᴳ, dispatch-f/g, exit∘, exit-out,
   exit-loop`: they sit under module parameters they never use (`Kg Kf gS fS`, `rank rk fuel rb`), so
   `ROCommitment/Realization/{Bisim,Machine,Bound}` pass 4–8 dead arguments per call. Split the parameter telescope into
   `(g f)` / `(Kg Kf)` / `(gS fS)` / rank levels; `exit∘` is then an alias of `Lp.exitK` (delete). Same defect in
   `Dp/Settle/Iter :: Loop` (kernels depending on settlement proofs). Out-of-scope call sites; ≈ −3 here, many shorter
   calls. Also: the module name is a leftover (`Trace/` has one child) — rename to `Protocol.Machine.Trace` (5 imports).
4. `src/CategoricalCrypto/GamePlaying/Defer/Run.agda :: DeferStep`: `μ-const` is a module parameter `DeferStep` ignores,
   so `Examples/CoinToss/Ideal/Receiver/Machine.agda:347` passes a hypothesis the type does not use. Move `μ-const` to the
   inner module of `runFrom-defer`/`run-defer` (0 LOC, cross-part call site).
5. `src/CategoricalCrypto/GamePlaying/Hop.agda :: FLGP`: `StR`/`StI` are module parameters only `hop-bound` uses, so an
   outside call of `FLGP` leaves them unsolved. Bind them on `hop-bound`.
6. `src/CategoricalCrypto/GamePlaying/Partial.agda :: hop-bound⊥`: zero code consumers (a one-line wrapper of
   `hop-boundᵇ⊥` + `badProb⊥-bounded`); delete (−9), optionally renaming `hop-boundᵇ⊥` to it (1 consumer). Docs
   `dp-transport.md:326`, `fcom-uc.md:152` name it.
7. `src/CategoricalCrypto/Machines/Pure.agda :: swap-copair`: an alias of upstream `[]∘+₁` with one consumer
   (`UC/Machine/Dictionary.agda:93`); delete and use `[]∘+₁` there (−5, cross-part).
8. `src/CategoricalCrypto/GamePlaying/Test.agda :: DeferMachine.here` (rule 33): re-proves the public
   `GamePlaying.Defer.avg-here`; retarget to `avg-here μ _≋_ F F′ pt u (proj₁ u) (inj₂ λ _ → refl)` (−5).
9. `src/CategoricalCrypto/Machines/Iteration.agda :: pad`: `pad θ = θ ⊗₁ id` is a second spelling (the rest of the layer
   writes `θ ⊗₁ id`; `Monoidal.Properties.Ext`'s `pad-*` pad the OTHER side). Inline at Congruence's ≈8 sites (−4).

### Simplifications drafted but not verified (`QUALITY-REVIEW-R3C.d/unverified-draft.patch`, 37 files, +111/−299)
All unchecked: the deadline came before a single check could run on them. Apply, check touched modules + importers.
10. Comment pass over the whole scope (≈ −150): stale `badProb-super` (Average), the false "no `GConstruction` in its
    closure" (Pointwise), stale 269/704 s timings (Collapse), dead `docs/kb/frontier/…` citation (Pin), stale "two
    bridges" (GamePlaying, Hop, Partial), garbled Raw paragraph and Test comment, overclaims (Interaction "every
    statement", Strategy "provably", Protocol "no partiality", Fubini "pure iso" — `relabel-step` needs only a retraction),
    export-list and proof narration (Pure, Bundle, Sandwich, Trace, Fubini, Safety, Agree, Defer, Defer/Run, Hop, Test,
    Machine/Core TODO/notes), rule-24 duplicates (G's `βᴹ` pointer, Compose's paragraph 4, Potential's lazy-sampling NB).
11. Dead code / aliases (internal Machines layer): `Trace :: traceᴹ-cong` (0 uses, −5), dead opens in `Trace`
    (`BraidedProps`, `Iteration`, `PureSub`) and in `Trace/{Fubini,Vanishing}` (`Frame`), `Sim :: ≈ᴹ-isEquivalence`
    (0 uses; `reflᴹ`/`⟺ᴹ`/`_○ᴹ_` via `EqC.reflexive/symmetric/transitive`), `Frame :: 𝕄` (alias of `monoidalCategory`),
    `Fubini :: pure-swap` (single use), `Assoc :: ⊗-split` unused implicit patterns.
12. Proof swaps: `Safety :: super` deleted, `hit-bounded = ≤-trans (hit≤badProb⊥ …) (badProb⊥-bounded cert …)` (−7,
    statement unchanged); `Partial :: StepBisim⊥ = StepBisim⊥ʳ id id …` (−2); `Trace/Compose :: dispF/dispG` inlined
    (−11) and `compose-StepSettles.value` via `Kᶜˡ-read` (−5), `I.` qualification dropped; `Interaction ::
    runWith⊥-emb` via `>>=ᴹ-congˡ` (−4); `Potential`/`Average` hand-rolled `x ≤ x + y` → `Data.Rational.Properties.Ext.p≤p+q`
    / `p≤q+p` (≈ −10).

### Further unverified finder items (not drafted)
13. `Machines/Tensor.agda :: tstep-sim` via `tstep-pad` + `tstep-∘` (−3); a shared `tstep-relabel` replacing
    `Fubini`'s private copy and `Vanishing :: iterv-i₁.tstep-ν` (−3); `Vanishing :: ∇ψ.∇ν` as one `[]∘+₁` step (−7);
    `Pure.∘-pureᴹ`/`⊗-pureᴹ` moved to `Tensor` so `Fubini :: βᴹ-pure`'s `where` goes (−5).
14. `Protocol/Machine/Trace/Compose.agda :: MT, V, K, 𝒢` and `Compose.agda :: MC, MT, S` re-apply modules
    `Collapse`/`Pointwise` already export (L879 class; re-measure perf).
15. The "eventually equal" Σ-shape `Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n + i) d Q ≡ v)` is written 12× (in scope: `prAgree`,
    `rawPr`, `compose-pr`): name it once in `Dp.Settle` (L757, home moved since `Dp.Stable` was deleted).
16. `Machines/Core.agda :: mk` as the record's `constructor` (−2, 37 files); `Collapse :: Loop.loop-fix` eta-wrapper;
    `Base :: Elgotᵏ` plumbing private; `Frame :: onL-str` rename to `onL-id⊗` (mirror of `onR-id⊗`);
    `Pointwise :: ⊗-pureˡ h = K.pureᵏ-⊗ h id` (second spelling at `UC/Seam/Budget:133`).
17. `GamePlaying.agda :: prune-cert` re-binds the `private variable` telescope and a local `Φ`; `Coupling`/`Coupling⊥`
    duplicate `fR`/`fI` (−3); `Defer`'s averaged-point premise written 4× (name it, −4); `Partial :: Pr₁⊥-coin` inline.

## Tried, not worth it
- (none this round)

## Not reached
- **Sweep classes**: implicit-drop on the 24 files from `Machines/Iteration` on; join-lines, binder-drop, import-drop,
  using-minimize, with-case, where-inline not run at all. Measured cost under today's gate contention: implicit-drop took
  ≈ 2 h for 21 files (Machines/Category alone ≈ 40 min).
- **Enum dispositions**: none of the 23 `enum-with`, 126 `enum-where` (85 flagged) or 309 `enum-comments` sites is
  dispositioned site by site; item 10 covers the comment blocks the finders flagged, not all 309.
- **Verification**: items 10–12 (the draft patch) are unchecked; items 1–9 and 13–17 are unspiked; the tip's root closure
  and the four non-root leaves were not re-run.
- **Files**: every file was read by a finder on dimensions 1, 2, 4, 5, 6, 7, 9; no perf (dimension 3) measurements were
  taken, and no companion-doc (dimension 8) pass was made.

## Out-of-scope edits
None.
