# Quality review — protocol-rewrite, part R2b (2026-10-01)

Scope: `scope-R2b.txt` — `UC/Machine/StateEvent{,/Adequacy,/Agree,/HitTests,/Lift,/Read,/Spike/Carry}`,
`UC/Machine/EventBounds{,/Transport}`, `UC/Machine/Monitor/Slide`, `UC/Seam/Grounded`,
`Machines/{Category,G}`, `Protocol/Machine/Trace/Compose`, `Examples/ChimericLedger/{Property,Transfer}`.
`ChimericLedger/Property.agda` is also on R2a's list, so it was reviewed read-only (suggestions only).
Base `133f630e`, branch `quality-R2b`.

Verification: pagda check run: yes. Root `src/CategoricalCrypto.agda` at `-M8G -H2G`: rc=0, warn grep empty, after every
cone-touching commit and at the tip (see the report table). Leaves reached outside the root: `ChimericLedger.Transfer`,
`ChimericLedger.Serialize`, `MerkleDamgard.QueryBound`, `StateEvent.Spike.Carry` — all green at the tip.
Soundness baseline (rule 3, over `src`): 16 before, 16 after, identical lines.
Sweep tally (`QUALITY-REVIEW-R2b.d/*.json`, kept/candidates): using-drop 33/48 (+6 opens by hand in Lift);
implicit-drop 123/153 first pass, of which five files aborted, rerun 14/17 (+ Lift by hand); binder-drop 0/36;
join-lines 28/35; enum-with 0 sites; enum-where 42 sites + Lift by hand, every one dispositioned below;
enum-comments 133 blocks + 17 in Lift, every one dispositioned below. `StateEvent/Lift.agda` does not parse under the toolkit grammar (nested `case … of λ where`
inside a clause with a `where`), so every class was done on it by hand.


## Committed (skim)

Net over `src`: 15 files, +264 / −398 (−134). Every commit: touched modules and the root re-checked, warn grep
empty; the ChimericLedger leaf re-checked whenever its cone changed. Timings are warm single-module, before → after.

- `3e059311` (+33/−33) using-drop sweep: 33 non-clashing `using` lists to bare opens (toolkit-verified per file).
- `0c0c466e` (+6/−6) the same, by hand, in `StateEvent/Lift` (the sweep grammar cannot parse it; the bare
  `Categories.Category`/`PropositionalEquality` opens clash, so those keep `using (Category)` / `hiding ([_])`).
- `3ff1e3e1` (+42/−84) comments: dangling `trace-pt`/`solve-pt` and misqualified `Settles-iter` (Trace.Compose),
  the stale "`UC.Audit`'s header" citation and a misattributed contract row (EventBounds), the false "one `assoc`
  away from definitional" claim (Seam.Grounded), wrong terms ("renaming", "depth", "`Bad`", "exactly one ask",
  "`cap` beyond the cap"); type-echo and "the old theorem" glosses cut; Trace.Compose's 28-line header to 14; the
  `onL-α` gotcha moved from the `Machines.Category` header to `onL-α` (rule 24); Machines.G header narration cut.
- `03ff9eb1` (+69/−69) implicit-drop sweep, Machines.{Category,G}, Monitor.Slide, Trace.Compose, EventBounds
  (warm times 9→10, 15→15, 20→19, 10→10 s).
- `dc48153b` (+20/−24) implicit-drop rerun on the five files the first pass aborted (their cone was rebuilding under
  the 5G heap), plus `Lift` by hand; `flag-slide`'s `bottom` keeps its objects (red without them).
- `818b1e34` (+28/−57) join-lines sweep. binder-drop ran on every file and kept nothing (tally committed).
- `c2e15290` (+1/−4) `Transfer :: ledger-uc-to-pov-family` stated as `BoundedHitᴺ R badR (λ n q → εᴹ n (q + q))`,
  which its four-line result type was, verbatim up to unfolding.
- `ffdde432` (+1/−2) `HitTests :: wait-irrelevant` is `stateRead-hit …` itself (`PrHit becomesBad id (out false)`
  reduces to `0ℚ`).
- `e1257d73`, `20a55527`, `3915307e`, `56fccf6a`, `89d24c08`, `a4bc198c` (+81/−137 together) enum-where
  dispositions that came back green and perf-neutral (list below).
- `214ef97c` (+1/−0) a one-line gotcha on `StateEvent :: ▷-≲`'s `pt` (inlining it costs 18 s → 184 s).


## Suggestions (need your call), ranked by complexity removed

### Structural

1. `src/CategoricalCrypto/UC/Machine/Monitor.agda :: compileᴹ` vs `src/CategoricalCrypto/UC/Machine/StateEvent/Read.agda :: flagReader`. **Two readers are one reader, and a monitored event is a flag-wire event.**
   - Today `compileᴹ B μ Y E = flagReadᴹ ∘ (subᴵ E ∘ (a⇐ᴵ ∘ T₁ᴵ Y μ))` and `flagReader B Y E = flagReadᴹ ∘ (subᴵ E ∘ a⇐ᴵ)`. So `compileᴹ B μ Y E` is `flagReader B Y E ∘ T₁ᴵ Y μ` up to `assoc`.
   - Spiked green in a scratch module (not committed, 10 s):
     `eventRun Y f μ E m ≈ₚ readRun Y (μ 𝒫.∘ f) (flagReader B) E m`, hence
     `HitsAt q r f μ ⇔ BoundedAt q r (μ 𝒫.∘ f) (flagReader B)`, both directions in one line each. The proof is two
     `assoc`s and the dead `EventBounds :: ctxRun-∘`, which gains its first consumer.
   - Proposal, stage 1 (about −10, interface-visible, Monitor/EventLift are R2a's files):
     move `flagReader` into `UC.Machine.Monitor` beside `flagReadᴹ`; define
     `HitsAt q r f μ = BoundedAt q r (μ 𝒫.∘ f) (flagReader B)` and retire `compileᴹ`/`eventRun` (or keep `compileᴹ`
     as `flagReader B Y E 𝒫.∘ T₁ᴵ Y μ`). One reader, one event-bound notion; `HitsAt` becomes "the state event of the
     monitored process".
   - Stage 2 (the real win; about −250..−400 across `UC/Quantitative/EventLift{,/Cov}`, `UC/Machine/Monitor/Slide`,
     `UC/Machine/Dominated`): two hand-built "+1 certificate of the reader over a closed test" developments exist side by
     side — `StateEvent/Lift :: FlagCert`/`FlagShaped`/`shaped-run`/`flagSkeleton`/`flag-slide` (state events) and
     `EventLift/Cov :: Cert`/`CovCtx`/`Dominated.eventSkeleton`/`Monitor/Slide.compiled-slide` (monitors). With stage 1,
     `hitsᵘ` would follow from `stateLift` if `monitorᴹ report 𝒫.∘ u ≈ᴹ u′ ▷ acc` for `u′` the monitored process with the
     flag port forgotten and `acc` its accumulator, plus the strategy agreement
     `runᴹ (u′ ▷ acc) (flagStrat d) ≈ₚ runᴹ u (watchFrom report false d)`.
   - Crux (NOT spiked): that simulation. Both flags are updated only at completed `B`-answers and the accumulator is
     monotone, so the flag `▷` accumulates equals the monitor's `acc` pointwise; the cost is stating a test on the state
     of a 𝒢-composite (`Machines.Collapse` state). First step: prove it for `Watch.watchᴹ` (already a collapsed
     one-machine form with the accumulator in its state). Estimate 2–3 sessions; go/no-go after the crux.

   The scratch proof of the reader identity, for reference:
   ```agda
   eventRun-flag : eventRun Y f μ E m ≈ₚ readRun Y (μ 𝒫.∘ f) (flagReader B) E m
   eventRun-flag = step ⟨≈⟩ ≈sym (ctxRun-∘ Y (flagReader B Y E) m μ f)
     where
     step : eventRun Y f μ E m ≈ₚ ctxRun Y (flagReader B Y E 𝒫.∘ T₁ᴵ Y μ) m f
     step = runᴹ-resp-≈ᴹ {Ωᴵ} (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ʳ 𝒫.sym-assoc S.○ᴹ 𝒫.sym-assoc))) (ask tt out)
   ```

2. `src/CategoricalCrypto/UC/Machine/EventBounds.agda :: Boundedᴺ`, `StateEvent/Adequacy.agda :: BoundedHitᴺ`,
   `Examples/ChimericLedger/Property.agda :: preservesValue⇒saturated` (result type). **One saturated-quantifier notion.**
   - The shape `(p : ℕ → ℕ) → Poly p → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν × ((n : ℕ) → X n (p n) (ε n (p n) ℚ.+ ν n))`
     is written out four times, and its `let ν , neg , b = h p Pp in ν , neg , λ n → …` plumbing six times
     (`Adequacy :: hitᴺ⇒stateᴺ`, `stateᴺ⇒hitᴺ`, `Transport :: transportᴺ`, `Property :: preservesValue⇒saturated`,
     `preservesValue⇒stateSafe`, `Transfer :: ledger-pov-family-negligible`).
   - Proposal: `Saturated X ε` and `saturated-map` in `UC.Approximate` beside `GradedBound` (8 lines); then
     `Boundedᴺ f 𝔠 = Saturated (λ n q r → BoundedAt q r (f n) (𝔠 n))`, `BoundedHitᴺ P Bad = Saturated (λ n q r → (d : …) →
     asks≤ q d → PrHit (P n) (Bad n) d ℚ.≤ r)`, and `hitᴺ⇒stateᴺ ε = saturated-map λ n q → hit⇒stateBounded … q`
     (likewise `stateᴺ⇒hitᴺ`). Spiked green in a scratch module (9 s): both identities hold by `refl`
     against the current definitions, and both maps are
     `saturated-map {ε = ε} λ n q r → hit⇒stateBounded (P n) (Bad n) (T n) (bd n) q {r}`, with
     `saturated-map g h p Pp = let ν , neg , b = h p Pp in ν , neg , λ n → g n (p n) _ (b n)`.
   - Net about −10 LOC; the gain is one notion instead of four spellings. `UC.Approximate` is outside this part's scope.

3. `src/CategoricalCrypto/UC/Machine/StateEvent.agda` — **the library module carries a test suite.** The "Acceptance
   examples" section (`rename`, `padᴹ`, `unused`, `ghost`, `erased`, `erase`, `ghost-no-descent`, ≈45 LOC) and the
   `refl` pins `pullTest-id`/`pullTest-∘` have no code consumer; they pin behaviour. Move them to a test module
   (`StateEvent/HitTests` or a sibling `StateEvent/Tests` wired into the root's test list, rule 33), keeping
   `ghost-no-descent` cited from the header. Also dead and a second spelling: `StatePred`/`pullPred` (`StateTest` is
   the notion every consumer uses; −5), `unflag`/`unflag-▷`/`dropF` (−32; only `docs/flag-wire-spike.md` cites them),
   `eventSim-refl`/`eventSim-trans`/`≈ᵉ⇒≈ᴹ` (keep: the preorder structure of `EventSim` is the API; rule 32).

4. `src/CategoricalCrypto/UC/Machine/StateEvent/Spike/Carry.agda` — **an unwired `Spike` module.** No importer, not in
   the root, so nothing checks it (it is green at this base, 10 s). Its one theorem `flag-carry` is `audit-carry`
   applied verbatim. Either delete it (−51) and turn `docs/state-event-transport-spike.md` §1 (c) into prose, or wire
   it into the root as a leaf. Deletion is the maintainer's history-module rule; the doc is outside this scope.

### Lemma dedup (generic material, outside this scope's files)

5. `src/ProbabilisticLogic/Dp/Mass.agda :: mass-bindʳ` — generalise to any non-negative test
   (`(P : B → ℚ) → NNF P → … ((p : A) → cum n (k p) P ℚ.≤ c) → cum n (d >>=ₚ k) P ℚ.≤ c`), define `mass-bindʳ` at
   `λ _ → 1ℚ`. It replaces `StateEvent/Lift :: bind-≤` (8 lines, its comment already says it is `mass-bindʳ` at the
   event) and the identical five-step `bound` chains in `Lift :: flagSkeleton` and `UC/Machine/Dominated ::
   eventSkeleton` (8 lines each), and their duplicated `0≤r`. About −18.

6. `src/ProbabilisticLogic/Dp/Settle.agda` — add `Settles-map⋆ : Σ i (Settles i d ν) → Σ j (Settles j (d >>=ₚ
   returnₚ ∘ h) (ν >>=⊥ return⊥ ∘ h))`. It is spelled out at `Trace/Compose :: dispF`, `dispG` (the same lemma twice),
   `StateEvent/Adequacy :: ker▷` and `flagRun`'s `pt▷`. About −10.

7. `Lift :: covered` is `UC/Seam/EventTransfer :: cov-ind` line for line; `Lift :: ≈⇒cofinal` is a missing
   `≈ₚ⇒cofinal : (P) → NNF P → d ≈ₚ e → Cofinal P P d e` for `ProbabilisticLogic/Dp.agda`. Hoist both (−5).

8. `Lift :: flag-slide`'s `bottom`/`w` duplicate `Monitor/Slide :: compiled-slide`'s `bottom` (now inlined into its
   `core`) and `w`, and the λ⇐-free core appears a third time at `compiled-slide`'s last step. One exported
   `T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇒ᴵ 𝒫.∘ subᴵ m) ≈ subᴵ (ρᴵ⇒ 𝒫.∘ m)` in `UC/Machine/Slide.agda` serves all four (−8). `a⇐-sub`
   repeats `relay-slide`'s first five steps; generalising `relay-slide` to `μ : Proc A (B ⊗ᴵ F)` would let `core` be
   `relay-slide w 𝒫.id` plus a `T₁ᴵ`-identity step (−15), but `relay-slide` is the 17 s proof, so measure first.
   Subsumed by Suggestion 1 stage 2 if that is taken.

9. `Protocol/Observe.agda :: hitFrom` and `StateEvent/Adequacy :: hitK` are the same three clauses over a kernel
   (`kernel P` vs `K`). Generalising one over a state `Set` makes `hitFrom P Bad` an instance (check that the pattern
   lambda `λ (s′ , r)` vs `proj₁ mr` is still definitional), and `hitK-idle` a state-map lemma. About −5; the
   coin case of `flag-hit`/`hitK-idle`/`GamePlaying.Partial.runWith⊥-bisim` is the same proof three times.

### Dead public definitions (rule 32: your call; `grep -rnF` over `src` finds only the definition)

10. `Read :: stateRead-resp-env` (9 LOC) · `Adequacy :: stateᶠ⇒boundedHit` (its converse is used once) ·
    `EventBounds/Transport :: transport-near`, `transportᵉ`, `eventSim⇒near`, `flagged-transport`, `hitsTransport`,
    `hitsTransportᴺ` (the WP4 package API; keep, but nothing exercises it — add a test that pins one, rule 33) ·
    `Transfer :: ledger-pov-family-negligible`, `ledger-conserves-value-from-hash`, the `Mute`/`Liar` corollaries
    (example statements; keep). `EventBounds :: ctxRun-∘` is the B-uc ledger's open item and is used by Suggestion 1.

### Small

11. `Read :: stateᶠ⇒stateᴺ` and `EventLift :: hitsᶠ⇒hitsᴺ` are both `boundedᶠ⇒boundedᴺ _ _` under a new name, each
    used once (in `ChimericLedger/Property`). Inline them (−6; Property and EventLift are R2a's).
12. `Examples/ChimericLedger/Property.agda` (R2a's, read-only here): `preservesValue⇒saturated`'s result type is
    `Saturated (λ n q r → (d : …) → asks≤ q d → Pr (R n) (auditWatch n d) ℚ.≤ r) εᴹ` under Suggestion 2; its comment
    block on `PreservesValue` duplicates `Transfer`'s header (rule 24).

### enum-where dispositions (every listed site, plus Lift by hand)

- Transfer: `G` ×3 (incl. the two the enumerator missed in `mute-never-accepts`/`liar-quiet`), `atAcc`, `hits`,
  `reports` — inlined. `quiet` — kept: two clauses on the query, needed for `reportsLoss` to reduce.
- Category: `split` — inlined; `solved` — kept (macro reads the goal, see Tried).
- G: `reconcile`, `step-eq`, `enter₁`, `loop-relabel`, `branch₁`, `branch₂`, `p-ok`/`s-ok` (both laws), `reduce`
  (trace-∘ˡ) — inlined. `exit-relabel` — kept: the section comment names it as the law's content. `enter₂` — two
  uses. `reduce` (trace-∘ʳ) — kept, perf (Tried). `S′`, `S″`, `m`, `n`, `k′`, `M`, `V`, `k` — several uses.
- Trace.Compose: `value` (trace-settles) — inlined. `point` ×2 — kept: one clause on `inj₂` with the `⊥` case
  elided, so the inline form is a `λ where` with the same clause. `raw` — two uses. `value`
  (compose-StepSettles) — kept: carries its own `where point`.
- Monitor.Slide: `bottom` — inlined; `core` — kept (Tried); `μ`, `w` — many uses.
- StateEvent: `unflag-▷.pt`, `unused.pt`/`st` — inlined. `▷-≲.pt` — kept, perf. `stepU`, `back`, `st` (both) —
  multi-clause pattern matches; `go` — two uses.
- Adequacy: `cont`, `κ` — two uses each (the enumerator's `singleUseCandidate` counted one).
- Agree: `read-point` — inlined. `pt` (embeds) — two clauses.
- Lift (not parseable by the toolkit): `played`, `0≤r` (flagSkeleton), `qE′` (stateLift) — inlined. `answered`
  (shaped-run) — clauses incl. an absurd one. `a⇐-sub`, `core` (flag-slide) — single-use typed lemmas, left for
  Suggestion 8, which replaces them. `bottom`, `w`, `u`, `bound` — several uses or used by `case`.
- enum-with: zero sites in every file (Lift checked by hand: no `with`).

### enum-comments dispositions (every block)

Cut or corrected blocks are the ones in `3ff1e3e1`; every other block was kept for the reason given.
- Transfer (17 blocks): header — the three-claim map; Claim-1/2/3, "what claims 1 and 2 do not say", "replay attack"
  banners — landmarks over several definitions (the single-definition "…off a premise about the hash alone" banner was
  cut, so Claim 1 now groups its eight definitions); `p n + 1` (why the cap plus one), hash invisibility, rate-`1`
  twice, no simulator, `TruthfulAudit`, `Mute`, `Liar`, the replay block — each a why. Cut: "operational
  corollaries" (type echo), "Monetary conservation" (duplicates the header).
- Category (2): header kept to the one-step-simulation orientation; the solver gotcha moved to `onR-α`/`onL-α`.
- G (7): header trimmed to its `β` fact; naturality (the 397 s split), superposing (`exit-relabel` is the content),
  `Mealy-Gᴹ` (8 GB, one application) — whys; banners group several definitions.
- Trace.Compose (14): header rewritten (dangling refs fixed, narration cut); `⊗S`, one pass, rank (corrected),
  routings pinned (gotcha), `ranked-from-kᴳ`, the three steps, the closed composite, `ansᴹ` inverse, read at the
  trace — kept; "`E⊥-map` at the two routings" — cut (echo).
- EventBounds (8): header (citation corrected); `Reader` (citation removed); `ctxRun-∘` (absorb cite); `BoundedAt`
  (the cap is essential; misattributed completed-run sentence cut); slack-order echo — cut; `boundedᶠ⇒boundedᴺ` — why.
- Transport (11): all kept; `cap` and "depth" wording corrected.
- Monitor.Slide (6): header (why the module exists: 17 s), `relay-slide`, `watch-resp-≈`, `openedᴹ` — kept.
- StateEvent (15): header, zigzag, `dropF`, `unflag-▷`, `padᴹ`, `unused`, ghost — kept; "A presented machine…" —
  cut (echo); "renaming" — corrected.
- Adequacy (12): `hitK` (mirrors `hitFrom`), flag-read depth, `idleTest`, `Boundedᴺ` order, the "…lifted" pair —
  kept; "The adequacy theorem…" and "slack carried across" — cut; "The old theorem" — reworded.
- Agree (10): header (why the agreement is at the observation), `flag-tower`, `kᶜ`, `emit`, `flag-read`, `play-run`
  cite — kept; "The whole observation." — cut.
- HitTests (12): kept (test-case statements); `Reads` — corrected (`T`, not `Bad`).
- Read (8): header, `flagStrat`, banners — kept; `asks≤-flag` — corrected; the two `resp` glosses — cut.
- Carry (2): header label corrected; the >10 min note — gotcha, kept.
- Grounded (9): kept, except the false definitional claim (cut).
- Lift (by hand, 17): all kept — header (the shaped-strategy argument), the `case` vs `where` OOM gotcha, `pendF`
  potentials, `bind-≤` citation, `Final`/`FlagShaped`/`unflagStrat` glosses (non-obvious semantics of the shapes),
  the admitted-context note; banners group several definitions.


## Tried, not worth it

- `src/CategoricalCrypto/UC/Machine/StateEvent.agda :: ▷-≲` — inlining the single-use `pt` into `simFn`: green, but
  the module's warm check goes from 18 s to 184 s. Kept named, with a comment.
- `src/CategoricalCrypto/Machines/G.agda :: trace-∘ʳ` — inlining the single-use `reduce`: green, 15 s → 160 s. The
  mirror-image `trace-∘ˡ`'s `reduce` inlines at no cost (committed). Kept named, with a comment.
- `src/CategoricalCrypto/Examples/ChimericLedger/Transfer.agda :: mute-silent`, `mute-never-accepts`, `liar-quiet` —
  replacing the continuation `G` by `_`: red (the continuation is not determined through `trans`); inlined as a
  lambda instead (committed).
- `src/CategoricalCrypto/UC/Machine/Monitor/Slide.agda :: compiled-slide` — inlining `core` (a 17-step chain): green
  and perf-neutral, but it nests the chain at a 24-column indent and pushes six lines past the file's 99-column width;
  rewrapped it is longer than the named version. Kept.
- `src/CategoricalCrypto/UC/Machine/StateEvent/Lift.agda :: flag-slide` — dropping `bottom`'s `{X} {Y ⊗ᴵ X}`: red
  (unsolved interface metas). Kept.
- `src/CategoricalCrypto/Machines/Category.agda :: onL-α` — inlining `solved`: not attempted; its `solveMor!` macro
  reads the goal, which as the left operand of `○` has an unsolved right-hand side.


## Integration-owned files

None of this part's files is integration-owned. Suggestion 1 touches `UC/Quantitative/EventLift*` and
`UC/Machine/Monitor.agda` (R2a's), Suggestions 5–7 `ProbabilisticLogic/Dp*` and `UC/Seam/EventTransfer`.

## Out-of-scope edits

None.

## Notes for the orchestrator

- `Examples/ChimericLedger/Property.agda` is on both this part's and R2a's list; it was left untouched here.
- `docs/state-event-contract.md` rows 14 and 25 are stale (the one-interface `Reader` type; row 25 calls
  `ledger-uc-to-pov-family` claim 2, where the code's claim 2 is `ledger-uc-to-state`). `docs/event-bounds-in-setup.md`
  still quotes an old `UC.Audit` header. Not in this scope.
