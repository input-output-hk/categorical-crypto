# Quality review — protocol-rewrite (2026-09-11)

Scope: round 2 — the 109 live `.agda` files changed in `140a5fef..6256a140` under
`src/`, excluding `ProbabilisticLogic/Distribution/Binomial/` (a parallel agent owns
it), plus `Machine/Core.agda` and `Examples/Basic.agda`, named in the brief. Base
merged forward to `protocol-rewrite`'s tip (`1548985f`) before the apply phase.
Round 1's ledger (the previous contents of this file) is carried forward below:
every entry reappears with its *latest* verdict, and the ones this round closed have
moved to *Tried*.

Eight files were excluded from editing mid-review because two statement-redesign
agents took them: `UC/Audit`, `UC/Seam/Audit`, `UC/Seam/Audit/Bounded`,
`UC/Seam/Budget`, `UC/Saturated`, `UC/Family`, `UC/Family/Monoidal`,
`UC/Approximate`. Findings on them are recorded here and were not applied.

Verification: yes. Every commit checked green *before* landing, under each file's own
OPTIONS, with `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`; green means
rc=0 **and** an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`.
One methodological note for future runs, because it nearly produced a false green:
with the gate shared, a module often gets elaborated as somebody else's dependency
between your edit and your check, so its own check then reports **zero** `Checking`
lines. That is a real green (the interface on disk was built from your edit), but it
is indistinguishable at a glance from "nothing was checked". Appending a comment line
does **not** force re-elaboration here, contrary to the toolchain note — deleting the
module's `.agdai` under `_build/2.8.0/agda/` does. The five `Categories/GConstruction*`
edits in `edec4420` were re-verified that way, cold, after their first check came back
`chk=0`; and a deliberate `NotInScope` sentinel confirmed the oracle reads the working
tree rather than the index.

Closure check, after the last commit: `CategoricalCrypto`, `UC`, all four Pins
(`Protocol.Machine.Pin`, `UC.Model.Pin`, `ChimericLedger.Pin`, `MerkleDamgard.Pin`),
`ChimericLedger.{Carry,Birthday}`, `UC.Model` and the zero-importer leaf
`ProbabilisticLogic.Dp.Zero` — **all green**, rc=0 with an empty warning gate.

Soundness baseline: whole-`src` hatch grep **19 lines before**, **16 after**, measured
with `git grep` at my base `1548985f` and at HEAD. By category: 16 `postulate` +
4 `{!` before (three lines, one of which held two holes), 16 `postulate` + **0** `{!`
after — the `{!` category is now empty tree-wide and nothing else moved. (The brief's
figure of 21 predates the `pmf-postulates` merge, which proved two away before I
started.) Zero hatches anywhere in the 109-file scope, before and after; every one of
the 16 survivors is in inherited `Categories/APROP/**` (twelve files) or
`Categories/Coherence/Symmetric/Test.agda`.

Warm-cost census: all 109 in-scope modules measured individually, warm, forced by a
probe comment (`.claude/sweeps-tally/census-round2.tsv`). **109/109 green,
109/109 inside house rule 5's `60 s + LOC/4` budget, and 109/109 under the brief's
150 s bar.** Total 1418 s; the three above 60 s are `GConstructionMonoidal` 96 s
(budget 129 s, and 5 of its dependencies rebuilt in that run),
`GConstructionLoopCoherence` 68 s (budget 91 s) and `GConstructionTensorCoherence`
61 s (budget 123 s). **No perf regression was found, so none was reverted.**

Sweep tally — `.claude/sweeps-tally/round2-*.json`:

| class | candidates | disposition |
|---|---|---|
| `enum-comments` | 942 blocks, 100 flagged | 34 `singleDefBanner` dispositioned individually (30 keep — each heads a `mutual`/`private` block of 3-23 definitions, so rule 25's "more than one definition" is met, which is why the flag is a false positive at those sites; 4 cut: the two `Dₚ shorthands` banners that went with their blocks, `UC/Core.agda`'s title-less divider over one record, and `ChimericLedger/Birthday.agda`'s per-lemma banner over `no-replay`, demoted to the comment it carries), 45 `leftoverMarker` read (mostly false positives on the words "new"/"now" used substantively; the genuine ones are in *Committed*), 15 `headerOverTier` content-tested against rule 23's narration clause, 9 `insideDefinition` kept as per-clause glosses that carry a why |
| `enum-with` | 118 sites | 34 are `with … in eq` (no `case_of_` counterpart), 10 multi-scrutinee, 74 single-scrutinee. **Not dispositioned per site — see *Suggestions*.** A transform+oracle script was written for the class (`.claude/sweeps/with_case.py`, EXPERIMENTAL, README rule 2) and dry-validated on five sites, but not run under the oracle |
| `enum-where` | 358 sites, 252 flagged `singleUseCandidate` | **Not dispositioned per site — see *Suggestions*** |
| `using-drop` | 786 `using` lines (590 in the 63 files new this round) | **Started and stopped at 1 of 109 files — see *Suggestions*** |
| `join-lines`, `implicit-drop`, `binder-drop` | — | **Not run — see *Suggestions*** |

The three automatic classes are the honest gap in this round and are filed as a work
item below with their measured per-file cost, not as a *Tried* entry.

New in the toolkit: `.claude/sweeps/with_case.py`, the transform half of the
`enum-with` class, written under the README's rule 2 and marked `EXPERIMENTAL:`. It is
dry-validated but has never been run under its own oracle — see *Simplifications*.
(`.claude/sweeps/` is untracked in this repo, so the script lives in the main checkout
alongside `sweep.py` and `where_inline.py`; only the tallies are committed.)

Coverage, stated plainly. All 109 in-scope files were read in full and
dimension-attested, by ten parallel readers plus this one. The one gap is the three
automatic sweep classes, filed as a work item below with the measured cost that
justifies stopping — not disclosed and dropped. A companion-docs reader was launched
and died at a session limit; the maintainer's own review commit `97063c50` landed
mid-review and covers most of what it would have said, and what remains owed is named
under *Companion docs*. `Machines/Frame.agda` carries six open round-1 entries of its
own, all still standing and not re-litigated here.

## Committed (you can skim these)

- `a2cdc2ca` **Take the `Dₚ` reasoning shorthands from the shared module** —
  `UC.QueryBound.Compose` and `.Compose.Step` each carried a private copy of
  `ProbabilisticLogic.Dp.Reasoning` (nine and six names, character-identical up to
  binder spelling and the level generalization). `map-bind` was the one gap and moves
  into `Dp.Reasoning` beside `bind-map` (rule 27; grepped clash-free against all
  thirteen consumers). The banner both copies carried cited `UC.Machine.Run`, which
  reads the shorthands from the shared module itself. −74 lines.
- `7f1d74e5` **Drop the two commented-out hole sketches** — `Machine.Core`'s
  `cup`/`cap` and `Examples.Basic`'s `F≤Secure`: commented-out declarations with
  `{!!}` bodies, for names that exist nowhere else in `src/`. Takes the hatch grep
  from 19 lines to 16.
- `38495a94` **Point the comments at what is actually there** — one commit, comment
  text only, over 22 files. The ones worth naming, each verified by grep before the
  edit: `UC.Machine`'s re-export note said `UC.QueryBound`'s certificates name
  `⊎assocˡ`/`⊎assocʳ` (that module contains neither; the three real consumers are
  `Grading`, `Dictionary`, `Slide`); `UC.QueryBound`'s "The closure property still
  owed" banner survived `qb-∘` being proved in `Compose.Laws`, and its pointer named
  `UC.Machine.Grading` (`Budgetᴹ`) for an assembly that is `UC.Machine.Budget`
  (`budgetᴹ`) — `Budgetᴹ` has no referent in `src/`; `Compose.Step`'s header narrated
  a superseded design through a name (`Bd≈`) that occurs nowhere else;
  `Machine.Probabilistic.Model` said three times that the trace "lives on the
  g-construction branch" when the twelve `GConstruction*` modules are in-tree and
  `Machines.Base.Tracedₚ` is built; `UC.Seam` cited `UC.Bridge.Reflects`, a module
  this round deleted; `UC.Machine.Dictionary`'s two section banners headed each
  other's blocks; `Protocol.Machine`'s `Morphism-∘` said "Stated, not proved" after
  `Protocol.Machine.Total.morphismCompose` inhabited it; `Protocol.Machine.Total`'s
  header stated the side condition as `≡ 1ℚ` where the code takes `1ℚ ≤ _+_`;
  `UC.Machine`'s `docs/kb/frontier/15-probabilistic-uc-model.typ` citation resolves
  to nothing (no `docs/kb/` exists). The rest are rule-22 leftovers ("no longer",
  "used to sit here", "Superseded:", "the form this module carried before", "before
  the move to the seal"), two rule-24 duplicates reduced to pointers, one type-echo
  comment, one title-less divider and one per-lemma banner demoted to a comment.
  **Every `Measured warm cost:` figure was kept** — including `Adequacy.Wiring`'s
  "9.9 s, down from 87 s … and 282 s", which prices two named alternatives and is
  load-bearing under house rule 5.
- `1d9cfeec` **Delete what nothing reaches** — `MerkleDamgard.Core`'s `mdArrow`,
  `respRM`, `mdStep`, `mdStepᵇ` and `bad` (each reachable only from another of them;
  `MDState` stays, `QueryBound` uses it ten times), which also takes
  `CategoricalCrypto.SFunM` and `.SFunPartial` out of that module's import closure —
  `SFunᵉ` was their only name in the file and `mdArrow`/`respRM` its only uses. Plus
  `_++ᵛ_` and `bool→ℚ` from two `using`/`renaming` lists, `Level`'s `0ℓ` from
  `UC.Machine.Bridge`, `Protocol.Machine`'s `⟦_⟧ᴵ` and `Sum`'s `inj₁`/`inj₂` from
  `UC.Machine.Wire`, `proj₁`/`proj₂` from `UC.Machine.Slide`, `_[_≈_]` from
  `UC.Machine` and `UC.Machine.Grading`, `ℕ` from `Protocol.Machine.Total`, and the
  unused `as ℚP` alias from `Dp`, `Dp.Advantage` and `Dp.Dominate` — every one grepped
  to a single occurrence, the import line itself. The surviving copy of `mdStep`'s
  relay logic is `MerkleDamgard.QueryBound`'s `enter`/`advance`, which is the same
  clauses with `botₚ` where `mdStep` returned garbage.
- `edec4420` **Small style debts** — rule 19: three `Categories.Category.Monoidal.Bundle`
  imports that `Categories.Category.Monoidal` already re-exports `public`; rule 11:
  `refl⟩⊗⟨_` in a `open … public using` list with no use (the sweep skips `public`
  sites, so the toolkit cannot see it); rule 18/26: `GConstructionLoopCoherence`'s
  `X6 = Fin 6`, used at two of its three sites where the third and every sibling module
  writes `Fin n` inline; rule 17: `run⊥-embed`'s trailing argument, whose sibling
  `run⊥-embed-gen` was eta-reduced this round and it was not; rule 13: three `∎` on
  their own line, in two files that elsewhere use the on-line form.

- `d3a9d33b` **Take the two Maybe absurdities and the length-of-toList from the
  library** — rule 30, three swaps in `MerkleDamgard.Core`. `len-toList` and
  `toList-len` were the *same lemma declared twice in one file*, 480 lines apart, and
  both are `Data.Vec.Properties.length-toList`, which the sibling
  `MerkleDamgard.QueryBound` already imports. `nothing≢just` and `just≢nothing` are
  already in this repo, public, in `Data/Maybe/Ext` — Core spelled them `→ ⊥` where
  `Ext` spells `_≢_`, the same type by definition, so the ten call sites are
  unchanged. `MerkleDamgard.Core`'s warm cost is unchanged at 35 s.

- `a237de1c` **Four one-liners: three from the library, one from the goal** — rule 30:
  `Uniform.Birthday.square` is `Data.Nat.Properties.*-suc` then `+-comm` (since
  `1 ℕ.+ q` IS `suc q`), and `UC.Machine.Slide`'s `where`-local `_⟨trans⟩_` is
  `PropositionalEquality.trans`, `Set`-monomorphic, with no clash among that file's 30
  opens. Rules 12/14/17/18: `Dp.Zero.≈bot⇒zero`'s single-branch `with` becomes a `let`
  (the shape round 1 landed for `≤UC⁺⇒≤UC`), and `RationalDist.Advantage.adv⊥-≈⇒0`
  binds its argument on the left instead of opening with `λ e →`.

- `49a70ec5` **Six dead opens and imports in the machine layer** — none reachable by
  the mechanized sweep (four are bare `open`s with no list, two are whole-module
  imports). `open Equiv` in `Machines.{Category,Frame,Tensor,Sim.Lax}`, where the
  `_○_`/`⟺`/`refl⟩∘⟨_` in use come from `HomReasoning` via `Monoidal.Reasoning`'s
  `public` re-export and `Equiv` is not re-exported (`Category/Core.agda` has that line
  commented out) — `Tensor/Assoc` and `Trace/Naturality` DO use a bare `refl`, so
  theirs stay; `Monoidal.Properties monoidal` in `Tensor/Assoc`, none of whose twelve
  exported names occurs in the file; and `Level` in `G/Lax`, which uses no `Level`,
  `0ℓ`, `suc` or `⊔`.

## Suggestions (need your call)

### Statement audit

- `src/CategoricalCrypto/UC/QueryBound.agda :: QB` — **the counting theorem is about
  the representative, not about the machine.** The certificate layer is sound and not
  degenerate: `Below Φ r` forces strict descent, `pointᵍ`/`coh₀` pin the reachable
  initial potential to 0, and `Unfolding` is discharged at the real composite in
  `Compose.Step.unfoldᶜ`. But `QB c M = Σ[ N ] Certified c N × (N ≈ᴹ M)`, and
  `counting` gives a `CountBound` for **N**. The cited justification
  `UC.Machine.Run.runᴹ-resp-≈ᴹ` covers only `Closed B` machines under `runᴹ`
  (`Run.agda:44-45,109-140`), whereas `behᵍ`/`traceᵍ` is an open, word-indexed trace;
  `behᵍ`'s six occurrences are all inside this cluster and none is a transfer lemma.
  So nothing in `src/` carries the counting bound from `N` to `M`, and "a query bound
  with content" holds one step short of the `QB` that `Budget` consumes. The missing
  piece is ~15 LOC in `Run.agda`'s own shape: `traceᵍ`-simulation by induction on the
  word off `Run.step-sim`, then `EqC.fold`.
- `src/CategoricalCrypto/Examples/ChimericLedger/Birthday.agda :: target` — **audited
  in full, and it is NOT weaker than advertised.** It claims exactly: for `ℓ`, `ser`,
  `h₀`, `ser-inj`, and every `a₀`, `V`, `POV inputConsuming (genesis h₀ a₀ V) εbirthday`
  — for every `q` and every `d` with `asks≤ q d`,
  `PrHit (Sys inputConsuming (genesis h₀ a₀ V)) (badTotal …) d ≤ℚ fromℕ (q*q+q) * inv-pow-2 ℓ`.
  That is the trajectory observable (state read at every activation boundary), and
  `asks≤` leaves `coin` nodes free, so randomized adaptive strategies are covered;
  `docs/protocol-rewrite.md:37-39,1394` matches. The cheap-certificate failure mode was
  checked and is negative on every count: `Inv` is `flag ≡ true ⊎ Good` with five real
  fields, not `λ _ → ⊤`; `φ` is `bool→ℚ (flag tbl) + Γ (suc ∣tbl∣) m`, and `φ-init`
  discharges through `Uniform.Birthday.birthday`, which a constant-1 potential could
  not do (`1ℚ ≤ εbirthday m` is false whenever `m² + m < 2^ℓ`); the pool index is
  `length (Hs tbl)` on the nose, so `Γ` is charged at the true pool size; and
  `Good.hashed`/`Stale` are both load-bearing. Recorded so the next reviewer does not
  redo it.
- `src/CategoricalCrypto/Examples/ChimericLedger/Birthday.agda :: (header, 24-28)` —
  **the one overclaim found in that module**, and it is in the prose, not the theorem:
  "with `chimeric` in its place the invariant — and the bound — are false
  (`ChimericLedger.Replay` computes the attack)". The *invariant* half is right
  (`Stale` needs a first input, which `consumes chimeric` does not demand). The *bound*
  half is not supported at the state this module pins: `Replay`'s counterexample runs
  at an account-funded `s₀`, whereas at `genesis h₀ a V` the account table is empty and
  nothing ever credits it (`applyTx` only `subOne`s accounts and only creates UTxO
  entries), so every accepted withdrawal has `v ≡ 0`, a replayed no-input transaction
  destroys nothing, and the only remaining loss needs a genuine collision under either
  variant. So `POV chimeric (genesis h₀ a V) εbirthday` is not refuted by `Replay` and
  may well hold. This is an argument, not a machine-checked refutation, which is why it
  is here and not in a commit. Suggested repair: "…the invariant is false, and at a
  general `s₀` so is the bound".
- `src/CategoricalCrypto/Examples/ChimericLedger/Carry.agda :: Emulᴸ` — **the premise is
  refutable at the pair the module is named after.** `Emulᴸ v₁ v₂ s₀` unfolds to
  `Agreeˢ`, i.e. *exact* agreement at every positive slack, not an emulation at some
  advantage. For the two variants the example exists to compare it is false: at
  `Replay.s₀`, `watch s₀ (audited Replay.replay)` returns `true` with probability 1
  against `chimeric` and `false` with probability 1 against `inputConsuming`, and
  `Pin.chimeric-violates`/`consuming-safe` pin the underlying trajectory event. So the
  comment "What an emulation of one variant by the other has to show at the machine
  layer" oversells: the conclusion is reachable only at states where the two variants
  coincide. Note also that `δ` is wholly slack — from exact agreement one expects `ε`,
  not `ε + δ` — inherited from `Agreeˢ`'s formulation rather than needed by the ledger.
  Say what the module is (a plumbing demo: the seam's `agreeToAdv` at two concrete
  systems) and that the premise is not available for the interesting pair.
- `src/CategoricalCrypto/UC/Seam/Grounding.agda :: UnitGrade` — **the round's headline
  is proved but not reachable, and it carries a free hypothesis.** `subBlind⇒unitGrade`
  is sound and does prove what `UnitGrade` states; `SubBlind` is not assumed anywhere
  (`Grounded.subBlind` proves it outright via `Prefixedᵒ` + `astotal-bind`), `SimTotal`
  is satisfiable and non-trivial (`simTotal⇒point` shows it really pins the simulator's
  initialization mass), and `Grounding.Dead`'s mass-0 witness shows it cannot be
  dropped — so no circularity and no vacuity. Two things to weigh: (i) `TotalRun B v`
  is bound as `_` at `Grounded.agda:136` and used nowhere; the header gives the reason
  ("the consumer's pair is symmetric") but there is no consumer to force the symmetric
  shape; (ii) `unitGrade` and `UnitGrade` grep to five occurrences each, all inside
  `Grounding.agda`/`Grounded.agda`, and **`UC.Seam.Grounded` has no importer at all** —
  `UC/Seam/Audit/Bounded.agda:48` imports four wiring names from it and none of the
  four discharges, and `UC.agda`'s inventory lists `UC.Seam`, `.Carry`, `.Grounding`
  and `.Audit` but not `.Grounded`. Nothing in `src/` composes `unitGrade` with
  `povCarry`, and `ChimericLedger/Carry.agda` takes `Agreeˢ` as a raw hypothesis rather
  than getting it from a `_≤UC_`. One ~5-line corollary in `Carry` or `Grounded` plus a
  `UC.agda` map row closes the seam.
- `src/CategoricalCrypto/Machines/Sim/Lax.agda :: _≲ˡ[_]_` and `_≈ˡ[_]_` — **audited
  and clean; the scalar index is genuinely constrained.** `_≲ˡ[_]_` is `_≲_` minus
  `θ-discard`, with `θˡ-point : θˡ ∘ point (state f) ≈ point (state g) ∘ σ`, which pins
  `σ` up to `≈` once `θˡ` is fixed — it cannot be chosen freely — and `θˡ-step` is
  *identical* to `_≲_`'s, so nothing is related that a strict simulation would not
  relate up to its point. Since the relation is strictly weaker than `_≲_`, its
  downstream consumer (`UC/Seam/Grounding/Prefix.agda :: prefixedᵒ-obs`) is a stronger
  theorem, not a free one. `_≈ˡ[_]_` is `f ≈ᴹ · ≲ˡ[ σ ] · ≈ᴹ g` — deliberately **not**
  the equivalence closure (no `≈ˡ-trans`, no symmetry), so the σ measured is exactly
  one core's; and the index carries observable content, because `∘ᴹ-resp-≈ˡ` produces
  `σ ∘ τ` where `≲ˡ-trans` produces `τ ∘ σ`, and at the intended base
  (`unit ⇒ unit` = `⊤ → Dₚ ⊤`, so `σ ∘ τ = τ >>=ₚ σ`) that order is observable.
  Recorded so the next reviewer does not redo it. One loose end in the same module:
  `≲ˡ-trans` has **zero uses** (2 greps, its own signature and definition), and it is
  the only thing that exercises the header's second design rationale — delete it, or
  say in the header that prefixes are only ever composed spatially.
- `src/CategoricalCrypto/Machines/Collapse.agda :: compose≈∘ᴳ` — **this "theorem" is
  `S.reflᴹ`**: it asserts that `composeᴳ g f` and `𝒢._∘_ g f` are *convertible*, not
  that they are provably equal. That is deliberate — it is the elaboration pin the
  `opaque composeᴳ` boundary exists for — but the header never says so, and a reader
  meeting `compose≈∘ᴳ : … S.≈ᴹ …` will read it as content. One line settles it.

- `src/CategoricalCrypto/Examples/MerkleDamgard.agda :: indistinguishable` — **what is
  proved is single-oracle indistinguishability with the compression function hidden,
  not indifferentiability.** The distinguisher's type is
  `Strat (Neg Generalᴵ) (Pos Generalᴵ)`: it has no compression-oracle interface
  (`Sys = md ∘ᵖ comp : Protocol unitᴵ Generalᴵ` closes `comp` off), and there is no
  simulator anywhere in either module — which is exactly why `ideal-marginal` can be an
  *exact* equality. That is a genuinely weaker claim than "MD is a random oracle". The
  module headers are honest about it (`Core.agda:171-172` says "compression hidden … No
  simulator"), but the title "MERKLE–DAMGÅRD as a protocol, and its concrete-security
  theorem" plus the `(Theorem 3.1)` citation at `Core.agda:125` invite the stronger
  reading. Nobody in this review read the cited paper, so this is "check the citation
  against the formalized statement", not "the citation is wrong" — but the statement
  should say "with `f` hidden" wherever the theorem is named. No trivializing hypothesis
  was found otherwise: `asks≤` is a real per-branch ask-depth bound, `_≈adv[_]_`
  quantifies over all `b`, `q`, `d`, and at `q = 0` it demands advantage `≤ 0`, which is
  tight. Two structural facts worth recording: the potential is an *exact* martingale,
  so `φ-init`'s slack to `bound q` is the only looseness; and `φ-step`/`φ-nn` are proved
  **without** using `Inv` (`md-cert` discards the hypothesis), so the ~700-LOC invariant
  development exists to discharge `φ-bad` alone.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Pin.agda :: bound` — `bound 2 ≡ 3/1` is
  pinned, i.e. the bound exceeds 1 and `indistinguishable` is **vacuous** at
  `n = 1, k = 2`, while the adjacent comment reads "The gap the chaining costs, and the
  bound that pays for it". Say the bound is vacuous at these parameters and the pin
  exercises the arithmetic only, or move `bound-2` beside `bound-1`, which is tight and
  says so.
- `src/CategoricalCrypto/UC/Emulation.agda :: blind-grade` (with `unit-grade`, and
  `src/CategoricalCrypto/UC/Model/Bridge.agda :: blind-gradeᵁ`, `unit-gradeᵁ`) —
  **four dead definitions, and the reason they are dead is a statement defect.**
  `blind-gradeᵁ` asks `(s : X ⇒ X) → sub s ∘ g ≈ᵁ g` for **every** `s`. The intended
  consumer, `UC/Seam/Grounded.agda:135-143 subBlind⇒unitGrade`, can only produce that
  for the `s` the emulation yields and only under `SimTotal B s v`, so it open-codes
  `blind-gradeᵁ`'s body instead of calling it. Proposal: restate as
  `f ≤UC g → ((s : X ⇒ X) → Blind s → sub s ∘ g ≈ᵁ g) → …`, taking the emulation
  first so blindness is demanded only at `proj₁ (p id)`, then route
  `subBlind⇒unitGrade` through it — or delete all four and the four comments
  (`UC.agda:17`, `UC/Audit.agda:7`, `UC/Seam.agda:33`, `UC/Seam/Grounding.agda:161`)
  that promise them. Note `unit-gradeᵁ`/`unit-grade` are `reflect (blind-grade blind e)`:
  the second hypothesis is the implication whose conclusion is the theorem, so they
  carry no content past `blind-grade` — disclosed in both headers, so honest, but it
  means only one of the four is load-bearing.
- `src/CategoricalCrypto/UC/Machine/Bridge.agda :: ContextDominated` — **narrower
  than the name and the header claim.** The obligation is stated only at `A := unitᴵ`
  and at the trivially graded hole (`E : Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ`), with the
  plugged process `conjᴵ u = λᴵ⇐ 𝒫.∘ u` for a **closed** `u : Proc unitᴵ B` — never a
  general `f g : Proc A B` at a general hole, although `ctxRun` itself is stated
  generally. The header ("the obligation that lets the second be read as the first")
  claims the general reading. With `dominated` unconsumed (next item) nothing pins
  whether the closed, unit-hole case suffices. Either generalize, or say in the header
  that this is the instance layer 1 needs and why.
- `src/CategoricalCrypto/Protocol/Machine/Total.agda :: totalRun-morphism` — the
  `TotalRun` node is uninstantiated. `totalRun-morphism` and `totalRun-∘` have no
  consumer; `TotalRun` appears elsewhere only as a *transported* hypothesis
  (`UC/Seam/Grounding.agda:172`, and `Grounded.agda:132` says outright that
  `TotalRun v` "is not consumed here"). Nothing discharges
  `(d : Strat …) → 1ℚ ≤ Prᵇ P true d + Prᵇ P false d` for any concrete protocol. The
  content is genuine (the layer-1 → machine-image transfer through `prAgree`), but
  the hypothesis is as strong as the conclusion modulo the agreement theorem, so this
  is a *reading*, not a liveness proof, and the roadmap should price it as one owed
  inhabitant.
- `src/CategoricalCrypto/UC/QueryBound.agda :: BudgetLawsᴹ` — dead by supersession,
  and its `qb-∘` field got **looser** in this delta. `budgetᴹ` (the real `Budget`
  assembly) bypasses the record entirely; `budgetLawsᴹ` has zero consumers. Meanwhile
  `BudgetLawsᴹ.qb-∘` changed from `QB (c * c′) (g 𝒫.∘ f)` to the raw
  `Col.MT.traceᴹ … (Col.W.α ∘ᴹ ((g ⊗ᵉ f) ∘ᴹ Col.W.γ))` spelling, so the record no
  longer states the `Budget.qb-∘` field it exists to feed — while `Laws.qb-∘-category`
  next door *does* prove the packed form. Either restate at `g 𝒫.∘ f` (now provable)
  or delete the pair; deleting also retires `qb-T₁ᴹ`/`qb-subᴹ` and the
  `Machines.Collapse` import from the module whose header says it is at its
  typechecking budget.
- `src/CategoricalCrypto/UC/Model/Unit.agda :: AnyEnvironment` — the header claims the
  metatheory is "BLIND to the closure object … the closures that `ℰᵒ` happens to
  quantify over never enter a statement". What the five re-typings establish is that
  the *metatheorems* are ℰ-generic; the closures plainly do enter a statement at
  `ℰ = ℰᵒ` (`_≋_`, hence `_≈ℰ_`, quantifies over them). Narrow to "the five
  metatheorems are ℰ-generic, so the choice of closure object never enters their
  proofs".
- `src/CategoricalCrypto/UC/Approximate.agda :: Approximation` — *(excluded file,
  reported only)* the same class as round 1's `Grading` entry, at a different record.
  No field forces `_≈[_]_` to separate anything: `_≈[_]_ = λ _ _ _ → ⊤` discharges all
  four laws and `⟦⟧-resp-≈₀`, after which `_∼ᵃ_` relates every pair and every
  `_≈ℰ_`/`_≤UC_` over it holds. Relatedly `ApproximateObservation.induces` is trivial
  at every existing instance (`Induced.approximate` sets `induces = λ h → h`), so the
  field the header calls "the field connecting the two" has never carried content.
- `src/CategoricalCrypto/Machine/Probabilistic/Model.agda :: MachineModel.hom-triv` —
  *(inherited; flagged, not a branch regression)* this module is `--safe` with **K
  enabled**, while `MachineAxioms` is `--safe --without-K` and deliberately keeps
  `HomTransportTrivial` out of its record with the note "Implied by `UIP Obj`". Under
  K, `Axiom.UniquenessOfIdentityProofs.WithK.uip` gives `p ≡ refl`, so `hom-triv` is
  provable here — the record demands of every instance something that is free in this
  file, and the header's justification ("Plausible precisely because `_≈ₚ_` is
  observational") is the wrong reason. Also: this is the **second** in-scope module
  without `--without-K`; round 1's ledger named only `Channel/Category.agda`.
- `src/CategoricalCrypto/Protocol/Safety.agda :: hit-bounded` — audited in full and
  **clean** (the supermartingale reading is sharp; the cheap certificate `Inv = λ _ → ⊤`,
  `φ = λ _ _ → 1ℚ` discharges all eight fields but forces the vacuous `1ℚ ≤ ε m`).
  One reading a user can get wrong, inherited from the observable rather than from
  `HitCert`: `hitFrom` samples the state only at activation boundaries, so a `Bad`
  state entered *and left inside one* `step`'s call tree is invisible to
  `BoundedHit`. That is documented at `Observe.agda:9-10,174-175` but not in
  `Safety.agda`, which is the module a concrete system reads. One line, or a
  `see Protocol.Observe`.
- `src/CategoricalCrypto/UC/Model/Seal.agda:56-58` — the number or the record name is
  wrong: "the conversion checker meets two `Grading` records and eta-expands both,
  forming the thirteen law types". `Grading` has 18 fields, 8 of them laws; thirteen
  is `Budget`'s field count, and the sentence is about transporting a `Budget`. Either
  "two `Budget` records" (then thirteen is right) or "eighteen field types".
- `src/CategoricalCrypto/UC/Model/Pin.agda :: relay-emulates`, `relay-compose` — both
  are reflexivity instances (`f ≤UC f`, and `h ∙ f ≤UC h ∙ f` from `UC-compose` on two
  `≤UC-refl`s). The header discloses that the module prices application sites, and the
  four `*-app` names say "pin", but these two read like theorems; the file's own
  `*-app`/`*-pin` convention would say what they are.

### Public API / module layout

- `src/CategoricalCrypto/UC/Machine/Dominated.agda :: dominated` — **the round's
  headline theorem is unreachable from the layer's entry point.** `ContextDominated`
  greps to seven hits, all inside `Bridge.agda`/`Dominated.agda` plus one header line
  in `UC.agda:67`; `UC.Machine.Dominated` has no importer at all. `UC.agda` re-exports
  `UC.Machine.Bridge` and `.Grading` `public` but not `.Dominated`, and its module map
  never mentions it — so from the designed entry point the obligation still reads as
  owed when it is discharged. One `open import … public` beside line 94 and one map
  line.
- `src/CategoricalCrypto/UC.agda` + `src/CategoricalCrypto/UC/Model.agda` — the layer
  has **two roots and neither is imported**, and `UC.agda`'s three-tier inventory
  (lines 12-77) never mentions the `UC.Model.*` cone — this round's main deliverable —
  except one parenthetical. `UC.Model` re-exports nothing (nine bare imports: a
  build-closure target, so rule 19 does not bite). Add a `model` row for `UC.Model`,
  and either fold its import list into `UC.agda` or say there that `UC.Model` is the
  second root and why (the `open StdUC` seal discipline).
- `src/CategoricalCrypto/UC/Family/Monoidal.agda :: ucSetup^ω` — *(excluded file,
  reported only)* **the whole asymptotic cone is uninstantiated and is one lemma from
  not being.** `UC.Family.Monoidal` has zero importers; `UC.Family`'s only importer is
  `UC.Family.Monoidal`; `absorb`, `absorb-negl`, `CarriedNegligible`,
  `carried-negligible`, `≈^ω-witness`, `Approximate^ω`, `UCBase^ω`, `ucSetup^ω` each
  grep to their own signature and body only. Three of the four parameters are
  available concretely (`M := 𝔾ᵒ`, `obsᴹ := observationᵒ`, `bud := budgetᵒ`, `Ix := ℕ`,
  `κ := id`, cofinality trivial); the only gap is
  `qapx : ApproximateObservation observationᵒ ℚ-errors 0ℓ`, which the `Induced` route
  below produces for free. A four-line `Model` module instantiating it at the seal
  turns `Famᴹ`/`ucSetup^ω` from declared into witnessed.
- `src/CategoricalCrypto/Machines/Collapse.agda` — **~150 LOC of general-purpose
  `Kl(Dₚ)` point-level facts hosted in the module named for the G-composite collapse,
  and it is costing a downstream module the whole `GConstruction` closure.** Nothing in
  `⊗-pure`, `⊗-pureˡ`, `α+⇒-fn`, `α+⇐-fn`, `+-swap-fn`, `+₁-fn`, `pureᶠ`, `∘ᶠ`, `⊗ᶠ`,
  `idᶠ`, `α⇒ᶠ`, `α⇐ᶠ`, `σᶠ`, `swp-pt`, `onL-pt`, `onR-pt`, `tstepL`, `tstepR` mentions
  a G-composite. The proof it costs something: `Examples/MerkleDamgard/QueryBound.agda`
  imports `Machines.Collapse` and its **only** use of it is `Col.⊗-pureˡ`, eight times
  — so that file pays a 16 s module with `𝒢ₚ`/`Tracedₚ`/`GConstruction` in its closure
  for one three-line lemma. A `Machines.Pointwise` holding those lines leaves
  `Collapse.agda` as the ~140 lines its header describes. **Decide this together with
  the `UC/Machine/Dictionary` + `Wire` relocation above** — Dictionary's
  `midfn`/`midᴹ`/`pureᴵ` family wants the same home. Related, same file:
  `Collapse :: ⊗-pure` collides by name with
  `Categories/Category/Kleisli/Discrete/Pure.agda :: ⊗-pure`, a different statement in
  a module the machine layer routinely has in scope (`Machines/Base` and
  `UC/Seam/Grounding/Prefix` both open `KDP`); `⊗-pt`/`⊗-ptˡ` would match the
  `swp-pt`/`onL-pt`/`onR-pt` naming right next door. And `Collapse`'s private `mid`
  means "the intermediate machine" in the one file that also has upstream's
  middle-four `W.mid` in scope — `bodyᴹ` or `innerᴹ`.
- `src/CategoricalCrypto/Machines/Sim/Lax.agda :: _≲ˡ[_]_` — **the duplication the
  brief asked about is NOT between `Sim/Lax` and `G/Lax`; it is between `Sim/Lax` and
  the strict cone.** `G/Lax` (71 LOC) is a pure consumer: its two theorems are one-line
  applications of `Sim/Lax`'s congruences and share no proof text (the single overlap
  is one line, `∘ᴹ-resp-≈ˡ ≈ˡ-refl (∘ᴹ-resp-≈ˡ (⊗ᵉ-resp-≈ˡ u v) ≈ˡ-refl)`, verbatim in
  both, which one `private legs u v` collapses). The real duplication is with
  `Sim.agda` + `Category.agda` + `Tensor.agda` + `Trace/Congruence.agda`, and it is
  exactly the `Run`/`Run.Lax` shape: four proof bodies are character-identical modulo
  the `ˡ` suffix — `≲-trans.θ-step` ≡ `≲ˡ-trans.θˡ-step`, `∘ᴹ-resp-≲` ≡ `∘ᴹ-resp-≲ˡ`,
  `⊗ᵉ-resp-≲` ≡ `⊗ᵉ-resp-≲ˡ`, `trace-resp-≲` ≡ `trace-resp-≲ˡ` — plus eight duplicated
  `θ`/`θ-pure` lines. Sharing is available on exactly the brief's dependency set: a
  `record StepSim` with `θ`, `θ-pure` and `θ-step`, with
  `stepsim-∘`/`-⊗ᵉ`/`-trace`/`-trans` written once, after which `_≲_` is `StepSim` +
  `θ-discard` + strict `θ-point` and `_≲ˡ[ σ ]_` is `StepSim` + lax `θ-point`; ~14
  lines of proof and 8 of plumbing. **Caveat that makes it a measurement, not a swap:**
  `_≲_` is `Mealy-Category`'s hom equality and `Machines/Collapse.agda`'s header prices
  itself on these records' conversion behaviour, and a nested record changes the
  eta-expansion shape. If you decline, `Sim/Lax`'s header already states the identity
  in prose and nothing further is owed.
- `src/CategoricalCrypto/Machines/G.agda :: Mealy-G` (with `Mealy-G-Monoidal`) — a dead
  pair: `Mealy-G-Monoidal` greps to 2 (signature + definition) and `Mealy-G` to 3, the
  third being inside `Mealy-G-Monoidal`'s own type. Every consumer goes through
  `Mealy-Gᴹ` (6 refs, live in `Machines/Base` and `Machines/G/Lax`). Deleting the pair
  also strands `Categories.Category.Core` and
  `Categories.Category.Monoidal.Core using (Monoidal)`. Same shape:
  `Machines/Base.agda :: 𝒢ₚ-Monoidal` (2 refs, zero uses) where its sibling `𝒢ₚ` has
  89 — `Base.agda:279-282`'s comment justifies keeping the pair as two projections of
  one application, but only one projection was ever needed. And
  `Machines/Frame.agda :: αρ-λ` and `onRᵍ-⊗id` have zero consumers in the live tree
  (every hit outside their own lines is inside `SFunM/Spike/SlotFrame.agda`, which
  imports no `Machines.*` module, so those are its own copies).
- `src/CategoricalCrypto/Machines/Collapse.agda :: γ-pure` — a verified on-paper
  reduction: `γ` is **literally `α`'s six factors with `C.id C.⊗₁ C.σ⇒` appended**
  (`Categories/GConstructionTrace.agda:53-60`), and the object instantiation lines up
  exactly (`γ {A⁺}{B⁺}{B⁻}{C⁻} = α {B⁺}{B⁻}{A⁺}{C⁻} ∘ id ⊗₁ σ⇒`), so the seven-deep
  `∘ᶠ` chain is `∘ᶠ (⊗ᶠ (idᶠ (P ⊎ Q)) (σᶠ R N)) (α-pure P Q N R)` — ~7 LOC, and the
  proof becomes its mathematical content. The four-clause `λ where … refl` tail stays
  (the statement keeps `γᶠ` in four-clause form, which `stepEq` pattern-matches). Needs
  the green check: this is the 16 s module whose consumers price themselves on its
  spelling.
- `src/CategoricalCrypto/Machines/Frame.agda :: 𝕄` — a one-line projection
  (`𝕄 = monoidalCategory`) whose only consumer is `Machines.Reassoc` (4 uses, all
  feeding `solve-mor`/`MorAtoms`/`MorSolve`). Rules 18/27/28 put it there beside the
  solver calls, together with the comment that explains it — which currently sits in
  the file that does not use the frontend. `Reassoc` already opens `Frame`. Related,
  smaller: `Machines/Trace/Naturality.agda :: id⊗id-comm` is written a second time
  inline inside `Machines/Sim.agda :: mk-cong`; it is a padding fact with no trace
  content, and a named `pad-id` in `Frame` beside `pad-transport` serves both.
- - `src/CategoricalCrypto/UC/Seam/Plug.agda` (with `UC/Seam/Extract.agda` and
  `UC/Seam/Transfer.agda`) — **three of the five modules added under `UC/Seam/` this
  round are not about the seam**, and none of them imports `CategoricalCrypto.UC.Seam`.
  `Plug`'s `Tick` is a generic statement about a `Machines.Trace` loop at the
  `(⊥⊎⊤)`/`(⊥⊎Bool)` shape and its `Plugged`/`obs-resp` are about a
  `Machines.Collapse` composite at `unitᴵ`/`Ωᴵ` — no `Strat`, no `Agreeˢ`, no grade;
  its consumers are `Seam/Adequacy`, `Seam/Transfer` and `UC/Machine/Dominated`.
  `Extract`/`Transfer` are the `Certified`→`Strat` extraction and its two dominations,
  and their only consumer is `UC/Machine/Dominated`, whose own header already calls
  them "the three moving parts … next door". Moving them to
  `UC/Machine/{Plug,Extract,Transfer}` leaves a self-contained machine-layer cone and
  leaves `UC/Seam/` as exactly the chain its own header describes
  (`Seam → Adequacy{,/Wiring} → Carry`, `Grounding{,/Dead,/Prefix} → Grounded`). Two
  secondary notes: `Grounding/Dead.agda` is named for the seven-name mass-0 half that
  nothing consumes while its seventeen-name `Massed`/`Massedᵒ` half is the live content
  (`Grounding/Mass.agda` would name it for what it does); and `Plug.agda :: obs-resp`
  collides by name with `UC/Model/Observation.agda :: obs-resp` — different statements,
  both live, both in `UC.*`, and `Grounded` imports one while `Transfer` bare-opens the
  other. `collapse-resp-≈ᴹ` for Plug's.
- `src/CategoricalCrypto/UC/Seam/Grounding.agda :: EnvCtx` (with `EnvPlugs`,
  `toEnvPlugs`, `fromEnvPlugs`, `EnvAsCtx`, and `Grounded :: envAsCtx`) — **an entire
  dead sub-development, ~35 LOC, motivated by a comment that is false.** Nothing
  anywhere unpacks an `EnvCtx`: `envAsCtx` and `EnvCtx` grep to 2 each, `fromEnvPlugs`
  to 2, `EnvAsCtx` to 6 of which 4 are comments. The reason is that `stratIsEnv`
  applies `≈ᴳ-at` to the four components **inline**, so `Grounding.agda:110-111`'s
  "`EnvAsCtx → StratIsEnv` is then the one-line application of `≈ᴳ-at` to those four
  fields" names an implication that does not exist in `src/`. Two ways out: delete the
  six names and the 64-70 + 110-111 comments (keeping the measured-blockage paragraph
  at 112-118 and `Proc≈`/`toProc≈`/`fromProc≈`, which are live), or actually write
  `envAsCtx⇒stratIsEnv` and route `stratIsEnv` through it, which is the design the
  comment promises. `docs/protocol-rewrite.md:583-584` advertises `EnvCtx`/`EnvAsCtx`
  as deliverables, so the doc moves either way.
- `src/CategoricalCrypto/UC/Machine/Dictionary.agda` + `src/CategoricalCrypto/UC/Machine/Wire.agda`
  — **~250 LOC of machine-layer lemmas hosted in the UC layer (rule 27).** In
  `Dictionary`, everything from line 73 to 238 mentions no `Iface`, `Proc` or UC
  notion (sole exception `wireStep-copair`): `pure-idᵏ`, `swapᵏ`, `assocˡᵏ`,
  `assocʳᵏ`, `∘-pureᵏ`, `+₁-pureᵏ`, `pureᴵ`, `swapᴵ`, `enter-pure`, `exit-pure`,
  `tstep-inj₁/₂`, `midfn`, `midᴹ`, `id-pureᴹ`, `∘-pureᴹ`, `⊗-pureᴹ`, `midᴹ-pure`,
  `⊗ᵉ-pureˡ/ʳ`, `swap-copair`, `⌜⌝-pureᴹ`. In `Wire`, lines 74-153 likewise
  (`sandwichᴹ`, `ret≡`, `map-eq`, `map-fuse`, `sandwich-∘`, `squeeze`). Natural home:
  `Machines.Tensor.Structural` / a new `Machines.Sandwich`, with `ret≡`/`map-eq`/
  `map-fuse` in `Dp.Reasoning`. That takes `Dictionary` from 414 LOC to ~180 — the
  eight zigzags its header says it is about — and stops these facts being invisible to
  `Machines.*`.
- `src/CategoricalCrypto/UC/Machine/Dictionary.agda :: ⊗ᵉ-pureˡ` / `⊗ᵉ-pureʳ` — collide
  by name with `Machines.Tensor.Structural`'s, **with opposite handedness**: Struct's
  puts the pure factor on the right, Dictionary's on the left, different statement and
  arity. No actual clash today (Dictionary's are `private`, and `Wire.agda` imports
  Struct's while bare-opening Dictionary), but `Wire.agda:166` uses Struct's while
  Dictionary is in scope at the same point. Rename Dictionary's pair or merge them
  into Struct with one convention.
- `src/CategoricalCrypto/UC/Seam/Audit.agda :: open A public using (…)` — the facade
  re-exports `_≤UC[_]_`, `sim`, `sim-qb`, `emulate`, `simCost`, `AuditBound`,
  `audit-carry`, and its **only** importer (`UC/Seam/Audit/Bounded.agda:46`) imports
  `using (module TrivialGrade)` — not one of the seven. Every consumer of those names
  reaches them from the source. Rule 32 leans keep on a documented module (`UC.agda`'s
  header names this one), so it is your call rather than a cleanup. *(Excluded file;
  reported only.)*
- `src/CategoricalCrypto/UC/Machine.agda:55 :: open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ) public`
  — a re-export layer (rule 19) whose three consumers (`Grading`, `Dictionary`,
  `Slide`) could each `open import Data.Sum.Ext using (…)` in one line, as
  `Machines.Collapse.agda:35` already does. This is the shape round 1 asked for as "a
  scope fix"; whether it stays public API is yours.
- `src/ProbabilisticLogic/Dp/Zero.agda` — the whole 69-LOC module has **zero
  importers**, and every name is used only inside it. Its header's premise is not
  exercised: the actual consumer of the zero-mass end, `UC/Seam/Grounding/Dead.agda`,
  goes through `Dp.Mass`'s `≼ᵐbot⇒0`/`massless-≈ₚ[0]`, and `Dp/Mass.agda:217-219`
  already prices the trade. Rule 32 leans keep-for-downstream; against that, it is a
  build node whose header claims a role another module took. Delete, or add one header
  line saying it is unwired groundwork.
- `src/CategoricalCrypto/Protocol/Safety.agda :: kernel` — a spurious parameter and a
  three-way duplication. `kernel s q = evalC (step P s q)` sits inside
  `module _ {B} (P) (Bad : St P → Bool)` but does not depend on `Bad`, so the dead
  argument surfaces at the consumer (`Birthday.agda:380` writes `kernel Sys₀ Bad st q`).
  The same definition is `Examples/MerkleDamgard.agda:59-60 protoK`, and
  `Trajectory.agda:80` plus `Observe.runFrom`/`hitFrom` open-code it. One `kernel` in
  `Protocol.Observe`'s `module _ (P)` block next to `evalC`/`runFrom` retires all of
  them. The narrow version — just lift it out of the `Bad` binder — is nearly free.
- `src/ProbabilisticLogic/Dp/Dominate.agda :: dom₀-refl` (with `dom₀-trans`,
  `dom₀⇒dom`, `dom⇒dom₀`, `dom-mono`, `domˡ`, `domʳ`) — seven public names, ~30 LOC,
  the whole relation algebra of `Dom`/`Dom₀`, with no consumer anywhere. The names
  that *are* used downstream are `Dom₀`, `Dom`, `Dom≤`, `≈⇒dom₀`, `cum-shift`,
  `bind-const-zero`, `dom-bind`, `dom≤-bind`, `dom₀-bind`. Same shape, smaller:
  `Dp/Mass.agda :: mass-mono`, `total-mass`; `Interaction.agda :: run⊥-embed` and
  `run⊥-embed-gen` (an orphan tail left by this round's generalization — the live root
  is `runWith⊥-emb`); `Protocol/Observe.agda :: AllLeaves-uniformVec` (its `serve`-side
  twin *is* consumed); `UC/Machine.agda :: ApproximateObservationᴹ`;
  `UC/Model/Seal.agda :: ≈ᴹ⇒≈ᵒ` and `⊗ᵒ` (and the header clause at line 17 that
  justifies exporting `⊗ᵒ` "because it is not derivable outside" — nothing consumes
  it); `UC/Model/Bridge.agda :: ≈ℰᶜ⇔≈ᵁ`, `≈ℰᶜ⇒≈ℰ`, `≈ᴳ-refl`, `≈ᴳ-sym`, `≈ᴳ-congʳ`,
  `≈ᴳ⇒≈ᵁ`; `UC/Environment.agda :: ≈ℰ-at`; `UC/Machine/Wire.agda :: map-eq`;
  `UC/QueryBound/Object.agda :: Certifiedᴳ`, `certified⇒QBᴳ`;
  `ProbabilisticLogic/Prelude.agda :: >>=ᴹ-congʳ` (added to the re-export list this
  round with no consumer, where its sibling `>>=ᴹ-congˡ` is genuinely reached through
  Prelude). Rule 32 makes every one of these your call, which is why they are one
  entry.

- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda` — **1826 LOC that are two
  developments meeting at two points.** Rule 5's budget is 516 s and the measured warm
  cost is 34 s, so there is **no perf argument**; the case is readability. Layer A
  (expectations) speaks only `E`, `Dist-ℚ`, `Pr₁`; layer B (support combinatorics)
  speaks only `OnSupport`, `runPath` and list/vector facts; they touch only at the
  coupling's definitions and at `md-cert`. Keeping the `module MD (n k) ⦃ NonZero k ⦄ (IV)`
  parameterization and chaining `open`s the way `MerkleDamgard.agda:95` already does:
  `Core/Base.agda` (103-304: parameters, `Comp`/`General`, `pack`/`chunk`/`toBlocks`,
  `mdRun`, `respR`, the pool/`collC` vocabulary, `bound`, the coupling, `respG`),
  `Core/Marginals.agda` (306-592), `Core/Potential.agda` (594-913),
  `Core/Invariant.agda` (915-1800), and `Core.agda` keeping `md-cert`/`bad-bound` and
  re-exporting the four. Import graph `Base ← {Marginals, Potential, Invariant} ← Core`,
  the three middle modules independent of one another. The real cost is re-deciding
  `private`: most of `Invariant` is private today and would become public at the module
  boundary. No typecheck win is claimed.
- `src/CategoricalCrypto/Examples/MerkleDamgard.agda :: protoK` (with
  `runFrom-as-runWith`, `runFrom-kernel`) — three fully general lemmas about an
  arbitrary `Protocol unitᴵ B`, with nothing MD-specific in any of them, buried in the
  MD example (rule 27). `Protocol.Observe` cannot host them as they stand (it does not
  import `Interaction`, which owns `runWith⊥`, and the two clash on `run`), so the home
  is a new `src/CategoricalCrypto/Protocol/Kernel.agda`. Note `Observe.agda:62` already
  points at `Examples.MerkleDamgard` as the reference consumer of this seam, which is
  backwards. Related: `Protocol/Safety.agda :: kernel` and `MerkleDamgard.agda :: protoK`
  are the same definition (see the `kernel` entry above) — one relocation settles both.
- `src/Categories/GConstructionTrace.agda :: mid` — **this is upstream's `swapInner`,
  verbatim, and unlike round 1's `β`/`swapʳ` case it is PUBLIC there.**
  `mid = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒` is character-for-character
  `Categories.Category.Monoidal.Interchange.Braided.swapInner.from` at the same type.
  What that buys, all upstream and all located: `swapInner-commutative : i⇒ ∘ i⇒ ≈ id`
  **proves the involution `mid`'s own comment asserts and nothing in the repo proves**;
  `swapInner-natural` is `GConstructionHomCoherence.ob-nat` modulo one
  `swapInner-commutative`, and `ob-nat` is the only one of that module's three
  obligations carrying generators; and `swapInner-braiding` together with those two and
  `⊗-distrib-over-∘` derives `GConstructionTensorCoherence.T.TX` (= `⌜⌝-⊗`) outright,
  retiring `module T` (~62 LOC, one signature, one solver call). The derivation was
  checked on paper against the upstream statements, not machine-checked, so it is a
  spike, not a swap. `swapInner-unitˡ`/`-unitʳ`/`-assoc` versus `U.UL`/`U.UR`/`A.AC` was
  **not** settled — the repo states those in absorbed form with a generator. The repo
  already knows this module: `SFunM/Spike/SlotFrame.agda:313-318` records
  `Ω ≈ swapInner.from`. At a minimum `mid` should cite it (rule 30), and
  `HasInterchange` is the upstream record for exactly this data.
- `src/Categories/GConstructionTensorCoherence.agda :: midᵗ` — the free-wiring layer is
  copied across the family: `midᵗ` **6 times** (TensorCoherence ×3, TraceCoherence,
  HomCoherence, LoopCoherence), `βᵗ` **4 times**, `αᵗ` and `γᵗ` **5 times each**
  (EmbeddingCoherence has both twice in one file), and `private instance S≤S : Symm ≤ Symm`
  **8 times** — ~20 definitions, ~60 LOC, all character-identical over the per-module
  `APROP sig` and all using only `id`/`_∘_`/`_⊗₁_`/`σ`/`α⇒`/`α⇐`. One
  `Categories.GConstructionCoherence.FreeWiring (sig : APROPSignature)` exporting the
  four plus a non-private `S≤S` removes them. **Caveat that makes this a measurement,
  not a cleanup:** `GConstructionCoherence/Wiring.agda`'s header records a measured
  requirement that `⟪_⟫`/`soundness` be instantiated from the SAME `sig` (a syntactic
  fast path in conversion). Instantiating the shared module at each caller's own `sig`
  should preserve that, but rule 31 wants a before/after.
- `src/Categories/GConstruction.agda` — the four trace hypotheses are a ~10-line
  telescope written out verbatim **five times** (`GConstruction:73-82`,
  `GConstructionTrace:70-78`, `GConstructionEmbedding:69-77`, `GConstructionLoop:39-47`,
  `GConstructionMonoidal:87-95`), ~50 LOC, plus the four-argument application
  `trace-resp-≈ trace-∘ˡ trace-∘ʳ trace-comm` four times inside `GConstructionMonoidal`
  alone and positionally at every consumer (`Machines/G.agda:61`,
  `UC/Machine/Wire.agda:116,123`). A `record TraceLaws` in `GConstructionTrace`
  collapses all five and gives the four laws a name to cite instead of a bulleted
  re-listing. Not mechanical: it changes the public arity of `GConstruction`,
  `GConstructionMonoidalCategory` and `Embed.WithTrace.absorb*`. It is the single
  largest boilerplate item in that cluster. Smaller sibling: the bundle
  `Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = C.symmetric }` is defined
  identically in the same five files; making it public in `GConstructionTrace` removes
  four copies.
- `src/Data/Sum/Ext.agda :: ⊎assocˡ` / `⊎assocʳ` — duplicate `Data.Sum.Base.assocˡ` /
  `assocʳ` (stdlib-2.3 `Data/Sum/Base.agda:66-71`), which reduce on each of the three
  constructor patterns to exactly the repo's clauses, so any `refl` pin downstream
  survives. 18 references across `src/`, so it is a real edit needing a green check. If
  they stay, they should at least be level-polymorphic: the repo's `private variable`
  forces all three summands to one level where stdlib's take `Set a`/`Set b`/`Set c` —
  a general-purpose module should not be less general than what it duplicates. The
  header also now overclaims: it says `Data.Sum.Algebra` has the associativity maps
  "only inside an `↔` bundle", but `Data.Sum.Base` exports them as bare functions and
  `⊎-assoc` is built *from* them. (The `unitˡ⇒`/`unitʳ⇒` half of the header is correct.)
- `src/Categories/Category/Monoidal/Utilities/Ext.agda :: scalar-λ⇐` (with `module Hole`)
  — **wrong `Ext` parent (rules 27/29).** Upstream `…Monoidal.Utilities` is notation and
  structure; the theorems (Kelly's coherence, `coherence-inv₃`, which this file imports
  and uses) live in `…Monoidal.Properties`. Both names here are theorems, and the file's
  only use of `Utilities` is `module Shorthands`. The right name is
  `Categories.Category.Monoidal.Properties.Ext`, a convention the repo already follows
  at `src/Categories/Functor/Monoidal/Properties/Ext.agda`. Rule 30 checked: no upstream
  scalar-centrality lemma exists.
- `src/Categories/GConstruction.agda :: (module layout)` — the same layer is expressed
  once as a hierarchy and nine times as a name prefix: `GConstruction.agda` +
  `GConstructionCoherence.agda` + a `GConstructionCoherence/` directory, alongside eight
  flat top-level `GConstruction*` siblings. Upstream puts category constructions under
  `Categories.Category.Construction.*` (39 modules; no `G` or `Int`, so no rule-29
  collision). Concretely: `Categories.Category.Construction.G` and `.G.{Trace,Loop,
  Embedding,Monoidal}`, with the solver residues under `.G.Coherence.*` and the existing
  `Terms`/`Wiring`/`Decomp` moving to `.G.Coherence.Assoc.*`. Adjacent to — not covered
  by — round 1's `Monoidal/Pure.agda :: PureSub` entry, which made the same observation
  about `Categories.Category.Construction.*` for a different identifier and concluded
  "namespace *tenancy*, not collision"; if you read that as settling the naming
  question, this is a duplicate.
- `src/Categories/GConstructionEmbedding.agda :: ⌜⌝-id` — the only member of
  `WithTrace` that uses none of the four trace hypotheses; its content is
  `σ⇒ ∘ id ⊗₁ id ≈ σ⇒` (`C.elimʳ C.⊗.identity`), and it sits inside `WithTrace` only so
  the RHS can be spelled `G.id`. Stating it outside, next to `⌜⌝-resp-≈`, makes a
  hypothesis-free fact look hypothesis-free — but the five use sites depend on
  `categoryHelper`'s `id = C.σ⇒` reducing, so it needs a green check. Related, same
  file: `unitorˡᴳ`/`unitorʳᴳ`/`associatorᴳ` are the monoidal structure's data and their
  only consumer is the record literal in `GConstructionMonoidal`; rules 27/28 put them
  there beside `_⊗₀ᴳ_`/`unitᴳ`, leaving Embedding with its header's own contract
  (`⌜_,_⌝` plus the two absorptions).
- `src/Categories/GConstructionLoop.agda :: trace-conj` — misplaced and open-coded at a
  third site. It is a general consequence of the two trace naturalities with no
  `mid`/loop content, so rules 27/28 put it in `GConstructionTrace.WithTrace` beside
  `trace-gyank`/`right-superposing`, whose stated purpose is exactly "the consequences
  of the trace hypotheses"; and `GConstructionMonoidal.homomorphismᴳ:144-148` open-codes
  it (`(refl⟩∘⟨ trace-∘ʳ) ○ trace-∘ˡ` at `k = h = mid`) while already having it in
  scope, so those two chain lines collapse to one `≈⟨ trace-conj ⟩`.
- `src/Categories/GConstruction.agda :: GConstruction` — this module and
  `GConstructionMonoidal` wrap their whole body in an **anonymous** `module _ (C) (Monoidal) (Traced) where`,
  while `GConstructionTrace`/`GConstructionLoop` use top-level parameters and
  `GConstructionEmbedding` uses a named `module Embed`. An anonymous module cannot be
  opened at arguments, which is why `GConstructionMonoidal` writes
  `GC.composeᴳ-raw C M T` three times and `GC.composeᴳ` in two `unfolding` lines where
  `GConstructionTrace` gets one `module W = GT C M T`. Making the parameters
  module-level, or naming the inner module, removes the repeated application and one
  level of indentation from 180 lines — at the cost of a small public-surface change at
  every consumer.
- `src/Categories/GConstructionHomCoherence.agda :: pattern 10F` / `11F` — stdlib's
  `Data.Fin.Patterns` stops at `9F`, and this round added two character-identical
  copies (here at file top level, so re-exported, and in
  `GConstructionTensorCoherence.agda:184-185`). Rules 27/29: a new
  `src/Data/Fin/Patterns/Ext.agda` (the repo has 18 `*/Ext.agda` modules, so the
  convention is established) with both sites importing it.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: os-⊤` (with
  `OnSupport-mono`, `OnSupport-bind-return`, `OnSupport-∧`) — four general additions to
  the `OnSupport` kit, `private`, split across three blocks 480 lines apart, all stated
  over an arbitrary `Dist-ℚ A` with no MD content and none used outside Core. Rules
  27/28: they belong in `ProbabilisticLogic/Distribution/RationalDist.agda` beside
  `OnSupport-return`/`OnSupport-bind`/`OnSupport-Dmap`.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: sumR` (with `sumR-tri`,
  `tri-mono` and `φ-init`'s `sumR1`/`arith`) — ~45 lines whose only job is to bridge two
  encodings of the same triangle number: `Examples/RandomOracle.agda:191-193` defines
  `triangle : ℕ → ℚ` by ℚ-recursion, `Uniform/Birthday.agda:36-41` defines `sumN : ℕ → ℕ → ℕ`
  with `Γ t j = fromℕ (sumN t j) * ε`, and `bound` is stated in the first encoding while
  `φ` is in the second. Either state `bound q = Γ 0 (q * k)` and the bridge vanishes, or
  prove `triangle-sumN : ∀ t → triangle t ≡ fromℕ (sumN 0 t)` once, upstream, where the
  next consumer will want it.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: chunk` (with `chunk-inj`,
  `toList-inj`, `snoc-view`) — stdlib has `Data.Vec.Base.group`, which returns the
  reconstruction witness with the chunking, so `chunk-inj` becomes a three-step
  `M ≡ concat (chunk j M) ≡ concat (chunk j M') ≡ M'` instead of the recursive
  `take-drop-inj` route; `toList-inj` is `Data.Vec.Properties.toList-injective` modulo a
  `cast-is-id` step; and `snoc-view` is `Data.List.Base.initLast`, which needs no
  `0 < length xs` hypothesis. None is a mechanical swap (the view-to-Σ step is real),
  but all three are the ecosystem form. Consequence to weigh: Core is the only consumer
  of the repo's `Data.Vec.Properties.Ext.take-drop-inj`.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda` — `proj₁ (proj₂ …)` occurs
  **138** times and `proj₂ (proj₂ …)` 47 times; `φ-step` alone spells
  `proj₁ (proj₂ s)` eight times. Named accessors for the two shapes that carry them
  (`FState = Bool × (Comp.Table × General.Table)` and the walk output
  `Comp.Table × (CV × Bool)`) are the single largest legibility lever in the file. They
  stay definitionally transparent, but several sites are inside `E`-integrands and
  `with`-scrutinee positions where the file documents conversion sensitivities, so this
  needs a green check.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: MDInvData` — a 6-line
  record with a single inhabitant that `md-cert` immediately projects four times; its
  fields are a subset of `SuperCert`'s plus `flag⇒coll`. Rule 18 eta-scaffolding:
  `md-cert` can take the four components directly. The sibling
  `ChimericLedger/Birthday.agda` builds its `SuperCert` with no such record. Judgment
  only because it removes a public name.

### Simplifications / perf not committed (judgment needed)

- **The three automatic sweep classes, unfinished.** `using-drop` ran on 1 of 109
  files before I stopped it to free the gate for the review's own commits; the
  measured cost that justifies stopping is **~4 minutes of gate time for the first
  file alone** (18 `using` lines, 16 dropped), against 786 lines tree-wide in scope
  and a gate now shared with three other agents. At that rate the class is 5-9 hours
  of serialized agda. `join-lines`, `implicit-drop` and `binder-drop` were not
  started. Remaining counts: `using-drop` 768 lines over 108 files; `join-lines`,
  `implicit-drop`, `binder-drop` unenumerated. Round 1's verdicts still stand for the
  two judgment-bearing ones (`implicit-drop` declined as a class, `binder-drop` kept
  0 of 259), so the live work is `using-drop` and `join-lines`.
- **The two `enum-*` classes, unfinished per site.** `enum-with` 118 sites and
  `enum-where` 358 sites (252 flagged) are enumerated (`.claude/sweeps-tally/`) but
  not dispositioned individually, which the contract requires and I did not do. For
  `enum-with` the missing half of the mechanism now exists: I wrote
  `.claude/sweeps/with_case.py` under the toolkit's README rule 2 (tree-sitter-free
  textual transform of the `lhs with scrut` / `... | pat = rhs` shape into
  `case_of_` + `λ where`, one site at a time, pagda + warning-gate oracle, restores on
  red, inserts `open import Function.Base using (case_of_)` at its sorted position when
  `case_of_` is out of scope). It is dry-validated on five `ChimericLedger/Value.agda`
  sites (output is well-formed Agda) but **never run under the oracle**, so it carries
  no verdict yet. Expect a low yield: the dominant shape is `with x ≟ y` where the
  goal's own reduction depends on the scrutinee, which `case_of_` cannot abstract —
  but that is a prediction, and the script exists precisely so it does not have to
  stay one. For `enum-where`, `.claude/sweeps/where_inline.py` already exists and
  round 1 recorded that the tally's `approxUses` is unreliable, so the script's own
  occurrence count is the evidence to use.
- `src/CategoricalCrypto/UC/Machine/Run.agda` vs `src/CategoricalCrypto/UC/Machine/Run/Lax.agda`
  — **~30 duplicated lines, and the header reason does not rule out sharing them.**
  Normalizing indentation and the `-sim`/`-lax` suffix: `contᵍ`, `resume-*` and
  `runFrom-*` (Run 82-101 vs Lax 69-88) are character-identical, `padϕ` is identical,
  and `pad-fn`/`step-*` differ only in `S.θ sim` vs `L.θˡ l`. Lax's header says the
  induction is repeated because Run's helpers are parameterized by a `_≲_` "whose
  `θ-discard` a lax simulation deliberately does not carry" — true of the current
  parameterization, but the induction's actual dependencies are only `ϕ : St f → St g`
  and the step law, which both sides have. Parameterizing a shared module over those
  two leaves `run-sim`/`run-lax` differing only in the point law. If you decline, the
  header should say "over `ϕ` and the step law" rather than implying no sharing is
  possible.
- `src/CategoricalCrypto/UC/Model/Environment.agda` — **the presheaf is proved twice.**
  Its `_≋_`, `≋-isEquivalence`, `≈ᵒ⇒≋`, `ℰ₀`, `ℰᵒ` are `UC/Environment`'s `_≋_`,
  `≈⇒≋`, `ℰᴼ`: same `_≋_`, same `F₁ = _∘ f` with a `sym-assoc`/`sym-assoc` transport
  in `cong`, `identity = identityʳ`, `homomorphism = sym-assoc`,
  `F-resp-≈ = ∘-resp-≈ʳ`, differing only in routing the transport through
  `∼-cast`/`⟦⟧-resp-≈` versus `∼ᴼ-resp`/`obs-resp`. ~28 LOC. The blocker is placement,
  not content: `UC.Environment` is parameterized by a whole `UCBase` while `ℰᴼ` uses
  only `𝒞` and the `Observation`. Safe route: split `Test`/`Closure`/`obs`/`_≋_`/
  `≈⇒≋`/`ℰᴼ` into a sub-module parameterized by `(𝒞) (O : Observation 𝒞 os ℓs)` only
  (rule 27, and it keeps no `Grading` in `Model/Environment`'s closure). The
  alternative — moving `observationᵒ`/`ucBaseᵒ` up and instantiating
  `UC.Environment ucBaseᵒ` — carries the documented perf risk that a conversion
  meeting two `Grading` records is the unaffordable configuration
  (`Seal.agda:53-59`, `Enrichment.agda:5-14`). Either way `UC/Environment.agda:67`'s
  claim that `UC.Model.Environment.ℰᵒ` "is this at the machine model" becomes true;
  today it is false.
- `src/CategoricalCrypto/UC/Model/Unit.agda :: AnyEnvironment` — **five definitions
  duplicated verbatim** with `src/CategoricalCrypto/UC/Model/Pin.agda:54-71`
  (`refl-at`, `dummy-at`, `trans-at`, `compose-at`, `collapse-at`, character-identical
  modulo two spaces), and both files open with the same `private variable`. `Pin`'s
  block **is** `AnyEnvironment ℰᵒ`, and `AnyEnvironment` is never instantiated. Making
  `Pin` read `open Unit.AnyEnvironment ℰᵒ` works dependency-wise and would make
  `AnyEnvironment`'s claim load-bearing rather than a standalone re-typing.
- `src/CategoricalCrypto/UC/Model/Bridge.agda :: observationᵒ` — hand-rolls
  `UC.Approximate.Induced.observation`. Its four interesting fields are `Ap._∼ᵃ_`,
  `Ap.∼ᵃ-isEquivalence`, and a `⟦⟧-resp-≈` that is `Induced`'s at `ℚ-errors` (where
  `ε₀-least = <⇒≤`). `UC/Machine.agda:145-155` already builds `Observationᴹ` this way.
  `private module I = Induced ∣𝔾ᵒ∣ Approximationᴹ 𝟘ᵒ Ωᵒ Obs (λ e → ≈ₚ⇒≈ₚ[0] (obs-resp e))`,
  `observationᵒ = I.observation`; levels check out. **It also hands you
  `approximateᵒ = I.approximate`**, which is the `qapx` the asymptotic cone is missing.
  This cone is eta-sensitive, so measure before/after rather than assume.
- `src/CategoricalCrypto/UC/QueryBound/Counting.agda :: eraseCons` — is
  `UC/QueryBound.agda :: map-square` verbatim up to renaming (same four-step chain in
  the same order). `map-square` is `private` and inside an `opaque`, so the dedup needs
  it promoted to `Dp.Reasoning` (with its `opaque` and its comment) together with
  `map-cong` and `return-≡`, which are themselves duplicated character-for-character
  between `QueryBound.agda:74-84` and `Counting.agda:56-64`; then
  `Counting.map->>=` retires to `Dp.Reasoning.bind-map` (same statement *and* proof
  term) and the four `eraseCons` sites become `map-square` calls that get the
  `opaque` chain-sharing the definition exists to provide. I landed only the two
  blocks the brief named (`a2cdc2ca`); this second half touches a module whose header
  says it is at its measured typechecking budget, so it wants a before/after
  measurement, not a swap.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda` — **seven more verified
  rule-30 one-liners** (four of the original eleven landed; see *Committed*). Each
  stdlib source below was located on disk and read; each pair of statements was
  compared: `∨-true` (948) is
  `Data.Bool.Properties.∨-zeroʳ` (`:267`); `∨-false` (1023) is `∨-identityʳ` (`:257`);
  `just-inj` (1032) is `Data.Maybe.Properties.just-injective` (`:39`), which
  `ChimericLedger/Value.agda:31` already imports; `suc∸1` (688) is
  `Data.Nat.Properties.suc-pred` (`:1754`, and
  `pred n = n ∸ 1` by definition); `0≤ε` (585-589) is
  `ProbabilisticLogic.Distribution.Uniform.0≤inv-pow-2 n` (`:132`), from a module Core
  already imports — replacing a six-line derivation through `P-uniform-Vec`/`E-const`/
  `E-mono`/`0≤bool` with one application, which also makes `P-uniform-Vec` and
  `replicateᵛ` droppable; and `+-inter` (662) / `+-lswap` (670) are
  `Algebra.Properties.CommutativeSemigroup`'s `interchange` / `x∙yz≈y∙xz` at ℚ's `+`,
  the exact pair round 1 committed at `6a70b955` — copy the import verbatim from
  `Dp/Commutative.agda:28-30` (ℚ has `+-0-commutativeMonoid`, not a bare
  `+-commutativeSemigroup`). These seven are left because each needs an import the file
  does not already have — `Data.Bool.Properties`, `Data.Maybe.Properties`, the
  `Algebra.Properties.CommutativeSemigroup` instantiation at ℚ — and adding three
  imports to a 1826-LOC module with three importers is one deliberate batch with one
  check, not an end-of-session addendum.
- `src/ProbabilisticLogic/Dp/Mass.agda :: cum-add` and
  `src/ProbabilisticLogic/Dp/Dominate.agda :: cum-zero` — exact re-derivations of
  `Dp/Commutative.agda`'s public `cum-test-+` and `cum-test-0` (and `Mass.leafₚ-add`
  / `Dominate.leafₚ-zero` are character-identical to `leafₚ-test-+` / `leafₚ-test-0`,
  `node-zero` finisher included). `Mass.cum-const`/`leafₚ-const` follows from
  `cum-test-*` via `cum-cong-P` and `*-comm`; `Mass`'s private `regroup` has the same
  statement as `Commutative`'s private `node-+` up to argument order, and
  `Dominate`'s `spread` is `node-+` at `y₁ = y₂ = e` then `sym (*-distribʳ-+ …)`.
  ~34 LOC plus three helpers. The cheap fix (import from `Commutative`) reverses
  round 1's `6a70b955`, which deliberately let `Dp.Elgot`/`Dp.Iter.Out` drop that
  dependency; the right fix (move the "`cum n d` is a linear functional in its test"
  section plus `node-+`/`node-*` into `Dp.agda`'s existing two-term-arithmetic
  section, rules 27/28) does not.
- **The `UC/Seam` cluster's own duplication, four items.**
  `UC/Seam/Plug.agda :: Plugged.point-red` is **byte-identical** to
  `UC/Seam/Grounding/Dead.agda :: point-⊛` at `S := MC.state K`, `T := MC.state u`
  (same statement, since `Machines.Collapse.Sᴳ g f = MC.state g MC.⊛ MC.state f`, and
  the same one-term proof), and `UC/Seam/Adequacy.agda :: point-red` is the same lemma
  plus one step for `stateˢ`'s constant point — three copies of a fact that mentions
  only `MC.State`, `_⊛_` and `point`, so its home is a `Machines` properties module.
  `UC/Seam/Transfer.agda :: ρᴷ`/`ρᵁ` **are** `UC/Seam/Adequacy/Wiring.agda ::
  outE`/`outU` paired with the other factor's state, clause for clause, and
  correspondingly `Wiring.kᵂ`'s clauses 2-4 are `Transfer.bodyᴿ`'s two clauses with
  `mapₚ` spelled as bind+return; one shared `outE`/`outU` pair (they need only
  `B : Iface`) retires both copies and makes the two loops visibly the same dispatch.
  `UC/Seam/Grounded.agda :: plug-run` re-derives `UC/Seam/Plug.agda ::
  Plugged.collapse` — `plugˢ B d u` is definitionally `Plug.Plugged.tracedᴹ` at
  `K := strategyEnv B d`, and `plug-run`'s witness is `collapse`'s inverted, composed
  with one `unprocᵒ-∘` step; `Grounded` does not import `Plug` at all today. This is
  the cleanest of the three.
  `UC/Seam/Carry.agda :: Reads` is a **third spelling** of `Dp.Stable`'s
  eventually-constant reading: it unfolds to
  `Σ[ n ] ((m : ℕ) → cum (n + m) x (indᵇ b) ≡ u)`, which is verbatim the codomain of
  `Dp.Stable.Stable⇒Σ+` and verbatim `Protocol.Machine.PrAgree`'s body. Give
  `Dp.Stable` a name for that Σ-shape (it has none — `Stable` itself uses the `n ≤ m`
  form) and both become one application.
- `src/CategoricalCrypto/UC/Seam/Extract.agda :: coinᵈ` (with `E-coinᵈ`) —
  general-purpose, buried in the narrowest module in the cluster: both are
  `{A : Set} → Dₚ A → …` and neither mentions the module's four parameters. The home
  is `ProbabilisticLogic.Dp.Coin`, which already has the other direction (`coinₚ`) and
  the `cum` agreement (`coinₚ-cum`); `coinᵈ` is exactly "a `Dₚ` node's two weights as a
  `Dist-ℚ Bool`" and its two obligations are the node's own `wt-1`/`wt-nn`. Related:
  `Transfer` composes `Dp.Stable.coin-bind-cum` with `E-coinᵈ` at four sites, and that
  composite is one lemma that belongs next to `coinᵈ`. Same class in the same cluster:
  `UC/Seam/Carry.agda :: one-sided` and `shift` mention no `Iface`/`Proc`/`Protocol`
  at all — `one-sided` belongs in `Dp.Advantage` beside `_≼ₚ[_]_`, `shift` in
  `Data/Rational/Properties/Ext` (which already hosts every other ℚ fact that proof
  uses), and moving both leaves `Carry.agda` as exactly what its header says it is.
- `src/CategoricalCrypto/Examples/ChimericLedger/Birthday.agda :: memb` (with `memb-∈`,
  `memb-∉`) — **verified stdlib collapse, 13 lines to 3.** `memb h hs` is
  `⌊ h ∈? hs ⌋` for `_∈?_` from `Data.List.Membership.DecPropositional _≟_`, and the
  reduction chain was checked against stdlib source: `any? P? (x ∷ xs)` is
  `map′ … (P? x ⊎-dec any? P? xs)`, `does (a? ⊎-dec b?) = does a? ∨ does b?`, and
  `map′` preserves `does` — so `⌊ h ∈? (g ∷ gs) ⌋` reduces to
  `⌊ h ≟ g ⌋ ∨ ⌊ h ∈? gs ⌋` definitionally, which is `memb`'s clause, so `dup`'s
  definitional behaviour (relied on at three sites) is unchanged. Then
  `memb-∈ hs h e = toWitness (Equivalence.from T-≡ e)` and
  `memb-∉ hs h e = toWitnessFalse (Equivalence.from T-not-≡ e)`. Needs a green check
  because the chain is definitional, not propositional.
- `src/CategoricalCrypto/Examples/ChimericLedger/Birthday.agda :: lookup-bs-∈` — a
  general `RandomOracle` fact, written twice in the repo, and this is the weaker of the
  two: `MerkleDamgard/Core.agda:1476-1480` has `lookup⇒mem` in the `Any (_≡ (key , w))`
  form for the same `RandomOracle.lookup-bs`, where Birthday's Σ-form forces a
  `subst (Stale …)` dance at its use site. Right home (rule 27):
  `Examples.RandomOracle`, beside `lookup-bs`/`freshQuery`, in the `(q , h) ∈ s` form —
  −8 lines here and −5 in Core. Same cluster, same shape:
  `Birthday.agda :: φ-bad` and `Trajectory.agda :: init-good` are the same three-step
  `cong not (Equivalence.to T-≡ (≡⇒≡ᵇ _ _ eq))` idiom, i.e. two instances of
  `total s ≡ total s₀ → badTotal s₀ (s , tbl) ≡ false`, which belongs beside
  `badTotal` in `POV.agda` (both files then drop three single-name imports each); and
  `Birthday.agda :: oracle-hit`/`oracle-miss` are pure unfoldings of `POV.oracle`'s own
  `step` with no Birthday content, which belong beside `oracle`.
- `src/CategoricalCrypto/Examples/ChimericLedger/Value.agda :: Shape.accepted` — does
  not carry the balance equation `eb`, and that forces a **third** copy of the
  validation cascade: `accept-eq` consumes `eb` but `accepted` does not expose it, so
  `applyTx-total-≤` and `applyTx-total-fresh` each re-walk the whole five-way
  `with … in` cascade to recover it (12 duplicated lines) even though `shape` exists
  precisely to walk it once (the header says so). One extra field on `accepted`
  collapses each to a two-way case; cost is a pattern variable at the two Birthday
  match sites. Related, same file: `lookupU-tail`/`lookupU-cons` and `lookupU-cons-≢`
  are three near-identical "re-apply the `k ≟ k₀` decision by hand" helpers in two
  `private` blocks 50 lines apart, with the explanatory comment attached only to the
  later one (rule 28). And `Value.agda :: ⊥-just`/`⊥-nothing` are
  `Data.Maybe.Ext.nothing≢just`/`just≢nothing` with the `⊥-elim` absorbed — used ~20
  times each, so the local abbreviation earns its keep, but it should be *defined*
  from `Data.Maybe.Ext` rather than by a second absurd pattern.
- `src/CategoricalCrypto/Examples/ChimericLedger/Birthday.agda :: presTree` and
  `φ-step`'s `served` — ~25 lines of parallel scaffolding: both repeat the
  `with shape ser inputConsuming s tx` cascade, the `step-rejected`/`step-accepted`
  `subst`s, `qs`, `K`, and the `go : (r : Maybe Hash) → … ≡ r → …` / `go (…) refl`
  idiom. One "reading of an activation" datatype resolving both the shape cascade and
  the table lookup (rejected / table-hit / fresh-sample) would let both consumers case
  once. Bigger than a sweep; the largest single structural redundancy in the file.
  Separately: `s₀`, `Sys₀` and `Bad` are `private` but appear in the type of the public
  `cert : HitCert Sys₀ Bad εbirthday`, so a downstream reader cannot name the system or
  the bad event the certificate is about — `cert` is effectively unusable outside the
  file while `target` is fine. Rule 32 leans public; they are three-line abbreviations.
- **Three more verified one-liners, not landed** (the other four did — see
  *Committed*), each grep-checked against the definition it replaces, each one site:
  `src/ProbabilisticLogic/Dp/Mass.agda :: mapₚ-≼ᵐ` (199-204) — the five-line
  `cum-cong-P`/`>>=ₚ-boundB` sandwich is `Dp.Iter.mapₚ-cum`'s *equality* directly:
  `mapₚ-≼ᵐ d h n = suc n , ≤-reflexive (sym (mapₚ-cum n h d (λ _ → 1ℚ)))`; no cycle
  (`Dp.Iter` imports only `Dp` + stdlib), but it does add an import.
  `src/ProbabilisticLogic/Distribution/Uniform/Birthday.agda :: 0≤scaled` (31-33) — is
  `Data.Rational.Properties.Ext.0≤*` (`Ext.agda:50`) at
  `0≤fromℕ m` and `0≤inv-pow-2 n`; needs the `Ext` import, after which `*-zeroˡ` drops
  from the line-17 `using` list.
  `…/RationalDist/Expectation.agda :: Prᵇ⊥` (88) — write it through the `E⊥` defined 19
  lines above (`Prᵇ⊥ b μ = E⊥ μ (indᵇ b)`); it is the same term, and the comment at
  line 90 (`` `Pr₁⊥` is `E⊥` at the verdict indicator, on the nose. ``) then restates
  what the code shows and goes with it.
  Related, same class, needing one more grep than I could run:
  `src/CategoricalCrypto/UC/Machine/Dominated.agda :: ε≤ε+δ` (191-192) uses five `ℚP.`
  prefixes where `Data.Rational.Properties` is bare-opened on line 33 and the same
  names appear unqualified at 135-136 and 166-167; after dropping them the `as ℚP`
  alias is unused.
- `src/ProbabilisticLogic/Distribution/Uniform/Collision.agda :: countMatch` — the
  right home (rule 27), and it now has two older twins. `countMatch`/`E-countMatch` is
  the general form of `Examples/RandomOracle.agda`'s private `count-matches`/
  `sum-bound`/`sum-bound-closed`/`E-collisions`/`E-collisions-rec` — same recursion,
  same `lookupᴰℚ-+`/`P-uniform-Vec`/`suc·c` proof, differing only in the table's entry
  shape (`count-matches s = countMatch (map proj₂ s)`) — and
  `MerkleDamgard/Core.agda:645-648`'s private `cm-nn` is `0≤countMatch` at that table
  form. `RandomOracle.agda` is inherited; `MerkleDamgard/Core.agda` is in scope.
- `src/ProbabilisticLogic/Distribution/Uniform/Birthday.agda :: sumN` (with
  `sumN-mono`, `sumN-≤`, `square`) — pure ℕ arithmetic inside a module parameterized
  by `(n : ℕ)` that they never mention, and `src/Data/Nat/Properties/Ext.agda` exists.
  Symptom: `MerkleDamgard/Core.agda:605,639` reach `sumN` only by `open Birthday n`,
  i.e. through an unrelated parameter, and `Core.agda:634-642`'s `sumR-tri`
  re-derives `Birthday.Γ-step`'s own `fromℕ-+`/`*-distribʳ-+` argument.
- `src/CategoricalCrypto/UC/Machine.agda :: Reindex` — is upstream's
  `Categories.Category.SubCategory.FullSubCategory` field for field (same twelve
  fields, same bodies, levels work out), so `𝒫ᴵ = FullSubCategory (𝒢ₚ 0ℓ) ⟦_⟧ᴵ` would
  delete ~25 lines. **But** every field here pins the object implicits and the header
  records that as measured-necessary (inference "exhausts a 10 GiB heap"), where
  upstream writes the unpinned form. So this is a measurement, not a swap: if it
  checks, take it; if it does not, the header should still cite `FullSubCategory` and
  say it cannot be used, because rule 30 makes a reader ask.
- `src/CategoricalCrypto/GamePlaying.agda :: cond` / `cond-diag` — verbatim
  `Data.Bool.Base.if_then_else_` and `Data.Bool.Properties.if-eta`
  (stdlib-2.3 `Data/Bool/Properties.agda:748-751`). The local copies exist because the
  prelude hides `if_then_else_`; a direct `Data.Bool.Base` import is the rule-30
  alignment. Caveat: `if_then_else_` is `infix 0`, so the six argument-position uses
  in `MerkleDamgard/Core.agda` (439, 443, 534, 536, 563, 581) need parentheses, and
  that file must be re-measured.
- `src/CategoricalCrypto/UC/Machine/Grading.agda` — the eight `where` blocks rebuild
  what they just destructured (~45 lines): each `*-object` wrapper matches
  `(X⁺ , X⁻)` then re-pairs via `retᴵ` in a three-line ascribed `where`. `Σ` has eta,
  so `⟦ retᴵ X ⟧ᴵ ≡ X` should hold definitionally without the match and collapse all
  eight — but this is the module whose header says the elaboration is delicate, so it
  needs a measurement. Conservative fallback (rule 14): drop the redundant `X : Iface`
  ascriptions and put each `where` on one line, −19 lines.
- `src/CategoricalCrypto/Protocol/Machine/Compose.agda :: private module block` — five
  module aliases (`MC`, `MT`, `S`, `V`, `K`) re-applied with identical arguments to
  ones `Machines.Collapse` already exports publicly, and the file then uses **both**
  spellings (local `MT`/`MC`/`V` in the body, `Col.MT`/`Col.MC`/`Col.T`/`Col.W` in
  `morphism-∘`'s own statement). `open Col using (module MC; …)` unifies them. Perf
  caveat: the aliases are definitionally equal but not the same generated names, and
  this module's header prices itself at a measured 11 s — re-measure before landing.
- `src/CategoricalCrypto/GamePlaying.agda :: badProb-super` — the eight-argument
  explicit telescope is repeated verbatim on all three recursive calls plus the clause
  heads; a `module _ (…) where` wrapper keeps the exported type and saves ~8 lines.
  Sibling: `badProb-bounded`'s seven `SuperCert.… c` qualifications want
  `where open SuperCert c`, which is what `Protocol.Safety` already does.
- `src/ProbabilisticLogic/Distribution/Uniform.agda :: indᵇ-≤1` — see the general-ℚ
  entry below; recorded here because the same fact is written three times
  (`Dp/Mass.agda:126-130`, and the `where` blocks of `Expectation.Pr₁≤1` and
  `Expectation.Pr₁⊥≤1`) and belongs once beside `bool→ℚ`'s definition, where `0≤1ℚ`
  and `≤-refl` are already in scope.
- `src/CategoricalCrypto/Machines/G/Lax.agda:55-71` — mechanical, not landed: the two
  theorems spell `𝔾.U [ B , C ]` and `𝔾.U [ g ∘ f ]` where `MonoidalCategory` already
  does `open Category U public`, so `B 𝔾.⇒ C` and `g 𝔾.∘ f` work and line 10's
  `open import Categories.Category using (Category; _[_,_]; _[_∘_])` goes entirely
  (`Category` is already unused there). It would also make the file self-consistent —
  `⊗₁ᴳ-resp-≈ˡ` two lines below already writes `𝔾._⊗₁_ g f`. Left because this is a
  conversion-sensitive layer (the other theorem sits in an
  `opaque unfolding GM._⊗₁ᴳ_`) and it deserves its own check rather than riding along
  with the import drops.
- **Four more dead-scaffolding removals in `UC/Seam`, identified and not landed.**
  `UC/Seam.agda:82` — `module 𝒫 = Category 𝒫ᴵ` is dead (`𝒫` occurs elsewhere only in
  two comments), and with it line 52's `open import Categories.Category` (`Category`
  occurs only at 52 and 82).
  `UC/Seam/Extract.agda:50` — `private module MC = Core (𝒱ₚ 0ℓ)` is dead (`MC.` occurs
  zero times in the file), and with it lines 45, 40 and 29: `Core`, `𝒱ₚ` and `0ℓ` each
  occur only on their own import line and inside line 50. Four dead lines.
  `UC/Seam/Grounded.agda:31` — `open import …Protocol.Machine.Total using (TotalRun)`;
  `TotalRun` appears in the file only in two comments (the hypothesis is bound as an
  unannotated `tu`).
  `UC/Seam/Grounded.agda :: stratIsEnv` — `procᵒ (strategyEnv B d)` written three times
  in one term; the file's own `plug-run` already binds it once in a `where`.
- **Five more mechanical edits identified and not landed, for gate-time reasons only.**
  Each is a one-site change with no judgment in it; I am listing them rather than
  claiming coverage I do not have.
  `src/CategoricalCrypto/UC/Model/Reading.agda:33` — `open import Categories.Morphism.Reasoning ∣machines∣ using (cancelInner)`
  sits mid-file; rule 10 wants the sibling pattern (`import … as MR` at the top,
  `open MR ∣machines∣ using (cancelInner)` after the header), which `Model/Bridge.agda:34,55`
  and `Model/Unit.agda:33,92` already use. Reading is the only outlier.
  `src/CategoricalCrypto/UC/Model/Seal.agda:94` — `M._∘_ g f` → `g M.∘ f` (rule 20;
  `M` is a `Category` alias used only here).
  `src/CategoricalCrypto/UC/Model/Unit.agda:89,94` — replace
  `import Categories.Morphism as Mor` + `Mor._≅_ ∣𝔾ᵒ∣ 𝟘ᵒ 𝟘ᵘ` with
  `open Mor ∣𝔾ᵒ∣ using (_≅_; module _≅_)`, so the parameter reads `(unit-≅ᵒ : 𝟘ᵒ ≅ 𝟘ᵘ)`
  and `private module ι = _≅_ unit-≅ᵒ`; the file already does exactly this for `MR`.
  `src/CategoricalCrypto/UC/Model/Observation.agda:63-69` — the three declarations
  `infix 4 _∼ᴼ_` / `_∼ᴼ_ = Ap._∼ᵃ_` / `∼ᴼ-isEquivalence = Ap.∼ᵃ-isEquivalence` are
  eta-wrappers; `open Ap using () renaming (_∼ᵃ_ to _∼ᴼ_; ∼ᵃ-isEquivalence to ∼ᴼ-isEquivalence)`
  is the rule-18 form with rule 11's explicit licence, and `IsEquivalence` may then
  drop from the imports.
  `src/CategoricalCrypto/UC/Machine/Run.agda:58-61` — inline the single-use
  `private pad = S.θ sim V.⊗₁ V.id` into `pad-fn`'s type; the sibling
  `UC/Machine/Run/Lax.agda:57` already writes the inlined form, so the shape is known
  to check.
- `src/CategoricalCrypto/UC/Machine/Dictionary.agda :: exit-pure` — a matched pair with
  `enter-pure`, split across the `private` line purely by current importer
  (`enter-pure` is imported by `Wire.agda`; `exit-pure`, used 8× in-file, is not).
  Rules 26/32: make the pair uniform either way.
- `src/CategoricalCrypto/GamePlaying.agda :: badProb-super` — see the telescope entry
  below; additionally `Machine/Probabilistic/Model.agda`'s three hypothesis records
  (`MachineCategory`, `MonoidalMachines`, `QueryBudget`) are now all satisfiable from
  in-tree material (`Machines.Base.Tracedₚ`), which the header no longer denies after
  `38495a94` — worth checking whether the module should now *build* `MachineModel`
  rather than keep bundling hypotheses.
- `src/CategoricalCrypto/UC/Machine/Wire.agda :: map-fuse` — re-derives
  `Dp.Reasoning.map-map` with the pointwise `≡` fused into the same `bindᶠ`;
  `map-map d h k ⟨≈⟩ map-eq d (k ∘′ h) l eq` proves the same statement from the
  existing lemma and makes the currently-dead `map-eq` live. Rule 27 also wants
  `ret≡`/`map-eq`/`map-fuse` in `Dp.Reasoning` beside `map-map`/`map-arg`.
- `src/CategoricalCrypto/UC/Machine/Wire.agda` and `src/CategoricalCrypto/UC/Machine/Slide.agda`
  — eight and nine signatures re-bind the same telescope (`{X Y X′ Y′ : Set}` /
  `{A B Y : Iface}`), which rule 16 wants hoisted into one `private variable` block.
  `Wire` is clean (no clause binds any of them positionally); `Slide` is not
  (`slideᴹ {B} {Y} E m x`, `λ-slide {Y} m`, `T₁-wire Y up down` do), so that one needs
  a check.
- `src/CategoricalCrypto/UC/QueryBound/Object.agda` — placement verdict: **it belongs
  here** (the `⟦_⟧ᴵ`/`retᴵ` re-indexing boundary with a measured reason, and
  `QueryBound.agda` is at budget and would gain a `Protocol.Machine` dependency). Two
  small things: `qb-∘ᴳ` — the one ᴳ-form not here — sits in `Compose/Laws.agda`
  (forced: it needs `Compose.Step`) and the header never says so, so a reader looking
  for the composition case finds nothing; and lines 37-42 are two adjacent `opaque`
  blocks (`opaque QBᴳ` then `opaque unfolding QBᴳ`) which a single block should
  subsume — flagged **unverified**, and only worth doing on a green + re-measured
  check, since it is a deliberate perf boundary.
- `src/CategoricalCrypto/UC/Budget.agda :: ctxBudget` — the header's middle sentence
  reads against the definition: "so the conservative bound is `c` alone. The product
  form is kept for the closures that do relay downwards, but GUARDED at `c′ ⊔ 1`",
  one line above `c ℕ.* (c′ ℕ.⊔ 1)`. Reword to say the product is what is defined and
  `c` is what would suffice for closed contexts. Everything else in that header
  checks out (twelve laws / thirteen fields, the arithmetic, both module-parameter
  consumers).
- `src/CategoricalCrypto/UC/Machine/Budget.agda :: qb-∘ᴹ` — the only one of thirteen
  fields given a named top-level definition; the other twelve are inline lambdas.
  Either say in one line why `qb-∘` alone needs the named, fully-ascribed form (if it
  is a perf device it should say so, rule 26), or make it a lambda.
- `src/CategoricalCrypto/UC/Machine.agda :: subᴵ′` — only reorders `subᴵ`'s implicits,
  and the field ordering it was built for is gone with the R1 cone (its comment said
  so; `<COMMENTS>` fixed the comment, not the definition). Both live sites already
  pass all three implicits explicitly, so they would read `subᴵ {X} {Y} s {A}`.
  Retire it, or keep it and say what it is for now.
- `src/CategoricalCrypto/UC/QueryBound/Compose/Step.agda :: Bd` — declared, defined,
  **zero uses** (`Nᶜ` re-spells the same machine inline and `solveᶜ` takes `bodyStep`
  directly). Delete it or route `Nᶜ` through it. Related, in the same scope: the raw
  G-composite spelling
  `Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) (Col.W.α Col.MC.∘ᴹ ((g Col.T.⊗ᵉ f) Col.MC.∘ᴹ Col.W.γ))`
  appears at `QueryBound.agda:490`, `Compose/Step.agda:130,234,241`,
  `Compose/Laws.agda:36` and `Protocol/Machine/Compose.agda:304`, and
  `Collapse.agda:252,260` states it twice more — so `Collapse` is the home for a name.
  Three of those headers price themselves on the literal spelling, so it is a
  re-measure.
- `src/CategoricalCrypto/UC/Model/Bridge.agda:191-192` — the banner "The three
  instruments the seam consumes, over the inherited kernel" overclaims: of the three,
  only `≈ᴳ-at` has a consumer. Rewrite it, or land the `blind-gradeᵁ` restatement
  above and make it true.
- `src/ProbabilisticLogic/Dp/Reasoning.agda :: map-arg` — `map-arg h de = bindˣ de`
  ignores `h` entirely; it exists only so the caller can name the function
  positionally. Rule 18 says cut an eta-wrapper; round 1's refusal of `implicit-drop`
  says the annotation is the reader's orientation. 11 use sites. I lean keep —
  recorded so it is a decision rather than an oversight. Same class:
  `bindᶠ`/`bindˣ` name, by ad-hoc superscript, what `RationalDist/Setoid.agda:31,35`
  calls `>>=ᴹ-congˡ`/`>>=ᴹ-congʳ` — but the sibling's `ˡ`/`ʳ` are *inverted* relative
  to the argument they vary, so aligning would import a confusing convention into
  ~180 call sites. Recorded as a naming inconsistency, not a proposal.
- `src/ProbabilisticLogic/Dp/Mass.agda :: 0≤1-` (with `1-≤`, `shift`) and
  `src/ProbabilisticLogic/Distribution/Uniform.agda :: indᵇ-≤1` — general ℚ facts in
  probability modules, the same class as round 1's open `Protocol/Observe :: ≤-shift`
  entry; `Data/Rational/Properties/Ext.agda` is the home and has no twin of any of
  them. The `≤ 1ℚ` half of the Boolean indicator is written three times
  (`Dp/Mass.agda:126-130`, `Expectation.Pr₁≤1`'s `where b≤1`, `Expectation.Pr₁⊥≤1`'s
  `where bd`) and belongs once beside `bool→ℚ`'s definition.
- `src/ProbabilisticLogic/Distribution/Uniform.agda :: header` — "Uniform sampling on
  bit-strings of fixed length, with the basic probability lemma `P-uniform-Vec`"
  describes about a third of the module: it also carries `δ` and its cons rules,
  `fromℕ` with the full semiring-map family, `inv-pow-2`, `archimedean`, and now
  `indᵇ`. Either one header line or splitting the ℚ-embedding half out (rule 23).
- `src/CategoricalCrypto/Protocol/Machine/Total.agda :: morphismCompose` — the
  inhabitant of `Protocol.Machine.Morphism-∘` lives in a module about total runs only
  because `totalRun-∘` needs it; the functoriality theorem it completes is
  `Protocol.Machine.Compose.morphism-∘`. Moving it (with its polarity comment) under
  Compose's existing `-- Functoriality` banner costs Compose one import and a
  `module 𝒢 =` alias. Related: `Morphism-∘` has no hypothesis-consumer anywhere, so
  either keep it as documentation or fold the statement into `morphismCompose`'s own
  signature and delete the name.
- `src/CategoricalCrypto/Protocol/Safety.agda :: HitCert` — a near-duplicate of
  `GamePlaying.SuperCert` (same eight fields, same statements, `E⊥`/`Dist⊥` for
  `E`/`Dist-ℚ`), and `super` retraces `badProb-super`'s three-case induction. I am
  **not** proposing a merge — the observables genuinely differ and Safety's header
  already names the relationship — but `pres` spells out
  `OnSupport (Reached (λ sr → Inv (proj₁ sr))) (kernel s q)` where
  `GamePlaying.Preserved` names exactly that shape. A `Preserved⊥` next to
  `Reached`/`evalC-support` in `Protocol.Observe` gives the two layers matching
  vocabulary at one line's cost.

- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: lookupAll` — nearly
  `Data.List.Relation.Unary.All.lookup`/`lookupAny`, but Core's membership is
  `Any (_≡ y)` where stdlib's `_∈_` is `Any (y ≡_)`, so the swap needs an `Any.map sym`.
  Judgment call at three lines. Same size class: `⌊≟⌋-refl` is
  `trans (isYes≗does (x ≟ x)) (dec-true (x ≟ x) refl)` from `Relation.Nullary.Decidable`
  — two steps against a three-line `with`.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda` — **13 separate `private`
  blocks in one module**, with three families split across them: the
  `count-matches`/`state-collisions` facts at 645-653, 1493-1504 and 1557-1569;
  `just-inj`/`nothing≢just` at 1063-1067 against their mirror `just≢nothing` at 1136;
  and `labels-++`/`labels-inj` at 1580-1592 against `labels-length` at 1624 with three
  unrelated lemmas in between. Rule 28. Most of these die to the stdlib swaps; group
  whatever survives.
- `src/CategoricalCrypto/Examples/MerkleDamgard/QueryBound.agda :: θ-step` — the four
  clauses share a literally identical eight-line tail with only `z` varying, **and the
  comment at 172-174 forecloses abstracting it**: `θᴰ z` is written in constructor form
  in each clause precisely because "left to a meta, `θᴰ`'s constructor-headed clauses
  invert and strand `resume`'s arguments". Recorded so nobody spends a spike
  rediscovering that; if you want it collapsed the helper has to take the reduced
  `MSt md` value explicitly. Same reason applies to `enter-drive`, `advance-drive`,
  `onEnter-coh` and `onAdvance-coh`, whose RHSs are identical across clauses but whose
  goals only reduce after `bs` is split. Separately: `onEnter i [] e` and the `[]`
  clauses of `onAdvance`/`onEnter-coh` are unreachable (`e : length [] ≡ k` contradicts
  `NonZero k`) yet return a plausible-looking value rather than `⊥-elim`, so the `Φ`
  accounting on that branch is never checked against anything.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda` — three sites spell
  `≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ))) (+-mono-≤ _ _)` inline (`cm-nn`,
  `sc-nn`, `φ-nn`), which is
  `ProbabilisticLogic.Distribution.RationalDist.Support.0≤+`. Round 1's ledger already
  proposes promoting that out of `private`; these are three more consumers for it, and
  Finder A found the same open-coding at `Dp.agda:137`, `Collision.agda:53` and
  `Dp/Embed.agda:90,149`. Worth widening the round-1 entry rather than opening a new
  one.

### Test / pin coverage (rule 33)

- `src/CategoricalCrypto/Protocol/Machine/Pin.agda :: agree-false` — **the round's own
  change left a pin gap.** This delta added the `b : Bool` parameter to `PrAgree`
  (`cum (n + m) … (indᵇ b) ≡ Prᵇ P b d`), and no pin instantiates it at `b = false`:
  the file pins the machine side at `indᵇ false` against *literals*
  (`nay-false ≡ 1ℚ`, `stuck-false ≡ 0ℚ`) and pins the *agreement* only at `bool→ℚ`
  (= `indᵇ true`, definitionally). One `refl` pin closes it, in the shape of the
  existing `agree`:
  `agree-false : cum 8 (runᴹ (morphism flip) echo) (indᵇ false) ≡ Prᵇ flip false echo`
  (optionally `layer₁-false : Prᵇ flip false echo ≡ half`). It is the pin that breaks
  if `Prᵇ`/`indᵇ`'s two readings ever disagree — i.e. exactly what this round
  changed. Everything else added this round is correctly out of `refl` range
  (`morphism-∘` is a machine equality, `hit-bounded`/`super` are `≤`-statements,
  `TotalRun` needs the undischarged liveness, and `PrHit`/`hitFrom` is already pinned
  at both verdicts in `Examples/ChimericLedger/Pin.agda`).
- `src/CategoricalCrypto/Examples/MerkleDamgard/Pin.agda` — **pins the right things**
  (every pin is on a public entry point — `Pr Sys`, `Pr general`, `bound` — which is
  the opposite of the `Protocol.Machine.Pin` problem), and the headline pins are
  non-vacuous: `bound-1 ≡ 0ℚ` with `tight ≡ 0ℚ` is a tightness witness, and
  `real-collides ≡ 3/4` against `ideal-collides ≡ 1/2` exercises the chaining at a
  probability strictly between 0 and 1 — precisely what `ChimericLedger/Pin` lacks.
  The gap: **`indistinguishable` is never applied anywhere in `src/`**, and
  `hash-asks`/`collide-asks` are proved and then unused although they are exactly the
  hypotheses it wants. `indistinguishable false 1 (hash (false ∷ [])) (hash-asks _)`
  in `OneBlock` and `indistinguishable true 2 collide collide-asks` in `TwoBlocks` turn
  the module from "pins the arithmetic the theorem is about" into "pins the theorem",
  and it is the only place a reader would see `asks≤` discharged at a real strategy.
  (At `TwoBlocks` the instance is the vacuous `1/4 ≤ 3`; say so, or pick parameters
  where it bites.)
- `src/CategoricalCrypto/UC/Model/Pin.agda` — every pin here is a typing/elaboration
  pin, disclosed and priced by the header (158.8 s transparent / 12 GiB OOM). Round
  1's standing ask was a *behavioural* `refl` pin in `UC.*` (`⟦_⟧ᴼ`/`wireᴹ`,
  "`refl`-pinnable exactly like `Protocol.Machine.Pin.machine`") and it is still open.
  `relayᵒ` is precisely the process that makes it cheap: a stateless `wireᴹ` relay,
  closed at `unitᴵ`.
- `src/CategoricalCrypto/Protocol/Machine/Pin.agda :: machine`, `agree`, `machine-∘`
  — round 1's rule-33 finding stands: the pins fix `cum` at hand-tuned depths 5/6/8,
  an internal bind-junction count, so the file freezes the internal structure of
  `drive`, `stepᴹ`, `stateᴹ.point`, `runᴹFrom`, `resumeᴹ` and `coinₚ`. The retarget
  needs a new interface (a public "mass from depth `n` on" wrapper in `Dp`, or the
  pins stated as the `Σ[ n ] ∀ m` witness), so it is yours.
- `src/CategoricalCrypto/Examples/ChimericLedger/Pin.agda` — round 1's ask for a
  second instantiation at an injective `ser`, so `POV.AtBirthday` becomes reachable
  and one pin exercises the sampling path at a probability strictly between 0 and 1,
  is still open. This round proved the birthday bound, which makes it more valuable,
  not less.
- Per-layer gaps, still open from round 1: `Dp.Elgot`'s whole law set has no pin;
  `Machines.Base`'s `ℳₚ`/`Tracedₚ`/`𝒢ₚ`/`Remainingₚ`/`Elgotₚ` have none (the
  `𝒢`-composition pin is a measured obstruction — `cum n` expands 2ⁿ branches — but
  nothing pins even `𝒫ᴵ`'s `id`/`∘` behaviourally at a one-ask strategy).

### Companion docs

- The maintainer's own review commit `97063c50` landed while this review ran and
  supersedes a docs audit I had queued (its finder died at the session limit). Its
  findings — `AuditBound` uninhabitably strong, `SaturatedRespects` false as stated
  (with its own "~60-100 LOC of arithmetic" comment refuted, i.e. a confirmed rule-21
  defect), the vanishing-vs-negligible boundary in `UC/Family`, the integration gaps
  — are not duplicated here; two statement-redesign agents own the files. **The one
  thing I could not do and is still owed: a drift pass of `docs/protocol-rewrite.md`
  and `docs/stduc-supersession-plan.md` against the current code.** Concretely
  known-stale from this review: nine modules plus the doc cite
  `docs/kb/frontier/15-probabilistic-uc-model.typ`, which does not exist (no
  `docs/kb/` directory); `docs/protocol-rewrite.md:564` and `UC.agda:47` say
  `BudgetLawsᴹ` is the ceiling of the composition line, which `budgetᴹ` bypassed; and
  `docs/stduc-supersession-plan.md` describes a migration this round performed, so it
  is likely a spent work plan.

## Tried, not worth it

- `src/CategoricalCrypto/UC/Machine.agda :: GradingLawsᴹ` — **retired by the code.**
  Round 1's crux-spike showed `Gradingᴹ` assembles; this round took the other route
  and deleted the cone. `GradingLawsᴹ` has no referent in `src/` (its last occurrence
  was a comment, fixed in `<COMMENTS>`), and the grading is `gradingᴹ = Std.gradingᵗ (𝒢ₚᴹ 0ℓ)`
  on 𝒢's own objects. The spike worktree the entry pointed at is superseded.
- `src/CategoricalCrypto/UC/Base.agda :: Grading` — **closed.** The module is gone
  (`Grading` now lives in `UC.Core`), and the entry's premise — "Nothing in `src/`
  constructs a `Grading 𝒫ᴵ`, so `grade-stable`, `absorbᵘ`, the four `_≤UC_`
  metatheorems and `absorb` are all currently green over [the degenerate] model" — is
  false as of this round: `UC.Machine.gradingᴹ : Grading (𝒢ₚ 0ℓ)` is a non-degenerate
  instance built from the actual monoidal tensor, and `ucBaseᴹ` feeds it to the
  metatheory. The *class* of the finding survives one record along, at
  `UC.Approximate.Approximation` — filed above under *Statement audit*.
- `src/CategoricalCrypto/UC/QueryBound.agda :: BudgetLawsᴹ` (round 1's "declared,
  uninhabited, no `Budgetᴹ` bridge") — **closed, but around the record rather than
  through it:** `UC/QueryBound/Compose/Laws.agda :: budgetLawsᴹ` inhabits it and
  `UC/Machine/Budget.agda :: budgetᴹ : Budget (𝒢ₚ 0ℓ) gradingᴹ (suc 0ℓ)` inhabits
  `Budget` directly, bypassing it. The new fact — the record is now dead and its
  `qb-∘` field got looser — is filed above as a fresh finding, not as this one.
- `src/ProbabilisticLogic/Dp/Advantage.agda :: _≈ₚ[_]_` — **acted on.** The relation
  is two-sided as of `48e92987` (`d ≼ₚ[ ε ] e = (b : Bool) (n : ℕ) → …`) and the
  header now carries the "BOTH verdict masses" paragraph with its citation.
  `UC/Machine.agda:125-132` states the same correctly.
- `src/CategoricalCrypto/UC/QueryBound.agda :: traceᵍ` (round 1: re-exported but
  referenced only inside `module Certificate`) — **resolved:** `Counting.agda` uses it
  at six sites, so the re-export is load-bearing.
- `src/CategoricalCrypto/UC/Emulation.agda :: _⊛₁_` — no longer present in the form
  the entry described; the live dead-name question at this module is `blind-grade`/
  `unit-grade`, filed above.
- `implicit-drop` as a class, and `binder-drop` — round 1's verdicts stand and were
  not re-litigated. `implicit-drop`: 113 oracle-green survivors declined because the
  result leaves signatures half-annotated in a layer where object annotations are the
  reader's only orientation, with no perf argument either way (9 s → 10 s measured).
  `binder-drop`: 0 of 259 candidates survived, i.e. every implicit binder in every
  signature is load-bearing.
- **Section-banner normalization** to rule 25's closed boxed form — round 1's census
  (21 closed, 97 open in the branch; 253 closed, 433 open inherited) still holds and
  the verdict stands: the repo has no single convention, the open form is the majority
  on both sides, and the M1/M2/M3 layers are each internally consistent.
- `src/ProbabilisticLogic/Dp.agda :: node-dirac` → `Data.Rational.Solver.+-*-Solver` —
  round 1's decline stands (LOC-neutral, pulls the Horner normalizer and ℚ's `_≟_`
  into `Dp`'s closure, and there is no reflective ℚ tactic). Widened observation, not
  a reversal: `Dp/Mass.agda` and `Dp/Dominate.agda` already import that solver for
  seven private helpers, one of which (`regroup`) is a solver-proved twin of what
  `6a70b955` installed the stdlib way. The inconsistency is filed under
  *Simplifications*; the solver adoption itself stays declined.
- `src/Categories/GConstructionEmbedding.agda :: ⌜_,_⌝` (with `absorbˡ`, `absorbʳ`,
  `⌜⌝-∘`, `⌜⌝-≅`, `unitorˡᴳ`, `unitorʳᴳ`, `associatorᴳ` and
  `GConstructionEmbeddingCoherence`) — **the question is answered: it is load-bearing
  now.** Round 1 recorded "330 LOC with zero importers … keep as pre-landed
  infrastructure, or park until task 3". The cluster now has two real importers:
  `GConstructionMonoidal.agda:25` consumes `⌜_,_⌝`, `⌜⌝-resp-≈`, `⌜⌝-id`, `⌜⌝-∘`,
  `absorbˡ`, `absorbʳ`, `unitorˡᴳ`, `unitorʳᴳ` and `associatorᴳ` — everything except
  `⌜⌝-≅`, which the three iso definitions use — and `UC/Machine/Wire.agda:23` calls
  `GE.Embed.WithTrace.absorbˡ`/`absorbʳ`. Nothing to park.
- `src/CategoricalCrypto/UC/QueryBound.agda :: qbᵢ-wire` (round 1: "the layer's only
  anti-degeneracy witness") — **superseded by a better one.**
  `Examples/MerkleDamgard/QueryBound.agda :: qbᴹᴰ : QB k (morphism md)` is a second
  witness, at a non-trivial rate `k`, and it is the first `QB` inhabitant built from a
  real protocol rather than from a wire. (`qbᴹᴰ` itself has no consumer and no pin —
  filed under the zero-consumer entry above.)
- `src/Categories/Category/Monoidal/Pure.agda :: PureSub` → upstream `SubCat`;
  `src/Categories/Category/Kleisli/Discrete.agda :: Klᴹ-Symmetric` → upstream
  `Kleisli-Symmetric`; `Machines/Frame.agda :: pad-inv` and `:: swp` → upstream forms
  — all four round-1 declines stand unchanged (the `SubCat` Σ-packing, the measured
  eta-OOM recorded in `Kleisli/Discrete`'s own header, the longer functor plumbing,
  and the `private` block around upstream's `swapʳ`).
- Rule 29 shadowing — re-checked over the 63 files this round adds: no file of the
  same relative path exists in `agda-categories-0.3.0/src` or
  `standard-library-2.3/src`. No violation.
