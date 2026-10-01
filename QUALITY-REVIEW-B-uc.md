# Quality review — protocol-rewrite, part B-uc (2026-09-29)

Scope: the 52 files of `scope-B-uc.txt` at `c71d95fe` (`UC.agda`, `UC/{Factor,Graded}`,
`UC/Machine{,/*}`, `UC/Model{,/*}`, `UC/Quantitative/EventLift{,/Cov}`,
`UC/QueryBound{,/*}`, `UC/Robust/Model`, `UC/Seam{,/*}`; 8.6k LOC). Branch
`quality-B-uc` in `.claude/worktrees/quality-B-uc`. The emphasis was complexity:
adapters that are `refl`, Seam lemmas the generic layer already states, QueryBound
families vs the `GradedSubCat` laws, and duplicated observation notions.

Verification: every commit was checked green before it landed: rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing` grep, on the
`UC` closure (47–50 modules rebuilt), `UC.Model` and `UC.Robust.Model`. At the tip:
- The root `CategoricalCrypto` is green.
- So are the five modules that reach this scope from outside the root closure: `ChimericLedger.{Serialize,Transfer,Property,ReplayFamily}` and `MerkleDamgard.QueryBound`.
- NUL is byte-level clean over all 62 changed blobs, and `git diff --check` is clean. Soundness baseline:
whole-`src` grep, 16 lines before and 16 after. Nothing in scope carries a hatch.

Sweep tally (the JSONs are committed under `.claude/sweeps-tally/B-uc-*`):

| class | result |
|---|---|
| `using-drop` | batch 1 (`…-1.json`) + batch 2 (`…-2.json`): 452 of 485 candidates kept over 52 files. Batch 1 aborted 41 files on a 3 GiB heap; batch 2 re-ran them at 8 GiB. |
| `enum-with` | 0 sites |
| `enum-comments` | 438 blocks, every one dispositioned. `B-uc-comment-dispositions-{model,machine,querybound,seam}.json` hold 245 edits and 451 dispositions, 643 comment lines net. |
| `enum-where` | 126 sites, 88 flagged single-use. All flagged sites were spiked with `where_inline.py --apply` (`B-uc-where-inline.json`): 13 inlined, 18 red, 20 declined on width, 94 skipped-shape (multi-use). The 38 unflagged sites are multi-use by the enumerator's own count. |
| `implicit-drop` | **unfinished**, see *Suggestions → Work items* |
| `binder-drop`, `join-lines` | **not run**, see *Suggestions → Work items* |

## Committed (you can skim these)

- `e73ca6f0`, `cf255f15` — bare `open` where a `using` list resolved no clash (rule 11),
  52 files, −42 LOC net. Each file passed the sweep oracle alone, and the closure was
  rebuilt green. `open … public` and `using () renaming` sites were left alone, as the
  toolkit requires.
- `1622abec`, `b49238b6`, `0fc5ae60`, `4437fe00` — comment pass (rules 21–26), four
  clusters, −643 comment lines. Code is untouched. Accuracy fixes that ride along:
  - `UC.agda` claimed no `UC.Model` name is re-exported (two are).
  - A `docs/kb/frontier/15-…typ` path that does not exist.
  - `Model.Enrichment`'s "`p = p`" claim (it is a `subst` along `sealᵒ`).
  - `graded-∘ᵒ`'s named consumer, which does not use it.
  - `Model.Dominated`'s stale "approximate AND graded has nothing to read" (`dominatedᵍ` is exactly that).
  - Grading named the wrong consumers of `qb-T₁ᴵ`/`qb-subᴵ`.
  - Monitor said semantic agreement is unproved (`Monitor.Agree.agree` proves it).
  - `emulAgreeᵁ`'s "the one the family premise consumes" (no consumer).
  - Step's reference to the deleted `Collapse.Congruence`.
  - Three pointers to "`UC.Machine`'s header" for an inversion note that sits at `𝒫ᴵ` and says 10 GiB, not 1 GiB.
  - The "+1 unit for the accumulator" explanation, written five times, is now once at `Cov.covCtx`.
- `0bca1c61` — explicit implicits dropped at use sites where inference recovers them
  (`UC.Graded`, `UC.Machine`), plus two binders that became unused. The sweep's
  Grading/Dictionary survivors were deliberately not taken (see *Tried*).
- `27e6ed54` — `UC.Machine`: two private module aliases (`𝒢`, `𝒫`) with zero uses.
- `e37c4aa5` — `UC.Model.Dominated.qEᶜ` now goes through `qb-T₁ᴵ`, which the inlined
  term was verbatim. Same statement; Cov already spells it this way.
- `613a73a1` — `UC.Seam.Budget`: its private `_⟨≈⟩_`/`bindˣ`/`bindᶠ` were
  character-for-character `Dp.Reasoning`'s, so it now imports those (−13).
- `3fae6e42` — `EventLift.Cov.swap₃` is stdlib `xy∙z≈xz∙y` (rule 30).
- `e772846a` — `UC.Robust.Model.relayᵒ`: its `where down` case split is `[ id , ⊥-elim ]`.
- `458a67e4` — single-use `where` bindings inlined, one spike per flagged site with
  `where_inline.py --apply`. 13 sites were inlined green; 18 went red; 20 were declined
  because they would exceed the line width; 94 were skipped-shape, because the tool
  counted more than one use, so the enumerator's flag was a false positive. Two `where`
  blocks that the inlining left empty were removed.

Out-of-scope edits: none.

## Suggestions (need your call)

Ranked by LOC removed and complexity retired. Line numbers are at the quality tip.

### Structural

1. `src/CategoricalCrypto/UC/Seam/Grounded.agda :: emulAgreeᵁ` — **the trivial-grade
   collapse cone has no consumer: about −750 LOC across six modules.**
   - `emulAgreeᵁ` is used nowhere; `grep -rnF` finds only its own two lines. Its
     consumer was the family premise of the old `EndToEnd`, which the ledger redesign
     retired. The ledger's *Resolved (family-premise)* entry records that consumer,
     and it no longer exists.
   - Everything that exists only to prove it:
     - `Grounded`'s `Proc≈`/`toProc≈`/`fromProc≈`, `module TrivialGrade` (with `SimTotal`, `SubBlind`), `TG`, `≈ᵁ-at`, `emSimTotal`, `subBlind⇒emul`, `simTotal⇒point`, `subPrefixed{ˢ,}`, `subBlind` (about 190 LOC).
     - All of `UC/Seam/Grounding.agda` (237; sole importer is Grounded).
     - `UC/Machine/Run/Lax.agda` (79; sole importer is Grounding).
     - `Machines/Sim/Lax.agda` (189) and `Machines/G/Lax.agda` (70), whose importers are only Grounding, Run/Lax and each other.
     - `Dp.Mass.{astotal-bind, astotal-≼ᵐ, total-dominated}`.
   - What stays in Grounded: `𝟘ᴳ`, `ιᴳ`, `closedᵒ`, `stageᵒ`, `plug-λ`, `plug-run`,
     which is about 60 LOC; it could then fold into `UC.Seam`.
   - Taking this also dissolves the open ledger items on `Run`/`Run.Lax` duplication
     and `Grounding` dead scaffolding.
   - Against it: rule 32. `emulAgreeᵁ` is a real theorem (removing the simulator at the
     trivial grade), and `Sim.Lax` is general machine material. If you keep it, keep it
     for that reason, and add a test that pins `emulAgreeᵁ` (rule 33).
   - The `Machines/*` files belong to part C, so coordinate.
   - Unspiked: deletion gates are `grep`, which is done; the build of the remainder is
     not yet checked.

2. `src/CategoricalCrypto/UC/QueryBound/Counting.agda :: module Refined` vs
   `src/CategoricalCrypto/UC/QueryBound/Exact.agda :: module Ledger` — **one potential
   construction written twice, over `≤` and over `≡`. About −100..−140.**
   - `Ans Φ X Y r` is `Σ` of a step with `downward + Φ ≤ r`. `QEᵢ` is the same with `≡`
     (Exact's header calls it "`QBᵢ`'s twin"). `CountedRun.bound` is `Balanced` with `≤`.
   - `Ledger.chain` uses only reflexivity, transitivity and `+`-monotonicity of the
     relation.
   - Plan: parameterise `Ledger` by `_∼_ ∈ {≤, ≡}` with those three laws. `Counting`
     becomes an adapter to `QBᵢ`, which deletes `Refined` (lines 82–197) and its
     private helper block. `#inj₁`/`#inj₂` then fold into `weight downward`/`weight
     fromAbove`, which are one notion spelled two ways today.
   - Changes `Ledger`'s parameters. Its two consumers are `HashForward/UC.agda:130` and
     `ROCommitment/UC.agda:163`.
   - Crux to spike: whether `Counting`'s ≤-form still elaborates in the measured time
     once it goes through a relation parameter.

3. `src/CategoricalCrypto/Iface.agda :: unitᴵ` vs
   `src/CategoricalCrypto/UC/Machine/Dictionary.agda :: 𝟭ᴵ` — **two empty interfaces.**
   - `⊥ ⇿ ⊥` and `retᴵ 𝔾.unit` are the same object spelled with two empty types.
   - That forces two families of unitor wires: at `unitᴵ`, `Bridge.λᴵ⇐/λᴵ⇒` and
     `Slide.ρᴵ⇒`; at `𝟭ᴵ`, `Dictionary.λᴵ` plus three raw wires.
   - It also forces the whole "hole wire" apparatus: `Slide.λ-nat/λ-tri/ρ-tri/λ-slide`,
     `natᴳ`/`slideᴳ`. With one unit these are unitor naturality and the triangle,
     reachable through the existing zigzags.
   - Estimate −80..−120 LOC.
   - `Grounded`'s header prices only the *iso* between the two units (over the perf bar),
     not re-spelling the unit. Crux spike: redefine `unitᴵ = 𝟭ᴵ` and measure the
     absurd-pattern fallout (`Data.Empty.Polymorphic.⊥` is a `Lift`, so `()` becomes
     `lift ()` in about 55 files) and the cost of `Slide`/`Monitor.Slide`.
   - Multi-session and cross-part (Iface is part C/D).

4. Fossil hypothesis types, each a named `Set₁` with exactly one inhabitant, proved
   through a wrapper that takes the proof as an argument. **About −35 LOC.**
   - `src/CategoricalCrypto/UC/Machine/Bridge.agda :: ContextDominated`, with
     `UC/Machine/Dominated.agda :: Skeleton`, `skeleton⇒dominated` and `EventSkeleton`.
     Put the Π-type directly on `dominated`/`eventSkeleton`. Bridge then keeps
     `λᴵ⇐/λᴵ⇒/conjᴵ/ctxRun` only and drops about 7 imports.
   - `src/CategoricalCrypto/UC/Seam.agda :: Adequacy`. Its only code use is
     `adequacy : Adequacy`; type `adequacy` directly.
   - These are public names, so this is your call.

5. `src/CategoricalCrypto/UC.agda`, and `UC/Model.agda`'s import list — **a re-export
   layer with no downstream opener.**
   - The only in-repo importer of `CategoricalCrypto.UC` is the root
     (`CategoricalCrypto.agda:70`), and nothing reads a name through it. All 17 `public`
     opens and `open Compose public` are therefore API surface only.
   - Either drop the `public`s, or (rule 19) fold both import lists into the root, which
     is already the closure module: −90 LOC and two fewer modules.
   - This is the downstream-facing entry point, so rule 32 applies: your call.

6. `src/CategoricalCrypto/UC/Seam/EventTransfer.agda :: Watched` vs
   `src/CategoricalCrypto/UC/Seam/Transfer.agda :: loopFwd…uFwdL` — **the same forward
   induction, clause for clause.**
   - EventTransfer 134–223 differs only in the target (`w acc (…)`), `resumeᵂ` for
     `resume`, the `w-ask`/`w-coin` rewrites, and the verdict leaf.
   - Transfer is not literally the identity-watch instance, because `IsWatch` forces
     `w acc (out v) ≡ out acc`.
   - A shared induction parameterised by a transformer family and a leaf obligation
     should work. About −70; unspiked.
   - While there, take `(iw : IsWatch report w)` instead of the unpacked triple. The
     triple is also unpacked by hand in `Machine/Dominated :: EventSkeleton` and
     `EventLift:130`.

7. `src/CategoricalCrypto/UC/Seam/Grounded.agda :: plug-run` re-derives
   `UC/Seam/Plug.agda :: Plugged.collapse`. The ledger already has this and it is still
   open; `Monitor/Agree.agda:562` already relies on the definitional identity. There are
   now four spellings of "observe env ∘ u": `⟦_⟧ᴼ`, `ctxRunˢ`, `Obs`, `Bridge.ctxRun`.
   Stating `adequacy` as `⟦ strategyEnv B d ∘ u ⟧ᴼ ≈ₚ runᴹ u d` would retire `plugˢ`,
   `ctxRunˢ` and `runˢ`. The last of these is `runᴹ` with its arguments flipped (rule 18).

8. `src/CategoricalCrypto/UC/QueryBound.agda :: qb-T₁ᴹ`, `qb-subᴹ` — **dead, and strictly
   subsumed by `Grading.qb-T₁ᴵ`/`qb-subᴵ`.**
   - Same conclusion, and the `resp` hypothesis is literally
     `Dictionary.T₁-resp-≈`/`sub-resp-≈`.
   - The ledger's *Resolved* note kept them as "general public theorems" on 2026-09-11.
     `qb-T₁ᴵ` arrived later (`4032e95e`, 2026-09-22), so that decision predates the
     subsuming lemma.
   - Proposal: `qb-T₁ᴵ Y A B f (N , c , e) = T₁ᴵ Y N , qbᵢ-T₁ … , T₁-resp-≈ e`,
     `qb-T₁ᴳ` via `T₁-⊗₁`, and delete the `ᴹ` pair. The current `qb-T₁ᴵ` takes a round
     trip through `⊗₁`. About −20.

9. `src/CategoricalCrypto/UC/Model/EventBounds.agda` — **misplaced.** It imports nothing
   from the seal and is pure machine layer (`Proc`, `ctxRun`, `QB`), and
   `UC.Machine.Monitor` imports it. Move it to `UC/Machine/EventBounds.agda`: 0 LOC, and
   the layering becomes true. Also in this file, `ctxRun-∘` has zero code uses.

10. `src/CategoricalCrypto/UC/Model/Quantitative.agda` — **the whole module has zero
    consumers.** `Qᵒ`, `QSetupᵒ`, `QUCᵒ` and `Queryᵒ` grep to their own lines only;
    its sole importer is `UC/Model.agda`'s closure list. Either keep it as the
    existence proof of the instance, with a test pinning it (rule 33), or delete it
    (−41).
    - Related: `Model/Family/Negligible.agda` applies the identical six-argument list
      as `Model/Family.agda`. Merge the two (about −20; check use-site ambiguity first).

### Dead public definitions (rule 32: each is your call; `grep -rnF` over `src`, comments excluded, finds only the definition)

`UC/Model/Observation :: ≈ₚ⇒∼ᴼ` (then `<⇒≤` and `≈ₚ[]-mono` become unused) ·
`UC/Model/EventBounds :: ctxRun-∘` · `UC/Model/Graded :: graded-∘ᵒ` ·
`UC/Model/Seal :: ifaceᵒ-onto` · `UC/Machine/Monitor :: qbᵢ-monitor` (34 LOC) and the
`refl` pins `monitor-query/answer/flag` (move them to a test module or delete) ·
`UC/Seam/Adequacy :: adequacyᵍ` · `UC/Seam/Audit/Context :: absorb-plugᵍ` ·
`UC/Seam/EventTransfer :: cov-true`/`covL-true` · `UC/Seam/Grounding ::
prefixedᵒ-scalar`, `massedᵒ-resp-≈` · `UC/Graded :: sub-graded` (an alias; `emulᵍ`
calls `sub-gradedᵒ` directly) · `UC/QueryBound/Counting :: counting` (an alias of
`qbᵢ⇒count`; the type alias `QueryBound.Counting` also has no consumer).
Together about −130 LOC.

### Small unifications (judgment because public or cross-module)

- `src/CategoricalCrypto/UC/Machine/Bridge.agda :: λᴵ⇒` — its certificate
  `certified⇒QB (qbᵢ-wire [ ⊥-elim , id ] inj₂)` is built at EventLift:181, Cov and
  Model.Dominated. Name it `qb-λᴵ⇒`.
  - More generally, `certified⇒QB (qbᵢ-wire …)` occurs 11 times, so a `qb-wire` lemma
    beside `qbᵢ-wire` would serve them all.
- `src/CategoricalCrypto/UC/Machine.agda :: a⇒ᴵ` — the name is inverted against
  agda-categories: it is `associator.to`, which is α⇐. As a result, `gradingᴹ` reads
  `pred-α⇒ = qb-a⇐ᴳ-object`. The rename touches 13 files (rule 20).
- `src/CategoricalCrypto/UC/Machine.agda :: subᴵ′` — the ledger already has this and it
  is still open. It is `subᴵ` with its implicits reordered, and is now used at 7 files.
- `src/CategoricalCrypto/UC/Machine/Monitor.agda :: readerᴹ` — only permutes
  `compileᴹ`'s arguments, so give `compileᴹ` the `Reader` order instead.
- `src/CategoricalCrypto/UC/Seam/Budget.agda :: fgt`, `pad`/`padᵈ` — `fgt` is
  `Data.Product.map₁ forgetᶜ`, and `pad`/`padᵈ` are one lemma at two `Z`s. About −5.
- `src/CategoricalCrypto/UC/Seam/Audit/Context.agda :: auditClose` is literally
  `ιᴳ unitᴵ`. `src/CategoricalCrypto/UC/Seam/Grounded.agda :: closedᵒ` is `stageᵒ` at
  `A = unitᴵ`, so it could be defined that way (one notion).
- `src/CategoricalCrypto/UC/Machine/Dictionary.agda :: T₁-resp-≈`, `sub-resp-≈`, `T₁-∘`,
  `sub-∘` — one lemma four times: a family `h` with `h f ≈ F₁ f` inherits
  `F-resp-≈`/`homomorphism` from `F`. A generic lemma in `Categories/…/Ext` plus four
  one-liners would save about −18. This area is perf-pinned, so measure first.
- `src/CategoricalCrypto/UC/Machine/Grading.agda` — the ledger's `-object` where-block
  entry is still open and was not reopened. The `ᴳ` lemmas `qb-a⇒ᴳ`, `qb-λ⇒ᴳ` and
  `qb-ρ⇒ᴳ` exist only to feed their `-object` wrappers.
- `src/CategoricalCrypto/UC/Model/Family/Ingest.agda :: ifaceᶠ` — two importers take
  Ingest only for this one-liner. Move it to `Model/Family.agda`.
- `src/CategoricalCrypto/UC/Model/Dominated.agda :: qb-gradedᵒ` — belongs beside
  `qbᵒ`/`qbᵘ` in `Model.Enrichment`; three examples import Dominated only for it.

### Work items (unfinished sweep classes)

- `implicit-drop` — about 5 of 52 files were processed in 2 h 40 min on a contended gate
  (roughly 30 min per file) before I stopped it.
  - Of what it produced, `Graded`/`Machine` were committed. `Dictionary`/`Grading` were
    declined (see *Tried*), and the in-flight `Monitor/Agree` trial was reverted.
  - Remaining: 47 files. They are the files whose headers document pinned implicits as
    a measured perf device (`QueryBound`, `Compose/*`, `Slide`, `Agree`, `Seam/*`), so
    each survivor needs a warm before/after timing as well as a green check.
- `binder-drop` and `join-lines` — not run. Remaining: all 52 files. Budget per file is
  about the same as `implicit-drop`.

## Tried, not worth it

- `src/CategoricalCrypto/UC/QueryBound.agda :: QB` family as projections of
  `UC/Machine/Grading.agda :: gradingᴹ` — no. `QB` is rated in ℕ including 0
  (`qb-closed : QB 0 M`, 15 uses); `Rates` is ℕ⁺; and `gradingᴹ` is built *from* the
  family, not the other way. Only the round trips (Suggestions 8 and 12) are
  redundancy.
- `src/CategoricalCrypto/UC/Machine/Grading.agda`,
  `src/CategoricalCrypto/UC/Machine/Dictionary.agda` :: implicit-drop survivors — green
  under the sweep, but declined. They strip exactly the object pins the headers record
  as the measured fix (for example `𝔾._⊗₁_ {⟦ Y ⟧ᴵ} …`), and several left a
  signature's objects fixed only by unification with the body. Without a warm timing
  the change is not shown to be free.
- `src/CategoricalCrypto/UC/Model/Dominated.agda` vs
  `src/CategoricalCrypto/UC/Machine/Dominated.agda` — no duplication: the Model file is
  `dominated` read through the seal coercions.
- `src/CategoricalCrypto/UC/Model/Observation.agda :: Obs` vs `UC/Seam/*` — no second
  reading notion; Seam imports `Obs`/`obs-resp`/`∼ᴼ-resp` from Observation.
  (The *four spellings* in Suggestion 7 are all on the Seam/machine side.)
- `src/CategoricalCrypto/UC/Model/Graded.agda` ↔ `src/CategoricalCrypto/UC/Graded.agda`
  double naming — forced by the 12 GiB `unfolding`-with-`StdUC` configuration
  (Model.Enrichment's header). Only the dead alias `sub-graded` is excess.
- The seal adapters (`procᵒ`, `unprocᵒ`, `gradedᵒ`, `graded₂ᵒ`, `procᵘ`, `qbᵒ`, …) — all
  `f = f` by design, one per shape, and each is used except those listed under
  *Dead*. Collapsing them is the documented seal discipline, not an adapter to remove.

## Integration-owned files (noted, not edited)

- `UC/Quantitative/Family.agda` — the parameters `∼-isEquivalence`, `∼-from-zero` and
  `reflects` are instantiated once in `src` (`Model/Family/Contextual`, at `qual₊`'s
  values and `λ h → h`). Fixing `_∼_ = ApproxSpace._∼ᵃ_ X` deletes three parameters.
- `Categories/LocallyGraded/SubCategory.agda` — `pred⇒image : Pred r f → Image forget r f`
  and `⌊⌋-image h = h , refl` would replace `Model.Enrichment.imageᵒ` and seven or more
  hand spellings (`Family/Emulation:112`, `Ingest:97`, `UC/Family:199`,
  `UC/Quantitative/Family:271,386`, `UC/Audit:232`, `Seam/Audit/Context` qbᴱ/qbʷ).
- `UC/Audit.agda :: carry-obs`, `UC/Robust/Observation.agda :: robust-resp-≈ᵁ` and
  `Seam/Grounded :: ≈ᵁ-at` — the same `≈ᵁ`-read-at-one-context cast, three times. One
  `≈ᵁ-observe` beside `_≈ᵁ_` would serve all three; it is moot for Grounded if
  Suggestion 1 is taken.
