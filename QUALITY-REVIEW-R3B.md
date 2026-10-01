# Quality review — protocol-rewrite, part R3B: UC model and quantitative layer (2026-10-01)

Scope: the 93 files of `scope-R3B.txt` (12.7k LOC) at base `27cda67f` (`family-makeover`), branch `quality-R3B`.
Never reviewed before this round: `Abstract*`, `Standard*`, `UCSetup*`, `Approx/*`, `UC/{Core,Approximate*,Family*,
Quantitative*,Robust}` (5.2k LOC, integration-owned until now). The rest was re-read for new findings and for the
status of the B-uc/R2a/R2b items.
Method: seven read-only finders, one per cluster. The parent did all edits and checks, one agda run at a time.

Verification: pagda check run yes. Base root (cold, `-M8G -H2G`): rc=0, 380 modules, warn-grep empty. Each
`using-drop` site passed the toolkit oracle on its own file. The tip check covers the root plus the 11 non-root
leaves this scope reaches; results are under *Checks at the tip*.
Soundness baseline (rule 3, whole `src`): 16 before, 16 after. NUL check: byte-level over every committed blob.
Sweep tally (toolkit JSONs in `QUALITY-REVIEW-R3B.d/`): `using-drop` 223 kept / 302 candidates / 77 skipped
(`open … public` and `using () renaming` sites) over 92 files. `StateEvent/Lift.agda` does not parse under the
toolkit grammar and was skipped. `enum-with`: 0 sites. `enum-where`: 125 sites (95 flagged) and `enum-comments`:
549 blocks, both enumerated only; see *Not reached*.

## Checks at the tip (`4e4a47b0` code; `-M8G -H2G`, rc / warn-grep / Checking-count / wall)

| module | result |
|---|---|
| `CategoricalCrypto` (root) | rc=0, warn 0, 92 rechecked, 142 s |
| `Abstract2.{Equivalence,OAPEmulation,WideSubcategory}`, `Standard2.Morphism` | all rc=0, warn 0 |
| `RandomOracle`, `RandomOracle2`, `Examples.RelSetup` | all rc=0, warn 0 |
| `Examples.ChimericLedger.{Transfer,Serialize}`, `Examples.MerkleDamgard.{Pin,QueryBound}` | all rc=0, warn 0 |

Soundness grep: 16 lines before and after, identical as sets. NUL: 0 of 57 new blobs. `git diff --check`: clean.

## Committed (you can skim these)

- `9c28a807` Sweep using-drop: bare opens where no clash. 36 files, +208/−227. Interface-neutral: these are
  non-public opens only. The blank lines the tool left where a multi-line `using` was dropped were removed.
- `4e4a47b0` Comments: stale names, dangling doc paths, leftovers and narration. 16 files, +30/−71, prose only.
  - Names that no longer exist: `ContextDominated`, `UC.Approximate.Induced`, `qb-sub`, `Approx.Forget.F₀`.
  - `docs/kb/frontier/15-…typ` is not in the tree.
  - `LocalTests` claimed verdicts about the model's `_≈ℰᴺ_`, which it never touches.
  - `Schedule` named a nested `pointwise ℕ (pointwise ℕ …)` instance that nothing uses.
  - `UC.Family.Negligible` cited `UC.Family`'s deleted closing comment.
  - `Model.Dominated` had a broken sentence.
  - Other cuts: consumer narration (`Abstract2/Morphism`, `Contextual`), a type-restating comment
    (`Equivalence`), a note-to-self (`EventBounds`), a misleading `wire-pure` gloss (`Dictionary`), and a header
    sentence duplicating its own body (`Controlled`).

Out-of-scope edits: none. Every commit touches only `scope-R3B.txt` files.

## Suggestions (need your call), ranked by LOC saved / complexity removed

Line numbers are at the quality tip unless stated. "Consumers" are `grep -rnF <name> src`, comment-only hits and
the defining line excluded. None of these was applied; the "spike" column says what was typechecked.

### Structural — whole cones with no consumer

1. `src/CategoricalCrypto/UC/Quantitative.agda :: QUCSetup` — **the scalar quantitative arm has no consumer: ≈ −880 LOC,
   −7 modules.**
   - Arm A = `UC/Quantitative{,/Witness,/Bridge,/Observed}` and its three instantiations
     `UC/Family/Quantitative`, `UC/Family/Negligible/Quantitative`, `UC/Model/Quantitative` (880 LOC together).
   - The three instantiations are imported only by the root's build list (`CategoricalCrypto.agda:74,75,81`), and
     none of their results is used anywhere: `≈ᵁ^ω⇔≈ᵁ₊`, `≤UC^ω⇒≤UC₊`, `≤UC₊⇒≤UC^ω`, `setup₊`,
     `uniform-witness⇒≤UCᴺ`, `≤UCˢ⇒≤UCᴺ`, `≈ᵁˢ⇒≈ᵁᴺ`, `QUCᵒ`, `Queryᵒ`, `QSetupᵒ`.
   - Everything downstream uses the OTHER quantitative relation, `UC.Quantitative.Contextual._≈ᵁᵠ[_]_`, through
     `UC.Quantitative.Family` and `UC.Model.Family.Contextual` (six example files). That arm stays.
     (`Contextual`/`Family`/`Query`/`EventLift` are not part of arm A.)
   - Inside arm A, `UC/Quantitative.agda:91-186` (the `ctx-*` kit), half of `Witness` (`Witness⁺`,
     `dummy⇒universal`, `universal⇒dummy`, `at-trans`, `at-compose`), half of `Bridge` and a third of `Observed`
     are dead even relative to the leaves.
   - Follow-on: `Approx/Forget.agda` (57) then has only `Approx/Separating` (an example) as consumer.
   - The maintainer's test: what is arm A needed for? It is the "one QUCSetup" formulation whose single-level reading
     the 2026-09-21 ruling settled (QUALITY-REVIEW.md:3999 — not re-litigated here: this item is about consumers,
     not about merging A into B). Either pin it (a `UC/QuantitativeTests.agda` exercising `≈ᵁ^ω⇔≈ᵁ₊` and
     `uniform-witness⇒≤UCᴺ`, rule 33) or delete it. Unspiked beyond grep (deletion is cross-part: the root is part D).

2. `src/CategoricalCrypto/Abstract.agda` + `Standard.agda` + `Abstract2/OAPEmulation.agda` + `Abstract2/Equivalence.agda`
   — **the object-graded theory is a closed island: −601 LOC, −4 modules** (plus `RandomOracle.agda`, already
   ledgered at QUALITY-REVIEW-A-examples.md:415).
   - Importers: `Abstract` ← `Standard`, `OAPEmulation`, `Equivalence`; `Standard` ← `RandomOracle` (no importer);
     `OAPEmulation`, `Equivalence` ← nothing. None is in the root closure.
   - `OAPEmulation` is three identity adapters (`≤UC≡≤UCᴼ = refl`, `op⇒oap`/`oap⇒op` are `h ↦ h`) plus
     re-proofs of `Abstract`'s `≤UC-refl`/`dummy-complete`/`≤UC-trans` with `ι f` renamed.
   - `Standard` is `Standard2` byte for byte except for which `AbstractUC` it opens.
   - `Equivalence` is the only machine-checked link between object- and morphism-grading; it is the one piece with
     research value (README §2 advertises it). Fallback: keep `Abstract` + `Equivalence`, delete `OAPEmulation`
     (−90) and `Standard` (−33, after RandomOracle).
   - If `Abstract` goes, `Abstract2`/`Standard2` are fossil names; renaming them is a separate step (16 importers).
   - README.md:76 says GradeStable is "equivalently bare kernel = U-kernel"; `Equivalence`'s header and the code
     say "sufficient, not equivalent". The README overclaims (docs are outside this part's scope).

3. `src/CategoricalCrypto/UC/Model/Family/Ingest.agda` (whole module) + `UC/Model/Dominated.agda :: dominatedᵒ`
   — **no consumer: −125 LOC, −1 module.**
   - `conjᶠ`, `_≈advᴹ_`, `ingest`, `ingest-negligible`, `ingest-≈ᵁ`, `ingest-≈ℰⁿ`, `ingest-≤UCᵁ` grep to their own
     file; the module's only importer is the root's build list. `dominatedᵒ`'s only consumer is `ingest`.
   - The ledger item QUALITY-REVIEW.md:3385 ("vacuous gate") is about this module's earlier shape; the code has
     changed since, so this is new.
   - `ingest`'s body is the same shape as `Emulation.≈ctx⇒≈ℰ[]` — two front ends into `_≈ℰ[_]_`.
   - Keep with a test pinning `ingest` (rule 33), or delete.

4. `src/CategoricalCrypto/UC/Machine/EventBounds/Transport.agda` — **a transport package with two live names:
   ≈ −110 LOC.**
   - Live: `bounded-absorb` (`Examples/HashForward/Audit.agda:40`), `transportᵉ` (`StateEvent/HitTests.agda:176`).
   - Zero consumers: `Near`, `Lifts`, `Agrees`, `unlift`, `transport`, `transportᶠ`, `transportᴺ`,
     `readRun-closed`, `closed-bound`, `FlagNear`, `transport-near`, `eventSim⇒near`, `flagged-near`,
     `flagged-transport`, `hitsTransport`, `hitsTransportᴺ`. Several are R2b-ledgered as "keep, add a test"
     (QUALITY-REVIEW-R2b.md:141); `transportᴺ`, `closed-bound`, `readRun-closed` are new.
   - Within the dead part, `hitsTransport`/`hitsTransportᴺ` duplicate `transport`/`transportᴺ` (same
     `upper-dom`/`xy∙z≈xz∙y` plumbing).
   - Option A: delete the dead chain (also drops six imports). Option B (one notion): generalise
     `Lifts`/`Agrees`/`Near` from `τ` to per-process observations so `hitsTransport` is `transport` at
     `flagReader B` (≈ −12). Crux for B: the 8 GiB record gotcha at :74-75 — measure.

5. `src/CategoricalCrypto/Approx/Small/Controlled.agda` (whole) + `Approx/Controlled.agda :: Ctrl, include, F₀ᶜ,
   ≈ᶜ-isEquivalence` — **dead chain: ≈ −110 LOC, −1 module.**
   - `Small.Controlled` is imported only by the root; none of `CollapseControlled`, `SmallPreserving`, `smallSub`,
     `CtrlSmall`, `FSmallᶜ` is used. `Ctrl`'s only consumer is that module; `include`, `F₀ᶜ` have zero uses;
     `≈ᶜ-isEquivalence`'s only consumer is `Ctrl`.
   - `include` is `Nonexpansive` re-spelled as `Controlled` at `idᶜ` (two spellings of one notion).
   - QUALITY-REVIEW.md:3782-3791 moved/inlined these but never ruled on deletion.

6. `src/CategoricalCrypto/UC/Family/Vanishing.agda` and `UC/Family/Negligible/Setup.agda` — **each tier applies
   `Std2.StdUC` twice: ≈ −95 LOC, −2 modules.**
   - `UC.Family` applies `Std2.StdUC Famᴹ ℰ^ω` privately as `Std^ω` (:104); `Family.Vanishing` exists only to apply
     it again publicly as `Canonical^ω` (its whole body, :35). Same for `UC.Family.Negligible`'s private `N` (:89)
     and `Negligible.Setup.Canonicalᴺ`.
   - `Negligible.Setup` holds otherwise only `ucSetupᴺ` (consumer: `shared-computational`), `≈ℰⁿ⇒≤UC` (no
     consumer) and `shared-computational` (`refl , refl , refl`, no consumer).
   - Proposal: make `Std^ω`/`N` public as `Canonical^ω`/`Canonicalᴺ`, delete both modules, retarget
     `Model/Family.agda:23-29`, `Family/Quantitative.agda:35,55`, `Negligible/Quantitative.agda:41,59`.
   - Crux: heap. `Family/Negligible.agda:55` opens `UC.Family` without a `using` list, so a public `Canonical^ω`
     would be copied into it (≈0.7 GB per the Quantitative header). Give it a `using`, measure.
     `Family.agda:114-117` cites `shared-computational` as its measured witness; move the pin to a test.
   - Docs citing `ucSetupᴺ`: `docs/retirement-negligible-order.md`, `docs/coin-toss.md:417`.

7. `src/CategoricalCrypto/UCSetup.agda`, `UCSetup/Morphism.agda`, `Abstract2/Morphism.agda`,
   `Abstract2/WideSubcategory.agda`, `Abstract2.agda` — **dead internals of the setup-morphism layer: ≈ −165 LOC.**
   The layer is your freshly landed API (`3e8aabee`, `0a2e9592`); keep the records, cut what nothing uses:
   - `UCSetup.agda :: faithful⇒grade-stable`, `module GradeStableFromTests` (−26; cited by docs
     `protocol-rewrite.md:746`, `stduc-supersession-plan.md:189`, `rewrite-verdict.md:153`).
   - `UCSetup/Morphism.agda :: idᵁ, composeᵁ`, the identity-law block, `module Factorization` (−60). Statement
     audit: `identityʳ-ν`/`identityˡ-ν` are `ℰ′.refl`, there is no equality on `UCSetupMorphism` and no
     associativity, so the "Identity and composition" banner promises a category that is never built.
   - `Abstract2/Morphism.agda :: transfer-impossible` (dead); `epi⇒preserves-≈ℰ`, `mono⇒reflects-≈ℰ` only rename
     `epi⇒preserves ν`/`mono⇒reflects ν` (rule 18).
   - `Abstract2/WideSubcategory.agda :: W-ext, coarsen, epi⇒coarsens, restrict-dummy (= map₂ restrict-≈ᵁ),
     module Fine, module Trivial` (−36).
   - `Abstract2.agda :: UC-dummy-sim, UCᵈ-sim, ≤UC-resp-≈, ≤UCᵈ⇔≤UC, ≤UC-sub` (−41; `≤UC-sub`'s consumer
     `UC.Factor.liftᵖ` is gone, docs `ledger-lift-eps.md`/`ledger-factoring.md` still cite it).
   - Four copies of the "same setup, new ℰ" record literal (`Abstract2/Morphism :: reobserve`, the codomain of
     `UCSetup/Morphism :: changeKernel`, `Factorization.imageSetup`, `Equivalence.setupᴼ`): one `reobserve` in
     `UCSetup.agda` serves all (≈ −8).
   - `Abstract2/WideSubcategory`, `Standard2/Morphism` have no importer; `Transfer`'s only consumer is
     `WideSubcategory`. If you do not want the API yet, the whole island is a further ≈ −290.

8. `src/CategoricalCrypto/UC/Quantitative/Query.agda :: Qᵠ, 𝒞ᵇ, _≈ᵇ_` (lines 147-206) — **the presheaf packaging has no
   consumer: −42 LOC** (and `Approx/Schedule.agda :: reindex-cong`, whose only consumer is `Qᵠ`, −6).
   - `Contextual` uses `pullᵠ`, `filteredᵠ`, `Budgeted` directly. Keep only if "it IS a presheaf" is to be pinned
     (then add a test).
   - Same file: `absorb-test`/`absorb-closure` (71-82) are consumed only through `proj₁`, once each
     (`Contextual.agda:144,165`); inline the `≤-reflexive (cong ε (scale-comm …))` there (−14).

9. `src/CategoricalCrypto/UC/Core.agda :: Observable` — **a general presheaf record with one producer: ≈ −45.**
   `Evaluation.observable` (:146) is its only producer; the general `P` is never instantiated otherwise. Define
   `Test`, `_≋_`, `pull`, `ℰᴼ` directly in `Evaluation`, delete `Pᴱ`, `transpose`, `observable`, `module Obs`.
   Consumers to retarget: the four `Observable.ℰᴼ (Evaluation.observable X)` sites, `Model/Setup.agda:23`,
   `Quantitative/Observed.agda:67,169`. Also dead here: `Θ` (:45-52) and `≋-cast` (:77-79), −11.

10. `src/CategoricalCrypto/UC/Model/Enrichment.agda :: qbᵘ, procᵘ` → `UC/Model/Graded.agda :: procᵘ-∘, plug-gradedᵒ`
    → `UC/Graded.agda :: plug-graded` — **"adversary fills a grade" chain, each name's only consumer is the next,
    the last has none: −30.** The comment at `Enrichment:58-62` justifies `procᵘ`'s placement by `qbᵘ`'s body,
    and `qbᵘ` has no use.

11. `src/CategoricalCrypto/UC/QueryBound/Counting.agda` — the counting theorem (`qbᵢ⇒count`, `CountBound`, `Budget`)
    has no consumer; only the root imports it. It is what gives `QB` its meaning, so keep — but pin it with a test
    (rule 33) rather than leave it as build closure. Related, still open: QUALITY-REVIEW.md:180.

### Structural — one notion, two spellings

12. `src/CategoricalCrypto/UC/Machine/StateEvent.agda :: _≈ᵉ_, ≈ᵉ⇒≈ᴹ, ▷-≈` + `StateEvent/Read.agda ::
    stateRead-resp-≈ᵉ, stateBounded-resp-≈ᵉ` — an equivalence-closure layer for one single-step consumer
    (`Transport.transportᵉ`, which wraps one `EventSim` back into the closure). Restate `transportᵉ` directly:
    `upper-≈ (readRun-resp-≈ Y (S.≲⇒≈ᴹ (▷-≲ e)) (flagReader B) E m) (h Y E m qE qm le)` and delete the layer
    (≈ −22). `≈ᵉ⇒≈ᴹ` has zero uses. Changes `transportᵉ`'s hypothesis type (the HitTests pin), so: your call.

13. `src/CategoricalCrypto/UC/Quantitative/Family.agda :: ≤UC[]-compose.strict-final`, `UC/Quantitative/Witness.agda ::
    at-compose.strict`, `Abstract2.agda :: UC-compose.strict-final` — the same `sub-commute₂`/assoc/`sub-commute₁`/
    `⟺ sub-homomorphism` chain three times. One `ext-sub-interchange` in `Categories/Monad/Graded/FromMonad.agda`
    (part D's file) ≈ −20. Cross-part.

14. `src/CategoricalCrypto/UCSetup.agda :: prefix` is `ext` by definition (`FromMonad.μT _ = Equiv.refl`). Delete
    `prefix`, use `ext W f` (consumers `UCSetup:127,142`, `UC/Quantitative:166,184`; −3, one name less). Crux:
    perf of the spelling (QUALITY-REVIEW.md:2928 measured spelling costs here).

15. `src/CategoricalCrypto/UC/Machine/StateEvent/Agree.agda :: embeds` vs `UC/Machine/Monitor/Agree.agda ::
    stratTest-embeds` — two wire proofs of the two sides of one embedding. `embeds` follows from
    `stratTest-embeds` plus `λᴵ⇒ ∘ λᴵ⇐ ≈ id`, which does not exist yet in 𝒫ᴵ (one `wire-∘ᴹ` step beside
    `Slide.λ-tri`). ≈ −6.

16. `src/CategoricalCrypto/Approx/Separating.agda :: eventually` is `UC.Family.Approximation^ω` hand-unfolded at
    `ℚ-metric`, `Ix = ℕ`, `κ = id`, and reproves `ℚ-metric`'s laws pointwise. Hoist an `Eventually apx Ix κ` into
    `Approx` with two consumers (`UC.Family`, `Approx.Separating`), ≈ −18. Related placement:
    `UC/Approximate/Separating.agda` (the separating instance `ℚ-metric` + the `inv-suc` counterexample) points the
    wrong way — `Approx.Separating` imports three `UC.Approximate*` modules. Move `ℚ-metric`, `≈ᵐ-0`, `≈ᵐ-gap` into
    `Approx`, `inv-suc`/`¬negligible-inv-suc`/`inv-suc-→0` into `LocalTests` (their only consumer), −1 module.

17. `src/CategoricalCrypto/UC/Machine/Monitor/Agree.agda` — three unrelated things: `stratTest`/`qb-stratTest`/`m₀`
    (strategy-as-test; belongs beside `strategyEnv`/`qb-strategyEnv`), `module Read` (the `flagReadᴹ ∘ subᴵ E`
    collapse; belongs beside `flagReader` in `Monitor`, and its name collides with `StateEvent.Read`), and
    `flag-agree` (the only monitor agreement; sole consumer `UC/Quantitative/EventLift`). 0 LOC, placement.
    Supersedes R2a #17 (which pointed at `Seam/Budget`). `m₀ = λᴵ⇐` is an alias used 8 times (rule 18).

18. `src/CategoricalCrypto/UC/Seam/Audit/Context.agda` — a fossil directory (`UC.Audit`/`UC.Seam.Audit` are deleted)
    holding four definitions with one consumer (`Model/Family/Emulation.agda:29`). Fold them into Emulation next
    to `≈ᶠ-runs`, with `auditClose` replaced by `Gr.ιᴳ unitᴵ` (closes the open B-uc item "auditClose is ιᴳ unitᴵ"),
    ≈ −10, −1 module, −1 directory. Fallback: rename to `UC/Seam/Context.agda`.

### Statement audit

19. `src/CategoricalCrypto/UC/Machine/StateEvent/HitTests.agda :: wait-irrelevant` — **vacuous for its stated
    purpose.** At `out false` there is no activation, so no `wait` state is ever reached; `0` follows from
    `onWait (idle false) = false` alone, and the test would still pass if wait states were sampled. Restate at an
    input that reaches a wait state (`ask₁`, `onWait (wait _) = true`, `Bad = λ _ → false`, expected `0ℚ`).
    Adding the stronger test is a commit I did not land (it needs the restated term to reduce; unspiked).

20. `src/CategoricalCrypto/UC/Robust/Model.agda :: relay-selectedᵒ` — honest but degenerate: it is `uc-preserves-at`
    at `f := sub s ∘ g`, `u := ≈ᵁ-refl`, i.e. `robust-sub`; no non-trivial emulation is exercised and the
    `Robust … (relayᵒ 𝔄)` premise is discharged nowhere. The comment "the acceptance test the top class cannot
    give" oversells it; add "at the trivial agreement".

21. `src/CategoricalCrypto/UC/Quantitative/Observed.agda :: absorbᵘ`, `UC/Quantitative/Bridge.agda` — `induces`/
    `reflects` are applied twice in `src`, both as `λ h → h`; every `*-agreement` in Bridge is `KE.run∼`/`KE.mk∼`
    and every `*-emulation` is `≤UC⇒dummy`/`dummy-complete` around them. Moot under Suggestion 1.
    (The B-uc note on pinning `_∼_ = _∼ᵃ_` — QUALITY-REVIEW-B-uc.md:273 — no longer applies: the Negligible
    instance now uses a different `_∼_`.)

### Dead public definitions (rule 32: each is your call)

`grep -rnF` over `src`, comment-only hits and the definition excluded, finds only the definition:

| Definition | LOC |
|---|---|
| `UC/Family.agda :: ≈ℰⁿ-refl, ≈ℰⁿ-sym, ≈ℰⁿ-trans, ≈ℰⁿ⇒≈ᵁ` | 19 |
| `UC/Family.agda :: ≈^ω-witness` — its only use of `κ-cofinal`; the parameter then threads six module headers for nothing (option: delete it, ≈ −15 over 7 files; or keep as a guard against vacuous instantiation) | 2 (+15) |
| `UC/QueryBound/Exact.agda :: qeᵢ-wire` (its "QEᵢ is not vacuous" role is superseded by HashForward/ROCommitment inhabiting `QEᵢ`) | 15 |
| `UC/Family/Quantitative.agda :: ≈ᵁ^ω⇒≈ᵁ₊, ≈ᵁ₊⇒≈ᵁ^ω, ≤UC^ω⇒≤UC₊, ≤UC₊⇒≤UC^ω` (eta-wrappers of `R₊`/`R^ω`; keep the `≤UC` pair if the `⇔` bundling cost at :101-102 still holds) | 15 |
| `Approx/Schedule.agda :: reindex-∘` (a `refl`), `pointwise-refinement` | 14 |
| `UC/Approximate/Local.agda :: ∼ᴺ≡∼Small` (a `refl` pin that `∼ᴺ-isEquivalence` already relies on), `∼ᴺ⇒pointwise` (a projection; cited in two comments) | 13 |
| `UC/QueryBound/Compose/Laws.agda :: qb-∘` — only consumer is `qb-∘-category`, whose body goes raw≈∘ᴳ, ⟺, raw≈∘ᴳ; the ledger kept it (QUALITY-REVIEW.md:1189) for `budgetᴹ`, which no longer exists | 12 |
| `UC/Machine.agda :: Evaluationᴹ, QEvaluationᴹ` (the seal-side `qevaluationᵒ` is what the model is fed; root header comment says otherwise) | 12 |
| `UC/Robust.agda :: ⊤ᴬ, Respects≈Env, factors-resp` (QUALITY-REVIEW.md:2451's `⊤ᴬ` level note predates the loss of its consumer `uc-preservesᵒ`) | 8 |
| `UC/Machine/EventBounds.agda :: boundedᴺ-reindex` | 7 |
| `Approx/Forget.agda :: forget` (the advertised natural transformation; nothing uses it) | 6 |
| `UC/Approximate/Separating.agda :: inv-suc-→0` (move to a test rather than delete) | 10 |
| `Approx/Error.agda :: ℕ-unrefinable` (a negative sanity result; move to a test) | 4 |
| `UC/Model/Observation.agda :: ∼ᴼ-resp` (+ its private `module Ap`) | 3 |
| `Approx/Evaluation.agda :: qual` | 2 |
| `Approx/Filtered.agda :: ≈ᵃ-sym` (part of the equivalence kit; flag only) | 2 |
| `UC/Quantitative.agda :: ctx-sym` | 2 |
| `Abstract.agda :: Iᵤ, car, grd, U-≋, atk-idˡ` | 15 |
| ledger-carried, still dead: `StateEvent :: unflag, unflag-▷, dropF` (R2b), `Read :: stateRead-resp-env` (R2b), `Adequacy :: stateᶠ⇒boundedHit` (R2b), `Object :: Certifiedᴳ, certified⇒QBᴳ` (QUALITY-REVIEW.md:449), `Step :: Bd` (QUALITY-REVIEW.md:985), `Seal :: ⊗ᵒ` (QUALITY-REVIEW.md:445) | — |

### Small (public names, cross-part, or perf-pinned)

- `src/CategoricalCrypto/Approx/Error.agda :: halving` — single use (`ℚ-refinement`); inline (−8). Public, so yours.
- `src/CategoricalCrypto/Approx/Filtered.agda :: Allowance` — single-use public alias of `PosetHomomorphism I I` (−3).
- `src/CategoricalCrypto/Approx/Space.agda`, `Controlled.agda`, `Filtered.agda` — `≈[]-mono ⊕-identityˡ (≈[]-trans h k)`
  (zero-error transitivity) is written six times; one `≈[]-trans₀` in `ApproxSpace` (adds a public name).
- `src/CategoricalCrypto/Approx/Controlled.agda :: Control.preserves-⊕` — spent only to close `_∘ᶜ_` under itself
  (`docs/history/controls-allowances-inventory.md`: "never used by any consumer"). Dropping a law from a structure
  is a design decision.
- `src/CategoricalCrypto/Approx/Small.agda :: Collapse` re-exports `SmallClass S` publicly; its only external use
  is `UC/Quantitative/Bridge.agda:126` (`using (Small)`).
- `src/CategoricalCrypto/UC/Approximate.agda :: →0-cong, →0-0` are general `_→0` facts; they belong beside
  `→0-≤` in `ProbabilisticLogic/Distribution/Uniform/Decay.agda` (part D). `UC/Approximate/Decay.agda ::
  0<inv-pow-2` belongs beside `0≤inv-pow-2` in `Uniform.agda:151`.
- `src/CategoricalCrypto/UC/Machine/EventBounds.agda :: Saturated, saturated-map` — move beside
  `UC.Approximate.GradedBound` (ledger R2b:89; the note-to-self in the comment was cut in this round).
- `src/CategoricalCrypto/UC/Robust.agda:23 :: open AbstractUC setup public` — its only importer
  (`Robust/Model.agda:17`) takes only `UC.Robust`'s own names; drop the `public` (rule 19; a re-export, so yours).
- `src/CategoricalCrypto/UC/Quantitative.agda :: run-resp-≈` and `≈C⇒ctx` are one lemma (moot under Suggestion 1).
- `src/CategoricalCrypto/UC/Quantitative/EventLift.agda :: agree` — public, single use (`hits⇒upper`).
- `src/CategoricalCrypto/UC/Machine/Bridge.agda:10-31` — explains `dominated`'s statement, which lives in
  `Machine/Dominated.agda`; move it there (rule 24), Bridge's header then fits 25 lines.
- `src/CategoricalCrypto/UC/Machine/Slide.agda`, `Wire.agda` — `Sum.map (λ a → a) f` is `Sum.map₂ f` (≈25 sites,
  in public statements of `wire-∘ᴹ`/`∘-wireᴹ`/`T₁-wire`/`sub-wire`; measure first).
- `Rates`: `module Rates = SymmetricMonoidalCategory Rates` is repeated in 11 files; one exported bundle name in
  `Categories/Category/Instance/Rates.agda` (part D).
- `src/CategoricalCrypto/UC/QueryBound/Exact.agda :: Ledgerᴿ` — its four law parameters are
  `IsPreorder _≡_ _∼_` + `_+_ Preserves₂ _∼_ ⟶ _∼_ ⟶ _∼_` (rule 30, ±0).
- `src/CategoricalCrypto/Abstract2.agda :: naiveKleisli` — only consumer is the orphan `Equivalence`; move it there.
- `src/CategoricalCrypto/Abstract2.agda :: _≈ᵁ_` could be stated with `ext`/`prefix` (follows 14; perf crux).

## Tried, not worth it

- `src/CategoricalCrypto/UC/Quantitative/Family.agda :: ∼-isEquivalence/∼-from-zero/reflects` (QUALITY-REVIEW-B-uc.md:273,
  "fix `_∼_ = _∼ᵃ_`") — retired: the parameters now live in `Observed`, and `Family/Negligible/Quantitative` instantiates
  `_∼_` at `N.∼ᴺ-isEquivalence`, so pinning it would break that instance.
- `src/CategoricalCrypto/UC/Quantitative/Observed.agda :: two imports of Approx.Error` — not a duplicate: opening
  `module AllPositive` would clash with Observed's own `module AllPositive`.

## Not reached (deadline 15:57 CEST)

Commit candidates the finders verified by reading, not applied for lack of time. Each needs one green check of its
module and importers:
- `UC/Quantitative/Query.agda :: private module S = Controlledᴹ Sched` is dead (no `S.` use); drop it and the
  `Approx.Controlled` import.
- `UC/Quantitative/Observed.agda` unused `Func` import. `UC/Quantitative/EventLift.agda` unused `Data.Product.Base`
  and `Data.Unit.Base`. `UC/Seam.agda` unused `Data.Empty`, `tt`, `Protocol.Machine`. `UC/Seam/Adequacy.agda`
  dead private `module Sm` with its `Machines.Sim` import, and `Data.Bool.Base`. `UC/Seam/Grounded.agda`
  `Data.Bool.Base`. `UC/Model/Dominated.agda` `Data.Empty`, `Data.Sum.Base`, `Function.Base`, `certified⇒QB`,
  `qbᵢ-wire`. Agda does not warn on unused imports, so these need a check.
- `UC/QueryBound.agda :: 0<⊔1` — private and single-use; it is `m≤n⊔m c 1`.
- `UC/QueryBound/Compose.agda :: slack, reassoc` — private; they are stdlib
  `Algebra.Properties.CommutativeSemigroup.x∙yz≈xz∙y`/`xy∙z≈xz∙y`. `reassoc`'s last two arguments are swapped
  relative to the stdlib lemma (rule 30).
- `UC/Approximate.agda :: →0-+` — a verbatim duplicate of `ProbabilisticLogic.Distribution.Uniform.Decay.→0-+`.
  Keep the export with `open import …Uniform.Decay using (→0-+) public`, so `ChimericLedger/Transfer` needs no
  edit.
- `UC/Machine/Slide.agda :: qb-Kctx` — two round trips: `qb-resp-≈ (⟺ᴹ a⇒-α⇒) (qb-a⇒ᴳ …)` is `qb-wire ⊎assocʳ
  ⊎assocˡ`, and `qb-resp-≈ (⟺ᴹ sub-⊗₁) (qb-subᴳ …)` is `qb-subᴵ …`. After that, `qb-a⇒ᴳ` inlines into
  `qb-a⇒ᴳ-object`. Perf-pinned module, so measure warm before and after.
- `Abstract2.agda :: λ-cancel` is `MR.cancelˡ` (−6). `unit-comp` reuses `GradedKleisli`'s `μ-ret` shape (−10).
  `≤UC⇒dummy`'s type should be spelled `f ≤UC g → f ≤UCᵈ g` (definitionally equal). `UC-compose` re-binds
  block variables `f`, `g` (rule 16). Seven importers need rechecking.
- `UC/Quantitative.agda :: ctx-pre` binds `P`, `C′` unused. `≈C⇒ctx` eta-reduces.
- `UC/Robust.agda` variable block `W X X′ Y` → `X Y`; possibly unused `Function.Properties.Equivalence` import.
- `UC/Machine/{Dictionary,Grading,Slide}.agda` — duplicate `Data.Sum.Base` imports merge into one line each.
- `Abstract.agda` doubled blank lines. `UCSetup.agda` import order (`Function.Bundles`) and three banners
  missing their closing rule.
- Comment trims the finders proposed but I did not re-verify:
  - `Exact` header (31 lines, repeats `Counting`'s);
  - `Quantitative` header 11-17, `Witness` header, `Family/Quantitative` 13-15, `Neg/Quantitative` 17-19
    (duplicate);
  - `Neg/Setup` 6-15 and 65-70;
  - `Model/Observation` 5-13, `Core` 43-44, `Query` 152-153, `Observed` 155-158, `Bridge` 44-45;
  - `Grounded` 63-68, `Contextual` header 15-19;
  - `Bridge.agda:10-31` (move to `Machine/Dominated`'s header);
  - `Machine/Dominated` 88-89 (duplicate of 214-216);
  - `Controlled` header 12-14, `Error` header 18-19, `Filtered` header 13-17, `Separating` header 10-11.

Sweep classes and dispositions:
- **`implicit-drop`, `binder-drop`, `join-lines`: not run** (92 files). Measured cost this round: one class over
  the scope took ≈ 75 min of serialized checks (`using-drop`: 92 files, 302 candidates).
- **`enum-where`: 125 sites, 95 flagged `singleUseCandidate`, none dispositioned.** Run `where_inline.py --apply`
  per flagged site.
- **`enum-comments`: 549 blocks, not dispositioned per block.** The finders gave per-block verdicts for the ≥3-line
  blocks; the cuts that landed are in `4e4a47b0`, and the rest are listed above.
- `StateEvent/Lift.agda` needs a by-hand sweep (parse error).

Not done at all:
- No spike behind any suggestion beyond `grep`.
- No second-opinion verification on proof-swap candidates.
- No perf measurement.

## Out-of-scope observations (files of other parts; not edited)

- Eight examples (`Examples/{ROCommitment/UC, ROCommitment/Hiding/UC, ROCommitment/Realization/Assembly, CoinToss/UC,
  CoinToss/Ideal/Compose, CoinToss/Hiding/UC, CoinToss/Ideal/UC, CoinToss/Ideal/Receiver/UC}.agda`) import
  `UC.Model.Dominated` and use no name from it (part A).
- Root `CategoricalCrypto.agda:11-12` says the UC modules are fed `UC.Machine.Evaluationᴹ`; they are fed
  `qevaluationᵒ` (part D; see dead `Evaluationᴹ` above).
- `docs/uc-module-inventory.md:57` cites the deleted `UC.Machine.Bridge.ContextDominated`; README.md:76 overclaims
  GradeStable as an equivalence.
