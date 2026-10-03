# Quality review — protocol-rewrite.next5, part B (2026-10-03)

Scope: the 66 files of `scope-R4B.txt` (UC model, quantitative layer, `Approx`), base `aae4d19e`,
branch `quality-R4B`. Lenses of `brief-common-r4.md` 1–6; no sweep toolkit (another agent).
Verification: pagda root check `src/CategoricalCrypto.agda` (`-M8G -H2G`) green with an empty warning
grep after every batch and at the tip; the three non-root leaves the scope reaches
(`Examples.ChimericLedger.{Serialize,Transfer}`, `Examples.MerkleDamgard.QueryBound`) green at the tip;
escape-hatch grep over `src` unchanged (16 hits, all prose, identical set); byte-level NUL check over all 53
added/modified blobs clean; `git diff --check aae4d19e HEAD` clean.

## Committed (you can skim these)

- `8b0dfafc` `UC.Machine.Dominated :: dominated`, `UC.Model.Dominated :: dominatedᵍᵠ, dominatedᵍ` —
  **statement strengthened**: `skeleton` already proves `≈ₚ[ ε ]`; the `(δ : ℚ) → 0ℚ < δ` slack only
  weakened it to `ε + δ`. Now `… (ε : ℚ) → … → … ≈ₚ[ ε ] …`. One out-of-scope call site
  (`Examples/CoinToss/Ideal/Receiver/Compose :: coin-ctxʰ`) widens with `≈ₚ[]-mono (<⇒≤ (0<inv-pow-2 n))`,
  its statement unchanged. Docs that called the slack forced (`coin-toss.md` §5/§6, `fcom-uc.md`,
  `rcom-icom-b1.md`, `open-items.md`) resynced. −30 net.
- `f6017e50` `UC.Machine :: spaceᴹ, Approximationᴹ` → inlined in `UC.Model.Observation.qevaluationᵒ`, their
  one consumer; `UC.Machine` (56 importers) loses its `Approx.*`, `Dp.Advantage`, `UC.Core`, `Machines.Core`
  imports. −14.
- `d8880ea5` zero-consumer deletions: `UC.Core :: ≋-isEquivalence`, `UC.Model.Seal :: ifaceᵒ-onto`,
  `UC.Machine.StateEvent :: eventSim-refl, eventSim-trans`, `StateEvent.Read :: asks≤-flag`,
  `UC.Family.Negligible :: ≈ℰⁿ⇒≤UC`, `UC.Family :: absorb-negl` with `UC.Approximate :: NegligibleBound⇒VanishingBound`,
  `Approx.Small :: smallSetoid, ∼Small-refl, FSmall`, `UC.Model.Setup`'s `≈ᵒ⇒≋` re-export;
  `UC.Seam.Grounded :: factorᵒ` inlined into `factorᵖ`. −80.
- `7a8df402` leftover imports/aliases from the moves (`Monitor.Agree`'s `Core`/`Sim` opens, `StateEvent.Agree`'s
  `Wiring` import, `Seam.Adequacy`'s `Dictionary` import, `Enrichment`'s unused bundle alias). −14.
- `a6002976` `UC.Robust.Model :: relay-selectedᵒ` now goes through `uc-preserves` (+ `dummy-complete`), so the
  module's headline `≤UC` entry point is pinned (rule 33); statement unchanged. −2.
- `a38594e2` docs/headers resynced to the moves: `UC.Core :: Evaluation` (Observable is gone),
  `Composite`'s `Unfold.Walk`, the third readable-composite route in `hash-forward.md`, `stratTest`'s home,
  deleted `Qᵠ` / `Negligible.Setup`, "filtered space" (no presheaf), stale `Bridge` and `UC.Core` headers.
- `18b27a84` `UC.Quantitative.{Query.Tests,Contextual,Family}` take ONE `QEvaluation` instead of its four
  fields as five parameters (one notion, as `UC.Family` already does); `Model.Family.Contextual` passes
  `qevaluationᵒ`. −13.
- `0916962b` `ctx-absorb`'s local `cut` → agda-categories `MR.pushʳ` (rule 30); `Negligible⇒→0` via `→0-cong`;
  `Query :: Budgeted` (single use) inlined into `pullᵠ`. −14.
- `8ce1da3f` `Approx.Schedule` header overclaimed that the composition theorems' substitutions are compositions
  of controlled maps (they are `pullᵠ`'s allowance map; the control is `reindex (_· r)`); design narration
  cut in `Controlled`, `Family.Negligible`, `Model.Dominated`.
- `8f33269d` `UC.QueryBound.Exact :: fromAbove` → `Counting`, its only consumer; mislabelled one-definition banner gone.
- `e9f0f6b1` **`Approx.Filtered :: Filt`** (with `_≈ᶠ_`, `identityᶠ`, `composeᶠ`, `composeᶠ-resp`) and
  `Approx.Controlled :: _∘ᶜ_, _≐_, _≐ᶜ_, ≐-reflexive, _≈ᶜ_, identityᶜ, composeᶜ, composeᶜ-resp` deleted: no
  consumer but `FilteredTests`, which pinned only the category. `FilteredTests` keeps `Runs`, `along`,
  `admitted-doubled` (re-proved directly) and `ℕ-unrefinable`. Note: `simplification-options.md` §2.1 (shelved)
  would need `Filt` back. −145.
- `4e095711` **`Approx.Space :: Nonexpansive, _≈map_, identity, compose, compose-resp, Approx, F₀`** and the whole
  `Approx.Forget` (`F₊`) deleted: no consumer; `Approx.Separating` used only the setoids the functors send a space
  to. **Statement respelling (same proposition up to δ):**
  `F₊-identifies : Setoid._≈_ ⟦ Sequences ⟧₊ inv-pow-2 zeroᶠ` → `positive-identifies : inv-pow-2 ∼ᵃ zeroᶠ`;
  `F₀-separates : ¬ Setoid._≈_ ⟦ Sequences ⟧₀ inv-pow-2 zeroᶠ` → `zero-separates : ¬ Setoid._≈_ (zeroSetoid Sequences) inv-pow-2 zeroᶠ`. −120.
- `2d65d736` `UC.QueryBound.Compose.Step` deleted; `Compose.Laws :: qb-∘-category` proved directly through
  `Composite.eq-∘ᶜ` (statement byte-identical), `qb-∘` gone (closes the open item). Warm Laws 7.50 → 7.56 s. −49.
- `66c1bb63` `UC.Machine.Composite` reads the solved loop off `Machines.Collapse.Loop`: `Pt, pt-*, step-in,
  solve-outᶜ, solve-loopᶜ` (a re-derivation from `Trace`) deleted, `solve-out` definitional. Public names keep
  their types. Warm 8.21 → 8.1 s. −47.
- `238f42fa` `UC.Seam.Adequacy.Wiring` deleted: one generic `kᶜ`/`k-red`/`traced≈` in `UC.Machine.Plug.Plugged`
  serves `Seam.Adequacy` and `StateEvent.Agree` (which carried a private copy). `step-run` now states
  `runᴹFrom tracedᴹ …` instead of the deleted, definitionally equal `pairedᴹ B d u`. No module got slower. −78.
- `ea44ffb0` boundaries: the flag reader (`FlagSt`, `flagReadᴹ`, `flagReader`, the collapse module, renamed
  `Read` → `Collapsed` so it no longer shadows its host) moves from `Monitor` to `StateEvent.Read`, the generic
  reading that imported the specific monitor only for it; `Monitor.Agree`'s one result `flag-agree` folds into
  `Monitor`. Docs resynced. −30.
- `8c67bdf9` `docs/uc-module-inventory.md` LOC / importer counts recounted (53 modules, 7497 LOC).
- `4d1d05ee` `UC.Machine.Transfer :: uFwd, uFwdL` drop an argument `n : Neg B` they only threaded to each other
  (their mirrors `uBwd`/`uBwdL` never had it); internal helpers.
- `689a90e4` `StateEvent.Read :: Collapsed.readᴹ` is `mk Sᴿ readStep` (it re-spelled the private `Sᴿ`). −3.
- `a3f4cae9` `UC.Machine.Slide :: unit-cancel` — **statement generalised**: old
  `unit-cancel : (x : Proc unitᴵ B) → 𝒫._≈_ {unitᴵ} {B} (λᴵ⇒ 𝒫.∘ conjᴵ x) x`, new
  `unit-cancel : (x : Proc A B) → 𝒫._≈_ {A} {B} (λᴵ⇒ 𝒫.∘ (λᴵ⇐ 𝒫.∘ x)) x` (the proof never used `A = unitᴵ`).
- `715b175e` `StateEvent.Agree :: embeds` is now `stratTest-embeds` composed with `λᴵ⇐` and cancelled by
  `unit-cancel 𝒫.id` — the second wire proof of one embedding is gone; closes that open item (its crux,
  `λᴵ⇒ ∘ λᴵ⇐ ≈ id`, is the generalised `unit-cancel`). −6.
- `48de82aa` `Approx.Error :: positiveSetoid` deleted (its one consumer was `Approx.Forget.F₊`). −3.

## Suggestions (need your call)

Ranked by complexity removed.

### Public API / module layout

6. `src/CategoricalCrypto/UC/Seam/Grounded.agda` — the module is about the seal's trivial grade, not the seam
   (`UC.Model.TrivialGrade`?).

### Simplifications not committed (judgment needed)

12. `src/CategoricalCrypto/UC/Machine/Grading.agda :: qb-T₁ᴳ, qb-subᴳ` (single use each, −6, but the header's opaque/perf split needs a
   measurement); `UC/Machine/Dominated.agda :: Sm` is `Machines.Pointwise.S` under another name (−2);
   `Dominated :: Decompose` (private, one use) could be `skeleton`'s `where` (−3).
13. `src/CategoricalCrypto/UC/Model/Family/Emulation.agda :: ≈ctx⇒≈ℰ[], ≤UC[]⇒≈ℰⁿ` — single-use chain into
   `≤UC[]⇒≤UCᴺ` (−6), but `quantitative-family.md` §5 presents them as API.
14. `src/CategoricalCrypto/UC/Approximate/Local.agda :: _∼ᴺ_` — the header says it IS `_∼Small_ familySpace`;
   define it so (0 LOC, one spelling). `zeroᶠ` is defined identically in `Approx/Separating` and
   `UC/Approximate/LocalTests`. `Local :: ∼ᴺ-gap` and `Approx.Error :: ℕ-ordered` are consumed only by tests.
15. `src/CategoricalCrypto/UC/Quantitative/Family.agda` applies `Families Rg ℕ (λ n → n) …` a second time beside
   `UC.Family`'s application; both meet in the examples (the two-spellings risk `Query`'s header warns about).
   Green today; first suspect if those examples slow down.

## Tried, not worth it

- `src/CategoricalCrypto/UC/QueryBound.agda :: qbᵢ-closed, qbᵢ-id` — inlining into `qb-closed`/`qb-idᴹ` saves 2–3
  lines each and breaks the `qbᵢ-*`/`qb-*` presentation/closure pairing every other law has; kept.
- `src/CategoricalCrypto/UC/Machine/Composite.agda :: Sg, Sf, stepg, stepf, Sᶜ, bodyStep, eqᶜ` — zero external
  consumers, but they are the module's working vocabulary (≈ 20 internal uses); inlining is noise, privatising is
  rule 32. Kept.
- `src/CategoricalCrypto/UC/Machine/Monitor/Agree.agda :: flag-agree` vs `StateEvent/Agree.agda :: stateRead-agree`
  — checked as a possible two-spellings pair: different statements, composed in `EventLift.agree`.
- `src/CategoricalCrypto/UC/Model/Setup.agda`, `UC/Model/Family.agda` — instantiation layers (they apply a
  parameterised module), not forwarding layers.
- `src/CategoricalCrypto/Approx/Filtered.agda :: ≈ᵃ-sym` — zero consumers, but it is the symmetry law of a
  relation whose `refl`/`trans`/`mono`/`resp₀` laws are all consumed; kept as that relation's API.
- `src/CategoricalCrypto/UC/Machine/StateEvent/Lift.agda :: read-≈` — single use, but named as the `Refine`
  argument it feeds; inlining saves 3 lines of a 390-line module. Kept.
- `src/CategoricalCrypto/Approx/Controlled.agda` header "everything is stated with `⊑`" and `Approx/Error.agda`'s
  "NOT an ordered monoid" — genuine whys (they keep an upper-bound model admissible); kept.

## Not reached

- Suggestions were not spiked unless stated; the vanishing-tier crux (respelling `_≈ℰ[_]_` off
  `Canonical^ω`) in particular is unmeasured.
