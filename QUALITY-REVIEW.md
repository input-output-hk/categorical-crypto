# Quality review — protocol-rewrite (2026-09-04)

Scope: the branch delta against its merge-base `f71a2381` — 65 `.agda` files
(~9 000 LOC) plus `docs/protocol-rewrite.md`. Inherited modules outside that
delta were read for context and never edited.

**Base reviewed: `f096c5d5` ("Record the theory review and its resolutions").**
The branch moved twice while the review ran: six commits (`dbea8ba8..f096c5d5`,
an external theory review and its four fixes) landed mid-pass and this review
was re-based onto them and the affected files re-swept; four more
(`7dcce03b..b775802a`, a second theory review, `UC.Audit` and `UC.Seam.Audit`)
landed after the final verification, so **the nine files below were reviewed at
`f096c5d5` and not at the current tip**, and two of them did not exist here at
all:

    UC.agda  UC/Base.agda  UC/Bridge.agda  UC/Emulation.agda  UC/Family.agda
    UC/Seam.agda  UC/Seam/Grounding.agda      (+ new: UC/Audit, UC/Seam/Audit)

A rebase onto `b775802a` conflicts on `UC/Bridge` and `UC/Family` (both were
`using`-swept here and rewritten there); it is left undone deliberately rather
than resolved against a tip that keeps moving.

Verification: yes. Every commit checked green *before* landing, under each
file's own OPTIONS, with
`pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`; green means rc=0
**and** an empty
`grep -nE 'ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve'`
(the extended gate — pagda prints `error: [UnsolvedConstraints]` at rc=0).
Closure check (`CategoricalCrypto`, `UC`, `UC.Family`, `UC.Seam.Carry`,
`UC.Seam.Grounding`, both `Pin`s, `GConstructionEmbedding` — the leaf set, which
covers all 65 transitively): green.

Soundness baseline: whole-`src` hatch grep **21 lines before, 21 after**
(18 `postulate`, 4 `{!`, every one in inherited `Categories/APROP/**`,
`Distribution/Binomial/PMF`, `Machine/Core`, `Examples/Basic`); **zero hatches
anywhere in the diff scope**, before and after. `--without-K` discipline: all
64 branch-authored modules carry `--safe --without-K`; the one in-scope file
without it — `Channel/Category.agda`, `--safe
--no-require-unique-meta-solutions` — already lacked it at `f71a2381`, so
nothing in the diff drops it. 20 modules add `--guardedness` and nothing adds
anything else. Both `refl` pins recompute, and three more were added.

Sweep tally — `.claude/sweeps-tally/protocol-rewrite/*.json`, all seven classes
over all 65 files (the `latetip-*` files are the re-run over the nine modules
the mid-pass commits moved):

| class | candidates | kept green | skipped | committed | checks |
|---|---|---|---|---|---|
| `using-drop` | 395 (+60 late-tip) | 343 (+56) | 53 `open … public` | all | 406 (+39) |
| `join-lines` | 38 (+2) | 35 (+2) | 0 | all | 58 (+6) |
| `implicit-drop` | 591 | 113 | 0 | **0 — declined, see *Tried*** | 413 |
| `binder-drop` | 259 | **0** | 0 | 0 | 39 |
| `enum-with` | 1 site | — | — | 1 (edited) | — |
| `enum-where` | 146 sites | — | — | 2 (edited), 144 declined per site | — |
| `enum-comments` | 384 blocks | 0 flagged | — | 13 blocks cut/rewritten | — |

`binder-drop` keeping **0 of 259** is worth its own line: every implicit binder
in every signature of the branch is load-bearing.  `enum-comments` flagging
**0 of 384** blocks is the other one: no `singleDefBanner`, `leftoverMarker`,
`typeEcho`, `headerOverTier` or per-clause gloss anywhere in the branch.  The 13
blocks changed were found by the three checks the flags cannot see — header
*content* (rule 23's narration clause), accuracy against the code, and
consolidation across sites.

Per-file warm cost: all 65 within house rule 5's `60 s + LOC/4` budget; the two
slowest single-module warm checks are `UC/Machine.agda` and `UC/Seam.agda`, and
`UC/Seam` needs `-M8G` (its header says why), which is why the sweep's default
3 GiB reported it red — a sweep-configuration artefact, not a defect.

## Committed (you can skim these)

- `088331c9` **Drop the non-clashing `using` lists** — rule 11, over 58 files;
  343 of 395 candidates, each kept only while its module stayed green under the
  extended gate. `open … public` sites and `using () renaming (…)` untouched.
- `9ce6e2bb` **Put what fits on one line on one line** — rule 14, 35 joins, none
  exceeding its own file's existing width; plus the `using`-drops for the six
  modules the first sweep could not reach.
- `6a70b955` **Take the two-term rearrangements from the stdlib, and dedup the
  zero node** — rule 30: `Dp.Commutative.exch`/`scalar` are
  `Algebra.Properties.CommutativeSemigroup`'s `interchange`/`x∙yz≈y∙xz` at ℚ
  (the pair `Distribution.Linearity` already spends); `Dp.uniformize`'s
  `subst`-plus-`⊔-comm` is `Data.Nat.Properties.m≤n⊔m`, which also retires
  `⊔ℕ-comm`, `subst` and an unused `m≤m+n` from the imports. Rules 27/28:
  `node-0` was character-identical to `Dp`'s `private node-zero`, and
  `cum-cong-P` moved to `Dp` beside `cum-mono-P`, letting `Dp.Elgot` and
  `Dp.Iter.Out` drop their whole dependency on `Dp.Commutative`.
- `dc3fb268` **Put the imports back in order, and take the two upstream
  projections** — rule 10 at nine sites; rule 30 for `Frame.𝕄` (=
  `SymmetricMonoidalCategory.monoidalCategory`, and the reflection frontends
  still accept it) and `Cocartesian.Ext.+₁-id` (= the `-+-` bifunctor's own
  `identity`).
- `fd814f00` **Trim the comments that narrate the superseded design, and fix the
  stale ones** — rules 21/22/24/25. Two accuracy fixes worth naming:
  `Trace.Remaining`'s "the four laws left for wave 2 … a consumer takes the
  record as a module parameter" was stale twice over (all four are theorems, and
  nothing takes `Remaining` as a parameter), and `Prelude`'s "curated to what
  consumers reference" is refuted by its own list.
- `fa6d94bc` **Say the ledger's Maybe dispatches with `case_of_`, and inline the
  projection** — rule 12 at `checkIns`, `applyTx` and `oracle`; rule 18 for
  `ledgerOf = proj₁`; rule 24 for the audit-form sentence, which was said three
  times.
- `faa2ffb9` **Inline the two single-use bindings that only restated a callee's
  own type** — `≤UC⁺⇒≤UC`'s `with`/`... |` becomes a one-line `let`, and
  `iter-uniform`'s `tr` goes inline. The other 13 of that shape are declined by
  spike, not analogy.
- `bc28e3c3` **Pin the composite agreement, the stabilization, and the
  divergence branch** — three `refl` pins `Protocol.Machine.Pin` was missing:
  `agree₊₁`/`agree₊₂` (so `agree` is evidence for `PrAgree`'s `∀ m`, not a point
  sample), `agree-∘` (the composite half, and the one pin that breaks if
  `_∘ᵖ_`'s `graft`/`serve` and `𝒢`'s trace-composition disagree), and
  `layer₁-dead`/`machine-dead` for the `dead`/`botₚ` branch the module header
  spends its longest sentence on and nothing computed.

## Suggestions (need your call)

### Statement audit

- `src/CategoricalCrypto/UC/Machine.agda :: GradingLawsᴹ` — **the assembly is
  not blocked; I have it green.** The comment above `UCBaseᴹ` says
  `Gradingᴹ : GradingLawsᴹ → Grading 𝒫ᴵ` "does NOT assemble" (a `GradedKleisli`
  eta cliff). Crux-spiked to a GO and re-verified independently: `Gradingᴹ`
  typechecks rc=0, warn-clean, in an 84 s warm check of a 265-LOC
  `UC/Machine.agda` (budget 126 s), hatch grep 21 → 21, no `opaque`, no OPTIONS
  change, both `refl` pins still computing. The cure is *not* `opaque`: a
  `--show-implicit` token diff of the two types shows they differ in exactly one
  position — the record literal's expected type carries `⟦ Y ⊗ᴵ A ⟧ᴵ` folded
  while `GradingLawsᴹ.T₁-∘`'s stored type carries it unfolded to
  `⟦ (Pos Y ⊎ Pos A) ⇿ (Neg Y ⊎ Neg A) ⟧ᴵ`, because Agda solved
  `𝒫._≈_`/`𝒫._∘_`'s object implicits by inverting `Proc` and the solution came
  back normalized. Reconciling folded against unfolded *inside that carrier* is
  the heap. So the medicine is perf-finding #1's own — pin every object implicit
  — applied to `GradingLawsᴹ`'s eight statements and to the use site (both
  halves are needed; either alone still exhausts 6 GiB), plus a `subᴵ′` that
  reorders `sub`'s ancilla implicit to `Grading`'s order. Exactly four of the
  eight laws blow up — `T₁-∘`, `sub-∘`, `a-isoˡ`, `a-nat`, the `∘`-bearing ones
  — and the five data fields never did. **Bonus, also verified:**
  `Budget 𝒫ᴵ (Gradingᴹ L) (suc 0ℓ)` assembles in 9 s by the same recipe with
  `BudgetLawsᴹ`'s statements unchanged, so the whole `UCBase`+`Budget` bridge to
  the intended model is reachable; the one real blocker there is that
  `qb-a⇒`/`qb-a⇐`'s witness `qbᵢ-wire` needs `⊎assocˡ`/`⊎assocʳ`, which are
  `private` in `UC.Machine` — a scope fix, not a proof. Kept, unlanded, in
  `.claude/worktrees/agent-a344d6941d0872d63` (branch
  `worktree-agent-a344d6941d0872d63`, based at `ebb3f2a5`; `UC/Machine.agda`
  modified, `UC/BSpike.agda` new — the latter takes `qb-a⇒`/`qb-a⇐` as
  hypotheses to isolate the conversion question from the privacy one, so it is
  evidence, not a landable module). Not committed here because it changes eight
  statements' spelling and adds two public names, and because the pinning is
  load-bearing: a later rule-15 pass must not re-hide those implicits, so it
  needs the comment or an equivalent. Doc consequence: the price-table row
  "`Grading 𝒫ᴵ` (via `GradingLawsᴹ`'s eight fields)" becomes accurate as
  written, and the second bullet of "Two perf findings" needs rewriting.
- `src/CategoricalCrypto/UC/Base.agda :: Grading` — **the priced obligation that
  is not like the others.** `Grading 𝒫ᴵ` has a degenerate model: take
  `_⊛_ = λ _ _ → unitᴵ` and every one of `T₁ Y f`, `sub s`, `a⇒`, `a⇐` to be
  `𝒫.id {unitᴵ}`. Then `T₁-resp-≈`/`sub-resp-≈` and `T₁-id`/`sub-id` are
  `refl`, `T₁-∘`/`sub-∘` are `⟺ identityˡ`, `a-isoˡ` is `identityˡ`, `a-nat` is
  `refl` — all ten fields discharged. Under it `tv₁ Y f E = E ∘ id` is
  independent of `f`, so `_≈ℰ_` relates every pair of homs and `_≤UC_` holds of
  everything at `s = id`. Nothing in `src/` constructs a `Grading 𝒫ᴵ`, so
  `grade-stable`, `absorbᵘ`, the four `_≤UC_` metatheorems and `absorb` are all
  currently green over that model with nothing ruling it out. This is not
  unsoundness — the theorems do follow from the ten laws, which is the point of
  an abstract layer — but it is the same *class* of defect as the four the
  external theory review fixed (the bounded `κ`, in particular), and the doc
  prices `Grading 𝒫ᴵ` as one owed statement among six rather than as the single
  node whose absence leaves all of M3's proved content uninstantiated. With the
  spike above it stops being a suggestion and becomes a task.
- `src/CategoricalCrypto/UC/QueryBound.agda :: BudgetLawsᴹ` — declared,
  uninhabited, **single occurrence in `src/`**: no consumer, and no
  `Budgetᴹ : (G : Grading 𝒫ᴵ) → BudgetLawsᴹ → Budget 𝒫ᴵ G _`. So `QBᵢ`'s
  genuine content — the amortised potential, the one thing that forbids
  `QB c f = ⊤` — never reaches `Budget.QB` today. The spike above shows the
  bridge is reachable, modulo the `⊎assocˡ`/`⊎assocʳ` privacy fix.
- `src/ProbabilisticLogic/Dp/Advantage.agda :: _≈ₚ[_]_` — the relation compares
  only `Pr≤ n d = cum n d bool→ℚ`, so a run that outputs `false` and a run that
  diverges are at distance 0. That is deliberate and consistent with
  `RationalDist.Advantage`, whose header states it ("a diverging experiment
  moves the advantage the same way a `false` one does") — but *this* module is
  the one `Observationᴹ` uses, and it does not. One line, since a UC statement's
  meaning turns on it.
- `src/CategoricalCrypto/Protocol/Observe.agda :: Bounded` — the second
  parameter is named `bad` but is a strategy *transformer* `Strat → Strat` (the
  ledger's instance is `watch`), while `BoundedHit`'s `Bad` really is a state
  predicate. Two different things one letter apart; `watch`/`observe` would say
  which. Renaming touches `POV.POVaudit`, `Observe.transfer`, `UC.Seam`.
- `src/CategoricalCrypto/Protocol/Observe.agda :: ≤-shift` — `x ≤ a → |y − x| ≤ b
  → y ≤ a + b` is a general ℚ fact sitting `private` in a protocol-observation
  module. Rule 27 puts it in `Data.Rational.Properties.Ext`, which this file
  already imports — but that file is inherited and outside the diff, so it is
  yours rather than mine.

### Public API / module layout

- `src/CategoricalCrypto.agda :: (unchanged by this branch)` — the branch adds
  64 modules and wires **none** into the library index; the only in-scope module
  reachable from it is the inherited repair `Channel.Category`, and the
  transitive closure of the index is 58 of 308 modules. `pagda.nix` sets
  `entryModule = "CategoricalCrypto"` for the docs backend, so all 64 —
  including every module the doc calls an entry point
  (`ProbabilisticLogic.Prelude`, `CategoricalCrypto.Protocol`,
  `Protocol.Observe`, `Machines.Base`, `Dp.Elgot`, `CategoricalCrypto.UC`) — are
  typechecked by CI but absent from the published documentation. 250 of 308
  modules are already outside the index, so this is not a regression; but "one
  designed entry point per layer" and "invisible in the docs" sit badly
  together. Cheapest fix: list the five entry points in the index, not `public`,
  the way `Examples.*` already is.
- `src/Categories/GConstructionEmbedding.agda :: ⌜_,_⌝` (with `absorbˡ`,
  `absorbʳ`, `⌜⌝-∘`, `⌜⌝-≅`, `unitorˡᴳ`, `unitorʳᴳ`, `associatorᴳ`, and all of
  `GConstructionEmbeddingCoherence`) — **330 LOC with zero importers anywhere in
  `src/` or `spikes/`**, and they pull `Categories.APROP`,
  `…Hypergraph.Solver.Frontend` and `…Solver.Split` into the build closure.
  `Machines.G` builds `Mealy-G` from `Categories.GConstruction` directly. The
  doc lists them as harvested groundwork for the open task 3, which is a good
  reason to keep them — so this is your call, not a cleanup: keep as pre-landed
  infrastructure (worth a header line, since nothing in the tree points at
  them), or park them until task 3 starts.
- `src/CategoricalCrypto/UC/Family.agda :: open E public using (…)` — 22 of the
  27 re-exported names have no consumer anywhere in `src/` (each occurs exactly
  once, on the `using` line); `UC.Family` itself uses only `Test`, `Closure`,
  `obs`, `tv₁`, `_≈ℰ_`, and has no importer. Rule 32 leans keep, but this is the
  one place narrowing costs nothing today. Same shape one name wide:
  `UC/QueryBound.agda :: traceᵍ`, in the `open Certificate public using (…)`
  list but referenced only inside `module Certificate`.
- `src/CategoricalCrypto/UC/Emulation.agda :: _⊛₁_` — zero occurrences in `src/`
  outside its own definition and `UC.Family`'s `using` line, and `UC-compose`'s
  statement uses `_⊙_`/`_≤UC_`, not `_⊛₁_`, despite the comment calling it "the
  composite simulator `UC-compose` must produce".
- `src/ProbabilisticLogic/Dp/Elgot.agda :: iterₚ` (with `iterₚ-cong`,
  `iterₚ-fix`, `iterₚ-codiagonal`, `iterₚ-out`) — five of the six re-exports are
  redundant at the only consumer: `Machines.Base` separately `open import`s
  `Dp.Iter`, `Dp.Iter.Codiagonal` and `Dp.Iter.Out`, so those names resolve from
  the source and only `iterₚ-transfer` is reachable *only* through the facade.
  Either `Machines.Base` goes through `Dp.Elgot` — which is what "the one-import
  entry to the law set" claims — or the facade is doing less than its header
  says. Same shape: `Protocol.Machine`, `Protocol.Machine.Pin`, `Dp.Coin` and
  `Dp.Advantage` all reach past `ProbabilisticLogic.Prelude` into
  `Distribution.{Uniform,RationalDist,…Expectation}` for names `Prelude`
  re-exports.
- `src/ProbabilisticLogic/Prelude.agda :: δ` — re-exported unqualified from a
  module that `Protocol.Observe` and `POV` bare-`open`, and **both bind `δ`
  locally** (`{ε δ : ℕ → ℚ}`), shadowing it. Unused through `Prelude` and
  actively confusing; `E` versus `private module E = Em …` in `UC.Family`/
  `UC.Seam` is the same class.
- `src/Categories/Category/Monoidal/Pure.agda :: PureSub` — a genuinely new
  abstraction (no upstream monoidal wide subcategory exists: `SubCat` has
  neither ≈-respect nor ⊗-closure, and `CounitalCopy` is a different notion),
  but the name `Pure` imports Kleisli vocabulary into a module stated over an
  arbitrary symmetric monoidal category, where the concept is "a wide symmetric
  monoidal subcategory as a predicate". Relatedly, upstream puts category
  constructions under `Categories.Category.Construction.*`, and everything under
  `Categories.Monad.*` upstream is structure *on a `Monad 𝒞`* — whereas
  `DiscreteMonad ℓ` is a raw `Set ℓ → Set ℓ` triple (upstream's shape for it is
  `Categories.Monad.Relative.Monad J` at `J : Sets ℓ → Setoids ℓ ℓ`, plus a
  commutativity field). No collisions and no rule-29 violation — checked
  mechanically over both libraries — but the three names claim more of
  upstream's namespace than they occupy.
- `src/Categories/Category/Monoidal/Distributive.agda :: δ⇒` / `δ⇐` — duplicate
  spellings of the public `distributeˡ`/`distributeˡ.inv`, both used in parallel
  downstream (`Machines/Tensor` uses `δ⇒` twice, `δ⇐` four times, `distributeˡ`
  once). Upstream's names are `distributeˡ`/`distributeˡ⁻¹`, and
  `Distributive/Properties`'s `δ⇐-i₁`/`δ⇐-i₂` are verbatim ports of upstream's
  `distributeˡ⁻¹-i₁`/`-i₂` (identical proof term, statement differing only in
  `⁂` vs `⊗₁`) — matching the names and citing the source would be a real rule-30
  alignment, at ~12 files.
- `src/Categories/Category/Monoidal/Distributive/Properties.agda :: ⊥-unique` —
  stated as a bare `{u v : X ⊗₀ ⊥ ⇒ Y} → u ≈ v`. The ecosystem shape is
  `IsInitial (X ⊗₀ ⊥)` (or `X ⊗₀ ⊥ ≅ ⊥`), from which
  `Categories.Object.Initial.IsInitial.!-unique₂` and the rest of
  `Object.Initial` come free. Same content, strictly more useful.

### Test / pin coverage (rule 33)

- `src/CategoricalCrypto/Protocol/Machine/Pin.agda :: machine`, `agree`,
  `machine-∘` — these pin `cum` at hand-tuned depths 5/6/8, and the depths are
  an internal bind-junction count (the header explains them as "the `>>=ₚ`
  junctions the point, the machine's step and the strategy's resumption each
  spend"), so the file freezes the internal structure of `drive`, `stepᴹ`,
  `stateᴹ.point`, `runᴹFrom`, `resumeᴹ` and `coinₚ`: an observation-preserving
  refactor of any of them breaks it. Rule 33's failure mode. I added the pins
  that need no new interface (see *Committed*); the retarget does need one —
  a public "mass from depth `n` on" wrapper in `Dp`, or the pins stated as the
  `Σ[ n ] ∀ m` witness — so it is yours.
- Per-layer gaps, for the record. `Dp.Elgot`'s whole law set (`iterₚ`,
  `iterₚ-fix`, `iterₚ-cong`, `iterₚ-out`, `iterₚ-transfer`, `iterₚ-codiagonal`,
  `iterₚ-uniform`) has no pin and its only consumer is `Machines.Base`;
  `Machines.Base`'s `ℳₚ`/`Tracedₚ`/`𝒢ₚ`/`Remainingₚ`/`Elgotₚ` have none — the
  doc *measures* why the `𝒢`-composition pin is out of reach (`cum n` expands
  2ⁿ branches; at n = 16 the mass has not converged), so that one is a known
  obstruction, but nothing pins even `𝒫ᴵ`'s `id`/`∘` behaviourally at a one-ask
  strategy, which is in reach; and `UC.*` has no pin at all, where `⟦_⟧ᴼ`/
  `wireᴹ` is `refl`-pinnable exactly like `Protocol.Machine.Pin.machine`.
  `qbᵢ-wire` is the layer's only anti-degeneracy witness, and it certifies
  `QBᵢ`, not `Budget.QB`.
- `src/CategoricalCrypto/Examples/ChimericLedger/Pin.agda :: (the instantiation
  `POV 1 (λ _ → [])`)` — a *second* instantiation at an injective `ser` is what
  would make `POV.AtBirthday` reachable, and a birthday-shaped pin at ℓ = 1
  (two distinct transactions get two independent fresh 1-bit hashes, colliding
  with probability ½ — `εbirthday`'s own event) is the one pin that would
  exercise the sampling path at a probability strictly between 0 and 1. I did
  not build it: choosing the two transactions so the collision destroys value is
  design work, not a mechanical addition. (The account-only-genesis vacuity this
  finding started from was fixed upstream at `94fc6e78` while the review ran.)

### Simplifications / perf not committed (judgment needed)

- `src/Categories/Monad/Setoids/Discrete.agda` **(inherited, outside the diff —
  flagged, not touched)** — it re-derives the same ~20-name vocabulary
  `Categories.Monad.Discrete` now provides, and `>>=-comm-y`'s 16-line proof is
  byte-identical in the two files, using only `DiscreteMonad` primitives.
  Routing `Setoids.Discrete`'s `Commutative` through `DiscreteMonad ℓ` and
  re-exporting would delete ~50 lines. The consumer split is real
  (`Monad.Discrete` ← the 4 Machines-stack modules, `Monad.Setoids.Discrete` ←
  11 SFunM-stack modules), so it has to be a re-export, not a deletion.
- `src/CategoricalCrypto/SFunM/Spike/SlotFrame.agda` **(inherited, outside the
  diff)** — 36 top-level identifiers shared verbatim with the new
  `Machines/Frame.agda` over the same `(𝒱 : SymmetricMonoidalCategory o ℓ e)`
  parameter (`pad-inv σ-pad-inv swp-swp σ⊗-inv pad-transport pad-braid unbraid
  σ-splitˡ σ-splitʳ swp-natural swp-natural′ swp-nat onL-∘ onRᵍ-∘ onL-cong
  onR-cong onL-id onR-id onL-str onRᵍ-id⊗ onRᵍ-⊗id onL-branch onR-branch
  onL-sim onR-sim σ-onL σ-onR σ-unit ρα-λ αρ-λ ρ-swp dsc dsc-swp discard-onL
  onR-collapseˡ onL-collapseʳ 𝕄`). Nothing outside `SFunM/Spike/` imports it.
  The spike is the more upstream-aware of the two — it imports
  `Interchange.Braided`, uses `swapInner-coherent`, and documents at its lines
  307–318 that `swp` **is** upstream's `private swapʳ` from
  `Categories/Category/Monoidal/Interchange/Braided.agda:113-114` — so the merge
  direction is spike → `Frame`, and the one thing worth harvesting immediately
  is that citation.
- `src/CategoricalCrypto/Machines/Frame.agda :: λλ-α` — derivable from
  `Categories.Category.Monoidal.Properties.Kelly's.coherence-inv₁` at
  `X = Y = unit` plus `Monoidal.unitorˡ-commute-to`; both are already in scope
  (the `Monoidal.Properties` import is bare). Replaces a 10-line private block.
  Not committed because the residual `assoc`/`cancelˡ associator.isoʳ` shuffling
  is proof work rather than a swap.
- `src/CategoricalCrypto/Machines/Frame.agda :: swp-swp` / `swp-natural′` —
  bundling `swp` as an explicit iso `swpᵢ = record { from = swp ; to = swp ;
  iso = record { isoˡ = swp-swp ; isoʳ = swp-swp } }`, mirroring upstream's
  `Interchange/Symmetric.swapInner-iso`, would turn `swp-natural′`'s five-step
  block into `conjugate-from swpᵢ swpᵢ (swp-natural g)` and make the
  `insertʳ`/`cancelˡ swp-swp` sites uniform `switch-*`/`cancel-*`. Do **not**
  define it as the composite iso `associator⁻¹ ∘ᵢ (idᵢ ⊗ᵢ braided-iso) ∘ᵢ
  associator`: its `.to` is bracketed `(α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒` where `swp` is
  `α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)`, which costs an `assoc` at every use site.
- `src/CategoricalCrypto/Machines/Frame.agda :: σ⊗-inv` — `σ-pad-inv` goes
  through the named `pad-inv` while its mirror `σ⊗-inv` open-codes the same
  argument. Rules 26/28: give the left padding its own `pad-invˡ` and route both
  through it, or open-code both.
- `src/ProbabilisticLogic/Distribution/RationalDist/Support.agda :: 0≤+`
  **(inherited, outside the diff)** — `private`, and the exact `_≤_`-spelled twin
  of the public `Data.Rational.Properties.Ext.0≤*` that sits beside it at every
  use. Promoting it would make `Dp.node-nn` read `0≤+ (0≤* n₁ m₁) (0≤* n₂ m₂)`
  instead of a `≤-trans`/`≤-reflexive`/`+-identityʳ` chain.
- `src/ProbabilisticLogic/Dp/Commutative.agda :: pairₚ-≼` / `pairₚ′-≼` and
  `src/ProbabilisticLogic/Dp.agda :: >>=ₚ-congᵖ` — four- and five-deep
  `≤-trans (≤-reflexive …)` towers that `Data.Rational.Properties.≤-Reasoning`
  (with `≡⟨_⟩` for the reflexive steps) would flatten; roughly LOC-neutral.
  Relatedly `Dp.Commutative.mapₚ-≤` belongs beside `mapₚ-cum` in `Dp.Iter`
  (rule 28).
- `docs/protocol-rewrite.md :: "Assumption ledger"` — accurate on hatches (21
  tree-wide, 0 in-scope, verified) and on the stated `Set`s, but two claims have
  drifted: `Machines.Trace.Remaining` is **not** a module parameter of anything
  (`Machines.G` builds it from `Laws.Remainingᴹ` unconditionally — only
  `Iteration.Elgot` is still a parameter), and `UC.Seam`'s `pov-carry` is listed
  under "Proved, hypothesis-free" although it consumes `AgreeToAdv`, exactly as
  `POV.pov-via-audit` consumes `TrajectoryFromAudit`. Also: the M3 section says
  "the `Dₚ`-facing six add `--guardedness`"; the count is seven.
- The systematic one, which is genuinely a lifecycle question and so genuinely
  yours: roughly fifteen module headers carry a paragraph that also appears in
  `docs/protocol-rewrite.md` — the `HomTransportTrivial` archaeology in
  `UC.Environment`, the `Ix = ℕ` account in `UC.Family`, the `Reflects`
  refutation in `UC.Bridge`, the reference-arc LOC prices in `UC.QueryBound`,
  the transfer-form "three reasons" in `Machines.Iteration`. Rule 24 wants one
  copy and rule 23 says an essay lives in `docs/` with a pointer — but which
  copy survives depends on whether `docs/protocol-rewrite.md` is durable or is a
  work plan to be retired when the branch lands, which only you know. I cut only
  the clauses that carry no positive content (see `fd814f00`) and left every
  paragraph that states a why, a gotcha or a price.

## Tried, not worth it

- `implicit-drop` **as a class, all 113 oracle-green survivors declined** (591
  candidates, 8 files). It is green but not a strict improvement: it leaves
  signatures half-annotated in a layer where the object annotations are the
  reader's only orientation. Concretely — `⊗idᵉ-hom` would read
  `((g ∘ᴹ f) ⊗ᵉ idᴹ) ≈ᴹ ((g ⊗ᵉ idᴹ) ∘ᴹ (f ⊗ᵉ idᴹ {D}))`, three `idᴹ` at the
  same object with one annotated; `natˡ`'s two dropped `idᴹ`s are at *different*
  objects `C` and `D` whose combination into `C + D` on the right is the content
  of the law; `onL-sim`/`onR-sim` lose the `id {X}`/`id {Y}` that show the
  square is over `X → Y`; and `Frame.σ-unit` becomes `σ⇒ ≈ id`, whose objects
  are then solved from its own *body* and whose surviving comment is the only
  place `unit` appears. It also leaves redundant parens (`⟺ (hexagon₁)`,
  `pad-transport θ (i₂)`, `dsc (id)`). 34 of the 113 are inside
  `Reassoc.onL-α`'s hand-tuned `solveMor!` term, where inference would replace
  an explicit pin in the layer's single solver call; measured warm cost is
  unchanged (9 s → 10 s), so there is no perf argument either way. The tally is
  committed if you want to take it.
- `enum-where`, 144 of 146 sites, dispositioned by measured property rather than
  by family opinion (the tool's own `approxUses` reads 0 even for bindings that
  are plainly used, so its `singleUseCandidate` flag is not usable evidence
  here — worth fixing in the toolkit). Real token counts: **54 are used twice or
  more**, so rule 18 does not apply; **57 are single-use with a multi-line
  body**, where inlining moves a multi-line expression into a chain step; **15
  are single-use, one-line and ascribed**, of which one was taken (`tr`) and 13
  declined after spiking `Frame.swp-natural`'s `step-α`/`step-σ` — the inline
  typechecks but turns two named naturality squares into 70-character
  justifications inside a `begin … ∎` chain and breaks its alignment; and **20
  are single-use, one-line and bare**, every one a named step of a `≤-trans`
  sandwich (`f1..f4`, `d1..d5`, `c1..c4`, `e1..e4`, `s1..s5`, `t1..t5`),
  assembled in one chain at its own site — I checked the assembling line in each
  of the four files — where the names index the module header's step-by-step
  account and inlining collapses them into one ~350-character application.
- **Section-banner normalization** to rule 25's closed boxed form. Measured
  census: the branch has 21 closed and **97 open** banners (rule/title, no
  closing rule), and the *inherited* tree has 253 closed and 433 open — the repo
  has no single convention and the open form is the majority on both sides.
  97 cosmetic hunks against the majority style; the M1 files are closed-form and
  the M2/M3 files open-form, which is at least consistent per layer. Dropped.
- `src/ProbabilisticLogic/Dp.agda :: node-dirac` (with `node-zero`,
  `Dp/Commutative.agda :: node-+`, `node-*`) → `Data.Rational.Solver.+-*-Solver`.
  It exists and applies, but after the `interchange`/`x∙yz≈y∙xz` swaps these are
  one- and two-liners, so `solve n (…) refl` is LOC-neutral while pulling
  `Algebra.Solver.Ring`'s Horner normalizer and ℚ's `_≟_` coefficient decisions
  into `Dp`'s import closure. There is no `Data.Rational.Tactic.RingSolver`
  (only ℕ and ℤ have the reflective tactic), so there is no mechanism for a win
  and rule 31 forbids the claim.
- `src/Categories/Category/Monoidal/Pure.agda :: PureSub` → upstream
  `Categories.Category.SubCategory.SubCat` (`I = Obj`, `U = id`). `SubCat` packs
  homs in a Σ and has no ≈-respect field, so every hom in the machine layer
  would become a pair and `pure-resp-≈` would have to be added back. Strictly
  worse.
- `src/Categories/Category/Kleisli/Discrete.agda :: Klᴹ-Symmetric` → upstream
  `Categories.Category.Monoidal.Construction.Kleisli.Symmetric.Kleisli-Symmetric`.
  The statement matches, but the module header already records the measured
  reason it is not used ("upstream's `Kleisli-Symmetric` heap-exhausts here,
  because its `commutative` field eta-expands the Kleisli hom setoid's
  `IsEquivalence` into metas that are never solved. Do not replace it by a
  transport off that construction."), which matches this repo's recorded
  `GradedKleisli` eta-OOM class. Left alone; that comment earns its place.
- `src/CategoricalCrypto/Machines/Frame.agda :: pad-inv` (with `pad-transport`,
  `onL-branch`, `onR-branch`) → the generic upstream forms
  (`Categories.Functor.Properties.[_]-resp-∘`/`-resp-Iso`/`-resp-square`,
  `Monoidal.Reasoning.serialize₁₂`/`₂₁`). They exist, but the functor plumbing
  at each site is longer than the two- and three-combinator proofs already
  there.
- `src/CategoricalCrypto/Machines/Frame.agda :: swp` → an upstream import.
  `swp = α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒` is character-for-character upstream's `swapʳ`
  (`Interchange/Braided.agda:113-114`), but that definition and its mirror
  `swapˡ`/`swapˡ-act` are inside a `private` block, and the public
  `swapInner-natural` is 4-factor and does not specialize without unitors. There
  is nothing importable today; the honest fix is an upstream PR de-privatising
  `swapʳ`/`swapˡ`/`swapˡ-act`, which would delete `swp-swp`, `swp-nat` and one
  naturality outright. (The formula appears a third time as
  `Categories/GConstruction.agda`'s private `β`.)
- `src/CategoricalCrypto/Examples/ChimericLedger/POV.agda :: oracle` — the
  `case_of_` swap needed `Function.Base`, which POV did not import. Not dropped:
  a bare `open import Function.Base` is green with no clash, so the swap landed
  (`fa6d94bc`). Recorded because the sibling precedent in the previous review
  declined the same swap for want of the import.
- Rule 29 shadowing, checked and clear: for every `.agda` file the branch adds,
  no file of the same relative path exists in `agda-categories-0.3.0/src` or
  `standard-library-2.3/src`. No violation; the naming concerns above are about
  namespace *tenancy*, not collision.
