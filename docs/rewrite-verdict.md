# Rewrite verdict: `protocol-rewrite` vs the old lineage

Comparison of `protocol-rewrite` (M1–M3, at the addendum-3 integration
86 files / +11883/−295 over `f71a2381`) against the old lineage's tip
(`sfunm-setoid` + `spike/pov-tower`, 59 files / +9592/−1888 over the same base).

## Verdict: ADOPT the rewrite as the mainline

The rewrite dominates on every axis the maintainer has pressed, and its gaps versus the
old lineage are enumerable ports, not regressions in kind.

| axis | protocol-rewrite | old lineage |
|---|---|---|
| statement honesty | POV over the state trajectory at a pinned genesis; randomized strategies native (`coin`); **no budget in any statement**; `SameTV` ancilla-parametric ⇒ **no K island**; ε-indexed `≈ₚ[ε]` replaces the (at Dₚ uninhabitable) ℚ-valued `adv`; the bridge quantifies over the budgeted strategies instead of witnessing a dominating one, a context's budget is guarded against zero, and the seam is built along the embedding with a simulator-aware carry at both grades (addenda) | budget-parametric statements needing calibration remarks; 2-module K island; deterministic `Dgr` (`Reflects` refuted once); ledger `valid` had two value-leak bugs making POV(inputConsuming) **false** |
| reach | machine category = `Traced` + **`GConstruction` verbatim, zero hypotheses** (`𝒢ₚ` closed); unbounded machines native — infinite traces with no towers, no `Stabilizes`, no `clip` | never reached `𝒢` (blocked at ro-model phase 1); infinite traces only via the tower workaround |
| example | `ChimericLedger.POV` = 190 lines, 3 layer imports, plain-Agda ledger, `Sys = ledger ∘ᵖ oracle`, pins by `refl` | same shape achieved only after three API redesign passes; rests on `System` certificate luggage |
| equalities | one hom-equality (simulation zigzag) from birth | four-relation zoo (`≈ᴹᶜ/≲/≲ᵒ/≈ˢ`) + ~780 LOC of word machinery with no counterpart in the rewrite |
| hatches / flags | 21 = baseline; zero postulates; `--without-K` everywhere incl. all of `UC.*`; `--guardedness` on 18 Dₚ-facing modules only | 21 = baseline; K island (2 modules) |
| perf | typical module 2–12 s warm; the measured outliers are `UC.Machine` 74 s, `UC.Machine.Grading` 22 s and the ledger pin ~3 min, each documented at its site | 450 s MD remainder (slated for deletion); two conversion-wall incidents |

## What the old lineage still has (the port ledger, in harvest order)

1. ~~**`van-bound`**~~ — PORTED verbatim (addendum 3): `Uniform/Decay`,
   `Nat/Properties/Ext`, consumed by `UC.Family.VanishingBound`.
2. **The α query-bound content**: the trace-free `qb` calculus is now PROVED
   hypothesis-free (`qbᵢ-id`/`qbᵢ-T₁`/`qbᵢ-sub` + hom-level forms + the two
   reassociators, addendum 3); what remains of the old branch's content is
   `Counting` (250–350) and `qb-∘` (250–400, the token walk over a ⊕-trace).
3. **The MD example**: its crypto core (`MerkleDamgard/Core`, machine-free) ports
   verbatim; the machine side becomes a `Protocol` with the free-monad `Call`
   (k calls per message) — replacing the old `_∘ᵍ_`/`stableN`/clock apparatus outright.
4. **The functor seam**: `Morphism-∘` (300–500; the ≲ direction has the state map, the
   reverse needs thought — flagged) and `PrAgree` (250–450), whose missing link — a
   general `Dist⊥ → Dₚ` embedding — LANDED as `Dp.Embed` (addendum 3): `embed-cum`
   is exact at every budget past `suc |entries|`, so what remains is the unrolling.
5. ~~**`Monoidal (GConstruction C)`**~~ — PROVED (addendum 4): generic over the four
   existing trace hypotheses, instantiated as `Machines.Base.𝒢ₚᴹ` with
   `𝒢ₚ-Monoidal : Monoidal (𝒢ₚ ℓ)`.
6. **The seam's remaining steps**: `EnvAsCtx` (~80–120, REPLACES `StratIsEnv` as the
   obligation — the reduction is proved generically as `UC.Environment.≈ℰ-at`) and
   `Adequacy` (~250–350), after which `AgreeToAdv` and `pov-carry` are theorems
   (addendum 1); the trivial grade's `SubBlind`/`IotaBlind` (~60–90 each) and
   `AuditIsBounded` (~120–180), after which both simulator carries reach layer 1
   (addendum 2); `ContextDominated` (~250, instance-specific);
   `GradingLawsᴹ`'s eight fields — the ASSEMBLIES `Gradingᴹ`/`Budgetᴹ` are now
   proved (addendum 3), so the laws alone stand between `𝒫ᴵ` and a full
   `UCBase`+`Budget`; `UC-compose` (two `Grading` fields).

Total to parity-and-beyond: ≈1200–1900 LOC, all routine-to-medium, none research-grade.

## Honest liabilities of the rewrite

* `morphism` preserves composition but **not identities** (`wireᵖ` costs a query where
  `𝒢.id` forwards silently — the Katis–Sabadini–Walters delay at the functor seam). A
  genuine functor lands in a subcategory of `𝒢`; the UC seam must be built with that in
  mind. Recorded in `Protocol/Machine`'s header.
* `refl`-pins of *categorical* composites are measured out of reach at Dₚ (`cum n`
  explores 2ⁿ branches through junction delays); pins compute for protocol composites
  and direct machine images. The old clocked layer was better at this — it is the one
  thing it was better at, and the recorded reason it could return as an internal exact
  fragment if ever needed.
* The old branch's proved-but-unported content (item 2 above) means the rewrite is
  *currently* behind on inhabited query-bound theorems; adopt-then-port, not
  port-then-adopt, is still the right order because nothing in the port is blocked by
  the rewrite's design — while the reverse direction (fixing the old statements) was
  what this rewrite exists to avoid.

## Disposition of the old branches

`spike/pov-tower` (frozen at 75cbfb70): archive; reference for the System-API pattern
and the coherence-field refutations. `sfunm-setoid`: archive after items 1–3 are
harvested; its MD-relocation plan docs remain the map for item 3. `spike/pov-dp`,
`spike-dp`, `spike-elgot`: fully harvested, archive. The MD line inherited at
`f71a2381` stays green and untouched on this branch until item 3 replaces it; the M3
doc records the one-to-one supersession map for the deletion pass.

## Addendum: external theory review, findings and resolutions

Reviewed at `ebb3f2a5` (`docs/protocol-rewrite-theory-review.md`); all four findings are
resolved on this branch.

1. **Vacuous birthday target.** `AtBirthday`'s account-only genesis dead-locked the
   input-consuming ledger, so the bound held with probability zero. Genesis is now all the
   value in ONE UTxO output keyed by a genesis hash `h₀` (an `AtBirthday` parameter beside
   `ser-inj`), the bound is `ε q = (q² + q)·2⁻ˡ` — the `+ q` for fresh hashes colliding
   with `h₀` — and `ChimericLedger.Pin` pins acceptance-with-probability-1 and the state
   change by `refl`, so the vacuity cannot return unnoticed.
2. **`Reflects` quantifier order.** A finite `Strat` mentions finitely many first queries
   and so cannot reflect a `Dₚ` context that samples an unbounded-support question at
   query bound one. `UC.Bridge.Reflects` now quantifies over the compared pair *before*
   witnessing the strategy; the uniform form is priced as a `Dₚ`-valued or coinductive
   strategy language, not built.
3. **Seam direction.** `AgreeToAdv` cannot follow from `Reflects` (wrong direction).
   `UC.Seam` is rebuilt along the embedding instead: `strategyEnv` (a finite strategy as
   an environment) is constructive, `StratIsEnv` (`UC.Seam.Grounding`) and `Adequacy` are
   the two stated-and-priced steps, and `AgreeToAdv` — hence `pov-carry` — is now a
   THEOREM of those plus `PrAgree` (`UC.Seam.Carry`). Carrying a bound across `_≤UC_`
   needs the interface-observable audit form, the simulator being quantified at a graded
   codomain; recorded in the module header.
4. **κ cofinality.** `UC.Family` now takes `κ-cofinal : ∀ N → Σ[ i ] N ≤ κ i`, without
   which a bounded `κ` makes every eventual statement — hence the UC preorder — vacuous.
   `≈^ω-witness` is what it buys.

## Addendum 2: second external theory review, findings and resolutions

Reviewed at `f096c5d5`; round 1's four resolutions are confirmed there, and all three
new findings are resolved on this branch.

1. **Context budgets collapsing to zero.** `c * c′` charges a genuinely querying
   context nothing when the closure certifies at `QB 0` (an ancilla with no downward
   port). `UC.Base.ctxBudget c c′ = c * (c′ ⊔ 1)` replaces it in `UC.Bridge`, in
   `UC.Family`'s `_≈ℰ[_]_` (as `ctxQB`, still polynomial) and in `UC.Audit`; the
   port-specific bound on crossings of the distinguished hole is priced, not built.
2. **A simulator-aware carry.** `UC.Emulation.unit-grade` proves the unit-grade
   specialization (an emulation at a blind grade IS `pov-carry`'s direct premise) and
   `UC.Audit.audit-carry` proves the graded one (an interface-observable audit bound
   crosses `_≤UC_` at the emulation's slack, the simulator absorbed into the test and
   its queries charged there). Both are proved over an arbitrary base because at the
   machine instance an `≈ℰ` between composites cannot be a term's type; the instance
   modules name the residue (`SubBlind`/`IotaBlind`, `AuditIsBounded`).
3. **The existential reflection.** Gone: `UC.Bridge.ContextDominated` quantifies over
   the strategies the context's budget affords and concludes at `ε + δ` for an
   arbitrary positive δ, which is what a convexity argument over a supremum-valued
   mass delivers and what layer 1's budget-quantified theorems feed directly.

## Addendum 3: the integration (2026-09-05)

Three streams merged onto the branch, all green (closure + pins rc=0 with the
extended warning gate empty; hatch grep 21 = baseline; K island still absent).

1. **The cheap bundle** (5 commits): the van-bound port (ledger item 1, done);
   `Dp.Embed` (`embed-cum` exact via a conditional-coin cascade — structural, no
   guardedness, divisor-free by stating the induction mass-scaled); the three
   trace-free budget laws, proved; and `StratIsEnv` reduced to `EnvCtx`/`EnvAsCtx`
   through the generic `≈ℰ-at`. One honest BLOCKED mark: the closing application
   `EnvAsCtx → StratIsEnv` does not come back at the instance (measured in four
   spellings; the residue is the instance's own unfolding under application —
   the same class the pinning below cures, recorded in `UC.Seam.Grounding`).
2. **The qualitative core split** (5 commits): `UC.Base` split into a
   quantity-free core (`UC.Core`: `Grading` + a qualitative `Observation`) and
   optional enrichments (`UC.Approximate`'s abstract `ErrorAlgebra` with the ε/2
   argument proved once; `UC.Budget`; `UC.Environment.Approximate`), the
   `Induced` construction giving both machine and asymptotic observations from
   their ε-relations, `UC.Saturated` stating the transportable POV form, and
   `UC.Core.Standard` PROVING the reconciliation with the inherited `UCSetup`
   doctrine (a monoidal category grades itself; `a⇐`/`a-isoˡ` land exactly on
   `GradeStableFromTests`' `θ`/`θ-μ`). `UCSetup` itself is not instantiable at
   the machine model — `𝒢ₚ` has no monoidal structure yet, and the core is the
   test-generated case of the presheaf interface — which is the precise sense
   in which the abstraction-notes layering is realized rather than duplicated.
3. **The quality pass** (9 mechanical commits + `QUALITY-REVIEW.md`, 27
   judgment items): landed for the protocol/machine/Dₚ layers; its edits to the
   UC layer were superseded by the core split (conflicts resolved in the
   split's favor), so a style re-sweep of the restructured `UC.*` is owed.
4. **`Gradingᴹ`/`Budgetᴹ` assembled** (from the quality review's crux spike):
   the eta-cliff verdict in `UC.Machine` was WRONG — with every object implicit
   pinned the assembly typechecks, and it lives in `UC.Machine.Grading` because
   the same text inside `UC.Machine` costs 852 s against 74 + 22 s split. The
   grading obligation is now exactly `GradingLawsᴹ`'s eight fields.

**Open defect worth the maintainer's eye — a degenerate `Grading`.** The
`Grading` record's ten laws are satisfied by the constant grading
`_⊛_ = λ _ B → B` (every `T₁`/`sub` the identity), under which `_≈ℰ_` collapses
to plain observational closure and `_≤UC_` between closed processes becomes
nearly trivial to inhabit. This is the same vacuity class the two theory
reviews flagged (`QB c f = ⊤`, bounded `κ`): nothing false is provable, but a
theorem quantified over an ABSTRACT grading proves less than its reading
suggests. The intended instance (`Gradingᴹ`, where `_⊛_ = _⊗ᴵ_` is injective on
messages) is now assembled, which contains the risk at the model; a
non-degeneracy field (or stating emulation theorems at the instance) is the
principled fix, priced but not chosen here.

The layering after the merge (core / enrichment / model / frontend, with what
each may not assume) is recorded in `docs/protocol-rewrite.md`'s M3 section,
which also carries the updated priced table: the statement-only surface is now
`Counting`, `qb-∘`, `EnvAsCtx`, `Adequacy`, `ContextDominated`,
`SubBlind`/`IotaBlind`, `AuditIsBounded`, `TrajectoryFromAudit`,
`GradingLawsᴹ`'s eight fields, `UC-compose`'s two, and `SaturatedRespects` —
every one a type with a price, none a postulate.

## Addendum 4: direction ruled, gate closed, observation honest (2026-09-05)

The maintainer accepted `docs/kb/frontier/15-probabilistic-uc-model.typ` and RULED
that the UC layer is to be built by instantiating the inherited, proven
`UCSetup`/`Abstract2` metatheory (`Standard2.StdUC`) at the machine model — no
parallel UC definition. Three consequences landed, all green (four-root sweep,
warn-gate empty, hatches 21):

1. **`Monoidal (GConstruction C)` is proved** (`Categories.GConstructionMonoidal`,
   generic, NO new hypotheses — the four trace assumptions `GConstruction` already
   took suffice), with the machine bundle `Machines.Base.𝒢ₚᴹ : MonoidalCategory`.
   The plan's pricing was pessimistic twice (the hypergraph solver takes the
   compound-object `σ⇒` whole; `homomorphism` needed one new loop-re-bracketing
   lemma `trace-mid` and no dinaturality) and optimistic once (the one-shot
   8-atom coherence is unaffordable at 900 s; split at the single differing
   segment it is 29 s). Sharpest perf law yet: state the category and its
   monoidal structure as projections of ONE `GConstruction*` application — two
   separate applications heap-exhaust 8 GiB where the bundle costs 12.7 s.
2. **The observation is two-sided** (`≼ₚ[ε]` quantifies the verdict indicator):
   answers-`false` is no longer identified with diverges, refuted by `refl`-pins
   (`nay`/`stuck`); `indᵇ true = bool→ℚ` definitionally, so the one-sided API and
   the MD suite were untouched. Layer 1's `_≈adv[_]_` had the identical defect
   and is fixed the same way.
3. **Crypto-grade negligibility** (`Negligible`, magnification form) sits beside
   `_→0`, with `NegligibleBound⇒VanishingBound`, `CarriedNegligible` (the
   proposal's §3 discipline, PROVED at the `ctxQB` budgets via `PolyQB`) and
   `absorb-negl`.

**Consequences for the ledger above.** Port item 5 is closed; `GradingLawsᴹ`'s
four trace-carrying fields now have their fusion tools — and under the ruled
direction they may dissolve entirely: `UC.Core.Standard.gradingᵗ` applied to the
genuine `𝒢ₚᴹ` yields the grading from the monoidal structure, leaving only the
zigzag between the direct relays (`T₁ᴵ`/`subᴵ`) and their monoidal spellings.
The degenerate-`Grading` defect of addendum 3 is likewise expected to dissolve
(the ruled route's grading is the curried tensor by construction, not an
abstract record); to be re-assessed after the `StdUC` instantiation. In flight:
the `StdUC`-at-machines performance spike, whose verdict gates the build.

## Addendum 5: the seam closed, the cone built and retired, the perf ruling (2026-09-06)

Everything below is merged on `protocol-rewrite`; hatches 21 = baseline throughout.

**Landed since addendum 4.**

1. **The seam is closed**: `PrAgree` (`Protocol.Machine.Agree`, via the `Dp.Stable`
   closure family — `Dp.Embed` off the path) and `Adequacy` (`UC.Seam.Adequacy`),
   making `agreeToAdv`/`povCarry` closed terms and wiring `pov-carryᴸ` into the
   ledger (`Examples.ChimericLedger.Carry`).
2. **`Counting` and `qb-∘` are theorems** (`UC.QueryBound.{Counting,Compose}`);
   `BudgetLawsᴹ` assembles (`Compose/Laws`).
3. **`Morphism-∘` is a theorem** (`Protocol.Machine.Compose`). Neither simulation
   direction is definable (fused continuations one way, an unreachable-but-total
   configuration the other); the proof simulates out of a third machine of
   reachable configurations. `Wiring`'s pointwise calculus generalized into
   `Machines.Collapse`.
4. **`GradingLawsᴹ`'s eight fields were proved** (the `Cast/*`+`Laws/*` cone),
   **and then the cone was retired** — see the perf ruling. The grading now IS
   `gradingᵗ (𝒢ₚᴹ 0ℓ)` (363 ms), with `gradingᴹ : Grading (𝒢ₚ 0ℓ)` and `ucBaseᴹ`
   closed terms in `UC.Machine`; addendum 4's dissolution prediction was correct.

**The perf ruling and its root cause.** The maintainer set a hard bar: ≤150 s
warm per module. The measured root cause (8-line core, `docs/`): *receiving* an
agda-categories `Monoidal` law at a hand-written type costs ~470 s — the record's
law types use private tensor abbreviations no consumer can spell, and the
mismatch normalizes through the ⊕-trace. Derived types are free. Consequences,
all measured: opaque seals are a NEGATIVE for consumers of the unfolding (probe:
bare crossing 421 s, partial seal 1.14× worse); the `Iface`-indexed grading is
unaffordable in principle (re-indexing the free grading costs >1500 s); the cone
(~3.0 h) was deleted, −658 LOC, and `UC.agda`'s closure fell from hours to
**158 s**. Layout law: re-index objects at the use site (5.9 s), never in the
statement (42 s).

**Deleted theorems (sanctioned).** The relay-form laws `T₁-∘`/`sub-∘`/`a-isoˡ`/
`a-nat` about `T₁ᴵ`/`subᴵ`/`a⇒ᴵ` are no longer proved anywhere; the action-form
laws are free via `gradingᵗ` and `Dictionary`'s zigzags bridge the two readings.

**Restated (never weakened).** `Observationᴹ : Observation (𝒢ₚ 0ℓ)`;
`Seam.Audit`/`Seam.Grounding` drop their `Grading 𝒫ᴵ` parameter and read at
`⟦_⟧ᴵ`-images. All QueryBound, seam, and example statements verbatim.

**Owed / over the bar.**

- `Budget` at the machine model: wants `QB`/`Certified` generalized to
  𝒢-objects (statement generalization, not attempted).
- A structural ceiling: any module reading a G-composite's step pays ~230–250 s
  for one G-record `_∘_` projection (`Wiring` 230 s, `Protocol.Machine.Compose`
  231 s, `Compose/Step` 721 s = same class + conversion). Opacity cannot bridge
  it; under-150 s for this class needs a new mechanism or an explicit exemption.

## Addendum 6: both remaining perf items closed (2026-09-10)

Addendum 5's "Owed / over the bar" section is fully resolved (merge `4ed9e9da`):

1. **`Budget` at the machine model is a closed term** — `UC.Machine.Budget.budgetᴹ
   : Budget (𝒢ₚ 0ℓ) gradingᴹ (suc 0ℓ)`. The generalization went through
   `UC.QueryBound.Object`: `QBᴳ A B = QB {retᴵ A} {retᴵ B}` sealed `opaque`
   (with `p = p` image bridges inside the unfolding block), so the existing
   `Iface`-spelled API is byte-identical and the 𝒢-object spelling never
   re-indexes during field checking.
2. **The G-projection ceiling is retired, by opacity done right.**
   `GConstruction._∘_` is now the opaque `composeᴳ`, with its defining equation
   (`composeᴳ-raw`, by `refl` inside the block) exported as the ONE unfolding a
   consumer applies. Addendum 5's "opacity cannot bridge it" was true of the old
   layout (consumers consumed the unfolding); the fix makes them consume the
   equation instead, and the concrete certificates (`Compose/Step`) work on the
   raw trace form directly. The congruence residue is paid once, in
   `Machines.Collapse.Congruence`. Measured warm after: `Compose/Step` 721 → 9 s,
   `Wiring` 230 → 8 s, `Protocol.Machine.Compose` 231 → 10 s, `Compose/Laws`
   11 s, `Congruence` 9 s — every module in the repo is under the 150 s bar.

Restatements in the merge (definitional, never weakened): `BudgetLawsᴹ.qb-∘`
states its composite in the trace spelling (the `𝒢._∘_` reading is recovered as
the theorem `qb-∘-category`, and `qb-∘ᴳ` feeds `budgetᴹ`); `QB` stores the
underlying machine equality (`S.≈ᴹ`) rather than projecting the definitionally
identical relation from `𝒫ᴵ`; `EnvCtx.plugs` sits behind the opaque `EnvPlugs`
with definitional to/from bridges. Deleted as unused: `Dictionary`'s four
resp/id corollaries (`T₁-resp-≈ᴹ`, `T₁-idᴹ`, `sub-resp-≈ᴹ`, `sub-idᴹ`).
`𝒫ᴵ` itself is now literally `Reindex.category (𝒢ₚ 0ℓ) ⟦_⟧ᴵ`. Hatches 21.

## Addendum 7: the audit chain assembled, the supersession executed (2026-09-11)

Six merges since addendum 6, all green at hatches 21; every module under the
150 s bar.

1. **The seam residue** (`52d0f457`): `IotaBlind`, `EnvAsCtx`, and `StratIsEnv`
   (the long-blocked one) PROVED (`UC.Seam.Grounded`) — the unlock was taking
   the trivial grade at the bundle's own unit. `SubBlind`/`UnitGrade` were
   REFUTED as stated (a divergent-initialization scalar is not the identity; a
   never-observing process `≤UC`-emulates everything) and `AuditIsBounded`
   found to omit `asks≤ q (bad d)`.
2. **The MD example ported** (`e1cc100f`, ledger item 3): crypto core verbatim
   (1857 LOC, 35 s); machine side as a `Protocol`; `indistinguishable`
   reproved against the STRONGER `Strat` class; `qbᴹᴰ` a theorem (was a
   hypothesis); the retired machine apparatus and the old `MerkleDamgard/UC`
   ladder deleted.
3. **`ContextDominated` PROVED** (`251fa20f` + `42a42215`): reduced to
   `Skeleton` (budget `c·(c′⊔1)` falls out of `qb-∘`/`qb-sub` exactly), then
   `Skeleton` proved — certificate-to-strategy extraction (truncation answers
   `out (not b)`, invisible per-verdict), a budget-tied transfer at the
   instance (a generic `Dp`-layer form is IMPOSSIBLE — written, proved,
   deleted; depth-tied budgets have no generic `cum` statement), convexity
   reassembly. δ confirmed unnecessary.
4. **Supersession phases 2 + P6 executed** (`6e044949`, `6964f9cc`): the seam
   re-spelled at the seal (at the Model cone's ~9 s floor); the B-names
   deleted; `ucSetup^ω : UCSetup` at `Fam` a closed term. To state the Budget
   unitor certificates (maintainer-approved), `Grading` gained unit/unitor
   DATA fields and `Budget` the four certificates. End state, sharper than
   planned: `Grading`/`UCBase` survive as infrastructure (`gradingᵗ`,
   `UC.Environment`); the hand-rolled METAtheory is what retired. Seal-crossing
   rule (measured): bundle-derived data cross by `subst` along `sealᵒ`;
   retyping OOMs at 8 GiB.
5. **The carry repaired per maintainer rulings** (`e22baf27`): `_≤UC_`
   untouched; `UnitGrade` restated with `TotalRun` hypotheses on the machines
   (consumers assume literally `Hash ≤UC RO`; totality is a THEOREM for
   protocol images — `totalRun-morphism`) and its squeeze PROVED
   (`unitGrade : SubBlind → UnitGrade`, via the new mass calculus `Dp.Mass`:
   two-sided domination + exact totality force the scalar's mass to 1).
   `SubBlind` restated true (SimTotal hypothesis) — its proof is the one open
   piece: a lax-simulation congruence through `∘ᴹ`/`⊗ᵉ`/trace (machine-layer
   sub-project). `AuditIsBounded` fixed, stated, not yet proved.

**Open at this addendum**: the birthday bound (in flight — `TrajectoryFromAudit`
+ RO collision analysis), `AuditIsBounded`'s proof (~120–180 LOC, inputs all
theorems), the `subBlind` lax-simulation sub-project, the MD `≤UC`-RO successor
statement, quality re-sweep, and the OPTIONAL confidential ledger (maintainer:
end of project).

## Addendum 8: the birthday bound is a theorem (2026-09-11)

`Examples.ChimericLedger.Birthday.target : Target a₀ V` (merge `dcdf0142`) —
POV's `AtBirthday.Target` inhabited verbatim: no strategy of query budget `q`
moves the repaired ledger's total value away from genesis except with
probability `εbirthday q = (q²+q)·2⁻ˡ`. The port ledger's flagship quantitative
item is closed, by the DIRECT route (no UC seam, hence tight — the `POVaudit`
carry route stays available once `AuditIsBounded` is proved, at ε(2q)).

Structure: `TrajectoryFromAudit` proved with NO persistence induction (the
audit answer is definitionally the truth about the state — the old ~250–400
LOC pricing was for the wrong proof); the adaptivity handled once and
generically (`Protocol.Safety.hit-bounded`: invariant + supermartingale
potential bounds every adaptive strategy, divergence not a violation); the
birthday arithmetic general (`Uniform.Birthday.birthday : Γ 1 q ≤ (q²+q)·2⁻ⁿ`);
the certificate's crux a `dup` flag reconstructed from state (a collision may
only make a transaction REPLAYABLE, so the potential records the debt when the
sample is charged — with `badTotal` as indicator the supermartingale is false)
plus a `Stales` invariant making a table hit at an accepted transaction
impossible. **`inputConsuming` is spent exactly there** — the staleness witness
is the transaction's first input — making the slides' repair load-bearing in a
proof for the first time (with `chimeric` in its place the bound is FALSE, and
`ChimericLedger.Replay` computes the attack).

Owed consolidation (DISCHARGED in the housekeeping merge): `MerkleDamgard.Core`'s private `sumR`/`Γ` copy onto
`Uniform.Birthday` (noted in that header). Hatches 21; every module ≤50 s.
