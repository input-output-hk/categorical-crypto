# The graded extraction bridge

Branch `graded-bridge`, off `protocol-rewrite` at `96946499`.

[`docs/fcom-extraction.md`](fcom-extraction.md) §"Not delivered, precisely"
item 1 lists four residuals (a)–(d) between the RO-commitment branch's two
delivered components and the UC-level ε-statement, and
[`docs/hash-forward.md`](hash-forward.md) step 5 records the same stop seen from
the exact toy. This branch turns (a), (b), (c) and the application (e) into
theorems, and replaces (d) and (f) by a precise account of why they are not the
statements they were written as.

Everything below is a checked term unless it is in the "Not delivered" section.
Hatches in `src/` stay at their baseline of zero: the
`postulate|TERMINATING|primTrustMe|\{!` grep counts 16 hits before and 16 after,
all of them the words "postulate-free" in inherited comments.

## What the four residuals turned out to be

Two of the four were priced by the doc as proof work and are in fact free once
the composite is grouped correctly; one needed a coercion of the shape
`UC.Model.Seal`'s header already prescribes; and the fourth is not a proof
obligation at all but a typing mistake, described in "Not delivered" below.

### (a) `plug-runᵍ` — delivered

`src/CategoricalCrypto/UC/Seam/Audit/Context.agda:146`

```agda
plug-runᵍ : obs (tv₁ 𝟘ᴳ (gradedᵒ f) auditTestᵍ) (closedᵒ w) ≈ₚ ctxRunˢ B e closedᵍ
```

at `auditTestᵍ = auditTest B e ∘ T₁ 𝟘ᴳ (sub (procᵘ a))` (`Context.agda:129`) and
`closedᵍ = (plugᴹ a ∘ f) ∘ w` (`Context.agda:140`), for `f : Proc A (X ⊗ᴵ B)`,
an adversary machine `a : Proc X 𝟭ᴵ`, a resource `w : Proc unitᴵ A` and an
environment strategy `e`. The doc priced it at "`unprocᵒ-∘` twice and probably
cheap", and that is what it is: the two `T₁`s merge, `plug-λ` cancels the two
unitors, and the seal is crossed once for the adversary and once for the
resource.

Three corrections to the statement as the doc wrote it, all forced by the types.

* The ancilla is `𝟘ᴳ`, not `ifaceᵒ X`. The grade is what `sub (procᵘ a)`
  consumes; the ancilla is the quantifier `_≈ℰ_` ranges over and the audit
  context deflates it.
* The adversary is `Proc X 𝟭ᴵ`, not `Proc unitᴵ X`. It CONSUMES the adversary
  port (`subᴵ′ a : Proc (X ⊗ᴵ B) (𝟭ᴵ ⊗ᴵ B)` is what composes with `f`), and its
  codomain is the bundle's own unit — `UC.Machine.Dictionary.𝟭ᴵ`, not `unitᴵ`,
  whose iso to it `UC.Model.Unit` prices over the perf bar.
* The machine composite carries the unitor wire that deflates that unit:
  `plugᴹ a = λᴵ ∘ subᴵ′ a` (`src/CategoricalCrypto/UC/Machine/Plug.agda:31`),
  `λᴵ` being the wire `UC.Machine.Dictionary.λ⇒-λᴳ` reads as the bundle's left
  unitor.

With the grade filled at `𝟭ᴵ` the context is `UC.Audit.absorb`'s own shape —
a test precomposed with `T₁ W (sub _)` — at an adversary instead of at a
simulator. Nothing new was defined for it.

`audit-qbᵍ` (`Context.agda:134`) is the matching budget, `qb-∘ (qb-T₁ (qb-sub _))`
at `q * ((c ⊔ 1) ⊔ 1)` — the same expression `Examples.HashForward.Audit`'s
`absorbed-budget` charges a simulator. And `absorb-plugᵍ` (`Context.agda:189`)
says the context is closed under absorbing one: `sub` is functorial, so

```agda
auditTestᵍ B e a ∘ T₁ 𝟘ᴳ (sub (procᵒ s)) ≈ auditTestᵍ B e (a ∘ s)
```

— a simulator in front of an adversary is again an adversary, which is what
keeps the IDEAL side of an absorbed event class one of these contexts too.

### (b) `adequacyᵍ` — delivered, and the second loop is not needed

`src/CategoricalCrypto/UC/Seam/Adequacy.agda:119`, at the doc's statement:

```agda
adequacyᵍ : (A B X : Iface) (f : Proc A (X ⊗ᴵ B)) (a : Proc X 𝟭ᴵ) (w : Proc unitᴵ A)
            (d : Strat (Neg B) (Pos B))
          → runᴹ (pairedᴹ B d ((plugᴹ a ∘ f) ∘ w)) (ask tt out)
            ≈ₚ runᴹ ((plugᴹ a ∘ f) ∘ w) d
```

The doc priced this as "the `play-run` induction redone with two loops rather
than one". It is two lines: `UC.Seam.Adequacy.adequacy` is stated at an
ARBITRARY `u : Proc unitᴵ B`, and `(plugᴹ a ∘ f) ∘ w` is one. The ⊕-trace
solves the adversary's loop and the resource's inside that composite, and
`play-run`'s induction never looks at the process it runs against, so the
three-party closed system is the one-party statement at a composite process.
`compose-≈ᴹ` supplies the collapsed representative in the direction the doc's
spelling asks for.

This is the same observation as "if the existing `plug-run` is the `X = unitᴵ`
special case, say so": `plug-run` is *not* that special case — it crosses the
seal for a closed process where `plug-runᵍ` crosses it for an open one with two
things plugged — but `adequacy` genuinely is, and its statement is untouched.

### (c) Concrete resources — delivered

* `src/CategoricalCrypto/Examples/ROCommitment/Resource.agda`: the lazily
  sampled oracle and the one-shot cell as one `Proc unitᴵ Resᴵ` over `Dₚ`, the
  table and the cell being the state. `hash-hit`/`hash-miss` are the
  `KeepOrSample` shape at the machine layer — a point already answered is
  answered from the table, a fresh one draws `uniformₚ k` and is kept — and
  `cell-put`/`cell-get`/`cell-nak` are the cell. It is `Game.fetchT` one layer
  down; `Examples.ChimericLedger.POV.oracle` is the same lazy table as a `Calls`
  tree, and is not reused because this machine is not a protocol image (the
  system it sits under is not one either).
* `src/ProbabilisticLogic/Dp/Uniform.agda`: `uniformₚ`, `Protocol.uniformVec`'s
  cascade in `Dₚ`. Generic.
* `src/CategoricalCrypto/Examples/HashForward/Resource.agda`: the one-message
  channel and a hash oracle at a hash function given as a parameter. The oracle
  is deterministic because `Dig` is an abstract parameter of that toy — there is
  no distribution on it to sample — which is exactly why the lazily sampled one
  lives at ROCommitment's concrete bit vectors.

Both resources' query certificates are free, and generically so:

```agda
qbᵢ-closed : QBᵢ S point step 0        -- src/CategoricalCrypto/UC/QueryBound.agda:236
qb-closed  : (M : Proc unitᴵ B) → QB 0 M              -- :280
```

A closed process has `Neg unitᴵ` empty, so no output of its is downward, its
potential stays at zero and its rate is zero. This sits beside `qbᵢ-wire` in the
Inhabitation section and mentions no example.

### (e) HashForward's `Pr` inequality at the nontrivial grade — delivered

The generic half is `extractᵍ` (`Context.agda:171`), `extract` at a nontrivial
grade:

```agda
extractᵍ : asks≤ q e → QB c a → QB c′ w
         → 𝔈 𝟘ᴳ (auditTestᵍ B e a) (closedᵒ w) (ctxBudget (q * ((c ⊔ 1) ⊔ 1)) c′)
         → AuditBound (gradedᵒ f) 𝔈 ε
         → (n : ℕ) → Pr≤ n (runᴹ closedᵍ e) ≤ ε (ctxBudget (q * ((c ⊔ 1) ⊔ 1)) c′)
```

It stops in `Dₚ` rather than at layer 1's `Bounded`, and that is not a
concession: `Bounded P bad ε` is about a `Protocol`, and the processes at a
nontrivial grade are raw machines for the reason `docs/hash-forward.md` item 5
records. `Pr≤` on the closed `Dₚ` run is the probability statement those
machines have. `extract` itself is untouched — it still spends `prAgree` to
reach layer 1 at the trivial grade, at a protocol image.

The application is `hf-pr-bound`
(`src/CategoricalCrypto/Examples/HashForward/Audit.agda:125`): for every
designation `μ`/`ε` of the ideal monitored experiment, every environment
strategy, every adversary machine at `Advᴵ` and every resource below,

```agda
Pr≤ n (runᴹ (closedᵍ Honᴵ e a real w) e)
  ≤ (ε (simCost (ctxBudget (q * ((c ⊔ 1) ⊔ 1)) c′) 2) + δ) + η
```

which is review §3's last acceptance criterion verbatim: the theorem is a `Pr`
bound, the simulator is not identified with a silent scalar — it is run in the
ideal experiment, `absorb simᵒ 2` is what puts it there — and the accounting
includes its interaction, at `simCost`. No prefix tolerance is spent, and
`scalar-blindᵒ`/`subBlind` (both `unit ⇒ unit`) are not in the proof.

Two hypotheses remain quantified rather than discharged, and both are the ones
the branch below already had: the designation's membership — which is
`AuditBound`'s own quantifier, and which `docs/hash-forward.md` item 2 records
as the missing non-trivial designation — and the resource, which
`Examples.HashForward.Resource` inhabits.

## Generic versus example-specific

| module | generic? |
|---|---|
| `UC.Machine.Plug` | generic — `λᴵ`, `plugᴹ`; closing a grade with an adversary machine |
| `UC.Model.Graded` (+`procᵘ`, `qbᵘ`, `plug-gradedᵒ`) | generic — three more seal coercions, one per shape |
| `UC.Graded` (+`plug-graded`) | generic — the same fact in the grading's `sub` vocabulary |
| `UC.QueryBound` (+`qbᵢ-closed`, `qb-closed`) | generic — a closed process is 0-bounded |
| `UC.Seam.Grounded` (`plug-λ` domain) | generic — the domain was never used |
| `UC.Seam.Adequacy` (+`adequacyᵍ`) | generic — at any `f`, `a`, `w`, `d` |
| `UC.Seam.Audit.Context` (+ the graded block) | generic — at any interfaces and any event class |
| `ProbabilisticLogic.Dp.Uniform` | generic — `uniformₚ` |
| `Examples.HashForward.Resource` | the toy: channel and hash oracle at a given hash |
| `Examples.HashForward.Audit` (+`hf-pr-bound`) | the toy: the `Pr` bound |
| `Examples.ROCommitment.Resource` | the example: oracle and cell |

Nothing generic mentions an example, and no example restates a generic fact.

## The seal coercions, and why there are three more

`UC.Model.Seal`'s third discipline — a coercion per SHAPE, exported from inside
the block, because a definition's TYPE there is checked with the seal closed —
is what the grade-filling needed, and `UC.Model.Graded` is where the graded
shapes already live:

| name | what it crosses |
|---|---|
| `procᵘ` | an adversary machine `Proc X 𝟭ᴵ` as a hom into the bundle's UNIT |
| `qbᵘ` | its query certificate, as `budgetᵒ` accepts it |
| `plug-gradedᵒ` | filling the grade and deflating the unit IS the machine composite `λᴵ ∘ subᴵ′ a ∘ f` |

`procᵒ` cannot serve for `procᵘ`: its codomain is `ifaceᵒ 𝟭ᴵ`, which outside the
block is not the bundle's `unit` — the same `ifaceᵒ`-opacity `objᵒ`/`ifaceᵒ-onto`
exist for. `UC.Graded.plug-graded` reads `plug-gradedᵒ` back in the grading's
own vocabulary, where the adversary acts through `sub` exactly as a simulator
does (the consolidation plan's decision 2).

## One measured obstacle worth recording

`UC.Model.Setup`'s grading is the curried tensor's, `ucBaseᵒ`'s is
`gradingᵗ 𝔾ᵒ`, and the two agree on the nose but their RECORDS do not. A
`Budget` certificate is stated over `ucBaseᵒ`'s, so a `qb-sub`/`qb-T₁` consumer
must spell the action with that one (`T₁ᵉ`/`subᵉ` in `Context.agda`) or Agda
reports a `MismatchedProjectionsError` between `MonoidalCategory.U` and
`.monoidal`. Equalities between the two spellings still go through — `T₁-⊗ 𝔾ᵒ`
is the bridge, as it already was in `audit-run`.

## Modules

All checked with `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`,
rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate; the warm column is a single-`Checking`-line run.

| module | LOC | measured | rule-5 budget |
|---|---|---|---|
| `ProbabilisticLogic.Dp.Uniform` | 20 | — | 65 s |
| `UC.Machine.Plug` | 32 | — | 68 s |
| `UC.QueryBound` (+46) | 509 | — | 187 s |
| `UC.Model.Graded` (+31) | 87 | 57 s† | 82 s |
| `UC.Graded` (+9) | 71 | 24 s† | 78 s |
| `UC.Seam.Grounded` (±3) | 281 | — | 130 s |
| `UC.Seam.Adequacy` (+17) | 126 | — | 91 s |
| `UC.Seam.Audit.Context` (+92) | 229 | 32 s† | 117 s |
| `Examples.HashForward.Resource` | 78 | 9.5 s | 80 s |
| `Examples.HashForward.Audit` (+36) | 137 | 10.6 s | 94 s |
| `Examples.ROCommitment.Resource` | 103 | 9.4 s | 86 s |

† not a warm single-module run: the figure includes rebuilding dependencies
this branch had just edited (`UC.Model.Graded`'s run rebuilt the whole
`UC.Model.Enrichment` closure, `UC.Seam.Audit.Context`'s rebuilt
`UC.QueryBound`). A dash is a module whose own warm figure could not be
isolated. Two things got in the way and both are worth recording. Concurrent
agents held the pagda memory gate's whole 24 GiB budget with `-M20G` checks for
most of this branch's verification window, so every run below had to queue
through it. And a re-check of an unchanged module does NOT re-elaborate it —
agda 2.8 keys interface staleness on CONTENT, so `touch`ing a file to force a
warm measurement does nothing (measured: `checking=0`, 9–16 s of interface
loading). A warm figure has to be taken on the run that first checks the new
text, which is what the three daggered rows are, or by a real edit.

Every one of these is far inside its rule-5 budget on the run that did check
it, and none of them is anywhere near a perf defect: the largest is
`UC.Seam.Audit.Context` at 32 s against 117 s, and that run also rebuilt
`UC.QueryBound`.

Every module this branch touches, and every closure the brief names, was run
green with an empty gate grep:

| closure | rc | secs | `Checking` lines |
|---|---|---|---|
| `CategoricalCrypto.UC` (the whole UC cone) | 0 | 56 s of compute | many |
| `Examples.MerkleDamgard.QueryBound` | 0 | 31 | 5 |
| `Examples.ChimericLedger.EndToEnd` | 0 | 24 | 7 |
| `Examples.ChimericLedger.Carry` | 0 | 18 | 6 |
| `Examples.ChimericLedger.Factor` | 0 | 17 | 2 |
| `Examples.MerkleDamgard.Pin` | 0 | 11 | 1 |
| `Examples.ROCommitment.Test` | 0 | 12 | 2 |
| each of the eleven modules above, re-checked | 0 | 13–16 | 0 (up to date) |

`src/CategoricalCrypto.agda` — the whole-library root — is the one check that
did not complete: it needs more than a 3 GiB heap (measured: `Heap exhausted`
at `-M3G -H1G` after 120 s and 26 modules), and a retry at a larger heap could
not be admitted through the memory gate inside this branch's window without
crowding a concurrent agent's 20 GiB check off the box. Its exposure to this
branch is the two inventory lines added to it; every module below it was
checked, and `CategoricalCrypto.UC` — which carries every module this branch
edited — is green.

## Not delivered, precisely

### 1. (d) `closed-kernel` — and why it is not the statement to prove

`docs/fcom-extraction.md` item 1(d) asks for

```agda
closed-kernel : (oracle : Proc unitᴵ Resᴵ) (a : Proc unitᴵ Advᴵ)
                (d : Strat (Neg Honᴵ) (Pos Honᴵ)) (q : ℕ) → asks≤ q d
              → Pr≤ q (runᴹ ((subᴵ′ a ∘ real) ∘ oracle) d)
                ≡ Pr₁ (runWith respR sR₀ (compile a d))
```

Three obstructions, in order of how fundamental they are. The first two are
about the STATEMENT and no amount of proof work reaches them.

**(i) At this example the left-hand side does not depend on the system.**
`Examples.ROCommitment.Honᴵ` is `HonA ⇿ ⊥`: the honest port is report-only, the
receiver never answers the environment. So `Neg Honᴵ` is empty, a
`d : Strat (Neg Honᴵ) (Pos Honᴵ)` has no `ask` available to it, and `runᴹ M d`
is `point >>= λ _ → (a coin tree)` for EVERY `M`. The right-hand side is a full
adaptive interaction. The equation cannot hold with a `d` that does anything,
and holds vacuously with one that does not.

The reason is structural rather than a slip: in this example the DRIVER is the
corrupted committer, which sits at the grade, and `runᴹ` drives a closed system
through its codomain interface. The vocabulary for a grade-driven closed run —
something of the shape
`runᴳ : Proc unitᴵ (X ⊗ᴵ B) → Strat (Neg X) (Pos X ⊎ Pos B) → Dₚ Bool` — does
not exist, and inventing it is a core addition, not a bridge. Note that the
model-level statement (f) is NOT affected: a model test is an arbitrary machine
and can drive the grade; it is only the `Strat`-driven closed run that
degenerates here.

**(ii) `compile` cannot exist at an arbitrary machine adversary.** `Strat` is
executable finite syntax whose `coin` carries a `Dist-ℚ Bool` (the plan's
decision 4, kept deliberately); a `Proc`'s step is an arbitrary `Dₚ`
computation, which may diverge and need not be finitely branching. So
`compile : Proc Advᴵ 𝟭ᴵ → Strat _ _ → Strat Q R` is uninhabited. What can exist
is a compile at an adversary given as syntax,

```agda
advᴹ    : Strat AdvQ AdvA → Proc Advᴵ 𝟭ᴵ
compile : Strat AdvQ AdvA → Strat (Neg Honᴵ) (Pos Honᴵ) → Strat Q R
```

and even that has to solve a mismatch of its own: the game's answer alphabet `R`
carries the receiver's reactions (`rcptR`, `outR`, `failR`), which in the machine
system go UP to the honest port and are never seen by the adversary. The
compiled strategy therefore has to merge two channels that the machine system
keeps apart, which is where obstruction (i) returns.

**(iii) The transport itself, once a driver is fixed.** `prAgree` is two nested
`Stable` inductions over a PROTOCOL image: the outer on the `Strat` tree, the
inner on `drive`'s inductive `Calls` tree. At raw machines the inner induction
has no tree — the composite's step is a ⊕-trace solved by `iterₚ`, a fixpoint —
so a `Dₚ`→`Dist-ℚ` transport needs a termination/fuel argument for that loop,
which is `Protocol.Machine.Compose`'s 312-line argument in the form
`docs/hash-forward.md` says the wire decision exists to avoid.

The honest statement to aim at, once (i) is settled by giving the honest
interface a query or by adding a grade-driven run, is (iii) alone, and its
generic pieces belong in `ProbabilisticLogic/Dp/**` (the transport) and
`Protocol/Machine/**` (the compile), not at the example.

### 2. (f) ROCommitment's `raw-emulation`

```agda
raw-emulation :
    (W : Channel)
    (Et : T₀ W (T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)) ⇒ Ωᵒ)
    (m  : 𝟘ᵒ ⇒ T₀ W (ifaceᵒ Resᴵ))
    {c c′ : ℕ} → QB c Et → QB c′ m
  → Obs ((Et ∘ T₁ᵒ W realᵒ) ∘ m)
    ≈ₚ[ εᶜ k (ctxBudget c c′) ]
    Obs ((Et ∘ T₁ᵒ W (sub simᵒ ∘ idealᵒ)) ∘ m)
```

Unreachable for a second reason on top of (d). `raw-emulation` quantifies over
every ancilla `W`, every test `Et` and every closure `m` with a query bound —
and a model test is an arbitrary machine of the seal. `Game.extraction-bound`
quantifies over `Strat Q R` with `asks≤ m d`, i.e. over finite executable
syntax. The seam has `StratIsEnv` in one direction — an embedded strategy IS one
of the environments — and there is no converse: compiling a query-bounded
machine test into a finite strategy would have to enumerate an arbitrary `Dₚ`
step, which is (ii) again. So the game bound bounds the observations of the
strategy-embedded contexts, and `_≈ᵁ_`'s quantifier asks for all of them.

What this leaves is not nothing: the components the plan's witness form asks for
(`simQB`, `εᶜ-negligible`) were already delivered on the branch below, and the
bound now has a `Pr` consumer at a nontrivial grade (`extractᵍ`) that ROCommitment
cannot use only because its bound is a `Dist-ℚ` game bound rather than an
`AuditBound`. An `AuditBound` for the RO commitment — i.e. a designation of the
ideal experiment's observation, as `pinned` takes — would make `extractᵍ` apply
to it verbatim.

### 3. The silent designation is still the trivial one

`hf-pr-bound` is quantified over the designation. Discharging it at
`hf-audit-silent`'s `μ = silent` means computing the ideal monitored
experiment's observation, which is `docs/hash-forward.md` item 2 unchanged. One
piece of it is now cheap and worth recording: absorbing a simulator into a
graded audit context is composing it with the adversary, because `sub` is
functorial — `auditTestᵍ B e a ∘ T₁ 𝟘ᴳ (sub (procᵒ s))` is
`auditTestᵍ B e (a ∘ s)` — so the ideal side of the membership is again a
machine run that `audit-runᵍ` reads. That identification is not in `src/`.

### 4. No `≤UC[ c ]` with an ε, no family

Unchanged from `docs/fcom-extraction.md` items 3 and 5. `UC/Asymptotic/Family.agda`
is untouched, deliberately: `hf-pr-bound` is stated raw and at one level so that
it becomes an instance of the generalized family relations rather than
competing with them.

## Nothing was weakened

No pre-existing statement was edited. `plug-run`, `adequacy`, `prAgree`,
`extract`, `audit-run`, `auditTest` and `audit-qb` keep their statements
verbatim. The one existing signature that changed is
`UC.Seam.Grounded.plug-λ`, whose closure argument was `𝟘ᵒ ⇒ X` and is now
`D ⇒ X` at an arbitrary `D` — a strictly more general lemma, with the same
proof and every existing use unchanged; `plug-runᵍ` plugs an OPEN process into
it, which is what needed the generalization. `UC.Audit`, `UC.Seam.Audit`,
`UC.Asymptotic.*`, `Abstract2*`, `UC.Model.Bridge` and `UCSetup` are untouched.
