# Hash-then-forward: review §3's nontrivial-grade application

Branch `hash-forward`, off `protocol-rewrite` at `d461b1fa`.
[The implementation review](protocol-implementation-review.md) §3 asks for an
application "at explicit nontrivial grades: process families of the generic
`A ⇒ X ⊛ B` shape and simulator families `Y ⇒ X`", with "a small example with
an inhabited simulator-facing port whose simulator actually performs a query"
and "the query's occurrence/count, not just a positive upper bound".
[`docs/ledger-factoring.md`](ledger-factoring.md)'s closing sections say why the
ledger cannot be that example and what one would need. This is that example.

Everything below is a checked term unless marked otherwise; hatches stay at
zero in `src/`.

## The shape

```agda
real      : Proc Resᴵ (Advᴵ ⊗ᴵ Honᴵ)     -- A ⇒ X ⊛ B, with X = Advᴵ
ideal     : Proc Resᴵ (Lkᴵ  ⊗ᴵ Honᴵ)     -- A ⇒ Y ⊛ B, with Y = Lkᴵ
simulator : Proc Lkᴵ Advᴵ                -- Y ⇒ X
```

`Resᴵ` is the resource below — a channel that stores one message, delivers it
and leaks it, plus a hash oracle. `Honᴵ` is the honest interface (`sendᴴ`,
`recvᴴ`), common to both worlds. `Advᴵ` is the REAL adversary-facing port and
carries one query, `peekᴬ`, answered with a digest. `Lkᴵ` is the IDEAL
simulator-facing port and carries two, `leakˢ` and `hashˢ m`, answered with the
leaked message and with a digest.

* The **ideal functionality** is the resource with its leak exposed: a stateless
  relabelling (`wireᴹ upᶠ downᶠ`) routing `leakˢ`/`hashˢ` and the honest
  traffic onto the resource's own ports.
* The **real protocol** hardens it: on `peekᴬ` it fetches the leak itself and
  hashes it, answering with the digest alone. Honest traffic is relayed
  unchanged. Three states, because that takes two activations.
* The **simulator** runs the real protocol's program against the ideal
  functionality instead of against the resource: `leakˢ`, then `hashˢ` at what
  came back, then `wireᴬ` of the digest.

The emulation direction is the standard one: the real world leaks *less* (a
digest) than the ideal one (the message), so the simulator can produce the real
view from the ideal one, and `real ≤UC ideal` says the protocol is at least as
secure as the leaky channel it is built on. The toy makes NO claim that it is
strictly more so; that is the probabilistic statement it deliberately avoids.

## Where the oracle lives, and what was rejected

**Decision: the oracle is a RESOURCE BELOW, at the shared domain `Resᴵ`,
reachable by the simulator because the ideal functionality relays it on the
simulator-facing port `Lkᴵ`.** Two consequences, both intended: the emulation is
exact and holds for *whatever* the closure plugs in below (so "random oracle" is
nomenclature here, not a hypothesis), and the simulator's oracle query is a real
downward query whose occurrence is countable.

Three alternatives, and why each was rejected.

1. **Oracle inside both systems** (each holds a lazily sampled table and exposes
   it at its adversary port), which is `Examples.MerkleDamgard`'s shape. Then
   `ideal` is stateful, and `sub s ∘ g` is a composite of two stateful machines
   — a genuine ⊕-trace, which at the machine layer is
   `Protocol.Machine.Compose`'s 312-line argument re-run for a `subᴵ` that is
   not a `morphism` image. See "The one structural fact" below: this is the
   whole reason the ideal functionality is a wire.
2. **Oracle at the resource boundary the way `hashPortᵒ` is**
   (`Examples.ChimericLedger.Factor`). That port is an OBJECT boundary with
   every hom graded at `𝟘ᴳ` — `docs/ledger-factoring.md` says so in as many
   words — so it is exactly what does not give a nontrivial grade. Here the
   port is still an object boundary (`Resᴵ` is the domain), but the ADVERSARY
   interface is the grade, which is the difference §3 asks about.
3. **A one-query, stateless simulator.** Tried and dropped: a simulator that
   translates `peekᴬ` into a single oracle query would have to know the message
   before it asks, and a stateless relabelling cannot. A content-bearing
   simulator here is two-step, and that is why the ledger's is not one — its
   `POV.oracle` exposes no adversary interface at all, so its simulator has
   nothing to ask.

`POV.oracle` was not reused for the same reason `docs/ledger-factoring.md`
records: it is lazily sampled and has no adversary interface. `GamePlaying.*`
was not reused either — nothing here is a game hop, because nothing here has an
error term.

## The one structural fact that makes it affordable

`sub s ∘ gradedᵒ g` is, at the machine layer, `subᴵ s ∘ g` in `𝒢ₚ`
(`UC.Model.Graded.sub-gradedᵒ`, one `refl` past
`UC.Machine.Dictionary.sub-⊗₁`). `𝒢ₚ`'s composition is a ⊕-trace, and there are
exactly two ways in this repository to get one in readable form:

* `Protocol.Machine.Compose.morphism-∘`, when BOTH factors are protocol images;
* `UC.Machine.Wire.∘-wireᴹ`, when the lower factor is a WIRE — the loop is then
  solved generically by `GConstructionEmbedding`'s absorption and the composite
  is the upper factor with its interface renamed, same state.

The first is unavailable: `subᴵ s` is not a `morphism` image and cannot be one.
The mismatch is the one `Protocol.Machine`'s own header records — a layer-1
protocol PARKS a continuation when it relays, while `subᴵ` relays the bypassed
interface in the same step and keeps its state — so `morphism (subᵖ S)` and
`subᴵ (morphism S)` are not `≈ᴹ`-equal in either direction (the parking state is
reachable, and `MSt`'s `wait` holds a function that cannot be inverted). They
become equal only after composition, where `traceᴹ` solves the loop inside one
step, which is the argument we are trying not to re-run.

So the second route is what the example is designed around, and the design
decision it forces is precisely "the ideal functionality is a wire". With that,
`real-factors` is

```agda
real ≈ᴹ subᴵ simulator ∘ ideal
```

proved as `∘-wireᴹ upᶠ downᶠ (subᴵ simulator)` followed by ONE pointwise case
analysis (13 clauses, each a `>>=ₚ-identityˡ` or a `bot-bind-≈ₚ`). Statelessness
of the ideal functionality is honest, not a dodge: the channel's state is the
resource's, which is where an ideal channel's state belongs.

**Is the real protocol reverse-engineered from the composite?** Its step table
is what a reader would write for "hash what is on the wire" — fetch the leak,
hash it, report the digest, relay honest traffic — and the simulator's is the
same program addressed to the ideal functionality's ports instead of the
resource's. That they coincide after composition is the theorem; that they are
the same program is why the emulation is exact rather than approximate, and it
is the ordinary situation whenever a simulator reconstructs a view by rerunning
the protocol's own computation. The two are separate definitions at separate
interfaces (`Proc Resᴵ (Advᴵ ⊗ᴵ Honᴵ)` and `Proc Lkᴵ Advᴵ`), and neither is
defined in terms of the other.

One implementation note worth keeping. `realStep` splits the STATE inside each
letter's clause rather than across them (`case s of λ where`), because a clause
with a constructor in the state position makes the pure-relay cases stick at a
variable state, and `real-factors` compares them there.

## What each of review §3's five steps delivers

### 1. The application types at nontrivial grade — DELIVERED

`UC.Model.Seal.gradedᵒ` already crossed the seal for the object part, so no new
relation and no generalization of `_≤UC_` was needed: `_≤UC_`
(`Abstract2`/`UC.Emulation`) is stated at arbitrary grades and always was. What
was missing were two facts about `gradedᵒ`, neither derivable outside the
`opaque` block, added there (`UC.Model.Graded`):

| name | content |
|---|---|
| `≈ᴹ⇒≈ᵍ` | `gradedᵒ` respects the machine equality |
| `sub-gradedᵒ` | `(procᵒ s ⊗₁ id) ∘ gradedᵒ g ≈ gradedᵒ (subᴵ s ∘ g)` |

`UC.Graded` reads the second as a statement about `sub` (`sub-graded`, free —
`sub c` is `c ⊗₁ id` on the nose) and turns a machine-level factoring into an
emulation. `UC.Seam.Grounded.closedᵒ`/`stageᵒ` are NOT touched, weakened or
re-proved; they are the `ιᴳ`-inflated images at `𝟘ᴳ` and remain exactly that.
The relation between them is that `closedᵒ`/`stageᵒ` insert a unit grade where
`gradedᵒ` reads an existing one — they are not instances of each other, because
a protocol image with no adversary interface has no grade to read.

At the toy (`Examples.HashForward.UC`):

```agda
realᵒ  : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)
idealᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Lkᴵ)  (ifaceᵒ Honᴵ)
simᵒ   : ifaceᵒ Lkᴵ ⇒ ifaceᵒ Advᴵ
```

`ifaceᵒ Advᴵ` is inhabited — `AdvQ` has `peekᴬ` and `AdvA` has `wireᴬ` — so
`simᵒ` is not a scalar and `UC.Seam.Grounding.Prefix.scalar-blindᵒ` and
`UC.Seam.Grounded.subBlind`, which are expressly `unit ⇒ unit`, do not apply to
anything here.

### 2. The emulation theorem — DELIVERED, exactly

```agda
real-agrees : realᵒ ≈ᵁ sub simᵒ ∘ idealᵒ
real-≤UC    : realᵒ ≤UC idealᵒ
```

in the INHERITED order (`UC.Model.Setup`'s, i.e. `Abstract2`'s — where
`UC-compose` is), with `dummy-complete` supplying the quantifier. There is no
ε: the emulation is one machine equality read through `≈C⇒≈ᵁ`, so the model's
relation is not forced to carry an error and none is invented to fill it.

### 3. Query allowance, and the OCCURRENCE proof — DELIVERED

The allowance is `2`: `simCert : Certified 2 simulator` (the amortised
potential `UC.QueryBound.QBᵢ`, `Φ` being what a `peekᴬ` in flight still owes),
and `simQB : QB 2 simulator`. `UC.Seam.Graded.≤UC[]ᵍ` attaches it:
`hf-emul : realᵒ ≤UC[ 2 ] idealᵒ`. The composed monitored experiment's budget is
`audit-carry`'s own `qb-∘ (qb-T₁ (qb-sub …))`, restated at the toy as
`absorbed-budget`, and `simCost` reads it as the rescaling of the context's.

Query bounds are not runtime bounds and nothing here claims PPT.

The occurrence/count is new and generic: **`UC.QueryBound.Exact`**. Where
`QBᵢ` is an amortised upper bound and `Counting` reads it as
`#downward ≤ c · #upward`, `QEᵢ` replaces the potential's inequalities by an
EQUATION per step, against two weightings — `δ` on the outputs being counted,
`cost` on the letters that pay for them — and a ledger `Λ` of what a state still
owes:

```agda
Λ s + cost x ≡ δ o + Λ s′                           -- per step
weight δ (outputs) + Λ (final) ≡ weight cost (word) -- per run (exactᴱ)
mapₚ … (exactᴱ w) ≈ₚ behᵍ S point step w            -- and it IS the run
```

`qeᵢ-wire` inhabits it generically: a stateless relay emits exactly one downward
output per activation from above and none otherwise. At the toy, two
instantiations of the SAME ledger:

| statement | weighting | reading |
|---|---|---|
| `sim-hash-count` | `δ = hashes`, `cost = peeks` | exactly one `hashˢ` query per `peekᴬ` |
| `sim-query-count` | `δ = downward`, `cost = twoPerPeek` | exactly two queries of any kind per `peekᴬ` |

`sim-hash-count-settled` reads the first without the residual: when the run ends
at a settled state (`Λ ≡ 0`, i.e. between transactions) the count is
`weight peeks w` on the nose. `sim-round` is the same thing computed at one
concrete transaction — a `peekᴬ` answered in order produces `leakˢ`, then
`hashˢ` AT THE LEAKED MESSAGE, then the digest — which is the witness that the
words the count quantifies over are inhabited by a live run and not only by
divergent ones.

**What "the simulator performs a query" means here, exactly.** It is a statement
about the trace of the very machine the emulation carries — `sim hf-emul` is
`procᵒ simulator` on the nose — rather than about the emulation relation: for every
activation word `w` and every branch of `behᵍ` (the machine's own behaviour
function, the one `UC.QueryBound.CountBound` is also stated at), the multiset of
outputs contains exactly `weight peeks w` outputs of the form `inj₁ (hashˢ m)`,
up to a peek still in flight. Divergent branches carry no mass in `Dₚ`, so an
off-protocol word constrains nothing and the statement needs no admissibility
side condition. It is an equation in both directions, so it rules out a
simulator that asks nothing as firmly as one that asks too much.

### 4. The absorbed context as an admissible ideal experiment — DELIVERED, and
### narrower than the trivial-grade route

`audit-carry` tests the ideal side through `Et ∘ T₁ W (sub simᵒ)` — the real
side's monitoring context with the simulator in front of it. `absorbed-budget`
states its certificate: `Bud.qb-∘ q (Bud.qb-T₁ (Bud.qb-sub (qbᵒ simQB)))`, at
`c * ((2 ⊔ 1) ⊔ 1)`, which `ctxBudget` reads as `simCost` of the original
(`UC.Audit`'s `shuffle`, private there and used by `audit-carry` itself).
Membership is `absorb-absorbs`: `absorb s cs 𝔉` is the largest class closed into
`𝔉`, so nothing is assumed of the real side.

**No prefix tolerance is spent anywhere.** `UC.Seam.Audit.TrivialGrade.watchedᵖ`
and `UC.Seam.Grounded.subPrefixedˢ` exist because a trivial-grade simulator's
whole contribution to a context is an initialization one hopes is silent. This
simulator's contribution is its actual interaction, it is RUN in the ideal
experiment, and `sim-hash-count` says exactly how much of it there is.

### 5. The generic graded carry at `X ≠ unit` — DELIVERED; the probability
### extraction is NOT, and the obstruction is precise

```agda
hf-audit-carry : (μ : ℕ → Dₚ Bool) (ε : ℕ → ℚ) (δ η : ℚ) → 0ℚ < δ → 0ℚ < η
               → ((q n : ℕ) → Pr≤ n (μ q) ≤ ε q)
               → AuditBound realᵒ (absorb simᵒ 2 (pinned idealᵒ μ))
                   (λ q → (ε (simCost q 2) + δ) + η)
```

`UC.Audit.audit-carry` was already generic in the grade; what was missing was an
application at one that is not `unit`, and this is it. The event class is new
and generic: `UC.Audit.pinned f μ` designates a context by the observation the
experiment is expected to make, which is
`UC.Seam.Audit.TrivialGrade.watched`'s shape with layer 1's monitor run
abstracted away — `watched` is stated at a closed PROTOCOL image and its
extraction context is a trivial-grade one, so it is not available at a
nontrivial grade. `pinned-bound` supplies `AuditBound` from a bound on the
designated observations alone; its `δ` is the `Mass`-level price of reading an
equivalence as a numeric comparison (`dominate`), which at the intended model is
exact (`UC.Seam.Audit.Bounded.supply`, off a zero-slack `≼ₚ[ 0ℚ ]`) and is not
a defect of the instance.

`hf-audit-silent` is the toy's own designation: the ideal monitored experiment
reports `false`, `ε ≡ 0`. That half is deliberately trivial and is flagged as
such below.

**What is NOT delivered: the layer-1 probability.** The real-side conclusion is
an `AuditBound`, not a `Protocol.Observe.Bounded`. Turning one into the other is
`UC.Seam.Audit.Context.extract`, and it is restricted to the trivial grade for a
reason that is structural, not incidental: its extraction context is
`auditTest = (procᵒ env ∘ unitorˡ.from) ∘ unitorˡ.from`, i.e. the embedded
strategy behind two unitors that DEFLATE the grade, and `unitorˡ.from` at a
grade `X` exists only for `X = 𝟘ᴳ`. At `X ≠ 𝟘ᴳ` the extraction context must
plug an ADVERSARY machine into the grade, and identifying the resulting
observation with a layer-1 run needs an `adequacy`/`plug-run` for a two-sided
closed composite — an environment above and an adversary at the grade — where
`UC.Seam.Adequacy` states only the one-sided closed case.

**The smallest change that would remove it**: a `plug-runᵍ` beside
`UC.Seam.Grounded.plug-run` reading `obs (tv₁ W (gradedᵒ f) (Et ∘ T₁ W (sub a))) m`
as `runᴹ` of the machine composite `subᴵ a ∘ f` closed by `m`, plus
`UC.Seam.Adequacy`'s identification of that run with a layer-1 one. The first is
`unprocᵒ-∘` twice and is probably cheap; the second is the genuine addition,
because `adequacy` is stated for `Proc unitᴵ B` and an adversary at the grade
makes the closed system a three-party one. Nothing here is blocked by the seal
and nothing would need the core changed.

## Generic versus example-specific

| module | generic? |
|---|---|
| `UC.Model.Graded` | generic — two seal coercions for `gradedᵒ`, no example in sight |
| `UC.Graded` | generic — `Factors`, `sub-graded`, `emulᵍ`, `≤UCᵍ` at any interfaces |
| `UC.Seam.Graded` | generic — `≤UC[]ᵍ` at any interfaces |
| `UC.QueryBound.Exact` | generic — the ledger certificate, its run theorem, `qeᵢ-wire` |
| `UC.Audit` (`pinned`, `pinned-bound`) | generic — stated over an arbitrary base, budget and mass |
| `Examples.HashForward` | the toy: interfaces, three machines, `real-factors` |
| `Examples.HashForward.UC` | the toy: emulation, `Certified 2`, the two exact counts |
| `Examples.HashForward.Audit` | the toy: `≤UC[ 2 ]`, the absorbed budget, the carry |

Nothing generic mentions the toy, and nothing in the toy restates a generic
fact.

## Modules

All checked with `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`,
rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate; the warm column is a single-`Checking`-line run.

| module | LOC | warm | rule-5 budget |
|---|---|---|---|
| `UC.Model.Graded` | 50 | 8.8 s | 72 s |
| `UC.Graded` | 60 | 9.1 s | 75 s |
| `UC.Seam.Graded` | 28 | 9.8 s | 67 s |
| `UC.QueryBound.Exact` | 168 | 9.3 s | 102 s |
| `UC.Audit` (+27) | 214 | 4.8 s | 113 s |
| `Examples.HashForward` | 220 | 10.0 s | 115 s |
| `Examples.HashForward.UC` | 250 | 15.5 s | 122 s |
| `Examples.HashForward.Audit` | 101 | 10.0 s | 85 s |

## Not delivered, precisely

1. **The layer-1 probability at a nontrivial grade** — see step 5 above for the
   obstruction and the smallest change that removes it. This is the one item
   that touches review §3's acceptance criteria directly: the carry runs at
   `X ≠ unit` and its accounting includes the interaction, but the bound it
   produces is an `AuditBound`, not a `Pr`/`PrHit` inequality.
   **Delivered since**, as `Examples.HashForward.Audit.hf-pr-bound` off the
   generic `UC.Seam.Audit.Context.extractᵍ` — see `docs/graded-bridge.md` (e).
2. **A non-trivial audit designation.** `hf-audit-silent` supplies `ε ≡ 0` at
   the designation "the ideal monitored experiment reports `false`". A
   designation with content would pin the observation to the run of a monitor
   against the CLOSED ideal experiment, which means computing the observation of
   a composite — the same trace work step 5's obstruction is about. The generic
   half (`hf-audit-carry`, quantified over `μ` and `ε`) is stated so that a
   better designation drops straight in.
3. **No asymptotic family.** `UC.Asymptotic.Audit._≤UC^ω[_]_` is stated at
   `closedᵒ (morphism (R n))` — the trivial grade, and protocol images — so it
   cannot be instantiated here, and `uc-audit-carry`/`uc-audit-boundedᵖ` with
   it. `UC.Audit.audit-carry`, which those two wrap, is what the toy applies
   directly. A graded family relation would be the levelwise `_≤UC[ cs n ]_` at
   `gradedᵒ`; it was not added because the toy has no security parameter, so
   every level would be the same statement and the polynomial allowance would
   have nothing to grow in.
4. **No concrete resource.** `Resᴵ` is an interface; the emulation is exact for
   every closure, which is stronger than fixing a lazily sampled oracle, but it
   also means no `Dₚ`-level oracle is exercised. Plugging `POV.oracle`-style
   sampling in below would need the closed system, i.e. item 1's machinery.
   **Delivered since**: `Examples.HashForward.Resource` (deterministic hash —
   `Dig` is abstract here) and `Examples.ROCommitment.Resource` (lazily
   sampled), `docs/graded-bridge.md` (c).
5. **`real` is a raw machine, not a `morphism` image.** Deliberate — the
   parking mismatch above — and it is why `Protocol.Observe.Bounded`,
   `TotalRun`, `prAgree` and the rest of the layer-1 vocabulary are not in play
   at the toy. Item 1's `Pr` bound is therefore `Pr≤` on the closed `Dₚ` run,
   which is the probability statement a raw machine has. A protocol-image version of `real` would not factor through
   `subᴵ simulator`, so this is not a presentation choice that could be changed
   without redoing the trace argument.

## Against the consolidation plan's architectural decisions

`docs/uc-presheaf-preservation-plan.md` postdates this branch's base
(`d461b1fa`); everything here was checked against it afterwards and nothing had
to change.

* **Decision 1** (use `UCSetup`/`Abstract2` and the existing graded Kleisli
  action, preserve `_≈ᵁ_` and the inherited `_≤UC_` quantifiers) — `emulᵍ`
  lands in `_≈ᵁ_` and `≤UCᵍ` in the inherited `_≤UC_`, through the existing
  `dummy-complete`, so the quantifier is the one that was there.
* **Decision 2** (absorbing a simulator is the presheaf's action on `sub`, not
  an independent operation) — the only absorption used is the pre-existing
  `UC.Audit.absorb`, i.e. `Et ∘ T₁ W (sub s)`; nothing new was defined for it.
* **Decision 3** (no generic `Simulator`, `ClosingContext`,
  `MonitoredExperiment` or `Monitor` records, no new experiment category) — the
  whole branch adds exactly one record, `UC.QueryBound.Exact.QEᵢ`, and the only
  new `data` declarations are the toy's own message types and its machine's
  state. The simulator is a plain `Proc Lkᴵ Advᴵ`, `procᵒ` of it is a grade
  morphism, tests and closures are `UC.Emulation`'s own, and no monitor appears
  at all: `pinned` designates an observation, where `watched` designates a
  concrete `Strat → Strat`. No `Category` is constructed anywhere.
* **Decision 4** (`Strat` stays executable finite syntax) — untouched; the toy
  uses no strategy.
* **Decision 5** (query certificates are optional model enrichment, not fields
  of `UCSetup`) — `QEᵢ` is a standalone module, `UCSetup` and `Budget` are
  untouched, and the allowance the emulation carries still goes through the
  ordinary `Certified`/`QB`/`qbᵒ` pipeline. Nothing forgets a witness: the
  emulation is exact, so there is no error to forget.
* **Decision 6** (several observation instances on one family category) — no
  observation was added or changed.
* **§4.4** asks precisely for this example, "reuse the ordinary grading action
  and query certificates. Neither a new simulator datatype nor a new category is
  needed" — neither was needed. The oracle-facing grade is exposed by changing
  the application interface explicitly (`Advᴵ`/`Lkᴵ` are the grades), not by
  assigning a positive budget to a `unit → unit` scalar, and `absorbed-budget`
  is the "admits the simulator's actual interaction at the adjusted budget"
  half.

## Nothing was weakened

No pre-existing statement was edited. The two edits to existing files are
additive: `UC/Audit.agda` gains `pinned`/`pinned-bound` beside `AuditBound`
(and one `proj₁; proj₂` in an import), and `UC/Seam/Audit.agda` re-exports the
two new names. `UC.agda` and `CategoricalCrypto.agda` gain inventory entries and
`open import` lines.
