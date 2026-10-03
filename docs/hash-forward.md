# Hash-then-forward: a simulator that spends a query

`Examples.HashForward` and `Examples.HashForward.UC`
are an application at an explicit nontrivial grade: a process of the generic
`A ⇒ X ⊛ B` shape, a simulator `Y ⇒ X` with an inhabited simulator-facing port that
actually performs a query, and the query's count stated exactly, not only as an upper
bound. The chimeric ledger cannot be this example: its hash port is an object boundary
graded at `𝟘ᴳ`, where every simulator is a scalar and blind to the run
(`UC.Graded`'s header).

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
   `Protocol.Machine.Compose`'s argument re-run for a `subᴵ` that is not a
   `morphism` image. See "The one structural fact" below: this is the
   whole reason the ideal functionality is a wire.
2. **Oracle at the resource boundary the way `hashPortᵒ` is**
   (`Examples.ChimericLedger.Transfer`). That port is an OBJECT boundary with
   every hom graded at `𝟘ᴳ`, so it is exactly what does not give a nontrivial
   grade. Here the port is still an object boundary (`Resᴵ` is the domain), but
   the ADVERSARY interface is the grade.
3. **A one-query, stateless simulator.** Tried and dropped: a simulator that
   translates `peekᴬ` into a single oracle query would have to know the message
   before it asks, and a stateless relabelling cannot. A content-bearing
   simulator here is two-step, and that is why the ledger's is not one — its
   `ChimericLedger.System.oracle` exposes no adversary interface at all, so its
   simulator has nothing to ask.

The ledger's lazily sampled `System.oracle` was not reused for that reason.
`GamePlaying.*` was not reused either — nothing here is a game hop, because
nothing here has an error term.

## The one structural fact that makes it affordable

`sub s ∘ gradedᵒ g` is, at the machine layer, `subᴵ s ∘ g` in `𝒢ₚ`
(`UC.Model.Graded.sub-gradedᵒ`, one `∘-resp-≈ˡ` past
`UC.Machine.Dictionary.sub-⊗₁`). `𝒢ₚ`'s composition is a ⊕-trace, and there are
three ways in this repository to get one in readable form:

* `Protocol.Machine.Compose.morphismCompose`, when BOTH factors are protocol images;
* `UC.Machine.Wire.∘-wireᴹ`, when the lower factor is a WIRE — the loop is then
  solved generically by `GConstructionEmbedding`'s absorption and the composite
  is the upper factor with its interface renamed, same state;
* `UC.Machine.Composite.unfoldᶜ`, for any two processes: the composite as one
  product-state machine, read through `Unfolding`'s six equations.

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
analysis (13 clauses, each a unit law or a `botₚ` absorption). Statelessness
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

`realStep` splits the STATE inside each
letter's clause rather than across them (`case s of λ where`), because a clause
with a constructor in the state position makes the pure-relay cases stick at a
variable state, and `real-factors` compares them there.

## The emulation

`UC.Model.Seal.gradedᵒ` already crosses the seal for the object part, so no new
relation and no generalization of `_≤UC_` is needed: `Abstract2._≤UC_` is stated at
arbitrary grades. What `gradedᵒ` needs is two facts, neither derivable outside the
`opaque` block, so `UC.Model.Graded` exports them from inside:

| name | content |
|---|---|
| `≈ᴹ⇒≈ᵍ` | `gradedᵒ` respects the machine equality |
| `sub-gradedᵒ` | `(procᵒ s ⊗₁ id) ∘ gradedᵒ g ≈ gradedᵒ (subᴵ s ∘ g)` |

`UC.Graded` reads them in the setup's vocabulary and turns a machine-level factoring
(`Factors f s g`, i.e. `f ≈ subᴵ s ∘ g`) into an emulation (`emulᵍ`, `≤UCᵍ`).
`UC.Seam.Grounded.stageᵒ` is a different reading, not an instance of it:
it inserts a unit grade (`ιᴳ`) where `gradedᵒ` reads an existing one, and a protocol
image with no adversary interface has no grade to read.

At the toy (`Examples.HashForward.UC`):

```agda
realᵒ  : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)
idealᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Lkᴵ)  (ifaceᵒ Honᴵ)
simᵒ   : ifaceᵒ Lkᴵ ⇒ ifaceᵒ Advᴵ

real-agrees : realᵒ ≈ᵁ sub simᵒ ∘ idealᵒ
real-≤UC    : realᵒ ≤UC idealᵒ
```

`ifaceᵒ Advᴵ` is inhabited — `AdvQ` has `peekᴬ` and `AdvA` has `wireᴬ` — so `simᵒ`
is not a scalar. The order is the INHERITED one (`UC.Model.Setup`'s, i.e.
`Abstract2`'s), with `dummy-complete` supplying the quantifier. There is no ε: the
emulation is one machine equality read through `≈C⇒≈ᵁ`, so none is invented.

## What the simulator spends

The count is generic: **`UC.QueryBound.Exact`**. Where `QBᵢ` is an amortised upper
bound and `UC.QueryBound.Counting` reads it as `#downward ≤ c · #upward`, `QEᵢ`
replaces the potential's inequalities by an EQUATION per step, against two
weightings — `δ` on the outputs being counted, `cost` on the letters that pay for
them — and a ledger `Λ` of what a state still owes:

```agda
δ o + Λ s′ ≡ Λ s + cost x                           -- per step
weight δ (outputs) + Λ (final) ≡ weight cost (word) -- per run (exactᴱ's runs)
mapₚ … (runs (exactᴱ w)) ≈ₚ behᵍ S point step w     -- and it IS the run (erases)
```

`exactᴱ w : Counted Λ w` packs both, so a count is a statement about the machine's
own behaviour and not only about some distribution of balanced runs.

At the toy, two instantiations
of the SAME ledger `Φˢ`:

| statement | weighting | reading |
|---|---|---|
| `sim-hash-count` | `δ = hashes`, `cost = peeks` | exactly one `hashˢ` query per `peekᴬ` |
| `sim-query-count` | `δ = downward`, `cost = twoPerPeek` | exactly two queries of any kind per `peekᴬ` |

`sim-hash-count-settled` reads the first without the residual: when the run ends at a
settled state (`Λ ≡ 0`, i.e. between transactions) the count is `weight peeks w` on
the nose. `sim-round` computes one concrete transaction — a `peekᴬ` answered in order
produces `leakˢ`, then `hashˢ` AT THE LEAKED MESSAGE, then the digest — which
witnesses that the words the count quantifies over are inhabited by a live run and
not only by divergent ones.

The upper bound `hf-bounded` consumes is derived from the exact one:
`simCert : Certified 2 simulator` is `exact⇒certified simExactAll`, and
`simQB : QB 2 simulator` its closure. Query bounds are not runtime bounds and nothing
here claims PPT.

**What "the simulator performs a query" means, exactly.** It is a statement about the
trace of the very machine the emulation carries (`simᵒ` is `procᵒ simulator` on the
nose), not about the emulation relation: for every activation word `w` and every
branch of `behᵍ`, the outputs contain exactly `weight peeks w` of the form
`inj₁ (hashˢ m)`, up to a peek still in flight. Divergent branches carry no mass in
`Dₚ`, so an off-protocol word constrains nothing and the statement needs no
admissibility side condition. It is an equation, so it rules out a simulator that
asks nothing as firmly as one that asks too much.

## The event bound at the machine

`Examples.HashForward.UC` states the toy as an event bound against an adversary:

```agda
hf-bounded  : AdvBoundedAt (k * 2) q r ideal → AdvBoundedAt k q r real
hf-exact    : runᴹ ((plugᴹ a ∘ real) ∘ w) d ≈ₚ runᴹ ((plugᴹ (a ∘ simulator) ∘ ideal) ∘ w) d
hf-pr-bound : Upper (runᴹ ((plugᴹ (a ∘ simulator) ∘ ideal) ∘ w) d) r
            → Upper (runᴹ ((plugᴹ a ∘ real) ∘ w) d) r
```

`hf-bounded` is `UC.Machine.EventBounds.bounded-absorb real-factors simQB`: the
simulator joins the adversary (`plug-absorb`), so the adversary's rate is multiplied
by the simulator's `2`, the context cap is untouched, and the exact factoring costs no
slack. `hf-exact` is the same move on the closed runs, for every resource `w`
plugged in below, and `hf-pr-bound` carries ANY one-sided bound of the ideal run to
the real one.

No prefix tolerance is spent. A trivial-grade simulator's whole contribution to a
context is an initialization one hopes is silent; this simulator's contribution is
its actual interaction, it is RUN in the ideal experiment, and `sim-hash-count` says
exactly how much of it there is.

## Why `real` is a raw machine

`real` is a `Proc`, not a `morphism` image — deliberately, by the parking mismatch
above — so `Protocol.Observe.Bounded`, `prAgree` and the rest of the layer-1
vocabulary are not in play at the toy, and the probability statement is `Upper` on the
closed `Dₚ` run, which is what a raw machine has. A protocol-image version of `real`
would not factor through `subᴵ simulator`, so this is not a presentation choice that
could be changed without redoing the trace argument.

The toy has no security parameter, so it states no family relation: every level would
be the same statement and a polynomial allowance would have nothing to grow in.

## Generic versus example-specific

| module | generic? |
|---|---|
| `UC.Model.Graded` | generic — the seal coercions for `gradedᵒ` |
| `UC.Graded` | generic — `Factors`, `emulᵍ`, `≤UCᵍ` at any interfaces |
| `UC.QueryBound.Exact` | generic — the ledger `QEᵢ`, its run theorem, `exact⇒certified` |
| `UC.Machine.EventBounds` | generic — `advReader`, `AdvBoundedAt`, `plug-absorb`, `bounded-absorb` |
| `Examples.HashForward` | the toy: interfaces, three machines, `real-factors` |
| `Examples.HashForward.UC` | the toy: emulation, the two exact counts, `Certified 2`, the adversary-absorbed event bound |

Nothing generic mentions the toy, and nothing in the toy restates a generic fact.
