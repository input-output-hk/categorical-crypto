# Proposal: the prefix-tolerant audit event class (unit-grade bridge)

> **Deliverable retired 2026-09-21.** The budgeted endpoint this plan aimed at
> (`UC.Seam.Audit.Prefix.uc-audit-bounded`, `UC.Asymptotic.Audit.uc-audit-boundedᵖ`
> and the ledger's `ledger-uc-to-pov-simCost`) is deleted: a budgeted emulation
> forgets to a pointwise one, so the route gave a weaker bound at a stronger
> premise and had no consumer (`docs/end-to-end.md` §4). The plan's general
> content — `prefix-absorbᵒ`, `sim-prefixed`, `bounded-carry` — is kept.

Status: **implemented** (see "Outcome" below). Scope narrowed per
[the follow-up review](protocol-implementation-review.md) §3.1: this plan
covers the **budgeted unit-grade probability bridge only**. It does not handle
an interactive simulator — that is the review's §3 (a separate application at
nontrivial grades with the simulator's interface exposed), which reuses this
plan's initialization tolerance as one component. Prerequisite reading:
`docs/end-to-end.md`'s "Obstruction" section, `UC/Seam/Audit/Bounded.agda`,
`UC/Seam/Grounded.agda` (`subBlind`), `UC/Seam/Grounding/Prefix.agda`.

## Where it sits

The development carries two currencies for "the adversary can't do much":

* **probability** (layer 1): `Protocol.Observe.Bounded`, `UC.Saturated`'s
  `SaturatedHitᴺ` — actual `Pr[hit] ≤ ε` statements; and
* **graded**: `UC.Audit.AuditBound` — bounds stated against the audit grading,
  whose budgeted form carries `simCost`.

The bridge is `UC.Seam.Audit.Bounded`: `boundedIsAudit` / `auditIsBounded`
convert one into the other by *extraction* — given a budgeted test, build the
context realizing it as a member of the audit event class, plug it into the
machine, read the probability off.

## The obstruction (why extraction fails today)

The event class is `absorb s cs (watched I bad)`, and `watched` demands the
extraction context observe **exactly** (`≈ₚ`) an ideal monitored run. The
extraction context has the simulator `s` in front of it. At the unit grade `s`
is a scalar (`unit ⇒ unit`), and `scalar-blindᵒ` shows its entire contribution
is an almost-surely-total silent prefix — but almost-sure totality yields only
ε-closeness, never equality: `UC.Seam.Grounded.subBlind` is precisely that
statement, and it is the best possible. (Exact equality is not impossible for
*every* scalar — `s ≈ id` gives it — but relying on it restricts the emulation
premise to special simulators, which defeats the purpose.)

Consequence: `ledger-uc-to-pov`'s probability bound is obtained through the
trivial-grade collapse, and `uc-audit-carry` (the budgeted route, the one that
charges `simCost`) never reaches a probability.

## The proposal

Widen the event class **for the unit-grade bridge**: membership tolerates an
almost-surely-total silent prefix before the monitored run. The scalar
simulator's contribution is exactly such a prefix, and exactly what `subBlind`
proves discardable. Substrate: `UC.Seam.Grounding.Prefix`'s
`Prefixedᵒ`/`Massedᵒ` machinery (built for the `SubBlind` repair).

Work items, in order:

1. Define the widened class as a NEW designation alongside `watched` — the
   exact `watched` interface and its proved consumers stay intact (review §2
   step 2).
2. Show the scalar-fronted extraction context inhabits it (this is `subBlind` +
   `scalar-blindᵒ` re-read at the new class).
3. Reprove the supply and extraction lemmas (`boundedIsAudit` /
   `auditIsBounded`) at the widened class. The real effort: the class must be
   closed under the context compositions `Absorbs` performs — a silent mass-1
   prefix must remain one after plugging into a context. `Prefix`'s congruence
   lemmas (`prefixedᵒ-⊗ˡ/ʳ`, `prefixedᵒ-sub`) are the substrate.
4. Note the separate inclusion obligation (review §2): extraction currently
   lands in `watched R badR`, not in the pullback class `absorb s cs (watched
   …)` that `ledger-audit-carry` bounds. The widened class must be stated so
   that the concrete monitor's membership at the adjusted budget is PROVED, not
   presumed — `absorb-absorbs` is not a substitute for it.

## What this delivers, and what it does not

Delivers: the unit-grade budgeted route reaches a layer-1 probability — the
extraction gap for ε-close scalar simulators closes, and the two routes of
`docs/end-to-end.md` compose at the unit grade.

Does NOT deliver: a bound accounting for a simulator that actually interacts.
At the current application types (`UC/Asymptotic/Audit.agda`) both endpoints
are inflated by `ιᴳ`, so the budgeted simulator is `unit ⇒ unit` and a positive
`cs` certificate witnesses no interaction. Prefix congruence propagates a
supplied prefix witness; it cannot turn answer-dependent interaction into
silent initialization. The interactive case is the review's §3: expose the
simulator-facing interface at nontrivial grades, retain the interaction inside
the ideal monitored experiment, and use THIS plan's tolerance only for
initialization.

## Outcome

All four items are proved, `--safe --without-K`, postulate-free.

* **Item 1.** `UC.Seam.Audit.TrivialGrade.watchedᵖ`, a new designation beside
  `watched`, with `watched⇒watchedᵖ` exhibiting the widening. `watched` and
  every proved consumer of it are byte-identical.
* **Item 2.** `UC.Seam.Grounded.subPrefixedˢ` — the scalar simulator's whole
  contribution to a context, hoisted out of `subBlind`'s own proof, with
  `subBlind` re-derived from it. `UC.Seam.Grounding.Prefix.prefixedᵒ-bind`
  (likewise hoisted, out of `prefixedᵒ-obs`) reads the prefix off the
  observation as an EXACT `≈ₚ` rather than as ε-closeness, which is what lets
  the class be stated syntactically.
* **Item 3.** `UC.Seam.Audit.Bounded.auditIsBoundedᵖ`/`boundedIsAuditᵖ`, and
  the closure `UC.Seam.Audit.Prefix.absorb-watchedᵖ`. The **syntactic** prefix
  is stable under the `Absorbs` compositions: absorption prepends the
  simulator's initialization (`subPrefixedˢ`) and two prefixes in sequence are
  one by `>>=ₚ-assoc` plus `Dp.Mass.const-bind-astotal`. No prefix-up-to-`≈ₚ`
  and no explicit-η fallback was needed.
* **Item 4.** `UC.Seam.Audit.Prefix.ctx-absorb` proves the extraction context
  lies in the pullback class `absorb s cs (watchedᵖ I bad)` at the adjusted
  budget, and `auditIsBoundedᴬ` extracts a probability from a real-side bound
  at that class. `uc-audit-bounded` is the whole unit-grade budgeted route:
  `Bounded I bad ε` ⟹ `Bounded R bad (λ q → ε (simCost q cs) + ν)` across a
  budgeted emulation, generic in the two protocols.

Supporting general-purpose additions: `Dp.Mass.astotal-returnₚ` (the empty
prefix) and `Dp.Mass.const-bind-astotal` (two almost surely total computations
in sequence, by the `ε/2` product bound); `UC.Audit.q≤simCost`;
`UC.Seam.Audit.Context`, which factors the extraction context and its three
properties out of `Audit.Bounded` with the event class a parameter — the shape
review §2 needs, since the carried class is a statement about the ideal process
while the bound is about the real one.

Not delivered, unchanged from the section above: any accounting for a simulator
that actually interacts (review §3), and a ledger-level consumer.
