# Proposal: `≈ℰⁿ` as an `Observation` (grade-carrying observation interface)

Status: proposed, deliberately deferred. This is `docs/end-to-end.md`'s
continuation-spec item 4, expanded. The pricing below restates and extends
`UC/Family.agda`'s closing comment, which is the authoritative one-paragraph
version.

## What exists

At the family tier (`UC/Family.agda`): `f ≈ℰ[ ε ] g` says every environment at
every allowance distinguishes `f` from `g` by at most `ε`; `_≈ℰ_` is the
vanishing version (ε quantified away); `_≈ℰⁿ_` keeps the witness —
`Σ ε. CarriedNegligible ε × f ≈ℰ[ ε ] g`. Witness-keeping is the point: a
property whose slack must *stay* negligible survives `≈ℰⁿ` but dies through
`≈ℰ` (once "vanishing" is said, no negligible rate can be read back out).
Its equivalence algebra (`refl`/`sym`/`trans` with ε-addition,
`≈ℰⁿ⇒≈ℰ`) is proved by hand in that module; `UC.Saturated._≈negl_` is the
same move at layer 1, also by hand.

## The idea

The core has an `Observation` interface (`UC.Model.Observation`, `Induced`,
`ApproximateObservation`): give it a category and an observation and the
tests/closure/`≋` relation, the environment presheaf `ℰᴼ`
(`UC/Environment/Presheaf.agda`), and every `UC.Emulation` notion (`≤UC`
included) come out generically. If `≈ℰⁿ` were the `≋` of some Observation on
the family category, its algebra and its whole emulation theory would be
instances of the general machinery instead of bespoke lemmas — and the family
tier would plug into everything generic over Observations.

## Why it is a core redesign, not a local one

`Induced` builds its relation by quantifying the ambient ε **away**; retaining
the witness is the opposite move. Making it fit therefore means one of:

* a **second `Observation` on `Fam`** carrying the witness-retaining relation,
  with every `UC.Emulation` notion re-derived over it (`≤UC` included); or
* an **`Observation` interface parameterized by its grade** — a graded/indexed
  observation whose `≋` lives over an error monoid, with the current interface
  as the trivial grade. This touches the core that all of `UC.Model`, the seam
  and the examples are built over.

Either way the change is to the core's observation interface, not to
`UC.Family`. The second option is the principled one (it would also subsume
`ApproximateObservation`, whose `approximate` field is already the graded
half), but it re-types the largest interfaces in the UC cone, with the usual
seal/perf hazards (re-indexing in statements, conversion boundaries).

## Why deferred

Nothing needs it: the negligible tier consumers actually use lives at layer 1
(`UC.Saturated._≈negl_`, consumed by the end-to-end theorem), and the family
tier's hand-rolled lemmas are complete for their current use. The payoff is
dedup and access to generic metatheory, and it arrives only if family-level
reasoning becomes routine — which the seal-object `ContextDominated` ingestion
(end-to-end continuation item 1) would bring about. Decide after that lands,
when the redesign's shape will be better informed. Independent of the
prefix-tolerant audit class (`docs/prefix-tolerant-audit-plan.md`).
