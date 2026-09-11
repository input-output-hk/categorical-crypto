# Proposal: the prefix-tolerant audit event class

Status: proposed, not started. This is `docs/end-to-end.md`'s continuation-spec
item 2, expanded to a work plan. Prerequisite reading: that file's
"Obstruction" section, `UC/Seam/Audit/Bounded.agda`, `UC/Seam/Grounded.agda`
(`subBlind`), `UC/Seam/Grounding/Prefix.agda`.

## Where it sits

The development carries two currencies for "the adversary can't do much":

* **probability** (layer 1): `Protocol.Observe.Bounded`, `UC.Saturated`'s
  `SaturatedHitᴺ` — actual `Pr[hit] ≤ ε` statements; and
* **graded**: `UC.Audit.AuditBound` — bounds stated against the audit grading,
  which is what tracks `simCost`, the oracle budget the simulator itself
  spends.

The bridge is `UC.Seam.Audit.Bounded`: `boundedIsAudit` / `auditIsBounded`
convert one into the other by *extraction* — given a budgeted test, build the
context realizing it as a member of the audit event class, plug it into the
machine, read the probability off.

## The obstruction (why the routes don't compose today)

The event class is `absorb s cs (watched I bad)`, and `watched` demands the
extraction context observe **exactly** (`≈ₚ`) an ideal monitored run. The
extraction context has the simulator `s` in front of it, and the simulator's
initialization makes the observation only ε-close — never equal. This is not a
proof we failed to find: `UC.Seam.Grounded.subBlind` is precisely the statement
that an almost-surely-total simulator gets ε-close and no more. The same wall
from the other side: `Absorbs` relates a REAL monitored run to an IDEAL one,
which an emulation supplies only up to vanishing error while `watched` demands
equality.

Consequence: `ledger-uc-to-pov`'s probability bound is obtained through the
trivial-grade collapse, where the simulator is provably blind and costs the
ideal side nothing — so the main theorem's ε is the birthday bound at the
audit-adjusted allowance, **not** a `simCost`-adjusted one. A simulator that
actually burns oracle queries is tracked only by `ledger-audit-carry` at the
graded end, which never reaches a probability.

## The proposal

Widen the event class: membership tolerates a **prefix of almost-surely-total
silent computation** before the monitored run — "observes an ideal monitored
run after discarding a mass-1 silent prefix" instead of "observes an ideal
monitored run". The simulator's initialization is exactly such a prefix, and
exactly what `subBlind` proves discardable. The substrate exists:
`UC.Seam.Grounding.Prefix`'s `Prefixedᵒ`/`Massedᵒ` machinery (built for the
`SubBlind` repair) already discharges mass-1 prefixes against observations.

Work items, in order:

1. Define the widened class (a `Prefixedᵒ`-tolerant `watched`, or a new
   designation alongside it — do NOT change `watched` itself; its consumers'
   statements stay verbatim).
2. Show the simulator-fronted extraction context inhabits it (this is
   `subBlind` re-read at the new class; expect it to be close to definitional).
3. Reprove `boundedIsAudit` and `auditIsBounded` at the widened class. This is
   the real effort: the class must be closed under the operations `Absorbs`
   needs (composition with contexts), i.e. a silent mass-1 prefix must remain a
   silent mass-1 prefix after plugging into a context. `Prefix`'s congruence
   lemmas are the substrate; whatever is missing there is machine-layer work.
4. Re-run the carry chain: `uc-audit-carry` now reaches a layer-1 `Bounded`,
   and the end-to-end theorem gains a `simCost`-adjusted variant (the current
   statement stays; the adjusted one is a second, stronger corollary).

## Risk

Item 3's closure. If "tolerates a prefix" is not stable under the specific
context compositions `Absorbs` performs, the class needs a more careful shape
(e.g. prefix-up-to-≈ₚ rather than syntactic prefix), and the effort grows. The
alternative route named in `docs/end-to-end.md` — an exactly-total simulator
hypothesis — is close to assuming `s ≈ id` and not worth the statement.

## Payoff

`ε̃ = RO-model bound + emulation error` becomes honest even for a simulator
with a nonzero footprint: the main probability bound charges `simCost` instead
of relying on the trivial-grade collapse. Independent of the `≈ℰⁿ`-observation
redesign (`docs/graded-observation-redesign.md`).
