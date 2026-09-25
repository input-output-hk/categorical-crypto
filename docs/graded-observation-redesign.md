# Proposal: a local negligible observation (and the quantifier triage)

Status: proposed, reshaped per
[the follow-up review](protocol-implementation-review.md) §4. An earlier
version of this document treated a negligible-tier observation as necessarily a
core-interface redesign; that framing was wrong. `UC.Core.Observation` accepts
an **arbitrary equivalence** (`UC/Core.agda:80-93`) — the witness-retaining
limitation belongs to the `Induced` helper, which quantifies its ambient ε
away, not to the interface. So the negligible tier can be a second, LOCAL
instance, and the qualitative core stays untouched.

## The local instance

On the existing family category:

```text
μ ∼ᴺ ν  =  ∃ negligible δ. ∀ i. μ(i) is δ(κ(i))-close to ν(i)
```

Zero error gives reflexivity, symmetry is symmetry, `Negligible-+` gives
transitivity, and exact respect of hom equality gives observation congruence —
all the `Observation` fields, no core change. With it, the generic environment
presheaf (`UC/Environment/Presheaf.agda`) and the inherited UC machinery
instantiate at the negligible tier for free.

## The quantifier triage (the substantive design content)

Three contracts that must not be conflated:

```text
local negligible observation (∼ᴺ):
  for every context, there EXISTS a negligible error for that context;

current _≈ℰⁿ_ (UC/Family.agda):
  ONE global budget-indexed error bounds every context;

current SaturatedBoundedᴺ (UC.Saturated):
  for every polynomial allowance, one negligible slack covers ALL its strategies.
```

The global relation implies local contextual agreement by specializing to each
context's carried allowance. **Neither the converse nor the move from
per-context error to allowance-uniform saturation follows automatically** — a
per-context negligible witness is a weaker deliverable than the
allowance-uniform slack `SaturatedHitᴺ` carries, and no uniformization theorem
exists to close the gap.

## Work items

1. Add the local `Observationᴺ`/UC instance on the family category, reusing the
   generic presheaf and inherited machinery.
   **Done**: `UC.Approximate.Local` (`_∼ᴺ_`), `UC.Family.Negligible`
   (`Observationᴺ`, `UCBaseᴺ`, `_≈ℰᴺ_`, `_≤UCᴺ_`), `UC.Model.Family.Negligible`
   at the machine family; the §1 acceptance criteria are
   `UC.Approximate.LocalTests`.
2. Prove the one-way bridge `_≈ℰⁿ_ ⇒` contextual `∼ᴺ`-agreement. Do not
   identify the relations.
   **Done**: `UC.Family.Negligible.≈ℰⁿ⇒≈ℰᴺ`/`≈ℰⁿ⇒≤UCᴺ`; no converse stated.
3. The public security contract is then a CHOICE (review §4 step 3):
   * to retain allowance-uniform saturation (`SaturatedBoundedᴺ`-shaped
     conclusions), keep uniform evidence in a quantitative refinement of UC and
     prove its simulator/composition laws;
   * a per-adversary negligible property instead matches the local qualitative
     relation — a different, separately stated theorem, never a substitute for
     `SaturatedBoundedᴺ`.
4. A grade-indexed core interface is on the table only if these local
   constructions demonstrate a concrete need to compose quantitative evidence
   generically. Reusing `Induced` is not, by itself, justification for a core
   rewrite.

Separately (same review section): the probability-free `SaturatedProperty` /
`Robust` / `uc-preserves` API is still absent and is independent of the above —
an observation-invariant property, robustness quantified over closing contexts,
the simulator slid into the test, over the inherited relation/bridge. It does
not discharge the monitor-inclusion or error-uniformity obligations.

## Why this is not urgent

The negligible tier consumers currently use lives at layer 1
(`UC.Saturated._≈negl_`, consumed by the end-to-end theorem). The local
instance becomes load-bearing with the family-premise work (review §1), whose
step 2 names it as the vehicle — build it then, with §1's acceptance criteria
in hand (admit a one-shot `2⁻ⁿ` difference, reject a one-shot `1/(n+1)` one).
