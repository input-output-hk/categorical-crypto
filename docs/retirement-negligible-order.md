# Retirement: the negligible tier's emulation order — RETIRED

`Abstract2._≤UC_` at `ucSetupᴺ` is ADOPTED as the negligible tier's canonical
emulation order, and the tier's three own order names are retired in its
favour. A single candidate in the form of
[`docs/retirement.md`](retirement.md), whose §6 kept those names when the tier
still had no inherited order to adopt.

Paths are relative to `src/CategoricalCrypto/` unless prefixed.

## The candidate

`UC/Family/Negligible.agda` exported three names for the tier's emulation order,
all re-exported or derived from `Em UCBaseᴺ`:

| name | site | in-repo consumers |
|---|---|---|
| `_≤UCᴺ_` (renamed from `Em._≤UC_`) | `:71` | `≈ℰⁿ⇒≤UCᴺ`, same module. Nothing else in `src/` |
| `≈ℰᴺ⇒≤UCᴺ` (renamed from `Em.≈ℰ⇒≤UC`) | `:71` | `≈ℰⁿ⇒≤UCᴺ`, same module. Nothing else in `src/` |
| `≈ℰⁿ⇒≤UCᴺ` | `:84-85` | **none**. `UC/Model/Family/Negligible.agda:7-8` names it, in a comment |

`_≈ℰᴺ_` and `≈ℰⁿ⇒≈ℰᴺ` are **not** candidates: both are consumed, by each other
and by `UC.Family.Negligible.Setup`.

## The decision, and what is checked

`retirement.md` §6 retired fourteen metatheorem reexports from this same block
and explicitly kept these three, listing them under "the negligible semantics
are untouched". That was right at the time: the tier had no inherited order of
its own, so `_≤UCᴺ_` was the only emulation order it had, and deleting it would
have deleted a notion rather than a duplicate.

`retirement.md` §7 also states the standard a zero-consumer name has to meet,
and it is not mere absence of consumers:

> none of them **became** consumerless through anything steps 1–6 built — they
> were already unreached before the plan started, so no gate reading "after
> callers migrate" is satisfied by this arc.

`UC/Family/Negligible/Setup.agda` builds `ucSetupᴺ` — `Famᴹ` at `Observationᴺ`
— so the tier now inherits `Abstract2`, and the order it lacked exists there.
That inherited order is adopted as the tier's canonical one, and the three
names are dropped in its favour; adopting a canonical definition and proving it
equivalent to a retired one are different claims, and only the first is made
here. What is checked, in `UC/Family/Negligible/Setup.agda`:

| name | what it gives |
|---|---|
| `ucSetupᴺ` | the tier's canonical setup, hence `Canonicalᴺ._≤UC_` as its order and the whole of `Abstract2` with it |
| `rel-agree` | the bridge's kernel IS this tier's own `_≈ℰᴺ_`, by `refl` — so the order is stated about this relation and not a parallel one, with no transport |
| `sub-agree^ω` | the two spellings of a simulator's action are one morphism under `_≈^ω_` |
| `≈ℰᴺ⇒≤UC` | the tier's agreement reaches the canonical order: `≈ℰᴺ⇒≤UCᴺ`'s premise, inherited conclusion |
| `≈ℰⁿ⇒≤UC` | a budget-indexed bound reaches it: `≈ℰⁿ⇒≤UCᴺ`'s premise, inherited conclusion |

`_≤UCᴺ_`, `≈ℰᴺ⇒≤UCᴺ` and `≈ℰⁿ⇒≤UCᴺ` have no in-repo consumer (the table in
"The candidate", re-confirmed). **No proof is deleted**: the three bodies are
`UC.Emulation UCBaseᴺ`'s, still reachable by applying that module.

**The equivalence of the old and the canonical order is a checked theorem**, in
`UC/Family/Negligible/Setup.agda`, stated directly against `UC.Emulation
UCBaseᴺ` and `Canonicalᴺ._≤UC_` with the three aliases left retired:
`≈ℰᴺ⇒≈ᵁ-sub`/`≈ᵁ⇒≈ℰᴺ-sub` at a fixed simulator, and `≤UCᵉ⇒≤UC`, `≤UC⇒≤UCᵉ`,
`≤UCᵉ⇔≤UC` for the orders — plus `≤UC⇒≤UCᵉ⁺` for the adversary-quantified
presentation of the old one. It is derived from the generic reverse contextual
bridge `UC.Core.Bridge.≈ᵁ⇒≈ℰᶜ` with `rel-agree` (the contextual kernels),
`sub-agree^ω` (the simulator action, post-composed as `sub-agree^ω-∘`) and
`dummy-complete`/`≤UC⇒dummy` (dummy versus quantified presentation); the
simulator is carried across unchanged in both directions. The retirement does
not rest on that equivalence — it rests on the adoption above and on the
recoverability of the three bodies.

## What it does not do, and what the surrounding audit found

It does not retire `UC.Emulation`; `_≈ℰᴺ_` still comes from it. But the audit
that question needed has been done, and it shrinks the problem a long way.

`UC/Emulation.agda:34` is `open import CategoricalCrypto.UC.Environment base
public`, so the module is that re-export plus six order names
(`_≤UC_`, `_≤UC⁺_`, `≈ℰ⇒≤UC`, `≤UC-refl`, `≤UC-trans`, `dummy-complete`).
An importer wanting only `obs`/`tv₁`/`_≈ℰ_`/`grade-stable` can therefore name
`UC.Environment` directly, which is also what rule 19 asks of a re-export
layer. Each importer was classified by making that swap and typechecking.

**Eight were plumbing-only and are migrated** (same names, same module
beneath, nothing deleted): `UC.Seam.Audit.Context`, `UC.Seam.Audit.Prefix`,
`UC.Seam.Grounding.Dead`, `UC.Core.Bridge`, `UC.Robust.Model`,
`UC.Asymptotic.Audit`, `Examples.HashForward.Audit`,
`Examples.ChimericLedger.EndToEnd`.

**Five genuinely use the order**, and they are the whole remaining surface:

| module | what it uses |
|---|---|
| `UC.Audit` | `_≤UC_`, in `≤UC[]⇒≤UC` |
| `UC.Robust.Observation` | `dummy-complete`, `_≤UC⁺_` |
| `UC.Model.Bridge` | the identification of the two orders |
| `UC.Family` | re-exports the six at `UCBase^ω` |
| `UC.Family.Negligible` | re-exports two at `UCBaseᴺ` — this candidate |

Both remaining questions were then chased to an answer.

**`UC.Family`'s re-export — blocked behind a parked call, not technically.**
Deleting the six names from the `using` list at `Family:203-205` breaks exactly
one site, `UC/Model/Family/Ingest.agda:48` (`_≤UC_`, `≈ℰ⇒≤UC`). `retirement.md`
§7 already lists `Ingest`'s `ingest-≤UC`/`ingest-≤UCᵁ` as zero-consumer with a
replacement named, and declines them: their gate reads "after callers migrate"
and the module has never had a caller, so the gate is vacuous rather than met.
That is unchanged by this arc — re-confirmed, still zero consumers — so the
`UC.Family` re-export waits on that maintainer call and on nothing else.

**`UC.Emulation` itself cannot be retired, and this is not a missing gate.**
The issue's premise is that it "can be an instance of `Abstract2._≤UC_`". That
holds only where a monoidal base exists. Its two remaining non-re-export
users, `UC.Audit` and `UC.Robust.Observation`, are parameterized by an
arbitrary `UCBase`, which carries a `Grading` and no monoidal category of
grades and no graded Kleisli triple — so `Abstract2` is not available there at
all, and `_≤UC_`/`_≤UC⁺_`/`dummy-complete` have nothing to be an instance of.
This is the reason `retirement.md` §7 already records for keeping
`UC.Robust.Observation`, and it applies to the module itself.

So the accurate statement is narrower than the issue's: the emulation order is
inherited wherever the base is monoidal — which is what this candidate did at
the negligible tier and what `UC.Family`'s re-export would do at the vanishing
one — and `UC.Emulation` stays for the arbitrary-`UCBase` case.

## Proposed change

`UC/Family/Negligible.agda`: drop `_≤UC_ to _≤UCᴺ_` and `≈ℰ⇒≤UC to ≈ℰᴺ⇒≤UCᴺ`
from the renaming at `:70-71`, and delete `≈ℰⁿ⇒≤UCᴺ` at `:84-85`.

`UC/Family/Negligible/Setup.agda`: drop the translation lemma `≤UCᴺ⇒≤UC` (old
order ⇒ canonical) and its two private helpers `bridged`/`transported` — with
the tier's own order gone there is no second order to translate from, so that
direction goes with it and is left to the derivation above; keep `≈ℰᴺ⇒≤UC`,
`≈ℰⁿ⇒≤UC`, `sub-agree^ω` and `rel-agree`.

Net ≈ −30 lines. `UC/Model/Family/Negligible.agda:7-8`'s comment needs its
names updated.

**Performed**, on the maintainer's instruction. `retirement.md`'s own workflow
is a dedicated branch with one commit per candidate; this was taken on
`protocol-rewrite` instead, and is one self-contained green change.

Also updated: the comments naming the retired relations —
`UC/Model/Family/Negligible.agda:7-10`, `UC.agda`'s inventory, and two in
`UC/Family/Negligible/Setup.agda`.
