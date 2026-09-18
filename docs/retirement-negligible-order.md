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
"The candidate", re-confirmed). Their bodies were `UC.Emulation UCBaseᴺ`'s;
since the order's own retirement they are reachable nowhere. The former order
survives only as `_≤UCᵉ_` in `UC/Family/Negligible/Setup.agda` — recorded there
as the subject of the equivalence below, and for nothing else.

**The equivalence of the old and the canonical order is a checked theorem**, in
`UC/Family/Negligible/Setup.agda`, stated against that `_≤UCᵉ_` (and its
adversary-quantified form `_≤UCᵉ⁺_`) and `Canonicalᴺ._≤UC_`, the three aliases
left retired:
`≈ℰᴺ⇒≈ᵁ-sub`/`≈ᵁ⇒≈ℰᴺ-sub` at a fixed simulator, and `≤UCᵉ⇒≤UC`, `≤UC⇒≤UCᵉ`,
`≤UCᵉ⇔≤UC` for the orders — plus `≤UC⇒≤UCᵉ⁺` for the adversary-quantified
presentation of the old one. It is derived from the generic reverse contextual
bridge `UC.Core.Bridge.≈ᵁ⇒≈ℰᶜ` with `rel-agree` (the contextual kernels),
`sub-agree^ω` (the simulator action, post-composed as `sub-agree^ω-∘`) and
`dummy-complete`/`≤UC⇒dummy` (dummy versus quantified presentation); the
simulator is carried across unchanged in both directions. The retirement does
not rest on that equivalence — it rests on the adoption above and on the
replacements named in the table.

## What it did not do, and what the surrounding audit found

It did not retire `UC.Emulation` — `_≈ℰᴺ_` still came from it. A follow-up did;
this is the audit that made the follow-up possible.

`UC/Emulation.agda:34` was `open import CategoricalCrypto.UC.Environment base
public`, so the module was that re-export plus six order names
(`_≤UC_`, `_≤UC⁺_`, `≈ℰ⇒≤UC`, `≤UC-refl`, `≤UC-trans`, `dummy-complete`).
An importer wanting only `obs`/`tv₁`/`_≈ℰ_`/`grade-stable` can therefore name
`UC.Environment` directly, which is also what rule 19 asks of a re-export
layer. Each importer was classified by making that swap and typechecking.

**Eight were plumbing-only and are migrated** (same names, same module
beneath, nothing deleted): `UC.Seam.Audit.Context`, `UC.Seam.Audit.Prefix`,
`UC.Seam.Grounding.Dead`, `UC.Core.Bridge`, `UC.Robust.Model`,
`UC.Asymptotic.Audit`, `Examples.HashForward.Audit`,
`Examples.ChimericLedger.EndToEnd`.

**Five genuinely used the order**, and they were the whole remaining surface;
the follow-up settled four of the five:

| module | what it used | what became of it |
|---|---|---|
| `UC.Audit` | `_≤UC_`, in `≤UC[]⇒≤UC` | `≤UC[]⇒≤UC` retired — zero consumers, and `UC.Audit.Canonical.audit-forget` after `audit⇒witness` is its conclusion wherever the base is monoidal |
| `UC.Robust.Observation` | `dummy-complete`, `_≤UC⁺_` | `uc-preserves`/`uc⁺-preserves` retired — zero consumers, and `UC.Robust`'s are the canonical statements, reached by `UC.Core.Bridge.≈ℰᶜ⇒≈ᵁ`/`≈ᵁ⇒≈ℰᶜ` |
| `UC.Model.Bridge` | the identification of the two orders | the identification stays; a further step unfolded `_≤UCᶜ_` in place, which took the last importer with it |
| `UC.Family` | re-exports the six at `UCBase^ω` | dropped, with `Ingest.ingest-≤UC` and `Asymptotic.Family.≤UC^ωⁿ⇒≤UCᶠ`, whose inherited-order twins `ingest-≤UCᵁ`/`≤UC^ωⁿ⇒≤UCᵁ` carry their conclusions |
| `UC.Family.Negligible` | re-exports two at `UCBaseᴺ` — this candidate | now `UC.Environment UCBaseᴺ` |

Both remaining questions were then chased to an answer.

**`UC.Family`'s re-export — blocked behind a parked call, not technically.**
Deleting the six names from the `using` list at `Family:203-205` breaks exactly
one site, `UC/Model/Family/Ingest.agda:48` (`_≤UC_`, `≈ℰ⇒≤UC`). `retirement.md`
§7 already lists `Ingest`'s `ingest-≤UC`/`ingest-≤UCᵁ` as zero-consumer with a
replacement named, and declines them: their gate reads "after callers migrate"
and the module has never had a caller, so the gate is vacuous rather than met.
The maintainer has since ruled: `ingest-≤UCᵁ` is `ingest-≤UC`'s conclusion at
the inherited order on the same premises, so the gate is met by a replacement
rather than by absence, and both went.

**`UC.Emulation` could not be an INSTANCE, and the module went anyway.**
The issue's premise is that it "can be an instance of `Abstract2._≤UC_`", which
holds only where a monoidal base exists; its two remaining non-re-export users,
`UC.Audit` and `UC.Robust.Observation`, are parameterized by an arbitrary
`UCBase` and so had nothing to instantiate. Retiring the statements at those
two left them needing only `UC.Environment`, and unfolding `UC.Model.Bridge`'s
`_≤UCᶜ_` took the last importer, so `UC/Emulation.agda` is deleted.

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
