# Simplifying the model: an optional variant, and options that keep its reach

Written 2026-09-29 after the maintainer asked whether the theory behind the machine
model "has to be so complicated". Sizes are from `protocol-rewrite` at `c71d95fe`,
grouped by mathematical layer rather than by directory.

| Layer | LOC |
|---|---|
| Machine tower (`SFunM`, `Machines`, `GConstruction*`, `Machine`, `Channel`) | 11.4k |
| Partiality (`Dₚ`, `Iter`, `Cofinal`/`Dom`, `ASTotal`, `SFunPartial`, `GamePlaying/Partial`, `Uniform/Decay`) | 4.1k |
| ε-layer (`Approximate*`, `Approx/**`, `Negligible*`) | 1.9k |
| Grading (`LocallyGraded`, `Rates`, `Family*`, `Quantitative/**`, `QueryBound*`) | 5.9k |
| Model glue (`UC/Model`, `UC/Seam`, `UC/Machine`) | 5.7k |
| Generic UC core (`UCSetup`, `Abstract2`, `Core`, `Audit`, `Robust`) | 2.0k |

Two layers are essential as they stand. The generic core is a category, a graded monad
that attaches adversaries, a presheaf of environments, and the order "for every adversary
a simulator agreeing in every environment"; nothing there is removable. The machine
tower is the price of string-diagram wiring with interface polarity; without it there is
no model to run examples in.

Everything else is downstream of one design decision: **composition of machines along an
interface is resolved by Elgot iteration in a partial monad.** Messages ping-pong between
the two machines, the loop is closed by `Dₚ`'s iteration, and so probabilities are
suprema of finite approximants. That single choice forces the partiality layer, the
sup-free spellings (`Cofinal`, `Dom`, `Mass`, `Approximants`), the "δ-close for every δ"
form of `≈ᵁ` at the model, the `Seam` modules that ground `Dₚ` observations in an
`Evaluation`, and a separate error algebra in the ε-layer. No example iterates; the
partiality machinery is exercised only by the glue.

## 1. Optional variant: total, rate-certified machines (changes what can be modelled)

Not adopted (maintainer, 2026-09-29: "for now I don't want to change what we can model").
Recorded because it is the one change that simplifies the mathematics rather than the code.

The framework already carries the datum that bounds the ping-pong: the rate certificate
`QB r f` ("at most `r` messages out per message in"). Make certificates intrinsic — the
model category is the graded category `L` of `GradedSubCat Rates`, not machines plus a
side predicate — and composition along an interface is a bounded unrolling of at most
`r · r′` exchanges, hence total. Consequences:

- Machines are Mealy coalgebras over finite rational distributions. `Dₚ`, `Iter`,
  `Cofinal`, `Dom`, `ASTotal`, `Mass`, `Approximants` disappear.
- A reading is a finite `Dist Bool`; `≈ᵁ` is equality of distributions; the ε-layer is
  statistical distance, a rational pseudometric on `S`, with `Negligible` on schedules
  as today. The three flavours of approximate equality (`≈ₚ`, `≈ₚ[δ]`, `≈[ε]`) become one.
- Budget `q` and run length coincide (both count environment activations); `at n` is
  "run for `n` activations", not a stage of an approximant.
- Most of `Seam` goes: there is nothing to ground.
- Estimated saving: partiality layer, half the ε-layer, most of the glue — 8–10k LOC —
  and the abstract theory no longer needs sup-free statements.

Costs: the category laws of bounded-unrolling composition must be proved (associativity
is the work; the certificate makes the "budget exceeded" branch unreachable, so the laws
should hold exactly, but that is a spike, not a certainty); machines of unbounded rate
are no longer in the universe, so a protocol that loops without a retry cap must be
stated with a cap and a `2⁻ⁿ` failure schedule; the slogan "machines form a traced SMC
with Elgot iteration" is lost. This is the standard model's own choice (every machine
is PPT), so the loss of reach is the one the literature already accepts.

Go/no-go spike: composition of certified machines by bounded unrolling over
`RationalDist`; category laws; interface tensor; measure the size.

## 2. Options that keep the current reach

Ranked by structure removed per unit of work. None changes which machines or protocols
can be modelled.

### 2.1 Internalise the ε-layer into the environment presheaf

**Status (2026-09-30):** conditional structural go, shelved by the maintainer — `docs/certified-homs-spike.md`.

`Quantitative/Family` re-proves `Abstract2`'s composition theorems "step by step" with
an error schedule threaded through (`≤UC[]-compose`, `≤UC[]-compose′`, `≈ctx-*`). The
vanishing-TV design (`docs/vanishing-tv-presheaf.md`) and the `QUCSetup` landing put
the error into the presheaf's setoid instead, so that `_≤UC^ε_` is literally the generic
`_≤UC_` of one setup and every composition theorem is inherited. What blocks finishing
it, per `Quantitative/Family`'s own header, is that the compared homs carry no
certificate, so absorbing an adversary has no allowance to charge. The remedy is the
same move as in §1 but without totality: make the compared homs the certified ones
(`L.Hom`), i.e. state the family setup over `L` rather than over `M` with certificates
on the side. Reach is unchanged (uncertified machines can still be modelled; they just
carry no security statement, which is already true). Removes the parallel ε-theory in
`Quantitative/Family` (~1–2k LOC) and makes `Approx/**` the definition of one setoid.

### 2.2 Probabilities as lower reals

**Status (2026-09-30):** cheap version NO-GO; D4 (`Cofinal`/`Dom` as LowerReal's relations) done; the full `Dp/**` rebuild is unspiked — `docs/lower-real-reading-spike.md`.

Replace the coinductive `Dₚ` with sub-probability valuations into a lower-real carrier
(the `probability-theory` branch has `Carrier/LowerCut/*`; the plan there recorded three
interface obstructions to revisit). The supremum lives in the carrier, so `Cofinal`,
`Dom`, `cum`, `Mass` and `Approximants` vanish: `_≼ₚ_` is pointwise `≤`, `_≈ₚ_` is
equality, Elgot iteration is a least fixed point in an ω-cpo. Same reach; the machine
category is unchanged above the monad. Largest structural win short of §1; cost is a
rebuild of `Dp/**` (4k LOC) against a carrier without subtraction or decidable order.

A cheap partial version: keep `Dₚ` for machines but make the *reading* a lower real,
`S := 𝕃` with `eval = Pr[true]`. Then `Mass`/`Approximants` fold into `S` itself (a
mass is the identity map) and the ε-layer's `≈[ε]` is `|x − y| ≤ ε` on `𝕃`. Removes
the mass structure and part of `Seam`; keeps `Dp/**` as is.

### 2.3 One accounting theory

**Status (2026-09-30):** NO-GO — the family theory is already the single-level one levelwise, so there is no second proof to delete — `docs/one-accounting-theory-spike.md`.

The single-level graded theory (fixed security parameter, budget `q`, `UC/Audit`) and
the family theory (`UC/Family`, `Quantitative/Family`, `Famᴹ`) are two theories of the
same shape. `UC/Family.ucSetup^ω` already exhibits families as one `UCSetup` instance,
so the direction is fixed: single-level statements should be the family theory at
constant families (or the family theorems should be the generic ones at `ucSetup^ω`,
which is §2.1). The concrete-security statements are kept; what goes is their second
proof.

### 2.4 Small-step composition, iteration only in the runner

Compose machines as Mealy machines over `Dist` whose one step is one step of the
active component (activation-token semantics), so composition needs no iteration; take
the supremum only in the runner (`Pr≤ n`). Category laws then hold up to run
equivalence, which is the hom-setoid the UC layer already uses. Same reach; removes
`Dₚ` from composition but not from the runner; the laws-via-runner proofs are new work
and the win is uncertain. Recorded, not recommended ahead of §2.1–2.3.

## Recommendation

§1 stays not adopted. Of §2.1–2.3, only §2.1 holds up, and only conditionally; it is
shelved (2026-09-30). The cheap §2.2 and §2.3 are closed as NO-GO, with nothing left to
delete. Still open: the full §2.2 (rebuild `Dp/**` over a lower-real carrier, ~4k LOC,
the only remaining route that deletes `cum`/`Cofinal`/`Dom`) and §2.4. Neither is
recommended without a spike.
