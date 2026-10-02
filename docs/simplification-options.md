# Simplifying the model: an optional variant, and options that keep its reach

Options for simplifying the theory behind the machine model, recorded after the
maintainer asked whether it "has to be so complicated". Sizes are grouped by
mathematical layer rather than by directory and were measured at `c71d95fe`; they
include modules since deleted (`SFunM`, `SFunPartial`, `UC/Audit`), which the layer
lists below no longer name.

| Layer | LOC |
|---|---|
| Machine tower (`Machines`, `GConstruction*`, `Machine`, `Channel`) | 11.4k |
| Partiality (`Dₚ`, `Iter`, `Cofinal`/`Dom`, `ASTotal`, `GamePlaying/Partial`, `Uniform/Decay`) | 4.1k |
| ε-layer (`Approximate*`, `Approx/**`, `Negligible*`) | 1.9k |
| Grading (`LocallyGraded`, `Rates`, `Family*`, `Quantitative/**`, `QueryBound*`) | 5.9k |
| Model glue (`UC/Model`, `UC/Seam`, `UC/Machine`) | 5.7k |
| Generic UC core (`UCSetup`, `Abstract2`, `Core`, `Robust`) | 2.0k |

Two layers are essential as they stand. The generic core is a category, a graded monad
that attaches adversaries, a presheaf of environments, and the order "for every adversary
a simulator agreeing in every environment"; nothing there is removable. The machine
tower is the price of string-diagram wiring with interface polarity; without it there is
no model to run examples in.

Everything else is downstream of one design decision: **composition of machines along an
interface is resolved by Elgot iteration in a partial monad.** Messages ping-pong between
the two machines, the loop is closed by `Dₚ`'s iteration, and so probabilities are
suprema of finite approximants. That single choice forces the partiality layer, the
sup-free spellings (`Cofinal`, `Dom`, `Mass`), the "δ-close for every δ"
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
  `Cofinal`, `Dom`, `ASTotal`, `Mass` disappear.
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

`Quantitative/Family` re-proves `Abstract2`'s composition theorems with an error
schedule threaded through (`≤UC[]-trans`, `≤UC[]-compose`, `≈ctx-*`). The idea: put
the error into the presheaf's setoid, so that `_≤UC^ωᵉ_` is literally the generic
`_≤UC_` of one setup and every composition theorem is inherited. What blocks it, per
`Quantitative/Family`'s own header, is that the compared homs carry no certificate, so
absorbing an adversary has no allowance to charge; the proposed remedy was to compare
the certified homs (`L.Hom`) instead.

**Spiked; NO-GO as stated, conditional structural GO, shelved.** The obstruction is
structural: a quantitative setup with an `Approx`-valued presheaf compares two
*elements*, but `_≈ctx[_]_` reads its error at the allowance of the *context*, which is
no longer visible once the compared hom has been pulled through it; an element-level
closeness that reads an allowance off the two elements cannot be transitive unless it
ignores the allowance (the spike's `AllowanceNoGo`). What survives is a `Filt`-valued setup with the
admitted agreement `_≈ᵃ[_]_` as its comparison: at the rated base it reproduces
`_≈ᵁᵠ[_]_` exactly and the spike's generic `at-trans`/`at-compose` produce exactly `seqError`
and `composeError`. That is a win in structure, not size (the parallel ε-theory is
~300 lines, not 1–2k, and the replacement costs about the same), and it is conditional
on the reach question: the unmoved compared homs would need *some* certificate, or a
two-sorted setup with an uncertified `𝒟 ⊇ 𝒞`. The spike modules are deleted; recover
them with `git log --all -- src/CategoricalCrypto/UC/Quantitative/Spike`.

### 2.2 Probabilities as lower reals

Replace the coinductive `Dₚ` with sub-probability valuations into a lower-real carrier.
The supremum lives in the carrier, so `Cofinal`, `Dom`, `cum` and `Mass` vanish: `_≼ₚ_`
is pointwise `≤`, `_≈ₚ_` is equality, Elgot iteration is a least fixed point in an
ω-cpo. Same reach; the machine category is unchanged above the monad. Largest
structural win short of §1; cost is a rebuild of `Dp/**` (4k LOC) against a carrier
without subtraction or decidable order. **Unspiked.**

**The cheap version — keep `Dₚ`, make only the *reading* a lower real — is NO-GO.**
With one lower real (`Pr[true]`) the readout gets coarser: answering `false` and
diverging are identified, a changed semantics rather than a simplification. With one
lower real per verdict the readout is faithful, but the model's ε-layer is *already*
definitionally the pullback of the lower reals' along the reading, and the mass is a
projection of it, so nothing folds away. The part that was worth doing (D4) is done:
`Dp.Cofinal`/`Dp.Dom` are `Data.Rational.LowerReal`'s relations at `cumₛ`, kept as named
notions because they are the inference adapters (LowerReal's lemmas take their
sequences explicitly).

### 2.3 One accounting theory

The single-level quantitative theory (`UC.Quantitative.Contextual`, fixed security
parameter and budget) and the family theory (`UC.Quantitative.Family`, `UC/Family`) have
the same shape, and the proposal was to make single-level statements the family theory
at constant families so that their second proof could go.

**Spiked; NO-GO: there is no second proof.** The family theory is already the
single-level one levelwise: `_≈ctx[_]_` is *defined* as `_≈ᵁᵠ[_]_` at every level, and
every family composition law wraps a single-level lemma (`≈ctx-sub` wraps `ctx-sub`,
`≤UC[]-trans` wraps `at-trans`). Deriving the single-level lemmas back through constant
families works but is circular. The qualitative tier already takes the clean direction:
`UC/Family.ucSetup^ω` is the vanishing-advantage family as one `UCSetup` over the
levelwise `Famᴹ`, so `Abstract2`'s theory is inherited for families.

### 2.4 Small-step composition, iteration only in the runner

Compose machines as Mealy machines over `Dist` whose one step is one step of the
active component (activation-token semantics), so composition needs no iteration; take
the supremum only in the runner (`Pr≤ n`). Category laws then hold up to run
equivalence, which is the hom-setoid the UC layer already uses. Same reach; removes
`Dₚ` from composition but not from the runner; the laws-via-runner proofs are new work
and the win is uncertain. Recorded, not recommended ahead of §2.1–2.3.

## Recommendation

§1 stays not adopted. Of §2.1–2.3, only §2.1 holds up, and only conditionally; it is
shelved. The cheap §2.2 and §2.3 are closed as NO-GO, with nothing left to delete. Still
open: the full §2.2 (rebuild `Dp/**` over a lower-real carrier, ~4k LOC, the only
remaining route that deletes `cum`/`Cofinal`/`Dom`) and §2.4. Neither is recommended
without a spike.
