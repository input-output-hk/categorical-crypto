# UC module inventory

One row per module under `src/CategoricalCrypto/UC/`, with names relative to
`CategoricalCrypto`. The purpose column quotes or paraphrases the first sentence of the
module header. **Importers** counts the other files under `src/` that import the module,
including the library root `src/CategoricalCrypto.agda`. **Root** marks the modules the
root imports directly. There is no `UC.agda` or `UC/Model.agda`: the root imports the
leaves itself.

To regenerate, list the modules with their LOC, then count the importers of each
module `M`:

```sh
find src/CategoricalCrypto/UC -name '*.agda' | sort | xargs wc -l
grep -rlE "^ *(open +)?import +CategoricalCrypto\.M( |$)" src | grep -v '<M.agda>' | wc -l
```

The second grep is anchored at `( |$)` so that it does not count importers of `M`'s
sub-modules. A plain `grep -rlF CategoricalCrypto.M` would count those as well.

| module | LOC | importers | root | purpose |
|---|---|---|---|---|
| `UC.Approximate` | 82 | 16 |  | negligible rational sequences (`Negligible` beside `_→0`) and the two-argument bounds held to them |
| `UC.Approximate.Decay` | 77 | 5 |  | negligibility of an exponentially decaying bound: a polynomial numerator against `2^-sch(n)` |
| `UC.Approximate.Local` | 84 | 2 |  | the local negligible agreement `_∼ᴺ_` of an index-family of observations |
| `UC.Approximate.LocalTests` | 85 | 1 | yes | acceptance criteria as theorems: `_∼ᴺ_` admits a one-shot `2⁻ⁿ` difference and rejects a one-shot `1/(n+1)` one |
| `UC.Core` | 89 | 4 |  | observation by evaluation: `Evaluation` and the test presheaf `ℰᴼ` it induces |
| `UC.Family` | 161 | 1 |  | `𝒞^ω`, the indexed family layer: `Categories.LocallyGraded.Family` at `Poly⁺` admissibility over the resource grading, with the negligible observation on top: `Canonicalᴺ`, `_≈ℰⁿ_`, `ucSetupᴺ` |
| `UC.Graded` | 79 | 3 |  | emulation at a nontrivial grade, from a machine-level factoring |
| `UC.Machine` | 155 | 57 |  | the intended model: the UC layer over the machine layer (`retᴵ`, the inverse of `Protocol.Machine`'s `⟦_⟧ᴵ`; `𝒫ᴵ`) |
| `UC.Machine.Composite` | 223 | 5 |  | a `𝒢ₚ`-composite of two processes as one product-state machine, and the six equations (`Unfolding`) that read its step off |
| `UC.Machine.Dictionary` | 295 | 11 |  | the ancilla dictionary: `UC.Machine`'s direct relays read as the monoidal spellings of the same processes |
| `UC.Machine.Dominated` | 197 | 2 |  | `dominated`, the bridge's context domination, via the two-machine skeleton |
| `UC.Machine.EventBounds` | 151 | 10 |  | event bounds at the machine: the capped-allowance presentation, the absorption of a morphism into the context, and an adversary as a reader (`advReader`, `AdvBoundedAt`) |
| `UC.Machine.Extract` | 65 | 3 |  | a budgeted context, read off its certificate as a (fuel-indexed) strategy |
| `UC.Machine.Grading` | 141 | 4 |  | the machine model's graded subcategory `gradingᴹ`: `UC.QueryBound`'s certificate at a positive rate |
| `UC.Machine.Monitor` | 256 | 3 |  | a watch as a process (`monitorᴹ`), the monitored process as its accumulator's flag wire (`monitor-flag`), and that wire at `flagStrat d` as the watched run (`flag-agree`) |
| `UC.Machine.MonitorTests` | 34 | 1 | yes | the three behaviours the watch compiler is accepted on, at the monitor steps deciding them |
| `UC.Machine.Plug` | 154 | 4 |  | what a closed composite observes at the verdict tick: one pass of the traced loop, then the loop |
| `UC.Machine.Slide` | 275 | 4 |  | a closed ancilla context with a hole is a plain context on the hole (`Kctx`, `ctxRun-slide`) |
| `UC.Machine.StateEvent` | 57 | 6 |  | state predicates over machine presentations, and the flag-wire machine `M ▷ P` that turns a Boolean state test into an interface event |
| `UC.Machine.StateEvent.Adequacy` | 222 | 3 |  | at a protocol image the state-event reading is `PrHit` past a depth, and `BoundedHit` ⇔ `StateBoundedAt` at the same cap |
| `UC.Machine.StateEvent.Agree` | 177 | 2 |  | the state-event reading at embedded strategies is the closed run of `M ▷ P` at `flagStrat d` (`_≈ₚ_`) |
| `UC.Machine.StateEvent.HitTests` | 143 | 1 | yes | the distinguishing cases of the state-event reading, through its public entry points |
| `UC.Machine.StateEvent.Lift` | 390 | 2 |  | the strategy-to-contexts lift for state events (`stateLift`), at the same cap and with no slack |
| `UC.Machine.StateEvent.Read` | 211 | 7 |  | reading a state event in an ordinary experiment: the completion reader `flagReader` and its collapse over a test (`Collapsed`), `stateRead`, and `StateBoundedAt`/`StateBoundedᴺ` as `EventBounds` instances |
| `UC.Machine.Transfer` | 334 | 1 |  | the extracted strategy observes what the context observes, at one verdict |
| `UC.Machine.Wire` | 105 | 5 |  | composing with a wire costs no trace |
| `UC.Model.Dominated` | 141 | 1 |  | `UC.Machine.Dominated.dominated` at seal objects |
| `UC.Model.Enrichment` | 49 | 15 |  | the rate grading at the sealed model, and the seal coercions that certify into it |
| `UC.Model.Family` | 25 | 6 |  | `UCSetup` at the machine family: `UC.Family` and `UC.Quantitative.Family` at the sealed bundle |
| `UC.Model.Family.Emulation` | 132 | 4 |  | the family UC premise on protocol images with its error kept: `_≈ᶠᴺ_`; `≤UC[]⇒≤UCᴺ`; the context a strategy's closed run is read at (`≈ᶠ-runs`) |
| `UC.Model.Graded` | 71 | 2 |  | the seal's coercions for a nontrivially graded process image |
| `UC.Model.Observation` | 76 | 9 |  | the (ticked) verdict object `Ωᵒ` and what a closed process shows at it (`Obs`) |
| `UC.Model.Seal` | 112 | 21 |  | the machine monoidal bundle behind an `opaque` seal, and the coercions across it |
| `UC.Model.Setup` | 25 | 16 |  | the UC setup of the model: `StdUC` at the sealed machine bundle and the readout's test presheaf `ℰᵒ` |
| `UC.Quantitative.Contextual` | 196 | 1 |  | the query-sensitive contextual comparison, as the admitted agreement of a filtered space of tests |
| `UC.Quantitative.EventLift` | 98 | 4 | yes | event bounds at the monitored readout (`HitsAt`, `Hitsᴺ`), the lift `hitsᵘ` via `stateLift`, and `agree`/`hits⇒bounded` back at the strategy level |
| `UC.Quantitative.Family` | 242 | 1 |  | the quantitative contextual relation on families of graded morphisms, the emulation witness over it, and its composition laws |
| `UC.Quantitative.Query` | 119 | 1 |  | the query-sensitive test model as a filtered space: tests compared through certified closures |
| `UC.QueryBound` | 363 | 31 |  | query bounds with content: the amortised-potential certificate `QBᵢ`, its `≈ᴹ`-closure `QB` and closure laws, and the trace `traceᵍ`/`behᵍ` that counting reads |
| `UC.QueryBound.Compose` | 248 | 1 |  | the query bound multiplies along composition: the two-position token walk |
| `UC.QueryBound.Compose.Laws` | 49 | 6 |  | the composition closure of `QB`, at the hom level and at 𝒢's own objects |
| `UC.QueryBound.Counting` | 108 | 1 | yes | what `QBᵢ`'s potential means on a run: at most `c` downward outputs per activation from above |
| `UC.QueryBound.Exact` | 191 | 3 |  | exact output counts: what a query bound cannot say |
| `UC.QueryBound.Object` | 57 | 4 |  | `UC.QueryBound`'s hom-level predicate at 𝒢's own objects |
| `UC.Robust` | 79 | 1 |  | properties that are preserved by `≤UC` under reasonable assumptions |
| `UC.Robust.Model` | 35 | 1 | yes | the qualitative carry at the intended instance, and its acceptance test at a selected environment class |
| `UC.Seam` | 61 | 6 |  | a finite strategy embedded as an environment (`strategyEnv`) |
| `UC.Seam.Adequacy` | 97 | 1 |  | `adequacy`: an embedded strategy run against a closed process observes what layer 1's own run observes |
| `UC.Seam.Budget` | 189 | 5 |  | what an embedded strategy costs: the query bound its ask-depth gives it; the test it embeds to (`stratTest`, `qb-stratTest`) |
| `UC.Seam.Grounded` | 82 | 2 |  | the trivial grade at the sealed machine bundle: the grade object, the inflating wire, `stageᵒ`, and a closed two-protocol system as their composite (`factorᵖ`) |

50 modules, 7094 LOC.
