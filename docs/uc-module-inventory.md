# UC module inventory

One row per module under `src/CategoricalCrypto/UC/` at the `UC.Audit` retirement
(`docs/audit-retirement-spike.md`, regenerated with the commands below), with names
relative to `CategoricalCrypto`. The purpose
column quotes or paraphrases the first sentence of the module header. **Importers** counts the other files under `src/` that
import the module, including the library root `src/CategoricalCrypto.agda`. **Root**
marks the modules the root imports directly. There is no `UC.agda` or `UC/Model.agda`
any more: `28917ece` folded both into the root.

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
| `UC.Approximate` | 125 | 17 |  | decay classes of rational sequences (`Negligible` beside `_→0`) and the bounds graded by them |
| `UC.Approximate.Decay` | 85 | 6 |  | negligibility of an exponentially decaying bound: a polynomial numerator against `2^-sch(n)` |
| `UC.Approximate.Local` | 99 | 2 |  | the local negligible agreement `_∼ᴺ_` of an index-family of observations |
| `UC.Approximate.LocalTests` | 48 | 1 | yes | acceptance criteria as theorems: `_∼ᴺ_` admits a one-shot `2⁻ⁿ` difference and rejects a one-shot `1/(n+1)` one |
| `UC.Approximate.Separating` | 106 | 2 |  | the two instruments a negative closeness statement needs, incl. the faithful `ℚ-metric` |
| `UC.Core` | 161 | 7 |  | the extra structure on a category that the UC models here are generated from |
| `UC.Family` | 225 | 4 |  | `𝒞^ω`, the indexed family layer: families levelwise certified at a rate schedule polynomial in the security parameter |
| `UC.Family.Negligible` | 108 | 2 |  | the negligible tier as a second observation on the family category, and the one-way bridge into it |
| `UC.Family.Negligible.Setup` | 75 | 1 |  | the canonical local-negligible `UCSetup`, and the bridge into it |
| `UC.Family.Vanishing` | 35 | 1 |  | the vanishing tier's agreement in the inherited order (`Canonical^ω`) |
| `UC.Graded` | 86 | 3 |  | emulation at a nontrivial grade, from a machine-level factoring |
| `UC.Machine` | 182 | 58 |  | the intended model: the UC layer over the machine layer (`⟦_⟧ᴵ`/`retᴵ`, `𝒫ᴵ`) |
| `UC.Machine.Bridge` | 72 | 9 |  | the bridge between the environment layer and layer 1's concrete statements |
| `UC.Machine.Dictionary` | 297 | 14 |  | the ancilla dictionary: `UC.Machine`'s direct relays read as the monoidal spellings of the same processes |
| `UC.Machine.Dominated` | 184 | 2 |  | `dominated`, the bridge's context domination, via the two-machine skeleton |
| `UC.Machine.EventBounds` | 162 | 6 |  | event bounds at the machine: the capped-allowance presentation, the absorption of a morphism into the context, and an adversary as a reader (`advReader`, `AdvBoundedAt`) |
| `UC.Machine.Grading` | 147 | 4 |  | the machine model's graded subcategory `gradingᴹ`: `UC.QueryBound`'s certificate at a positive rate |
| `UC.Machine.Monitor` | 241 | 7 |  | a watch as a process (`monitorᴹ`), the completion reader `flagReader`, and the monitored process as its accumulator's flag wire (`monitor-flag`) |
| `UC.Machine.Monitor.Agree` | 250 | 5 |  | the test a strategy embeds to (`stratTest`, `qb-stratTest`), the flag reader collapsed, and `flag-agree`: the accumulator's flag wire at `flagStrat d` is the watched run (`_≈ₚ_`) |
| `UC.Machine.MonitorTests` | 37 | 1 | yes | the three behaviours the watch compiler is accepted on, at the monitor steps deciding them |
| `UC.Machine.Run` | 118 | 17 |  | a simulation is invisible to a closed run |
| `UC.Machine.Run.Lax` | 55 | 1 | yes | what a lax simulation does to a closed run: it prefixes it |
| `UC.Machine.Slide` | 283 | 4 |  | a closed ancilla context with a hole is a plain context on the hole (`Kctx`, `ctxRun-slide`) |
| `UC.Machine.StateEvent` | 181 | 7 |  | state predicates over machine presentations (`EventSim`), and the flag-wire machine `M ▷ P` that turns a Boolean state test into an interface event |
| `UC.Machine.StateEvent.Adequacy` | 236 | 3 |  | at a protocol image the state-event reading is `PrHit` past a depth, and `BoundedHit` ⇔ `StateBoundedAt` at the same cap |
| `UC.Machine.StateEvent.Agree` | 207 | 2 |  | the state-event reading at embedded strategies is the closed run of `M ▷ P` at `flagStrat d` (`_≈ₚ_`) |
| `UC.Machine.StateEvent.HitTests` | 182 | 1 | yes | the distinguishing cases of the state-event reading, through its public entry points |
| `UC.Machine.StateEvent.Lift` | 392 | 2 |  | the strategy-to-contexts lift for state events (`stateLift`), at the same cap and with no slack |
| `UC.Machine.StateEvent.Read` | 108 | 6 |  | reading a state event in an ordinary experiment: `stateRead`, and `StateBoundedAt`/`StateBoundedᴺ` as `EventBounds` instances |
| `UC.Machine.Wire` | 110 | 6 |  | composing with a wire costs no trace |
| `UC.Model.Dominated` | 148 | 9 |  | `UC.Machine.Dominated.dominated` at seal objects |
| `UC.Model.Enrichment` | 70 | 18 |  | the rate grading at the sealed model, and the seal coercions that certify into it |
| `UC.Model.Family` | 34 | 6 |  | `UCSetup` at the machine family: `UC.Family` at the sealed bundle, with `Canonical^ω` and the negligible tier |
| `UC.Model.Family.Contextual` | 19 | 6 |  | `UC.Quantitative.Family` at the sealed machine bundle: `_≈ctx[_]_` and `_≤UC^ωᵉ_` |
| `UC.Model.Family.Emulation` | 100 | 4 |  | the family UC premise on protocol images with its error kept: `_≈ᶠᴺ_`; `≤UC[]⇒≤UCᴺ` |
| `UC.Model.Graded` | 85 | 2 |  | the seal's coercions for a nontrivially graded process image |
| `UC.Model.Observation` | 76 | 11 |  | the (ticked) verdict object `Ωᵒ` and what a closed process shows at it (`Obs`) |
| `UC.Model.Seal` | 118 | 22 |  | the machine monoidal bundle behind an `opaque` seal, and the coercions across it |
| `UC.Model.Setup` | 25 | 17 |  | the UC setup of the model: `StdUC` at the sealed machine bundle and the readout's test presheaf `ℰᵒ` |
| `UC.Quantitative.Contextual` | 209 | 1 |  | the query-sensitive contextual comparison, as the admitted agreement of the filtered test presheaf |
| `UC.Quantitative.EventLift` | 101 | 4 | yes | event bounds at the monitored readout (`HitsAt`, `Hitsᴺ`), the lift `hitsᵘ` via `stateLift`, and `agree`/`hits⇒bounded` back at the strategy level |
| `UC.Quantitative.Family` | 253 | 1 |  | the quantitative contextual relation on families of graded morphisms, the emulation witness over it, and its composition laws |
| `UC.Quantitative.Query` | 206 | 1 |  | the query-sensitive test model as a filtered instance: tests compared through certified closures |
| `UC.QueryBound` | 470 | 34 |  | query bounds with content: the amortised-potential certificate `QBᵢ` and the run-level counting statement |
| `UC.QueryBound.Compose` | 305 | 1 |  | the query bound multiplies along composition: the two-position token walk |
| `UC.QueryBound.Compose.Laws` | 60 | 6 |  | the composition closure of `QB`, at the hom level and at 𝒢's own objects |
| `UC.QueryBound.Compose.Step` | 217 | 5 |  | the composite's step computed: `Unfolding` for the real `𝒫ᴵ` composite, and `qb-∘` |
| `UC.QueryBound.Counting` | 104 | 1 | yes | what `QBᵢ`'s potential means on a run: at most `c` downward outputs per activation from above |
| `UC.QueryBound.Exact` | 203 | 3 |  | exact output counts: what a query bound cannot say |
| `UC.QueryBound.Object` | 63 | 4 |  | `UC.QueryBound`'s hom-level predicate at 𝒢's own objects |
| `UC.Robust` | 91 | 1 |  | properties that are preserved by `≤UC` under reasonable assumptions |
| `UC.Robust.Model` | 36 | 1 | yes | the qualitative carry at the intended instance, and its acceptance test at a selected environment class |
| `UC.Seam` | 66 | 8 |  | a finite strategy embedded as an environment (`strategyEnv`) |
| `UC.Seam.Adequacy` | 103 | 1 |  | `adequacy`: an embedded strategy run against a closed process observes what layer 1's own run observes |
| `UC.Seam.Adequacy.Wiring` | 96 | 2 |  | the closed G-composite `strategyEnv B d ∘ u` as one machine with a readable step |
| `UC.Seam.Audit.Context` | 60 | 1 |  | the certified context a strategy's closed run is read at: the embedded strategy behind two unitors at the trivial grade |
| `UC.Seam.Budget` | 147 | 2 |  | what an embedded strategy costs: the query bound its ask-depth gives it |
| `UC.Seam.Extract` | 86 | 3 |  | a budgeted context, read off its certificate as a (fuel-indexed) strategy |
| `UC.Seam.Grounded` | 94 | 3 |  | the trivial grade at the sealed machine bundle: the grade object, the inflating wire, `closedᵒ`/`stageᵒ`, and a closed two-protocol system as their composite (`factorᵖ`) |
| `UC.Seam.Plug` | 119 | 5 |  | what a closed composite observes at the verdict tick: one pass of the traced loop, then the loop |
| `UC.Seam.Transfer` | 340 | 1 |  | the extracted strategy observes what the context observes, at one verdict |

61 modules, 8701 LOC.
