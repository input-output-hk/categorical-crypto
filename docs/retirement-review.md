# Retirement review (WP11)

> `_≤UC^ωⁿ_` below is `UC.Model.Family.Emulation._≈ᶠᴺ_` in the current tree (renamed 2026-09-30).

Review of what the quality campaign removed between `c71d95fe` (before it) and
`74ce2e18` (`protocol-rewrite` after the `wp6-docs` merge), as WP11 of the
state-event plan asks: "Lack of an importer is not by itself a reason to retire
reusable mathematics. Record a replacement, a deliberate scope decision, or a
restoration decision." Nothing here changes source; every recommendation is
input for the maintainer.

Sources. The deleting commit is `git log --diff-filter=D --format=%h
c71d95fe..74ce2e18 -- <path>`. A removed name inside a surviving file is traced
with `git log -S<name> c71d95fe..74ce2e18 -- <path>`. Reasons come from that
commit's message or from the part reviews at `74ce2e18`:
`QUALITY-REVIEW-A-examples.md` (A), `-B-uc.md` (B), `-C-machines.md` (C) and
`-D-foundations.md` (D), cited as part and item. Importer counts are the
review's where it gives one. Otherwise they are computed at the deleting
commit's parent with `git grep -lE "import +<Module>( |$)" <c>^ -- src`,
excluding the file itself, and marked *(computed)*. LOC is the file at the
deleting commit's parent. Paths are relative to `src/CategoricalCrypto/`
unless they start with `src/` or `docs/`.

Recommendations:
- **keep** means keep deleted.
- **restore** means bring the file or name back where it was.
- **restore→general** means re-home the content in a general-purpose module
  (house rule 27), usually restated at the live carrier.

## 1. Deleted modules (52)

| module | LOC | deleted by | recorded reason | replacement | importers at deletion | recommendation |
|---|---|---|---|---|---|---|
| `Examples.ChimericLedger.ReplayFamily` | 58 | `22aa2103` | A10: one theorem plus side condition, alias and forwarder; Transfer already hosts the family counterexamples | last section of `Examples/ChimericLedger/Transfer.agda` (`Chimericᶠ` `:340`, `chimeric-not-preserving`) | 0 *(computed; a non-root leaf, D verification table)* | **keep**. The content moved verbatim, and the move puts the family counterexamples side by side |
| `Examples.Possibilistic` | 94 | `7f025978` | A26: "a test in disguise", same opens as `SFunM.Test.Possibility` | `SFunM/Test/Possibility.agda:149-153` (`eval Lossy` pin, `Lossy-idempotent`) | 1, the root *(computed)* | **keep**. The eval pins and `Lossy-idempotent` survive as a test section |
| `Machines.G.Lax` | 70 | `dd9ebf45` | B1: exists only for `emulAgreeᵁ`'s cone; importers are only Grounding, Run/Lax and each other | none | 1 (Grounding) [B1] | **keep**. Its one result `∘ᴳ-resp-≈ˡ` is `Sim.Lax`'s congruences applied with strict structural legs (its header). It is re-derivable if `Sim.Lax` returns |
| `Machines.Sim.Lax` | 189 | `dd9ebf45` | B1, as above. B1's "Against it": "`Sim.Lax` is general machine material" | none | 3 (G.Lax, Run.Lax, Grounding) [B1] | **restore**. Simulation up to a scalar initialization prefix, with `⊗ᵉ`/`∘ᴹ` congruence, is general Mealy-machine theory at any Kleisli base. It is the only notion here that relates machines differing by a dead-weight initialization. Its UC consumer was the retired part, not its mathematics |
| `Protocol.Machine.Total` | 53 | `1d43486a` | C3: `totalRun-∘`, `totalRun-resp-≈ᴹ` have zero uses; after impl-B nothing uses `TotalRun` | the probabilistic content is `ProbabilisticLogic.Dp.Mass.Total` (`src/ProbabilisticLogic/Dp/Mass.agda:131`) | 1, the root *(computed)*. C3: "`TotalRun`'s one consumer is `UC/Seam/Grounded`" | **keep**. It is a predicate plus two closure lemmas at the closed-machine shape, a thin wrapper over `Dp.Mass.Total` |
| `SFunM.Kleisli` | 183 | `2c178865` | C1: the SFun layer written twice; the Class-parametrised copy is deleted and the Kleisli stack renamed over it | `SFunM` (renamed) | 5 (its own sub-modules, `Examples.Possibilistic`, `SFunM.Test.Possibility`) *(computed)* | **keep**. It was renamed, not removed |
| `SFunM.Kleisli.Monoidal` | 381 | `2c178865` | C1 | `SFunM.Monoidal` | 3 *(computed)* | **keep** (renamed) |
| `SFunM.Kleisli.Morphism` | 141 | `2c178865` | C1 | `SFunM.Morphism` | 1 *(computed)* | **keep** (renamed) |
| `SFunM.Kleisli.Properties` | 162 | `2c178865` | C1 | `SFunM.Properties` | 4 *(computed)* | **keep** (renamed) |
| `SFunM.Spike.CommutativeMaybe` | 99 | `aed1c111` | "none imported from outside the tree nor by the root … `Machines.Core` and its cone (same construction)" (commit); C Committed | none | 2, both in the Spike tree *(computed)* | **restore→general**. `Maybe` on `Setoids` as a commutative monad is, per its header, "the one input to `…Monoidal.Construction.Kleisli` that is not upstream". It is category theory with no crypto content and no replacement (agda-categories 0.3.0 has no `Maybe` monad on `Setoids`) |
| `SFunM.Spike.Distributor` | 368 | `aed1c111` | as above | the `Machines.Tensor*` cone (commit's claim) | 1 (Spike) *(computed)* | **keep**. A spike of the interface-tensor distributor that the machine layer realizes |
| `SFunM.Spike.Instance.Rel` | 167 | `aed1c111` | as above | none | 0 *(computed)* | **restore**, ported to `Machines.Core` as an instance or test. It is the only certification of the general layer at a base that is not the Kleisli category of a monad (`Rels`). C "Test suites" records that no suite exercises `Machines.*` directly. The port is unspiked |
| `SFunM.Spike.Instance.RelDist` | 77 | `aed1c111` | as above | none | 0 *(computed)* | **restore→general**. "`Rels` satisfies the interface-tensor hypothesis" (header) says `Rels` is monoidal-distributive in the sense of `Categories.Category.Monoidal.Distributive`. That is a general fact, and it belongs beside that record |
| `SFunM.Spike.Instance.Setoid` | 172 | `aed1c111` | as above | none | 1 (SetoidDist) *(computed)* | **keep**. It is one more Kleisli-of-a-monad instance, like the live `Dₚ` one, and is re-derivable once `CommutativeMaybe` returns |
| `SFunM.Spike.Instance.SetoidDist` | 77 | `aed1c111` | as above | upstream extensive ⇒ distributive | 0 *(computed)* | **keep**. Its header says "Nothing is proved here" |
| `SFunM.Spike.Instance.Type` | 107 | `aed1c111` | as above | none (the SFun ↔ `Machines` bridge is open, C1 "Longer term") | 0 *(computed)* | **keep**. It pins the spike layer against the old elementwise SFun layer. A bridge would have to be restated against `Machines.Core` anyway |
| `SFunM.Spike.Instance.TypeDist` | 161 | `aed1c111` | as above | `Categories.Category.Construction.Kleisli.Discrete.Distributive` | 0 *(computed)* | **keep** |
| `SFunM.Spike.KleisliDiscrete` | 289 | `aed1c111` | D "Out-of-part": a verbatim pre-extraction copy of `Kleisli/Discrete` | `Categories.Category.Construction.Kleisli.Discrete` | 2 (Spike) *(computed)* | **keep** |
| `SFunM.Spike.KleisliDistributive` | 140 | `aed1c111` | D "Out-of-part": it "generalizes `Kleisli/Discrete/Distributive`" | the discrete special case only | 1 (Spike) *(computed)* | **restore→general**. The content is that the Kleisli category of any monad over a distributive base inherits coproducts unconditionally and the distributor along `pure`. The live module has only the discrete instance, so the general statement is what was lost. It belongs in `Categories.Category.Construction.Kleisli.*` |
| `SFunM.Spike.Laws` | 108 | `aed1c111` | commit | `Machines.Category` | 1 (Spike) *(computed)* | **keep** |
| `SFunM.Spike.Mealy` | 149 | `aed1c111` | commit: `Machines.Core` "opens with the same header text" (C Committed) | `Machines.Core` | 8 (Spike) *(computed)* | **keep** |
| `SFunM.Spike.MonoidalDistributive` | 59 | `aed1c111` | D "Out-of-part": ≅ `Monoidal/Distributive` | `Categories.Category.Monoidal.Distributive` | 6 (Spike) *(computed)* | **keep** |
| `SFunM.Spike.SlotFrame` | 1183 | `aed1c111` | commit | `Machines.Frame` and cone | 3 (Spike) *(computed)* | **keep** |
| `SFunM.Spike.Tensor` | 599 | `aed1c111` | commit | `Machines.Tensor` | 2 (Spike) *(computed)* | **keep** |
| `UC` | 57 | `28917ece` | B5: 17 public re-exports; its only importer is the root, and nothing reads a name through it | root `CategoricalCrypto.agda` import list | 1, the root [B5] | **keep**. It was a re-export layer (rule 19) |
| `UC.Audit.Canonical` | 73 | `aa4d8bb2` | commit: integration back-port of the UC/Approx layer "deletes UC.Audit.Canonical". No review section | the Σ-shaped `_≤UC[_]_` makes the witness the relation itself (`Examples/HashForward/Audit.agda:54-58`); `≤UC[]⇒≤UC` (`UC/Audit.agda:58`) is `audit-forget` | 1 (`UC.Model.Audit`) *(computed)* | **keep**. `audit⇔witness` became definitional |
| `UC.Machine.Run.Lax` | 72 | `dd9ebf45` | B1: sole importer Grounding | none | 1 (Grounding) [B1] | **restore**, with `Sim.Lax`. "A lax simulation prefixes a closed run" is the run-level payoff of `Sim.Lax`, and together with `Dp.Mass.astotal-bind` (§2) it makes an a.s.-terminating initialization invisible to an ε-comparison. None of that is specific to the trivial grade |
| `UC.Model` | 16 | `28917ece` | B5: a closure list | root import list | 1, the root [B5] | **keep** |
| `UC.Model.Family.Negligible` | 21 | `2336b208` | B10 "Related": the same six arguments as `Model.Family` | `UC.Model.Family` (opens `UC.Family.Negligible{,.Setup}`, `:26,29`) | 4 *(computed)* | **keep** (merged) |
| `UC.Robust.Observation` | 150 | `aa4d8bb2` | commit only. No review section | `UC.Robust` at any `UCSetup` (`robust-resp-≈ᵁ`, `robust-sub`, `uc-preserves`), `UC.Core.always` (`UC/Core.agda:157`), `∼[_]` (`src/Relation/Binary/Properties/Setoid/Ext.agda:11`), `UC.Robust.Model` | 1 (`UC.Robust.Model`) *(computed)* | **keep**, and record the scope decision. `docs/history/retirement.md` §7 had recorded this module KEPT because its gate ("whole original scope recovered") was not met. Still not recovered: `robust⇔robustᵍ` and the ungraded-codomain `Robust`, plus `verdict-preservedᵒ`. See §7 |
| `UC.Robust.Selected` | 64 | `aa4d8bb2` | commit only | `Factors`/`factors-resp`/`factors-closed` in `UC/Robust.agda:82-95`. The acceptance test is `UC/Robust/Model.agda:31 relay-selectedᵒ` | 1 (Observation) *(computed)* | **keep**. `uc-preserves-factors` is `uc-preserves` at `factors-closed` |
| `UC.Seam.Grounding` | 215 | `dd9ebf45` | B1: all of it exists only for `emulAgreeᵁ`; sole importer Grounded | none | 1 (Grounded) [B1] | **keep**. `Massed`/`Prefixedᵒ` at the sealed trivial grade are UC-specific plumbing for the retired family premise. The general parts are `Sim.Lax`, `Run.Lax` and `astotal-bind` |
| `Categories.Category.Kleisli.Discrete.Pure` | 70 | `1dadde05` | D9: upstream's home for Kleisli constructions (git records a delete and an add) | `src/Categories/Category/Construction/Kleisli/Discrete/Pure.agda` | 13 *(computed)*. D9 gives 18 for the three-module family | **keep** (moved) |
| `Categories.GConstructionLoopCoherence` | 109 | `8739aa2f` | D3: `trace-mid` by sliding; a 63.4 s solver module | `trace-slide` (`src/Categories/Category/Monoidal/Traced/Ext.agda:43`); `GConstructionLoop.trace-mid` has the same statement | 1 *(computed)* | **keep**. Same statement, derived instead of solved |
| `Categories.GConstructionTensorCoherence` | 173 | `9c271400` | D2: retired onto upstream interchange laws; a 59.3 s module | `mid-unitˡ`/`mid-unitʳ`/`mid-assoc` (`src/Categories/GConstructionTrace.agda:134,150,166`) | 1 *(computed)* | **keep**. The commit says the statements are the same |
| `Data.Sum.Ext` | 19 | `adfb608c` | D8: `unitˡ⇒`/`unitʳ⇒` are stdlib `fromInj₂ ⊥-elim`/`fromInj₁ ⊥-elim` | stdlib `Data.Sum.Base` | 5 [D8] | **keep** |
| `LibExt` | 299 | `74179850` | D1: imported only by four island files | none needed | 4 [D1] | **keep**. List, arithmetic and predicate utilities of the retired island |
| `ProbabilisticLogic.Abstract` | 307 | `74179850` | D1: a second, parallel notion of probability; the only model is degenerate (`0# ≈ 1#`) | `RationalDist` (`Dist-ℚ`), `RationalDist.Setoid` | 11, all in the island [D1] | **keep**. An axiomatic interface with no non-degenerate model (D10) is a deliberate scope decision, not lost mathematics |
| `ProbabilisticLogic.Distribution.Bernoulli` | 123 | `74179850` | D1 | none. `Uniform.uniform-Bool` (`src/ProbabilisticLogic/Distribution/Uniform.agda:204`) is only the ½ case | 4 (island) *(computed)* | **restore→general**, restated at `Dist-ℚ`. Bernoulli(m/(m+n)) with `P-bernoulli-true/false` is basic finite probability, and the live library has no biased coin |
| `ProbabilisticLogic.Distribution.Binomial` | 246 | `74179850` | D1. Its dead items are `count`, `exactly`, `at-least`, `at-most` and the `E-binomial-*` family | none | 2 (island) *(computed)* | **restore→general** at `Dist-ℚ`. The binomial as a product of Bernoullis, `P(all true) = pᵏ` and the expected count k·m/(m+n) are reusable finite-probability theorems with no live counterpart. `pow` should become stdlib `_^_` (D1) |
| `ProbabilisticLogic.Distribution.Markov` | 37 | `74179850` | D1, D10: `stepⁿ` is correct only at uniform row width | none | 2 (island) *(computed)* | **keep** as written. The deleted statement was wrong (D10's counterexample gives 2/3 where the true value is 3/4). A correct n-step kernel via `_>>=_` would be new work, not a restoration |
| `ProbabilisticLogic.Dp.Stable` | 69 | `a5aaf7c4` | C11: `prAgree` is `Raw.rawPr` at the protocol image, so `Stable` loses its only consumer | `Dp.Settle.Settles` for halting runs. C "Tried": the two are not the same notion | 2 (`Protocol.Machine.Agree`, `UC.Seam.Transfer`), both dropped in the same commit *(computed)* | **keep**. Exact stabilization of `cum` past a budget has no remaining use, and `Settles` covers the halting case the library needs |
| `ProbabilisticLogic.Dp.Support` | 83 | `1dadde05` | D9: folded into `Dp` beside `Supp`/`uniformize` | `src/ProbabilisticLogic/Dp.agda:321-` (`Supp-bot`, …) | 3 *(computed)* | **keep** (moved) |
| `ProbabilisticLogic.Examples.BiasedCoin` | 53 | `74179850` | D1: every example is a parametric theorem never instantiated | none | 1 (island index) *(computed)* | **keep**. It can be re-created as a `Dist-ℚ` test if Bernoulli returns (§3) |
| `ProbabilisticLogic.Examples.Coins` | 56 | `74179850` | D1 | none | 1 *(computed)* | **keep** (§3) |
| `ProbabilisticLogic.Examples.MultipleCoins` | 42 | `74179850` | D1 | none | 1 *(computed)* | **keep** (§3) |
| `ProbabilisticLogic.Examples.Weather` | 37 | `74179850` | D1, D10: holds only because both rows have width 3 | none | 1 *(computed)* | **keep** (§3) |
| `ProbabilisticLogic.Expectation` | 441 | `74179850` | D1: `weight-sum*` is `Distribution.Linearity.lookup-L*` at `Probabilityᴿ`; the `E-+` chain is dead; heap defect (`-M8G`) | `Distribution.Linearity`, `RationalDist.Expectation` | 3 (island) *(computed)* | **keep**. The linear algebra lives on in `Linearity` |
| `ProbabilisticLogic.Logic` | 76 | `74179850` | D1: `Σ[_][_]_` is a one-field record for `p ≤ P ∙ X`; `Σ-zero`/`-weaken`/`-mono` dead | none needed | 4 (island) *(computed)* | **keep** |
| `ProbabilisticLogic.Models.Trivial` | 118 | `74179850` | D1, D10: the one-point model validates exactly the collapse `Abstract` guards against | none | 1 *(computed)* | **keep** (§3) |
| `ProbabilisticLogic.Prelude` | 27 | `adfb608c` | D8: pure re-export; 5 of 11 importers already imported the sources | `RationalDist{,.Partial,.Expectation,.Setoid,.Advantage}`, `Uniform` | 11 [D8] | **keep** |
| `ProbabilisticLogic.Reasoning` | 14 | `74179850` | D1 | none needed | 10 (island) *(computed)* | **keep** |

## 2. Dead public results deleted inside surviving modules

These are the names the part reviews list as dead public code: B "Dead public
definitions" and B1/B8/B10; D7; C3, C19 and the carried L227; A2, A23, A24,
A27, A28. A few more that A committed as "no consumer" are included. Names
still present at `74ce2e18` are omitted: C L243/L342, `advᵇ⊥-sym/-triangle`
(kept by `8086f412`), `sim-log-repeat`/`extract-relog`/`extract-table` (kept
by `f75bd9c7`), `comSimʰ` (`Examples/CoinToss/Compose.agda:142`), and
`UC.Model.Quantitative`. The "importers" column is zero for every row: that is
the review's grep criterion.

| name (file at `c71d95fe`) | deleted by | recorded reason | replacement | recommendation |
|---|---|---|---|---|
| `≈ₚ⇒∼ᴼ` (`UC/Model/Observation.agda:59`) | `1f19f73d` | B Dead | none | **keep**. The step from exact to approximate agreement is a one-liner at use |
| `ctxRun-∘` (`UC/Model/EventBounds.agda:112`) | `1f19f73d` | B Dead | none; `UC.Audit.absorb` is the class-level form | **restore** (now `UC.Machine.EventBounds`). It is the functoriality law of the context run: a morphism in front of the process is the same experiment as that morphism in front of the test |
| `graded-∘ᵒ` (`UC/Model/Graded.agda`) | `1f19f73d` | B Dead | none (`G.Equiv.refl`) | **keep**. It is `refl`, so re-add it with its consumer. `docs/rcom-icom-b1.md` §7 step 4 names it for B2-M6 |
| `ifaceᵒ-onto` (`UC/Model/Seal.agda`) | `1f19f73d` | B Dead | none | **restore**. `ifaceᵒ (objᵒ X) ≡ X` is the seal's section law. `UC.Model.Dominated`'s header relies on it in prose ("`objᵒ` is a section of `ifaceᵒ`") |
| `qbᵢ-monitor` (`UC/Machine/Monitor.agda:118`) | `1f19f73d` | B Dead: "(34 LOC)" | `EventLift.Cov` re-derives its cost (`docs/quantitative-family.md:1398`) | **restore**. The rate-1, `Φ ≡ 0` certificate of the public construction `monitorᴹ` says a monitor is query-transparent, and that is a fact about the construction |
| `monitor-query`/`-answer`/`-flag` (`UC/Machine/Monitor.agda`) | `1f19f73d` | B Dead: "move them to a test module or delete" | none | **restore** into a test module (§3) |
| `adequacyᵍ` (`UC/Seam/Adequacy.agda:118`) | `1f19f73d` | B Dead | `adequacy` at the composite `(plugᴹ a ∘ f) ∘ w`, since `ce039deb` stated `adequacy` at `⟦ strategyEnv B d ∘ u ⟧ᴼ` (`UC/Seam/Adequacy.agda:95-96`) | **keep**. It is now an instance. The docs that name it are stale (§4) |
| `absorb-plugᵍ` (`UC/Seam/Audit/Context.agda:175`) | `1f19f73d` | B Dead | `absorb ŝ 𝔉 k = 𝔉 (k ∙ˢ ŝ)` (`UC/Audit.agda:112-113`), so closure under absorption is definitional at the class level | **keep** |
| `cov-true`/`covL-true` (`UC/Seam/EventTransfer.agda`) | `1f19f73d` | B Dead | none | **keep**. They are trivial instances at flag `true` |
| `prefixedᵒ-scalar`, `massedᵒ-resp-≈` (`UC/Seam/Grounding.agda`) | `1f19f73d` | B Dead | module later deleted | **keep** (§1 Grounding) |
| `sub-graded` (`UC/Graded.agda:65`) | `1f19f73d` | B Dead: an alias of `sub-gradedᵒ` | `sub-gradedᵒ` | **keep** |
| `QueryBound.Counting`, `Counting.counting` | `1f19f73d` | B Dead: an alias of `qbᵢ⇒count` | `qbᵢ⇒count` | **keep** |
| `qb-T₁ᴹ`, `qb-subᴹ` (`UC/QueryBound.agda:636,640`) | `94386bf4` | B8: subsumed by `Grading.qb-T₁ᴵ`/`qb-subᴵ` | `qb-T₁ᴵ`/`qb-subᴵ` | **keep**. The commit says the conclusion is the same |
| `emulAgreeᵁ`, `SimTotal`, `SubBlind`, `subBlind⇒emul`, `simTotal⇒point`, `subPrefixed{ˢ,}`, `≈ᵁ-at`, `Proc≈` (`UC/Seam/Grounded.agda`) | `dd9ebf45` | B1: no consumer since the ledger redesign retired `EndToEnd`'s family premise. B1 "Against it": "`emulAgreeᵁ` is a real theorem" | none | **keep**. The trivial-grade collapse is a statement about one degenerate grade of the sealed model, and its only use was the retired premise. The general parts it rested on are recommended for restoration separately (`Sim.Lax`, `Run.Lax`, `astotal-bind`) |
| `astotal-bind` (`src/ProbabilisticLogic/Dp/Mass.agda`) | `dd9ebf45` | B1 | its halves `const-bind-≼`/`const-bind-≽` survive (`Dp/Mass.agda:163,170`) | **restore→general** (`Dp.Mass`). "An a.s.-terminating prefix is invisible up to every ε" is the natural statement, and it is one line over the surviving halves |
| `astotal-≼ᵐ` (`Dp/Mass.agda`) | `dd9ebf45` | B1 | none | **restore** (`Dp.Mass`). It is the monotonicity of `ASTotal` along `≼ᵐ`, basic closure API of a public predicate |
| `total-dominated` (`Dp/Mass.agda:408`) | `dd9ebf45` | B1 | `squeeze-astotal` (`Dp/Mass.agda:209`) | **keep**. It is a two-line instance |
| `KleisliTriple⇒ᴹ`, `toMonad⇒`, `fromMonad⇒`, `⇒-setoid`, `⇒ᴹ-setoid`, `⇒↔⇒ᴹ` (`src/Categories/Monad/Construction/Kleisli/Ext.agda:48-126`) | `8086f412` | D7 | none. Upstream has `Kleisli⇒Monad` and `Monad⇒-id` separately, but not the translation between the two morphism notions | **restore**. It is the morphism half of the monad ↔ Kleisli-triple correspondence: `KleisliTriple⇒` (unit and extend laws) is equivalent to `Monad⇒-id` pulled back along `Kleisli⇒Monad`, by an `Inverse` on component families (its header). It is general category theory and a candidate upstream contribution |
| `FromPropositional`, `<$>ᴹ-congˡ` (`src/Class/Monad/Ext/Setoid.agda`) | `8086f412` | D7: a third presentation of the same notion | `MonadSetoid` | **keep** |
| `iterₚ-turn`, `iterₚ-done`; `exactˢ⇒≈ₚ` (`src/ProbabilisticLogic/Dp/Iter.agda:244,250`; `Dp.agda:356`) | `8086f412` | D7 | the `iterₚ` fixpoint law with the `returnₚ` identity | **keep** |
| `≼ᵐbot⇒0`, `massless-≈ₚ[0]` (`Dp/Mass.agda:210,214`) | `8086f412` | D7: "likely leftovers of the deleted `Dp.Zero`" | none | **keep** |
| `mass-mono` (`Dp/Mass.agda:74`) | `8086f412` | D7 | `cum`'s budget monotonicity (`src/ProbabilisticLogic/Dp.agda:156-`) at the constant-1 test | **keep** |
| `total-mass` (`Dp/Mass.agda:242`) | `8086f412` | D7 | `Total` itself | **keep**. It only repackages `Total` |
| `astotal-returnₚ`, `const-bind-astotal` (`Dp/Mass.agda:342,348`) | `8086f412` | D7 | none | **restore** (`Dp.Mass`). Closure of `ASTotal` under `returnₚ` and under a bind with an a.s.-total continuation is the predicate's monad-closure API |
| `dmap-ret`, `Dmapⱼ-cong`, `mass-L-toList` (`…/RationalDist/Partial.agda:138,141,59`) | `8086f412` | D7 | `Dmap`/`return` laws, `refl` | **keep** |
| `𝒫-setoid`, `module 𝒫` (`…/Distribution/Possibility.agda:37`) | `8086f412` | D7: two same-named modules for two equalities | `Possibility.Setoids`' `𝒫` | **keep** |
| `Stable-bot` (`Dp/Stable.agda:49`) | `8086f412` | D7 | module deleted (§1) | **keep** |
| `transfer`, `transfer-at`, `≤-shift` (`Protocol/Observe.agda:225-`) | `1d43486a` | C3: zero uses. "`Observe`'s header used to advertise `transfer`" | none | **restore**. A bad-event bound on `P` carries to an indistinguishable `P′` with the advantage added. This is the elementary game-hopping transfer, which a layer-1 user of `≈adv[_]` needs |
| `rawKernel` (`Protocol/Machine/Raw.agda`) | `1d43486a` | C3: zero uses | `Raw.rawPr` (after `a5aaf7c4`) | **keep** |
| `strip⊥`, `trace-mapin`, `trace-mapout`, `trace-cong⊥`, `≈ᵉ-trans⊥`, `≡→≈ᵉ⊥`, `strip-eval`, `strip⊥-cong` (`SFunPartial.agda`) | `97d500a7` | C19: zero uses. `strip⊥` is left-unitor conjugation | generic `λ⇒ᵉ ∘ᵉ (f ∘ᵉ λ⇐ᵉ)` | **keep** |
| `≲ˡ-trans` (`Machines/Sim/Lax.agda:92`) | `dd9ebf45` | C L227 | none | **restore** with `Sim.Lax` |
| `Functionality` (`Examples/RandomOracle.agda`) | `3a36b1fd` | A24, C "Integration-owned": no consumer | the RO step itself (`step`, `step-hit`/`step-miss`, `Lazy.oracle`, `Examples/RandomOracle.agda:55-90`) | **keep**. It was the table repackaged as an `SFunᵉ`, not a theorem |
| `Kⁱ … Kᴵ` (ideal half), `fromQ`, `toQ-fromQ`, `fromQ-toQ`, `fromR-toR`, `Rcomʷ`/`Icomʷ`/`Rcomʰʷ`/`Icomʰʷ` (`Examples/ROCommitment/Realization/{Machine,Bisim,Assembly}.agda`) | `f75bd9c7` | A2: staged for the BLOCKED step B2-M4, and would be rewritten by any `simStep` repair | none (`docs/rcom-icom-b1.md` row B2-M2: "recover from git history") | **keep**. It is staged code for a blocked leg whose machine must change first (§5) |
| `hf-witness` (`Examples/HashForward/Audit.agda:73`) | `aa4d8bb2` | A27: no consumer; "a named result that `docs/quantitative-family.md` cites" | `hf-emul` is now the witness (`Examples/HashForward/Audit.agda:54-58`) | **keep**. The citing doc is stale (§4) |
| `εᴸ-mono` (`Examples/ChimericLedger/Property.agda:95`) | `f2da5997` | A28: no consumer | none | **keep**. A monotonicity of the example's own bound |
| `upᴵ`, `upᴵʰ` (private), `eraseP`, `MerkleDamgard.Core.bad-bound` | `fb0445a9` | A Committed: no use; `bad-bound` restated `badProb-bounded md-cert` | `hop-bound` | **keep** |
| `replay-watch-asks` (`Examples/ChimericLedger/Replay.agda`) | `967680ab` | A Committed: no consumer | none | **keep** |
| `padᴵ` (`Examples/CoinToss/Ideal/*`) | `ec68f2c1` | A Committed: dead | none | **keep** |
| `hash-hit`, `hash-miss` (`Examples/ROCommitment/Resource.agda`) | `d06d2eaf` | A Committed: "lose their last consumers" | `Resource.lazy-hit`/`lazy-miss`, `lazy-bind` | **keep** |

`callC-supp` (`Examples/MerkleDamgard/Core.agda`) was dropped by `a65481a1`
and re-introduced in use by `cb4af285` (`:918`). It is not a deletion at the
tip.

## 3. Deletions that also removed a documented example or test

- **`ProbabilisticLogic.Examples.{BiasedCoin,Coins,MultipleCoins,Weather}`**
  (`74179850`). These were the island's worked examples: a biased coin at
  2/3, joint and conditional bounds at 1/2 and 1/4, and a Markov weather
  chain. D1 notes that they were parametric in `Abstract` and never
  instantiated, and D10 that `Weather` held only at uniform row width.
- **`ProbabilisticLogic.Models.Trivial`** (`74179850`). Its header gave it as
  the consistency check of `Abstract`'s axioms. D10 records that the check was
  vacuous.
- **`SFunM.Spike.Instance.{Rel,RelDist,Setoid,SetoidDist,Type,TypeDist}`**
  (`aed1c111`). These instantiation certificates and `refl` pins of the
  general Mealy layer were the only checks of its generality claim at
  `Rels` and at the full `Setoids` Kleisli category.
- **`UC.Machine.Monitor`'s `monitor-query`/`-answer`/`-flag`** (`1f19f73d`).
  Their banner read "the three behaviours the compiler is accepted on", so
  they were acceptance pins of `monitorStep`.
- **`UC.Robust.Selected.uc-preserves-factors`** (`aa4d8bb2`). This was the
  acceptance test that `ClosedUnder` is exercised at a class other than `⊤ᴬ`.
  It was replaced, not lost: `UC/Robust/Model.agda:31 relay-selectedᵒ`
  applies `uc-preserves-at` at `Factors V` with a real simulator.
- **`adequacyᵍ`** (`1f19f73d`) is item 1(b) of `docs/fcom-extraction.md`
  (`:251`, `:292`). It is now an instance of `adequacy` (§2).
- **`hf-witness`** (`aa4d8bb2`) is the named result `docs/quantitative-family.md`
  cites (`:1270-1271`, `:1326`).
- `Examples.Possibilistic` and `ChimericLedger.ReplayFamily` were
  non-root leaves checked in the D and A verification tables. Their content
  survives (§1), so no test was lost.

## 4. Current documentation that still names deleted modules or results

WP11's second bullet. These are grep hits at `74ce2e18`, not triaged: some are
dated build records, and `9c271400` leaves `docs/protocol-rewrite.md`'s two
mentions deliberately. Recorded only.

| pattern | hits |
|---|---|
| `Seam.Grounding` | `docs/stduc-supersession-plan.md:239,256,295,303,337,415,459`, `docs/uc-module-inventory.md:79` (regenerated here), `docs/history/consumer-migration.md:164`, `docs/dp-transport.md:390`, `docs/rewrite-verdict.md:101,144,264`, `docs/history/prefix-tolerant-audit-plan.md:17,54,100`, `docs/retirement-negligible-order.md:89`, `docs/protocol-rewrite.md:605,922,956-958,1124,1140,1480`, `docs/history/direct-extraction.md:243`, `docs/protocol-implementation-review.md:121` |
| `Robust.Observation` / `Robust.Selected` | `docs/history/retirement.md:259` (records it as KEPT), `docs/history/presheaf-action.md:75,154,155,176,177,183`, `docs/history/consumer-migration.md:256,287,291,352`, `docs/retirement-negligible-order.md:99,119`, `docs/protocol-rewrite.md:572,1495,1630,1631`, `docs/history/direct-extraction.md:228,230,307,309` |
| `Audit.Canonical`, `AuditWitness`/`audit⇒witness`, `hf-witness` | `docs/discard-audit.md:15`, `docs/hash-forward.md:184-185`, `docs/retirement-negligible-order.md:98`, `docs/quantitative-family.md:1270-1271,1307,1326`, `docs/history/issue-quantitative-uc-resources-and-migration.md:123,126`, `docs/quantitative-uc-setup-plan.typ:473,476,477` |
| `adequacyᵍ` | `docs/fcom-extraction.md:251,292`, `docs/fcom-hiding.md:386`, `docs/dp-transport.md:367,429`, `docs/history/graded-bridge.md:71,76,176` |
| `qbᵢ-monitor` | `docs/event-bounds-in-setup.md:724,846,910,1021,1228,1256,1311`, `docs/state-event-contract.md:315`. `docs/quantitative-family.md:16` already records the deletion |
| `Dp.Support` / `Dp.Stable` | `docs/fcom-uc.md:88,103,400,420`, `docs/event-bounds-in-setup.md:1055,1088,1124,1130`, `docs/rcom-icom-b1.md:384`; `docs/dp-transport.md:55`, `docs/rewrite-verdict.md:231`, `docs/protocol-rewrite.md:309,513,1085` |
| `Protocol.Machine.Total` | `docs/ledger-lift-eps.md:227`, `docs/state-event-contract.md:330`, `docs/event-bounds-in-setup.md:830,848`, `docs/ledger-factoring.md:85`, `docs/protocol-rewrite.md:44,490` |
| `Model.Family.Negligible` | `docs/history/retirement.md:217,303`, `docs/graded-observation-redesign.md:56`, `docs/history/uc-presheaf-preservation-plan.md:429` |
| `ReplayFamily` | `docs/state-event-contract.md:123,132` |
| `Sim.Lax` | `docs/discard-audit.md:64,206` |
| other | `ProbabilisticLogic.Prelude` `docs/protocol-rewrite.md:19,55`; `GConstruction{Loop,Tensor}Coherence` `:366,436,437`; `Category/Kleisli/Discrete` `:114`; `SFunM.Spike` `:148-149,341` (C Committed); `Spike.` also in `docs/history/size-reduction-strategies.md`, `docs/history/deepframe-preservation-notes.md`, `docs/history/module-reorg-plan.md` |

Two stale in-source headers were found on the way. `UC/Graded.agda:7` cites
`subBlind`, which `dd9ebf45` deleted. `dd9ebf45` itself says `UC/Audit.agda`'s
comment on `UC.Seam.Grounding` was left stale.

## 5. The commitment repeated-query simulator defect

**Recorded.** The defect is written down in these places:
- `docs/rcom-icom-b1.md` §7, row B2-M3 ("IDEAL SIDE IMPOSSIBLE at the machines as they stand") and row B2-M4 (BLOCKED).
- `docs/quantitative-family.md:1578-1587` (§11 item 4), `:2336-2345` (§14.5 check 5, "BLOCKER, still listed") and `:2363-2365` (§14.6 item 2).
- In source: `Examples/ROCommitment/Realization/Bisim.agda:247-265`, the banner "Where the ideal leg stops" with `sim-log-repeat`, `extract-relog` and `extract-table`, kept by `f75bd9c7` as "the obstruction record".
- `Examples/ROCommitment/Realization/Bound.agda:8-10` (header: "the machine leg is blocked by `Realization.Bisim`'s `extract-relog`").
- `Realization/Bisim.agda:9-10`.
- A31 (the open-domain premise of `coin-toss-from-com{,ʰ}`/`coin-toss-ideal*` may be unsatisfiable; `Realization/Assembly :: assembly{,ʰ}` are the real statements).
- A34 (`respRʰ`/`respIʰ` are hand transcriptions that no theorem connects to the protocol; `docs/fcom-hiding.md` "Not delivered" 1/3).

**State at `74ce2e18`.** `simStep`'s relay clause still conses
`(x , d)` onto the log at every relayed answer
(`Examples/ROCommitment.agda:167-168`). The line citations `:193-:214` in
`docs/quantitative-family.md` predate the current layout, and so does
`Realization/Statement.agda:51-52`: that file does not exist, and
`Realization`/`Realizationʰ` are `Realization/Assembly.agda:60-62`. The shared
lazy-oracle work in the range changed only the oracle side and did not touch
`simStep`:
- `97cd3cc2` added `RandomOracle.Lazy` (`Examples/RandomOracle.agda:67-`), used by MerkleDamgard.
- `d06d2eaf` added `Resource.lazy-bind`.

**Repair components** (WP11's list) against the record:
- *Deduplication by query point.* RECORDED as the maintainer call "`simStep`
  caches (only cons a point the log does not already answer)"
  (`docs/rcom-icom-b1.md` B2-M3). The alternative is restating `Game.respI`
  over the relay log, which makes `Game.cert` false. NOT implemented.
- *A repeated-query regression.* NOT RECORDED as such. The existing
  `sim-log-repeat`/`extract-relog`/`extract-table` witness the defect; they
  are not a regression test for a repaired simulator.
- *The reachable log/table relation.* NOT RECORDED. B2-M3 says "no state
  relation can repair it" for the current machine; no relation is stated for
  a caching one.
- *The missing realization theorem.* RECORDED as missing: `Realization` and
  `Realizationʰ` stay hypotheses, and `assembly`/`assemblyʰ` are conditional
  (`docs/quantitative-family.md` §14.5 check 5).

## 6. The real-hash assumption

**Recorded.** The ledger's random-oracle premise is `hash ≤UC^ωⁿ oracle^ω`,
the explicit hypothesis of `ledger-preserves-value-from-hash`
(`Examples/ChimericLedger/Transfer.agda:163-164`, with `hash-liftⁿ` `:159`,
`hash-liftᵇ` `:151` and `oracle^ω` `:101-102`). It is recorded as "RECORDED,
NOT DISCHARGED" at `docs/quantitative-family.md:2356-2362` (§14.6 item 1) and
`:1888`. The same place notes that `Examples.MerkleDamgard.indistinguishable`
(`Examples/MerkleDamgard.agda:141`) is stated at `≈adv[_]` over fixed-length
messages, so an instance needs a padding adapter and a `_≤UC^ωⁿ_` proof.

No collision-resistance replacement exists. A case-insensitive grep for
`collision.?resist` over `src` and `docs` finds nothing, so the premise has
not been replaced. The citation `Transfer.agda:190` in
`docs/quantitative-family.md:1862,2357` is stale; the declaration is at `:163`.
`docs/chimeric-ledger-proof-boundaries-plan.md:98` separately lists "the
required repeated-query behavior of the concrete lazy oracle" as work, not
done.

## 7. Summary

Counts:

| recommendation | §1 modules | §2 names (rows) |
|---|---|---|
| keep | 44 | 29 |
| restore | 3 (`Sim.Lax`, `Run.Lax`, `Spike.Instance.Rel`) | 9 |
| restore→general | 5 (`CommutativeMaybe`, `Instance.RelDist`, `KleisliDistributive`, `Bernoulli`, `Binomial`) | 1 |
| total | 52 | 39 |

Of the 44 modules marked keep, 21 were renamed, moved or merged with their
content intact: `ReplayFamily`, `Possibilistic`, the four `SFunM.Kleisli*`,
the eight Spike modules with a live twin, `UC`, `UC.Model`,
`Model.Family.Negligible`, `Kleisli.Discrete.Pure`, `Dp.Support`,
`Prelude` and `Data.Sum.Ext`.

**Items where I disagree with the deletion:**
1. **The finite-probability results** `Distribution.Bernoulli` and
   `Distribution.Binomial` (`74179850`). The island's axiomatic carrier
   deserved retiring. Its concrete finite-probability theorems did not:
   biased coins, binomial `pᵏ`, and expected count k·m/(m+n). The live
   `Dist-ℚ` library has no counterpart, so they should be restated there.
2. **`KleisliDistributive` and `CommutativeMaybe`** (`aed1c111`) are general
   category theory, with no live or upstream counterpart, that was deleted
   together with a spike tree. So is the fact inside `Instance.RelDist`.
3. **`Sim.Lax`, `Run.Lax` and `Dp.Mass`'s `ASTotal` closure API**
   (`astotal-bind`, `astotal-≼ᵐ`, `astotal-returnₚ`, `const-bind-astotal`;
   `dd9ebf45`, `8086f412`). This is general machine and probability
   mathematics that was deleted with its one UC-specific consumer.
   B1 raised the rule-32 objection before the deletion.
4. **`KleisliTriple⇒ᴹ` / `⇒↔⇒ᴹ`** (`8086f412`) is the morphism half of the
   monad ↔ Kleisli-triple correspondence.
5. **`Protocol.Observe.transfer`/`transfer-at`** (`1d43486a`) is the
   elementary bound-transfer step across `≈adv[_]`.
6. **Public API of live constructions:** `qbᵢ-monitor` with the
   `monitor-*` acceptance pins, `ifaceᵒ-onto` and `ctxRun-∘` (`1f19f73d`).
7. **Process, not content:** `UC.Robust.Observation` (`aa4d8bb2`) —
   ruled: scope decision, see `docs/history/retirement.md` §7.
