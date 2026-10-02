# Open items

Open suggestions from the quality-review rounds and the retired plans, verified against `src/` at
`8f05fb41` and trimmed after the round-3 leftovers landed; maintainer rulings are excluded. Each
line: `module :: definition` — size — why.

## Solver

- `Categories/GConstruction{Identity,Hom,Trace,Embedding}Coherence.agda, GConstructionCoherence/{Terms,Wiring}.agda :: αᵗ βᵗ γᵗ midᵗ, instance S≤S` — ~−40 LOC — the same free-wiring terms are copied in 4–6 files; one shared `FreeWiring sig` module, measured against `Wiring`'s same-`sig` fast path.
- `Categories/GConstruction{,Trace,Embedding,Monoidal}.agda :: Cˢ` — −9 LOC — the same `record { U ; monoidal ; symmetric }` built in four files; make it public once in `GConstructionTrace`.
- `Categories/GConstructionEmbedding.agda :: ⌜_,_⌝, ⌜⌝-id, ⌜⌝-resp-≈/-∘/-≅, unitorˡᴳ/unitorʳᴳ/associatorᴳ`, `GConstructionLoop.agda :: trace-conj` — placement, ~0 LOC — `⌜⌝-*` are the functor laws of `C × Cᵒᵖ → G` (package a `Functor`, then `⌜⌝-≅` is upstream's `[_]-resp-≅`); `⌜⌝-id` uses no trace law; `trace-conj` belongs in `GConstructionTrace.WithTrace`.
- `Categories/Monad/Graded/Uncurried.agda` — one root import line, or delete — no importer and not in the root, so it is never checked.

## Foundations

- `Class/Monad/Ext.agda` — flag only — orphan with no importer, so unchecked.
- `ProbabilisticLogic/Dp/Mass.agda :: total-resp-≼ₚ` — ≈ −3 LOC — zero consumers (keep `Dp :: laterₚ-≈ₚ`, rule 32).
- `ProbabilisticLogic/Dp/Mass.agda :: split, scale, expand, collect, product, 1-≤, shift` — move — unit-interval ℚ facts for `Data.Rational.Properties.Ext`.
- Hand-rolled `0 ≤ a + b` / `x ≤ x + y` at `Dp.agda`, `Uniform/{Duplicate,Collision}`, `GamePlaying/Potential`, `MerkleDamgard/Core`, `UC/Machine/Dominated` — ~−15 LOC over ~8 files — add `0≤+` beside `Data.Rational.Properties.Ext.p≤p+q` and use both.
- `ProbabilisticLogic/Dp/Mass.agda :: mapₚ-≼ᵐ` — −4 LOC — the `cum-cong-P`/`>>=ₚ-boundB` sandwich is `mapₚ-cum` used directly.
- `ProbabilisticLogic/Distribution/Uniform/Birthday.agda :: 0≤scaled, sumN (+ sumN-mono, sumN-≤, square)` — −2 LOC, placement — `0≤scaled` is `0≤*`; `sumN` is pure ℕ inside a module parameterised by an unused `n`, home `Data/Nat/Properties/Ext`.
- `ProbabilisticLogic/Distribution/RationalDist/Expectation.agda :: Prᵇ⊥` — ±0 — define as `E⊥ μ (indᵇ b)`, the same term.
- `ProbabilisticLogic/Distribution/Uniform.agda` header — 1 line — describes only `P-uniform-Vec`.
- `Categories/Category/Construction/Kleisli/Discrete.agda :: ≈ᵏ-isEquivalence`, `Monoidal/Distributive/Instance/Rels.agda :: δ⁻¹` — −3 / −4..−8 LOC — stdlib pointwise setoid; graph of `×-distribˡ-⊎`'s inverse.
- `ProbabilisticLogic/Distribution/{Bernoulli,Binomial}` (deleted) — ~370 LOC, restate at `Dist-ℚ` — no biased coin, binomial `pᵏ` or expected count `k·m/(m+n)` in the live library; retirement review disagreed with the deletion.

## Machines / Protocols

- `CategoricalCrypto/Machine/Core.agda` dead half (`_∣ʳ`, `liftᴷ`, `_⊗ʳ_`, `⊗-assoc*`, `idᴷ`, `transpose`, `⨂₁`, `_∘ᴷ_`, `Trace`/`Invariant*`, `OAP`/`_≈ℰ_`/`_≤UC_`) and `Channel/Core.agda` (`destruct-⊗`, `⊗-*-assoc`, `⊗-*-neutral`, `⨂*`) — ≈ −135 LOC — zero uses inside the kept legacy layer; `_≈ℰ_` there is intensional `≡`, so the "complete by dummy adversary" comment is unproved.
- ~16 private `module MC = Core (𝒱ₚ 0ℓ)` copies — ≈ −30..−50 LOC — one public instantiation set in `Machines.Base`; blocked earlier by `ShadowedModule` in openers that define their own, so measure.
- `CategoricalCrypto/GamePlaying/Hop.agda :: FLGP` — 0 LOC — a special case of `runWith-join` not derived from it.
- `CategoricalCrypto/GamePlaying/Average.agda :: badProb-avg, AvgDrift` — design call — `SuperCert` could be the `V ≡ ⊤` case; `AvgDrift` is CPS rather than a shared-randomness kernel.
- `CategoricalCrypto/GamePlaying/Partial.agda :: cond, cond-diag` — ≈ −6 LOC — stdlib `if_then_else_`/`if-eta`.
- `CategoricalCrypto/Machines/{Frame :: 𝕄, Tensor/Assoc :: ⊗-split implicits}` and dead opens in `Trace`, `Trace/{Fubini,Vanishing}` — ≈ −8 LOC — single-use aliases (`𝕄` moves to `Reassoc` beside its solver calls if kept).
- `CategoricalCrypto/Protocol/Safety.agda` header — 1 line — owes that `hitFrom` samples only at activation boundaries (documented in `Observe`).
- `CategoricalCrypto/Interaction.agda :: runWith⊥-emb` — −4 LOC — via `>>=ᴹ-congˡ`.
- `CategoricalCrypto/Machines/Pure.agda :: ∘-pureᴹ, ⊗-pureᴹ` → `Tensor` — placement — skipped in round 3: the move needs `Machines.Category` in `Tensor`.
- `CategoricalCrypto/Machines/Base.agda :: Elgotᵏ` private — small — skipped in round 3.
- `CategoricalCrypto/Machines/Collapse.agda :: γ-pure, compose≈∘ᴳ` — −7 LOC, 1 comment — `γ` is `α` with `id ⊗₁ σ⇒` appended, so the chain is `∘ᶠ (⊗ᶠ idᶠ σᶠ) (α-pure …)` (perf-pinned); `compose≈∘ᴳ` is `S.reflᴹ`, an elaboration pin that reads like a theorem.
- `CategoricalCrypto/Machines/Sim/Lax.agda :: ≲ˡ-trans, _≈ˡ[_]_, ≲⇒≲ˡ, ≲ˡ-refl, ≲ˡ congruences` — −6..−65 LOC or 1 header line — zero consumers (`Run/Lax` uses only the record); module itself is KEEP by ruling.
- `CategoricalCrypto/Machines/Base.agda :: 𝒢ₚ-Monoidal; 𝒢ₚ/Tracedₚ/ℳₚ` — −2 LOC; perf — `𝒢ₚ-Monoidal` has zero uses; `Base` imports `Machines.G`, so most importers pay for the G closure they never use (split the G side out, measure).
- `CategoricalCrypto/GamePlaying.agda :: Coupling`/`Coupling⊥` duplicate `fR`/`fI` — ≈ −4 LOC — skipped in round 3.
- `CategoricalCrypto/Protocol/Observe.agda :: transfer, transfer-at, ≤-shift` (deleted) — ~20 LOC, restore — the elementary game-hop step (bad-event bound carries to an `≈adv`-close `P′`) has no replacement.
- `Machines.*` at the `Rels` base (old `SFunM.Spike.Instance.Rel`) — ~100–170 LOC test — nothing checks the general Mealy layer at a non-Kleisli base.
- Comment pass remainder over the R3C scope: the `Machine/Core` TODOs.

## UC core

- `CategoricalCrypto/UC/QueryBound.agda :: QB` / `QueryBound/Counting.agda :: qbᵢ⇒count, CountBound` — ~15 LOC proof work + a test — the counting bound is proved for the certified representative `N`, nothing carries it to `M` (`N ≈ᴹ M`); needs a `traceᵍ`-simulation off `Run.step-sim`; `Counting` itself has no consumer, pin it (rule 33).
- `CategoricalCrypto/UC/QueryBound.agda :: qbᵢ-T₁ / qbᵢ-sub` — ≈ −55..−65 LOC — twin 70-line blocks differing only in the ancilla summand; one side-parameterised private module, or derive `qb-subᴵ` as `σ ∘ T₁ᴵ ∘ σ`. Perf-sensitive.
- `CategoricalCrypto/UC/QueryBound.agda:69-93` private copy of `Dp.Reasoning` (`_⟨≈⟩_`, `bindᶠ`, `map-arg`, …) — ≈ −22 LOC — bare-open `Dp.Reasoning` instead; the earlier timing objection is weaker now.
- `CategoricalCrypto/UC/QueryBound.agda :: qbᵢ-wire, qbᵢ-closed, qbᵢ-upward` — ≈ −8..−15 LOC — share `pointᵍ`/`coh₀`/`cohR`; `qbᵢ-wire`'s `onRᵍ` stops being literal `returnₚ` in perf-pinned towers — measure.
- `CategoricalCrypto/UC/QueryBound/Compose/Laws.agda :: qb-∘` — −12 LOC — only consumer `qb-∘-category`, which can go raw≈∘ᴳ, ⟺, raw≈∘ᴳ; kept in round 3: one consumer.
- `CategoricalCrypto/UC/QueryBound/Compose/Step.agda :: Nᶜ, unfoldᶜ, eq-∘ᶜ` — placement — a public reading of a `𝒢ₚ` composite with nothing about query bounds; belongs in `Machines.*` beside `Collapse`.
- `CategoricalCrypto/UC/Machine.agda :: outT, subᴵ.outS` — small — `outT` is `Sum.map inj₂ inj₂`; inline into the relays (71 importers, measure).
- `CategoricalCrypto/UC/Machine/Monitor.agda :: compileᴹ` vs `flagReader` — stage 1 ≈ −10, stage 2 ≈ −250..−400 LOC — `compileᴹ B μ Y E ≈ flagReader B Y E ∘ T₁ᴵ Y μ` (spiked green); define `HitsAt` as `BoundedAt` of the flag reader; stage 2 merges the two "+1 certificate" developments (`StateEvent/Lift :: FlagCert/flagSkeleton/flag-slide` vs `Dominated`'s monitor cert) via a simulation `monitorᴹ report ∘ u ≈ᴹ u′ ▷ acc` (crux unspiked).
- `CategoricalCrypto/UC/Machine/StateEvent/Agree.agda :: embeds` vs `Seam/Budget.agda :: stratTest-embeds` — ≈ −6 LOC — two wire proofs of one embedding; skipped in round 3: needs `λᴵ⇒ ∘ λᴵ⇐ ≈ id` in 𝒫ᴵ.
- `CategoricalCrypto/UC/Machine/StateEvent/Lift.agda :: flag-slide.bottom/w, a⇐-sub, covered, ≈⇒cofinal` — ≈ −13 LOC — duplicate `Monitor/Slide`-style core (one exported `T₁ᴵ Y λᴵ⇒ ∘ (a⇒ᴵ ∘ subᴵ m) ≈ subᴵ (ρᴵ⇒ ∘ m)` in `UC/Machine/Slide`); `≈⇒cofinal` is a missing `≈ₚ⇒cofinal` for `Dp`.
- `CategoricalCrypto/UC/Machine/StateEvent/Adequacy.agda :: hitK` vs `Protocol/Observe.agda :: hitFrom` — ≈ −5 LOC — same three clauses over a kernel; generalise one over a state `Set`.
- `CategoricalCrypto/UC/Machine/{Slide,Wire}.agda` — small — the same implicit telescope re-bound in 8–9 signatures with no `private variable` block.
- `CategoricalCrypto/UC/Machine/Dictionary.agda :: ⊗ᵉ-pureˡ/ʳ; T₁-resp-≈, sub-resp-≈, T₁-∘, sub-∘` — rename; ≈ −18 LOC — collide by name with `Machines.Tensor.Structural`'s with opposite handedness; the four laws are one "family ≈ F₁ inherits the functor laws" lemma (perf-pinned, measure).
- `CategoricalCrypto/Iface.agda :: unitᴵ` vs `UC/Machine/Dictionary.agda :: 𝟭ᴵ` — −80..−120 LOC, multi-session — two empty interfaces force two unitor-wire families plus `Slide`'s hole-wire apparatus; spike `unitᴵ = 𝟭ᴵ`.
- `CategoricalCrypto/UC/Model/Enrichment.agda :: imageᵒ` → `Categories/LocallyGraded/SubCategory.agda` — small — a general `pred⇒image` fact sitting in the model, with hand-spelled copies elsewhere.
- `CategoricalCrypto/UC/Seam/Grounded.agda :: plug-run` vs `UC/Seam/Plug.agda :: Plugged.collapse` — small — two spellings of "observe env ∘ u".
- `CategoricalCrypto/UC/Seam/{Plug,Extract,Transfer}.agda` — placement, 3 modules — machine-layer content with no seam notion; move under `UC/Machine/`; `Plug :: obs-resp` collides by name with `UC/Model/Observation.obs-resp`.
- `CategoricalCrypto/UC/Seam/Transfer.agda :: ρᴷ, ρᵁ` vs `Seam/Adequacy/Wiring.agda :: outE, outU`; `Seam/Extract :: coinᵈ, E-coinᵈ`; `Seam/{Adequacy,Plug} :: point-red` — ≈ −15 LOC — same dispatch written twice; `coinᵈ` facts belong in `Dp.Coin`; `point-red` re-proves `Pointwise.point-⊛`.
- `CategoricalCrypto/UC/Model/Enrichment.agda :: qbᵘ, procᵘ` → `Model/Graded :: procᵘ-∘, plug-gradedᵒ` → `UC/Graded :: plug-graded` — −30 LOC — a chain whose last link has no consumer.
- `CategoricalCrypto/UC/Model/Seal.agda :: M._∘_ g f` — small — zero consumers (rule 32); `QueryBound/Object` header owes the line that `qb-∘ᴳ` lives in `Compose/Laws`.
- `CategoricalCrypto/UC/Core.agda :: Observable, Θ, ≋-cast` — ≈ −45 LOC — general presheaf record with one producer (`Evaluation.observable`); define `Test`/`_≋_`/`pull`/`ℰᴼ` in `Evaluation`.
- `CategoricalCrypto/UCSetup.agda :: faithful⇒grade-stable, GradeStableFromTests`, `UCSetup/Morphism :: idᵁ, composeᵁ, identity laws, module Factorization`, `Abstract2/Morphism :: transfer-impossible, epi⇒preserves-≈ℰ, mono⇒reflects-≈ℰ`, `Abstract2/WideSubcategory :: W-ext, coarsen, epi⇒coarsens, restrict-dummy, Fine, Trivial`, `Abstract2 :: UC-dummy-sim, UCᵈ-sim, ≤UC-resp-≈, ≤UCᵈ⇔≤UC, ≤UC-sub` — ≈ −150 LOC — dead internals of the setup-morphism layer; the "Identity and composition" banner promises a category never built.
- `CategoricalCrypto/Abstract.agda :: Iᵤ, car, grd, U-≋, atk-idˡ`, `Abstract2 :: UC-compose re-binding f g` — ≈ −20 LOC — dead names in the kept island.
- State-event transport for open systems — ~150–250 LOC proof work — `stateLift` handles closed systems only; a bound carried through a simulator needs a `collapseᵀ`-compatible projection or a permitted-class route.

## Quantitative

- `CategoricalCrypto/UC/Family/Vanishing.agda`, `UC/Family/Negligible/Setup.agda` — ≈ −95 LOC, −2 modules — each tier applies `Std2.StdUC` twice (private `Std^ω`/`N` then public `Canonical^ω`/`Canonicalᴺ`); make the private ones public and delete both; heap crux: `Family/Negligible` bare-opens `UC.Family`, give it a `using` and measure.
- `CategoricalCrypto/UC/Quantitative/Query.agda :: Qᵠ, 𝒞ᵇ, _≈ᵇ_, absorb-test, absorb-closure`, `Approx/Schedule.agda :: reindex-cong` — ≈ −55 LOC — presheaf packaging with no consumer (`Contextual` uses `pullᵠ`/`filteredᵠ`/`Budgeted` directly); `absorb-*` consumed only through `proj₁`, inline.
- `CategoricalCrypto/UC/Quantitative/EventLift.agda :: agree` — small — public, single use (`hits⇒upper`); kept in round 3: it is cited.
- Comment trims from R3B not re-verified: `Exact` header (repeats `Counting`'s), `Family/Quantitative`, `Neg/Setup`, `Model/Observation`, `Core`, `Query`, `Grounded`, `Contextual`, `Machine/Dominated` duplicate (88-89 vs 214-216), `Controlled`/`Error`/`Filtered`/`Separating` headers.

## Examples

- `CategoricalCrypto/Examples/ROCommitment/Realization/Assembly.agda :: Realization, Realizationʰ` — proof work — the F_com UC-level ε-statement is still a hypothesis; the binding ideal hop (B2-M3/M4) is blocked by the `simStep` defect below, the hiding counterpart (`raw-emulationʰ`) was never started.
- `CategoricalCrypto/UC/Model/Graded.agda :: graded-∘ᵒ` — small (`G.Equiv.refl`) — B2-M6 of `docs/rcom-icom-b1.md`, absent; re-add with the `Realization` proof.
- `CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Compose.agda :: coin-toss-idealʳ` — proof work — no exact receiver hop; the `+2⁻ⁿ` comes from `UC.Machine.Dominated.dominated` requiring `0 < δ`.
- `CategoricalCrypto/Examples/CoinToss/Test.agda` — proof work — no closed-game `Dist-ℚ` bound for the composed coin toss or the ideal coin.
- `CategoricalCrypto/Examples/ChimericLedger/Transfer.agda :: chimeric-not-preserving` — open question — the attack starts account-funded, which the UTxO genesis never reaches (`System.ledger-keeps-accts-[]`); whether the chimeric variant loses value from the UTxO genesis is undecided.
- `CategoricalCrypto/Examples/ROCommitment.agda :: simStep` — repair + regression test, maintainer's call — conses `(x , d)` onto the log on every relayed answer, including repeats, so `extract` disagrees with `Game.comI`; fix = cache and add only points the log does not already answer, plus a log/table state relation.
- `CategoricalCrypto/Examples/ROCommitment/Hiding/Asymptotic.agda :: εᵗ`, `Hiding/Game.agda :: respRʰ, respIʰ` — proof work — end-to-end hiding constant is `3q·2⁻ⁿ` (one merged hop `respIʰ → respRʰ` would plausibly give 2); `respRʰ`/`respIʰ` are hand transcriptions of `realʰ` and `idealʰ ∘ simulatorʰ` with no theorem connecting them to the machines; B2-M4 `binding-bound` is blocked on the deleted ideal-side `Ranked` instances.
- `CategoricalCrypto/Examples/ChimericLedger/Transfer.agda :: ledger-preserves-value-from-hash` — proof work — the premise `hash ≈ᶠᴺ oracle^ω` is never discharged; `MerkleDamgard.indistinguishable` is at `≈adv` over fixed-length messages, so it needs a padding adapter plus a family-emulation proof.
- `CategoricalCrypto/Examples/Basic.agda :: Encryption.Dec` — ruled 2026-10-02: leave main's behaviour; flagged — computes `p = lookupPlainText …`, ignores it and returns `inj₁ c`, so `DecRcv` is uninhabited and `SecureFromAuthenticated` can never deliver; fix `return just $ L⊗ ϵ ↑ₒ inj₂ p`.
- `CategoricalCrypto/Examples/CoinToss/Ideal/Compose.agda` vs `Receiver/Compose.agda` — −15..−20 LOC — `simᶜⁱ/simᶜʳ`, `coin-toss-ideal/ʳ`, `coinRealʷ/ʰʷ`, `coin-toss-idealᴺ/ʳᴺ` differ only in the first-hop certificate; one parameterised second-stage module; skipped in round 3: the corrupted party's channel is implicit, the crux of the merge. Also `Receiver/Compose :: ηʰ = 0ℚ + 2⁻ⁿ` (write `2⁻ⁿ`, ±1).
- `CategoricalCrypto/Examples/CoinToss/Ideal/{Machine,Hybrid}` vs `Ideal/Receiver/{Machine,Hybrid}` :: `hybridᴹ, idealᴹ, hybrid-eq, ideal-eq` — −60..−90 LOC, unspiked — composite scaffolding duplicated per corruption (a layer below the Compose item above); `Hiding.agda :: CoinAʰ` is a copy of `CoinToss.CoinA` with renamed constructors (−4, ~7 files).
- `CategoricalCrypto/Examples/CoinToss/{Compose,Ideal/Compose,Ideal/Receiver/Compose}.agda :: coin-toss-from-com*, coin-toss-ideal*` — statement audit — they assume the commitment emulation at the OPEN resource domain, which `docs/rcom-icom-b1.md` suggests is unsatisfiable (then `Assembly :: assembly{,ʰ}` are the real statements); confirm or demote.
- `CategoricalCrypto/Examples/CoinToss/Ideal/{Hybrid,Machine,Receiver/Hybrid}.agda :: hyb-sim, idl-sim, hyb-simʰ` and `Protocol/Machine/Compose :: CSt, stateᶜ, serveᶜ, …, π-sim, ι-sim` — interface — public statements over private machines (`Hᴺ`/`Iᴺ`); privatize the sims or publish the machines.
- `CategoricalCrypto/Examples/CoinToss/Ideal :: Fcoin, Fcoinʰ`, `Receiver/Reach :: endᴰ` — design calls, 0 LOC — `Fcoin` leaks in two steps and has no fairness parameter, `Fcoinʰ` has no abort, `endᴰ` keeps the drawn bit.
- `CategoricalCrypto/Examples/ROCommitment/Hiding/Test.agda` redundant `import … as G` — 1 line — kept in round 3: dropping it takes the warm check from 7 s to 84 s.
- `CategoricalCrypto/Examples/ROCommitment/Extraction.agda :: lookupPt lookup-here lookup-there` — −14 LOC — are `RandomOracle.lookup-bs{,-here,-there}` at `Pt`/`Dig` (argument order differs, heavier import); skipped in round 3.
- `CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: MDInvData` — −6 LOC — single-inhabitant record.
- `CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: sumR, sumR-tri, tri-mono; chunk-inj, toList-inj, snoc-view, lookupAll; proj₁ (proj₂ …) ×95; 13 private blocks` — ≈ −45 LOC + legibility — two encodings of the triangle number; stdlib `Vec.group`/`toList-injective`/`initLast`/`All.lookup`; named accessors.
- `CategoricalCrypto/Examples/MerkleDamgard/QueryBound.agda :: onEnter i [] e` (and `onAdvance`/`onEnter-coh` `[]` clauses); `qbᴹᴰ, certifiedᴹᴰ` — hygiene, pin — unreachable clauses (`NonZero k`) return a plausible value instead of `⊥-elim`; `qbᴹᴰ` has no consumer and no pin.
- `CategoricalCrypto/Examples/ChimericLedger/Birthday.agda :: lookup-bs-∈` vs `MerkleDamgard/Core :: lookup⇒mem`; `RandomOracle.agda :: count-matches, sum-bound, E-collisions*` — −8 / −30 LOC — one `(q , h) ∈ s` form beside `lookup-bs`; `count-matches` is a special case of `Uniform/Collision :: countMatch`.
- `CategoricalCrypto/Examples/ChimericLedger` small items — ≈ −25 LOC — three private `DecEq-×′` copies of `Prelude.DecEq-×′` (skipped in round 3); `Value :: Shape.accepted` should carry `eb` (`applyTx-total-fresh` re-walks the `with` cascade); `Birthday :: presTree, φ-step` repeat the `with shape …` cascade (one activation view, ≈ −25).
- `CategoricalCrypto/Examples/{ROCommitment/UC, ROCommitment/Hiding/UC, ROCommitment/Realization/Assembly, CoinToss/UC, CoinToss/Ideal/Compose, CoinToss/Hiding/UC, CoinToss/Ideal/UC, CoinToss/Ideal/Receiver/UC}.agda` — −8 import lines — import `UC.Model.Dominated` and use no name from it.
- `CategoricalCrypto/Examples/ROCommitment :: sim-hash-count` — design call — the simulator queries the oracle at the opening.
- Merkle–Damgård as the ledger's hash instance — proof work — would discharge the hash premise above together with the padding adapter.

## Docs / Tests

- `CategoricalCrypto/Protocol/Machine/Pin.agda :: machine, agree, agree₊₁, agree₊₂, machine-∘` — interface, ≈ −6 LOC — pins fix `cum` at hand-tuned depths 5/6/8 (restate as the `Σ n ∀ m` witness); `machine-∘` is derivable and the three depths sample one family.
- Per-layer pin gaps — new test lines — `Dp.Elgot`'s laws and `Machines.Base`'s `ℳₚ`/`Tracedₚ`/`𝒢ₚ` have no behavioural pin; `UC/QueryBound/Counting` and `UC/Family/Quantitative`'s `≤UC` pair likewise.
- Unfinished sweep classes (toolkit): `implicit-drop`, `binder-drop`, `join-lines`, `using-minimize`, `import-drop` over the R3 scopes (A: 60 files; B: 92; C: 24 remaining; D: 63 / 42 remaining); `enum-with` (A 93, C 23, D 11 sites) and `enum-where` (A 192, B 125, C 126, D 162 sites) enumerated but not dispositioned; `StateEvent/Lift.agda` needs a by-hand sweep (toolkit parse error). `import-drop` over `Examples/{ROCommitment,MerkleDamgard,HashForward}/**` (~700 import lines) never run. Run after a store GC, one session. The canonical `.claude/sweeps/{with_case,where_inline}.py` still carry the W2 bugs (unparenthesised `yes p` inside `λ where`, needless parens around an atomic RHS, `with` matched inside comments) — two one-line fixes.

## Deferred by maintainer

- The `flake.nix` pin of `agda-stdlib-meta@algebraic-solvers` (rule 35 flag); the solver upgrade to `de26b487` is in the stack's base.
- `simplification-options.md` §1: total, rate-certified machines with bounded-unrolling composition (est. −8–10k LOC) — not adopted.
- `simplification-options.md` §2.2 full version: rebuild `Dp/**` over a lower-real carrier (~4k LOC), the only route left that deletes `cum`/`Cofinal`/`Dom` — unspiked.
- `simplification-options.md` §2.4: small-step composition with the supremum taken only in the runner — win uncertain, unspiked.
- `Abstract`/`Standard`/`OAPEmulation`/`Equivalence` island, `RandomOracle{,2}`, `Channel/*`, `Machine/*` — keep by ruling; if `Abstract` ever goes, `Abstract2`/`Standard2` are fossil names (16 importers).
