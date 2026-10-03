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
- `CategoricalCrypto/GamePlaying/Average.agda :: badProb-avg, AvgDrift` — design call — `SuperCert` could be the `V ≡ ⊤` case; `AvgDrift` is CPS rather than a shared-randomness kernel.
- `CategoricalCrypto/GamePlaying/Partial.agda :: cond, cond-diag` — ≈ −6 LOC — stdlib `if_then_else_`/`if-eta`. Declined round 4: the prelude's `if_then_else_` is `Class.ToBool`'s (thunked branches, `case`-defined), and stdlib's needs a renamed import at each of ~10 consumers — no saving.
- `CategoricalCrypto/Interaction.agda :: runWith⊥-emb` — −4 LOC — via `>>=ᴹ-congˡ`. Declined round 4: it already goes via `>>=ᴹ-congˡ`, and dropping any of the three `Mℚ.trans` implicits leaves unsolved metas.
- `CategoricalCrypto/Machines/Pure.agda :: ∘-pureᴹ, ⊗-pureᴹ` → `Tensor` — placement — skipped in round 3: the move needs `Machines.Category` in `Tensor`. Re-tried round 4: crux stands (`∘ᴹ-resp-≈ᴹ` is in `Machines.Category`, which `Tensor` does not import).
- `CategoricalCrypto/Machines/Base.agda :: Elgotᵏ` private — small — skipped in round 3. Declined round 4: rule 32 — the `Dₚ` iteration lemmas are foundational, not a bespoke one-off.
- `CategoricalCrypto/Machines/Collapse.agda :: γ-pure` — −7 LOC — `γ` is `α` with `id ⊗₁ σ⇒` appended (perf-pinned). Declined round 4: `GConstructionTrace.γ` is right-nested, so `id ⊗₁ σ⇒` is its innermost factor, not a post-composite of `α`, and `α-pure`'s proof does not reuse without an associativity step.
- `CategoricalCrypto/Machines/Base.agda :: 𝒢ₚ/Tracedₚ/TraceLawsₚ/𝒢ₚᴹ` — perf — split the G side out of `Base`. Declined round 4 (measured): loading `Machines.G` costs a G-free importer ≈ 1.6 s warm (Pointwise 7.3 → 5.7 s, Pure 9.5 → 7.9 s without it), but only `Machines.{Pointwise,Pure,Sandwich}` are G-free — `Protocol.Machine`, `UC.Machine` and `Collapse` use `𝒢ₚ`.
- `CategoricalCrypto/GamePlaying.agda :: Coupling`/`Coupling⊥` duplicate `fR`/`fI` — ≈ −4 LOC — skipped in round 3. Declined round 4: consumers read `C.fR`/`C.fI` off each module, so sharing them needs an `open … public` layer (rule 19) for a net ≈ 0.
- `CategoricalCrypto/Protocol/Observe.agda :: transfer, transfer-at, ≤-shift` (deleted) — ~20 LOC, restore — the elementary game-hop step (bad-event bound carries to an `≈adv`-close `P′`) has no replacement.
- `Machines.*` at the `Rels` base (old `SFunM.Spike.Instance.Rel`) — ~100–170 LOC test — nothing checks the general Mealy layer at a non-Kleisli base.
- Comment pass remainder over the R3C scope: the `Machine/Core` TODOs.

## UC core

- `CategoricalCrypto/UC/QueryBound.agda :: QB` / `QueryBound/Counting.agda :: qbᵢ⇒count, CountBound` — ~15 LOC proof work + a test — the counting bound is proved for the certified representative `N`, nothing carries it to `M` (`N ≈ᴹ M`); needs a `traceᵍ`-simulation off `Run.step-sim`; `Counting` itself has no consumer, pin it (rule 33).
- `CategoricalCrypto/UC/QueryBound/Compose/Laws.agda :: qb-∘` — −12 LOC — only consumer `qb-∘-category`, which can go raw≈∘ᴳ, ⟺, raw≈∘ᴳ; kept in round 3: one consumer.
- `CategoricalCrypto/UC/Machine/StateEvent/Lift.agda :: FlagCert, flagSkeleton, flag-slide` vs `UC/Machine/Dominated.agda`'s certificate — ≈ −250..−400 LOC — two "+1 certificate" developments; `Monitor.monitor-flag` (`monitorᴹ report ∘ u ≈ accᴹ ▷ reported`) is the simulation that would let `Dominated`'s certificate read off the flag one, but the merge itself is unspiked.
- `CategoricalCrypto/UC/Machine/StateEvent/Agree.agda :: embeds` vs `Seam/Budget.agda :: stratTest-embeds` — ≈ −6 LOC — two wire proofs of one embedding; skipped in round 3: needs `λᴵ⇒ ∘ λᴵ⇐ ≈ id` in 𝒫ᴵ. Re-tried round 4: crux stands.
- `CategoricalCrypto/UC/Machine/Dictionary.agda :: T₁-resp-≈, sub-resp-≈, T₁-∘, sub-∘` — ≈ −18 LOC — one "family ≈ F₁ inherits the functor laws" lemma (perf-pinned). Declined round 4: the shared lemma has to abstract the object maps (`Y ⊗ᴵ_`, `_⊗ᴵ A`) across both spellings (`𝒫ᴵ`/`𝒢ₚᴹ`), while the four instances pin every implicit for `𝒫ᴵ`'s inversion reason — not a clean swap.
- `CategoricalCrypto/Iface.agda :: unitᴵ` vs `UC/Machine/Dictionary.agda :: 𝟭ᴵ` — −80..−120 LOC, multi-session — two empty interfaces force two unitor-wire families plus `Slide`'s hole-wire apparatus; spike `unitᴵ = 𝟭ᴵ`.
- `CategoricalCrypto/UC/Seam/Grounded.agda :: plug-run` vs `UC/Machine/Plug.agda :: Plugged.collapse` — small — two spellings of "observe env ∘ u". Declined round 4: two different statements (a seal crossing vs a trace collapse) sharing only the left side.
- `CategoricalCrypto/UC/Model/Seal.agda :: M._∘_ g f` — small — zero consumers (rule 32). Declined round 4: both statements naming it (`unprocᵒ-∘`, `procᵒ-∘`) have consumers (`plug-run`, `factorᵖ`).
- `CategoricalCrypto/UCSetup.agda :: faithful⇒grade-stable, GradeStableFromTests`, `UCSetup/Morphism :: idᵁ, composeᵁ, identity laws, module Factorization`, `Abstract2/Morphism :: transfer-impossible, epi⇒preserves-≈ℰ, mono⇒reflects-≈ℰ`, `Abstract2/WideSubcategory :: W-ext, coarsen, epi⇒coarsens, restrict-dummy, Fine, Trivial`, `Abstract2 :: UC-dummy-sim, UCᵈ-sim, ≤UC-resp-≈, ≤UCᵈ⇔≤UC, ≤UC-sub` — ≈ −150 LOC — dead internals of the setup-morphism layer; the "Identity and composition" banner promises a category never built.
- `CategoricalCrypto/Abstract.agda :: Iᵤ, car, grd, U-≋, atk-idˡ`, `Abstract2 :: UC-compose re-binding f g` — ≈ −20 LOC — dead names in the kept island.
- State-event transport for open systems — ~150–250 LOC proof work — `stateLift` handles closed systems only; a bound carried through a simulator needs a `collapseᵀ`-compatible projection or a permitted-class route.

## Quantitative

- `CategoricalCrypto/UC/Quantitative/EventLift.agda :: agree` — small — public, single use (`hits⇒upper`); kept in round 3: it is cited.

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
