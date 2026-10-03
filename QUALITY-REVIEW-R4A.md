# Quality review R4A — examples (2026-10-03)

Scope: the 53 files of `scope-R4A.txt` (`src/CategoricalCrypto/Examples/{ChimericLedger,CoinToss,ROCommitment,MerkleDamgard,HashForward}/**`, their parent modules, `Examples/RandomOracle.agda`), plus the new `Examples/CoinToss/Ideal/Stage.agda`, and the docs citing them (`coin-toss.md`, `fcom-{uc,hiding,extraction}.md`, `rcom-icom-b1.md`, `hash-forward.md`, `quantitative-family.md`, `mathematical-guide.md`, `end-to-end.md`, `dp-transport.md`, `state-event-contract.md`). Base `aae4d19e` (`protocol-rewrite.next5`). Style sweep not run (another agent's job, per the brief).

Verification: every commit checked with `pagda --useUntracked false check … +RTS -M8G -H2G` + warn grep, importers rechecked; tip: root `CategoricalCrypto` and the four outside leaves (`ChimericLedger.{Transfer,Serialize}`, `MerkleDamgard.{Pin,QueryBound}`) green, warn grep empty; every in-scope module is in that closure (checked mechanically). Escape-hatch baseline 16 (all prose), unchanged. NUL check over every committed blob: clean. `git diff --check aae4d19e HEAD`: clean.

## Committed

- `d4f9aa03` ChimericLedger: `acctΣ`/`wdrlΣ`/`valΣ` were one function under three names → `valΣ`; `lookupU-insertNew` reuses `lookupU-cons-≢`; `applyTx-total-fresh` (only consumer: the wrapper `conservation`) merged into `conservation`.
- `13636a11` ROCommitment.Hiding.Defer: private `PtD` was `GamePlaying.Defer.AvgPoint` re-spelled.
- `a0f894f3` ROCommitment: delete `Realization.Bisim.toR` (no consumer; `runWith⊥-bisimʳ` takes `toQ`/`fromR`), `UC.idealQB`/`Hiding.UC.idealʰQB` (no consumer, `_≤UC^ωᵉ_` reads no bound of the compared families); inline `Resource.resourceQB` (one-line, one consumer).
- `aa1a031a` ROCommitment.Hiding.Asymptotic: delete `εʰ` (= `Hiding.Game.εᴸ` at `k = n`), `εʰ-negligible` (no consumer), `hiding-boundⁿ` (= `G.hiding-bound n`); `Hiding.Test` pins `hiding-bound` directly.
- `cd729f47` docs resync after the moves (`UC.Machine.Composite`, `UC.Family.Negligible.{ucSetupᴺ,Canonicalᴺ}`, `pred⇒image`, `tossedᶜ`, `ηʰ`, `0<inv-pow-2`'s module, `AvgPoint` in the `AvgBisim` snippet); "exactly one" → "at most one" downward message per activation (`getᶜ` sends none).
- `f6e1d2e5` 17 example modules re-applied `Machines.Core (𝒱ₚ 0ℓ)` next to `Machines.Base`'s public `MC` → `open MC`.
- `e23bef7f` HashForward: `simCert` is the bound `hf-bounded` consumes (header, `hash-forward.md`), `mathematical-guide.md` names `hf-bounded` as `bounded-absorb`'s instance, `sub-gradedᵒ` is one `∘-resp-≈ˡ` past `sub-⊗₁`, step equation in `Exact`'s orientation; single-use `settle` inlined; `Pin`'s `OneBlock`/`TwoBlocks` re-exported `MD` to nobody.
- `5f327578` MerkleDamgard.Core: `stepR`+`stepR-bisim` / `stepI`+`stepI-bisim` folded (the `*-bisim` only `subst`ed along a `≡`-on-projection relation; now `StepBisim` directly, matching `refl`, as `ROCommitment.Game`); `cm-nn` = `Collision.0≤countMatch`; `idx≡k` via `+-comm 1 idx`; `codet<k` one `cong`; `⊒-trans` inlined.
- `964ea382` MerkleDamgard.Core: `interior` = stdlib `filter interior?`; `interior-cons<`/`interior-consᶠ`/`∈interior` were `filter-accept`/`filter-reject`/`∈-filter⁺`; `collC-mono1` goes through `collC-cons<`.
- `31f60fa6` `count-matches`/`E-collisions`/`triangle`/`state-collisions` move from `Examples.RandomOracle` (no other consumer) into `MerkleDamgard.Core`, next to `triangle`'s laws.
- `003fd5c5` `ROCommitment.Resource.Stage` → `Examples.CoinToss.Ideal.Stage`: it takes the coin-toss stage and serves only the two CoinToss hybrids; `Resource` drops `Machines.Sandwich`, `UC.Machine.{Composite,Wire}`, `Pointwise`, `Categories.Category`, `UC.QueryBound` from its cone (every Resource importer).
- `36ee0843` open-items: the stage's new name.
- `5be150a0` Tests: `CoinToss.Test.toss-round`/`toss-roundʰ`, `HashForward.UC.real-round` — live rounds of the real protocols (only ideals/simulators were pinned; every real-side headline held even for a diverging `toss`/`real`). Warm compute ≈ 9 s / 8 s.
- `bac8c597` `defer-commit`'s pointer says which game; `e13dd961` EOF blank line.

## Suggestions (ranked by complexity removed / value)

### Statement audit
3. `src/CategoricalCrypto/Examples/CoinToss/{Compose,Ideal/Compose,Ideal/Receiver/Compose}.agda :: coin-toss-from-comᶜ, coin-toss-idealᶜ, coin-toss-idealʳᶜ` — proofs build `≤UC[ simᶜ… , εᶜ… ]` but state `≤UC^ωᵉ`, so the closed-form schedules are only recoverable through `proj₁ ∘ proj₂` (`Test`). State the `≤UC[_,_]` form; Test pins read `εᶜⁱ εᶜ 5 3`. ±0 LOC.

### Simplifications / layout (judgment or out-of-scope file)
11. `src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Machine.agda :: Pointᶜ` — re-spells `GamePlaying.Defer.Run.DeferStep`'s inner point hypothesis; name it there (`DeferPoint`) and set `Pointᶜ = DeferPoint …`. Touches `GamePlaying/Defer/Run.agda` (out of scope). ≈ −5 LOC.
12. `ROCommitment/UC :: realᵒ, idealᵒ`, `Hiding/UC :: realʰᵒ, idealʰᵒ`, `CoinToss/UC :: tossᵒ`, `CoinToss/Hiding/UC :: tossʰᵒ` vs `CoinToss/Compose :: realᶠ, idealᶠ, tossᶠ, …` — two alias layers for one graded hom (`X ᵒ = gradedᵒ X`, `Xᶠ = …ᵒ`), the ᵒ layer consumed only by the ᶠ layer and the QB types. Keep one (`Xᶠ n = gradedᵒ (RO.X n)`, `tossQB : Pred 1⁺ (gradedᵒ toss)`) — as a whole family (rule 26). ≈ −12 LOC.
13. `src/CategoricalCrypto/Examples/ChimericLedger/Property.agda :: ideal-truthful` — no code consumer, one-line instance of `Observable.auditWatch-complete`; `Transfer.ledger-conserves-value-from-hash` spells the discharge inline. Cited by `mathematical-guide.md` §8, `state-event-contract.md` row 23, `end-to-end.md` §6: keep, or delete with those lines. −3 LOC.
14. `src/CategoricalCrypto/Examples/ChimericLedger.agda :: checkWdrls-[]`, `System.agda :: ledger-keeps-accts-[]` — no code consumer; the checked evidence behind the documented initialization gap of `chimeric-not-preserving` (open item). Keep unless the maintainer prefers the prose alone. −17 LOC.
15. `src/CategoricalCrypto/Examples/ROCommitment/Realization/Assembly.agda :: coin-from-Rcom, coin-from-Rcomʰ` — one consumer each (`assembly`/`assemblyʰ`), each `toss-over tossᶠ RcomQB CTU.tossQB`; inline. They mirror the named `coin-toss-from-com`. −8 LOC.
16. `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: cm-01, collC-01, cm0-all, sc0-ap` — exist because `countMatch` is ℚ-valued; an ℕ-valued count under `fromℕ` makes them case splits. Touches `Uniform.Collision` and `Uniform.Duplicate`. ≈ −15 LOC. Unspiked.
17. `src/CategoricalCrypto/Examples/CoinToss/Ideal/Reach.agda :: coinᶜ`, `Receiver/Reach :: eagerᶜʰ, deferᶜʰ`, `Ideal/Stage :: hybrid-eq` — `sandwichᴹ c (Sum.map₂ assocʳ) (Sum.map₂ assocˡ)` written four times; one `rebracketᴹ` in `Ideal/Stage`. ≈ −2 LOC.

## Tried, not worth it
- `src/CategoricalCrypto/Examples/ChimericLedger/Transfer.agda :: preserves-value-transfer` comment vs `end-to-end.md` §6 (rule 24) — the comment carries the "flag is an internal port, so the strategy spends the honest allowance" why that the doc does not; a trim saves ~2 lines. Left.
- `src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/UC.agda :: flatʰ` — type-fixing alias of `flatᵍ`; inlining needs `flatᵍ {X = …} {P = …}` at 4 sites.
- `src/CategoricalCrypto/Examples/CoinToss/Ideal/Hybrid.agda :: open St public using (hybridᴹ)` — not a forwarding layer: the instantiated name is consumed (`Ideal.Machine.coin-machine`, `Receiver.Compose`, `Receiver.UC`).
- `src/CategoricalCrypto/Examples/MerkleDamgard/QueryBound.agda :: resume` — one use (`θᴰ`), but the comment names it on an elaboration-sensitive path; not spiked.
- `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: interior` as a pattern-lambda `filter` — the predicate cannot be inferred from a matching lambda; a pattern telescope on `interior?` does it (landed in `964ea382`). `collC-mono1`'s own `with ii <? k` no longer reduces `filter` (stdlib's `<?` goes through `<ᵇ`), hence the route via `collC-cons<`.

## Out-of-scope edits
- `docs/open-items.md` (one line: the stage's new name). Docs edited only where they cite this scope (`mathematical-guide.md` one line, `quantitative-family.md` three).

## Not reached
- Comment-narration pass (lens 6) beyond the files touched; the sweep toolkit (by brief).
- Spikes for suggestions 2, 8, 16.
