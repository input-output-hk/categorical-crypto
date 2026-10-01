# Quality review — protocol-rewrite, part R2a (2026-10-01)

Scope: the 40 files of `scope-R2a-final.txt` (files changed since round 1, minus files other agents hold), base a0e8108b,
rebased onto 4c5bcb67. Complexity-first, per the maintainer's "too complicated" concern.
Verification: every commit checked with pagda (rc=0, warn-grep empty) on its touched modules plus direct in-repo
importers (comment/import-only commits: touched modules only). After the rebase onto 4c5bcb67: root green (rc=0,
148 modules, warn-grep empty) and the five non-root leaves the scope reaches (ChimericLedger/{Serialize,Transfer},
MerkleDamgard/{Pin,QueryBound}, StateEvent/Spike/MonitorFlag) green; NUL check over all 128 new blobs clean;
`git diff --check` clean. Rebase conflicts (3): `UC/Machine.agda` Proc comment and `UC/Model/Seal.agda` procᵒ-∘ comment
— upstream's new text kept, my cut dropped; `Machines/Sim.agda` header — my cut kept (upstream's 𝒫 paragraph is
already folded into the header's first paragraph).
Soundness baseline 16, unchanged. Sweep tally (toolkit JSONs in `QUALITY-REVIEW-R2a.d/`, kept/candidates/skipped):
using-drop 18/49/28, implicit-drop 75/347/0, join-lines 16/44/0, enum-with 0 sites, enum-where 82 sites,
enum-comments 274 blocks (all dispositioned, `dispositions.tsv`); binder-drop not run (Suggestion 22).
Net src delta vs 4c5bcb67: 39 files, +390/−834.

## Committed (you can skim these)
Sweep survivors, comment hygiene (one commit per cluster), dead imports/aliases, single-use where-inlines, and the
spiked proof swaps: Compose's π-sim/ι-sim through `Pointwise.simFn` (−31), Observe's `Dmap->>=`, Kleisli.Distributive's
`split₂ʳ`, Cov's stdlib ℕ lemmas, Pointwise's `ᶠ` laws through `Machines.Pure`, the CoinToss hybrids through `Walk.R-down`.
- 97a880dc Sweep using-drop: bare opens where no clash (5 files) (+18/-18)
- bf7f9454 Sweep implicit-drop: inferable implicits at use sites (10 files) (+40/-40)
- 8b50c9c6 Sweep join-lines: one-line constructs that fit the file width (6 files) (+16/-32)
- aab2927d Comments: cut narration and stale prose in the generic foundations (+9/-27)
- a03c40ad Setoids.Discrete: drop the unused Level import (+0/-2)
- bf026bff Class.Monad.Ext.Setoid: drop the Level import the Prelude already re-exports (+0/-1)
- eb274c53 Dp.Mass: one blank line between import groups (+0/-1)
- 18b70189 Kleisli.Discrete: open Category.HomReasoning Klᴹ directly (+1/-3)
- ae33321b Setoids.Discrete: name the one implicit >>=-cong binds (+1/-1)
- cb906b5d Kleisli.Distributive: pure-⊗ via Monoidal.Reasoning.split₂ʳ (+3/-5)
- 51aee764 Kleisli.Discrete: pureᵏ-cong takes h ≗ k (+1/-1)
- a1af9c61 Dp.Mass: one open of +-*-Solver for the private solver helpers (+2/-4)
- c59e7286 Dp.Mass: inline the single-use where helpers one, ind-sum, bound (+11/-19)
- 07bb93c0 Setoids.Maybe: inline the single-use identityˡ and >>=-comm helpers (+8/-13)
- 6e98b622 Comments: examples and tests cluster (+20/-58)
- 430973d0 MerkleDamgard.QueryBound: drop the unused ttᵛ import (+0/-1)
- 68d10888 MerkleDamgard.QueryBound: θ-step's unused binder is _ (+1/-1)
- ac3c1f98 MerkleDamgard.QueryBound: certifiedᴹᴰ's single-use helpers inline into its fields (+12/-20)
- 3d485457 SFunM.Test.Possibility: Buffer's send/schedule inline, as Cut and CRS do (+3/-8)
- 613602bf SFunM.Test.Possibility: drop the unused Graded.Morphism import (+0/-1)
- 69072871 CoinToss.Ideal.Hybrid: inline the single-use lkᴴ (+1/-6)
- 2cff0d8f CoinToss hybrids: uncurry hybStep (rule 17) (+2/-2)
- 6833724e CoinToss.Ideal.Hybrid: hearᴴ is Walk.R-down plus the pad (+1/-4)
- 323ef943 CoinToss.Ideal.Receiver.Hybrid: hearᴴʰ is Walk.R-down plus the pad (+1/-4)
- d2cfdb75 Comments: protocol and UC machine layer (+35/-84)
- 52fc6661 Protocol.Observe: drop the dead Rational.Properties imports and fossil renamings (+1/-3)
- e1fac8d8 UC.Machine.Monitor: drop the unused ttᵛ and PropositionalEquality imports (+0/-2)
- d55889ba UC.Machine: one Data.Sum import, at the top (rule 10) (+1/-3)
- 68e9ac31 UC.Machine: retᴵ next to the ⟦_⟧ᴵ/Proc vocabulary it inverts (rule 28) (+5/-4)
- 6f02ac0e Protocol.Machine: module telescopes use the private variable block (rule 16) (+2/-2)
- 04bf0eb4 Protocol.Machine: inline the single-use 𝒢 alias (+1/-2)
- 188acf04 UC.Machine.Monitor: inline the single-use state bindings (+2/-8)
- a0781d45 Protocol.Observe: uniformVec-bind's inner step is Dmap->>= (+1/-7)
- ec48497c Protocol.Machine.Compose: π-sim and ι-sim through Pointwise.simFn (+23/-54)
- 703e8f3e Protocol.Machine.Compose: morphismCompose in 𝒞 [ f ∘ g ] notation; drop the 𝒢 alias (+1/-2)
- 29779e09 Protocol.Machine: drop the unused Data.Nat and Protocol.Observe imports (+0/-2)
- 53f8bf4b Comments: machine core (+28/-102)
- 469f1518 Tensor.Structural: hexagon₁ from ⊕Sym; drop the ⊕Br alias and the Braided import (+1/-3)
- 75c07a38 Machines: drop unused generalized variables (Frame S; Structural W Z) (+2/-2)
- 5d0be90c Machines.Pointwise: drop the unused D and CK aliases and their imports (+0/-4)
- 8a5344cb Machines.Pointwise: one Data.Sum.Base open (+1/-2)
- 7cf35e99 Tensor.Structural: drop the unused λ⇐ᴹ/ρ⇐ᴹ (+0/-6)
- 80a82d70 Machines.Frame: inline the single-use σ-pad-inv into swp-swp (+2/-4)
- 1336e2cb Machines.Pointwise: inline simFn's single-use law (+3/-5)
- 6b220a7a Machines.Tensor: drop the unused {i} binder in ⊗ᵉ-resp-≈ᴹ (+1/-1)
- f69a8439 Tensor.Assoc: ⟩∘ᴹ⟨ for the one ∘ᴹ-resp-≈ᴹ use (rule 20) (+1/-1)
- 6323feec Machines.Tensor: tstep-∘ beside tstep-id (rule 28) (+8/-11)
- fe29fbbf Tensor.Assoc: the one-sided collapses move to their only user (+11/-11)
- 04b2a731 Machines.Tensor: λ⇒ᴹ/ρ⇒ᴹ beside the other structural machines (+7/-7)
- 19f58ecd Machines.Pointwise: idᶠ/∘ᶠ/⊗ᶠ through Machines.Pure's pureᴹ laws (+4/-8)
- 973b4a99 Comments: quantitative UC layer (+56/-122)
- aaa5d3e5 EventLift: drop the unused Data.Empty, Data.Sum.Base and Function.Base imports (+0/-3)
- 1d3f09ca EventLift: ≈ₚ-sym _ _ is Dp.Reasoning's ≈sym (+1/-1)
- f5a7bec8 EventLift: hitsᵘ's misindented signature (+1/-2)
- 031dfe38 EventLift.Cov: drop the unused cong from the PropositionalEquality list (+1/-1)
- 3f0238de EventLift.Cov: the ℕ inequalities are stdlib's +-mono-≤-<, m<m+n, m+n≤o⇒n≤o (+5/-13)
- 57787d84 EventLift.Cov: {rE r : ℕ} once in a private variable block (rule 16) (+6/-5)
- 4fa83138 EventLift.Cov: covCtx cases on qb-closedᴹ instead of four projections (rule 12) (+4/-12)
- ade42007 EventLift.Cov: inline the single-use zeroᵂ (+2/-4)
- f085ba95 Seam.Budget: drop the unused ttᵛ import; (λ o → o) is id (+1/-2)
- 035f1502 Seam.Budget: inline the single-use cohL/cohR and square (+7/-15)
- a97fbea4 UC.Graded: M._∘_ g f is g M.∘ f (rule 20) (+5/-5)
- ac65f0ea UC.QueryBound: qb-idᴹ beside qbᵢ-id (rule 28) (+3/-6)
- ea0edafd UC.QueryBound: inline the single-use certificate cohL/cohR fields and id-step (+15/-40)


## Suggestions (need your call), ranked by LOC saved / complexity removed

### Status after impl-R2a (2026-10-01, branch `impl-R2a` off d4b7eb00)
Every commit green on its modules + importers; root (`-M8G -H2G`) and the five non-root leaves the edits reach
(ChimericLedger/{Serialize,Transfer}, MerkleDamgard/{Pin,QueryBound}, StateEvent/Spike/MonitorFlag) green; escape
hatches 16 → 16.
| # | status | commit | LOC |
|---|---|---|---|
| 1 | DONE — `Class/Monad/Ext/{Setoid,Discrete}` deleted, `Dist⊥ᴰ`/`Listᴰ` are `DiscreteMonad` records; `SFunM.agda`'s header (integration-owned) still names `toDiscreteMonad` | ddf1f0b4 | +26/−188 |
| 2 | ruled: keep (maintainer, 2026-09-30) | — | — |
| 3 | DONE — option (a): one private `Ancilla` block (input splits + output injections) | fa446ee4 | +81/−123 |
| 4 | DONE — `Categories/Category/Monoidal/Symmetric/Properties/Ext.agda` holds `β` (Core's `swp`, `Traced.Ext.β` re-exported, Fubini's `β+` at `+-symmetric`) and the generic lemmas; monoidal-only ones to `Monoidal/Properties/Ext`; GConstructionTrace's `σ-unit` gone. Net LOC positive (new-module boilerplate + 9 import lines) | 748f332d | +151/−114 |
| 5 | SKIPPED (blocked) — a public `MC` in `Machines.Base` is a `ShadowedModule` error in every opener that defines its own (verified); four of those are stage-2-owned (`Monitor`, `Dominated`, `EventLift/Cov`, `Seam/EventTransfer`). Land after stage 2. Only the `Col` → `Pw` fossil landed | aff8d94b | +8/−8 |
| 6 | DONE | 7d377641 | +21/−57 |
| 7 | DONE — the `pureᶠ` family moves into `Pure`; `idᶠ` replaces `id-pureᴹ`; `midᴹ-pure : midᴹ ≈ᴹ pureᶠ midfn` | 1ed096c7 | +38/−37 |
| 8 | DONE — `Pointwise.fnStep` | befb9c57 | +14/−33 |
| 9 | DONE except `Monitor/Agree` (stage-2-owned) | 0f6035f5 | +29/−34 |
| 10, 13, 15, 17 | stage 2's files — left | — | — |
| 11 | DONE (cheap part; the unused half stays by ruling) | ba90d016 | +15/−27 |
| 12 | DONE — `qbᵢ-zero`; `qbᵢ-wire` via `qbᵢ-upward`, importer warm times unchanged (Grading 15/15 s, Slide 17/18, Bridge 8/8, Model.Dominated 15/15, Graded 46/45) | 60978f13 | +26/−31 |
| 14 | SKIPPED (blocked) — `StateEvent/HitTests.agda` (stage-2-owned) uses `initˢ` without importing `Machines.Base`; one import line there once stage 2 lands | — | — |
| 16 | DONE — `onR` at the general type, `onRᵍ*` renamed; `onR-cong` generalised | eab89584 | +18/−21 |
| 18 | `Emulation :: Cᴺ` private DONE (68755476, ±1); the rest still open (forwarding/rename/privatize-or-publish/placement are calls) | 68755476 | +1/−1 |
| 19 | MonitorTests retargeted at `monitorᴹ` DONE (1e8f9bc7, +11/−3); `qbᴹᴰ` pin still open | 1e8f9bc7 | +11/−3 |
| 20 | still open (each needs a measurement or touches stage-2/eta-sensitive code: `≈ᵏ-isEquivalence` is `Klᴹ`'s `equiv`) | — | — |
| 21 | no (ruling) | — | — |
| 22 | relay inlines DONE — root importers' warm profile ≤ +13 % per module (+5 % total, within noise); binder-drop still not run | c91a9b6e | +4/−12 |

### 1. `src/Class/Monad/Ext/Setoid.agda :: MonadSetoid / MonadLawsSetoid / CommutativeMonadSetoid` — a second spelling of `Elementwise` + `DiscreteMonad` (≈ −120..−140)
The Class-instance setoid layer exists only so `toDiscreteMonad` can build two values: `SFunPartial`'s `Dist⊥ᴰ`
and `SFunPossibility`'s `Listᴰ`. The `Dist-ℚ` instances in `ProbabilisticLogic/Distribution/RationalDist/Setoid.agda:38-56`
have no consumer; inside `Class/Monad/Ext/Setoid.agda` the `<$>ᴹ` section (57-84), `>>=-cong-f`, `>>=-cong-x` (37-43)
and `module ≈ᴹ` (28) have zero uses (≈ −38 on their own). Replacement: write `Dist⊥ᴰ`/`Listᴰ` as direct
`record { elementwise = record { … } ; >>=-comm = … }` values in `Partial`/`Possibility`, then delete
`Class/Monad/Ext/{Setoid,Discrete}.agda` and the three instance blocks. Nothing uses the level polymorphism
(every read is at 0ℓ). Out-of-scope edits: `SFunPartial.agda`, `SFunPossibility.agda` (both concurrently edited),
`RationalDist/{Partial,Setoid}.agda`. Not spiked (out-of-scope files are under concurrent edit).

### 2. `src/Categories/Monad/Construction/Kleisli/Ext.agda :: KleisliTriple⇒ᴹ` family (≈ −110) — re-open of D-foundations:179 — ruled: keep
The ledger's dead family has grown: `extend-μ` is now used only by that family, so ~110 of the file's 125 lines are
reachable from no consumer outside the file (only `KleisliTriple⇒` is used, by `Setoids/Discrete/Morphism`,
`Graded/Trivial`, `SFunM/Test/Possibility`). The maintainer's own "Restore the Monad⇒-id presentation" (e2e42744)
argues KEEP; if kept, the file header (3-8) is the one comment worth keeping.

### 3. `src/CategoricalCrypto/UC/QueryBound.agda :: qbᵢ-T₁ / qbᵢ-sub` — twin 70-line blocks (≈ −55..−65)
`relayT`/`relayS`, `stepT`/`stepS`, `liftT`/`liftS`, `relayed`/`relayedS`, `certT`/`certS` differ only in which
summand the ancilla sits in. (a) one private module parameterised by the side (the two `⊎` injections and the two
case splits), instantiated twice; or (b) `qb-subᴵ` derived as `σ ∘ T₁ᴵ ∘ σ` through `qb-∘-category` (rate
`1·(c⊔1)·1`, one `subst`), which needs an `subᴵ ≈ σ ∘ T₁ᴵ ∘ σ` lemma in `UC/Machine/Grading.agda`. Risk: both
certificates must still match `MC.step` on the nose; QueryBound is a 600-line perf-sensitive module. Not spiked.

### 4. `src/CategoricalCrypto/Machines/Frame.agda` generic half → `Categories/Category/Monoidal/Symmetric/Properties/Ext.agda` (≈ −10..−15; three definitions become one)
`Core.swp` is character-identical to `Categories/Category/Monoidal/Traced/Ext.agda :: β`; `Machines/Trace/Fubini.agda :: β+`
is the same shape on `+`; `Frame :: σ-unit` duplicates the private `σ-unit` at `Categories/GConstructionTrace.agda:110`.
`swp-swp`, `swp-nat*`, `pad-*`, `unbraid`, `σ-split*`, `σ⊗-inv`, `ρα-λ`, `ρ-swp` are generic symmetric-monoidal facts
living in `CategoricalCrypto/` (maintainer taste: generic in `Categories/`, instances in `CategoricalCrypto/`).
Target: one generic module holding `β` and these lemmas; `swp = β`; `Traced.Ext`, `GConstructionTrace`, `Fubini`
(`β+ = β` at `⊕Sym`) reuse it. Out-of-scope: `Machines/Reassoc.agda` (concurrently edited; uses `σ-split*`),
`Traced/Ext`, `GConstructionTrace`, `Fubini`. Round 1 declined only upstream's *private* `swapʳ`
(QUALITY-REVIEW.md:1642); this is the in-repo variant.

### 5. `src/CategoricalCrypto/Machines/Base.agda` — one public set of `𝒱ₚ 0ℓ` instantiations (≈ −40..−60)
`Machines/Pointwise.agda` publicly exports `MC/S/Cat/T/V/K/KP`, which importers use as `Pw.MC`, `Pw.S`, `Pw.T`, while ~20
other files each write their own `private module MC = Core (𝒱ₚ 0ℓ)` and ~10 a `Sim` copy: one instantiation reached
two ways. Put the instantiations once in `Machines.Base` (which already owns `𝒱ₚ`/`𝒫ₚ`/`distₚ`). `UC/QueryBound.agda:56`'s
`Pointwise as Col` is a fossil of the `Collapse` name. Needs a measurement (QUALITY-REVIEW.md:879 perf caveat);
touches many concurrently-edited files.

### 6. `src/CategoricalCrypto/UC/QueryBound.agda:69-93` — private copy of `ProbabilisticLogic.Dp.Reasoning` (≈ −22) — pending QUALITY-REVIEW.md:695
Code changed since that entry (`Counting`'s copies and `eraseCons` are gone; the header no longer claims a budget),
so the timing objection it carried is weaker now. Concrete diff: bare-open `Dp.Reasoning`; delete
`_⟨≈⟩_`/`bindᶠ`/`return-≡`/`map-map`/`map-cong`/`map-arg` and the `A′ B′ C′` variables; `map-cong X` → `map-eq X _ _`
(470, 474, 542, 546); the three `cohR` fields become `map-fuse …` one-liners; `≈ₚ-sym _ _ (` → `≈sym (` (446, 448).
With it, the `agree`/`forget-up`/`forget-tag` where-bindings inline (their names only fix `map-cong`'s implicits).
Left as a suggestion because the ledger entry is pending.

### 7. `src/CategoricalCrypto/Machines/Pointwise.agda :: idᶠ/∘ᶠ/⊗ᶠ` vs `Machines/Pure.agda :: id-pureᴹ/∘-pureᴹ/⊗-pureᴹ` (≈ −15..−25)
Two versions of one lemma family: `idᶠ`'s proof is literally `id-pureᴹ`'s. `midᴹ-pure`'s target
`pureᴹ (pureᵏ midfn)` is `pureᶠ midfn`. `Pure` cannot import `Pointwise` (cycle), so either fold the `ᶠ` family
into `Pure` or move `midᴹ-pure` into `Pointwise`. Touches `Pure` and `UC/Machine/Dictionary` (4 uses). `midᴹ` is opaque —
medium risk.

### 8. `src/CategoricalCrypto/UC/Machine/Run.agda :: step-sim` / `UC/Machine/Run/Lax.agda :: step-lax, pad-fn` (≈ −14) — remainder of QUALITY-REVIEW.md:651
After the shared `runFrom-ϕ` landed, the two `pad-fn`s and the two step laws are still character-identical up to
`S.θ…` vs `L.θˡ…`. Add the converse of `simFn` to `Pointwise`:
`fnStep : (θ) (θp : KP.Pure θ) → θ ⊗₁ id ∘ k ≈ k′ ∘ θ ⊗₁ id → ∀ p → (k p >>=ₚ padϕ (KP.fn θp)) ≈ₚ k′ (KP.fn θp (proj₁ p) , proj₂ p)`
with body `bindᶠ (≈sym ∘ pad) ⟨≈⟩ step ⟨≈⟩ bindˣ (pad p) ⟨≈⟩ identityˡ`; then `step-sim`/`step-lax` are one
application each. Touches `UC/Machine/Run.agda` (not in scope).

### 9. `padϕ` is spelled nine times (≈ −8)
`Run.agda:43`; `Compose.agda :: πpad, ιpad`; `Pointwise.agda` (`⊗-pureˡ`'s right-hand side, inside `simFn`);
`Monitor/Agree.agda:431, 458`; `MerkleDamgard/QueryBound.agda:153, 159`. Move `padϕ` into `Machines/Pointwise.agda`
(rule 27), state `⊗-pureˡ`/`simFn` with it, delete `πpad`/`ιpad`. Touches `UC/Machine/StateEvent.agda` (concurrently
edited, uses `padϕ` via `Run`) and `Monitor/Agree.agda`.

### 10. `src/CategoricalCrypto/UC/Quantitative/EventLift.agda:66-77 :: Hitsᶠ, hitsᶠ⇒hitsᴺ` — alias of `EventBounds.Boundedᶠ`/`boundedᶠ⇒boundedᴺ` at `compileᴹ` (≈ −9), and `eventDominatedᵘ` (≈ −8)
`Hitsᶠ` also takes `ε f μ` where `Hitsᴺ` takes `f μ ε` — two argument orders for one notion. `Property.agda:171`
would call `boundedᶠ⇒boundedᴺ _ _ εᴹ …` directly. Separately, `eventDominatedᵘ` has one consumer (`hitsᵘ`) and folds
into it. Low risk; touches `Examples/ChimericLedger/Property.agda`.

### 11. `src/CategoricalCrypto/Machines/Sim/Lax.agda :: _≈ˡ[_]_` is `Relation.Binary.Construct.Composition` (≈ −6; ≈ −65 if the unused half went)
`_≈ˡ[_]_ f σ g = (_≈ᴹ_ ; (_≲ˡ[ σ ]_ ; _≈ᴹ_)) f g` with stdlib's `_;_`; the congruences become Σ-patterns. FYI only (the
module is KEEP by ruling): `_≈ˡ[_]_`, `≲⇒≲ˡ`, `≲ˡ-refl`, `≲ˡ-trans` and the three `≲ˡ` congruences have zero
consumers; `Run/Lax` uses only the `_≲ˡ[_]_` record. Strict/lax shared core is QUALITY-REVIEW.md:323.

### 12. `src/CategoricalCrypto/UC/QueryBound.agda:188-253 :: qbᵢ-wire, qbᵢ-closed, qbᵢ-upward` — one zero-potential skeleton (≈ −8..−15)
`qbᵢ-wire up down = qbᵢ-upward ⊤ᵛ (returnₚ tt) (wireStep up down) (λ s a → returnₚ (inj₂ ((s , z≤n) , up a))) (λ _ _ → >>=ₚ-identityˡ _ _)`;
`qbᵢ-closed`/`qbᵢ-upward` share `pointᵍ`/`coh₀`/`cohR` verbatim. Risk: `qbᵢ-wire`'s `onRᵍ` stops being a literal
`returnₚ` inside perf-pinned `qb-∘` towers — measure first.

### 13. `src/ProbabilisticLogic/Dp/Mass.agda :: mass-bindʳ` = `UC/Machine/StateEvent/Lift.agda :: bind-≤` at test `1ℚ` (≈ −6)
Generalise to `cum-bindʳ : (n) (d) (k) (P : B → ℚ) → NNF P → (c) → 0ℚ ≤ c → (∀ p → cum n (k p) P ≤ c) → cum n (d >>=ₚ k) P ≤ c`;
`mass-bindʳ n d k = cum-bindʳ n d k _ (λ _ → 0≤1ℚ)`; `Lift`'s `bind-≤` becomes `cum-bindʳ j d k Qᵗ nnQ` (its own
comment admits the copy). Touches `StateEvent/Lift.agda` (concurrently edited).

### 14. `src/CategoricalCrypto/UC/Machine.agda :: initˢ` belongs in `Machines/Base.agda` (≈ −2, clarifies layering)
`Protocol/Machine.agda :: stateᴹ` and `Compose.agda :: stateᶜ` hand-write `record { obj = … ; point = λ _ → returnₚ … }`
because `initˢ` lives above them. 17 of its 18 users already import `Base` (the exception, `UC/Machine/StateEvent.agda`,
is concurrently edited). Then `stateᴹ = initˢ MSt (idle (init P))`, `stateᶜ = initˢ CSt (both (init P₂) (init P₁))`.

### 15. `src/CategoricalCrypto/UC/Machine/Monitor.agda :: Flagᴵ` — `Flagᴵ = Ωᴵ` (0 LOC, one notion?)
`Flagᴵ = Bool ⇿ ⊤` is `Ωᴵ` by definition and its comment says it has "`Ωᴵ`'s shape for `Ωᴵ`'s reason". Whether a flag
port and the verdict port should be ONE name is a modelling call, hence a suggestion; the swap is definitional.

### 16. `src/CategoricalCrypto/Machines/Core.agda :: onR` — finish C-machines:270 (≈ −3, one notion)
`onR = onRᵍ` landed; the rest is renaming `onRᵍ` to `onR` at the general type and restating `Frame`'s `onR-*` at it
where free. Touches 17+ files incl. concurrently-edited `StateEvent/Lift`, `Reassoc`, `Protocol/Machine/Trace*`.

### 17. `src/CategoricalCrypto/UC/Quantitative/EventLift.agda:84 :: openedᴹ` / `:145 :: qb-stratTest` — placement (≈ −4)
`compileᴹ B μ Y E 𝒫.∘ T₁ᴵ Y λᴵ⇒` is re-spelled at `Monitor/Slide.agda:70,73`, `EventLift/Cov.agda:290,301`,
`Monitor/Agree.agda:480`; `openedᴹ` generalised over `μ` and moved into `Monitor.agda` (or `Cov`, which EventLift
imports) gives one spelling. `qb-stratTest` is a strategy-cost lemma and belongs beside `qb-strategyEnv` in
`UC/Seam/Budget.agda` (rule 27); its importers (`StateEvent/Adequacy`, `Spike/Transport`) are excluded files.

### 18. Public interface narrowing / forwarding (rule 19, rule 32 — your call)
- `src/Categories/Monad/Setoids/Discrete.agda:34 :: open Elementwise elementwise public hiding (module Comm)` — a
  forwarding layer whose only consumer is `Setoids/Discrete/Morphism.agda` (`module ℳ = Discrete M` →
  `module ℳ = Elementwise (Discrete.elementwise M)`). ≈ −2.
- `src/ProbabilisticLogic/Distribution/Possibility/Setoids.agda:39 :: module 𝒫` — re-export alias of the
  `DiscreteMonad` setoid; its only use is `SFunM/Test/Possibility.agda:155` (`𝒫.trans` → `≈ᴹ.trans`). Also
  `>>=𝒫-cong`/`>>=𝒫-comm` share names with different lemmas in `Possibility.agda:82,122` (rename to `>>=𝒫ˢ-*`).
- `src/CategoricalCrypto/UC/Model/Family/Emulation.agda:46 :: module Cᴺ = Canonicalᴺ` — no importer writes `Cᴺ.`;
  `private` per rule 32's plumbing exception.
- `src/CategoricalCrypto/Protocol/Machine/Compose.agda :: CSt, stateᶜ, serveᶜ, graftᶜ, stepᶜ, machineᶜ, π-sim, ι-sim` and
  `src/CategoricalCrypto/Examples/CoinToss/Ideal/{Hybrid,Machine,Receiver/Hybrid}.agda :: hyb-sim, idl-sim, hyb-simʰ`
  are public proof scaffolding; the latter three are public statements over PRIVATE machines (`Hᴺ`/`Iᴺ`), so no
  downstream user can even restate them. Privatize the sims or publish `Hᴺ`/`Iᴺ`.
- `src/ProbabilisticLogic/Dp/Mass.agda :: total-resp-≼ₚ` — zero consumers and outside the ruled `ASTotal` closure (−7).
- `src/Categories/Monad/Setoids/Maybe.agda :: Setoids-Symmetric` — a general fact buried in `Maybe` (rule 27/29);
  inline at its one use or move to `Categories.Category.Monoidal.Instance.Setoids.Ext`.
  `Categories/Category/Distributive/Monoidal.agda :: Cartesian-SymmetricMonoidal` is the same Cartesian → symmetric
  monoidal bundle; one home serves both.

### 19. Test targeting (rule 33)
- `src/CategoricalCrypto/UC/Machine/MonitorTests.agda` pins `monitorStep`, the step helper, not the public entry
  `monitorᴹ`. Restated as `MC.step (monitorᴹ report) (…) ≡ …` each pin is still `refl`; needs `Machines.Base`/`Core`
  imports. (Suite restored by ruling — this is about its target, not its existence.)
- `src/CategoricalCrypto/Examples/MerkleDamgard/QueryBound.agda :: qbᴹᴰ, certifiedᴹᴰ` — no consumer, no pin
  (QUALITY-REVIEW.md:1636, unchanged).

### 20. Smaller library alignments (not spiked)
- `src/Categories/Category/Construction/Kleisli/Discrete.agda:43 :: ≈ᵏ-isEquivalence` is stdlib's pointwise setoid
  (`Function.Indexed.Relation.Binary.Equality.≡-setoid A (Trivial.indexedSetoid (≈ᴹ-setoid B))`), ≈ −3.
- `src/Categories/Category/Monoidal/Distributive/Instance/Rels.agda:23 :: δ⁻¹` is the graph of stdlib's
  `×-distribˡ-⊎` inverse (= `Kleisli/Discrete/Distributive :: undistribute`); `Lift ℓ (undistribute p ≡ q)` would
  collapse the iso clauses' `(lift refl , lift refl)` pairs, ≈ −4..−8.
- `src/CategoricalCrypto/UC/Machine.agda :: outT` / `subᴵ.outS` are `Data.Sum.map inj₂ inj₂` / `map inj₁ inj₁`;
  risk is that a stuck `outT x` in `UC.QueryBound` goals becomes `[_,_]′` — measure.
- `src/ProbabilisticLogic/Dp/Mass.agda :: split, scale, expand, collect, product` are unit-interval ℚ facts for
  `Data.Rational.Properties.Ext` (extends QUALITY-REVIEW.md:1008).
- `src/CategoricalCrypto/Machines/Tensor/Assoc.agda:49-53` and `Tensor/Structural.agda:56-59` repeat the same
  `module ℳ = Category Mealy-Category` + renaming block; export it once from `Machines/Category.agda` (excluded file).
- `src/CategoricalCrypto/UC/Seam/Adequacy.agda:53`, `UC/Seam/Plug.agda:99 :: point-red` re-prove `Pointwise.point-⊛`.

### 21. Two spellings of the closed-machine type — recorded, NOT recommended
`Protocol.Machine.Closed B` and `UC.Machine.Proc unitᴵ B` are definitionally equal; unifying would move `Proc` below
29 importers of `UC.Machine`. Recorded so it is not re-derived.

### 22. Unfinished work items (wrap-up called by the coordinator)
- `src/CategoricalCrypto/UC/Machine.agda :: T₁ᴵ.relay, subᴵ.relay` — inline as `mapₚ (map₂ outT) (MC.step f (s , inj₁ a))`
  etc. (≈ −8). Patch validated by dry-run, NOT typechecked: `QUALITY-REVIEW-R2a.d/patches-unlanded/B-where-UC_Machine.py`
  (written against a0e8108b; `UC/Machine.agda` was respelled upstream since, so it needs regenerating). It changes
  `T₁ᴵ`/`subᴵ`'s bodies, so all 71 importers need rechecking — measured cost of an importer pass on this branch at the
  shared memory gate: 30–60 min.
- Sweep class `binder-drop` was not run (statement-adjacent; 40 in-scope files; each kept site needs an importer pass —
  Protocol.Machine's 46 importers took ≈ 25 min per pass today). `using-drop`, `implicit-drop`, `join-lines`,
  `enum-with` (0 sites), `enum-where` (82 sites) and `enum-comments` (274 blocks) are complete; per-site dispositions in
  `QUALITY-REVIEW-R2a.d/dispositions.tsv`.

## Tried, not worth it
- `src/CategoricalCrypto/Protocol/Machine.agda :: open import Data.Sum.Base using (_⊎_; inj₁; inj₂)` — a bare open is RED:
  Data.Sum's `[_,_]` makes `𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]` an ambiguous parse. The `using` is a real clash guard; the other
  two dead imports landed alone (628e329c).
- `src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Hybrid.agda :: cellᴴʰ` (generalised over `Neg (Lkᴵʰ ⊗ᴵ Honᴵʰ)`) —
  superseded: once `hearᴴʰ` goes through `Walk.R-down` (8fe7b104) no duplicated tail is left for it to absorb.
  Alternative patch kept at `QUALITY-REVIEW-R2a.d/patches-unlanded/D-receiver-cell-generalise.py`.
- `src/CategoricalCrypto/UC/Machine/Monitor.agda :: qbᵢ-monitor`, `src/CategoricalCrypto/UC/Model/Seal.agda :: ifaceᵒ-onto`
  — zero-consumer, but restored by the maintainer in b8ef120f: KEEP, not re-proposed.

## Integration-owned files
- `src/Class/Monad/Ext.agda` — orphan (no importer); flagged only, per ruling. Suggestion 1 would also retire its
  `Ext/Setoid` and `Ext/Discrete` children.

## Out-of-scope edits
None: every commit touches only files in `scope-R2a-final.txt`.

## Ledger duplicates (not re-proposed; code unchanged unless noted)
QUALITY-REVIEW.md:180 (`QB` counts the representative), :323 (strict/lax `StepSim` core), :359 (`Frame :: 𝕄`), :651
(Run/Run.Lax — residue is Suggestion 8), :695 (QueryBound's `Dp.Reasoning` copy — Suggestion 6), :826 (`mapₚ-≼ᵐ`), :879
(Compose alias block — C1's simFn commit removed K/KP/V from it), :924 (Seal `M._∘_` — still pending; the UC.Graded sites
of the same class landed as 04446f51), :1008 (`1-≤`, `shift`), :1111 (Pin `cum` depths), :1636 (`qbᴹᴰ` unpinned), :1642
(`swp`→`swapʳ`); A-examples:143/150 (CoinToss `Walk`/`Hop` scaffolding — `hearᴴ`/`hearᴴʰ` now use `Walk`); B-uc:209 (`a⇒ᴵ`
naming); B-uc:264 (UC.Graded aliases, Tried); C-machines:258/270 (`pure-iso`, `onR`); D-foundations:179 (Suggestion 2).
