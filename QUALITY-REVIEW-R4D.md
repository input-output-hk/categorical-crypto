# Quality review — protocol-rewrite round 4, part R4D foundations (2026-10-03)

Scope: `scope-R4D.txt` (70 files: `ProbabilisticLogic/**`, the non-solver `Categories/**`, `Data/**`, `Class/DecEq/Ext`,
`Relation/Binary/Properties/Setoid/Ext`, `Algebra/Ordered/Bundles`, `CategoricalCrypto/{OracleCall,Machines/G}`) at base
`aae4d19e`. Lenses as in `brief-common-r4.md`; the style sweep was left to the sweep agent. Screened against
`docs/open-items.md` and the R3D ledger (`5838bfa8`); nothing below re-raises a ruled or declined item.

Verification: per commit, the touched modules (rc=0, warn-grep empty); then the root `src/CategoricalCrypto.agda`
(`-M8G -H2G`) and every non-root import-DAG leaf that reaches a changed module — see *Verification*. Escape-hatch
baseline over `src`: 16 before, 16 after, identical lines.

Spike patches (each `git apply --check`s against the tip): `QUALITY-REVIEW-R4D.d/`.

## Committed (you can skim these)

- `1db114fd` (+13/−13) indᵇ-not/indᵇ-cover beside indᵇ-nn in Uniform; E⊥-nn beside E-nn in Expectation
- `0c5b77be` (+2/−8) Uniform: the two definitional δ-cons lemmas are refl at their one use each
- `3e231c6a` (+2/−156) Linearity: delete the consumerless Regroup module and four unused lemmas
- `aa9d373a` (+1/−8) RationalDist: drop OnSupport-∧ (no use), a leftover TODO, and a false pointer
- `dec1b07e` (+8/−33) Data.Rational.Properties.Ext: delete unused lemmas; cancellations are AG's
- `4e307c6b` (+3/−26) Data.Nat: delete unused lemmas
- `11300efa` (+2/−40) Uniform.Decay: delete →0-*ˡ and vanishing-bound (no use in src)
- `1ff144e5` (+11/−36) Dp: uniformize is uniformizeˢ at Supp-all; Supp-mono is SuppL-map
- `95e17077` (+12/−28) Dp.Commutative: one pair-≼ at a pairing function instead of two mirrored proofs
- `196425dc` (+5/−15) Dp.Iter: iterₚ-≼ is the induction itself; Tᵗ-inlₒ is definitional
- `934ba049` (+14/−20) Dp.Settle.Iter: delete Settles-stepᵢ⋆ (no use); resync the fcom-uc Loop block
- `8f477605` (+1/−1) Protocol.Machine.Trace: Settles-iter is Dp.Settle.Iter.Settles-iter, not Loop's (comment)
- `2bb4772b` (+0/−70) LocallyGraded: delete forgetᴹ, unrestricted, GradedMonoidal-forget, U-faithful
- `6e8d8e90` (+39/−95) GConstruction: fold GConstructionLoop's trace-mid into GConstructionTrace; unwrap module C
- `30f304b9` (+31/−44) Coherence.Monoidal.Tactic: inline the macro body, objFuel; _==_ is stdlib's _≡ᵇ_
- `72d8c127` (+5/−5) Monoidal Ext headers: β swaps the last two factors; σ-unit states its objects
- `ef347cc9` (+1/−117) RationalDist: delete the consumerless Markov block and Dmap functor laws
- `fa33c431` (+0/−93) RationalDist.Partial: delete the consumerless Dist⊥ laws and instances
- `85706693` (+4/−10) LowerReal: the private halving lemmas are Rational.Properties.Ext's ½*+½* and 0<½*
- `b048703d` (+1/−8) Expectation: E-const is proved in place; Partial's lookupᴰℚ-const was its only body
- `802b0503` (+0/−2) Monad.Discrete header: drop the pointer to the deleted Monad.Setoids.Discrete
- `d09e0265` (+2/−4) Machines.G: point to GConstructionMonoidalCategory's one-application explanation
- `6d027b89` (+10/−7) Headers say what the statements are: Elgot uniformity, the trace laws, Ranked, birthday

Every deletion above was grep-checked over all of `src` and `docs` (comments excluded) for zero consumers and verified
by the closure check; the deleted law blocks (`ef347cc9`, `fa33c431`) are not on `main`, so the maintainer's
"no consumer ⇒ delete" test applies. The only statement-type change is `σ-unit` (`72d8c127`):
`σ-unit : σ⇒ ≈ id` → `σ-unit : σ⇒ {unit} {unit} ≈ id` — the same statement, its implicit objects (previously metas
solved only by the proof) now written out. `iterₚ-≼` (`196425dc`) keeps its type; `iterₚ-congᵖ` is gone.

## Suggestions (need your call), ranked by complexity removed

### 1. `src/ProbabilisticLogic/Dp/Mass.agda :: _≼ᵐ_, Total, ASTotal, astotal-*, const-bind-*, squeeze*, verdict-mass, mass-bind*` — almost-sure termination, no consumer (≈ −135 net)
Only `cum-bindʳ` (and through it `mass`, `mass-≤1`, `cum-≤1`, `leafₚ-≤1`) is used outside the module
(`UC/Machine/StateEvent/Lift.agda:183,370`). Everything else — the `≼ᵐ` domination, `Total`/`ASTotal`, `astotal-bind`,
`squeeze`/`squeeze-astotal` — has no consumer, and with it go `Data.Rational.Properties.Ext`'s "Masses within ε of one"
section (`1-ε≤m⇒1-m≤ε`, `x≤m*x+ε`, `1-[ε+ε]≤a*b`, `x≤y+c⇒x-c≤y`), `Uniform.indᵇ-≤1` and `Dp.cum-add`.
Not committed because `Protocol/Machine/Run/Lax.agda:5-6` (ruled KEEP) names `Dp.Mass.astotal-bind` as the route that
turns a lax prefix into an ε-agreement: the development is the one notion of almost-sure termination the layer has, and
whether that planned use justifies keeping it is your call. Spiked green (root + all leaves):
`QUALITY-REVIEW-R4D.d/mass-trim.patch` (+5/−140; Run.Lax's comment line then needs a one-line edit, part C).

### 2. `src/ProbabilisticLogic/Distribution/RationalDist.agda :: >>=ᴹ-identityʳ, >>=ᴹ-comm` — now consumerless (≈ −25)
Their only consumers were `Partial`'s `>>=⊥-identityʳ`/`>>=⊥-comm`, deleted in `fa33c431`. They are the right-unit and
commutativity laws of `Dist-ℚ` itself, so they were kept as the module's defining facts; by the "no consumer ⇒ delete"
test they go too (`>>=ᴹ-assoc`, `>>=ᴹ-identityˡ` stay, both used).

### 3. `src/Categories/Monad/Discrete.agda :: Elementwise, module Comm` — fold into `DiscreteMonad` (−16)
`Elementwise` was split off for `Monad.Setoids.Discrete`, which no longer exists; it now has one use (the
`elementwise` field) and costs a `module Comm` parameter plus `open … public hiding (module Comm)`. One record, with
`>>=-comm` as a second `field` block and `>>=-comm-y` after it. Spiked green (`Monad.Discrete`, `Class.Monad.Ext`,
`Machines.Base`): `QUALITY-REVIEW-R4D.d/elementwise-flatten.patch`. Not committed: the two producers
(`Machines/Base.agda:62`, `Class/Monad/Ext.agda:46`) are outside this part.
Same module: `<$>ᴹ-cong`, `<$>ᴹ-∘`, `>>=-<$>ᴹ` have no consumer (−9); kept as general functor-law facts (Categories/
exception), delete if you disagree.

### 4. `src/Categories/LocallyGraded/Monoidal.agda :: GradedMonoidalFunctor, Trivial-monoidal` — consumerless notion (≈ −55)
After `2bb4772b` (deleting `forgetᴹ`/`GradedMonoidal-forget`), the graded monoidal functor record and the trivial
graded monoidal structure have no consumer. Kept because they are the general notion of the `LocallyGraded` library
(Categories/ exception); delete with the header line 7 and the `Trivial` import if the library is not meant to grow.

### 5. `src/Categories/Category/Distributive/Monoidal.agda` (whole module) — root-only (−26)
`Cartesian-SymmetricMonoidal`/`MonoidalDistributive-Cartesian`: no importer except the root's index line. Unlike
`Kleisli.Distributive` and `Rels` it is not covered by a ruling. It is a general fact (a distributive category is
monoidal-distributive under ×) a user would look for; delete module + root line, or rule KEEP.

### 6. `src/ProbabilisticLogic/Dp/Settle.agda :: cum-settled-≈ₚ` → `Attains-≈ₚ` (0 LOC, fossil name)
It transports `Attains`, not `Settles`. Sites: `UC/Machine/StateEvent/Adequacy.agda:182`,
`Protocol/Machine/Trace.agda:19,286`, `docs/fcom-uc.md:115`, `docs/rcom-icom-b1.md:268` — mostly outside this part.

### 7. `src/ProbabilisticLogic/Dp/Advantage.agda :: Pr≤` — second spelling of `Pr≤[ true ]` (−3)
One use (`Upper`). Cited in `docs/mathematical-guide.md:15`, `docs/state-event-contract.md:44`,
`docs/simplification-options.md:133` and a comment in `Protocol/Machine/Agree.agda:112`; replace all by `Pr≤[ true ]`.

### 8. `src/ProbabilisticLogic/Dp/Elgot.agda :: padₛ, iterₚ-ctx` (−8)
`padₛ θ` is stdlib `Data.Product.Base.map₁ θ`; `iterₚ-ctx` is a one-line wrapper with one consumer
(`Machines/Base.agda:206`). Both changes land in `Machines.Base` (part C, perf-sensitive). Unspiked.

### 9. `src/Categories/Monad/Graded/FromMonad.agda :: sub-identityˡ, μ-identityʳ, μ-assoc`
`sub-identityˡ` is verbatim `Categories.Monad.Graded.Ext.sub-identityˡ` (stated for any triple); `μ-identityʳ`/`μ-assoc`
have no consumer. They complete the re-proved law set in this module's own `μ` spelling, so deleting them is a call
about whether `FromMonad` presents a full monad or only what is used.

### 10. `src/Categories/Category/Monoidal/Pure.agda :: PureSub.pure-λ⇐, pure-ρ⇐, pure-α⇐` — never projected (−6)
Dropping them strictly weakens the hypothesis every `Machines.*` module takes, so every consumer theorem gets more
general. But `PureSub` is documented as a wide *symmetric monoidal subcategory*, which contains the inverses; dropping
them changes which standard notion the record is. Your call.

### Smaller items
- `CategoricalCrypto/Machines/Base.agda :: MC` vs 8 re-applications of `Core (𝒱ₚ 0ℓ)` (`UC/Machine/{Slide:69,Composite:109,
  Dictionary:50,Monitor/Agree:41}`, `UC/QueryBound/Compose/Step:27`, `Examples/{CoinToss:34,ROCommitment:41}`,
  `Machines/Sandwich:30`): two spellings of one module application, three files mixing both (`MC.x` and unqualified).
  Replace each by `open MC` (parts B/C). Unspiked; check each for ambiguity and time `Composite`.
- `Categories/Category/Monoidal/Traced/Ext.agda` re-exports `β` (`… Symmetric.Properties.Ext symmetric public using (β)`)
  only so `GConstructionTrace` can re-export it again; sourcing it directly in GT clashes with GT's later full
  `open … Symmetric.Properties.Ext symmetric` (two applications), so it needs that block reshaped. 0 LOC.
- `Categories/GConstructionEmbedding.agda :: ⌜⌝-≅` takes `B⁻ ≅ A⁻`, so all three callers pass `MC.≅.sym x`; take
  `A⁻ ≅ B⁻` instead (statement change, 0 LOC).
- `ProbabilisticLogic/Dp/Coin.agda :: uniform-balanced` is `refl`; its two uses are in `Examples/CoinToss/Ideal/{,Receiver/}Machine`.
- `ProbabilisticLogic/Dp/Settle.agda :: Settlesᵀ*`, `uniformₚ-settles` (47 lines) have one consumer,
  `Examples/ROCommitment/Transport`; candidate to move there.
- `CategoricalCrypto/OracleCall.agda :: mapCall, reCall` are `Sum.map f (map₂ (f ∘_))` / `map₂ (map f (_∘ g))`; one
  consumer (`ChimericLedger/System.agda:56`). Unspiked.
- `Data/Nat/Poly.agda` (on `main`, flag only): its private `[2*n]^d≡2^d*n^d` is `Data.Nat.Properties.Ext.^-distribʳ-* d 2 n`.
- `Categories/LocallyGraded/SubCategory.agda :: Predicate` is the certified-arrow hom record, not a predicate (rename,
  importers in UC).
- `Data/Nat/Positive.agda :: value-injective` has no consumer; kept as the general fact about a refinement type.
- `CategoricalCrypto/GamePlaying/Partial.agda` (part A) takes 92 s warm (`--profile=modules`, measured here), within its
  rule-5 budget but the slowest module of the `RationalDist` cone.

## Tried, not worth it
- `src/ProbabilisticLogic/Distribution/RationalDist.agda :: mass, mass-L` — one mass notion (`mass μ = Lin.mass-L (toList μ)`,
  deleting `mass-L`, `mass-L-++`, `mass-scale-L`, `Lin-mass-L≡mass-L`; −29 net, root green). Dropped on perf:
  `GamePlaying.Partial` 91.9 s → 181.4 s (`--profile=modules`, same warm basis); root rebuild user time 3m03 → 5m14. The
  `* 1#` factors of the generic mass stay in every literal mass normalisation. Patch: `QUALITY-REVIEW-R4D.d/mass-unify-DEAD.patch`.
- `src/ProbabilisticLogic/Distribution/Uniform/Collision.agda :: 0≤countMatch` — `≤-reflexive refl` → `≤-refl`: not in scope
  there without another import; not worth an import line.
- `src/Categories/Category/Construction/Kleisli/Discrete/Pure.agda :: ≈-pure, ∘-pure, ⊗-pure` — inlining into `PureSubᵏ`
  breaks the named family `[]-pure` (used externally) belongs to; no gain.
- `src/Data/Rational/Properties/Ext.agda :: ∣∣≤` via `∣p∣≡p∨∣p∣≡-p` — same length; not done.

## Statement audit (dimension 1)

Key statements checked against their standard form: `Dp`'s `_≼ₚ_`/`_≈ₚ_`/`Cofinal` and monad laws, the Elgot set
(`iterₚ-fix`, `iterₚ-out`, `iterₚ-codiagonal`, `iterₚ-transfer`, `iterₚ-uniform`), `Dp.Advantage`, `Dp.Dominate`,
`Dp.Settle`, `Dp.Settle.Iter`, `Uniform.{Birthday,Collision,Duplicate,Decay}`, `Traced.Ext.Laws`,
`LocallyGraded.{Family,SubCategory}`. No vacuous statement, `refl`-theorem or rigged equivalence. Prose that overclaimed
was fixed in `6d027b89`. Statement changes that need your call:

- `src/ProbabilisticLogic/Distribution/Uniform/Duplicate.agda :: Φ-init` and `Uniform/Birthday.agda :: birthday,
  birthday-bound` — the proof establishes the textbook `Φ m [] = Γ 0 m = (0+…+(m−1))/2ⁿ = m(m−1)/2ⁿ⁺¹`, but publishes
  `(m²+m)/2ⁿ`, losing the pool shift (`Γ 0 → Γ 1`) and a factor 2 (`sumN-≤ t j : sumN t j ≤ j * (t + j)` drops the ½).
  Tighter: `birthday : ∀ q → Γ 1 q ≡ fromℕ (q * suc q) * inv-pow-2 (suc n)` (needs a closed-form `sumN`), and
  `Φ-init` stated against `Γ 0 m` or `m(m−1)/2ⁿ⁺¹`. Consumers (`ChimericLedger.{Birthday,Property}`,
  `MerkleDamgard.Core`, `GamePlaying.*`) then decide whether to weaken. `ChimericLedger/Birthday.agda:244` explains the
  loose bound as "`q²` fresh-hash pairs", which misreads the slack.
- `src/ProbabilisticLogic/Dp/Elgot.agda :: iterₚ-ctx` — the hypothesis quantifies over every `c` but the proof uses only
  the given one; `(c : C) → (∀ sa → v (padₛ (c ,_) sa) ≈ₚ …) → …` is strictly stronger. It is then
  `iterₚ-uniform u v (c ,_)` verbatim, so the wrapper can go (Suggestion 8; consumer `Machines/Base.agda:122,206`).
- `src/ProbabilisticLogic/Dp/Settle/Iter.agda :: Ranked, Settles-iter` — `Ranked` asks the drop at every depth `i`;
  `Settles-iter` spends it only at depth `proj₁ (bodyS w)`. Narrowing the hypothesis to that depth is strictly stronger;
  6 consumer sites (`Protocol/Machine/Trace.agda`, `Examples/ROCommitment/Realization/Machine.agda`), low priority.


## Out-of-scope edits
- `src/CategoricalCrypto/Protocol/Machine/Trace.agda:8` — comment named `Dp.Settle.Iter.Loop.Settles-iter`, which does not
  exist (it is `Dp.Settle.Iter.Settles-iter`); own commit `8f477605`.
- `docs/fcom-uc.md`, `docs/rcom-icom-b1.md` — resynced to `Dp.Settle.Iter` (in `934ba049`).

## Not reached
- The style sweep (using/implicit/join/binder/import) — assigned to the sweep agent per the brief.
- Lens 6 by full read only on the files the four finders covered (all 70); the GConstruction*Coherence perf-split
  modules and `Coherence/Monoidal/Tactic` beyond the macro were read for boundaries and consumers only.
- Suggestions 3, 8 and the smaller `MC`/`OracleCall` items were not landed because the call sites are in other parts;
  only Suggestion 3 is spiked.
- Dp small one-consumer wrappers (`node-nn`, `node-zero`, `cofinal-refl`, `dom≤⇒cofinal`, `upper-dom`, `map-map`) — each
  ≤ 3 lines of saving, not spiked.

## Verification
All at tip `6d027b89`, after a warm baseline root at `aae4d19e` (rc=0, 345 modules, 12m25 cold).

| check | flags | result |
|---|---|---|
| root `src/CategoricalCrypto.agda` | `-M8G -H2G` | rc=0, warn-grep empty, 133 modules re-elaborated, 3m26 user |
| `Abstract2.{Equivalence,OAPEmulation,WideSubcategory}` | `-M8G -H2G` | rc=0, warn-grep empty |
| `Examples.ChimericLedger.{Serialize,Transfer}` | `-M8G -H2G` | rc=0, warn-grep empty |
| `Examples.MerkleDamgard.{Pin,QueryBound}`, `Examples.RelSetup` | `-M8G -H2G` | rc=0, warn-grep empty |
| `RandomOracle`, `RandomOracle2`, `Standard2.Morphism` | `-M8G -H2G` | rc=0, warn-grep empty |
| `GradedKleisli.Functorial.Category`, `Coherence.Monoidal.Test.Tactic`, `Examples.RelationViewGreenSlime` | `-M8G -H2G` | rc=0, warn-grep empty |

These are all the non-root import-DAG leaves outside the solver tests. Every touched module was also checked on its
own before its commit (`-M3G -H1G`). Intermediate roots: after the first 16 commits (rc=0, 168 modules) and with the
law-block and Mass spikes applied (rc=0, 153 modules, all leaves green).
Timing: the one budget overrun (`GConstructionTrace` at 328 s wall-clock) was queueing behind the memory gate; the same
module re-measured warm takes 24 s wall-clock / 10.6 s user.

Gates: escape-hatch grep over `src` is 16 lines before and after, the same lines (all prose in solver-origin files).
Byte-level NUL check (python `b'\0' in blob`) over all 38 added or changed files: clean. `git diff --check aae4d19e HEAD`: clean.
