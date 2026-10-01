# Quality review — protocol-rewrite, part D-foundations (2026-09-29)

Scope: the 75 files of `scope-D-foundations.txt` at `c71d95fe` (9.9k LOC):
`src/ProbabilisticLogic/**`, `src/Categories/{GConstruction*,Category/**,Monad/**}` (the
nine in-scope `GConstruction*` modules; `GConstruction.agda`/`GConstructionCoherence*` are
out of scope), and `src/{Class,Data,Function,Relation}/**` not owned by another part.
Carried-forward ledger: the branch's own `QUALITY-REVIEW.md`. Every entry below that
matches one of its items says so (`LEDGER`), and nothing it records as a pending
Suggestion or Tried was committed here.

Verification: pagda check run: yes. Every commit's touched modules and their in-part importers
checked rc=0 with an empty warning grep (`-M3G -H1G`/`-M4G -H1G`; `-M8G` for
`ProbabilisticLogic.Expectation` and its two importers, which exhaust 3 GiB).
Root and non-root leaves at the tip: see *Verification* at the end.
Soundness baseline (rule 3 grep over `src`): 16 before, 16 after, identical lines —
none in this part's files. Byte-level NUL check over every committed blob: clean;
`git diff --check c71d95fe HEAD`: clean.

Sweep tally (toolkit JSONs in `QUALITY-REVIEW-D-foundations-tallies/`): per class kept/candidates (files skipped by the tool in brackets) —
`using-drop` 189 kept of 286 enumerated (3 runs: the first pass hit a disk-full outage and a
3 GiB heap on the `Abstract` island; re-run at `-M8G`, JSONs `using-drop*.json`);
`join-lines` 55/61; `binder-drop` 4/209 (3 kept, 1 declined, see *Tried*);
`implicit-drop` NOT finished (see *Suggestions* §11); `enum-with` 19 sites — machine
spike `with_case.py`: 0 converted, 12 red, 8 skipped-shape, then 3 hand-converted
(`≟-refl`, `runPath-step`, `runPath-nothing`); `enum-where` 206 sites (160 flagged
single-use) — machine spike `where_inline.py`: 6 inlined (kept), 18 red, 51 declined
(over width), 172 skipped-shape (not single-use at the use site); `enum-comments`
432 blocks, every one dispositioned in `enum-comments-dispositions.tsv`: 215 cut,
91 rewritten, 119 kept with the named reason, 7 left because they sit on code a
Suggestion below would change.

## Committed (you can skim these)

- `36d2adbf` Bare opens where a using list resolves no clash (sweep: using-drop) — 44 files, −14; oracle-green per file.
- `44216c75` Comments: cut narration and stale prose, keep the non-obvious why — 66 files, −789; comment-only (one trailing comment on a `where`), per-block table committed; stale claims fixed (e.g. `Monad/Discrete`'s "builds one", `Kleisli/Discrete/Distributive`'s "nothing touches the monad beyond the left unit law", `Monoidal/Distributive`'s "initial", `Dp/Advantage`'s pointer to a non-existent `UC.Approximate.Mass`, four dangling `docs/` citations).
- `496e02f2` One-line layout where a construct fits the file width (sweep: join-lines) — 22 files, −60.
- `554de2f9` Generalize two field telescopes over the block variables (sweep: binder-drop) — `PureSub.Pure`, `MonadSetoid.≈ᴹ-isEquivalence`; same statements (the dropped binders are the block's own variables at the same level).
- `90cb8739` GConstruction: drop redundant imports and aliases; `mid-σ` is `switch-fromtoʳ` — 4 files, −20; statements unchanged, `mid-σ` = upstream `Morphism.Reasoning.switch-fromtoʳ` on `Interchange.Symmetric.swapInner-iso` (rule 30).
- `e7ec9e53` Distribution: reuse the Ext metric lemmas and stdlib Bool facts — 6 files, −37; `advᵇ⊥-sym/-triangle`, `adv⊥-≈⇒0`, `E-abs-diff`, `E⊥-abs-diff` via `Ext.∣-∣-comm/∣-∣-triangle/∣x-x∣≡0`; `Partial`'s private re-derivation of `mass-as-const` gone; `∨-middle` = stdlib `interchange`; `∨-trueʳ/falseʳ` = `∨-zeroʳ/∨-identityʳ`.
- `2815f2f5` Dp: one name per fact — 4 files, −24; `Elgot.mapₚ-fn` = `Reasoning.map-eq`, `Iter.mapₚ-≈ₚ` (no user) = `map-arg`, `Settle.Settlesᵀ-coin` alias, `Coin.0≤ind` = `0≤bool`; every removed name grepped zero-reference over `src`.
- `c8fe9196` Utilities: stdlib `≟-refl`, rewrite in runPath lemmas, unused opens and binders — 6 files, −8.
- `0853998b` Inline single-use where bindings (sweep: where-inline) — 4 files, −10, plus the tally/disposition files.

Judgment-bearing commits (the four code commits) were checked by an independent
adversarial read (statements, removed names, taste): all hunks ACCEPT; its two nits
(double blank lines) and one follow-up (`Partial`'s now-unused `open import Algebra`)
were applied before committing.

## Suggestions (need your call), ranked by LOC saved / complexity removed

### 1. Retire the `ProbabilisticLogic` "abstract probability" island (≈ −2080 LOC, 14 modules + `LibExt`)
- `src/ProbabilisticLogic/Abstract.agda :: AbstractCore` (with `Logic`, `Expectation`,
  `Reasoning`, `Models/Trivial`, `Distribution/{Bernoulli,Binomial,Markov}`,
  `Examples/{BiasedCoin,Coins,MultipleCoins,Weather}`, and out-of-scope `src/LibExt.agda`)
  — a second, parallel notion of probability and expectation. It typechecks only because
  `CategoricalCrypto.agda:97` imports the index `ProbabilisticLogic`; no module outside the
  island imports any of it (grep over all of `src`), `LibExt` is imported only by four
  island files, the record's only instance is `Models/Trivial.Triv` (degenerate,
  `0# ≈ 1#`), and every example is a parametric theorem never instantiated. The live
  library's monad is `Dist-ℚ` (`RationalDist`, laws in `RationalDist.Setoid`) and its
  expectation `RationalDist.Expectation.E`. Proposal: delete the 14 modules and `LibExt`,
  and shrink `ProbabilisticLogic.agda` to the live `RationalDist` modules. Public API
  removal, hence yours. It also removes a perf defect: `ProbabilisticLogic.Expectation`
  (516 LOC) exhausts a `-M3G -H1G` heap and needs `-M8G` (measured this run; its header
  documents no cost).
- If the island stays, the smaller items the finder found: `Abstract :: _⁻¹, d,
  +-mono-≤, >>=-cong-l, _>>=_` and the `Abstract` record itself have no consumer
  (≈ −110); `Expectation :: weight-sum*` is `Distribution/Linearity.lookup-L*` at
  `Probabilityᴿ` and the `E-+` chain is dead (≈ −260); `Logic :: Σ-zero, Σ-weaken, Σ-mono,
  ⇒-resp-≐-Y` are dead and `Σ[_][_]_` is a one-field record standing for `p ≤ P ∙ X`;
  `Binomial :: pow`/`pow-cong` are stdlib `_^_`/`^-congˡ`, `P-all-true`/`P-all-false` one
  lemma at `↑ id`/`↑ not`, and `count`, `exactly`, `at-least`, `at-most`,
  `E-binomial-1-first-true`, `E-binomial-count` family (≈ −110) are dead; `Bernoulli ::
  E-bernoulli-true/false` and `Markov :: StochasticKernel, fromMatrix` are dead.

### 2. `src/Categories/GConstructionTensorCoherence.agda :: U.UL, U.UR, A.AC` — retire onto upstream interchange laws (≈ −120..−135 LOC, removes a 61 s solver module)
LEDGER (`GConstructionTrace :: mid`, the "`swapInner-unitˡ/ʳ/-assoc` vs `U.UL/UR/A.AC`
not settled" note) — this settles it on paper. agda-categories 0.3.0 makes `⊗` a strong
symmetric monoidal functor (`Categories.Functor.Monoidal.Tensor`) with
`⊗-homo = swapInner`, `associativity = swapInner-assoc`, `unitaryˡ/ʳ = swapInner-unitˡ/ʳ`;
`f ⊗₁ᴳ g = mid ∘ f⊗g ∘ mid` is conjugation by that `⊗-homo`, so UL/UR/AC are its
unitality/associativity conjugated (`⌜⌝-⊗` is its `braiding-compat`, already taken).
Derivation sketch (object indices checked on paper, not machine-checked): UL — rewrite
`σ{I,I}` to `id` (`braiding-coherence` + Kelly `coherence₃`), unfold `mid{I,I,X,Y}` by
`swapInner-unitˡ` and its self-inverse form, cancel the outer unitors, close by unitor
naturality; UR symmetric via `coherence₃`; AC — `id⊗α⇒ ∘ i⇒ ∘ i⇒⊗id = α⇐⊗id ∘ (α⇒⊗α⇒ ∘
i⇒ ∘ i⇒⊗id)` which is `swapInner-assoc`, input side by the inverse instance. Plan: three
C-level lemmas in `GConstructionTrace` beside `mid-*` (an 8 s module), not in
`GConstructionMonoidal` (the ledger's measured 9 s → >912 s re-price when explicit chains
live there); delete `GConstructionTensorCoherence` and its import. Needs a rule-31
before/after. Also drops one `pattern 10F/11F` copy and two `midᵗ` copies.

### 3. `src/Categories/GConstructionLoop.agda :: trace-mid` (+ `GConstructionLoopCoherence`, whole file) — JSV sliding (≈ −150..−190 LOC, removes a 68 s module)
`Traced.Ext.Laws` adds congruence, both naturalities and exchange to upstream `Traced`,
but not dinaturality (sliding: `trace ((id ⊗ g) ∘ h) ≈ trace (h ∘ (id ⊗ g))`). With it,
`trace-mid` is four lines (`g = mid`, `h = id ⊗ mid ∘ f`, `mid-involutive`) and the
36-line `vanishing₂`/Fubini chain plus all of `LoopCoherence` go; `trace-comm` is also a
standard consequence of sliding + `vanishing₂`. Changes the hypothesis record `GConstruction`
assumes (a new `Laws` field, to be proved for `Machines/G.agda :: Mealy-TraceLaws`), so it
is yours; first step: check whether sliding already follows from the four existing
fields (then it is a lemma and no statement changes).

### 4. `src/ProbabilisticLogic/Dp.agda :: Cofinal, Dom₀, Dom` — one approximant-sequence relation (≈ −15 net, four spellings → one)
After A3 the dominance relations are two definitions and five derived spellings, all on
`cumₛ d P = λ n → cum n d P : ℕ → ℚ`:

| today | as one application | definitional? |
|---|---|---|
| `Cofinal P Q d e` | `cumₛ d P ≼ cumₛ e Q` (exact) | yes |
| `Dom₀ P` | pure alias of `Cofinal P P` — two names for one notion | yes |
| `Dom P ε d e` | `cumₛ d P ≼[ ε ] cumₛ e P` | yes, verbatim |
| `Mass._≼ᵐ_` | `Cofinal (λ _ → 1ℚ) (λ _ → 1ℚ)` | yes |
| `_≼ₚ_` | `∀ P → NNF P → cumₛ d P ≼ cumₛ d′ P` | yes |
| `Advantage._≼ₚ[_]_` | `∀ b → cumₛ d (indᵇ b) ≼[ ε ] cumₛ e (indᵇ b)` | yes |
| `_≈ₚ_`, `_≈ₚ[_]_` | pairs of the two above | — |
| `Dominate.Dom≤` | bounded prefix; keep local (one generic fact) | — |
| `Stable`, the Σ+ "attains" shape (9 open-coded sites) | `Attains (cumₛ d P) v` | yes |

**Spiked, green.** A local stand-in module `Seq` (exact `_≼_` primitive,
`x ≼[ δ ] y = x ≼ (λ m → y m + δ)`, `≼-refl`, `≼-trans`, `≼-mapʳ`, `≼-+ʳ`, and
`≼⇒≼[0]`, `≼[]-mono`, `≼[]-trans`, `≼[]-resp` derived from them) with
`Cofinal P Q d e = cumₛ d P Seq.≼ cumₛ e Q`, `Dom P ε d e = cumₛ d P Seq.≼[ ε ] cumₛ e P`,
and every `cofinal-*`/`dom-*` lemma a one-line application, typechecks: `Dp` rc=0, and
unchanged importers `Dp.Advantage`, `Dp.Dominate`, `Dp.Mass`, `UC.Seam.Grounding`
(67 modules rebuilt) and `UC.Machine.Dominated` all rc=0, warning-clean — the
restatement is definitional, no call site moved. The generic lemmas must take their
sequences EXPLICITLY (see *Tried*). Patch:
`QUALITY-REVIEW-D-foundations-tallies/spike-dp-seq.patch` (+27 in-file because `Seq`
is local; −30 in `Dp` once `Seq` is `Approximants`).
Against `Data.Rational.Approximants` (on the other branch; not added here): restate
`Cofinal`/`Dom` as its relations at `cumₛ`, and let `cofinal-refl/-trans`, `dom₀⇒dom`,
`dom-mono`, `dom-trans` (with its private `shuffle`), `dom-resp` become its generic
lemmas; `≼ₚ-*`, `≼ₚ[]-*`, `≈ₚ[]-*` stay as one-line applications. Two requests for that
module: (a) it has no exact `_≼_`; make exact the primitive and define
`x ≼[ δ ] y = x ≼ (λ m → y m + δ)` — β-identical to its current `_≼[_]_`, so its
consumer is unaffected, and every slack lemma follows from `≼-refl`, `≼-trans`,
`≼-mapʳ` (pointwise `≤` on the right) and `≼-+ʳ`; (b) name its slack lemmas `≼[]-refl`/
`≼[]-trans` (matching `Dp.Advantage`'s `≼ₚ[]-*`) so the exact ones can be `≼-refl`/
`≼-trans`. The header's "`+ 0ℚ` is not definitional" is a real obstruction to *defining*
`Cofinal := Dom 0ℚ` (≥ 29 hand-built exact witnesses would each pay a `+-identityʳ`),
not to sharing the lemmas — the exact-primitive layout above sidesteps it. Delete
`Dom₀` (11 uses → `Cofinal P P`: Dp 3, Dominate 4, `UC/Machine/Dominated` 3,
`UC/Seam/Transfer` 1). Fallout ≈ 20 call sites in 7 files (4 outside this part:
`UC/Seam/Grounding` ×6 for `cofinal-trans`, `UC/Machine/Dominated`, `UC/Seam/Transfer`);
risk = the six Grounding sites inferring sequence arguments (`Dp.Reasoning`'s header
warns about stranded subjects) — one timed check. LEDGER (`UC/Seam/Carry.agda :: Reads`,
the Σ+ shape) — new evidence: six more open-coded sites and the generic
`attains-resp` that `Settle.cum-settled-≈ₚ` becomes.

### 5. `src/ProbabilisticLogic/Dp/Commutative.agda :: cum-test-+` (with the `cum` linear family) — bridge to `Distribution.Linearity` (≈ −60..−80)
LEDGER (`Dp/Mass :: cum-add`, `Dp/Dominate :: cum-zero`; still present verbatim) — widened:
the whole linear family has list-level twins in `Distribution/Linearity.agda`
(`cum-test-+`/`cum-add` ↔ `lookup-L-+`, `cum-test-0`/`cum-zero` ↔ `lookup-L-zero`,
`cum-test-*` ↔ `lookup-L-*ₗ`, `Mass.cum-const` ↔ `lookup-L-const`, `cum-fubini` ↔
`lookup-L-swap`, `cum-cong-P` ↔ `lookup-L-cong-P`). One inductive
`flatten : ℕ → Dₚ A → List (ℚ × A)` (structural in `n`, so `Dp`'s guardedness remark does
not bite) plus `cum-flatten : cum n d P ≡ lookup-L (flatten n d) P` (~25 LOC) turns
`cum-add`, `cum-test-±`, `cum-zero`, `cum-const`, `cum-fubini` and the helpers `node-+`,
`node-*`, `regroup`, `distr` (~120 LOC) into 2–3-line applications. Budget-monotone and
bind-sandwich lemmas stay native. Also `Coin :: 0≤E` and `Settle :: E⊥-nn` are one
missing `RationalDist.Expectation :: E-nn`.

### 6. `src/Categories/Monad/Setoids/Discrete.agda` vs `src/Categories/Monad/Discrete.agda :: DiscreteMonad` — one notion (≈ −25..−45)
`Setoids/Discrete` re-declares the whole `DiscreteMonad` vocabulary (`≈ᴹ-setoid`, `M`,
`_≈ᴹ_`, `module ≈ᴹ`, `≈ᴹ-Reasoning`, fixities, the five laws) and a separate
`Commutative` record, and re-opens `Derived` with the same positional telescope; it never
builds a `DiscreteMonad` (the `Monad/Discrete` header's "builds one from a full triple"
was false — corrected in the comment commit). Proposal: `record Elementwise ℓ` (the laws
without commutativity, `Derived`'s body inlined), `DiscreteMonad = Elementwise +
>>=-comm`, and `Setoids.Discrete K` produces an `Elementwise`. `Kleisli.Discrete` and the
12 `KD (Dₚ-DiscreteMonad …)` sites stay; `Dₚ-DiscreteMonad` changes by ~3 lines. Optional:
`SFunM/Kleisli/Properties` via `Klᴹ` retires `Setoids.Discrete.Kleisliᴹ`, `∘ᴹ-bind` and
`Kleisli/Ext.extend-μ` (another −10). The same Yoneda-commutativity 7-step proof exists
three times (`Class/Monad/Ext.agda:42-60`, `Class/Monad/Ext/Setoid.agda:108-129`,
`Monad/Discrete.agda:74-92`); level-generalizing `Derived` lets both setoid presentations
share it (≈ −25).

### 7. Dead public code (rule 32 — your call; each grepped over all of `src`, re-exports included)
- `src/Categories/Monad/Construction/Kleisli/Ext.agda :: KleisliTriple⇒ᴹ` (with `toMonad⇒`,
  `fromMonad⇒`, `⇒-setoid`, `⇒ᴹ-setoid`, `⇒↔⇒ᴹ`) — lines 48-126, zero consumers; only
  `extend-μ` and `KleisliTriple⇒` are used (≈ −85).
- `src/Class/Monad/Ext/Setoid.agda :: FromPropositional` (and `<$>ᴹ-congˡ`) — zero
  consumers, a third presentation of the same monad-with-setoid notion (≈ −40).
- `src/ProbabilisticLogic/Dp/Iter.agda :: iterₚ-turn, iterₚ-done` (then
  `Dp :: exactˢ⇒≈ₚ`, whose only use is `iterₚ-done`) (≈ −19);
  `src/ProbabilisticLogic/Dp/Mass.agda :: ≼ᵐbot⇒0, massless-≈ₚ[0]` (≈ −12, likely leftovers
  of the deleted `Dp.Zero`); `src/ProbabilisticLogic/Dp/Stable.agda :: Stable-bot` (−2).
  LEDGER `Dp/Mass :: mass-mono, total-mass`, `astotal-returnₚ`, `const-bind-astotal` —
  still zero-consumer.
- `src/ProbabilisticLogic/Distribution/RationalDist/Partial.agda :: dmap-ret, Dmapⱼ-cong`
  (−8) and `:: mass-L-toList` (a `refl` cast whose one use this run removed, −2);
  `src/ProbabilisticLogic/Distribution/Possibility.agda :: 𝒫-setoid` with `module 𝒫`
  (−4; also confusing: two same-named modules for two equalities);
  `src/ProbabilisticLogic/Distribution/RationalDist/Advantage.agda :: advᵇ⊥-sym,
  advᵇ⊥-triangle` (zero consumers; now one-liners after this run, so cheap to keep).

### 8. Forwarding layers (rule 19)
- `src/ProbabilisticLogic/Prelude.agda` (whole module) — LEDGER (`:: >>=ᴹ-congʳ`). New
  evidence: the module only re-exports, 5 of its 11 importers already import the sources
  alongside it, and seven re-exported names have no consumer reached through it
  (`mass-1`, `lookupᴰℚ-bind`, `Pr₁-bind`, `Pr₁⊥-just`, `>>=ᴹ-congʳ`, `adv⊥-triangle`,
  `adv⊥-≈⇒0`). Proposal: delete; each importer opens `RationalDist`, `.Partial` (for the
  `Dist⊥` instances), `.Expectation`, `.Setoid`, `.Advantage`, `Uniform` directly
  (net ≈ −15..−20; importers are in parts A/B/C).
- `src/ProbabilisticLogic/Dp/Elgot.agda :: open … public using (iterₚ; …)` — the only
  importer (`Machines/Base.agda:37`) already imports `Dp.Iter`, `.Codiagonal`, `.Out`
  directly; it needs one `open import ProbabilisticLogic.Dp.Iter.Transfer` for
  `iterₚ-transfer`. Then lines 35-38 and the Codiagonal/Out imports go (−6, +1 in
  `Machines/Base`, part C).
- `src/ProbabilisticLogic.agda :: open import … Abstract public`, `… Reasoning public` —
  the index's one importer uses none of them (moot under item 1).
- `src/Data/Sum/Ext.agda :: unitˡ⇒, unitʳ⇒` — stdlib `Data.Sum.Base.fromInj₂ ⊥-elim` /
  `fromInj₁ ⊥-elim` (agree on constructors; stdlib's have `[_,_]′` bodies). Delete the
  module; 5 consumers (`SFunM/{Monoidal,Morphism,Kleisli/Monoidal,Kleisli/Morphism}`,
  `SFunPartial`, whose `renaming (unitˡ⇒ to unbot) public` goes with it) need a green
  check at the `triangleᵉ`/`statelessᵉ` reduction sites (−19). LEDGER-partial
  (`:: ⊎assocˡ` — that half is gone; the unit half is new).

### 9. Placement (rules 27/28) — relocations whose importers are outside this part
- `src/ProbabilisticLogic/Dp/Iter.agda :: mapₚ-cum, leafₚ-mapₚ, returnₚ-cum-≤` — general
  `Dₚ` facts; home `Dp.agda` after the monad laws, with `Commutative :: mapₚ-≤`. Then
  `Dominate` and `Commutative` drop their `Dp.Iter` import. Blocked here only because
  `UC/Seam/{Transfer,EventTransfer}` import `returnₚ-cum-≤` from `Dp.Iter` by name.
- `src/ProbabilisticLogic/Dp/Stable.agda :: coin-bind-cum` → `Dp.Coin` (its first step is
  Coin's private `branch`; −3; importers `UC/Seam/{Transfer,EventTransfer}`).
- `src/ProbabilisticLogic/Dp/Settle.agda :: E⊥-coin` → `RationalDist.Expectation` (pure
  `Dist⊥`, no `Dₚ`; consumer `Protocol/Machine/Raw.agda:79`).
- `src/ProbabilisticLogic/Distribution/RationalDist/Expectation.agda :: 0≤bool` (with
  Expectation's local `b≤1`/`bd`, `Dp/Advantage :: indᵇ-nn`, `Dp/Mass :: indᵇ-≤1`) →
  `Distribution/Uniform.agda` beside `bool→ℚ`/`indᵇ`. LEDGER (`Uniform :: indᵇ-≤1`,
  `Dp/Mass :: 0≤1-`) — new sites: `Support :: 0≤1-ε` (same proof as `Dp/Mass.0≤1-`),
  `Support :: 0<1ℚ`, `Advantage :: swap-compl`, `Dp/Mass`'s private `co`/`back`/`cancel`
  (the last two are `Ext.−-+-cancel`/`+-−-cancel`), and `p≤p+q`/`p≤q+p` open-coded at
  `Collision:58,63`, `Duplicate:98`, `Birthday:54`, `Uniform:97,139` — all belong in
  `Data/Rational/Properties/Ext.agda`.
- `src/ProbabilisticLogic/Distribution/RationalDist/Advantage.agda :: E-not` (private) —
  the complement rule on `Dist-ℚ Bool`, the analogue of `Dp/Mass.verdict-mass`; public in
  `Expectation`.
- `src/Categories/Category/Kleisli/Discrete.agda` (with `/Distributive`, `/Pure`) —
  upstream keeps Kleisli constructions under `Categories.Category.Construction.Kleisli`;
  target `Categories.Category.Construction.Kleisli.Discrete{,.Distributive,.Pure}`
  (0 LOC, 18 importers).
- LEDGER, still valid at `c71d95fe`, nothing new: `Categories/Category/Monoidal/Utilities/Ext.agda
  :: scalar-λ⇐` (→ `Monoidal.Properties.Ext`), `GConstructionEmbedding :: ⌜⌝-id`,
  `unitorˡᴳ`/`unitorʳᴳ`/`associatorᴳ` placement, `GConstructionLoop :: trace-conj`
  (still open-coded at `GConstructionMonoidal.homomorphismᴳ`), `GConstruction ::
  (module layout)`, `GConstructionHomCoherence :: pattern 10F`, `Dp/Support` → `Dp.agda`.
  `GConstruction :: TraceLaws` is done (`Traced.Ext.Laws`); its `Cˢ` sibling (five
  identical copies: `GConstruction:45`, `Trace:45`, `Embedding:51`, `Loop:34`,
  `Monoidal:52`) is still open. `GConstructionTensorCoherence :: midᵗ` (FreeWiring)
  still valid with updated in-scope counts: `midᵗ` ×5, `βᵗ` ×2, `αᵗ`/`γᵗ` ×3, `S≤S` ×6
  (items 2 and 3 would cut these).

### 10. Statement audit
- `src/ProbabilisticLogic/Distribution/Markov.agda :: stepⁿ` — named and bannered "the
  n-step distribution for a stochastic matrix", but `empirical (NE.concatMap M …)`
  renormalises uniformly over the concatenation (the flaw of the removed
  `>>=-empirical` axiom, `Abstract.agda:315-319`). Correct only for uniform row width:
  `M s₀ = [s₀,s₁]`, `M s₁ = [s₁]` gives P(s₁) = 2/3 at `n = 2`, the true value is 3/4;
  `Examples/Weather` holds because both rows have width 3. Subsumed by item 1; else
  require uniform width or build it with `_>>=_`.
- `src/ProbabilisticLogic/Models/Trivial.agda :: Triv` — "sanity check that the axioms are
  consistent" is vacuous for the stated purpose: the one-point model validates exactly
  the collapse `Abstract.agda:52-57` guards against; there is no non-degenerate model
  (header reworded in the comment commit; item 1 subsumes).
- `src/Categories/Category/Monoidal/Pure.agda :: PureSub` — called a "wide symmetric
  monoidal subcategory … the structural isos are inside it", but the fields ask only for
  `λ⇒ ρ⇒ α⇒ σ⇒`; `λ⇐`/`ρ⇐`/`α⇐` are not derivable from them, and a monoidal
  subcategory needs both directions. Either add `pure-λ⇐ pure-ρ⇐ pure-α⇐` (the Kleisli
  instance discharges them by `structural (tt ,_)`, `structural (_, tt)`,
  `structural assocˡ′`) or keep the fields (the header now says "not their inverses").
  LEDGER (`:: PureSub → SubCat` decline stands); the mismatch is new.

### 11. Smaller simplifications not committed (judgment or out-of-part fallout)
- `src/ProbabilisticLogic/Dp/Coin.agda :: ind˘` — definitionally `indᵇ false`
  (`Uniform.agda:47`); 16 uses in Coin, 2 in Stable. Not landed: `coinₚ`'s weight is
  spelled with it and `coinₚ` is converted against in heavy UC modules; needs a timed
  root check (−3).
- `src/Categories/Category/Kleisli/Discrete.agda :: λ-isoˡ … α-isoʳ, σ-involutiveᵏ,
  ⊗ᵏ-identity` — seven public one-liner iso lemmas with zero external uses, inlinable into
  the `Klᴹ-Monoidal`/`Klᴹ-Symmetric` literals; `⊗ᵏ-identity` is `pureᵏ-⊗ id id`; the file
  is eta-sensitive (its header) (≈ −20).
- `src/Categories/Category/Kleisli/Discrete/Pure.agda :: IsPure` — a Σ in disguise:
  `Σ[ h ∈ (A → B) ] f ≈ᵏ pureᵏ h` with `fn = proj₁`, `is-fn = proj₂` keeps every
  `P.fn`/`P.is-fn` consumer (≈ −10).
- `src/Categories/Category/Monoidal/Distributive.agda :: δ⇒` — a pure alias of
  `distributeˡ`; upstream `Categories.Category.Distributive` names the field `isIsoˡ` and
  has `distributeˡ⁻¹-i₁`, the analogue of `δ⇐-i₁` (drop `δ⇒`, or adopt upstream names;
  39 `δ⇐` uses).
- `src/Categories/Category/Cocartesian/Ext.agda :: α+⇒, α+⇐` — definitionally upstream's
  `+-assocˡ`/`+-assocʳ`; define them so (0 LOC, rule 30).
- `src/Categories/GConstructionEmbedding.agda :: ⌜_,_⌝` (with `⌜⌝-resp-≈/-id/-∘/-≅`) —
  these are the functor laws of `⌜⌝ : C × Cᵒᵖ → G` (the JSV inclusion into Int);
  packaging a `Functor` makes `⌜⌝-≅` upstream's `[_]-resp-≅` (conceptual, ≈ 0 LOC).
- `src/ProbabilisticLogic/Distribution/RationalDist/Partial.agda :: module Eq` — the
  reflexive-pin `>>=ᴹ-cong {μ = x} {x} {f} {g} (Eq.refl {x = x}) pt` sites are
  `RationalDist.Setoid.>>=ᴹ-congˡ x f g pt` (≈ −7; keep the explicit pins, `_≈Mℚ_` only
  mentions `entries`).
- `src/ProbabilisticLogic/Distribution/RationalDist/Support.agda :: χ, 0≤χ, χ-pos` — a
  third ℚ indicator beside `bool→ℚ`/`indᵇ`: `χ P = bool→ℚ ∘ P` (≈ −4);
  `:: dec-∨, dec-∧` via `Relation.Nullary.Decidable.does-⇔` (≈ −4).
- `src/ProbabilisticLogic/Distribution/Possibility/Setoids.agda :: >>=𝒫-identityˡ,
  >>=𝒫-identityʳ, >>=𝒫-assoc` — one-line public bodies used once; inline into
  `𝒫-KleisliTriple` (≈ −10).
- `src/ProbabilisticLogic/Dp/Dominate.agda :: ≈⇒dom₀` — `proj₁ de P nn`; inline at
  `UC/Machine/Dominated.agda:116,119` (−3).
- `src/Data/Bool/Properties/Ext.agda :: ∨-mono, ∨-monoʳ` — stdlib naming would be
  `∨-mono-≤`, and `∨-monoʳ : a ≤ b → a ≤ b ∨ c` is not monotonicity (2 uses in
  `ChimericLedger/Observable`).
- `implicit-drop` class — **work item, unfinished**: 396 candidates over the 75 files (Partial 75,
  Cocartesian/Ext 43, GConstructionMonoidal 32, Kleisli/Discrete 25, …). The run was
  started at `-M8G` and stopped after ~2 h under memory-gate contention (four other
  reviews checking concurrently) without completing one file's bisection; no survivors
  were produced, so none is committed. 88 of the 396 sit in files the branch ledger's
  class-level `implicit-drop` decline (*Tried*) covers; for the other 308 rule 15
  applies. Cost: one bisection per file, O(log n) checks of 5–30 s warm each
  (≈ 75 files × 6 checks ≈ 450 checks ≈ 1–2 h on a free gate).

## Tried, not worth it
- `src/ProbabilisticLogic/Dp.agda :: Cofinal` (the §4 spike, first variant) — the generic
  lemmas with IMPLICIT sequence arguments are red: `_≼_` unfolds to a Π, so
  `?x ≼ ?y =?= cumₛ d P ≼ cumₛ e P` never solves (`_z m + δ = cum m h P + δ`, blocked).
  The second variant, sequences explicit, is green (see §4). Consequence for
  `Data.Rational.Approximants`: its `≼-refl`/`≼-trans` take `x`/`y`/`z` implicitly and
  will strand metas at every `cum` instance — make them explicit there.
- `src/ProbabilisticLogic/Distribution/RationalDist/Expectation.agda :: maybeℚ, E⊥` —
  `binder-drop` survivor declined: the file's `variable A` lives in `Type` (level 0),
  so dropping `{A : Type ℓ}` would have narrowed both definitions.
- `src/ProbabilisticLogic/Distribution/Possibility.agda :: ∨-middle` — first placement of
  the stdlib `interchange` import inside `private` is red (`UselessPrivate`); landed as a
  top-level parameterised open instead.
- `enum-with` sites (19): `with_case.py` converts none (12 red — the scrutinee must be
  abstracted in the goal: `runPath`'s own clauses, `χ`/`0≤χ`, `memb-*`, `1≤countMatch`,
  `Expectation`'s `ω ∈? sf`; 8 skipped-shape: `with … | eq`, `in e`, pattern-bound
  `with`). Three were closed differently instead (see *Committed*).
- `enum-where` sites: the 51 width-declined and 18 red inlines, per-site verdicts in
  `where-inline.json`.
- `join-lines`: 6 candidates reverted red by the oracle (`Dp.agda` ×2, `Stable`,
  `Settle`, `Expectation` ×2).

## Out-of-part observations (reported only)
- `src/CategoricalCrypto/SFunM/Spike/**` — no importer anywhere and not reached from any
  root; contains verbatim pre-extraction copies of in-scope modules
  (`Spike/KleisliDiscrete.agda` ≅ `Categories/Category/Kleisli/Discrete.agda`,
  `Spike/MonoidalDistributive.agda` ≅ `Categories/Category/Monoidal/Distributive.agda`,
  `Spike/KleisliDistributive.agda` generalizes `Kleisli/Discrete/Distributive`) —
  ≈ −3755 LOC for the 15-module tree.
- `src/CategoricalCrypto/Examples/ChimericLedger/System.agda:24 :: open import
  ProbabilisticLogic.Prelude` — no Prelude name is used there (check `Dist⊥` instance
  resolution before removing).

Integration-owned files: none of this part's findings touches one.

Out-of-scope edits: none.

## Verification (tip `0853998b` + this file)

| module | rc | warn | Checking lines | s |
|---|---|---|---|---|
| `src/CategoricalCrypto.agda` (`-M8G -H2G`; a `-M16G` run queued 3600 s behind the gate and was discarded) | 0 | 0 | 87 | 199 |
| `Examples/ChimericLedger/ReplayFamily` (timed out at 1800 s while rebuilding 115 modules on a contended gate; re-run) | 0 | 0 | 0 (cache hit of that build) | 12 |
| `Examples/ChimericLedger/Serialize` | 0 | 0 | 2 | 12 |
| `Examples/ChimericLedger/Transfer` | 0 | 0 | 2 | 12 |
| `Examples/MerkleDamgard/Pin` | 0 | 0 | 8 | 76 |
| `Examples/MerkleDamgard/QueryBound` | 0 | 0 | 1 | 10 |
| `SFunM/Spike/Instance/{SetoidDist,Type,TypeDist}` | 0 | 0 | 11/4/5 | 22/9/32 |
| `UC/Approximate/LocalTests`, `APROP/…/Test/{FindIso,Split,SubMatch}Tests` | 0 | 0 | 0/2/2/1 | ≤ 8 |

The eight `NOT-IN-ROOT` rows are every import-DAG leaf reached from this part's files
that the root does not import; the four `*Tests` suites are the closure check.
