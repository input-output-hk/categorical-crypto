# The protocol rewrite

Greenfield rewrite of the post-`string-diagram-solver` arc (base: `f71a2381`), built
statement-first. Reference material: `spike-pov-tower` (example, observables),
`spike-pov-dp`/`spike-dp`/`spike-elgot` (the Dₚ/machine layer, M2), `sfunm-setoid`
(proof techniques only). The five structural differences from the reference arc:

1. **Protocols are the spine; machines are a semantics functor.** Everything
   example-facing lives in plain Agda (`Protocol`, `_∘ᵖ_`, `Pr`/`PrHit`); the machine
   category appears once, behind `morphism`/`morphism-∘`/`Pr-agree` (M2).
2. **The machine layer is built once, over Dₚ, G-construction verbatim** — no clocks,
   no budget towers, no `Stabilizes` (M2).
3. **One hom-equality** (simulation zigzag) from the start (M2).
4. **The UC layer typed against its intended model from birth** — `Iface` objects, no
   `HomTransportTrivial`, indexed family category (M3).
5. **Every layer has one entry point** — `ProbabilisticLogic.Prelude` now;
   `Protocol`+`Observe` are the consumer surface of layer 1.

## Status

| milestone | status |
|---|---|
| M1: layers 0–1 + the ledger example | **DONE** — all green, pins by `refl`, hatches 21 = baseline |
| M2 wave 1: `Dₚ`, `Kl(Dₚ)`, `Mealy` + `Mealy-Category` + the ⊕-trace | **DONE** — all green, hatches 21 = baseline |
| M2 wave 2: the four residual trace laws, `Traced`, GConstruction, `morphism`/`Pr-agree` | not started |
| M3: the UC layer | not started |

## Modules (M1: 10 files, 795 LOC, all `--safe --without-K`)

| module | LOC | role |
|---|---|---|
| `ProbabilisticLogic.Prelude` | 33 | the probability vocabulary, one import |
| `…RationalDist.Advantage` | 38 | `adv⊥` pseudometric (ported; base lacked it) |
| `CategoricalCrypto.Iface` | 22 | interfaces `Pos ⇿ Neg`, `unitᴵ`, `_⊗ᴵ_` |
| `CategoricalCrypto.Strategy` | 33 | strategies with the `coin` node; `asks≤` (coins free) |
| `CategoricalCrypto.OracleCall` | 40 | the plain zero-or-one-call shape (ported) |
| `CategoricalCrypto.Protocol` | 106 | `Calls` trees (`ret`/`call`/`coin`/`dead`), `Protocol`, `wireᵖ`, `_∘ᵖ_`, `uniformVec` |
| `CategoricalCrypto.Protocol.Observe` | 134 | `run`/`Pr`, `hitRun`/`PrHit`, `Bounded`/`BoundedHit`, `_≈adv[_]_`, `transfer` |
| `Examples.ChimericLedger` | 186 | the ledger kernel + `Replay` (computed) |
| `Examples.ChimericLedger.POV` | 172 | oracle/ledger/`Sys = ledger ∘ᵖ oracle`, `POV`, audit gadget, `AtBirthday` |
| `Examples.ChimericLedger.Pin` | 31 | `chimeric-violates ≡ 1ℚ`, `consuming-safe ≡ 0ℚ`, by `refl` |

## What changed vs the reference branches

* **No machines anywhere in M1.** `_∘ᵖ_` grafts call trees by structural recursion —
  the strategy tree bounds every interaction, so `Pr`/`PrHit` are total with no budget,
  level, clock, or stabilization certificate. The reference arc's `Tower/*` (CofinalPower,
  Observe-stabilization, Compose/Relay, System, LiftCall — ~1400 LOC) has no counterpart;
  its role returns in M2 as the agreement theorems (`morphism-∘`, `Pr-agree`).
* **Sampling is syntax.** `Calls`/`Strat` carry a `coin : Dist-ℚ Bool` node (`smpl`
  restricted to a coin — sufficient: finite rational distributions are coin trees, and
  the interpreter needs no new mass-1 proofs since the node carries an honest
  distribution). The oracle's fresh answer is `uniformVec` = one fair coin per bit;
  randomized strategies are first-class from day one.
* **The ledger's validation is sequential** (`checkIns` consumes a shrinking UTxO set,
  `checkWdrls` debits as it checks). The reference kernel checked every entry against
  the ORIGINAL state, so duplicated inputs (counted twice, removed once) and duplicated
  withdrawals (checked against undebited accounts, debited with truncating `∸`) both
  broke preservation of value with no hash collision — `POV inputConsuming` was
  deterministically false there.
* **The birthday target is pinned at a genesis state** (`AtBirthday.genesis a V` — empty
  UTxO set, all value in one account): a fresh hash can collide with a pre-existing
  UTxO key, so an arbitrary `s₀` would add a `q · |s₀|` term to `ε`. General-`s₀` forms
  are kept everywhere else.
* `TrajectoryFromAudit` (trajectory probability ≤ audit-form probability of the
  audit-interleaved strategy) is a stated `Set` with its consumer proved, as in the
  reference; the persistence argument (audit answers are definitionally truthful;
  `total` is non-increasing along valid steps) prices it at ~250–400 LOC — three
  assoc-list inductions (`balance`∘`checkIns`, `balance`∘`unionNew`,
  `acctΣ`∘`checkWdrls`, all lemma-friendly in the sequential form) plus one run
  induction relating `d` to `audited d`.

## M2 wave 1 (21 files, 3379 LOC)

| module | LOC | role |
|---|---|---|
| `ProbabilisticLogic.Dp` | 445 | the biased-coin carrier, `cum`/`Supp`/`uniformize`, `_≼ₚ_`/`_≈ₚ_`, monad laws, bind sandwich, bind congruence |
| `…Dp.Commutative` | 186 | `cum` linear in its test, Fubini at two budgets, `>>=ₚ-comm` |
| `…Dp.Iter` | 250 | `Body`, `iterₚ`, `iterₚ-fix`, the loop sandwich, `iterₚ-cong` |
| `…Dp.Iter.Transfer` | 133 | `iterₚ-transfer` — transfer along a pure simulation |
| `…Dp.Iter.Out` | 171 | `iterₚ-out` — naturality for an *effectful* post-composition |
| `…Dp.Iter.Codiagonal` | 137 | `iterₚ-codiagonal` |
| `…Dp.Elgot` | 82 | `iterₚ-uniform`/`iterₚ-ctx`; the one-import entry to the law set |
| `Categories.Monad.Discrete` | 106 | `DiscreteMonad` — the elementwise commutative-monad interface |
| `Categories.Category.Kleisli.Discrete` | 293 | `Klᴹ` + its symmetric monoidal structure |
| `…Kleisli.Discrete.Distributive` | 74 | `MonoidalDistributiveᵏ` |
| `Categories.Category.Monoidal.Distributive` | 44 | the `MonoidalDistributive` record |
| `…Monoidal.Distributive.Properties` | 68 | `δ-unique`, `δ⇐-i₁/₂`, `⊥-unique` |
| `CategoricalCrypto.Machines.Core` | 164 | `State`, `Machine`, `onL`/`onR`, `_∘ᴹ_`, `_≲_`, `_≈ᴹ_` |
| `…Machines.Frame` | 405 | the point-free coherence library the layer runs on |
| `…Machines.Reassoc` | 95 | the three state-reassociation squares |
| `…Machines.Category` | 81 | `Mealy-Category` |
| `…Machines.Tensor` | 161 | `tstep`, `_⊗ᵉ_`, `⊗ᵉ-resp-≲`, `pureᴹ` + functoriality, `α⇒ᴹ`/`α⇐ᴹ`/`σᴹ` |
| `…Machines.Iteration` | 72 | the `Elgot` hypothesis record |
| `…Machines.Trace` | 263 | `solve`/`traceStep`/`traceᴹ`, `iter-onL`, yanking, vanishing₁, step-level naturality, state extension, `Remaining` |
| `…Machines.Trace.Naturality` | 92 | `trace-∘ˡ`, `trace-∘ʳ` for arbitrary machines |
| `…Machines.Base` | 57 | `Dₚ-DiscreteMonad`, `𝒱ₚ`, `distₚ` — the intended instance |

Cost: the whole machine closure elaborates in ~15 s (`Core`+`Frame`+`Reassoc`+
`Category` 11 s, `Tensor`+`Iteration`+`Trace`+`Naturality` 4 s); each `Dₚ` module
is ~4 s. `Trace.Naturality` is split off `Trace` on the elgot spike's measurement
that the two together cost 397 s against 7 s + 7 s apart, for the same proof term.

### What the simulation equality changed

`_≲_` is a state map `θ : St f ⇒ St g` with `discard g ∘ θ ≈ discard f`,
`θ ∘ point f ≈ point g` and `θ ⊗₁ id ∘ step f ≈ step g ∘ θ ⊗₁ id`; the category's
`_≈_` is `EqClosure _≲_` via `Categories.Category.EquivClosureHelper`.  Because a
simulation is a statement about one *step*, no machine is ever unrolled: the
reference arc's `run`/`eval`, its behavioural `_≈ᵉ_`, and the 2ⁿ-fold
decomposition of a word over two letters that its `⊗ᵉ-resp-≈ᵉ` needed
(`Spike.Distributor`'s second half, ~280 LOC) have no counterpart here, and
`⊗ᵉ-resp-≲` is three lines.  Of `Spike.SlotFrame`'s 1183 LOC only the 405 that
the two state actions actually need were ported; its interface slots, closure
(`cl-*`) machinery and `OneGen`/`compK-slot` interchange serve `run`/`eval` and
the deferred `⊗ᵉ-homomorphism`.

Associativity is the one law the refit made harder rather than easier: its step
obligation factors into three squares saying the action at a leaf of the state
tree survives re-bracketing.  `onR-α` and `onLR-α` are `solve-mor 𝕄` one-liners;
`onL-α` is not, because `onL {Q = Q ⊗₀ R}` crosses the block `σ⇒ {Q ⊗₀ R} {X}`
where the nested form crosses `σ⇒ {Q} {X}` and `σ⇒ {R} {X}` separately and the
normalizer never splits a crossing block, so its hexagon is split by hand
(`σ-splitˡ`/`σ-splitʳ`) and the residue goes to `solveMor!` with the four atomic
crossings named as generators.

### Statement deviations from the spikes

* **`iter-uniform` is stated along an arbitrary state map, not a state iso.**  The
  iso form suffices for every reconciliation the trace laws perform, but the
  simulation equality's congruence for `traceᴹ` needs uniformity along the
  simulation's own state map, which is not invertible.  At `Kl(Dₚ)` *neither* form
  is inhabited as literally stated — an arbitrary Kleisli map is effectful and
  `iterₚ-uniform` transfers along *pure* maps only — so the promotion restricts
  both this field and `_≲_`'s state map to a wide subcategory 𝒫 of pure maps.
  That restriction is wave 2's fourth residual and the only knowingly
  un-inhabited hypothesis in the layer; it is confined to one record field.
* **`Remaining.trace-resp-≲` is asked in generator form** (`f ≲ g → traceᴹ f ≲
  traceᴹ g`), the minimal obligation; the `≈ᴹ` form `GConstruction` wants is
  derived inside the record by `EqClosure`'s `gmap`.
* **`DiscreteMonad` replaces `KleisliTriple (Setoids ℓ ℓ)`** as the base's
  parameter, with commutativity folded in as a field rather than a second
  parameter.  Same hypotheses, repackaged: `Dₚ` cannot supply a setoid-wide
  triple (its `unit` has no congruence at a non-discrete setoid, `≈ₚ`'s tests
  being arbitrary ℚ-valued functions on the carrier), but the construction
  applies its parameter at discrete objects only.
* The `Dₚ` spike's `DpIter.Remaining` record is dropped: all four of its fields
  are now theorems.

### What wave 2 owes

Exactly the four fields of `CategoricalCrypto.Machines.Trace.Remaining`:

| field | statement | route | LOC | risk |
|---|---|---|---|---|
| `trace-resp-≲` | `f ≲ g → traceᴹ A B X f ≲ traceᴹ A B X g` | `iter-uniform` at the simulation's own state map, after restricting both to 𝒫 | net ≈ 0 | MED |
| `vanishing₂` | `traceᴹ A B X (traceᴹ … P (α⇐ᴹ ∘ᴹ f ∘ᴹ α⇒ᴹ)) ≈ᴹ traceᴹ A B (X + P) f` | `iter-cod` + the ⊕-side regrouping of `(B+X)+P` under `δ` | 120–200 | MED |
| `superposing` | `traceᴹ (P + A) (P + B) X (α⇐ᴹ ∘ᴹ (idᴹ ⊗ᵉ f) ∘ᴹ α⇒ᴹ) ≈ᴹ (idᴹ ⊗ᵉ traceᴹ A B X f)` | `iter-ctx` / the derived `iter-onL` + ⊕ bookkeeping | 100–160 | MED |
| `trace-comm` | `traceᴹ A B X (traceᴹ … P f) ≈ᴹ traceᴹ A B P (traceᴹ … X (βᴹ ∘ᴹ f ∘ᴹ βᴹ))` | `iter-cod` + `iter-uniform` at the ⊕-side swap | 200–320 | MED–HIGH |

and, beyond the record, four things the wave-1 deliverable deliberately stops
short of:

* **The 𝒫 restriction** (above): a wide subcategory of state maps, closed under
  `id`/`∘`/`⊗₁` and containing the structural morphisms, threaded through `_≲_`
  and `iter-uniform`.  Mechanically a one-field addition to `_≲_` plus one extra
  argument at the ~12 simulation sites.
* **`Elgot` at `Kl(Dₚ)`** — the elementwise-to-point-free translation.  `Dₚ`
  proves all six fields elementwise up to `_≈ₚ_`; each point-free field differs
  from its witness by a bounded, statically known number of junction delays,
  which `_≈ₚ_` absorbs but which have to be written.  250–450 LOC, MED, largest
  non-inherited row; the risk is concentrated in `iter-fix`, where `δ⇐`'s two
  `Dₚ`-junctions have to be matched against `contᵢ`'s one.
* **The machine SMC bundle** — `triangleᴹ`/`pentagonᴹ`/`hexagonᴹ`, the unitor,
  associator and braiding naturalities, `⊗ᵉ-homomorphism`, hence `Monoidal` and
  `Symmetric` for `Mealy-Category`.  All of them are `pureᴹ`-conjugations of a
  base coherence law, which is why `pureᴹ-cong`/`pureᴹ-id`/`pureᴹ-∘`/`⊗ᵉ-pureᴹ`/
  `pure-∘ˡ`/`pure-∘ʳ` are already proved here; `⊗ᵉ-homomorphism` and
  `assoc-commuteᴹ` additionally want `Ω`, `slot-comm` and `tstep-α`, which is why
  `Ω`/`tuck`/`untuck` are not in `Machines.Core` yet.
* **`Monoidal (GConstruction C)`** — inherited, unchanged, 300–600 LOC HIGH.

### Assumption ledger of M2 wave 1

Two explicitly parameterized records and nothing else: `Machines.Iteration.Elgot`
(the base's iteration, with the deviation above) and `Machines.Trace.Remaining`
(the four laws).  Every term in every module is total; zero postulates, zero
`TERMINATING`, zero holes; whole-`src` hatch grep 21 before and after.

### Unrelated branch defect found on the way

`src/Categories/PermuteCoherence/Unflatten.agda:22` does not typecheck
(`UnsolvedMetaVariables`): commit `2c638829`'s `using`-list cleanup removed both
`open import Level using (Level)` and the module's `{ℓ′ : Level}` binder, and
`FreeMonoidalData` takes that level explicitly.  This breaks the whole
APROP/hypergraph closure, so `Categories.Coherence.Symmetric` (`solveH!`,
`rewriteH!`, `rewriteDeep*!`, `normalize*!`) is unusable on this branch.  Not
touched here — a one-line restoration under `src/Categories/`, flagged for the
maintainer.  It is why `onL-α` went to `solveMor!` rather than the symmetric
solver.

## M3 pointers

M3 harvests: `sfunm-setoid`'s ℰᵗᵛ/StandardTV statements, the α query-bound +
counting theorem, restated over `Iface` with the ancilla parameterized (no K
island). Assumption ledger of M1: `ser`(+`ser-inj` at `AtBirthday`) — module
parameters, maintainer-sanctioned; zero postulates.
