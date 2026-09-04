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
| M2 wave 2: the four residual trace laws + `Elgot` at `Kl(Dₚ)` | **DONE** — the machine layer is hypothesis-free; hatches 21 = baseline |
| M2 wave 3: the machine SMC bundle, `Traced`, GConstruction, `morphism`/`Pr-agree` | **the machine layer is DONE** — `ℳₚ` symmetric monoidal, `Tracedₚ`, `𝒢ₚ` all closed terms; `morphism` landed, `Morphism-∘`/`PrAgree` stated and priced; hatches 21 = baseline |
| M3: the UC layer | **the statement layer is DONE** — `_≈ℰ_`/`grade-stable`/`absorb`/`_≤UC_` and its metatheorems are theorems, no K island, no `HomTransportTrivial`; the intended instance's observation is a theorem and its grading action is data with `Grading 𝒫ᴵ` priced; hatches 21 = baseline |

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

## M2: the machine layer (30 files, 4567 LOC, all `--safe --without-K`)

| module | LOC | role |
|---|---|---|
| `ProbabilisticLogic.Dp` | 445 | the biased-coin carrier, `cum`/`Supp`/`uniformize`, `_≼ₚ_`/`_≈ₚ_`, monad laws, bind sandwich, bind congruence |
| `…Dp.Commutative` | 186 | `cum` linear in its test, Fubini at two budgets, `>>=ₚ-comm` |
| `…Dp.Iter` | 250 | `Body`, `iterₚ`, `iterₚ-fix`, the loop sandwich, `iterₚ-cong` |
| `…Dp.Iter.Transfer` | 133 | `iterₚ-transfer` — transfer along a pure reindexing of state, loop variable and output |
| `…Dp.Iter.Out` | 171 | `iterₚ-out` — naturality for an *effectful* post-composition |
| `…Dp.Iter.Codiagonal` | 137 | `iterₚ-codiagonal` |
| `…Dp.Elgot` | 82 | `iterₚ-uniform`/`iterₚ-ctx`; the one-import entry to the law set |
| `Categories.Monad.Discrete` | 106 | `DiscreteMonad` — the elementwise commutative-monad interface |
| `Categories.Category.Kleisli.Discrete` | 293 | `Klᴹ` + its symmetric monoidal structure |
| `…Kleisli.Discrete.Distributive` | 74 | `MonoidalDistributiveᵏ` |
| `…Kleisli.Discrete.Pure` | 78 | `IsPure` + `PureSubᵏ` — the pure homs of `Klᴹ` |
| `Categories.Category.Monoidal.Distributive` | 44 | the `MonoidalDistributive` record |
| `…Monoidal.Distributive.Properties` | 62 | `δ-unique`, `δ⇐-i₁/₂`, `⊥-unique` |
| `Categories.Category.Monoidal.Pure` | 45 | the `PureSub` record — a wide symmetric monoidal subcategory |
| `Categories.Category.Cocartesian.Ext` | 68 | the coproduct associator and braiding on the injections, `+₁-id`, `+-unique₂` |
| `CategoricalCrypto.Machines.Core` | 100 | `State`, `Machine`, `onL`/`onR`, `_∘ᴹ_` |
| `…Machines.Sim` | 117 | `_≲_`, `_≈ᴹ_` and its combinators, `collapseˡ`/`collapseʳ` |
| `…Machines.Frame` | 392 | the point-free coherence library the layer runs on |
| `…Machines.Reassoc` | 95 | the three state-reassociation squares |
| `…Machines.Category` | 90 | `Mealy-Category`, `∘ᴹ-resp-≈ᴹ` |
| `…Machines.Tensor` | 174 | `tstep`, `_⊗ᵉ_`, `⊗ᵉ-resp-≲`/`⊗ᵉ-resp-≈ᴹ`, `pureᴹ` + functoriality, `α⇒ᴹ`/`α⇐ᴹ`/`σᴹ` |
| `…Machines.Iteration` | 113 | the `Elgot` hypothesis record, `tstep-pad`, the derived `iter-uniform`/`pure-+₁` |
| `…Machines.Trace` | 267 | `solve`/`traceStep`/`traceᴹ`, `iter-onL`, yanking, vanishing₁, step-level naturality, state extension, `Remaining` |
| `…Machines.Trace.Naturality` | 97 | `trace-∘ˡ`, `trace-∘ʳ` for arbitrary machines |
| `…Machines.Trace.Congruence` | 80 | `trace-resp-≲`, `trace-resp-≈ᴹ` |
| `…Machines.Trace.Superposing` | 119 | `superposing`, `super-step` |
| `…Machines.Trace.Vanishing` | 256 | `vanishing₂`, `vanish-step`, `[]-δ⇐` |
| `…Machines.Trace.Fubini` | 202 | `trace-comm`, `relabel-step`, `β+` |
| `…Machines.Trace.Laws` | 39 | `Remaining`, as a term |
| `…Machines.Base` | 281 | `Dₚ-DiscreteMonad`, `𝒱ₚ`, `distₚ`, `𝒫ₚ`, `Elgotₚ`, `Remainingₚ`, `ℳₚ`, `Tracedₚ`, `𝒢ₚ` — the intended instance, hypothesis-free |

Cost: the whole machine closure elaborates in ~40 s; no module is over 8 s warm
and each `Dₚ` module is ~4 s.  `Trace.Naturality` is split off `Trace` on the
elgot spike's measurement that the two together cost 397 s against 7 s + 7 s
apart, for the same proof term; the four law modules are split for the same
reason and each came in at 7–8 s.

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

* **Uniformity is asked in TRANSFER form, and along `𝒫` only** (see the wave-2
  section below).  The spikes asked for uniformity along a state *iso*; that is
  both too weak (it cannot carry the trace congruence, whose state map is not
  invertible) and, at a Kleisli base, uninhabited (an arbitrary hom is
  effectful).
* **`Remaining.trace-resp-≲` is asked in generator form** (`f ≲ g → traceᴹ f ≲
  traceᴹ g`), the minimal obligation; the `≈ᴹ` form `GConstruction` wants is
  derived by `EqClosure`'s `gmap` (`Trace.Congruence.trace-resp-≈ᴹ`).
* **`DiscreteMonad` replaces `KleisliTriple (Setoids ℓ ℓ)`** as the base's
  parameter, with commutativity folded in as a field rather than a second
  parameter.  Same hypotheses, repackaged: `Dₚ` cannot supply a setoid-wide
  triple (its `unit` has no congruence at a non-discrete setoid, `≈ₚ`'s tests
  being arbitrary ℚ-valued functions on the carrier), but the construction
  applies its parameter at discrete objects only.
* The `Dₚ` spike's `DpIter.Remaining` record is dropped: all four of its fields
  are now theorems.

## M2 wave 2

All four residual trace laws are theorems and `Elgot` is inhabited at `Kl(Dₚ)`,
so the machine layer has no hypothesis left: `Machines.Base.Remainingₚ` is a
closed term of `Trace.Remaining (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ) (Elgotₚ ℓ)`.

| deliverable | LOC (est → real) | verdict |
|---|---|---|
| the 𝒫 restriction | ≈0 → 240 new + 8 files retouched | landed as `PureSub`; grew, see below |
| `Elgot` at `Kl(Dₚ)` | 250–450 → 197 | landed; `Machines.Base` 63 → 260 |
| `trace-resp-≲` | ≈0 → 80 | `iter-uniform` at the simulation's own state map, exactly as predicted |
| `superposing` | 100–160 → 119 | `iter-out` only — *not* `iter-ctx`; `traceStep-onR` already absorbs the context |
| `vanishing₂` | 120–200 → 256 | `iter-cod` + **two `iter-transfer`s**; the estimate missed that this law moves the loop variable |
| `trace-comm` | 200–320 → 202 | `vanishing₂` twice + one loop-variable relabelling; the predicted `Dp.Commutative` Fubini was *not* needed |

### The 𝒫 design, as landed

`Categories.Category.Monoidal.Pure.PureSub` is a predicate `Pure : A ⇒ B → Set
(ℓ ⊔ e)` on the morphisms of `𝒱`, closed under `≈`, `id`, `_∘_`, `_⊗₁_` and
containing `λ⇒`/`ρ⇒`/`α⇒`/`σ⇒`.  Its level is fixed at `ℓ ⊔ e` rather than being
a parameter, which is what keeps every hom-set level of the layer unchanged; the
intended instance's purity lands there.  `_≲_` gains one field,

    record _≲_ {A B : Obj} (f g : Machine A B) : Set (ℓ ⊔ e) where
      field
        θ         : St f ⇒ St g
        θ-pure    : Pure θ
        θ-discard : discard (state g) ∘ θ ≈ discard (state f)
        θ-point   : θ ∘ point (state f) ≈ point (state g)
        θ-step    : θ ⊗₁ id ∘ step f ≈ step g ∘ θ ⊗₁ id

and the iteration hypothesis is asked in **transfer** form rather than the
state-only form wave 1 wrote:

    iter-transfer : {S T A A′ B B′ : Obj}
                    (κ : S ⊗₀ A ⇒ T ⊗₀ A′) (μ : S ⊗₀ B ⇒ T ⊗₀ B′) → Pure κ → Pure μ
                  → {u : S ⊗₀ A ⇒ S ⊗₀ (B + A)} {v : T ⊗₀ A′ ⇒ T ⊗₀ (B′ + A′)}
                  → v ∘ κ ≈ tstep μ κ ∘ u → iter v ∘ κ ≈ μ ∘ iter u

    iter-uniform : {S T A B : Obj} {u : S ⊗₀ A ⇒ S ⊗₀ (B + A)} (θ : S ⇒ T) → Pure θ
                 → {v : T ⊗₀ A ⇒ T ⊗₀ (B + A)}
                 → v ∘ pad θ ≈ pad θ ∘ u → iter v ∘ pad θ ≈ pad θ ∘ iter u

`iter-uniform` is now *derived* (κ = μ = `pad θ`, off `tstep-pad`: the
distributor is natural in the state).  Three things forced the transfer form:

* it is what the instance proves — `Dp.Iter.Transfer.iterₚ-transfer` is the
  primitive there and `iterₚ-uniform` its corollary, so the strong field is
  *cheaper* (27 lines) than the weak one would have been;
* `vanishing₂` and `trace-comm` relate a loop over `X + P` to nested loops over
  `X` and `P`, which **moves the loop variable**; no state-only uniformity can
  do that, and this is the one place the wave-1 route table was wrong;
* it makes `tstep`'s codomain state free, which is the same `δ⇒ ∘ (μ +₁ κ) ∘ δ⇐`
  the tensor already used.

Because a loop-variable transfer is built from `i₁`/`i₂`/`[_,_]`, the pure class
must contain the coproduct structure.  `PureSub` is stated over `𝒱` alone and
cannot say so, so `Elgot` carries `pure-i₁`, `pure-i₂`, `pure-[]` as fields and
derives `pure-+₁` from them; at `Kl(Dₚ)` all three are one-liners.

`Machines.Sim` is a new module holding `_≲_`/`_≈ᴹ_`/`collapseˡ`/`collapseʳ`: the
simulation equality is the only thing that needs 𝒫, and splitting it out of
`Machines.Core` keeps the two coherence-only modules (`Frame`, `Reassoc`) free of
the parameter.

### How the four laws go

* **`trace-resp-≲`** — `δ-unique` peels the dispatch off `solve`, `pad-transport`
  slides the state map past every action on the interface alone, and the loop is
  carried by `iter-uniform` at the simulation's own `θ`.  Nothing else.
* **`superposing`** — `pure-∘ˡ`/`pure-∘ʳ` reconcile the argument onto `state f`,
  `traceStep-onR` moves the context factor out, and the residue is a `δ-unique`
  whose loop branch is one `iter-out` at `id ⊗₁ i₂` (relabelling the exit branch
  by `i₂ : B ⇒ P + B`).  `iter-ctx` is spent only indirectly, inside
  `traceStep-onR`.
* **`vanishing₂`** — the hard one, and the one the wave-1 estimate under-priced.
  With `b` the `X + P`-loop's body, `c = id ⊗₁ α+⇐ ∘ b`, `q` the `P`-loop applied
  to `c`, `ν = id +₁ i₁` and `ψ = (ν +₁ i₂) ∘ α+⇐`, the proof is:
  `iter (id ⊗₁ ψ ∘ b) ≈ id ⊗₁ ν ∘ q` (one `iter-transfer` at `id ⊗₁ i₂` for the
  `P`-entries, `iter-fix` + `[]-δ⇐` for the `X`-entries), then `iter-cod` at
  `id ⊗₁ ψ ∘ b` — whose codiagonal collapses `ψ` to the identity, because
  `[ id , i₂ ] ∘ (ν +₁ i₂) ≈ α+⇒`.  That normalizes the `X + P`-loop to one whose
  loop branch only ever produces `X`, and a second `iter-transfer` at `id ⊗₁ i₁`
  splits it into the two nested loops.
* **`trace-comm`** — no new iteration content.  `vanishing₂` fuses each side into
  a single trace (over `X + P` on the left, `P + X` on the right), and the two
  are related by `relabel-step`: a trace does not see a pure iso of its loop
  variable, one `iter-transfer` at `id ⊗₁ +-swap`.  Recognizing `βᴹ` as the pure
  machine of `β+ = α+⇐ ∘ (id +₁ +-swap) ∘ α+⇒` is what makes the fusions'
  associators cancel against `βᴹ`'s own, leaving `+-swap` alone.  The wave-1
  table's guess that `Dp.Commutative`'s Fubini might reappear here was wrong: it
  does not.

`Categories.Category.Cocartesian.Ext` collects the ⊕-side bookkeeping all four
laws do: upstream builds `+-monoidal` by dualizing `-×-`, so its associator is a
nest of `[_,_]`s and every injection equation is `inject₁`/`inject₂`.  `+₁-id`
and `+-unique₂` moved there from `Monoidal.Distributive.Properties`, whose
distributivity they never needed.

### What wave 3 owed

* **The machine SMC bundle** — done, and the estimate that every law is a
  `pureᴹ`-conjugation of a base coherence law held: `Tensor.Structural` is 219
  lines and `Tensor.Assoc` 219, against ~750 for the same content over the
  behavioural equality on `ro-model`.  `Ω`/`tuck`/`untuck` were **not** needed
  after all — see the `⊗-split` note below.
* **`Mealy-Traced` and `GConstruction`** — done, two record literals as
  predicted, and **zero hypotheses survive**.
* **`Monoidal (GConstruction C)`** — the embedding layer landed; the
  `⊗`-homomorphism wall is still open, priced below.
* **`morphism`/`morphism-∘`/`Pr-agree`** — `morphism` landed; the two agreement
  theorems are stated as types (no postulate, no hole) and priced below.

## M2 wave 3 (11 new/changed files, +1213 LOC)

| module | LOC | role |
|---|---|---|
| `…Machines.Tensor` (+8) | 174 | `⊗ᵉ-resp-≈ᴹ`, the `EqClosure` lift of `⊗ᵉ-resp-≲` |
| `…Machines.Tensor.Structural` | 219 | `tstep-∘`, `λ⇒ᴹ`/`ρ⇒ᴹ`, the six iso laws, `triangleᴹ`/`pentagonᴹ`/`hexagonᴹ`, unitor and braiding naturality, the two one-sided collapses |
| `…Machines.Tensor.Assoc` | 219 | `⊗-split`/`⊗-split′`, `⊗ᵉ-homomorphism`, `tstep-α`, `assoc-commuteᴹ` |
| `…Machines.Bundle` | 82 | `⊗ᴹ`, `Mealy-Monoidal`, `Mealy-Symmetric`, `Mealy-SymmetricMonoidal` |
| `…Machines.G` | 56 | `Mealy-Traced`, `Mealy-G` — `GConstruction` instantiated unchanged |
| `…Machines.Base` (+21) | 281 | `ℳₚ`, `Tracedₚ`, `𝒢ₚ`: the closed instances |
| `Categories.GConstructionEmbedding` | 157 | harvested: `⌜_,_⌝`, `absorbˡ`/`absorbʳ`, `⌜⌝-∘`, `⌜⌝-≅`, `unitorˡᴳ`/`unitorʳᴳ`/`associatorᴳ` |
| `…GConstructionEmbeddingCoherence` | 173 | harvested: the two absorption coherence obligations, APROP-solved |
| `ProbabilisticLogic.Dp.Coin` | 74 | `coinₚ` — a `Dist-ℚ Bool` as one biased coin — and `coinₚ-cum` |
| `CategoricalCrypto.Protocol.Machine` | 131 | `⟦_⟧ᴵ`, `MSt`, `drive`, `morphism`, `runᴹ`, `Morphism-∘`, `PrAgree` |
| `…Protocol.Machine.Pin` | 73 | layer 1 and the machine image agree by `refl` |

Cost: every module is a warm single-module check of 5–16 s; the whole
`Machines.G` closure from cold (including `GConstruction*`) is 37 s.

### The bundle, as landed

Every coherence law is its `+`-monoidal instance conjugated by `pureᴹ`, exactly
as wave 2 predicted, and the two structural lemmas that carry it are

    ⊗ᵉ-pureˡ : (idᴹ {A} ⊗ᵉ pureᴹ h) ≲ pureᴹ (id +₁ h)
    ⊗ᵉ-pureʳ : (pureᴹ h ⊗ᵉ idᴹ {C}) ≲ pureᴹ (h +₁ id)

so `triangleᴹ`, `pentagonᴹ` and `hexagonᴹ` are one `pureᴹ-cong` at `⊕.triangle`,
`⊕.pentagon` and `⊕Br.hexagon₁` each.  The unitor naturalities hold because
`X ⊗₀ ⊥` is initial (`⊥-unique`), so the summand that would carry the other
machine cannot fire; the braiding's is `σ-onL`/`σ-onR` (the state braiding
exchanges the two state actions) against `tstep-swap` (the interface swap
exchanges the two arms).

The two laws wave 2 flagged as wanting `Ω`/`slot-comm` — `⊗ᵉ-homomorphism` and
`assoc-commuteᴹ` — did **not**.  `⊗-split` (`f ⊗ᵉ g ≈ᴹ (f ⊗ᵉ id) ∘ᴹ (id ⊗ᵉ g)`)
is the whole trick: both sides pair the same two states up to the unitors the
one-sided halves contribute, so its step obligation is one `tstep-∘` plus
`tstep-sim` on the two collapses, and afterwards every homomorphism is
one-sided, where `⊗idᵉ-collapse` erases the trivial state factor and no state
tree is ever re-bracketed.  Associator naturality then holds one generator at a
time (`natˡ`/`natᶜ`/`natʳ`), each of which is `pure-∘ˡ`/`pure-∘ʳ` around a
single `tstep-α`.  The 280 LOC of word-splitting `ro-model` needed for
`⊗ᵉ-resp-≈ᵉ` (`Spike.Distributor`'s second half) has no counterpart: at the
simulation equality the congruence is `⊗ᵉ-resp-≲`, three lines, and its
`EqClosure` lift is four more.

### Task 3: `Monoidal (GConstruction C)` — what remains

`Categories.GConstructionEmbedding{,Coherence}` transfer verbatim (the
`GConstruction*` modules are byte-identical on both branches) and add **no**
trace hypothesis: the four `GConstruction` already takes are enough, and at the
machine layer all four are terms, so nothing on the instance side is at risk.
`⌜ u , v ⌝ = σ⇒ ∘ u ⊗₁ v`, `absorbˡ`/`absorbʳ`, `⌜⌝-∘`, `⌜⌝-≅` and hence
`unitorˡᴳ`/`unitorʳᴳ`/`associatorᴳ` as `𝒢`-isos are all available (12.3 s over
the existing solver closure).

What is missing is the bifunctor.  With
`(A⁺,A⁻) ⊗ᴳ (B⁺,B⁻) = (A⁺ ⊗₀ B⁺ , A⁻ ⊗₀ B⁻)`, `unitᴳ = (I , I)` and
`f ⊗₁ᴳ g = w⁻ ∘ f ⊗₁ g ∘ w` for the two middle-four interchanges `w`, `w⁻`
(no trace), the residue is, in dependency order:

1. `⌜⌝-⊗ : ⌜u,v⌝ ⊗₁ᴳ ⌜p,q⌝ ≈ ⌜ u ⊗₁ p , v ⊗₁ q ⌝`.  A 4-generator symmetric
   coherence whose `σ⇒` sits at the **compound** objects `A⁺ ⊗₀ C⁺` and
   `B⁻ ⊗₀ D⁻`, and the normalizer never splits a crossing block
   (`Coherence.Monoidal.Test.Limitations.lim-hexagon`) — so it needs the
   hand-split `solveMor!` treatment `Machines.Reassoc.onL-α` uses, ~40–60 LOC.
2. `identity`, `triangle`, `pentagon`, `unitor*-commute`, `assoc-commute`: each
   is (1) + `⌜⌝-∘` + `absorbˡ`/`absorbʳ` transporting the base law; the two
   commute laws become 1-generator base solves once absorbed.
3. `homomorphism : (f′ ∘ᴳ f) ⊗₁ᴳ (g′ ∘ᴳ g) ≈ (f′ ⊗₁ᴳ g′) ∘ᴳ (f ⊗₁ᴳ g)` — the
   gate, since `Monoidal`'s `⊗` is a `Bifunctor` and nothing above assembles
   without it.  Route: `superposing` + `right-superposing` + `trace-∘ˡ/ʳ` +
   `trace-comm` fuse `trace ⊗ trace` into a double trace, then one coherence
   step over 8 atoms / 4 generators; splitting by
   `f ⊗ᴳ g = (f ⊗ᴳ id) ∘ᴳ (id ⊗ᴳ g)` cuts each half to 2 generators.
   `GConstruction`'s `right-superposing`, `trace-βyank` and `trace-gyank` are
   `where`-local to its `categoryHelper` literal and have to be lifted out or
   re-derived; the `RS` coherence they rest on *is* exported, from
   `GConstructionIdentityCoherence`.

`Braided`/`Symmetric` on `𝒢` is not needed downstream.

### Task 4: the semantics functor

An interface is a **pair** of objects and a protocol is a machine on the sum of
the two polarities — which is exactly a `GConstruction` hom, since
`(A⁺,A⁻) ⇒𝒢 (B⁺,B⁻)` unfolds to `Machine (A⁺ + B⁻) (A⁻ + B⁺)`.  So

    ⟦_⟧ᴵ    : Iface → Category.Obj (𝒢ₚ 0ℓ)
    ⟦ A ⟧ᴵ  = Pos A , Neg A

    morphism : Protocol A B → 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]

typechecks with no coercion, and no `Monoidal` structure on `𝒢` is used — the
seam task 3 leaves open is not in the way (`⟦_⟧ᴵ` is monoidal only *if* task 3
lands, which is what M3 will want for `_⊗ᴵ_`).

A protocol step makes finitely many calls, which a Mealy step cannot, so each
call is one activation and the pending continuation is state:

    data MSt : Set where
      idle : St P → MSt
      wait : (Pos A → Calls A (St P × Pos B)) → MSt

    drive : Calls A (St P × Pos B) → Dₚ (MSt × (Neg A ⊎ Pos B))

`drive` is **structural recursion on `Calls`** — the tree is inductive, so no
iteration, clock or fuel appears here either.  `coin` becomes one biased-coin
step (`coinₚ`, the new `Dp.Coin`), `dead` becomes `botₚ`, whose mass `cum` never
counts.

`Machine.Pin` computes both verdicts at a coin-flipping protocol and gets the
same rational by `refl`, before and after one `_∘ᵖ_` (which exercises
`graft`/`serve` and `drive` on a `call` node).

#### Finding: `morphism` preserves composites, not identities

`𝒢.id` is `σ⇒`, a **stateless** forwarder that accepts `inj₁ a⁺` at any time.
`morphism wireᵖ` demands a query first: at `(idle tt , inj₁ a⁺)` the two steps
are `botₚ` and `returnₚ (tt , inj₂ a⁺)`, so neither simulates the other.
`wireᵖ` is the *sequential* wire, and divergence on an unasked-for answer is
forced for a general protocol — `Pos A` and `Pos B` are different types, so
there is nothing to forward.  Layer 1 states no identity law (M1 has `_∘ᵖ_` and
no `Protocol` category), so nothing breaks; but a *functor* out of protocols
would have to land in a subcategory of `𝒢`, or restrict to on-protocol
environments.  Recording this is the point of the seam.

#### The two agreement theorems, stated and priced

Both are types in `Protocol.Machine`, so their shapes are certified; neither is
postulated.

    Morphism-∘ = (P₂ : Protocol B C) (P₁ : Protocol A B)
               → 𝒢ₚ 0ℓ [ morphism (P₂ ∘ᵖ P₁) ≈ morphism P₂ 𝒢.∘ morphism P₁ ]

**Price 300–500 LOC, one module.**  The direction that has a witness is
`morphism P₂ ∘𝒢 morphism P₁ ≲ morphism (P₂ ∘ᵖ P₁)`: the state map
`⊤ × ((MSt P₂ × MSt P₁) × ⊤) → MSt (P₂ ∘ᵖ P₁)` grafts the two pending
continuations with `serve`, and being a function it is `Pure` for free.  The
reverse direction has **no** state map — a grafted `wait` continuation does not
decompose — which is a second reason the equality has to be the equivalence
closure.  The step square is an `iter-fix` unrolling: `_∘ᵖ_`'s `graft`/`serve`
mutual recursion *is* the loop the ⊕-trace's `iter` performs, one internal
`B`-message per pass, so the proof is an induction on `P₂`'s call tree against
`solve-loop`.  Two cheap prerequisites: `graft`/`serve` are `private` inside
`_∘ᵖ_` and must be exported, and `GConstruction`'s `α`/`γ` have to be absorbed
(that is what `absorbˡ`/`absorbʳ` from task 3's embedding layer are for).

    PrAgree = (P : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B))
            → Σ[ n ∈ ℕ ] ((m : ℕ) → cum (n + m) (runᴹ (morphism P) d) bool→ℚ
                                  ≡ Pr P d)

**Price 250–450 LOC, two modules.**  `runᴹ` (the minimal closed-machine run,
against any machine of the closed shape) is landed, so only the theorem is
open.  It factors as (i) `drive` agrees with `Observe.evalC` at the `cum` level,
by induction on `Calls` with `coinₚ-cum` (landed) at each coin node, and (ii)
induction on the `Strat` tree threading the budget.  The one piece of real work
is (i)'s bind step: `Dist⊥`'s bind splices lists while `Dₚ`'s builds a coin
tree, so agreement needs `cum` of a bind factored as an expectation of `cum`s —
`Dp` has the exact `cum`/bind identities and `Dp.Commutative` has `cum` linear
in its test, so the ingredients are there.  A cheaper and more reusable route
is a general embedding `Dist⊥ X → Dₚ X` with a `cum` agreement and a
monad-morphism law up to `≈ₚ`; that is the missing link between the two
probability carriers in the repo (`Dp`'s header asserts it exists but nothing
proves it), and it makes `PrAgree` an induction on `Strat` alone.

`Morphism-∘` cannot be pinned by computation, and that is measured: `cum n`
expands `2ⁿ` branches, while `𝒢`'s point-free composite spends one delay
junction per structural morphism of `α`, `γ`, two `∘ᴹ` towers and the trace's
`iter` — several dozen.  At `n = 16` (16 s of normalization) the composite's
mass has not reached a value at all.

### Assumption ledger

Empty.  Every term in every module of M2 is total; zero postulates, zero
`TERMINATING`, zero holes; whole-`src` hatch grep 21 before and after (the M1
baseline).  `Machines.Iteration.Elgot` and `Machines.Trace.Remaining` are still
module *parameters* of the generic layer — that is what keeps it generic — and
both are discharged at the intended base in `Machines.Base`, where `ℳₚ`,
`Tracedₚ` and `𝒢ₚ` are closed terms.

`Morphism-∘` and `PrAgree` (`Protocol.Machine`) are stated `Set`s with nothing
inhabiting them — the `TrajectoryFromAudit` pattern: the statement is certified
to typecheck against the real definitions, and it is not assumed anywhere.

Two shape seams are open and neither is load-bearing today:

* `⟦ unitᴵ ⟧ᴵ` is `(Data.Empty.⊥ , Data.Empty.⊥)` while `Mealy-Monoidal`'s unit
  is `Data.Empty.Polymorphic.⊥` — isomorphic, not identical.  It bites only when
  M3 wants `⟦_⟧ᴵ` monoidal, and the cure is the `Iface`-polymorphism M3 plans
  anyway.
* `Monoidal (GConstruction C)` is still absent, so `⟦_⟧ᴵ` is a map of objects
  and `morphism` a map of homs, against the bare `Category`.

### Solver use

`onL-α` (`Machines.Reassoc`) is the layer's only solver call, and it goes to
`solveMor!` with the four atomic crossings named as generators; `solve-mor`, the
macro, is weaker on goals mixing `α`/`σ` with compound endpoints.  A solver call
gets its own ascribed lemma — never inlined in a `_○_` chain — which is what
keeps the surrounding chain's endpoints inferable.  (Wave 1 recorded the
symmetric solver as unusable here because
`Categories/PermuteCoherence/Unflatten.agda` had lost its level binder; commit
`b746517c` restored it, so `solveH!`/`rewriteH!` are available again — no law in
this layer needed them.)

## M3: the UC layer (11 files, 1513 LOC)

| module | LOC | role |
|---|---|---|
| `ProbabilisticLogic.Dp.Advantage` | 107 | `Pr≤`, `_≼ₚ[_]_`/`_≈ₚ[_]_` — advantage as an ε-indexed relation, with the pseudometric laws |
| `CategoricalCrypto.UC.Base` | 156 | `Grading`, `Budget`, `Observation`, `UCBase`; the derived agreement `_∼_` and its ε/2 equivalence |
| `…UC.Environment` | 173 | `SameTV` (ancilla a parameter), `Tests`, `ℰᵗᵛ`, `_≈ℰ_`, its congruences, `grade-stable`, `_≈ℰ[_]_`, `absorbᵘ` |
| `…UC.Emulation` | 88 | `_≤UC_`, `_≤UC⁺_`, `≤UC-refl`/`≤UC-trans`/`dummy-complete`/`≤UC⁺⇒≤UC`, `_⊙_`, `_⊛₁_`, `UC-compose` (stated) |
| `…UC.Family` | 189 | `𝒞^ω` at a parameterized index, `PolyQB`, `Fam`, `Grading^ω`, `Observation^ω`, `UCBase^ω`, `_≈ℰ[_]_`, `VanishingBound`, `absorb` |
| `…UC.Machine` | 219 | `Proc`, `𝒫ᴵ`, `wireStep`/`wireᴹ`, `Ωᴵ`, `⟦_⟧ᴼ`, `Observationᴹ`, `T₁ᴵ`/`subᴵ`/`a⇒ᴵ`/`a⇐ᴵ`, `GradingLawsᴹ`, `UCBaseᴹ` |
| `…UC.Machine.Run` | 157 | `step-sim`, `point-sim`, `run-sim`, `runᴹ-resp-≈ᴹ` — a simulation is invisible to a closed run |
| `…UC.QueryBound` | 265 | `Below`/`AtMost`/`Ans`/`forget`, `QBᵢ`, `qbᵢ-mono`, `traceᵍ`/`behᵍ`, `CountBound`, `Counting` (stated), `qbᵢ-wire`, `Certified`, `QB`, `qb-resp-≈`, `qb-mono`, `BudgetLawsᴹ` (stated) |
| `…UC.Bridge` | 77 | `λᴵ⇐`, `conjᴵ`, `ctxRun`, `Reflects` (stated) |
| `…UC.Seam` | 50 | `AgreeToAdv` (stated), `pov-carry` (proved) |
| `…UC` | 32 | the one entry point |

All `--safe --without-K`; the `Dₚ`-facing six add `--guardedness` and nothing
adds anything else. **There is no K island**, which was the acceptance test.

### The defects the redesign fixes at birth

* **`HomTransportTrivial` never arises.** The reference arc's environment
  carrier was `Σ[ Y ] Test (Y ⊗ A)`, so its agreement constructor forced an
  ancilla equation; a consumer whose scrutinee had a defined function in that
  index could not match it, and routing through a Σ-projection instead handed
  back a loop `Y ≡ Y` that only axiom K can consume.  The hypothesis that
  bought is *refuted* under univalence at its own instance (an `Iface` loop
  from `not : Bool ≃ Bool` permutes the verdict alphabet), and was discharged
  in a two-module K island.  Here `SameTV Y A` is a one-field record at a
  **fixed ancilla**: no equation is generated, `same` is a projection that
  reduces by eta, and `grade-stable` is a theorem whose only input is the
  action's associativity.
* **`_≈ℰ_` is the adaptive single-ancilla relation by definition**, not the
  kernel congruence of a presheaf.  The reference had to *prove* the two equal,
  and that proof (`≈ℰ⇒R`) is the direction that needed the hypothesis.  `ℰᵗᵛ`
  is still built — it is a genuine `Presheaf 𝒞 (Setoids _ _)` for each ancilla
  — and `≈ℰ⇒tv`/`tv⇒≈ℰ` are the identity pair witnessing that the definition is
  its kernel relation ancilla by ancilla.
* **The advantage is a RELATION, not a function.**  `Dₚ`'s termination mass is
  a supremum the layer never forms, so `MachineAxioms.adv : Obs → Obs → ℚ` is
  uninhabited at the intended instance.  `_≈ₚ[ ε ]_` relaxes `_≼ₚ_`'s
  budget-matching by a rational slack instead, and carries exactly the three
  pseudometric laws the vanishing layer spends.  Agreement is then *derived*
  (`x ∼ y = ∀ ε > 0 → x ≈[ ε ] y`) and its transitivity is the ε/2 argument,
  proved once in `UC.Base` rather than once per instance.  This is the
  absorb/ε misfit, closed.
* **`𝒞^ω` takes its index as a parameter** `(Ix , κ : Ix → ℕ)`.  Only three
  things ever needed `ℕ` in the reference: the polynomial's argument, the
  asymptotics' order, and the budget arithmetic, and all three read the index
  through `κ`.  `Ix = ℕ × ℕ`, `κ = proj₁` gives a second axis for free;
  `(ℕ , id)` recovers the reference.
* **Objects are `Iface` everywhere.** `𝒫ᴵ` presents `𝒢ₚ` with interfaces as its
  objects (`⟦_⟧ᴵ` is a bijection on objects), so `_⊗ᴵ_` — layer 0's own
  interface tensor — is the grading action.  No `Channel`, and no raw pair of
  sets, occurs in the layer.
* **The verdict interface is ticked.** `Ωᴵ = Bool ⇿ ⊤`.  A machine is reactive,
  so the reference's `Pos = Bool , Neg = ⊥` verdict can never be activated by a
  closed composite; the tick is the environment's single activation and the
  observation is layer 1's own `runᴹ` at `ask tt out`.
* **The `Reflects` quantifier order is sound.** The reference's applied form put
  `Σ[ d ]` before `∀ u v` with *deterministic* strategies, which is false: a
  context that flips a fair coin and asks one of two questions gets advantage ½
  against two different pairs, while any deterministic one-ask tree scores zero
  against one of them.  Layer 0's `Strat` has carried the coin node since M1, so
  the strong order is available unchanged.

### What is proved, and what is priced

Proved, hypothesis-free: the whole `Dp.Advantage` layer; `UC.Base`'s derived
`_∼_` equivalence; `UC.Environment` in full (`ℰᵗᵛ` a presheaf, `_≈ℰ_` an
equivalence and a congruence, `grade-stable`, `absorbᵘ`); `UC.Emulation`'s four
metatheorems and the equivalence of the plain and dummy-adversary forms;
`UC.Family` in full (`Fam` a category, the grading and observation lifted,
`absorb`); `UC.Machine.Run`'s `runᴹ-resp-≈ᴹ`, hence `Observationᴹ`;
`UC.QueryBound`'s `qbᵢ-mono`, `qb-resp-≈`, `qb-mono` and the inhabitation
`qbᵢ-wire`; `UC.Seam`'s `pov-carry`.

Stated as types with nothing inhabiting them — the `TrajectoryFromAudit`
pattern, no postulate and no hole anywhere:

| statement | where | price |
|---|---|---|
| `Grading 𝒫ᴵ` (via `GradingLawsᴹ`'s eight fields) | `UC.Machine` | four are trace-free (~40–60 LOC each); `T₁-∘`, `sub-∘`, `a-isoˡ`, `a-nat` are M2 task 3's trace-fusion gate |
| `Counting` | `UC.QueryBound` | 250–350 LOC; the reference's 248 plus an effectful recursion |
| `BudgetLawsᴹ` (four closure laws) | `UC.QueryBound` | `qb-T₁`/`qb-sub` ~50 each, `qb-id` ~30, `qb-∘` 250–400 (the reference's token walk over a ⊕-trace) |
| `Reflects` | `UC.Bridge` | ~250 LOC, instance-specific reifier; spike the two-machine skeleton first |
| `AgreeToAdv` | `UC.Seam` | `Reflects` + `PrAgree`, no new content |
| `UC-compose` | `UC.Emulation` | two more `Grading` fields (`sub`/`T₁` interchange, `a⇒` naturality in its first two slots) |

`Budget`'s `qb-T₁`/`qb-sub` land at `c ⊔ 1`, not `c`, and that is not
bookkeeping: the ancilla's own downward relay is a completed event an activation
from above must have deposited for, so a rate of zero cannot survive the
action.  `qbᵢ-wire` is where this is visible.

### Two perf findings, both recorded in the source

* **The reindexing record needs every object implicit passed explicitly.** Left
  to inference, each field of `𝒫ᴵ` asks Agda to invert
  `Machine (Pos A + Neg B) (Neg A + Pos B)` for the pair `(Pos A , Neg B)`, and
  `_+_` is not a constructor; the resulting normalization of `𝒢ₚ` — which
  carries the whole Elgot instance under it — exhausts a 10 GiB heap.  With the
  implicits pinned the module checks in seconds.
* **A record whose field types project a step out of a general `Proc` hits the
  `GradedKleisli` eta cliff.**  Declaring `QBᵢ` over `M : Proc A B` makes the
  level solver compare `Machine (Mealy-Monoidal … .⊗₀ (Pos A) (Neg B)) …`
  against the `_⊎_` spelling, and the record-eta comparison of the two
  spellings of the base instance exhausts the same heap.  The cure is to take
  the state, point and step as **parameters** and let a process supply them at
  the use site, where the identical conversion is a plain application and costs
  nothing (`UC.QueryBound.Certificate`, `Certified`).  The same medicine is the
  obvious next attempt at `Gradingᴹ : GradingLawsᴹ → Grading 𝒫ᴵ`, which does
  not assemble for exactly this reason — which is why the obligation is taken
  at `Grading 𝒫ᴵ` itself.

### Compatibility with the inherited MD line

The old UC modules are all still consumed by inherited code:
`MachineAxioms`, `FamilyCategory`, `VanishingTV`, `StandardTV` and
`OutputOnly` by `Machine/Probabilistic/Model` and `Examples/MerkleDamgard{,/UC}`;
`UCSetup`/`Abstract{,2}`/`Standard{,2}` by the `RandomOracle`/`RelSetup` line.
None was edited: M3 is built **alongside** them, under `CategoricalCrypto.UC.*`,
so the MD line is bit-for-bit unaffected.  Superseding them is a deletion pass
once the MD line is replayed onto this layer, and the mapping is one-to-one —
`MachineAxioms` → `UC.Base`'s three records, `FamilyCategory` → `UC.Family`,
`VanishingTV` → `UC.Environment` + `UC.Family`'s ingestion half, `StandardTV` →
`UC.Machine`, `OutputOnly` → `UC.Bridge` + `UC.Seam`.

One module of M2 changed: `Protocol.Machine`'s `runᴹFrom` now calls a named
continuation `resumeᴹ` instead of a `where`-local one, extensionally the same
step, so that `UC.Machine.Run` can quantify over it.  `Protocol.Machine.Pin`
still computes both verdicts by `refl`.

### Assumption ledger

Still empty of escape hatches: whole-`src` hatch grep 21 before and after (the
M1 baseline).  `Machines.Iteration.Elgot` and `Machines.Trace.Remaining` remain
discharged at the intended base; the six statements in the table above are
`Set`s with nothing inhabiting them and are not assumed anywhere; `UC.Seam` and
`UC.Family` take their `Grading`/`Budget` as module parameters, which is what
keeps them generic.
