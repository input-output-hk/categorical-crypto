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
| M2 wave 3: the machine SMC bundle, `Traced`, GConstruction, `morphism`/`Pr-agree` | not started |
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
| `…Machines.Tensor` | 166 | `tstep`, `_⊗ᵉ_`, `⊗ᵉ-resp-≲`, `pureᴹ` + functoriality, `α⇒ᴹ`/`α⇐ᴹ`/`σᴹ` |
| `…Machines.Iteration` | 113 | the `Elgot` hypothesis record, `tstep-pad`, the derived `iter-uniform`/`pure-+₁` |
| `…Machines.Trace` | 267 | `solve`/`traceStep`/`traceᴹ`, `iter-onL`, yanking, vanishing₁, step-level naturality, state extension, `Remaining` |
| `…Machines.Trace.Naturality` | 97 | `trace-∘ˡ`, `trace-∘ʳ` for arbitrary machines |
| `…Machines.Trace.Congruence` | 80 | `trace-resp-≲`, `trace-resp-≈ᴹ` |
| `…Machines.Trace.Superposing` | 119 | `superposing`, `super-step` |
| `…Machines.Trace.Vanishing` | 256 | `vanishing₂`, `vanish-step`, `[]-δ⇐` |
| `…Machines.Trace.Fubini` | 202 | `trace-comm`, `relabel-step`, `β+` |
| `…Machines.Trace.Laws` | 39 | `Remaining`, as a term |
| `…Machines.Base` | 260 | `Dₚ-DiscreteMonad`, `𝒱ₚ`, `distₚ`, `𝒫ₚ`, `Elgotₚ`, `Remainingₚ` — the intended instance, hypothesis-free |

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

### What wave 3 owes

* **The machine SMC bundle** — `triangleᴹ`/`pentagonᴹ`/`hexagonᴹ`, the unitor,
  associator and braiding naturalities, `⊗ᵉ-homomorphism`, hence `Monoidal` and
  `Symmetric` for `Mealy-Category`.  All of them are `pureᴹ`-conjugations of a
  base coherence law, which is why `pureᴹ-cong`/`pureᴹ-id`/`pureᴹ-∘`/`⊗ᵉ-pureᴹ`/
  `pure-∘ˡ`/`pure-∘ʳ` are already proved here; `⊗ᵉ-homomorphism` and
  `assoc-commuteᴹ` additionally want `Ω`, `slot-comm` and `tstep-α`, which is why
  `Ω`/`tuck`/`untuck` are not in `Machines.Core` yet.
* **`Mealy-Traced` and `GConstruction`** — both are *blocked on the bundle*, not
  on the laws: `Traced` is indexed by `Monoidal Mealy-Category` and
  `GConstruction` takes `(C , Monoidal , Traced)`.  Every field they need is now
  a term (`vanishing₁ᴹ`, `yankingᴹ`, `vanishing₂`, `superposing`,
  `trace-resp-≈ᴹ`, `trace-∘ˡ`, `trace-∘ʳ`, `trace-comm`), so once the bundle
  exists the assembly is the elgot spike's `Assemble.agda` verbatim — two record
  literals.
* **`Monoidal (GConstruction C)`** — inherited, unchanged, 300–600 LOC HIGH.
* **`morphism`/`morphism-∘`/`Pr-agree`** — the agreement theorems that connect
  layer 1's `Protocol` to the machine category.

### Assumption ledger

Empty.  Every term in every module of M2 is total; zero postulates, zero
`TERMINATING`, zero holes; whole-`src` hatch grep 21 before and after (the M1
baseline).  `Machines.Iteration.Elgot` and `Machines.Trace.Remaining` are still
module *parameters* of the generic layer — that is what keeps it generic — but
both are discharged at the intended base in `Machines.Base`.

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

## M3 pointers

M3 harvests: `sfunm-setoid`'s ℰᵗᵛ/StandardTV statements, the α query-bound +
counting theorem, restated over `Iface` with the ancilla parameterized (no K
island). Assumption ledger of M1: `ser`(+`ser-inj` at `AtBirthday`) — module
parameters, maintainer-sanctioned; zero postulates.
