# The protocol rewrite

Greenfield rewrite of the post-`string-diagram-solver` arc (base: `f71a2381`), built
statement-first. Reference material: `spike-pov-tower` (example, observables),
`spike-pov-dp`/`spike-dp`/`spike-elgot` (the Dₚ/machine layer, M2), `sfunm-setoid`
(proof techniques only). The five structural differences from the reference arc:

1. **Protocols are the spine; machines are composition-preserving semantics.** Everything
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

**Reconciled 2026-09-11 at `6256a140`.** The
[implementation review](protocol-implementation-review.md) reviews
`f71a2381..6256a140` and supersedes earlier completion verdicts here. The
implementation/pricing narrative, LOC counts, hatch counts and timings below
are historical snapshots, not a fresh census or benchmark. In particular, the
old projection-cost ceiling and deleted `Cast`/`Laws` route are retired findings,
not current blockers. Current proof status and remaining semantic gaps follow.

| milestone | status |
|---|---|
| M1: layers 0–1 + the ledger example | **DONE** — all green, pins by `refl`, hatches 21 = baseline |
| M2 wave 1: `Dₚ`, `Kl(Dₚ)`, `Mealy` + `Mealy-Category` + the ⊕-trace | **DONE** — all green, hatches 21 = baseline |
| M2 wave 2: the four residual trace laws + `Elgot` at `Kl(Dₚ)` | **DONE** — the machine layer is hypothesis-free; hatches 21 = baseline |
| M2 wave 3: the machine SMC bundle, `Traced`, GConstruction, `morphism`/`Pr-agree` | **DONE** — closed machine bundles; `PrAgree` proved; `Protocol.Machine.Compose.morphism-∘` and `Protocol.Machine.Total.morphismCompose : Morphism-∘` proved. The wire image is not the machine identity, so this is not a literal functor. |
| M3/M4: the UC layer and inherited model/family setup | **Constructions and major seams proved; end-to-end graded asymptotic UC→POV NOT complete.** Grading, Budget, UCBase and inherited model/family `UCSetup` are real closed constructions. `ContextDominated`, adequacy, grounding (with repaired totality premises), and `AuditIsBounded` are proved. The review finds a mismatched audit predicate, a false saturation statement, and missing robust/family integration; see below. |

The ledger's `TrajectoryFromAudit` and `Birthday.target` are also proved; the
birthday theorem is conditional on injective serialization. These results do
not by themselves supply an inherited graded asymptotic UC→POV theorem.

## Modules (M1: 10 files, 874 LOC, all `--safe --without-K`)

| module | LOC | role |
|---|---|---|
| `ProbabilisticLogic.Prelude` | 33 | the probability vocabulary, one import |
| `…RationalDist.Advantage` | 38 | `adv⊥` pseudometric (ported; base lacked it) |
| `CategoricalCrypto.Iface` | 22 | interfaces `Pos ⇿ Neg`, `unitᴵ`, `_⊗ᴵ_` |
| `CategoricalCrypto.Strategy` | 33 | strategies with the `coin` node; `asks≤` (coins free) |
| `CategoricalCrypto.OracleCall` | 40 | the plain zero-or-one-call shape (ported) |
| `CategoricalCrypto.Protocol` | 106 | `Calls` trees (`ret`/`call`/`coin`/`dead`), `Protocol`, `wireᵖ`, `_∘ᵖ_`, `uniformVec` |
| `CategoricalCrypto.Protocol.Observe` | 128 | `run`/`Pr`/`Prᵇ`, `hitRun`/`PrHit`, `Bounded`/`BoundedHit`, `_≈adv[_]_` (both verdicts), `transfer` |
| `Examples.ChimericLedger` | 186 | the ledger kernel + `Replay` (computed) |
| `Examples.ChimericLedger.POV` | 208 | oracle/ledger/`Sys = ledger ∘ᵖ oracle`, `POV`, audit gadget, `AtBirthday` |
| `Examples.ChimericLedger.Pin` | 74 | `chimeric-violates ≡ 1ℚ`, `consuming-safe ≡ 0ℚ`, the genesis liveness, all by `refl` |
| `Examples.ChimericLedger.Carry` | 46 | `Emulᴸ`/`advᴸ`/`pov-carryᴸ` — `pov-transfer`'s premise from the seam (a later addition; M3's model is what closes it) |

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
* **The birthday target is pinned at a genesis state** (`genesis h₀ a V` — all the value
  in one UTxO output keyed by a genesis hash): a fresh hash can collide with a
  pre-existing UTxO key, so `ε q = (q² + q)·2⁻ˡ` carries a `+ q` for collisions with
  `h₀` and an arbitrary `s₀` would add a `q · |s₀|` term. General-`s₀` forms are kept
  everywhere else. The first version of this genesis put all the value in an *account*
  with an empty UTxO set, which the external review found VACUOUS — `checkIns` rejects
  every input against an empty set while `consumes inputConsuming` demands one, so no
  transaction is accepted and the bad event has probability zero. `ChimericLedger.Pin`
  now pins the genesis live (accepted with probability 1, state changed) by `refl`.
* `TrajectoryFromAudit` (trajectory probability ≤ audit-form probability of the
  audit-interleaved strategy) is now proved in `Examples.ChimericLedger.Trajectory`.
  The historical price was ~250–400 LOC for persistence and run inductions;
  it is no longer an uninhabited statement. `Examples.ChimericLedger.Birthday.target`
  proves the birthday target under injective serialization.

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
* **`Monoidal (GConstruction C)`** — done, including the `⊗`-homomorphism wall;
  see task 3 below for where its pricing was wrong.
* **`morphism`/`morphism-∘`/`Pr-agree`** — `morphism` landed; the two agreement
  theorems are now proved; the original pricing is retained below as history.

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
| `…Dp.Embed` | 213 | `embed : Dist⊥ A → Dₚ A` as a cascade of conditional coins, `embed-cum` (exact past its depth), `embed-cong` |
| `…Dp.Stable` | 97 | `Stable` — an eventually-constant `cum` — and its closure under a value, a divergence, a bind junction and a coin node |
| `CategoricalCrypto.Protocol.Machine` | 137 | `⟦_⟧ᴵ`, `MSt`, `drive`, `morphism`, `runᴹ`, `Morphism-∘`, `PrAgree` (at either verdict) |
| `…Protocol.Machine.Agree` | 73 | `callAgree`/`runAgree`, `prAgree` — `PrAgree`, proved |
| `…Protocol.Machine.Pin` | 114 | layer 1 and the machine image agree by `refl`; `nay`/`stuck` pin `false` apart from divergence |

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

### Task 3: `Monoidal (GConstruction C)` — done

`Categories.GConstructionMonoidal`, generic over the four trace hypotheses
`GConstruction` already took — **no new hypothesis** — and instantiated at the
machine layer as `Machines.G.Mealy-G-Monoidal` and `Machines.Base.𝒢ₚ-Monoidal`,
with `𝒢ₚᴹ` the `MonoidalCategory` bundle the UCSetup route consumes.  Objects
and tensor are as priced: `(A⁺,A⁻) ⊗ᴳ (B⁺,B⁻) = (A⁺ ⊗₀ B⁺ , A⁻ ⊗₀ B⁻)`,
`unitᴳ = (I , I)`, and `f ⊗₁ᴳ g = mid ∘ f ⊗₁ g ∘ mid` for the middle-four
interchange `mid : (P ⊗ Q) ⊗ (R ⊗ S) ⇒ (P ⊗ R) ⊗ (Q ⊗ S)`, which is its own
inverse — one `mid`, not a `w`/`w⁻` pair — and spends no trace.

Where the pricing was wrong, in both directions:

* **`⌜⌝-⊗` is one solver call, not a hand split.**  It was priced at 40–60 LOC
  of `Machines.Reassoc`-style `solveMor!` on the ground that the normalizer
  never splits a crossing block.  That limitation is the *other* solver's
  (`Coherence.Monoidal.*`, whose `lim-hexagon` records it); the APROP
  hypergraph solver does not care where `σ⇒` sits, so `⌜⌝-⊗` is
  `solveTerm!ᵀ lhs rhs refl` over an 8-atom, 4-generator signature.  The
  associator naturality square goes the same way at 12 atoms and three
  generators.  All four residues share one 59 s module,
  `GConstructionTensorCoherence`.
* **Everything in item 2 held exactly.**  `identity`, `triangle` and `pentagon`
  are `⌜⌝-⊗` + `⌜⌝-∘` + `⌜⌝-resp-≈` around the base law, with `Utilities`'
  `triangle-inv`/`pentagon-inv` for the negative polarity; the two unitor
  squares and the associator square are `absorbˡ`/`absorbʳ` around one solver
  call each.  The monoidal module is 250 LOC and a 10 s warm check.
* **`homomorphism` needed one general lemma the plan did not name, and its
  "one coherence step over 8 atoms / 4 generators" is not affordable.**  The
  route is right as far as it goes: `serialize₁₂` + `right-superposing` +
  `superposing` + `trace-∘ˡ/ʳ` fuse `trace ⊗ trace` into a nested double trace
  (`⊗-trace`).  But the two sides' loops are `(B⁻⊗B⁺)⊗(Q⁻⊗Q⁺)` and
  `(B⁻⊗Q⁻)⊗(B⁺⊗Q⁺)` — the same four wires *interleaved* — so `vanishing₂`
  cannot merge the fused pair into the tensor's loop, and `trace-comm` on its
  own cannot reorder them.  Two lemmas close that gap, both plain facts about
  traced categories with no G-construction wiring in them:

      ⊗-trace-mid : trace u ⊗₁ trace v ≈ trace (mid ∘ u ⊗₁ v ∘ mid)
      trace-mid   : trace f ≈ trace (id ⊗₁ mid ∘ f ∘ id ⊗₁ mid)

  the first "the trace is monoidal" (`⊗-trace`, one 2-generator coherence,
  `vanishing₂`), the second "a loop object re-brackets along `mid`": four
  `vanishing₂` splits down to single wires, one Fubini step transposing the
  middle two, one 1-generator coherence.  `trace-mid` is the piece the plan was
  missing, and it does **not** need sliding/dinaturality — the four hypotheses
  suffice, which is why the instance side stayed safe.

  What is then left is one equation between the two loop bodies, and **solving
  it whole is out of reach**: ~50 boxes a side over 12 atoms and four
  generators, no answer in 900 s.  (The `assoc'` precedent —
  `GConstructionCoherence`'s "the 50-morphism equation is never solved whole" —
  holds here too.)  It splits at the one place the two sides genuinely differ:
  both apply the same four boxes, the left grouped `(f′⊗f) ⊗ (g′⊗g)` and the
  right `(f′⊗g′) ⊗ (f⊗g)`, and those two groupings are conjugate by `mid`.  So
  with `Lout`/`Lin`/`Rout`/`Rin` the wiring on either side of the boxes,

      ob-out : Lout ≈ Rout ∘ mid           (no generators)
      ob-nat : mid ∘ BoxL ∘ mid ≈ BoxR     (`mid`'s naturality, four one-box legs)
      ob-in  : Lin ≈ mid ∘ Rin             (no generators)

  paste by congruence, with the re-bracketings bridged by `stepR!` (pure
  assoc, no solver leaf).  29 s, against >900 s for the equation whole.

`GConstruction`'s `β`, `α`, `γ`, `trace-βyank`, `trace-gyank` and
`right-superposing` were `where`-local to its `categoryHelper` literal, so the
monoidal layer could not reach them; they moved verbatim into
`Categories.GConstructionTrace` under the same four hypotheses, taking
`GConstructionEmbedding`'s duplicate `β` with them.  No statement changed, and
`GConstructionEmbedding`'s two anonymous modules were named (`Embed`,
`Embed.WithTrace`) so that a consumer can `open` them at its own parameters.

`Braided`/`Symmetric` on `𝒢` was not built.

The **instantiation** hit the branch's recorded conversion cliff in its sharpest
form yet.  Declaring `Mealy-G-Monoidal : Monoidal Mealy-G`, with the category
and its structure spelled as two separate `GConstruction*` applications, makes
Agda reduce both sides to `Category` record values and compare them field by
field — and `assoc`/`identityˡ`/`identityʳ` there *are* the transported solver
witnesses.  Measured on `Machines.G` alone: heap exhausted at 8 GB after 118 s.
The cure is the bundle.  `GConstructionMonoidalCategory` returns a
`MonoidalCategory`, and the instance takes both the category and the structure
as **projections of one application** (`Machines.G.Mealy-Gᴹ`,
`Machines.Base.𝒢ₚᴹ`), so every field is syntactically shared and the comparison
never happens: 12.7 s at 1.7 GB.  That is the entry point an instance should
use; `Monoidal <the category spelled a second time>` is the shape to avoid.

| new module | LOC | warm check | role |
|---|---|---|---|
| `Categories.GConstructionTrace` | 145 | 7 s | `β`/`α`/`γ`/`mid`, the yanks, `right-superposing`, `⊗-trace`, `⊗-trace-mid` |
| `…GConstructionTraceCoherence` | 94 | 9 s | `TM`, `⊗-trace-mid`'s coherence (6 atoms, 2 generators) |
| `…GConstructionLoop` | 97 | 7 s | `trace-mid`, `trace-conj` |
| `…GConstructionLoopCoherence` | 123 | 67 s | `LC`, `trace-mid`'s coherence (6 atoms, 1 generator) |
| `…GConstructionTensorCoherence` | 251 | 59 s | `TX`, `UL`/`UR`, `AC` |
| `…GConstructionHomCoherence` | 177 | 29 s | `HOM`, by the three-obligation split |
| `…GConstructionMonoidal` | 250 | 10 s | the `Monoidal` record and its bundle |

### Task 4: composition-preserving semantics (historically called the functor)

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

#### The two agreement theorems: historical statement and pricing

Both are now inhabited, not merely certified types. Composition is proved by
`Protocol.Machine.Compose.morphism-∘` with the public G-composite wrapper
`Protocol.Machine.Total.morphismCompose`; `PrAgree` by `Protocol.Machine.Agree`.
The proposed route and estimates below record the earlier implementation plan.

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

    PrAgree = (b : Bool) (P : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B))
            → Σ[ n ∈ ℕ ] ((m : ℕ) → cum (n + m) (runᴹ (morphism P) d) (indᵇ b)
                                  ≡ Prᵇ P b d)

**PROVED** (`Protocol.Machine.Agree`, 73 LOC, on `Dp.Stable`'s 97), against a
price of 250–450 in two modules.  The route taken is neither of the two the
price anticipated: the budget bookkeeping factors out as `Stable P d u` — "every
budget past some witness scores `u`" — which is closed under the four ways a run
is built (a value, a divergence, a bind junction, a coin node), and once that is
in hand the theorem is two nested inductions with no arithmetic left in them,
one on the call tree an activation drives against `Observe.evalC`, one on the
strategy against `runFrom`.  The `Dist⊥`-vs-`Dₚ` bind mismatch the price called
"the one piece of real work" never arises: `Stable-coin` reads a coin node
directly as an `E μ`, so `Dp.Embed`'s cascade — the general embedding, landed —
is not on the path at all.  The test is a parameter throughout, so "at either
verdict" costs nothing.  One general lemma was owed and added:
`E⊥-bind`, the partial expectation's bind law.

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

`Morphism-∘` and `PrAgree` are theorems. `Total.totalRun-morphism` additionally
requires a protocol totality premise (the two verdict masses sum to at least
one for every strategy); it does not prove `TotalRun` for every `Protocol`,
whose syntax permits `dead`. `Total.totalRun-∘` transports a supplied total-run
certificate across composition agreement.

One shape seam is open and it is not load-bearing today: `⟦ unitᴵ ⟧ᴵ` is
`(Data.Empty.⊥ , Data.Empty.⊥)` while `Mealy-Monoidal`'s unit is
`Data.Empty.Polymorphic.⊥` — isomorphic, not identical.  It bites only when M3
wants `⟦_⟧ᴵ` monoidal, and the cure is the `Iface`-polymorphism M3 plans anyway.

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

## M3: the UC layer (20 files, 2735 LOC)

| module | layer | LOC | role |
|---|---|---|---|
| `CategoricalCrypto.UC.Core` | core | 100 | `Grading`, `Observation` (qualitative), `UCBase` |
| `…UC.Environment` | core | 172 | `SameTV` (ancilla a parameter), `Tests`, `ℰᵗᵛ`, `_≈ℰ_`, its congruences, `≈ℰ-at`, `grade-stable` |
| `…UC.Emulation` | core | 82 | `_≤UC_`, `_≤UC⁺_`, `≤UC-refl`/`≤UC-trans`/`dummy-complete`, `blind-grade`/`unit-grade`.  `≤UC⁺⇒≤UC`, `_⊙_`, `_⊛₁_` and the `UC-compose` obligation are RETIRED — the inherited layer has the composition theorem |
| `…UC.Core.Standard` | core | 49 | `gradingᵗ` — a monoidal category grades itself; the inherited doctrine's action |
| `ProbabilisticLogic.Dp.Advantage` | enrichment | 121 | `Pr≤[_]`/`Pr≤`, `_≼ₚ[_]_`/`_≈ₚ[_]_` — advantage as an ε-indexed relation on BOTH verdict masses, with the pseudometric laws |
| `…UC.Approximate` | enrichment | 254 | `ErrorAlgebra`, `ℚ-errors`, `Grade`/`GradedBound` with `_→0`/`VanishingBound` and `Negligible`/`NegligibleBound` its two instances, the two collapses and the sum closures (`→0-+`, `Negligible-+`), `Approximation` + the ε/2 equivalence, `ApproximateObservation`, `Induced`, `Mass` |
| `…UC.Budget` | enrichment | 64 | `Budget`, `ctxBudget` — the resource doctrine |
| `…UC.Environment.Approximate` | enrichment | 38 | `_≈ℰ[_]_`, `absorbᵘ` |
| `…UC.Audit` | enrichment | 133 | `_≤UC[_]_` (a budgeted simulator), `simCost`, `AuditBound`, `audit-carry` — the graded carry, proved |
| `…UC.Family` | enrichment | 252 | `𝒞^ω` at a parameterized index, `PolyQB`, `Fam`, `Grading^ω`, `Approximation^ω`, `Observation^ω`/`Approximate^ω`, `UCBase^ω`, `ctxQB`, `_≈ℰ[_]_`, `absorb`, and the negligible layer `CarriedNegligible`/`carried-negligible`/`absorb-negl` |
| `…UC.Machine` | model | 206 | `Proc`, `𝒫ᴵ`, `wireStep`/`wireᴹ`, `Ωᴵ`, `⟦_⟧ᴼ`, `Approximationᴹ`/`Observationᴹ`/`ApproximateObservationᴹ`, `T₁ᴵ`/`subᴵ`/`a⇒ᴵ`/`a⇐ᴵ`, `UCBaseᴹ` |
| `…UC.Machine.Grading` | model | 74 | the four re-basings `qb-T₁ᴳ`/`qb-subᴳ`/`qb-a⇒ᴳ`/`qb-a⇐ᴳ`, carrying a query-bound certificate about a pinned relay to `gradingᴹ`'s action through a `…Dictionary` zigzag.  `GradingLawsᴹ`, `Gradingᴹ` and `Budgetᴹ` are GONE (perf finding 8); the `Budget (𝒢ₚ 0ℓ) gradingᴹ` assembly this row used to call owed is `UC.Machine.Budget.budgetᴹ`, and `UC.Model.Enrichment.budgetᵒ` carries it across the seal |
| `…UC.Machine.Run` | model | 157 | `step-sim`, `point-sim`, `run-sim`, `runᴹ-resp-≈ᴹ` — a simulation is invisible to a closed run |
| `…UC.QueryBound` | model | 480 | `Below`/`AtMost`/`Ans`/`forget`, `QBᵢ`, `qbᵢ-mono`, `traceᵍ`/`behᵍ`, `#inj₁`/`#inj₂`, `CountBound`, `Counting`, `qbᵢ-wire`, `Certified`, `QB`, `qb-resp-≈`, `qb-mono`, `qbᵢ-resp-step`, `qbᵢ-id`/`qbᵢ-T₁`/`qbᵢ-sub` and their hom-level forms, `BudgetLawsᴹ` |
| `…UC.QueryBound.Counting` | model | 237 | `CountedRun`, `countᵍ`/`countᵍ-erase`, `qbᵢ⇒count` — `Counting` inhabited |
| `…UC.QueryBound.Compose` | model | 330 | `resumeF`/`resumeG`, `Unfolding` (the composite step's six equations), `qbᵢ-∘ᵍ` — the two-position token walk at rate `c * c′` |
| `…UC.QueryBound.Compose.Step` | model | 495 | `Pt` and the `pt-*` routings, `onLₑ`/`tstepₑ`, `α⁰`/`γ⁰`/`Hα`/`Hγ` with `α-pure`/`γ-pure`, `unfoldᶜ` — `Unfolding` discharged at the real composite — and `qbᵢ-∘`/`qb-∘` |
| `…UC.QueryBound.Compose.Laws` | model | 27 | `budgetLawsᴹ` — `BudgetLawsᴹ` assembled, given the two respect-`≈` hypotheses `qb-T₁ᴹ`/`qb-subᴹ` already take |
| `…UC.Machine.Bridge` | model | 96 | `λᴵ⇐`, `conjᴵ`, `ctxRun`, `ContextDominated` (proved by `UC.Machine.Dominated.dominated`) |
| `…UC.Seam` | model | 171 | `strategyEnv` (a strategy as an environment), `ctxRunˢ`/`runˢ`, `Agreeˢ`, `Adequacy`/`AgreeToAdv` (stated here, both inhabited below), `pov-carry` (proved) |
| `…UC.Seam.Adequacy.Wiring` | model | 358 | the G-composite's structural wiring collapsed to pure machines (`α-pure`/`γ-pure`), `kᵂ` (the loop's one-pass dispatch), `pairedᴹ`, `compose-≈ᴹ` |
| `…UC.Seam.Adequacy` | model | 188 | `bodyᵂ`/`verdictᵂ`/`contᵂ`, `play-run`/`step-run`, `adequacy` — `Adequacy`, proved |
| `…UC.Seam.Carry` | model | 96 | `run-agree`, `agree-to-adv`, and the now-closed `agreeToAdv`/`povCarry` |
| `…UC.Seam.Grounding` | model | 152 | `StratIsEnv`, its reduction `EnvCtx`/`EnvAsCtx`, and the trivial grade's `SubBlind`/`IotaBlind`/`UnitGrade` — the grading-dependent statements, read in the INHERITED metatheory at the sealed bundle (`_≈ᵁ_` at graded codomains, `_≈ᴳ_` at ungraded ones) |
| `…UC.Seam.Grounded` | model | historical 108 | `iotaBlind`, `envAsCtx`, `stratIsEnv`, and repaired `subBlind`/`unitGrade` proved with `SimTotal`/`TotalRun` premises |
| `…UC.Seam.Audit` | model | 58 | `UC.Audit` at closed model data; `AuditIsBounded` proved in `UC.Seam.Audit.Bounded`, but its premise is not a ledger audit-event bound |
| `…UC.Saturated` | frontend | 206 | REPAIRED: `SaturatedBounded[_]`/`SaturatedHit[_]` fix the slack per polynomial allowance and are graded (`_→0` and `Negligible` instances); `SaturatedRespects` is now PROVED by `saturated-respects`, with `saturated-respectsᴺ` and `_≈negl_` the negligible tier |
| `…UC` | — | 66 | the one entry point, with the layering as its orientation |

All `--safe --without-K`; the `Dₚ`-facing nine add `--guardedness` and nothing
adds anything else — the whole core and the whole enrichment are `Dₚ`-free. **There is no K island**, which was the acceptance test.
Every module is a warm single-module check of 8–10 s; `UC.Machine`'s closure
from cold is 85 s.

### The qualitative core, and its enrichment

The abstraction notes' governing constraint is that a general UC setup need not
support quantitative observations, so the layer is split three ways and the
split is load-bearing rather than cosmetic: rational advantage, security
parameters, negligible functions and ℕ query bounds are all model data, and the
core is what survives without them.

| layer | contains | does not assume |
|---|---|---|
| core (`UC.Core`, `UC.Environment`, `UC.Emulation`) | category, grading action, qualitative observation, environments, simulators, `_≤UC_` and its metatheorems | probability, rationals, ℕ bounds, negligible functions, an index |
| enrichment (`UC.Approximate`, `UC.Budget`, `UC.Audit`, `UC.Family`, `…Environment.Approximate`) | an abstract error algebra, approximate closeness, query-budget closure laws, a one-sided mass, the asymptotic construction | any particular error carrier; finite protocol syntax |
| model (`UC.Machine`, `UC.QueryBound`, `UC.Machine.Bridge`, `UC.Seam*`) | `Dₚ`, `𝒫ᴵ`, the ticked verdict, the amortised-potential certificate, the strategy embedding | — |
| frontend (`UC.Saturated`, layer 1's `Protocol`/`Strat`) | executable statements over protocols and strategies | completeness for arbitrary `Dₚ` contexts |

The core's two records, verbatim minus the `Grading` fields the previous section
already lists:

    record Observation {o ℓ e} (𝒞 : Category o ℓ e) (os ℓs : Level)
                     : Set (o ⊔ ℓ ⊔ e ⊔ suc os ⊔ suc ℓs) where
      open Category 𝒞
      field
        𝟙 Ω : Obj
        Obs : Set os
        ⟦_⟧ : 𝟙 ⇒ Ω → Obs

        _∼_             : Obs → Obs → Set ℓs
        ∼-isEquivalence : IsEquivalence _∼_
        ⟦⟧-resp-≈       : {u v : 𝟙 ⇒ Ω} → u ≈ v → ⟦ u ⟧ ∼ ⟦ v ⟧

    record UCBase (o ℓ e os ℓs : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ os ⊔ ℓs)) where
      field
        𝒞           : Category o ℓ e
        grading     : Grading 𝒞
        observation : Observation 𝒞 os ℓs

The observation carrier `Obs` stays (the notes permit it, and every consumer
reads a run *through* it), but the comparison is now an equivalence and nothing
else.  The enrichment is where the number returns:

    record ErrorAlgebra (es ℓe : Level) : Set (suc (es ⊔ ℓe)) where
      field
        Error    : Set es
        ε₀       : Error
        _⊕_      : Error → Error → Error
        _⊑_      : Error → Error → Set ℓe
        Positive : Error → Set ℓe
        half     : Error → Error
        ε₀-least : {ε : Error} → Positive ε → ε₀ ⊑ ε
        half-pos : {ε : Error} → Positive ε → Positive (half ε)
        half-sum : (ε : Error) → half ε ⊕ half ε ⊑ ε

    record Approximation (Obs : Set os) (E : ErrorAlgebra es ℓe) (ℓa : Level)
                       : Set (os ⊔ es ⊔ ℓe ⊔ suc ℓa) where
      open ErrorAlgebra E public
      field
        _≈[_]_    : Obs → Error → Obs → Set ℓa
        ≈[]-refl  : {x : Obs} → x ≈[ ε₀ ] x
        ≈[]-sym   : {x y : Obs} {ε : Error} → x ≈[ ε ] y → y ≈[ ε ] x
        ≈[]-trans : {x y z : Obs} {ε δ : Error}
                  → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε ⊕ δ ] z
        ≈[]-mono  : {x y : Obs} {ε δ : Error} → ε ⊑ δ → x ≈[ ε ] y → x ≈[ δ ] y

      _∼ᵃ_ : Obs → Obs → Set (es ⊔ ℓe ⊔ ℓa)
      x ∼ᵃ y = (ε : Error) → Positive ε → x ≈[ ε ] y

      ∼ᵃ-isEquivalence : IsEquivalence _∼ᵃ_        -- the ε/2 argument, once

    record ApproximateObservation {𝒞 : Category o ℓ e} (O : Observation 𝒞 os ℓs)
                                  (E : ErrorAlgebra es ℓe) (ℓa : Level) … where
      open Category 𝒞; open Observation O
      field approx : Approximation Obs E ℓa
      open Approximation approx public
      field
        induces    : {x y : Obs} → x ∼ᵃ y → x ∼ y
        ⟦⟧-resp-≈₀ : {u v : 𝟙 ⇒ Ω} → u ≈ v → ⟦ u ⟧ ≈[ ε₀ ] ⟦ v ⟧

`induces` is the notes' quantitative-to-qualitative constructor, and
`UC.Approximate.Induced` runs it in the direction both models actually need —
an approximation plus the runs it measures IS an observation, whose `_∼_` is
`_∼ᵃ_` and whose `induces` is then the identity.  So the ε/2 equivalence is
proved exactly once, over the abstract algebra, and neither model reproves it:

* `UC.Machine.Observationᴹ = Induced.observation 𝒫ᴵ Approximationᴹ …` at
  `Approximationᴹ = ≈ₚ[_]` over `ℚ-errors`;
* `UC.Family.Observation^ω = Induced.observation Fam Approximation^ω …` at
  eventual ε-closeness in `κ`, which is why the family's `_∼_` is *literally*
  vanishing advantage and `absorb` is `induces` at a vanishing error.  The
  family also re-exports `Approximate^ω`, so the construction iterates.

`⟦⟧-resp-≈₀` is the one field the notes' list does not name and the
construction needs: the core's `⟦⟧-resp-≈` only says a hom equality is observed
up to every *positive* error, while the asymptotic layer has to start its
eventual relation at zero.

Two consequences worth recording.  `Mass` is now a reading of the QUALITATIVE
agreement — `dominate : x ∼ y → (δ : ℚ) → 0ℚ < δ → (n : ℕ) → Σ[ m ] at n x ≤ at
m y + δ` — which makes `audit-carry` shorter than it was (the `δ + 0ℚ` shuffle
and its two ℚ lemmas are gone) and keeps the audit layer's only quantitative
commitment in one field.  And κ-cofinality is now documented where it sits, as
an asymptotic-instance requirement: nothing in the core, the environment layer
or the emulation metatheory mentions an index at all.

### Reconciliation with the inherited abstract layer

> **Superseded verdict.**  This section concluded that the new core supersedes
> the inherited layer.  The maintainer has ruled the other way: the inherited
> metatheory — `UCSetup` + `Abstract2.AbstractUC`, reached at the machine model
> through `Standard2.StdUC` — supersedes the hand-rolled core.  The dictionary
> below is still correct except for the `_≈ℰ_` row, which was wrong and is
> corrected in place.  `docs/stduc-supersession-plan.md` carries the phase-1
> bridge, the 65-name inventory, the findings and the phase-2 execution; read
> it for the current direction.

The inherited `CategoricalCrypto.UCSetup` and the new core are the same
intent, and the relation between them is now a **proved weakening in one
direction and a documented obstruction in the other**, not a third parallel
abstraction.

`UC.Core.Standard.gradingᵗ` derives a `Grading (MonoidalCategory.U M)` from any
monoidal category acting on itself.  That is exactly what
`CategoricalCrypto.Standard` feeds `UCSetup` (`𝒞 = ℐ = machines`,
`ℳ = curriedTensor`, so `T₀ X A = X ⊗ A`), so the dictionary is:

| new core | inherited `UCSetup` |
|---|---|
| `_⊛_` | `T₀`, at grades that are also 𝒞-objects |
| `T₁`, `sub` | `T₁`, `sub` — same names, same one-sided actions |
| `a⇒` | `μ X Y` |
| `a⇐`, `a-isoˡ` | the retraction `θ` and its `θ-μ`, which `UCSetup.GradeStableFromTests` already asks for as parameters |
| `a-nat` | `μ-commute` |
| `_≈ℰ_`, `≈ℰ-refl/sym/trans`, `≈⇒≈ℰ`, `≈ℰ-congˡ/congʳ` | **`_≈ᵁ_`, NOT `_≈ℰ_`** (corrected — this row said "the kernel congruence of `ℰ`", and that is a strictly coarser relation: the core's quantifies over an ancilla and the bare kernel does not).  At graded homs the two are the same relation, proved both ways as `UC.Model.Bridge.≈ℰᶜ⇔≈ᵁ`; at ungraded homs, where `_≈ᵁ_` is not stated, it is `UC.Model.Bridge._≈ᴳ_` (`≈ᴳ⇔≈ℰᶜ`).  `≈ℰᶜ⇒≈ℰ` into the bare kernel holds; the converse needs `GradeStable`.  Any rename mapping `≈ℰ ↦ ≈ℰ` silently WEAKENS every statement it touches |
| `grade-stable` | `GradeStable`, there a *statement*, here a theorem |
| `_≤UC_`, `≤UC-refl`, `≤UC-trans`, `dummy-complete` | `Abstract2.AbstractUC`'s, over `≈ᵁ` instead of `≈ℰ`; the two orders agree both ways (`UC.Model.Bridge.≤UCᶜ⇔≤UC`), the inherited one carrying the dummy quantifier in its statement where the core derives it |
| ~~`UC-compose`~~ | retired.  The core could only STATE it (the chain needs a `sub`/`T₁` interchange and an `a⇒`-naturality `Grading` does not ask for); `Abstract2.UC-compose` is a theorem, and `≤UCᶜ⇔≤UC` carries it to any core statement |
| `UCBase` | `UCSetup` — deliberately NOT the same name, to avoid shadowing (rule 29) |

What blocks the converse instantiation is not style but inhabitation, in two
places:

1. **`UCSetup` asks for `ℐ : MonoidalCategory` and `ℳ : GradedKleisliTriple ℐ 𝒞`.**
   The `MonoidalCategory` half is now available — task 3 landed, and
   `Machines.Base.𝒢ₚᴹ` is the bundle — but `𝒫ᴵ` still cannot be presented as a
   graded Kleisli category.  `Grading` is the subset of that structure `grade-stable`
   and the emulation metatheory actually spend — no unitors, no `return`/`ext`,
   no monoidal structure on the grades — and that subset IS inhabitable at
   `𝒫ᴵ` — superseded: the grading is now `UC.Machine.gradingᴹ`, derived on 𝒢's
   own objects, and `Iface` is vocabulary (perf finding 8).
2. **The observation runs the other way.** `UCSetup` takes a presheaf `ℰ` as
   *given* and defines `_≈ℰ_` as its kernel congruence; the core takes a
   comparison of CLOSED runs (`𝟙`, `Ω`, `_∼_`) and *derives* the relation on
   open homs by quantifying over ancilla, test and closure.  Neither direction
   is a special case of the other in general — an arbitrary presheaf has no
   `𝟙`/`Ω` to project — but the new layer does produce the inherited datum:
   `UC.Environment.ℰᵗᵛ Y : Presheaf 𝒞 (Setoids ℓ (ℓ ⊔ ℓs))` is an `ℰ` for each
   ancilla, and the derived relation is its kernel ancilla by ancilla
   (`record { same = … }` and `same` back).  So the core is the
   *test-generated* case of the inherited interface, one presheaf per ancilla
   instead of one presheaf.  The intended instance does better than that and
   supplies ONE presheaf: `UC.Model.Environment.ℰᵒ`, tests into `Ωᵒ` modulo
   closed observation, which is what makes `StdUC` instantiable there and the
   obstruction above moot.

Supersession runs the other way — see the note at the head of this section.
The inherited records are now what the machine model is stated
over; the mapping is the one above plus the module-level map already recorded
(`MachineAxioms` → `UC.Core` + `UC.Budget` + `UC.Approximate`,
`FamilyCategory` → `UC.Family`, `VanishingTV` → `UC.Environment` + `UC.Family`,
`StandardTV` → `UC.Machine`, `OutputOnly` → `UC.Machine.Bridge` + `UC.Seam`).
The earlier claim that nothing inherited was edited is historical; the MD line
has since been ported and superseded modules deleted (see compatibility below).

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
  — and the definition is its kernel relation ancilla by ancilla, the two
  directions being `record { same = … }` and `same`.
* **The advantage is a RELATION, not a function.**  `Dₚ`'s termination mass is
  a supremum the layer never forms, so `MachineAxioms.adv : Obs → Obs → ℚ` is
  uninhabited at the intended instance.  `_≈ₚ[ ε ]_` relaxes `_≼ₚ_`'s
  budget-matching by a rational slack instead, and carries exactly the three
  pseudometric laws the vanishing layer spends.  It compares BOTH verdict
  masses, `Pr≤[ true ]` and `Pr≤[ false ]`: divergence weighs 0 under either
  indicator, so the `true`-mass alone would identify a process that answers
  `false` with one that diverges, which the proposal's §1 forbids
  (`docs/kb/frontier/15-probabilistic-uc-model.typ`; `Machine.Pin`'s
  `nay`/`stuck` pin the separation).  `Pr≤` stays as the `true` reading, which
  is what the one-sided `Mass`/`Bounded`/`transfer` statements read.
  Agreement is then *derived* (`x ∼ y = ∀ ε > 0 → x ≈[ ε ] y`) and its
  transitivity is the ε/2 argument, proved once in `UC.Approximate`, over an
  abstract error algebra, rather than once per instance.  This is the absorb/ε
  misfit, closed.
* **`𝒞^ω` takes its index as a parameter** `(Ix , κ : Ix → ℕ)`.  Only three
  things ever needed `ℕ` in the reference: the polynomial's argument, the
  asymptotics' order, and the budget arithmetic, and all three read the index
  through `κ`.  `Ix = ℕ × ℕ`, `κ = proj₁` gives a second axis for free;
  `(ℕ , id)` recovers the reference.
* **Historically, objects were `Iface` everywhere.** The current grading uses
  𝒢's own objects; `Iface` remains frontend vocabulary. `𝒫ᴵ` presents `𝒢ₚ` with interfaces as its
  objects (`⟦_⟧ᴵ` is a bijection on objects), so `_⊗ᴵ_` — layer 0's own
  interface tensor — is the grading action.  No `Channel`, and no raw pair of
  sets, occurred in that earlier presentation of the layer.
* **The verdict interface is ticked.** `Ωᴵ = Bool ⇿ ⊤`.  A machine is reactive,
  so the reference's `Pos = Bool , Neg = ⊥` verdict can never be activated by a
  closed composite; the tick is the environment's single activation and the
  observation is layer 1's own `runᴹ` at `ask tt out`.
* **The bridge quantifies over strategies; it does not witness one.**  The
  reference's applied form put `Σ[ d ]` before `∀ u v` with *deterministic*
  strategies, which is false twice over — a context flipping a fair coin and
  asking one of two questions gets advantage ½ against two different pairs while
  any deterministic one-ask tree scores zero against one of them (fixed by layer
  0's `coin` node, there since M1), and a finite tree mentions finitely many
  first queries while a `Dₚ` context may ask an unbounded-support sampled
  question at query bound one (fixed by moving the pair in front, round 1).  What
  the second round found is that the surviving existential still asks for a
  finite strategy *exactly dominating* a `Dₚ` context at every slack, i.e. for
  constructive extraction of an optimal deterministic policy with attainment
  rather than approximation.  `ContextDominated` therefore quantifies
  universally: if every strategy of the context's carried budget leaves the two
  direct runs ε-close, the context separates them by at most ε + δ.  That is the
  shape the consumers have anyway (`_≈adv[_]_`/`Bounded` are quantified over
  budgeted strategies, instantiated at `q := ctxBudget c c′`), and the arbitrary
  positive δ is what a convexity argument delivers: a `Dₚ` mass is a supremum
  over budgets the layer never forms, so decomposing a context into the branches
  a strategy plays leaves a residue only a positive δ absorbs.  `_∼_` quantifies
  over every positive slack, so the δ costs a consumer nothing.

### What is proved, and what is priced

Proved, hypothesis-free: the whole `Dp.Advantage` layer; `UC.Approximate`'s
`∼ᵃ-isEquivalence` and the `Induced` construction; `UC.Core.Standard.gradingᵗ`;
`UC.Environment` in full (`ℰᵗᵛ` a presheaf, `_≈ℰ_` an equivalence and a
congruence, `grade-stable`) and `…Environment.Approximate`'s `absorbᵘ`; `UC.Emulation`'s four
metatheorems and the equivalence of the plain and dummy-adversary forms;
`UC.Family` in full (`Fam` a category, the grading and observation lifted,
`absorb`, and the negligible layer `carried-negligible`/`absorb-negl`);
`UC.Machine.Run`'s `runᴹ-resp-≈ᴹ`, hence `Observationᴹ`;
`UC.QueryBound`'s `qbᵢ-mono`, `qb-resp-≈`, `qb-mono`, the inhabitation
`qbᵢ-wire` and the three trace-free closure laws `qbᵢ-id`/`qbᵢ-T₁`/`qbᵢ-sub`
(`qbᵢ-resp-step` is what carries them), and the run-level meaning of the
certificate — `UC.QueryBound.Counting`'s `qbᵢ⇒count`, which inhabits `Counting`
and is what forbids a degenerate reading of the bound; `UC.Environment.≈ℰ-at`; `UC.Seam`'s
`strategyEnv` and `pov-carry`, and `UC.Seam.Carry`'s `run-agree`/`agree-to-adv`
— and since `Adequacy` and `PrAgree` are now theorems, `UC.Seam.Carry`'s
`agreeToAdv` and `povCarry` are closed terms, where `AgreeToAdv` used to be an
assumption of its own.  `Examples.ChimericLedger.Carry.pov-carryᴸ` is that at
the ledger instance: an environment agreement between the two variants' machine
images is now all `pov-transfer`'s premise costs.

`Adequacy` was priced at 250–350 LOC in one module and landed as 188 + 358 in
two, and the split is where the cost actually is.  The ⊕-trace's loop — what the
price anticipated — is the 188: `play-run` is one induction on the strategy
tree, `iterₚ-fix` unrolling the two passes an `ask` costs (the process
answering, the environment resuming).  The other 358 is the G construction's own
wiring: `α` and `γ` are six-fold composites of structural machines, and
collapsing each to a single `pureᴹ` of a `⊎`-relabelling — which
`Machines.Tensor`'s `pureᴹ-∘`/`⊗ᵉ-pureᴹ`/`pure-∘ˡ`/`pure-∘ʳ` do outright — is
what makes the loop's one-pass dispatch writable at all.  That collapse is
object-polymorphic, so it is exactly the "`α`/`γ` have to be absorbed"
prerequisite `Morphism-∘` is priced as needing, now available.  Measured: the
wiring module is a 234 s warm check of which **219 s is one conversion**,
projecting `_∘_` out of `𝒢ₚ`'s G-construction record — a cost any consumer of
`𝒫.∘` pays once, with no lever on this side (the module header records the
restructure that was tried and was worse); everything the module itself defines
measures under 5 s.

Proved as of the second review, and both about the SIMULATOR the emulation
carries — `pov-carry`'s premise being direct agreement, which `_≤UC_` does not
hand over:

* `UC.Emulation.unit-grade` — at a grade both ends are blind to, an emulation
  *is* the direct agreement: the simulator collapses by `sub s ∘ g ≈ℰ g` and the
  inflating wire by the ancilla quantifier.  Two lines over `blind-grade`, with
  the two blindness facts as hypotheses (named, and priced, at the instance in
  `UC.Seam.Grounding`).
* `UC.Audit.audit-carry` — the graded carry: from `f ≤UC[ cs ] g` (an emulation
  whose simulator carries a query budget) and an ideal-side `AuditBound g ε`,
  the real side inherits `AuditBound f (λ q → ε (simCost q cs) + δ)` for any
  positive δ.  The mechanism is that `sub s` slides off the process and onto the
  test — `Et ∘ T₁ W (sub s)`, the same context with the simulator in front of it
  — so the simulator's queries are charged to the environment leg
  (`simCost q cs = q * (cs ⊔ 1)`) and the emulation's slack is what separates the
  two masses.  `UC.Approximate.Mass` is the one-sided reading it needs, and at
  the intended instance that is `Pr≤` with `_≈ₚ[_]_`'s left half
  (`UC.Seam.Audit`'s `massᴹ`), so nothing new is assumed.

  **Review correction: this does not close the graded UC→POV path.** An event
  must be interface-observable, but `AuditBound` quantifies over **all tests**
  and has no audit monitor parameter. A constant-`true` test forces `ε q ≥ 1`
  at the relevant certified budgets for trivial-grade protocol images. Thus a
  small `POVaudit` bound does not supply the premise of `audit-carry`.
  `AuditIsBounded` is now proved, but only extracts a watched-event bound from
  that stronger all-tests premise; it does not provide the missing converse.
  `TrajectoryFromAudit` and `pov-via-audit` connect concrete audit and trajectory
  bounds, not an inherited graded emulation to those bounds. The previous claim
  here that the path was “closed both ways” was false. `pov-carry` remains a
  direct-agreement transfer; `ChimericLedger.Carry.Emulᴸ` is literally `Agreeˢ`,
  not the inherited simulator-bearing UC relation.

Current status of formerly priced obligations (2026-09-11):

| statement | where | status |
|---|---|---|
| `ContextDominated` | `UC.Machine.Bridge` | PROVED by `UC.Machine.Dominated.dominated` |
| `EnvAsCtx`, `StratIsEnv`, `IotaBlind` | `UC.Seam.Grounding` | PROVED in `UC.Seam.Grounded` |
| `SubBlind` | `UC.Seam.Grounding` | REPAIRED and PROVED by `Grounded.subBlind`, with `SimTotal`; the old unrestricted version remains refuted by divergent simulators |
| `UnitGrade` | `UC.Seam.Grounding` | REPAIRED and PROVED by `Grounded.unitGrade`, with `TotalRun` premises on both processes; not an unconditional simulator collapse |
| `AuditIsBounded` | `UC.Seam.Audit` | PROVED in `UC.Seam.Audit.Bounded`; the all-tests premise mismatch above remains |
| `SaturatedRespects` | `UC.Saturated` | REPAIRED and PROVED by `saturated-respects`: the allowance is quantified before the slack, so `VanishingBound δ` genuinely carries it |

The saturation counterexample — a delayed leak after `2^n` queries, invisible
eventually at each polynomial allowance but of constant advantage at an
exponential one — refutes a single vanishing slack uniform over all `q`, and
the repaired forms therefore choose the slack AFTER the allowance. The grade is
now a parameter (`UC.Approximate.Grade`): `SaturatedBounded`/`SaturatedHit` are
the `_→0` instances and `SaturatedBoundedᴺ`/`SaturatedHitᴺ` the `Negligible`
ones, with `saturated-respects[_]` proving the invariance once, over the
grade's closure under sums. Family qualitative equality is still vanishing
advantage, and `absorb-negl` still concludes that same relation: a negligible
premise is not a negligible conclusion (`1/n` is vanishing but not negligible).
The negligible tier accordingly keeps its error witness — `UC.Saturated._≈negl_`
and `saturated-respectsᴺ`, whose carry premise is `NegligibleBound` — and
`UC.Family`'s negligible layer specifies what a graded `≈ℰ` would cost. A
generic saturated robust-property API and integration of family bound ingestion
into the inherited relation are still missing. See the
[review's completion goal](protocol-implementation-review.md) for the
monitor-aware, polynomial-budget, negligible-strength path to a genuine
end-to-end graded asymptotic UC→POV theorem.

### Budget accounting, as corrected

`Budget`'s `qb-T₁`/`qb-sub` land at `c ⊔ 1`, not `c`, and that is not
bookkeeping: the ancilla's own downward relay is a completed event an activation
from above must have deposited for, so a rate of zero cannot survive the
action.  `qbᵢ-wire` is where this is visible.

The same guard was missing one level up, and the second review's first finding
is that its absence is unsound rather than untidy.  A *context* was charged
`c * c′` — the test's budget times the closure's — and a closure with no
downward port certifies at `QB 0`: take the ancilla to be `unitᴵ`, and a
1-bounded test that spends its tick on one query to the plugged interface is
paired with `1 * 0 = 0`, so the witnessing strategy may make no queries at all
and cannot distinguish implementations the context distinguishes perfectly.  The
family-level `_≈ℰ[_]_` had the same product, evaluating a concrete bound at
`ε (κ i) 0`.

`UC.Budget.ctxBudget c c′ = c * (c′ ⊔ 1)` is the correction, used by
`UC.Machine.Bridge.ContextDominated`, by `UC.Family`'s `_≈ℰ[_]_` (levelwise, as `ctxQB`,
still polynomial by `poly-*`/`poly-⊔`) and by `UC.Audit.AuditBound`.  The honest
reading of the product is conservative: for a CLOSED context the test is what
controls crossings into the plugged process, the closure only supplying ancilla
and input responses, so `c` alone would already be a bound; the product is kept
for closures that do relay downwards and the guard is what makes it sound at
zero certificates.  The principled form is a port-specific bound — crossings of
the DISTINGUISHED hole rather than a product of two whole-hom budgets — and it
is priced, not built: it needs `QB` to be indexed by a port of the interface
(`QBᵢ`'s potential split per summand, ~120–200 LOC over `UC.QueryBound`) and
`Budget`'s four closure laws restated per port (`qb-T₁` becoming "the bypassed
port's rate is unchanged, the plugged port's is `c`"), after which `ctxBudget`
is replaced by the test's hole-rate alone and the closure drops out of the
statement.

### The vanishing layer, ported

`Data.Nat.Properties.Ext` (153, new), `Data.Nat.Poly`'s `poly-≤2^`,
`Data.Rational.Properties.Ext`'s `_/_` arithmetic and halving facts,
`ProbabilisticLogic.Distribution.Uniform`'s `archimedean`/`fromℕ-inv-pow-2`, and
`…Uniform.Decay` (115, new: the `_→0` closure rules and `poly-inv-pow-2-→0`)
come over from the reference arc unchanged — the four pre-images were
byte-identical at the merge base, so it is a clean additive port.  `Decay`'s
`_→0` is spelled to match `UC.Family._→0` on the nose, so `VanishingBound` is
inhabitable at a birthday-shaped numerator (`vanishing-bound`) as soon as one is
supplied.

Above it sits the **negligible** layer, because `_→0` is not the cryptographic
condition — `1/n` vanishes and is not negligible (proposal §3,
`docs/kb/frontier/15-probabilistic-uc-model.typ`).  Both are kept: the `_→0`
forms are what `absorb` actually spends, the negligible forms are what a
concrete security theorem is held to.

| statement | module | what it asks |
|---|---|---|
| `_→0` | `UC.Approximate` | convergence; `absorb` spends only this |
| `Negligible` | `UC.Approximate` | every polynomially magnified copy still vanishes — equivalently, eventually below every inverse polynomial |
| `Negligible⇒→0` | `UC.Approximate` | proved: negligible is the stronger of the two |
| `VanishingBound ε` | `UC.Approximate` | `ε(n, p n) →0` at every polynomial allowance |
| `NegligibleBound ε` | `UC.Approximate` | `ε(n, p n)` NEGLIGIBLE at every polynomial allowance — the §3 discipline; no slack uniform over arbitrary, possibly exponential, `q` |
| `NegligibleBound⇒VanishingBound` | `UC.Approximate` | proved |
| `CarriedNegligible ε` | `UC.Family` | the same, read at the allowance a context's two legs CARRY (`ctxQB` of two `PolyQB`s) |
| `carried-negligible` | `UC.Family` | proved: `ctxQB-poly` is the polynomial witness, so this is no extra assumption |
| `absorb-negl` | `UC.Family` | proved: `absorb` at the negligible hypothesis — and concluding the same vanishing `≈ℰ`, so the grade is spent, not inherited |
| `Grade`, `GradedBound` | `UC.Approximate` | the common shape of the two disciplines; `VanishingBound = GradedBound _→0`, `NegligibleBound = GradedBound Negligible` |
| `→0-+`, `Negligible-+` | `UC.Approximate` | proved: both grades close under sums, which is the whole arithmetic content of the saturation transfer |
| `_≈negl_` | `UC.Saturated` | `≈adv` with its error witness retained and `NegligibleBound`-graded; an equivalence, and the premise `saturated-respectsᴺ` consumes |
| `_≈ℰⁿ_` | `UC.Family` | the same move at the family layer: `absorb-negl`'s premise with its `ε` kept. An equivalence (`≈ℰⁿ-refl`/`-sym`/`-trans`) refining `_≈ℰ_` (`≈ℰⁿ⇒≈ℰ`), but NOT wired in as an `Observation`'s `_∼_` — that is a core-interface redesign, specified in the module |

`Negligible` is stated multiplicatively (`p n · s n` still vanishing) rather
than as `s n ≤ 1/p n`: it is the same condition, it reuses `Poly` and `_→0`
instead of a second ε-quantifier, and it keeps every nonzero-denominator side
condition out of the statement.  It also means `Decay.poly-inv-pow-2-→0`
already has the shape a negligibility witness for a `2⁻ⁿ`-sized bound needs.

### The `Dist⊥ → Dₚ` embedding

`Dp`'s header asserts that binary trees of rational coins realise every finite
rational distribution; `Dp.Embed` is that, and exactly: `embed` is the
right-nested cascade whose node at `(w , x)` flips `(w/M , R/M)` for `M` the mass
of the list from there on, so `choiceₚ`'s `q + r ≡ 1` holds with no
renormalization of the list and the recursion stays structural.  `Dist-ℚ`'s
non-negativity is spent twice — the two conditional weights, and the one place
the normalization is undefined (a zero-mass suffix, which then carries no mass
either, so `botₚ` is exact rather than convenient).

    embed-cum : (μ : Dist⊥ A) (P : A → ℚ)
              → Σ[ n ∈ ℕ ] ((m : ℕ) → cum (n + m) (embed μ) P ≡ E⊥ μ P)

at `n = 1 + |entries μ|` — an equality, not a domination, which is what
`PrAgree` compares.  The induction is divisor-free because it is stated scaled
by the mass (`mass-L xs * cum … ≡ lookup-L xs (maybeℚ P)`), so the normalization
cancels one node at a time.  `E⊥`/`maybeℚ` join `Pr₁⊥` in the expectation module
with `mb = maybeℚ bool→ℚ`, so `Pr₁⊥ μ` IS `E⊥ μ bool→ℚ`.  In the event
`PrAgree` did not need this: `Dp.Stable`'s `Stable-coin` reads a coin node as an
`E μ` directly, so the proof never leaves `Dₚ` for a `Dist⊥` it has to embed.
The embedding stands as the link between the two carriers, unspent.

### Eight perf findings (historical measurements, not current ceilings)

These measurements preserve the implementation history. The projection ceiling
and the abandoned `Cast`/`Laws` strategy are retired; absolute claims below such
as “at any heap” or “no lever” describe the then-tested route, not a current
impossibility result or a new benchmark.

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
  nothing (`UC.QueryBound.Certificate`, `Certified`).  The same medicine — every
  object implicit passed EXPLICITLY, so both sides of every field are one
  spelling — is what assembles `Gradingᴹ : GradingLawsᴹ → Grading 𝒫ᴵ` and
  `Budgetᴹ` (`UC.Machine.Grading`); unpinned, the assembly exhausts a 10 GiB
  heap.  One more finding on top: the pinned section INSIDE `UC.Machine` costs
  a measured 852 s against 74 s for the rest of the module, while split into its
  own module the two cost 74 s + 22 s — heavy assemblies get their own module.
* **The same inversion is what the seam is split for.**  Every occurrence of a
  `Proc`-typed argument whose interface is left implicit costs one of those
  inversions, ~1 GiB each: the seam's embedding and statements alone reach a
  3 GiB heap, and adding a proof over them exhausts 6 GiB.  Three measures
  together bring `UC.Seam` back to a normal check: interfaces are explicit in
  every definition, each observation of a process is named once
  (`ctxRunˢ`/`runˢ`) and used by name, and the two dependent layers move out —
  the arithmetic corollary to `UC.Seam.Carry` and the `Grading`-dependent
  statement to `UC.Seam.Grounding`, since instantiating the environment layer
  at a grading costs a budget of the same order.
* **An `≈ℰ` between machine composites cannot appear as a term's type at this
  instance, at any heap.**  Bisected while building the second review's
  simulator carry: at `Grading 𝒫ᴵ` the statements are cheap (`SubBlind`,
  `IotaBlind`, `UnitGrade` check in 9 s as `Set₁`s) but the identity
  application `h u v e = h u v e` over them exhausts 3 GiB, because `≈ℰ`
  unfolds through the observation's projections and η-expands `Observationᴹ`,
  whose `⟦⟧-resp-≈` drags the machine equality in with it.  Naming the
  intermediate, pinning the object implicits and spelling composition as the
  environment layer's own `_∘_` all fail to move it, and it is not the graded
  codomain either: the same statement at a *variable* of that type is 9 s.  The
  cure is not local — it is the `opaque` boundary or one-spelling discipline
  `Gradingᴹ` also waits for — so the reasoning moves to where nothing unfolds:
  `UC.Emulation.unit-grade` and `UC.Audit.audit-carry` are proved over an
  arbitrary `UCBase` and the instance modules only name their obligations.  This
  is the same medicine `UC.Seam.Agreeˢ` already takes by being spelled in the
  `Dₚ` vocabulary.
* **…and it is neither the transport nor the bundling.**  Measured again while
  reducing `StratIsEnv`: the closing `EnvAsCtx → StratIsEnv` does not return
  inside 300 s at 8 GiB, against 13 s for every statement in that file, in four
  spellings — inline `∼-cast`; the generic `≈ℰ-at` with both object implicits
  passed; `Dp.Advantage.≈ₚ[]-resp` against an observation-level obligation that
  mentions no machine equality at all; and the same with the three components as
  module parameters rather than record fields.  The `∼ ⇝ Agreeˢ` conversion is
  free on its own at a variable of that type, so what is left is the instance's
  unfolding under the application, and the cure is the same non-local one.
* **The `~1 GiB` inversion is a 200-second wall in `UC.QueryBound` too.**  The
  three trace-free budget laws are 29 s with every interface explicit and do not
  come back inside 200 s with them implicit; the certificate-level halves
  (`qbᵢ-T₁`/`qbᵢ-sub`) are 5 s each either way, because their interfaces are
  module parameters.  `BudgetLawsᴹ` IS now assembled, and the prediction held:
  its four fields take their interfaces implicitly, so filling them pays the
  inversion once per field — 27 lines that check in ~220 s, which is why
  `UC.QueryBound.Compose.Laws` is a module of its own.
* **"Name the observation once" survives all the way down to the example.**
  `Examples.ChimericLedger.Carry` applies the seam's `agreeToAdv` at the two
  concrete ledger systems and hands the result to the example's `pov-transfer`.
  Written as one term it does not finish in 1750 s; with the advantage named
  (`advᴸ`) and `pov-carryᴸ` built on the name, the module is a **16 s** warm
  check.  Bisected: the STATEMENT (`Emulᴸ`, the `Agreeˢ` at the two machine
  images) is cheap and so is `advᴸ` — only the seam-as-a-subterm is not.  This
  is `UC.Seam`'s own discipline, and it does not stop at the seam's boundary.

* **A `Monoidal` law costs ~470 s to RECEIVE and nothing to PLUG.**  This is
  the finding that retired the `Cast`/`Laws` cone, and it is four measurements
  in isolation, warm, `-M8G -H1G`.  `associator.isoʳ` at three interface
  objects, checked against its own type written out verbatim in 𝒢's *public*
  vocabulary, is **470 s**; the type on its own is free; the SAME law at
  *variable* 𝒢-objects is **468 s**, so it is neither the objects nor their
  concreteness; and `UC.Core.Standard.gradingᵗ (𝒢ₚᴹ 0ℓ)` — all eight grading
  laws at the machine bundle — is **363 ms**.  The asymmetry is that a
  `Monoidal` law is stated with the record's own `private` `_⊗₀_`/`_⊗₁_`
  abbreviations, which no consumer can name; a written-out type therefore
  mismatches on a subterm sitting under a G-tensor, and the mismatch is settled
  by reducing both composites through the ⊕-trace.  `gradingᵗ` plugs each law
  into a `Grading` field whose type is DERIVED from it and writes none out, so
  nothing is ever compared.  Two corollaries.  (i) `Grading` is our own flat
  record, so once a law has been laundered through it the statement is spelled
  in public vocabulary and is cheap to handle — which is why the grading is
  taken on 𝒢's objects and `Iface` is kept as vocabulary only; re-presenting
  the same free record on `Iface` objects was measured at the same wall
  (>1500 s).  (ii) The rule generalizes: state nothing that must receive such a
  law.  Earlier readings of this cost as an object-SPELLING artifact were
  partial — `𝒫._∘_ g f` against `𝔾._∘_ g f` at objects spelled alike is 11 s,
  at objects spelled differently 525 s, and that object comparison alone, with
  no composite around it, is 11 s — the spelling mismatch is one way to trip
  the same reduction, not its cause.

### Compatibility with the inherited MD line (historical account)

**Current correction:** the MD consumers have since been ported and superseded
legacy modules deleted. The following alongside/unchanged account records the
earlier M3 stage only; it is not the state at `6256a140`.

The old UC modules are all still consumed by inherited code:
`MachineAxioms`, `FamilyCategory`, `VanishingTV`, `StandardTV` and
`OutputOnly` by `Machine/Probabilistic/Model` and `Examples/MerkleDamgard{,/UC}`;
`UCSetup`/`Abstract{,2}`/`Standard{,2}` by the `RandomOracle`/`RelSetup` line.
None was edited: M3 is built **alongside** them, under `CategoricalCrypto.UC.*`,
so the MD line is bit-for-bit unaffected.  Superseding them is a deletion pass
once the MD line is replayed onto this layer, and the mapping is one-to-one —
`MachineAxioms` → `UC.Core` + `UC.Budget` + `UC.Approximate`,
`FamilyCategory` → `UC.Family`, `VanishingTV` → `UC.Environment` + `UC.Family`'s
ingestion half, `StandardTV` → `UC.Machine`, `OutputOnly` →
`UC.Machine.Bridge` + `UC.Seam`.

One module of M2 changed: `Protocol.Machine`'s `runᴹFrom` now calls a named
continuation `resumeᴹ` instead of a `where`-local one, extensionally the same
step, so that `UC.Machine.Run` can quantify over it.  `Protocol.Machine.Pin`
still computes both verdicts by `refl`.

### Assumption ledger

The historical hatch census was 21 before and after (the M1 baseline), not a
fresh verification here. `Machines.Iteration.Elgot` and
`Machines.Trace.Remaining` are discharged at the intended base, as are the
model's Grading/Budget/UCBase/Mass and inherited model/family setup constructions.
Generic parameters (including family `κ` cofinality) remain explicit; they are
not missing instance proofs. The table above now consists of proved theorems
throughout, `SaturatedRespects` included since its quantifier repair.

The remaining premises and gaps must not be hidden by an empty-hatch ledger:
repaired `SubBlind` needs `SimTotal`, `UnitGrade` needs `TotalRun`, and
`totalRun-morphism` needs protocol totality; `Birthday.target` needs injective
serialization. `AuditBound` is an all-tests premise, not an audit-event bound.
The saturation quantifiers and negligible-strength mismatch require redesign,
and robust/family integration is missing. None of these gaps is discharged by
the absence of postulates or holes.

`UC.Approximate.Mass` is a new hypothesis in form only: it is one field with
content (an agreement implies ε-domination of the budgeted masses at every
positive slack) and the intended instance discharges it by one `proj₁`
(`UC.Seam.Audit.massᴹ`).  It exists because
`Observation` deliberately compares observations without valuing one, which is
what keeps it inhabited at `Dₚ`, while an audit-form statement bounds a single
observation.

## M4: the UC setup at the machine model (7 files, 440 LOC)

The maintainer's ruled direction, executed: **no parallel UC definition in this
cone.** The abstract theory is `CategoricalCrypto.UCSetup` + `Abstract2`,
reached through `Standard2.StdUC`, and the model inherits `_≈ᵁ_`, `_≤UC_`,
`≤UC-refl`, `dummy-complete`, `≤UC-trans`, `UC-compose` and `≈ᵁ⇒≈ℰ` **already
proved**. Semantic target: `docs/kb/frontier/15-probabilistic-uc-model.typ`,
§§1–2. Root: `CategoricalCrypto.UC.Model`.

| module | LOC | warm | role |
|---|---:|---:|---|
| `…UC.Model.Seal` | 95 | 8.7 s | `opaque 𝔾ᵒ = 𝒢ₚᴹ 0ℓ`, `∣𝔾ᵒ∣`, and the coercions `sealᵒ`/`ifaceᵒ`/`procᵒ`/`unprocᵒ`/`≈ᴹ⇒≈ᵒ`/`≈ᵒ⇒≈ᴹ`/`⊗ᵒ`/`gradedᵒ`/`unprocᵒ-∘` |
| `…UC.Model.Observation` | 80 | 8.7 s | `Ωᵒ`/`𝟘ᵒ`, `Test`/`Closure`, `Obs` (the one-ask closed run), `_∼ᴼ_`, `≈ₚ⇒∼ᴼ`, `∼ᴼ-resp`, `obs-resp` |
| `…UC.Model.Environment` | 64 | 8.7 s | `_≋_` and `≋-isEquivalence`, `≈ᵒ⇒≋`, `ℰ₀`, `ℰᵒ` — the presheaf, laws proved |
| `…UC.Model.Setup` | 20 | 9.2 s | `open StdUC 𝔾ᵒ ℰᵒ public` — nothing else |
| `…UC.Model.Pin` | 92 | 9.1 s | the six application-site shapes, `relayᵒ`, `relay-emulates`, `relay-compose` |
| `…UC.Model.Reading` | 76 | 9.2 s | `_≈ᴬ_`, `≈ᵁ⇒≈ᴬ`, `≈ᴬ⇒≈ᵁ`, `≈ᵁ⇔≈ᴬ` — proposal §2's displayed form, proved |
| `…UC.Model.Unit` | 129 | 8.8 s | `AnyEnvironment` (the metatheory is blind to the closure object), `Interconvert` (what an empty-object iso would buy) |
| `…UC.Model.Bridge` | 218 | 9.6 s | `observationᵒ`/`ucBaseᵒ`, `≈ℰᶜ⇔≈ᵁ`, `≤UCᶜ⇔≤UC`, `_≈ᴳ_` and `≈ᴳ⇔≈ℰᶜ`, and the three instruments `≈ᴳ-at`/`blind-gradeᵁ`/`unit-gradeᵁ` |
| `…UC.Model.Enrichment` | 53 | 9.6 s | `budgetᵒ` (transported along `sealᵒ`) and `massᵒ` — `UC.Audit`'s two enrichment parameters, supplied |
| `…UC.Model` | 40 | 8.8 s | the cone root and its orientation |

Plus 21 lines in `Categories.Functor.Monoidal.CurriedTensor.Properties`
(`sub-⊗`, `return-λ⇐`, `ext-⊗`, `μ-α⇐`, `μT₁-α⇐`, next to the existing
`T₁-⊗`): the curried tensor's graded triple read back in the monoidal
vocabulary. All five are generic in the monoidal category, which is exactly why
they are usable **through** the seal — a consumer that reasoned by unfolding
`sub`/`μ`/`T₁` at `𝔾ᵒ` instead would have to see inside it.

All `--safe --without-K --guardedness`. Escape-hatch grep 21 before and after.

### The recipe (historical measured guidance)

Every line below is a measured fact from `spike-stduc-perf`
(`src/CategoricalCrypto/Spike.agda` carries the table); deviate only with a new
measurement.

1. **Seal the whole `MonoidalCategory` bundle**, one `opaque` definition
   `𝔾ᵒ = 𝒢ₚᴹ 0ℓ`. Sealing only the `monoidal` field is 5.7× *worse* than
   sealing nothing; passing a re-assembled `record { U = …; monoidal = … }`
   OOMs at 8 GiB.
2. **One spelling of the index.** `𝔾ᵒ` is the only name the setup is given and
   `∣𝔾ᵒ∣ = MonoidalCategory.U 𝔾ᵒ` is defined once from it.
3. **Export every coercion from inside the `opaque` block** — the only scope
   where the seal is transparent. A consumer then needs no `unfolding`.
4. **`gradedᵒ` is not optional.** The seal hides `_⊗₀_`, so `A ⇒ T₀ X B` cannot
   be met by a machine on the interface sum without a coercion out of the
   block; `⊗ᵒ` is the same fact as an object equation.
5. **Three modules, not one**: the seal, then `open StdUC`, then statements.
6. **A concrete presheaf is fine.** `ℰ` need not stay a module parameter,
   because `ifaceᵒ` names objects of the seal without breaking it.
7. **Without a seal**, the two cures that remain are to apply an `Abstract2`
   lemma eta-expanded *and* pin the applied lemma's implicits: together
   158.8 s → 33.4 s. With the seal neither is needed.

### Measured costs (historical)

| experiment | transparent | sealed |
|---|---:|---:|
| `open StdUC` at `𝒢ₚᴹ 0ℓ`, setup only | OOM at 12 GiB in 50 s | 8.7 s |
| the six application-site shapes | OOM (12 GiB) at `𝒢ₚᴹ`; 158.8 s at `ℳₚ` | 9.1 s |
| the test presheaf, its laws, and `StdUC` on it | not attempted | 8.7 s + 9.2 s |
| the operational reading `≈ᵁ⇔≈ᴬ` | not attempted | 9.2 s |

The startup-plus-interface-loading floor is ~7 s here, so **every module of M4
is at the floor**: nothing in the model costs measurable elaboration.

The spike flagged the setoid quotient as extrapolated rather than measured,
since its own `ℰ` was the representable `Hom[-, Ω]`. Measured: it is free.
Behind the seal a test is a stuck `𝔾ᵒ [ A , Ωᵒ ]`, `Obs` is `unprocᵒ` (an
opaque function) followed by the machine layer's own run, and the three presheaf
laws are one `≈ᵒ⇒≋` each — so the quotient never gives the elaborator an object
meta to solve, which is the only thing the transparent index was ever expensive
about.

### The operational reading

For `f, g : A → X ⊗ B`, `UC.Model.Reading` proves `f ≈ᵁ g` **equivalent** to

    ∀ Y, e : Y ⊗ (X ⊗ B) → Ω, m : 𝟘 → Y ⊗ A.
      Obs (e ∘ (id ⊗ f) ∘ m) ∼ Obs (e ∘ (id ⊗ g) ∘ m)

which is the proposal's display. It is the stated bracketing shuffle and nothing
more: `μ Y X ∘ T₁ Y f ≈ α⇐ ∘ id ⊗₁ f` (`μT₁-α⇐`) re-brackets the test's domain,
and the two quantifications over tests correspond under `α⇒`/`α⇐`, whose
cancellation is `associator.isoʳ`. Consequences worth naming:

* The ancillas of the graded context closure **are** the ancillas of the
  displayed experiment. No second environment construction, and in particular
  no ancilla inside the presheaf's carrier — which is the one structural
  difference from `VanishingTV.ℰᵗᵛ`, whose carrier is a dependent pair
  `(Y , test on Y ⊗ A)` and which is why that layer needed a `SameTV` datatype
  and a `substCl` transport.
* `GradeStable` is **not** assumed, and no claim is made that `_≈ᵁ_` agrees with
  every presentation in `Abstract`. `≈ᵁ⇒≈ℰ` is inherited; its converse is not
  used anywhere in M4.

### The dictionary, and what it supersedes (implementation history)

`…UC.Machine.Dictionary` (374 LOC, warm 50.5 s) reads the direct relays of the
parallel `UC.*` stack as the MONOIDAL spellings of the same processes, at the
TRANSPARENT machine layer — these are `𝒢ₚ`-hom equalities, not statements behind
the seal. Nothing in `UC.*` is edited or rewired; the module only adds.

| relay | monoidal spelling | status |
|---|---|---|
| `a⇒ᴵ` | `associator.to` at `⟦X⟧ᴵ,⟦Y⟧ᴵ,⟦A⟧ᴵ` | proved (`a⇒-α⇐`) |
| `a⇐ᴵ` | `associator.from` | proved (`a⇐-α⇒`) |
| `T₁ᴵ Y f` | `id ⊗₁ᴳ f` | proved (`T₁-⊗₁`) |
| `subᴵ s` | `s ⊗₁ᴳ id` | proved (`sub-⊗₁`) |

Each proof is the same shape: `mid` and every structural machine is `pureᴹ`
(`pureᴹ-∘`, `⊗ᵉ-pureᴹ`, `pureᴹ-id` collapse the whole conjugation into `pureᴹ`
of one base map), `pure-∘ˡ`/`pure-∘ʳ` absorb the two `mid`s into the step, the
new generic `⊗ᵉ-pureˡ`/`⊗ᵉ-pureʳ` collapse the pure side's trivial state factor,
and only the residual step equality is elementwise — four sum cases, because
`T₁ᴵ`/`subᴵ` are defined by pattern matching. `GConstructionTrace` need not be
imported: `mid` can be written out in `pureᴹ`s by hand.

Hence the supersession map for `GradingLawsᴹ`'s eight fields:

| field | status | why |
|---|---|---|
| `T₁-resp-≈` | corollary (`T₁-resp-≈ᴹ`) | `𝔾.⊗.F-resp-≈` |
| `T₁-id` | corollary (`T₁-idᴹ`) | `𝔾.⊗.identity` |
| `sub-resp-≈` | corollary (`sub-resp-≈ᴹ`) | `𝔾.⊗.F-resp-≈` |
| `sub-id` | corollary (`sub-idᴹ`) | `𝔾.⊗.identity` |
| `T₁-∘` | corollary (`Laws.Relay.T₁-∘ᴹ`) | `𝔾.⊗.homomorphism` |
| `sub-∘` | corollary (`Laws.Simulator.sub-∘ᴹ`) | `𝔾.⊗.homomorphism` |
| `a-isoˡ` | corollary (`Laws.Assoc.a-isoˡᴹ`) | `𝔾.associator.isoʳ` |
| `a-nat` | corollary (`Laws.Nat.a-natᴹ`) | `𝔾.assoc-commute-to` |

The split is exactly the one `UC.Machine.Grading`'s own note predicted: the four
that land free are the trace-free ones, and the other four each compare a
`𝒫ᴵ`-COMPOSITE, hence the ⊕-trace. Those four are now proved too, and what
closes them is not a lemma but a way of ARRANGING the conversion.

### The gate, diagnosed and closed (historical; projection ceiling retired)

M4 left a measured reproducer — `𝔾.associator.isoʳ` alone, at
`⟦X⟧ᴵ,⟦Y⟧ᴵ,⟦A⟧ᴵ` with every implicit pinned, still running after 900 s at
12.8 GiB — and named an `opaque`-sealed re-export as the cure. Re-measured, the
diagnosis is different and the seal is NOT the cure.

* The reproducer is not divergent, only slow: the same projection now checks in
  **418 s** (`UC.Machine.Cast.Assoc`). M4's kill at 900 s was a kill, not a
  verdict.
* What costs is comparing two 𝒢-COMPOSITES that are not SYNTACTICALLY equal.
  Both sides then reduce to the ⊕-trace, and leaves that differ — even by one
  δ — are normalized inside it. 400–450 s per comparison, reproducibly, and it
  is the LEAVES that decide, not the object spelling: with the two factors left
  VARIABLE the trace has variable leaves and the comparison stays structural
  (`UC.Machine.Cast.*`, one `Equiv.refl` per composite SHAPE).
* Hence the recipe. A law is `Dictionary bridge ○ cast ○ 𝒢-law`, whose junctions
  are all syntactic except the single one against the borrowed law — so ONE
  𝒢-composite conversion per module, and one law per module.
* An `opaque` seal does not help. Inside the block the seal is transparent, so
  the crossing costs the same; outside it the crossing cannot be expressed at
  all. M4's seal earns its keep for a setup built ON `𝔾ᵒ`, which never crosses
  back down to `𝒫ᴵ`.

`𝔾.assoc-commute-to` is the exception that fixes the budget: it has TWO
composite ends and neither is writable in a spelling of ours (its `α⇐` and
`_⊗₁_` are the `Monoidal` record's private abbreviations), so it takes a module
of its own (`…Laws.Nat.Square`), the first module of the cone above 900 s.

| module | LOC | warm | role |
|---|---:|---:|---|
| `…UC.Machine.Cast.Tensor` | 68 | 997 s | `∘ᴳ-T₁`, `∘ᴳ-sub` — the two `⊗.homomorphism` shapes |
| `…UC.Machine.Cast.Assoc` | 31 | 418 s | `∘ᴳ-α` — the `associator.isoʳ` shape |
| `…UC.Machine.Cast.Nat` | 41 | 822 s | `∘ᴳ-nat⇒`, `∘ᴳ-nat⇐` — the two sides of the naturality square |
| `…UC.Machine.Laws.Relay` | 57 | 489 s | `T₁-∘ᴹ` |
| `…UC.Machine.Laws.Simulator` | 56 | 495 s | `sub-∘ᴹ` |
| `…UC.Machine.Laws.Assoc` | 49 | 423 s | `a-isoˡᴹ` |
| `…UC.Machine.Laws.Nat.Square` | 51 | 984 s | `α-natᴳ` — `assoc-commute-to` re-spelled |
| `…UC.Machine.Laws.Nat` | 86 | 1463 s | `a-natᴹ` |
| `…UC.Machine.Setup` | 41 | 2881 s | `gradingLawsᴹ`, `gradingᴹ`, `ucBaseᴹ` |

`…UC.Machine.Setup` pays the toll four more times: `GradingLawsᴹ`'s field
types are written with `UC.Machine.Grading`'s own `private module 𝒫`, the law
modules' with theirs, and for the four trace-touching fields the two spellings
differ by exactly that alias over a `𝒫ᴵ`-COMPOSITE — four more conversions.

**All nine modules above are now DELETED**, and the diagnosis that retired them
is perf finding 8 below: the price is not the objects, not the aliases and not
the comparison, but the act of WRITING OUT a type that has to receive a
`Monoidal` law.  Four of the nine were re-measured on the 2026-09-06 machine
before deletion, ~1.24x the numbers above — `Cast.Assoc` 520 s, `Cast.Nat`
1012 s, `Cast.Tensor` 1024 s, `Laws.Nat.Square` 1261 s — so the cone's real
total was ~3.0 h.  What replaced it is `UC.Core.Standard.gradingᵗ (𝒢ₚᴹ 0ℓ)`,
which never writes such a type out and costs 363 ms, plus four re-basings in
`…UC.Machine.Grading` at 5.9 s each.

The cone is a measured ~1.9 h of elaboration, all of it in the conversions
above; nothing in it is a proof step a reader would recognize as work. It is the
price of the machine layer and the 𝒢-monoidal layer being two spellings of one
category, and the only structural fix is to stop having two — to present `𝒫ᴵ`
as the reindexing of `𝒢ₚᴹ`, so that no crossing exists to pay for.

Two smaller findings worth carrying forward:

* **The pinning discipline extends to the borrowed 𝒢-law's own implicits.**
  `T₁-resp-≈ᴹ` costs +83 s with `𝔾.⊗.F-resp-≈`'s implicits inferred and +10 s
  with them given. Same failure mode as the one `UC.Machine.Grading`'s header
  documents, and mechanical to apply.
* **`_⊗₁ᴳ_` being trace-free is what makes the dictionary affordable.** Every
  proof that stays inside `⊗₁ᴳ` is 10–30 s; the moment a 𝒢-composition's
  *proof* appears the cost is unbounded.

### What remains (2026-09-11 review)

| item | where | status |
|---|---|---|
| `ifaceᵒ unitᴵ ≅ 𝔾ᵒ`'s monoidal unit | `UC.Model.Observation` header | not proved; a G-composite is a trace, so `isoˡ` is not the one-line argument the bijection of empty types suggests. Nothing depends on it — `ℰᵒ` is a presheaf for either family of closures |
| whether the model satisfies `GradeStable` | — | still open, and now known to be the ONLY gap between the two theories' agreements: `UC.Model.Bridge._≈ᴳ_` is the grade-stable refinement the core's relation already is, `GradeStable` is what would collapse it onto the bare `_≈ℰ_`, and `Abstract2.bridge` is the one inherited result unavailable without it (plan finding F2) |
| the confidential-ledger refinement | proposal §4 | out of M4's scope |
| `Morphism-∘`, `PrAgree`, `Adequacy`, `ContextDominated` | protocol/machine seam | PROVED, no longer remaining obligations; composition is not identity preservation |
| grounding and `AuditIsBounded` | `UC.Seam.Grounded`, `UC.Seam.Audit.Bounded` | PROVED with repaired totality premises for grounding; audit extraction does not repair the all-tests premise |
| `TrajectoryFromAudit`, `Birthday.target` | `Examples.ChimericLedger.Trajectory`, `…Birthday` | PROVED; birthday target conditional on injective serialization |
| monitor-aware graded carry | `UC.Audit` / ledger seam | OPEN semantic repair: an all-tests `AuditBound` cannot be supplied by a small `POVaudit` bound |
| saturation invariance | `UC.Saturated` | PROVED after repair: the slack is chosen per polynomial allowance, and the grade is a parameter, so the advertised `Negligible` tier is stated and carried alongside the `_→0` one |
| robust asymptotic integration and final UC→POV theorem | inherited family setup / ledger consumer | MISSING generic saturated robust API and bound-ingestion integration into the inherited relation; `Emulᴸ = Agreeˢ` is not a graded UC theorem. Completion goal: [implementation review](protocol-implementation-review.md) |

Whether the M4 cone should supersede the `UC.*` stack was left as the
maintainer's call here.  It has been ruled: **it should**, and
`docs/stduc-supersession-plan.md` is the plan and the execution record.  So the
last sentence of the paragraph above no longer holds — `UC.Model.Bridge` names
`UC.Core` and `UC.Emulation` deliberately, to identify the two theories, and
`UC.Seam.Grounding`/`UC.Seam.Audit` have moved off the hand-rolled core onto
this cone.
