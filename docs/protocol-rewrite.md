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
| M2: `Mealy (Kl Dₚ)` + GConstruction + `morphism`/`Pr-agree` | not started |
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

## M2/M3 pointers

M2 harvests: `spike/pov-dp` (all four Elgot base laws PROVED at Dₚ; the
independent-budgets trick), `spike/elgot-trace` (trace from `iter`, yanking,
`trace-∘ˡ/ʳ`, the `Assemble` shape with 4 residual laws), `docs/spike-pov-dp-verdict.md`
(per-law prices). M3 harvests: `sfunm-setoid`'s ℰᵗᵛ/StandardTV statements, the α
query-bound + counting theorem, restated over `Iface` with the ancilla parameterized
(no K island). Assumption ledger of M1: `ser`(+`ser-inj` at `AtBirthday`) — module
parameters, maintainer-sanctioned; zero postulates.
