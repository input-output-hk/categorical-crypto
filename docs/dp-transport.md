# The raw transport: `Dₚ` runs as `Dist-ℚ` kernel runs

Branch `dp-transport`, off `protocol-rewrite` at `2fcac147`.

[`docs/graded-bridge.md`](graded-bridge.md) stops at two items. (d)
`closed-kernel` — the transport between the two probability layers at RAW
machines — is not the statement it was written as, for three reasons that branch
lists. (f) ROCommitment's `raw-emulation` is unreachable on top of (d). This
branch builds the transport itself, generically and in full, inhabits its one
hypothesis at a machine that really samples, and says exactly what is still
between it and the RO commitment's machine-level bound.

Everything below is a checked term unless it is in "Not delivered". Hatches in
`src/` stay at their baseline of zero: the
`postulate|TERMINATING|primTrustMe|\{!` grep counts 16 hits before and 16 after,
all of them the words "postulate-free" in inherited comments.

## Route T, and why Route A is not available at this example

The brief offers a transport route and an audit route. **Route T is taken.**
Route A — state binding failure as an `AuditEvent` and let
`UC.Seam.Audit.Context.extractᵍ` apply the way `hf-pr-bound` does — is dead at
ROCommitment for two independent reasons, and neither is a proof-work reason.

**A1. `extractᵍ`'s conclusion is vacuous at `Honᴵ`.** It bounds
`Pr≤ n (runᴹ closedᵍ e)` for `e : Strat (Neg Honᴵ) (Pos Honᴵ)`, and
`Examples.ROCommitment.Honᴵ` is `HonA ⇿ ⊥`: `Neg Honᴵ` is empty, so every such
`e` is built from `out` and `coin` alone and `runᴹ M e` never reaches `M`'s step.
The resulting bound holds of a system that reports a binding failure on every
activation exactly as it holds of the real one. This is
`docs/graded-bridge.md`'s obstruction (i) seen from the audit side: at this
example the DRIVER is the corrupted committer, which sits at the grade, and
`runᴹ` drives a closed system through its codomain.

**A2. Nothing replaces `real-≤UC`.** The brief asks what does, and the answer is
that nothing available does. `UC.Audit.audit-carry` — the only route from an
ideal-side `AuditBound` to a real-side one — consumes `_≤UC[_]_`, whose
`emulate` field is an exact `≈ℰ`. ROCommitment's emulation is approximate by
construction, and `Game.extraction-bound` is a `Dist-ℚ` advantage between two
reactive kernels, not an `≈ℰ` between two homs. The ε-carrying analogue of
`_≤UC[_]_` is `docs/fcom-extraction.md` item 3, and it does not exist;
`docs/uc-presheaf-preservation-plan.md` §1 decision 1 is why this branch does not
invent it. A direct real-side `AuditBound` with no emulation in it would still
run into A1.

So Route A needs two core additions (a grade-driven closed run, and an ε-carrying
`≤UC[ ]`) before any proof work starts, where Route T needs neither: the
transport is a statement about `runᴹ` and `runWith⊥`, both of which already
exist.

## What the transport is

### `ProbabilisticLogic.Dp.Settle` — the `Dₚ` half, generic

`Dp.Stable` says a `cum` family has stopped moving AT ONE TEST. That is enough
for `prAgree`, whose inner induction is on an inductive `Calls` tree, and it is
not enough for a raw machine, whose step is an arbitrary `Dₚ` computation: a
bind junction needs the value's own reading, uniformly in the test.

```agda
Null  : Dₚ A → Set                            -- Settle.agda:51
Halts : ℕ → Dₚ A → Set                        -- :56  (mutual with `HaltsL`)

record Settles (n : ℕ) (d : Dₚ A) (ν : Dist⊥ A) : Set where   -- :143
  field halts : Halts n d
        score : (Q : A → ℚ) → NNF Q → cum n d Q ≡ E⊥ ν Q
```

`Halts (suc n) d` is `Null d ⊎ ((c : Bool) → HaltsL n (br d c))`: every branch
has reached a value within `n` steps, or the residue carries no mass. The `Null`
disjunct is not a convenience — `botₚ` never halts and never scores, and an
off-protocol activation's machine image IS `botₚ`, so a run that reaches one must
still settle. It is also what makes `Halts` monotone in the budget, which the
bind lemma spends.

The family is closed under exactly the four ways a `Dₚ` run is built:

| lemma | line |
|---|---|
| `Settles-return` | Settle.agda:177 |
| `Settles-bot` | :181 |
| `Settles-coin` | :185 |
| `Settles-bind` / `Settles-bind⋆` | :229 / :243 |

`Settles-bind` is the content. It is two mutual inductions on the halting budget
— one for `Halts (n + j) (d >>=ₚ f)`, one for the `cum` identity
`cum (n + j) (d >>=ₚ f) Q ≡ cum n d (λ p → E⊥ (κ p) Q)` — carrying the
continuations' settling over `Dp.Supp`, the depth-`n` support `Dp.uniformize`
already maxes budgets over. `Settles-bind⋆` is the consumer's form: the
continuation settles at every value at a budget of its OWN, and the uniformizer
supplies the single `j` the induction needs. Nothing anywhere is a global fuel.

`Settlesᵀ n d μ = Settles n d (Dmap just μ)` (:256) is the no-divergence case,
the form a closed game's kernel is written in, with its own four closure lemmas
and `Settlesᵀ-tag` (:289) for the relabelling a machine step performs on its
kernel's answer.

`Settles` is a RECORD and `Settles-resp` takes both values EXPLICITLY, and
neither is stylistic: `Dist-ℚ` is a record and `E⊥` projects it, so where the
type unfolds to a `Σ` the value is compared through `E⊥`, a value left implicit
eta-expands into entries and weights, and unification blocks on a weight. With a
rigid head and explicit values every such meta is solved by the type.

### `ProbabilisticLogic.Dp.Settle.Uniform` — the sampler settles

```agda
uniformₚ-settles : (n : ℕ) → Σ[ i ∈ ℕ ] Settlesᵀ i (uniformₚ n) (uniform-Vec n)
```

Four lines off `Settlesᵀ-bind⋆`. `Dp.Uniform.uniformₚ` is the cascade of `n`
fair `coinₚ`s and `uniform-Vec n` is the distribution; this says the cascade
halts after them and scores it exactly. It is what makes the transport apply to a
machine that really samples rather than only to a deterministic one.

### `CategoricalCrypto.Protocol.Machine.Raw` — the machine half, generic

```agda
StepSettles : Set                                       -- Raw.agda:61
StepSettles = (m : MC.St M) (q : Neg B)
            → Σ[ n ∈ ℕ ] Settles n (MC.step M (m , inj₂ q)) (Dmap⊥ ansᴹ (K m q))

rawAgree : (m : MC.St M) (d : Strat (Neg B) (Pos B))    -- :67
         → Σ[ n ∈ ℕ ] Settles n (runᴹFrom M m d) (runWith⊥ K m d)

rawRun   : (d : Strat (Neg B) (Pos B))                  -- :106
         → Σ[ n ∈ ℕ ] Settles n (runᴹ M d) (σ₀ >>=⊥ λ m → runWith⊥ K m d)

rawPr    : (b : Bool) (d : Strat (Neg B) (Pos B))       -- :112
         → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n + i) (runᴹ M d) (indᵇ b)
                                ≡ E⊥ (σ₀ >>=⊥ λ m → runWith⊥ K m d) (indᵇ b))

rawKernel : StepSettles → (b : Bool) (s : S) (d : Strat (Neg B) (Pos B))
          → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n + i) (runᴹFrom M (emb s) d) (indᵇ b)
                                 ≡ E (runWith resp s d) (indᵇ b))   -- :126
```

at `M : Proc unitᴵ B` an ARBITRARY closed machine and
`K : St M → Neg B → Dist⊥ (St M × Pos B)` an arbitrary step kernel. `rawPr` is
`Protocol.Machine.PrAgree`'s shape — a budget past which the `cum` family is the
kernel run's verdict probability, at either verdict — with the protocol image
replaced by `StepSettles`. `rawKernel` is the same against a TOTAL kernel in
`Dist-ℚ` along a state embedding, which is the form a closed game's bound is
stated at; the embedding half is `Interaction.runWith⊥-emb`, reused verbatim.

This is the brief's Route T lemma, and it is fuel-indexed exactly where the brief
says it has to be: `StepSettles` carries one fuel per activation, because the
trace loop inside a composite's step has no protocol-image structure to induct
on. `prAgree` is untouched and still proves the protocol-image case its own way.

**What the hypothesis costs and what it buys.** `StepSettles` is a genuine
hypothesis, not a repackaging: at a composite whose upper factor is an arbitrary
adversary machine the loop between the two factors need not terminate, so no
unconditional version of `rawAgree` can exist. Making the fuel a hypothesis is
what keeps `Raw.agda` free of `{-# TERMINATING #-}` and free of a global clock.

### `Examples.ROCommitment.Transport` — the hypothesis, inhabited

```agda
resK  : RState → Neg Resᴵ → Dist⊥ (RState × Pos Resᴵ)        -- Transport.agda:66

resKᵀ-fetchT : (s : RState) (x : Pt)                         -- :79
             → resKᵀ s x ≈Mℚ (fetchT (_, proj₂ s) (proj₁ s) x
                              >>=ᴹ λ u → return-ℚ (proj₁ u , digᴿ (proj₂ u)))

resource-settles : StepSettles resource resK                 -- :179

resource-run : (b : Bool) (d : Strat (Neg Resᴵ) (Pos Resᴵ))  -- :196
             → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n + i) (runᴹ resource d) (indᵇ b)
                                    ≡ E⊥ (runWith⊥ resK ([] , nothing) d) (indᵇ b))
```

The RO commitment's own lazily sampled resource. On the oracle half `resK` IS
`Examples.ROCommitment.Oracle.fetchT` (shared by both halves since `small-hoists`) relabelled onto `Resᴵ` — `resKᵀ-fetchT` is
that identification, and it is the same kernel the closed game's bound is proved
about — and the fresh branch draws `uniformₚ k`, so `uniformₚ-settles` is what
makes the activation settle. So the
`Dₚ` closed run of the concrete resource IS a `Dist-ℚ` kernel run, at every
strategy, with no protocol image anywhere: `docs/fcom-extraction.md` item 1(d)'s
"there is presently no route from `runᴹ (…)` in `Dₚ` to `runWith …` in `Dist-ℚ`
for these machines at all" is no longer true of the layer, only of the composite.

`resK` is `Dist⊥`-valued rather than `Dist-ℚ`-valued and that is not slack: two
cell activations are off-protocol (a second `putᴿ`, a `getᴿ` before one) and the
machine's image of those is `botₚ`, where the game's `respR` answers `idleR`.
That mismatch is residual 2 below.

## Generic versus example-specific

| module | generic? |
|---|---|
| `ProbabilisticLogic.Dp.Settle` | generic — halting and settling in `Dₚ`, no machine in sight |
| `ProbabilisticLogic.Dp.Settle.Uniform` | generic — the uniform cascade |
| `CategoricalCrypto.Protocol.Machine.Raw` | generic — at any closed machine and any kernel |
| `Examples.ROCommitment.Transport` | the example: its resource's kernel and the settling of it |
| `UC.Model.Enrichment` (+`procᵘ`, `qbᵘ`) | generic — two seal coercions, moved (below) |

Nothing generic mentions an example, and the example restates no generic fact.

## The `qbᵘ` move, and why it was not a cut-and-paste

`QUALITY-REVIEW.md` §Resolved (graded-bridge) recorded `qbᵘ`'s natural home as
"beside `qbᵒ` in `UC.Model.Enrichment` … moving it later is a cut-and-paste".
It is not: `qbᵘ`'s body is `qb-to-image X 𝟭ᴵ`, which typechecks only where
`procᵘ a` reduces to `a`, i.e. inside the block DECLARING `procᵘ`. `procᵘ` was in
`UC.Model.Graded`, which imports `UC.Model.Enrichment`, so `qbᵘ` alone cannot
cross. `UC.Graded`'s import of `procᵘ` moves with it; nothing else consumed it.

Both moved, statements verbatim. `procᵘ` and `qbᵘ` now sit beside `qbᵒ` in
`UC/Model/Enrichment.agda` inside its `unfolding sealᵒ` block; `UC/Model/Graded.agda`
keeps `≈ᴹ⇒≈ᵍ`, `sub-gradedᵒ`, `procᵘ-∘` and `plug-gradedᵒ` and now reads
`unfolding gradedᵒ procᵘ`; `UC/Seam/Audit/Context.agda`'s import splits in two.
No statement changed.

## Modules

All checked with `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`,
rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate.

| module | LOC | warm | rule-5 budget |
|---|---|---|---|
| `ProbabilisticLogic.Dp.Settle` | 294 | 6.0 s | 134 s |
| `ProbabilisticLogic.Dp.Settle.Uniform` | 29 | 6.5 s | 67 s |
| `CategoricalCrypto.Protocol.Machine.Raw` | 133 | 8.8 s | 93 s |
| `Examples.ROCommitment.Transport` | 209 | 14.4 s | 112 s |
| `UC.Model.Enrichment` (+29) | 79 | 9.4 s | 80 s |
| `UC.Model.Graded` (−17) | 73 | 9.5 s | 78 s |
| `UC.Graded` (one import) | 72 | 9.4 s | 78 s |
| `UC.Seam.Audit.Context` (one import) | 229 | 9.8 s | 117 s |

Every warm column is a single-`Checking`-line run, forced by deleting that
module's own `.agdai` under `_build/` — agda 2.8 keys interface staleness on
CONTENT, so `touch` does not force one.  Nothing is anywhere near its budget;
the largest is `Transport` at 14.4 s against 112 s.

Every closure the brief names was run green with an empty gate grep, this time
including the whole-library root, which `docs/graded-bridge.md` could not
complete:

| closure | rc | secs |
|---|---|---|
| `src/CategoricalCrypto.agda` (the whole library) | 0 | 71 |
| `CategoricalCrypto.UC` | 0 | 72 |
| `CategoricalCrypto.UC.Model` | 0 | 15 |
| `Examples.MerkleDamgard` / `.Pin` / `.QueryBound` | 0 | 17 / 7 / 10 |
| `Examples.ChimericLedger.*` (all twelve) | 0 | 5–15 each |

`Examples.HashForward.*`, `Examples.ROCommitment.*` and
`Examples.ROCommitment.Hiding.*` are inside the root's cone and were checked
with it.

## Not delivered, precisely

### 1. The composite's step — `StepSettles` at a two-factor system

The RO commitment's closed system is `real 𝒫.∘ resource` (driven at the grade)
or `(plugᴹ a 𝒫.∘ real) 𝒫.∘ resource` (an adversary machine plugged). `𝒫ᴵ`'s
composition is the G construction's, whose step is
`Machines.Trace.traceStep` — `solve ∘ k ∘ id ⊗₁ i₁`, with `solve` an `iterₚ`
fixpoint. `Raw.StepSettles` at such a step is exactly "the loop between the two
factors terminates", and at an arbitrary upper factor it is FALSE, so what is
missing is a composition lemma with the termination hypothesis made explicit:

```agda
-- generic, `Protocol/Machine/**`
Settles-∘ : {A B C : Iface} (g : Proc B C) (f : Proc A B)
            (Kg : St g → Neg C → Dist⊥ (St g × (Neg B ⊎ Pos C)))
            (Kf : St f → Neg B → Dist⊥ (St f × Pos B))
          → ((m : St g) (q : Neg C) → Σ[ n ∈ ℕ ] Settles n (step g (m , inj₂ q)) …)
          → ((m : St f) (q : Neg B) → Σ[ n ∈ ℕ ] Settles n (step f (m , inj₂ q)) …)
          → (rounds : ℕ)                    -- the loop closes within `rounds` trips
          → Σ[ K ∈ _ ] StepSettles (g 𝒫.∘ f) K
```

`real` makes at most one downward query per activation, so `rounds = 1` there and
the unrolling is `Machines.Trace.solve-i₁` once and `solve-loop` once; nothing
about `Protocol.Machine.Compose`'s 312-line argument is needed, because that
argument identifies a composite with a protocol image where this one only reads
one step of it. This is the piece that is larger than the rest of the branch and
it is where the branch stops.

### 2. The game answers `idleR` where the machine diverges

Even with residual 1, `rawKernel` wants a TOTAL `Dist-ℚ` kernel. The RO
commitment's machines are partial at exactly four activations — a second
`commitᴬ` and an `openᴬ` before a commitment in `real`, a second `putᴿ` and a
`getᴿ` before one in `resource` — where `Game.respR`/`respI` answer `idleR` and
leave the state alone. The machine's image is `botₚ`, which scores 0, so the
transport gives the INEQUALITY

```agda
Pr≤ n (runᴹ sys d) ≤ℚ Pr₁ (runWith respR sR₀ d)
```

in the direction a one-sided event bound wants, and NOT the equality a two-sided
advantage bound wants. The two games go off-protocol at the same states (the
condition is the presence of the commitment, which both erasures preserve), so
the repair is one of

```agda
-- (a) the two kernels pruned, and the coupling re-run in `Dist⊥`
prune-bound : (m : ℕ) (d : Strat Q R) → asks≤ m d
            → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ d) -ℚ Pr₁⊥ (runWith⊥ respR⊥ sR₀ d) ∣ℚ ≤ℚ ε m

-- (b) generic: pruning the same dead set on both legs of a coupling does not
--     increase the advantage
prune-adv : (dead : St → Q → Bool) → …
          → ∣ Pr₁⊥ (runWith⊥ (prune dead idealK) s d) -ℚ Pr₁⊥ (runWith⊥ (prune dead realK) s d) ∣ℚ
            ≤ℚ badProb realK bad s d
```

(b) is the better buy and is where `GamePlaying.Hop`/`Potential` would be lifted
once rather than re-proved per example; `Dist⊥` is `Dist-ℚ ∘ Maybe`, so it is a
`maybeℚ`-relativisation of `Coupling.FLGP` and `badProb-super`, not a new
argument. Neither is in `src/`.

### 3. The machine-level bound itself

With 1 and 2, the statement the brief asks for is, at one level `k`, with
`sys = real 𝒫.∘ resource` and `sysᴵ = subᴵ simulator 𝒫.∘ ideal 𝒫.∘ resource`:

```agda
binding-bound : (b : Bool) (m : ℕ) (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
              → asks≤ m d
              → Σ[ n ∈ ℕ ] ((i : ℕ) →
                  ∣ cum (n + i) (runᴹ sysᴵ d) (indᵇ b) -ℚ cum (n + i) (runᴹ sys d) (indᵇ b) ∣ℚ
                  ≤ℚ εᶜ k m)
```

`εᶜ k m` is `Examples.ROCommitment.Asymptotic.εᶜ`, the number
`Game.extraction-bound` already proves in `Dist-ℚ`, and the accounting includes
the simulator's interaction because `sysᴵ` RUNS it — `simQB : QB 2 simulator` is
what charges a context that absorbs it, at `simCost`.

**The adversary is the driver, not a plugged machine.** The brief asks for the
statement at `plug-runᵍ`'s typing, with `a : Proc Advᴵ 𝟭ᴵ` at the grade and an
environment strategy at `Honᴵ`. At THIS example that statement is the vacuous one
(A1 above): `Neg Honᴵ` is empty. The non-vacuous statement drives through the
adversary port, and it needs NO new vocabulary — `runᴹ` is stated at any closed
`Proc unitᴵ B`, so `B = Advᴵ ⊗ᴵ Honᴵ` is the grade-driven closed run
`docs/graded-bridge.md` calls for under the name `runᴳ` and prices as "a core
addition". It is not one; it is `runᴹ` at the tensored interface, and the
adversary is then the `Strat` the game already quantifies over. That is the one
correction this branch makes to `graded-bridge`'s account of (d)(i).

### 4. The hiding half — and where it is BETTER off

`docs/fcom-hiding.md` §"Not delivered" 2 states `raw-emulationʰ` and says it
"instantiates the SAME three at `Advᴵʰ`/`Honᴵʰ`/`Lkᴵʰ` and needs nothing further
of them". That is right about `plug-runᵍ`/`adequacyᵍ` and right about residuals 1
and 2 above, which are about the layer. It is wrong about A1, and in the hiding
half's favour: `Examples.ROCommitment.Hiding.Honᴵʰ` is `HonAʰ ⇿ HonQʰ` with
`HonQʰ` INHABITED (`commitᴱ b`, `openᴱ`), so `Neg Honᴵʰ` is not empty, an
environment strategy there really does drive the system, and `extractᵍ` at a
plugged adversary machine `a : Proc Advᴵʰ 𝟭ᴵ` is not vacuous. The corrupted party
is the receiver, and the honest committer is exactly the party the environment
instructs.

So Route A is available on the hiding side and not on the extraction side, and
the difference is which port carries a query — not anything about the two proofs.
What Route A would still owe there is A2: an ε-carrying `≤UC[ ]`, or an
`AuditBound` proved on the real side directly. Nothing on that side was touched
this branch; `protocol-rewrite` had no new commits over `2fcac147` when it
started, and `Examples/ROCommitment/Hiding/*` is a sibling's this round.

### 5. The UC-level statement, and the quantifier gap

What is reachable once 1–3 are in hand is a statement over the environments
`UC.Seam.Grounding.StratIsEnv` embeds — the contexts built from a FINITE strategy:

```agda
strat-emulation : (m : ℕ) (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
                → asks≤ m d
                → Obs ((auditTest (Advᴵ ⊗ᴵ Honᴵ) d ∘ T₁ᵒ 𝟘ᴳ realᵒ) ∘ closedᵒ resource)
                  ≈ₚ[ εᶜ k m ]
                  Obs ((auditTest (Advᴵ ⊗ᴵ Honᴵ) d ∘ T₁ᵒ 𝟘ᴳ (sub simᵒ ∘ idealᵒ)) ∘ closedᵒ resource)
```

`raw-emulation` (`docs/fcom-extraction.md` item 1, `docs/graded-bridge.md` item
(f)) asks for three quantifiers this does not have, and `StratIsEnv` is one-way
so none of them is recoverable from it:

* **the ancilla** — `raw-emulation` ranges over every `W : Channel`; the
  strategy-embedded context is at `W = 𝟘ᴳ`.
* **the test** — `raw-emulation` ranges over every query-bounded machine test
  `Et`; a `Strat` is finite executable syntax. Compiling a machine test back into
  one would have to enumerate an arbitrary `Dₚ` step, which is
  `docs/graded-bridge.md`'s obstruction (ii). `StratIsEnv` gives the inclusion
  and there is no converse.
* **the closure** — `raw-emulation` ranges over every `m : 𝟘ᵒ ⇒ T₀ W (ifaceᵒ Resᴵ)`
  with a query bound; the game fixes the concrete `resource`.

So the game bound bounds the observations of the strategy-embedded contexts at
the concrete resource, and `_≈ᵁ_`'s quantifier asks for all machine tests at all
ancillas at all closures. That is the whole of the gap, and it is a quantifier
gap rather than a proof gap.

## Nothing was weakened

No pre-existing statement was edited. `prAgree`, `extract`, `extractᵍ`,
`plug-runᵍ`, `adequacyᵍ`, `audit-runᵍ`, `absorb-plugᵍ` and `extraction-bound`
keep their statements verbatim, as do `procᵘ` and `qbᵘ`, which moved module
without a character changing. `UC/Audit.agda`, `UC/Asymptotic/*`, `Abstract2*`,
`UC/Model/Bridge.agda`, `UC/Budget.agda`, `Examples/ROCommitment/Hiding/*`,
`Examples/MerkleDamgard*` and `GamePlaying/*` are untouched.
