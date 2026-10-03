# The raw transport: `Dₚ` runs as `Dist⊥` kernel runs

The UC cone runs on `Dₚ` (`ProbabilisticLogic.Dp`, the rational probabilistic
delay monad), the game cone on `Dist-ℚ`. The RO commitment's systems are raw
machines, not layer-1 protocol images
([`docs/hash-forward.md`](hash-forward.md) §"Why `real` is a raw machine").
This document is the transport at RAW machines: generic in
`ProbabilisticLogic.Dp.Settle` and `Machines.Run.Raw`, inhabited at a
machine that really samples in `Examples.ROCommitment.Transport`. Its
continuation to two-factor composites and partial game kernels is
[`docs/fcom-uc.md`](fcom-uc.md).

## Route T, and why not Route A

The first attempt at this bridge was a `closed-kernel` lemma: for an adversary
machine `a` plugged at the grade, a resource below and an environment strategy
`d` at the honest port `Honᴵ`, the closed `Dₚ` run equals
`Pr₁ (runWith respR sR₀ (compile a d))` for a `compile` folding the plugged
machines into one game strategy. It is not provable as written, for two
reasons. `Examples.ROCommitment.Honᴵ` is `HonA ⇿ ⊥`: `Neg Honᴵ` is empty, so
every such `d` is built from `out` and `coin` alone, `runᴹ M d` never reaches
`M`'s step, and the left-hand side does not depend on the system. And `compile`
cannot exist at an arbitrary machine adversary: a machine's step is an
arbitrary `Dₚ` computation, a `Strat` is finite syntax.

**The adversary is the driver, not a plugged machine.** At this example the
corrupted committer sits at the grade, so the non-vacuous statement drives the
closed system through the adversary port: `runᴹ` at the tensored interface
`Advᴵ ⊗ᴵ Honᴵ`, with the adversary the `Strat` the game already quantifies
over. That needs no new vocabulary — `runᴹ` is stated at any closed
`Proc unitᴵ B` — and it is the transport below (**Route T**).

**Route A** — state binding failure as an audited event of a
strategy-embedded environment at `Honᴵ` and carry an ideal-side bound across
the emulation — is closed at the extraction half for two independent reasons,
neither of them proof work. (A1) By the same emptiness of `Neg Honᴵ`, any bound
read through an environment strategy at `Honᴵ` holds of a system that reports
a binding failure on every activation exactly as of the real one. (A2)
Carrying an event bound from the ideal side to the real side needs an EXACT
emulation, and this one is approximate by construction. On the hiding half A1
does not apply — `Examples.ROCommitment.Hiding.Honᴵʰ = HonAʰ ⇿ HonQʰ` with
`HonQʰ` inhabited (`commitᴱ b`, `openᴱ`), so an environment strategy there
does drive the system, and the honest committer is exactly the party the
environment instructs — but A2 does. Which port carries a query decides it,
not anything about the two proofs.

## `ProbabilisticLogic.Dp.Settle` — the `Dₚ` half

A raw machine's step is an arbitrary `Dₚ` computation, so a bind junction needs
the value's own reading, uniformly in the test — not a `cum` family that has
stopped moving at one test.

```agda
Null  : Dₚ A → Set
Halts : ℕ → Dₚ A → Set                        -- mutual with `HaltsL`

record Settles (n : ℕ) (d : Dₚ A) (ν : Dist⊥ A) : Set where
  field halts : Halts n d
        score : (Q : A → ℚ) → NNF Q → cum n d Q ≡ E⊥ ν Q
```

`Halts (suc n) d` is `Null d ⊎ ((c : Bool) → HaltsL n (br d c))`: every branch
has reached a value within `n` steps, or the residue carries no mass. The `Null`
disjunct is not a convenience — `botₚ` never halts and never scores, and an
off-protocol activation's machine image IS `botₚ`, so a run that reaches one
must still settle. It is also what makes `Halts` monotone in the budget, which
the bind lemma spends.

The family is closed under the ways a `Dₚ` run is built: `Settles-return`,
`Settles-bot`, `Settles-coin`, and `Settles-bind`/`Settles-bind⋆`.
`Settles-bind` is the content: two mutual inductions on the halting budget —
one for `Halts (n + j) (d >>=ₚ f)`, one for
`cum (n + j) (d >>=ₚ f) Q ≡ cum n d (λ p → E⊥ (κ p) Q)` — carrying the
continuations' settling over `Dp.Supp`, the depth-`n` support `Dp.uniformize`
maxes budgets over. `Settles-bind⋆` is the consumer's form: the continuation
settles at every value at a budget of its OWN, and the uniformizer supplies the
single `j` the induction needs. Nothing anywhere is a global fuel.

`Settlesᵀ n d μ = Settles n d (Dmap just μ)` is the no-divergence case, the
form a closed game's kernel is written in, with `Settlesᵀ-tag` for the
relabelling a machine step performs on its kernel's answer, and
`uniformₚ-settles : Σ[ i ∈ ℕ ] Settlesᵀ i (uniformₚ n) (uniform-Vec n)` is what
makes the transport apply to a machine that samples: the cascade of `n` fair
`coinₚ`s halts after them and scores `uniform-Vec n` exactly.

`Settles` is a RECORD and `Settles-resp` takes both values EXPLICITLY, and
neither is stylistic: `Dist-ℚ` is a record and `E⊥` projects it, so where the
type unfolds to a `Σ` the value is compared through `E⊥`, a value left implicit
eta-expands into entries and weights, and unification blocks on a weight. With
a rigid head and explicit values every such meta is solved by the type.

## `Machines.Run.Raw` — the machine half

```agda
StepSettles : Set              -- at M : Proc unitᴵ B, K : St M → Neg B → Dist⊥ (St M × Pos B)
StepSettles = (m : MC.St M) (q : Neg B)
            → Σ[ n ∈ ℕ ] Settles n (MC.step M (m , inj₂ q)) (Dmap⊥ ansᴹ (K m q))

rawAgree : (m : MC.St M) (d : Strat (Neg B) (Pos B))
         → Σ[ n ∈ ℕ ] Settles n (runᴹFrom M m d) (runWith⊥ K m d)
rawRun   : (d : Strat (Neg B) (Pos B))       -- given the initial state settles on σ₀
         → Σ[ n ∈ ℕ ] Settles n (runᴹ M d) (σ₀ >>=⊥ λ m → runWith⊥ K m d)
rawPr    : (b : Bool) (d : Strat (Neg B) (Pos B))
         → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n + i) (runᴹ M d) (indᵇ b)
                                ≡ E⊥ (σ₀ >>=⊥ λ m → runWith⊥ K m d) (indᵇ b))
```

at an ARBITRARY closed machine and an arbitrary step kernel: past a budget the
`cum` family is the kernel run's verdict probability, at either verdict.
`Protocol.Machine.Agree.prAgree` is `rawPr` at a protocol image, where
`StepSettles` is discharged by induction on the call tree an activation drives
(`drive-settles`). Against a TOTAL `Dist-ℚ` kernel along a state embedding the
bridge is `Interaction.runWith⊥-emb`.

`StepSettles` carries one fuel per activation, because the trace loop inside a
composite's step has no protocol-image structure to induct on, and it is a
genuine hypothesis: at a composite whose upper factor is an arbitrary
adversary machine the loop between the factors need not terminate, so no
unconditional `rawAgree` can exist. Making the fuel a hypothesis is what keeps
the module free of `{-# TERMINATING #-}` and of a global clock.

## `Examples.ROCommitment.Transport` — the hypothesis, inhabited

```agda
resKᵀ : RState → Pt → Dist-ℚ (RState × ResA)
resKᵀ (t , m) x = Dmap digᵀ (fetchT (_, m) t x)

resK : RState → Neg Resᴵ → Dist⊥ (RState × Pos Resᴵ)
resource-settles : StepSettles resource resK
```

The RO commitment's own lazily sampled resource. On the oracle half `resK` IS
`Examples.ROCommitment.Oracle.fetchT` relabelled onto `Resᴵ` — `resKᵀ` is
defined so, and it is the kernel the closed game's bound is proved about — and
the fresh branch draws `uniformₚ k`, so `uniformₚ-settles` makes the activation
settle, and `rawPr` at `resource-settles` reads the `Dₚ` closed run of the
concrete resource as a `Dist⊥` kernel run at every strategy, with no protocol
image anywhere.

`resK` is `Dist⊥`-valued rather than `Dist-ℚ`-valued and that is not slack: two
cell activations are off-protocol (a second `putᴿ`, a `getᴿ` before one), the
machine's image of those is `botₚ`, and the game's `respR` answers `idleR`
there. Pruning those activations on both legs of the coupling is
`GamePlaying.Partial` ([`docs/fcom-uc.md`](fcom-uc.md) §2).

## Not delivered

The transport reaches the closed real system `real 𝒫.∘ resource`
(`Examples.ROCommitment.Realization.Bound.extraction-real`); the remaining
distance to the commitment's UC-level ε-statement — the ideal leg, blocked at
the simulator's relay log — is
[`docs/fcom-extraction.md`](fcom-extraction.md) §"Not delivered" 1 and
[`docs/rcom-icom-b1.md`](rcom-icom-b1.md) §7. At the hiding half nothing yet
connects the game kernels to the machines
([`docs/fcom-hiding.md`](fcom-hiding.md) §"Not delivered").
