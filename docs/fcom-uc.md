# `F_com`'s closed-game bounds, and the distance to its UC-level ε-emulation

Branch `fcom-uc`, off `protocol-rewrite` at `587999b5`.

[`docs/dp-transport.md`](dp-transport.md) §"Not delivered, precisely" lists five
typed residuals between the RO commitment's `Dist-ℚ` game bound and a UC-level
ε-emulation. This branch delivers the two generic layers those residuals rest on — item 1
down to `StepSettles` at a traced machine, and the game-playing bridges at a
partial kernel (item 2) — and replaces the account of item 5 with a different
one: **the test quantifier is not the gap.**

Everything below is a checked term unless it is in "Not delivered". Hatches in
`src/` stay at their baseline of zero: the
`postulate|TERMINATING|primTrustMe|\{!` grep counts 16 hits before and 16
after, all of them the words "postulate-free" in inherited comments.

## 1. The loop settles — the round-trip bound, exactly

`docs/dp-transport.md` item 1 asks for `StepSettles` at a two-factor composite
and says the missing ingredient is a *round-trip bound*, "the number of internal
messages one activation can bounce between the factors". That bound is a
statement about `ProbabilisticLogic.Dp.Iter.iterₚ`, not about machines, and it
is now one.

### `ProbabilisticLogic.Dp.Settle.Iter` — generic

`Dp.Settle`'s `Settles-bind` is the junction a closed RUN passes. `iterₚ` is the
junction a COMPOSITE's step passes, and there no unconditional statement exists:
at an arbitrary body the loop never exits, so `iterₚ u w` halts at no budget and
`Settles n (iterₚ u w) ν` is false for every `n` and every `ν`.

The junction itself is unconditional and is the file's content:

```agda
Settles-stepᵢ  : (n j : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A)))
                 (ν : Dist⊥ (S × (B ⊎ A))) (κ : S × (B ⊎ A) → Dist⊥ (S × B))
               → Settles n x ν → Supp n x (λ p → Settles (suc j) (contᵢ u p) (κ p))
               → Settles (n + suc j) (stepᵢ u x) (ν >>=⊥ κ)   -- Iter.agda:100
Settles-stepᵢˢ : …  -- :112, the budgets maxed over the depth-`n` support
Settles-stepᵢ⋆ : …  -- :134, the all-points convenience
```

`stepᵢ u x` is `x >>=ₚ contᵢ u` with the exits taken one step earlier
(`Dp.Iter.tagᵢ` against `Dp.tagₚ`), so both inductions are `Dp.Settle`'s with
`tagᵢ` in place of `tagₚ` — `Null-stepᵢ`, `Halts-stepᵢ`/`HaltsL-stepᵢ`,
`cum-stepᵢ`/`leafᵢ-stepᵢ`. The `suc j` in the hypothesis is not slack: an exit
is a `returnₚ`, whose reading a budget of 0 does not yet see. **No fixpoint law
is spent**: `iterₚ u w` IS `stepᵢ u (u w)` definitionally, so
`Settles-stepᵢ⋆ … (u w) …` is already the one-turn loop lemma, and none of
`iterₚ-fix`/`solve-loop`'s `≈ₚ` ever appears. That matters, because `Settles`
is NOT `≈ₚ`-stable (see "Why `Settles` cannot be transported" below).

### The round-trip bound's exact shape

```agda
module _ {S A B : Set} (u : Body S A B) (Ku : S × A → Dist⊥ (S × (B ⊎ A)))
         (bodyS : (w : S × A) → Σ[ i ∈ ℕ ] Settles i (u w) (Ku w)) where

  loopK : ℕ → S × A → Dist⊥ (S × B)                       -- Iter.agda:152
  exitK : ℕ → S × (B ⊎ A) → Dist⊥ (S × B)
  loopK zero    w = return-ℚ nothing
  loopK (suc f) w = Ku w >>=⊥ exitK f
  exitK f (s , inj₁ b) = return⊥ (s , b)
  exitK f (s , inj₂ p) = loopK f (s , p)

  module _ (rank : S × A → ℕ) where

    Drops : ℕ → S × (B ⊎ A) → Set                         -- :163
    Drops r (_ , inj₁ _) = ⊤
    Drops r (s , inj₂ p) = rank (s , p) < r

    Ranked : Set                                          -- :170
    Ranked = (w : S × A) (i : ℕ) → Supp i (u w) (Drops (rank w))

    Settles-iter : Ranked → (f : ℕ) (w : S × A) → rank w < f
                 → Σ[ i ∈ ℕ ] Settles i (iterₚ u w) (loopK f w)   -- :172
```

Three things about this shape are the point.

* **The bound is a rank, not a global clock.** `Ranked` says: at every loop
  point, the body's depth-`i` support carries only re-entries of strictly
  smaller rank. It is read off a step table, one clause at a time, and it is
  quantified at every `i` because `Supp` is a depth-indexed notion.
* **It is quantified over the SUPPORT, not over all points.** An unreachable
  loop re-entry has no bound at all, and demanding one would make `Ranked`
  false at every machine that has unreachable configurations — which is all of
  them. This is what `Dp.Support.uniformizeˢ` exists for: `Dp.uniformize`
  assumes the per-value budget everywhere.
* **The kernel is the body's unrolled `f` rounds, the round past the last
  reading as divergence.** That is not a modelling choice, it is what makes
  `loopK` total, and `Settles-iter`'s conclusion is what pins `f` large enough
  that the divergence is never reached. Without the rank the reading is simply
  wrong, and `Settles-iter` would be false rather than unprovable.

At a two-factor composite `rank` counts the messages the upper factor still has
to bounce off the lower one: at ROCommitment's `real`, every clause of
`realStep` emits at most one `inj₁` (a `hashᴿ`) and the state it moves to
(`relayᴿ`/`checkᴿ`) emits none, so the measure is
`rank (m , inj₁ b) = 2`, `rank (m , inj₂ b) = 1` at an idle upper state and
`0` at a relaying one — three values, no arithmetic.

### `ProbabilisticLogic.Dp.Support` — generic

Three `Supp` facts `Dp`'s own `uniformize` does not give: `Supp-map` (pointwise
weakening), `Supp-all` (a fact that holds everywhere), and `uniformizeˢ` /
`uniformizeLˢ` — `uniformize` with the per-value witness assumed only on the
support. Their natural home is beside `Supp` in `ProbabilisticLogic/Dp.agda`;
they are one directory down because that file is not this branch's to edit.

### Why `Settles` cannot be transported along `≈ₚ`

Worth recording, because it is what dictates the shape of everything above and
of the residual below. `Settles n d ν` carries `Halts n d`, which is a fact
about the TREE (`Dp.Settle`:56) modulo semantic nullity. `_≈ₚ_` is cofinal
domination of the `cum` families, i.e. equality of suprema, and a supremum can
be approached without being reached: `d ≈ₚ e` and `Settles n d ν` do not give
`Σ i. Settles i e ν`. So no `Settles` fact can be moved along `Dp.Reasoning`'s
`>>=ₚ-identityˡ`/`>>=ₚ-assoc`/`bindᶠ`/`bindˣ`, along `Machines.Pointwise`'s
calculus, or along `Machines.Sim`'s `_≈ᴹ_` — every one of which is an `≈ₚ`.
A `Settles` witness for a composite's step has to be BUILT at the literal term,
out of `Settles-return`/`Settles-coin`/`Settles-bind`/`Settles-stepᵢ`. That is
what makes the machine half of item 1 a construction rather than a transport,
and it is why `Settles-stepᵢ` is stated at `stepᵢ` and not at `x >>=ₚ contᵢ u`.

(The escape hatch that does exist and is not taken: `Settles-cum`'s conclusion
alone — "the reading has arrived and no longer moves" — IS stable under an
exact `cum`-shift, which is what every one of those rearrangements actually
proves. It is not enough, because `Settles-bind` consumes `Halts` of its first
argument and a composite's `Settles` is itself used as a continuation.)

## 2. The game-playing bridges at a partial kernel

`docs/dp-transport.md` item 2: the machines diverge exactly where the game
kernels answer `idleR`, so the transport gives an inequality where a two-sided
advantage bound wants an equality, and the doc's own verdict — "(b) is the
better buy … a `maybeℚ`-relativisation of `Coupling.FLGP` and `badProb-super`,
not a new argument" — is what is done, once.

`CategoricalCrypto.GamePlaying.Partial` (293 LOC, generic, no example):

| name | line | total counterpart |
|---|---|---|
| `badProb⊥` | 46 | `GamePlaying.badProb` |
| `badProb⊥-bad` | 55 | `badProb-bad` |
| `Preserved⊥` | 66 | `Preserved` |
| `SuperCert⊥` | 69 | `SuperCert` |
| `badProb⊥-super` | 84 | `badProb-super` |
| `badProb⊥-bounded` | 119 | `badProb-bounded` |
| `Coupling⊥` / `FLGP⊥` | 132 / 143 | `Coupling` / `FLGP` |
| `StepBisim⊥` / `runWith⊥-bisim` | 233 / 240 | `Hop.StepBisim` / `runWith-bisim` |
| `hop-bound⊥` | 268 | `Hop.hop-bound` |

Each statement is its total counterpart with `E⊥`/`Pr₁⊥`/`OnSupport⊥` for
`E`/`Pr₁`/`OnSupport`, and each proof is the same induction: the sink scores 0,
which the supermartingale only benefits from and which the coupling passes
through untouched. The two structural differences are worth naming.
`Preserved⊥` is genuinely WEAKER than `Preserved` — an activation the machine
refuses to serve reaches no state, so it preserves any invariant — and the coin
junction stays `E`, not `E⊥`, because `Interaction.runWith⊥`'s `coin` clause
binds a TOTAL `Dist-ℚ Bool` with `_>>=ᴹ_`.

### Relation to the `Dist-ℚ` toolkit

The `Dist-ℚ` statements are the `Dist⊥` ones at a totally served kernel, and
the identification is a checked term rather than a remark:

```agda
embedᵏ  : (St → Q → Dist-ℚ (St × R)) → St → Q → Dist⊥ (St × R)      -- :198
total⇒⊥ : (K : St → Q → Dist-ℚ (St × R)) (s : St) (d : Strat Q R)
        → Pr₁⊥ (runWith⊥ (embedᵏ K) s d) ≡ Pr₁ (runWith K s d)      -- :201
prune      : (St → Q → Bool) → (St → Q → Dist-ℚ (St × R)) → St → Q → Dist⊥ (St × R)
prune-cert : (dead : St → Q → Bool)
           → SuperCert K bad s₀ ε → SuperCert⊥ (prune dead K) bad s₀ ε   -- :211
```

`prune dead K` is `K` cut down to the activations a machine serves, and `dead`
constantly `false` is `embedᵏ`. **Nothing in `GamePlaying`, `GamePlaying.Hop`
or `GamePlaying.Potential` was deleted or restated**: every existing consumer
(`Examples.MerkleDamgard.*`, `Examples.ROCommitment.Game.extraction-bound`) is
stated at the total form, and the `Dist-ℚ` versions are not *derived* from the
`Dist⊥` ones — `badProb` is a different recursion, not `badProb⊥ ∘ embedᵏ`, and
turning one into the other would be a fourth lemma nobody needs. What `prune`
buys is the direction that matters: a `SuperCert` proved once about the total
coupling (`Game.cert`, `Game.stepR`, `Game.stepI`) transfers to the pruned
kernels for free, so `hop-bound⊥` at the pruned `respR`/`respI` is
`docs/dp-transport.md`'s `prune-bound` as soon as the two `runWith⊥-bisim`
marginals are in place.

### `RationalDist.Expectation` — the algebra this needed

`E⊥`'s algebra was split between `Expectation.agda` (where `E⊥` is defined) and
`Dp.Settle` (where three of its lemmas had been proved, because that is where
they were first needed). `Eⱼ`, `E⊥-map` and `E⊥-map-bind` move to
`Expectation.agda` with their statements verbatim, and `OnSupport⊥`, `Mb`,
`E⊥-mono-on`, `Pr₁⊥≥0`, `∣Pr⊥-Pr⊥∣≤1` and `E⊥-abs-diff` join them — each the
total lemma at `maybeℚ`, with the sink obligation `0ℚ ≤ 0ℚ` or
`∣ 0ℚ -ℚ 0ℚ ∣ℚ ≡ 0ℚ`. `Dp.Settle` keeps `E⊥-coin`, which mentions `coinₚ`'s
shape and belongs where it is.

## 3–4. What is NOT delivered, and where each stops

Items 3, 4 and the machine half of item 1 stand on one another in that order
and none of them is reached. Their statements, with the exact types:

### 1b. `Settles-∘` at a two-factor composite — the second leg

The FIRST leg is delivered: `Protocol.Machine.Trace.trace-settles`
(`Trace.agda:95`) is `StepSettles` at a traced machine, which is the shape
every G-composite has. What is missing is the identification of `𝒢ₚ`'s `_∘_`
with a trace of a machine whose step has a kernel:

```agda
-- generic, `Protocol/Machine/Trace.agda` or beside it
compose-settles : {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set}
                  (g : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
                  (Kg : MC.St g → (B⁺ ⊎ C⁻) → Dist⊥ (MC.St g × (B⁻ ⊎ C⁺)))
                  (Kf : MC.St f → (A⁺ ⊎ B⁻) → Dist⊥ (MC.St f × (A⁻ ⊎ B⁺)))
                → ((m : MC.St g) (y : _) → Σ[ i ∈ ℕ ] Settles i (MC.step g (m , y)) (Kg m y))
                → ((m : MC.St f) (z : _) → Σ[ i ∈ ℕ ] Settles i (MC.step f (m , z)) (Kf m z))
                → (rank : _) (f′ : ℕ) → (Ranked …) → (∀ w → rank w < f′)
                → Σ[ K ∈ _ ] Raw.StepSettles (g 𝒢.∘ f) K
```

`trace-settles` reduces it to one obligation: a kernel and a `Settles` for the
step of `W.α ∘ᴹ ((g ⊗ᵉ f) ∘ᴹ W.γ)`, which is what `𝒢ₚ`'s `_∘_` unfolds to
(`Machines.Collapse.compose-raw≈ᴳ`, under `unfolding composeᴳ`). That step is
`onL (step α) ∘ onR (onL (step (g ⊗ᵉ f)) ∘ onR (step γ))`, and
`Machines.Pointwise`'s `swp-pt`/`onL-pt`/`onR-pt`/`tstepL`/`tstepR` give the
shape of every junction in it — each a `returnₚ` chain around one factor's
step, so each a `Settles-ret⋆` or a `Settles-bind⋆`. It is bulk, not
difficulty; what it is NOT is a transport along `Machines.Collapse.outer`,
which is an `S.≈ᴹ` and which by "Why `Settles` cannot be transported" a
`Settles` witness cannot ride. That is the reason `collapseᵀ`'s readable `kᴳ`
does not shorten this: `kᴳ` is a machine `𝒢ₚ`'s composite is EQUAL to, not one
it reduces to.

The ROCommitment instance then needs `Ranked` discharged at `real`, `ideal` and
`subᴵ simulator`, which is the by-inspection part (the rank is above).

### 2b. `prune-adv` / `prune-bound` at ROCommitment

The generic half is delivered (item 2). What is missing is the example's two
`StepBisim⊥`s: `Transport.resK` against `prune deadR respR` and the ideal-side
kernel against `prune deadI respI`, at `deadR (t , m) q = ` "a second `putᴿ`, or
a `getᴿ` before one", i.e. exactly the two clauses where `Transport.resK`
answers `return-ℚ nothing` (`Transport.agda:68`, `:71`) and `Game.opnR`/`opnI`
answer `idleR` (`Game.agda:138`, `:152`). Both erasures preserve the presence
of the commitment, so the two dead sets correspond; `runWith⊥-bisim` is then
the same induction `Game.stepR`/`stepI` already run, with `E⊥` for `E`.

### 3. `binding-bound`, non-vacuous

`docs/dp-transport.md`'s correction stands and is confirmed by the interfaces:
`Examples.ROCommitment.Honᴵ` is `HonA ⇿ ⊥`, so a
`d : Strat (Neg Honᴵ) (Pos Honᴵ)` has no `ask` and the plugged-adversary
statement is vacuous. The non-vacuous one is `runᴹ` at the tensored interface,
with no new vocabulary:

```agda
binding-bound : (b : Bool) (m : ℕ)
                (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ))) → asks≤ m d
              → Σ[ n ∈ ℕ ] ((i : ℕ) →
                  ∣ cum (n + i) (runᴹ (subᴵ simulator 𝒫.∘ ideal 𝒫.∘ resource) d) (indᵇ b)
                  -ℚ cum (n + i) (runᴹ (real 𝒫.∘ resource) d) (indᵇ b) ∣ℚ
                  ≤ℚ εᶜ k m)
```

Route for it: 1b gives `StepSettles` for both closed systems, `Raw.rawPr` turns
each side's `cum` family into a `Pr₁⊥` of a `runWith⊥`, 2b identifies those two
`runWith⊥`s with the pruned game kernels, and `hop-bound⊥` at
`Game.cert`-via-`prune-cert` is the bound. Every step of that route is now
either a checked term or one of 1b/2b.

**The hiding half: Route A, not Route T.** `docs/dp-transport.md` item 4
predicts this and the prediction holds. `Examples.ROCommitment.Hiding.Honᴵʰ` is
`HonAʰ ⇿ HonQʰ` with `HonQʰ` inhabited, so `Neg Honᴵʰ` is not empty,
`UC.Seam.Audit.Context.extractᵍ` at an adversary machine `a : Proc Advᴵʰ 𝟭ᴵ` is
not vacuous, and `audit-runᵍ`/`plug-runᵍ` apply as they do at
`Examples.HashForward.Audit.hf-pr-bound`. Route A is cheaper there because it
does not need 1b at all: `extractᵍ`'s conclusion is a `Pr≤` on
`runᴹ closedᵍ e`, and `closedᵍ` being a composite is not something `extractᵍ`
reads. What Route A still owes on that side is unchanged and is
`docs/dp-transport.md` A2: an ε-carrying `≤UC[ ]`, or an `AuditBound` proved on
the real side directly. Neither is this branch's, and
`Examples/ROCommitment/Hiding/*` is untouched.

## 5. The quantifier gap — the test quantifier is NOT it

`docs/dp-transport.md` item 5 names three quantifiers that `strat-emulation`
does not have and says "`StratIsEnv` is one-way so none of them is recoverable
from it". Two of the three are recoverable, and not from `StratIsEnv` — from a
theorem that is already in `src/`:

```agda
-- src/CategoricalCrypto/UC/Model/Dominated.agda:110, discharged at :121
ContextDominatedᵒ =
    (B : Iface) (X : G.Obj)
    (E : X G.⊗₀ (𝟘ᵒ G.⊗₀ ifaceᵒ B) G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ X G.⊗₀ 𝟘ᵒ)
    {c c′ : ℕ} → QB c E → QB c′ m
  → (u v : Proc unitᴵ B) (ε δ : ℚ) → 0ℚ ℚ.< δ
  → ((d : Strat (Neg B) (Pos B)) → asks≤ (ctxBudget c c′) d
     → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
  → Obs ((E G.∘ T₁ᵒ X (gradedᵒ (conjᴵ u))) G.∘ m)
    ≈ₚ[ ε ℚ.+ δ ] Obs ((E G.∘ T₁ᵒ X (gradedᵒ (conjᴵ v))) G.∘ m)

dominatedᵒ : ContextDominatedᵒ
```

`dominatedᵒ` takes agreement at every `asks≤ (ctxBudget c c′)` STRATEGY to
agreement at every budgeted model TEST at every seal-object ancilla. It is the
density lemma item 5 asks whether exists, its proof is
`UC.Machine.Dominated.skeleton`'s fuel-indexed extraction of a bounded-depth
test into a finite strategy (`UC.Seam.Extract`'s header states exactly the
finiteness obstruction and how the fuel answers it), and it is a theorem, not a
hypothesis. So, quantifier by quantifier:

* **the test** — CLOSED by `dominatedᵒ`. `StratIsEnv`'s one-way-ness is not the
  obstruction: the converse is not an inclusion of contexts but a
  *domination up to δ*, and that is what exists.
* **the ancilla** — CLOSED by `dominatedᵒ`, whose `X : G.Obj` is arbitrary.
  `W = 𝟘ᴳ` is a restriction of the strategy-embedded-context route
  (`Grounded.envAsCtx`), not of the statement.
* **the closure** — OPEN, and not a density question. `dominatedᵒ`'s `m` is an
  arbitrary budgeted closure of the ANCILLA; the resource sits inside `u` and
  `v`, which are closed processes. `_≤UC^ωᵉ_` ranges over every query-bounded
  `m : 𝟘ᵒ ⇒ T₀ W (ifaceᵒ Resᴵ)`, and `Game.respR`/`respI` ARE the concrete
  lazily-sampled oracle and one-shot cell: a different closure is a different
  game, with a different `SuperCert`. Lifting it means re-proving
  `Game.keep-or-sample` and `Game.rare-raise` against an abstract query-bounded
  resource, which is a genuine new theorem and not a quantifier manipulation.
  (`Asymptotic.resourceQB : QB 0 resource` is `qb-closed`, a certificate that
  the resource asks nothing downward — it says nothing about other closures.)

### The `+ δ`, and why it is absorbable

`dominatedᵒ` pays an arbitrary `δ > 0`, and `_≈ctx[_]_` demands a FIXED ε, so
the slack cannot be taken to zero: `(∀ δ > 0. d ≈ₚ[ ε + δ ] e) → d ≈ₚ[ ε ] e`
needs the cofinal supremum to be attained, which it is not constructively. It
does not have to be taken to zero. `εᶜ n q = fromℕ (q*q + q + q) *ℚ inv-pow-2 n`
is strictly positive, so taking `δ = εᶜ n q` gives `≈ctx[ 2 ·ᶠ εᶜ ]`, and
`2 ·ᶠ εᶜ` is `λ n q → fromℕ (2*(q*q+q+q)) *ℚ inv-pow-2 n`, which
`Asymptotic.εᶜ-negligible`'s own witness form
(`negligibleBound-inv-pow-2` at `t = λ _ q → 2*(q*q+q+q)`, the polynomial
closure lemmas unchanged) certifies as a `NegligibleBound`. **A constant factor
on the ε family is the whole price of the test and ancilla quantifiers.**

### What item 4 becomes, and what it is an instance of

With 1b/2b/3 in hand and `dominatedᵒ` on top, the statement to aim at is not
`strat-emulation` at all but, at one level `k`, with
`u = real 𝒫.∘ resource` and `v = subᴵ simulator 𝒫.∘ ideal 𝒫.∘ resource`
(both `Proc unitᴵ (Advᴵ ⊗ᴵ Honᴵ)`):

```agda
fcom-emulation : (X : G.Obj) (E : X G.⊗₀ (𝟘ᵒ G.⊗₀ ifaceᵒ (Advᴵ ⊗ᴵ Honᴵ)) G.⇒ Ωᵒ)
                 (m : 𝟘ᵒ G.⇒ X G.⊗₀ 𝟘ᵒ) {c c′ : ℕ} → QB c E → QB c′ m
               → Obs ((E G.∘ T₁ᵒ X (gradedᵒ (conjᴵ u))) G.∘ m)
                 ≈ₚ[ 2 ·ᶠ εᶜ k (ctxBudget c c′) ]
                 Obs ((E G.∘ T₁ᵒ X (gradedᵒ (conjᴵ v))) G.∘ m)
```

which is `_≈ctx[_]_` (`UC/Asymptotic/Contextual.agda:79`) at
`A = λ _ → 𝟘ᵒ`, `X = λ _ → 𝟘ᵒ`, `B n = ifaceᵒ (Advᴵ ⊗ᴵ Honᴵ)` — the trivial
grade, both systems closed, the resource absorbed — rather than at the graded
`Homᶠ (ifaceᵒ Resᴵ) (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)` that
`(λ k → realᵒ k) ≤UC^ωᵉ (λ k → idealᵒ k)` needs. The remaining distance to the
`≤UC^ωᵉ` witness is therefore exactly two things and neither is the test
quantifier:

1. **re-opening the grade and the resource.** `_≈ctx[_]_` compares
   `f n : A n ⇒ T₀ (X n) (B n)` with the adversary port and the resource port
   both OPEN; `dominatedᵒ` delivers the closed, trivially-graded form.
   `UC.Seam.Audit.Context.plug-runᵍ` and `absorb-plugᵍ` are the two coercions
   that cross that boundary for a PLUGGED adversary machine and an absorbed
   simulator; what is missing is the same for an arbitrary graded test, which
   is the `≈ctxᴬ⇒≈ctx`/`prefixᵒ` direction (`Contextual.agda:105`, `:112`) at a
   closed process — not proved, and not obviously cheap.
2. **the closure quantifier**, as above.

The `Certified` component of `_≤UC^ωᵉ_` is already inhabited:
`Examples.ROCommitment.UC.simQB : QB 2 simulator` plus
`Asymptotic.εᶜ-negligible` are exactly `Contextual.Certified`'s `sim-qb` and
`_≤UC^ωᵉ_`'s `NegligibleBound` fields (`docs/quantitative-family.md`'s witness
form), so what the coin-toss sibling's hypothesis is missing is the `≈ctx`
component alone.

## Generic versus example-specific

| module | generic? |
|---|---|
| `ProbabilisticLogic.Dp.Support` | generic — three `Supp` facts, no `Settles` in sight |
| `ProbabilisticLogic.Dp.Settle` (+`Settles-ret⋆`) | generic — one more junction |
| `ProbabilisticLogic.Dp.Settle.Iter` | generic — at any `Body`, any kernel, any rank |
| `ProbabilisticLogic.Distribution.RationalDist.Expectation` (+) | generic — `E⊥`'s algebra |
| `CategoricalCrypto.Protocol.Machine.Trace` | generic — at any traced machine |
| `CategoricalCrypto.GamePlaying.Partial` | generic — at any partial kernel |

Nothing here mentions an example, and no example was touched: `Examples/**` is
untouched on this branch, as are `UC/**`, `Protocol/**` and `Machines/**`.

## Modules

All checked with `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`,
rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted|No space left`
gate. Every warm column is a single-`Checking`-line run, forced by deleting
that module's own `.agdai` under `_build/2.8.0/agda/src/`.

| module | LOC | warm | rule-5 budget |
|---|---|---|---|
| `ProbabilisticLogic.Dp.Support` | 65 | 4 s | 76 s |
| `ProbabilisticLogic.Dp.Settle.Iter` | 183 | 7 s | 105 s |
| `ProbabilisticLogic.Dp.Settle` (−20 +14) | 290 | 6 s | 132 s |
| `CategoricalCrypto.Protocol.Machine.Trace` | 108 | 10 s | 87 s |
| `ProbabilisticLogic.Distribution.RationalDist.Expectation` (+54) | 222 | 6 s | 115 s |
| `CategoricalCrypto.GamePlaying.Partial` | 293 | 60 s | 133 s |

`GamePlaying.Partial` at 60 s against a 133 s budget is the only one worth a
word: it is `badProb⊥-super`'s and `FLGP⊥`'s two recursions over `Strat`,
each with a `with`-abstraction on `bad s`, and `GamePlaying.agda`'s own pair
costs the same order. It is not a rule-31 defect; it is the same argument
twice, once per layer, which is what item 2 asked for.

## Nothing was weakened

No pre-existing statement was edited. `badProb`, `badProb-super`,
`badProb-bounded`, `Coupling.FLGP`, `Hop.StepBisim`, `runWith-bisim`,
`hop-bound`, `Potential`'s certificates, `Settles`, `Settles-bind`,
`Settles-bind⋆`, `Settlesᵀ*`, `StepSettles`, `rawAgree`, `rawPr`, `rawKernel`,
`traceStep`, `solve`, `loopBody`
and `extraction-bound` keep their statements verbatim. Three lemmas moved
module without a character changing — `Eⱼ`, `E⊥-map` and `E⊥-map-bind`, from
`Dp.Settle` to `RationalDist.Expectation`, where `E⊥` is defined and where they
are now used by two cones instead of one.
