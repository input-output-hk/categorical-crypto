# `Rcom → Icom`: the theorem boundary (B1) and the residual obligations (B2)

**Status.** Delivered: the resource-installed statement `Realization`/`Realizationʰ`
and the coin-toss assembly from it (§6), and the real-side legs of the proof
(§7 "Delivered"). Remaining: the proof of `Realization` itself, blocked at the
IDEAL side's game bisimulation (§7 B2-M3, B2-M4), then the route of §7; the
receiver twin `Realizationʰ` is stated and has a candidate schedule (§5), but its proof
chain is not analysed here.

Module paths are under `CategoricalCrypto.` unless prefixed. The checked
statement lives in `Examples.ROCommitment.Realization.Assembly`.

## 0. The hypothesis to discharge

```agda
coin-toss-ideal  : realᶠ  ≤UC^ωᵉ idealᶠ                 -- Examples.CoinToss.Ideal.Compose
                 → (λ n → (tossᶠ  ∙ᶠ realᶠ)  n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-toss-idealʳ : realʰᶠ ≤UC^ωᵉ idealʰᶠ                -- Examples.CoinToss.Ideal.Receiver.Compose
                 → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
```

Both premises are at the OPEN resource domain `Resᶠ`
(`Examples.CoinToss.Compose`), so their closure quantifier ranges over every
query-bounded `m : 𝟙 ⇒ W ⊗₀ ifaceᵒ (Resᴵ n)`. The bound behind them
(`Examples.ROCommitment.Game.extraction-bound`) is proved against ONE resource.
So the theorem to prove is the resource-INSTALLED one, and the assembly
theorem (§6) consumes it; the two theorems above keep their statements and
their schedule pins.

## 1. The theorem signature

### 1.1 The two compared families

`Examples.ROCommitment.Realization.Assembly`: `Rcom n = realᶠ n ∘ resᶠ n`,
`Icom n = idealᶠ n ∘ resᶠ n` (and `Rcomʰ`/`Icomʰ` over `realʰᶠ`/`idealʰᶠ`),
all `Homᶠ (λ _ → 𝟘ᵒ) …`, and

```agda
Realization  = Rcom  ≤UC^ωᵉ Icom
Realizationʰ = Rcomʰ ≤UC^ωᵉ Icomʰ
```

`_≤UC^ωᵉ_` is `UC.Quantitative.Family`'s
`Σ[ s ∈ Y ⇒^ω X ] Σ[ ε ] NegligibleBound ε × f ≤UC[ s , ε ] g`, at the sealed
machine via `UC.Model.Family.Contextual` — the same instance the two headline
theorems are stated in. Nothing here is a new relation.

### 1.2 Closing the domain does not touch the grade

`_≤UC^ωᵉ_ {A} {X} {B} f g` reads the DOMAIN `A` and the GRADE `X` at different
places: the simulator is `Y ⇒^ω X`, indexed only by the two grades, and the
domain appears only as the source of `f n`. Replacing `A = Resᶠ` by
`A = λ _ → 𝟘ᵒ` therefore leaves the simulator's type, the adversary port and
the leak port exactly as they are. In `_≈ᵁᵠ[_]_`
(`UC.Quantitative.Contextual`) the closure is `m : 𝟙 ⇒ W ⊗₀ A n`, and at
`A n = 𝟘ᵒ` it carries the ancilla only — the resource's memory has left the
context's hands, which is the whole content of `docs/coin-toss.md` §5 "Why the
comparison boundary has to be CLOSED", while the test
`E : W ⊗₀ (X n ⊗₀ B n) ⇒ Ω` still sees the full grade `X n`.

### 1.3 Parenthesization

The existing chain is parenthesized as `(stage ∙ᶠ commitment) ∘ resource`; the
resource-installed premise as `stage ∙ᶠ (commitment ∘ resource)`. `_∙ᶠ_` is
`ext (X n) (k n) ∘ f n`, so the two differ by one `∘`-associativity, which
`≤UC^ωᵉ-resp` absorbs with the SAME simulator and schedule. The assembly does
not spend `≤UC[]-dom`: the new premise is closed already.

## 2. The simulator

`_≤UC^ωᵉ_`'s first component is a `Lkᶠ ⇒^ω Advᶠ`: a family
`(n : ℕ) → ifaceᵒ (Lkᴵ n) ⇒ ifaceᵒ (Advᴵ n)` certified at a rate schedule
`r : ℕ → ℕ⁺` with `Poly⁺ r`, one grading hom at `r n` per level.

**Corrupted committer.** `Examples.CoinToss.Compose.comSim`, at rate 2 over
`Examples.ROCommitment.UC.simᵒ = procᵒ simulator`, with `simQB : QB 2 simulator`
from the exact ledger behind `simCert`.

**Corrupted receiver.** `comSimʰ` beside it, at rate 1 over `ROHU.simʰᵒ` and
`simQBʰ : QB 1 simulatorʰ`.

**The adversarial ports the simulator must retain.** They are fixed by the two
grades and closing the domain does not narrow them:

| port | constructors | module |
|---|---|---|
| `Advᴵ = AdvA ⇿ AdvQ` | up `queryᴬ`, `commitᴬ`, `openᴬ`; down `ansᴬ` | `Examples.ROCommitment` |
| `Lkᴵ = LkA ⇿ LkQ` | up `hashˢ`, `commitˢ`, `openˢ`, `failˢ`; down `digˢ` | same |
| `Advᴵʰ = AdvAʰ ⇿ AdvQʰ` | up `askᴿᶜ`; down `ansᴿᶜ`, `comᴿᶜ`, `opnᴿᶜ` | `Examples.ROCommitment.Hiding` |
| `Lkᴵʰ = LkAʰ ⇿ LkQʰ` | up `relayᶠ`; down `digᶠ`, `rcptᶠ`, `bitᶠ` | same |

(`Iface`'s fields are `Pos Neg`, so `Neg (A ⇿ B) = B` is the "up" direction a
context drives.)

Two things the simulator's retention requires, both readable off the ideal
functionality's wire `ideal = wireᴹ upᶠ downᶠ`:

* **Oracle access survives the closure.** `downᶠ` sends `hashˢ x ↦ hashᴿ x`,
  so after `_∘ resᶠ n` the simulator still reaches the SAME oracle table the
  real receiver relays to (`realStep`'s `queryᴬ` clause). One resource under
  both sides is what makes that the same oracle and not two copies.
* **The extraction port survives.** `commitˢ b ↦ putᴿ b`, `openˢ ↦ getᴿ`,
  `failˢ ↦ nakᴿ`; the cell is the functionality's memory
  (`Examples.ROCommitment.Resource.resStep`). Closing the domain FIXES what the
  cell does (`cell-put`/`cell-get`/`cell-nak`) without removing the
  simulator's ability to drive it.

## 3. The permitted context class

`Rcom ≈ctx[ ε ] subᶠ comSim Icom` is, at each `n`, `_≈ᵁᵠ[ ε n ]_`:

```agda
(W : Obj) (E : W ⊗₀ (Advᶠ n ⊗₀ Honᶠ n) ⇒ Ω) (m : 𝟙 ⇒ W ⊗₀ 𝟘ᵒ) {c r′ : ℕ⁺}
→ Image forget c E → Image forget r′ m
→ ⟦ (E ∘ id ⊗₁ Rcom n) ∘ m ⟧ ≈[ ε n (value (c · r′)) ] ⟦ (E ∘ id ⊗₁ (subᶠ comSim Icom n)) ∘ m ⟧
```

* Ancilla `W` arbitrary, per level.
* Test `E` an arbitrary model morphism certified at a rate `c`.
* Closure `m` an arbitrary morphism into the ancilla certified at a rate `r′`;
  at the closed domain it supplies no resource.
* The error is read at `value (c · r′)`, the product of the two rates.
* Neither compared hom's own query bound is read.

Certificates the theorem needs all exist: `comSim`/`comSimʰ` for the witness;
`Examples.ROCommitment.UC.resourceQBᵒ` (the rate-0 `qb-closed` raised by
`qb-mono`) for the resource at the unit rate; `RcomQB`/`RcomʰQB` (Assembly)
for the real families. No rate schedule
on the compared families is needed for `Realization` itself: `_≤UC^ωᵉ_` does
not carry one.

## 4. The assumption ledger

Read off the interfaces and the machines.

### 4.1 Resource assumptions

| # | assumption | source | status |
|---|---|---|---|
| R1 | The oracle is the lazily-sampled table of `resource`: a repeat point is answered from the table, a fresh one draws `uniformₚ k` and is kept | `Examples.ROCommitment.Resource.lazyₚ`, `lazy-hit`/`lazy-miss` | a definition; the theorem is about this resource and quantifies over no other |
| R2 | The commitment cell is one-shot and faithful: first `putᴿ` receipts and stores, `getᴿ` returns what was stored, `nakᴿ` refuses | `resStep`, pinned by `cell-put`/`cell-get`/`cell-nak` | holds at the concrete resource. This is exactly what the OPEN domain does not give — `docs/coin-toss.md` §5 exhibits a closure answering every `getᴿ` with `outᴿ true` |
| R3 | ONE resource, shared by both compared systems | the statement's shape: `_∘ resᶠ n` on both sides | structural |
| R4 | The resource is closed and asks nothing downward: `QB 0`, entering the grading at `1⁺` | `qb-closed resource`, `resourceQBᵒ` | theorem |
| R5 | Off-protocol resource activations diverge (`botₚ`): a second `putᴿ`, a `getᴿ` before one | `resStep` | part of the model; the proof must PRESERVE it (residual B2-M3) |

### 4.2 Encoding assumptions

| # | assumption | source | status |
|---|---|---|---|
| E1 | The digest length IS the security parameter, so the schedule is the identity and nothing reindexes `n` | `Examples.ROCommitment (k : ℕ)`, `Examples.ROCommitment.Asymptotic` | structural to the family |
| E2 | `real` is the honest receiver: it relays the adversary's oracle queries, takes `commitᴬ c` on trust, and at `openᴬ b r` hashes `b ∷ᵛ r` itself and accepts iff the digest matches | `Examples.ROCommitment.realStep` | definition |
| E3 | `simulator` extracts from the relay log via `extract` and releases only when digest and extracted bit both agree (`release`) | `Examples.ROCommitment.simStep`, `Examples.ROCommitment.Extraction` | definition; its FAILURE probability is the game's `bad` |
| E4 | `ideal` is a stateless relabelling `wireᴹ` of the resource's ports — the functionality's memory is the cell | `Examples.ROCommitment.ideal`; rationale `docs/fcom-extraction.md` §"Where `F_com`'s memory lives" | definition |
| E5 | Off-protocol protocol activations diverge: a second `commitᴬ`, an `openᴬ` before a commitment, a resource answer `digᴿ` arriving with nothing in flight | `realStep`, `simStep` | model; must be preserved, not assumed away |

### 4.3 Feasibility assumptions

| # | assumption | source | status |
|---|---|---|---|
| F1 | Tests and closures are QUERY-bounded (`Image forget c E`, `Image forget r′ m` at `c r′ : ℕ⁺`), and the error is read at `value (c · r′)` | `UC.Quantitative.Contextual._≈ᵁᵠ[_]_` | structural — there is NO uniform-polynomial local-runtime claim anywhere in the statement |
| F2 | The schedule is negligible at every POLYNOMIAL allowance (`NegligibleBound`) | `UC.Approximate`; `Examples.ROCommitment.Asymptotic.εᶜ-negligible` | theorem for the candidate schedule of §5 |
| F3 | The simulator costs `2` downward messages per activation, `poly-const 2` | `Examples.ROCommitment.UC.simCert`, `comSim` | theorem |
| F4 | The game bound holds only at `asks≤ m d` for a FINITE strategy `d : Strat Q R` | `Game.extraction-bound` | theorem at the game; crossing to contexts is `dominatedᵍᵠ` |

### 4.4 Corruption and session scope, as the interfaces give it

* **STATIC corruption, fixed at the type level.** There is no corrupt message
  on any interface and no corruption event in any step function. Which party
  is corrupt is which MODULE is composed: `Examples.ROCommitment` puts the
  committer's three messages on `Advᴵ` and leaves `Honᴵ = HonA ⇿ ⊥`
  report-only; `Examples.ROCommitment.Hiding` puts the receiver on `Advᴵʰ` and
  gives the honest committer a driving port `Honᴵʰ = HonAʰ ⇿ HonQʰ`. Nothing
  in either supports adaptive corruption, and the statement must not be
  described as doing so.
* **ONE corrupted party per theorem.** The two cases are two theorems over two
  protocols, not two instances of one (`docs/fcom-hiding.md`).
* **SINGLE SESSION, SINGLE COMMITMENT.** The cell refuses a second `putᴿ`,
  `real` refuses a second `commitᴬ`, and `simulator` likewise. So each level
  `n` is one commitment instance; there is no multi-session or
  concurrent-instance content, and none may be claimed.
* **The environment cannot drive the extraction side through `Honᴵ`.**
  `Neg Honᴵ = ⊥`, so a `Strat (Neg Honᴵ) (Pos Honᴵ)` has no `ask`. The driver
  is the adversary port, which is the grade — which is why the contextual
  statement must keep the grade open and why the density lemma is the
  nontrivial-grade `UC.Model.Dominated.dominatedᵍᵠ`.

## 5. The candidate error schedule

CANDIDATE, to verify at proof time; not a pin.

The game bound, merged into one numerator (`Examples.ROCommitment.Asymptotic`):

```agda
εᶜ : ℕ → ℕ → ℚ
εᶜ n q = fromℕ (q * q + q + q) *ℚ inv-pow-2 n          -- (q² + 2q)·2⁻ⁿ
```

**No slack.** `dominatedᵍᵠ`/`dominatedᵍ` are exact (`≈ₚ[ ε ]`), so the
realization schedules are the game bounds themselves:

```agda
εᴿ  = εᶜ          -- (q² + 2q)·2⁻ⁿ        (corrupted committer)
εᴿʰ = εᵗ          -- 3q·2⁻ⁿ               (corrupted receiver)
```

with `εᵗ n q = fromℕ (q + (q + q)) *ℚ inv-pow-2 n`
(`Examples.ROCommitment.Hiding.Asymptotic`); negligibility is `εᶜ-negligible`
(resp. `εᵗ-negligible`).

**Every allowance transformation, in order.**

| step | what moves the allowance | factor |
|---|---|---|
| 1. game bound | `asks≤ m d` on `Strat Q R` (`Game.extraction-bound`) | — |
| 2. game ports ↔ machine ports | `Game.Q`/`Game.R` against `Neg`/`Pos (Advᴵ ⊗ᴵ Honᴵ)`; the relabelling is 1:1 on asks (`idleR` is outside the image) | ×1 (`Realization.Bisim.toQ`/`fromR`, B2-M7) |
| 3. per-strategy → per-context | `dominatedᵍᵠ`: hypothesis at `asks≤ (value (c · c′)) d`, conclusion read at `ε (value (c · c′))` — exactly `_≈ᵁᵠ[_]_`'s convention | identity |
| 4. domination | `dominatedᵍᵠ` is exact | identity |
| 5. assembly, inner leg | `≤UC[]-compose`'s `composeError` reads `εf n (scale q (1⁺ · 1⁺))`; `scale q 1⁺ = q ℕ.* 1` (`scale-unit`) | identity |
| 6. assembly, outer leg | the upper stage compared with itself at the zero schedule | `+ 0ℚ` |
| 7. second hop | `≤UC[]-trans`'s `seqError` reads it at `scale q (schedOf s n)`; the hop's own schedule is `0ℚ` (committer, `coin-hybridᵇ`) or `ηʰ`, which ignores its allowance (receiver, `coin-hybridʳᵇ`) | `+ 0ℚ` / `+ 2⁻ⁿ` |

Composed candidates, in the existing pins' own expressions (`εᶜⁱ`,
`Examples.CoinToss.Ideal.Compose`; `εᶜʳ`, `…Receiver.Compose`):

```text
committer :  εᶜⁱ εᴿ  n q  =  (q² + 2q)·2⁻ⁿ
receiver  :  εᶜʳ εᴿʰ n q  =  3q·2⁻ⁿ + 2⁻ⁿ  =  (3q+1)·2⁻ⁿ
```

Neither replaces `ideal-ε` or `ideal-εʳ`: those pin the schedule as a FUNCTION
of the premise's schedule and keep checking unchanged. The new numbers are the
instances at `εᴿ`/`εᴿʰ` and get their own pins.

## 6. The assembly — DELIVERED

`Examples.ROCommitment.Realization.Assembly`: `RcomQB`/`RcomʰQB`,
`coin-from-Rcom`/`coin-from-Rcomʰ` (`Examples.CoinToss.Compose.toss-over` at
the resource-installed pair), `assembly`/`assemblyʰ` (`≤UC^ωᵉ-resp` for the
associativity, then `≤UC^ωᵉ-trans` against `coin-hybridᵉ`/`coin-hybridʳ`), and
`pin`/`pinʰ` (`refl`): the assembly carries the SAME schedule expression
`coin-toss-ideal`/`coin-toss-idealʳ` carry for the open premise, so switching
the headline theorems' premise from open to resource-installed changes no
number.

## 7. B2 — the residual obligations, checked against source

### Delivered (verified present)

| item | content | where |
|---|---|---|
| B2-1 | `Settles` at a loop junction | `ProbabilisticLogic.Dp.Settle.Iter`: `Settles-stepᵢ`, `Settles-stepᵢˢ`, `Ranked`, `Settles-iter` |
| B2-2, B2-M1 | `StepSettles` at a traced machine and at a `𝒢ₚ`-composite | `Protocol.Machine.Trace`: `trace-settles`; `Kᴳ`/`kᴳ-settles`, `ranked-from-kᴳ`, `compose-settles`, `compose-StepSettles`, `compose-pr`. No `Settles` witness rides an `S.≈ᴹ` to `𝒢ₚ`'s own `_∘_`, but the CLOSED RUN's conclusion does, by `ProbabilisticLogic.Dp.Settle.cum-settled-≈ₚ` |
| B2-3 | the `Dₚ`→kernel transport at an arbitrary closed machine | `Protocol.Machine.Raw`: `StepSettles`, `rawAgree`, `rawPr` |
| B2-4 | the RESOURCE's own instance of it | `Examples.ROCommitment.Transport`: `resK`, `resource-settles`, `resource-run`, `resKᵀ` (the game's `fetchT`, relabelled) |
| B2-5 | the partial-kernel game toolkit | `GamePlaying.Partial`: `badProb⊥`, `SuperCert⊥`, `badProb⊥-super`, `FLGP⊥`, `StepBisim⊥`/`StepBisim⊥ʳ`, `runWith⊥-bisim`/`runWith⊥-bisimʳ`, `embedᵏ`, `total⇒⊥`, `prune`, `hop-boundᵇ⊥`, `badProb⊥-cong`; `GamePlaying.prune-cert` |
| B2-6 | the closed game and its supermartingale | `Examples.ROCommitment.Game`: `keep-or-sample`, `rare-raise`, `cert`, `extraction-bound`, `stepR`, `stepI` |
| B2-8, B2-M5 | the density lemma at a NONTRIVIAL grade, budgeted | `UC.Model.Dominated.dominatedᵍᵠ` (hypothesis at `asks≤ (value (c · c′)) d`) and its unbudgeted instance `dominatedᵍ`, in use at `Examples.CoinToss.Ideal.Receiver.Compose` |
| B2-9 | the run-agreement deferred-sampling engine | `GamePlaying.Defer.Run`: `DeferStep`, `runFrom-defer`, `run-defer` |
| B2-M2 (real) | `Ranked` at the real side | `Examples.ROCommitment.Realization.Machine.rankedᴿ` (`real 𝒫.∘ resource`, rank bound `boundᴿ`), step-table fact `real-up`, closed kernel `Kᴿ`; generic support clauses `ProbabilisticLogic.Dp.Supp-bot`/`Supp-return`/`Supp-bind` |
| B2-M7 | the ask-preserving relabelling `Neg (Advᴵ ⊗ᴵ Honᴵ) ↔ Game.Q`, `Game.R → Pos (Advᴵ ⊗ᴵ Honᴵ)` | `Examples.ROCommitment.Realization.Bisim`: `toQ`, `fromR`, `verdict-realOpen`. `idleR` is no interface answer and `fromR` sends it anywhere, which is sound because `prune deadR` removes exactly the activations that produce it. Strategy half: `Strategy.mapStrat`, `asks≤-mapStrat` |
| B2-M8 | `comSimʰ` | `Examples.CoinToss.Compose` |

### Missing (verified absent)

| item | statement | verdict |
|---|---|---|
| B2-M2 (ideal) | `Ranked` instances at `ideal`, `subᴵ simulator` and the ideal composite | ABSENT; needed by B2-M4's ideal leg, and any `simStep` repair (B2-M3) changes the machine they are about |
| B2-M3 | the example's two `StepBisim⊥`s against pruned kernels, with `deadR`/`deadI` naming the off-protocol activations | REAL SIDE DELIVERED — `Realization.Bisim`: `deadR`, `respR⊥ = prune deadR respR`, `_≋ᴿ_`, `bisimᴿ : StepBisim⊥ʳ toQ fromR Kᴿ respR⊥ _≋ᴿ_`. IDEAL SIDE IMPOSSIBLE at the machines as they stand: `simStep` conses `(x , d)` onto the simulator's log at EVERY relayed answer, including one the oracle served from its table, so after a repeated query the log holds the digest twice and `extract` reads `false` (`Bisim.extract-relog`, `sim-log-repeat`) where `Game.comI`'s `extract c t` reads the committed bit (`Bisim.extract-table`) — and the game's bad event is `dup` of the ORACLE's answer log, which a repeat does not raise. No state relation can repair it. Maintainer call: either `simStep` caches (only cons a point the log does not already answer) or `Game.respI` is restated over the relay log — the second makes `Game.cert` false, since a repeated query raises `dup` with certainty |
| B2-M4 | `binding-bound`: the two-sided `cum` bound between the real and simulated-ideal CLOSED machines at every `asks≤ m d` | BLOCKED by B2-M3's ideal side. The REAL leg is delivered — `Realization.Bound`: `real-run` (the closed machine's `cum` family reaches `Pr₁⊥ (runWith⊥ respR⊥ sR₀ (mapStrat toQ fromR d))` exactly), `game-bound⊥` (`Game.cert` through `prune-cert` and `hop-boundᵇ⊥`, because pruning the COUPLING and pruning its marginal are only `E⊥`-equal), and `extraction-real`, which bounds the closed real MACHINE against the pruned ideal GAME (`respI⊥ = prune deadI respI`) by `Game.ε m` at every `asks≤ m d`. What is missing is only the replacement of that ideal game by the ideal machine |
| B2-M6 | `gradedᵒ f ∘ procᵒ g ≈ gradedᵒ (f 𝒫.∘ g)` at a SINGLE grade | ABSENT; it is `G.Equiv.refl` inside `UC.Model.Graded`'s `opaque` block, beside `graded₂-∘ᵒ`, so add it with its consumer (route step 3) |

### The route, once B2-M3, B2-M4 and B2-M6 are in

1. `binding-bound` (B2-M4) at `u = real 𝒫.∘ resource`,
   `v = subᴵ simulator 𝒫.∘ (ideal 𝒫.∘ resource)`, both `Proc unitᴵ (Advᴵ ⊗ᴵ Honᴵ)`.
2. `dominatedᵍᵠ` at `P = Advᴵ`, `B = Honᴵ` → `_≈ᵁᵠ[ εᴿ n ]_` for every
   ancilla `W` and every budgeted `E`, `m`; at every `n` that is
   `_≈ctx[ εᴿ ]_` by definition.
3. `≈ctx-resp` against B2-M6 and `UC.Model.Graded.sub-gradedᵒ` to bring the
   two sides into the `Rcom` / `subᶠ comSim Icom` spelling.
4. Package: `comSim , εᴿ , εᴿ-negligible , (3)` — that is `Realization`.
5. `assembly` (§6).

The closure quantifier that `docs/fcom-uc.md` §4 and `docs/dp-transport.md`
§"Not delivered" 5 leave OPEN is closed by construction here: the
resource-installed boundary has `A n = 𝟘ᵒ`, so there is no resource left for a
closure to supply. That is the entire reason B1 moves the boundary.
