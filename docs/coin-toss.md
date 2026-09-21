# Blum coin-tossing over `F_com`, and the second hop to an ideal coin

Branches `coin-toss` (first hop) and `coin-hybrid` (second), off
`protocol-rewrite`. Paths are relative to `src/CategoricalCrypto/` unless
prefixed.

Nothing in the repository exercised `UC-compose` on a concrete protocol. §1–§4
do: **Blum coin-tossing run over the hash-based commitment emulates Blum
coin-tossing run over the ideal `F_com`, with the commitment's own ε carried
through the composition and every certificate the composition theorem demands
proved rather than assumed.** One theorem per corruption case.

§5 is the **second hop**, the one a textbook writes: **the same system emulates
an IDEAL COIN, exactly**, for the corrupted committer. Two things had to be
settled first, and they are the useful content. The shape `UC-composeᵉ` would
consume is FALSE — its simulator is a tensor and cannot see the committed bit.
The shape that is true needs a JOINT simulator, and a joint simulator can only
be compared where the ideal functionality's memory is not the CONTEXT's to
choose: the wire placement that makes a one-level emulation affordable
(`docs/hash-forward.md`, `docs/fcom-extraction.md`) is exactly what forces the
second level's comparison boundary to be CLOSED. Closing it turns out to be
free.

The corrupted-RECEIVER half of the second hop is delivered too, and §5's last
subsection is what it cost: there the coin is drawn in one activation and
combined with the adversary's share in another, so no state map — hence no
`Machines.Sim._≲_` — relates the two worlds, and the hop is a RUN equality
carried into a context. That is exact at the run layer and costs one positive
slack at the context layer, so it lands at `2⁻ⁿ` where the committer's lands
at `0`.

Everything here is a checked term. Hatches in `src/` stay at their baseline of
zero (`grep -rnE 'postulate|TERMINATING|primTrustMe|\{!' src/`: **16 before, 16
after**, all 16 the words "postulate-free" in inherited comments).

## 1. The placement, and the interface algebra

`UC.Asymptotic.Compose.UC-composeᵉ` (`UC/Asymptotic/Compose.agda:221`) reads

```text
  (sf : Certified Y X) (εf) → NegligibleBound εf → f ≈ctx[ εf ] subᶠ sf g
→ (t : Certified Q P) (εu) → NegligibleBound εu → u ≈ctx[ εu ] subᶠ t v
→ (cf) → Poly cf → QB (cf n) (f n)
→ (cv) → Poly cv → QB (cv n) (v n)
→ (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
```

with `_∙ᶠ_ : Homᶠ B P C → Homᶠ A X B → Homᶠ A (X ⊗ᶠ P) C`. So **`f` is the INNER
realization** (`A ⇒ X ⊛ B`, here the commitment) and **`u` the OUTER protocol**
(`B ⇒ P ⊛ C`, here the coin toss); the outer protocol's DOMAIN is the inner
one's CODOMAIN. At `Examples.ROCommitment`'s extraction half that codomain is
`ifaceᵒ Honᴵ` — the honest receiver's report port, `HonA ⇿ ⊥` — so the
coin-toss stage is

```agda
toss : Proc Honᴵ (Advᴵᶜ ⊗ᴵ Honᴵᶜ)                     -- CoinToss.agda:93
```

exactly the `Proc Resᴵ (Advᴵ ⊗ᴵ Honᴵ)` shape of `docs/hash-forward.md` with the
resource below replaced by the realized subroutine.

**The corrupted party is P1, so only P2 is protocol.** P1's whole interaction
with the commitment is `Advᴵ`, which is the inner realization's own grade; the
coin-toss stage never speaks to `F_com` at all (`Neg Honᴵ` is empty) and its
only outgoing message is the share it sends P1 in the clear. Hence

| | `Neg` | `Pos` |
|---|---|---|
| `Advᴵᶜ` (`CoinToss.agda:54`) | `⊥` | `shareᴬ : Bool → _` |
| `Honᴵᶜ` (`:62`) | `⊥` | `tossedᶜ : Bool → _`, `abortedᶜ` |

and the protocol is three states: on `rcptᴴ` sample `b₂` and publish
`shareᴬ b₂`; on `openedᴴ b₁` output `tossedᶜ (b₁ xor b₂)`; on `refusedᴴ` output
`abortedᶜ`.

**The composed grades.** With `X = ifaceᵒ Advᴵ`, `Y = ifaceᵒ Lkᴵ`,
`P = Q = ifaceᵒ Advᴵᶜ`:

```text
tossᶠ ∙ᶠ realᶠ   : Homᶠ (ifaceᵒ Resᴵ) (Advᴵ ⊗ Advᴵᶜ) (ifaceᵒ Honᴵᶜ)
tossᶠ ∙ᶠ idealᶠ  : Homᶠ (ifaceᵒ Resᴵ) (Lkᴵ  ⊗ Advᴵᶜ) (ifaceᵒ Honᴵᶜ)
```

— the commitment's leak port becomes the LEFT half of the composed adversary
grade, as the brief expects, and the coin toss's own adversary port the right
half. The simulator `UC-composeᵉ` produces is its own

```text
s n = (ℐ.id ⊗₁ sim t n) ∘ (sim sf n ⊗₁ ℐ.id)  :  (Lkᴵ ⊗ Advᴵᶜ) ⇒ (Advᴵ ⊗ Advᴵᶜ)
```

certified at `(cost t n ⊔ 1) * (cost sf n ⊔ 1) = 1 * 2 = 2` when `sf` is the
commitment's `Certified 2` simulator and `t` is `idᶜ`. Note its **tensor
shape**: the two simulators do not communicate. §5 is about exactly that.

**Two corruption cases, two ports, two theorems.** `docs/fcom-hiding.md` is
right that the halves are genuinely different ports, and the difference shows
here: for a corrupted RECEIVER the honest party is the committer, whose port
`Honᴵʰ` has an INHABITED `Neg` (`commitᴱ`, `openᴱ`), so the coin-toss stage
drives `F_com` and is a different protocol at a different rate
(`CoinToss/Hiding.agda:97`). There is no way to present one as an instance of
the other.

## 2. Machines and certificates

| name | file:line | content |
|---|---|---|
| `toss` | `CoinToss.agda:93` | the corrupt-committer case's stage, `Proc Honᴵ (Advᴵᶜ ⊗ᴵ Honᴵᶜ)` |
| `tossᵒ` | `CoinToss/UC.agda:50` | its image, `gradedᵒ toss` |
| `tossCert` | `:58` | **`Certified 0 toss`** |
| `tossQB` | `:91` | `QB 0 tossᵒ`, by `UC.Model.Dominated.qb-gradedᵒ` |
| `recvCert` | `:101` | **`Certified 1 real`** — `Examples.ROCommitment`'s honest receiver |
| `recvQB` | `:158` | `QB 1 (gradedᵒ real)` |
| `tossʰ` | `CoinToss/Hiding.agda:97` | the corrupt-receiver case's stage |
| `tossʰCert` | `CoinToss/Hiding/UC.agda:51` | **`Certified 1 tossʰ`** |
| `comCert` | `:113` | **`Certified 1 realʰ`** — `Hiding`'s honest committer |
| `simJCert` | `CoinToss/Ideal/UC.agda:62` | **`Certified 1 simJ`** — §5's joint simulator |

`tossCert` at rate **0** is the statement that the extraction half's stage makes
no downward call whatever: `Neg Honᴵ` is empty, so no output of `toss` can be
downward, the potential stays at zero, and the rate is zero — the same reason
`UC.QueryBound.qbᵢ-closed` gives for a closed process, at a domain that is not
the unit. `tossʰCert` at rate 1 is the hiding half's stage, which does drive
`F_com`: one `commitᴱ` or `openᴱ` per activation from above, nothing owed
afterwards.

`recvCert` and `comCert` are the two `F_com` real protocols' own bounds. Neither
existed: `Examples.ROCommitment.UC` and `…Hiding.UC` certify the SIMULATORS
only, because until now nothing moved the real process into a context.
`UC.QueryBound.qb-oneCall` does not apply — it is stated over a
`Protocol A B`, and these are raw machines (`docs/hash-forward.md` item 5) — so
both are the amortised certificate written out, with a constantly-zero
potential.

Two mechanical notes, both cost-free once known and both worth a reader's
second: a `Certified` clause table must split the LETTER before the STATE
wherever the machine's own step does, or a `cohL` clause at a variable state
does not reduce; and the sampling clauses go through
`Dp.Reasoning.map-bind` + `bindᶠ` rather than a bare `>>=ₚ-identityˡ`.

`Examples.Commitment` is untouched: it is the old layer-1 example and shares no
name with anything here.

## 3. The composed theorems

`CoinToss/Compose.agda`.

```agda
coin-toss-from-com  : realᶠ  ≤UC^ωᵉ idealᶠ  → (tossᶠ  ∙ᶠ realᶠ)  ≤UC^ωᵉ (tossᶠ  ∙ᶠ idealᶠ)   -- :82
coin-toss-from-comʰ : realʰᶠ ≤UC^ωᵉ idealʰᶠ → (tossʰᶠ ∙ᶠ realʰᶠ) ≤UC^ωᵉ (tossʰᶠ ∙ᶠ idealʰᶠ)  -- :132
```

**What is hypothesis and what is theorem.** The hypothesis is the commitment's
UC-level ε-statement in the canonical witness form, and nothing else. It is a
hypothesis because it is not a theorem yet: `docs/fcom-extraction.md`
§"Not delivered" 1 and `docs/dp-transport.md` §"Not delivered" own its stops,
and they are the sibling's, not this branch's. It is **not** postulated
anywhere — it is an argument of both theorems, and `src/` stays hatch-free.

Everything `UC-composeᵉ` asks about the morphisms it MOVES is proved here:

| obligation | discharge | where |
|---|---|---|
| `QB (cf n) (f n)`, `cf n = 1` | `recvQB` / `comQB` — the real `F_com` protocol's own bound | `CoinToss/UC.agda:158`, `Hiding/UC.agda:179` |
| `QB (cv n) (v n)`, `cv n = 0` resp. `1` | `tossQB` / `tossʰQB` | `CoinToss/UC.agda:91`, `Hiding/UC.agda:107` |
| `Poly cf`, `Poly cv` | `poly-const 1`; `poly-const 0` resp. `poly-const 1` | `Compose.agda:88-89`, `:138-139` |
| `NegligibleBound εu` | `λ _ _ → Negligible-0` | `:85` |
| `u ≈ctx[ εu ] subᶠ t v` at `t = idᶜ` | `≈C⇒≈ctx` off `sub-identityˡ` | `:86` |

Nothing is asked of the schedules' order: `≈ctx-pre` bumps its closure
certificate with `qb-mono` and substitutes exactly
(`UC.Budget.ctxBudget-closure`).

### The composed ε, exactly

`UC-composeᵉ`'s two substitutions, instantiated:

```text
εu ↦ λ n q → εu n (simCost q (cf n))                 = λ n q → 0ℚ
εf ↦ λ n q → εf n (simCost q ((cost idᶜ n ⊔ 1) * cv n))
```

with `cost idᶜ n = 1` and `cv n ∈ {0, 1}`, so `(1 ⊔ 1) * cv n = cv n` and
`simCost q (cv n) = q * (cv n ⊔ 1) = q * 1` in **both** cases. The composed
schedule is therefore

```agda
εᶜᵗ ε n q = 0ℚ ℚ.+ ε n (simCost q 0)                  -- Compose.agda:98
```

and `schedule-pin` / `schedule-pinʰ` (`:103`, `:141`) are `refl`-proofs that the
theorems really carry it — mechanical, so they stop checking the moment the
substitution changes, in `FactorEps.migration-pin`'s sense.

Negligibility is proved AFTER the substitution, by `UC-composeᵉ` itself:
`GradedBound-+[ Negligible ] Negligible-+` over two `NegligibleBound-simCost`,
the first summand being identically `0ℚ`.

### …and in closed form

Three of the four components of the premise ARE in the repository — the
extracting simulator `simᵒ`, its `QB 2`, and `εᶜ` with `εᶜ-negligible` — so the
premise narrows to the single relation that is not:

```agda
comSim              : Certified Lkᶠ Advᶠ                                    -- :153
coin-toss-from-comᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ
                    → (tossᶠ ∙ᶠ realᶠ) ≤UC^ωᵉ (tossᶠ ∙ᶠ idealᶠ)             -- :156
composed-ε          : (n q : ℕ) → εᶜᵗ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n  -- :163
```

So the composed error is **`(q² + 2q)·2⁻ⁿ`** — `Examples.ROCommitment.Asymptotic.εᶜ`
UNRESCALED. The coin-toss stage costs the test one activation and no more, and
`simCost`'s `_⊔ 1` floor absorbs it exactly; nothing is paid for the
composition beyond the `q ↦ q * 1` the floor already charges.

## 4. Acceptance

`CoinToss/Test.agda`, at `k = 3`:

* `attack-bound : εᶜᵗ εᶜ 3 3 ≡ fromℕ 15 *ℚ inv-pow-2 3` (`:59`) — the ceiling,
  evaluated.
* `bias` (`:94`), a corrupted committer that queries the oracle at `true ∷ r`,
  commits to the answer, waits for the honest share `s`, and opens at `s` — a
  bit it did not commit to unless `s ≡ true`, which forces P2's output to
  `s xor s`, i.e. constantly `false`. Its whole advantage is the commitment's
  extraction bad event, and §3's closed form says the composition carries that
  bound unchanged.
* `bias-round` (`:103`) computes one live run of it, so the words the trace
  statement quantifies over are inhabited by an attack that reaches the
  opening — `Examples.HashForward.UC.sim-round`'s role, same chain.
* `ideal-bound` (`:71`) is the same ceiling for the WHOLE statement, §5's hop
  included, and `coin-round`/`sim-round` (`:80`, `:90`) are the two live runs
  that hop rests on: the ideal coin leaking before it delivers, and the joint
  simulator publishing the share that lands the toss on that bit.

**The `F_com` premise at this instance is still the abstract one.** What the
repository has at `k = 3` is the CLOSED-GAME bound
(`Examples.ROCommitment.Test.bounded`), which is a `Dist-ℚ` statement about two
reactive kernels; the UC relation `coin-toss-from-comᶜ` takes is the one
`docs/fcom-extraction.md` §1 calls `raw-emulation`, and it is not proved at any
`k`.

## 5. The second hop: to an ideal coin, at a CLOSED boundary

"The coin toss over `F_com` emulates an ideal coin functionality." Two shapes
are available for it: one is false, the other is true and is delivered for the
corrupted committer.

### Form A — as `UC-composeᵉ` would consume it — is FALSE

`UC-composeᵉ`'s outer comparison is `u ≈ctx[ εu ] subᶠ t v` at the SUBROUTINE'S
HONEST INTERFACE, with `t : Certified Q P`, here `Lkᴵᶜ ⇒ Advᴵᶜ`. Such a `t`
sees only the coin functionality's leak port. Blum's simulator does not: it
learns the committed bit `b₁` because in the ideal world IT is the one that
hands `b₁` to `F_com`, and it publishes the share `b₁ xor c` so that the real
computation `b₁ xor share` lands on `F_coin`'s bit `c`. In the composed
simulator `(id ⊗₁ sim t) ∘ (sim sf ⊗₁ id)` the two halves are a TENSOR and do
not communicate, so `t` cannot see `b₁`.

The refutation needs no simulator-quantifier argument, only a context. Take a
closure below `Honᴵ` that answers `rcptᴴ` and then `openedᴴ true`, and a test
that reports `share xor coin`.

* Real: `share = b₂` uniform, `coin = true xor b₂`, so `share xor coin = true`
  with probability **1**.
* Ideal: `coin` is `F`'s own bit, sampled independently of whatever the
  simulator published as `share`, so `share xor coin` is uniform and the test
  reports `true` with probability **½**.

So `ε ≥ ½` for every `t` and every `F` whose `tossedᶜ` payload is independent of
the `openedᴴ` argument — i.e. for every ideal coin functionality. An `F` that
does read the `openedᴴ` argument and outputs `b₁ xor share` is the protocol
again, and the statement is vacuous.

### Form B — the correct shape — keeps the grade and makes the simulator JOINT

The statement a textbook makes keeps the subroutine's adversary interface in
the hybrid world's grade, so the simulator faces BOTH halves of that grade at
once. `UC-composeᵉ` is then not the vehicle at all: the hop is a plain
`_≤UC^ωᵉ_` witness, and `≤UC^ωᵉ-trans` puts it after §3's.

#### Why the comparison boundary has to be CLOSED

`F_com`'s ideal functionality keeps its memory in the CONTEXT. That is
`docs/fcom-extraction.md`'s cell-in-the-resource decision, and it is what makes
`ideal` a `wireᴹ` and the extraction example affordable at all. But
`_≈ctx[_]_`'s closure `m : 𝟘ᵒ ⇒ T₀ W (ifaceᵒ Resᴵ)` is universally quantified,
so at the open domain `Resᴵ` **nothing says the cell returns the bit it was
given**. The coin toss's output reads that bit; an ideal coin's output must
not. Counterexample: let `m` answer every `getᴿ` with `outᴿ true` whatever was
stored.

* Hybrid (`tossᶠ ∙ᶠ idealᶠ`): the adversary commits `b₁` through the grade,
  `putᴿ b₁` goes down and is ignored, the stage publishes `shareᴬ b₂`, the
  opening yields `openedᴴ true`, output `true xor b₂`. The environment reads
  `share xor output = true`, always.
* Ideal (`sub s ∘ F_coinᶠ`): output is `F_coin`'s own `c`, so
  `share xor output = share xor c`. For this to be `true` always, `c` must be
  determined by the share the simulator published — which is what "ideal coin"
  forbids.

So the second level has to be handed the first level's memory rather than
quantify over it: plug `Examples.ROCommitment.Resource.resource` under both
sides and compare at the CLOSED domain.

#### …and closing it is free

```agda
≈ctx-dom   : (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → QB 0 (p n))
           → (ε) → u ≈ctx[ ε ] v → (λ n → u n ∘ p n) ≈ctx[ ε ] (λ n → v n ∘ p n)
≤UC^ωᵉ-dom : (p) → ((n : ℕ) → QB 0 (p n)) → f ≤UC^ωᵉ g
           → (λ n → f n ∘ p n) ≤UC^ωᵉ (λ n → g n ∘ p n)
```

(`UC/Asymptotic/Compose.agda:219`, `:251`.) The closure absorbs `p`, so its
budget becomes `(0 ⊔ 1) * c′` — and `ctxBudget` GUARDS its closure leg at
`_⊔ 1` rather than multiplying by it, so a factor the guard swallows costs the
allowance nothing. The schedule is **unchanged** in the second hop.

That is the route taken, in preference to instantiating `UC-composeᵉ` with the
resource as its inner realization. Both work; the `UC-composeᵉ` one would put
the resource's own trivial grade in front of the composed one
(`𝟙 ⊗ (Lk ⊗ Advᶜ)` instead of `Lk ⊗ Advᶜ`) and read the outer schedule at a
`simCost` substitution. `≈ctx-dom` leaves the grade and the schedule alone, and
its proof is six lines of
`T-homomorphism` plus one `*-identityˡ`.

#### The ideal coin, and what it leaks

```agda
data CoinQ : Set where sampleᵏ deliverᵏ abortᵏ : CoinQ
data CoinR : Set where coinᵏ : Bool → CoinR
Lkᴵᶜ  = CoinR ⇿ CoinQ                                      -- Ideal.agda:64
Fcoin : Proc unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ)                          -- :93
```

`sampleᵏ` draws the bit ONCE and hands it to the simulator; only then does
`deliverᵏ` release it to the honest party, or `abortᵏ` refuse. The leak is not
a weakness of the statement but its content: Blum's corrupted committer sees
the honest share before it decides whether to open, so the coin is unfair in
Cleve's sense and a FAIR ideal coin has no simulator at all. Off-protocol
activations — a second `sampleᵏ`, a `deliverᵏ` before one — are `botₚ`, as in
`Examples.ROCommitment.Resource`.

#### The joint simulator

`simJ : Proc Lkᴵᶜ (Lkᴵ ⊗ᴵ Advᴵᶜ)` (`Ideal.agda:150`) is exactly what Form A
cannot build: one machine on both halves of the hybrid's grade. It runs the
random oracle ITSELF — the table is its state, nothing sits below it but the
coin — answers `hashˢ`, buys the coin at `commitˢ b₁` and publishes
`shareᴬ (b₁ xor c)`, which is what makes the hybrid's `b₁ xor share` land on
`c`. Its certificate is `Certified 1` (`Ideal/UC.agda:62`): one downward
`Lkᴵᶜ` message per activation from above, constantly-zero potential, exactly
`recvCert`'s shape.

#### The machine equality

```agda
coin-machine : ((a⇒ᴵ ∘ (T₁ᴵ Lkᴵ toss ∘ ideal)) ∘ resource) ≈ᴹ (subᴵ′ simJ ∘ Fcoin)
```

(`Ideal/Machine.agda:256`.) Both sides are ⊕-traces of two STATEFUL machines,
so `UC.Machine.Wire.∘-wireᴹ` does not apply — the obstruction
`docs/hash-forward.md` §"The one structural fact that makes it affordable"
prices. What does apply is `UC.QueryBound.Compose.Step`'s reading of a
`𝒢ₚ`-composite, which existed already for the query-bound walk and is now
public: `Nᶜ` is the composite as ONE machine with the product state, `unfoldᶜ`
the six equations for its solved loop, `eq-∘ᶜ` the equality to the category's
composite (`:102`, `:189`, `:219`). Nothing here unrolls a trace.

The two sides' loop objects differ — `Lkᴵ ⊗ᴵ Honᴵ` against `Lkᴵᶜ ⊗ᴵ Honᴵᶜ` —
so no simulation runs between them. `Reach.coinᶜ` (`:103`) is a THIRD machine
naming the reachable configurations, with a simulation into each; that is
`Protocol.Machine.Compose`'s `machineᶜ` method at a loop that unrolls twice
instead of recursively. A third machine is not a convenience:
`(heldᵖ b₂ , (t , nothing))` — the stage holding a share over an empty cell —
is unreachable, but a total state map has to place it, and it refuses `openˢ`
while answering `failˢ` with `abortedᶜ`, which no state of the ideal side does.

The two state maps are
`θᴴ (midᶜ t b₁ b₂) = (heldᵖ b₂ , (t , just b₁))` (`Hybrid.agda:93`) and
`θᴵ (midᶜ t b₁ b₂) = (midʲ t , heldᵏ (b₁ xor b₂))` (`Machine.agda:84`), and
everything they have to match is a `returnₚ` except ONE activation. At
`commitˢ b₁` the hybrid samples the SHARE `b₂` and the ideal side samples the
COIN `c`, publishing `b₁ xor c`; the two step distributions agree only after
reindexing along the flip. That is `ProbabilisticLogic.Dp.Coin.coin-flip`: a
coin whose two branch masses agree is blind to precomposing its branch
function with `not`, because `_≈ₚ_` compares cumulative masses and not
branches. It is the one-time pad in the delay monad, and it is the one
non-structural step in the whole hop.

#### Crossing the seal

`UC.Graded` gains three readings beside `ext-graded`, all
`UC.Model.Seal`-discipline exports from inside the `opaque` block: `≈ᴹ⇒≈ᵍ₂`
carries a machine equality at a TENSOR grade across, `graded₂-∘` plugs a
closed process under such a hom, `sub-graded₂` puts a joint simulator in front
of one (`UC/Model/Graded.agda:73`, `:79`, `:85`;
`UC/Graded.agda:83`, `:89`). `Ideal/UC.agda:150`'s `coin-hop` is `coin-machine`
through exactly those three and nothing else.

#### The theorems, and the error

```agda
coin-hybridᵉ     : (λ n → (tossᶠ ∙ᶠ idealᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ      -- :64
coin-toss-ideal  : realᶠ ≤UC^ωᵉ idealᶠ
                 → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ      -- :67
coin-toss-idealᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ
                 → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ      -- :88
schedule-pinⁱ    : proj₁ (proj₂ (coin-toss-ideal w)) ≡ εᶜⁱ (proj₁ (proj₂ w))
ideal-ε          : εᶜⁱ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n       -- :92
coin-toss-idealᴺ : realᶠ ≤UC^ωᵉ idealᶠ
                 → Canonicalᴺ._≤UC_ (… , coinRealQB) (Fcoinᶠ , FcoinQB)   -- :118
```

(`Ideal/Compose.agda`.) The premise is the SAME one §3 takes — the
commitment's UC-level ε-statement, an argument and not a postulate. The second
hop is exact, so `≤UC^ωᵉ-trans`'s sum reads `εᶜᵗ ε n q + 0ℚ`: reindexing the
second schedule at `simCost q (cost s₁ n)` changes nothing when that schedule
is constantly `0ℚ`. The closed form is therefore §3's, unrescaled —
**`(q² + 2q)·2⁻ⁿ`** — and `Test.agda:71` evaluates it at `k = q = 3`.

`coin-toss-idealᴺ` is the same statement in the canonical LOCAL-NEGLIGIBLE
`UCSetup` (`UC.Family.Negligible.Setup.ucSetupᴺ`), through
`UC.Asymptotic.Family.≤UC^ωᵉ⇒≤UCᴺ`: that forgetting stops at `_≈ℰⁿ_` and reads
it in `ucSetupᴺ`'s own kernel instead of spending `absorb-negl`, so the
negligible witness survives where `≤UC^ωᵉ⇒≤UCᵁ` loses it. Both compared
processes are closed, so the `Fam`-homs it wants carry `QB 0` — `qb-closed`
for the coin, and the product of `tossQB`, `recvQB` and `resourceQBᵒ` for the
real side. The order is qualitative, so `Test.agda`'s numerical pins say
everything there is to say about the schedule and gain nothing from a twin.

### …and the corrupted RECEIVER, one layer up

`Examples.CoinToss.Hiding`'s half does not follow as a machine equality, and
the reason is not budget. Run its hybrid — `tossʰ` over `idealʰ` over
`resource` — at the activation sequence

1. `goᶜ`         (the environment starts the honest committer)
2. `shareᴬʰ b₂`  (the corrupted receiver sends its share)
3. `getᶜ`        (the environment collects)

The outputs are `rcptᶠ`, `bitᶠ b₁`, `tossedᶜʰ (b₁ xor b₂)` with `b₁` drawn at
step 1. An ideal coin's must be `rcptᶠ`, `bitᶠ (c xor b₂)`, `tossedᶜʰ c` with
`c` the functionality's own bit. The two distributions ARE equal — substitute
`c = b₁ xor b₂` — but that bijection depends on `b₂`, which the environment
chooses at step 2, AFTER the draw.

`Machines.Sim`'s equality cannot see it. A `_≲_`'s state map is a function of
the state alone and its step equation is quantified over every input, so a
direct map would need `γ (b₁) xor b₂ = b₁` for BOTH `b₂`. The invariant that
kills every chain is finer: a hybrid state reached after `goᶜ` fixes the
letter at `shareᴬʰ b₂` as `bitᶠ b₁`, CONSTANT in `b₂`, where an ideal state
fixes it as `bitᶠ (c xor b₂)`, which is not; a `≲` preserves that letter
function exactly, and the two post-`goᶜ` mixtures over states must match, so
some hybrid state has to be identified with some ideal one. Neither a common
machine below (its step at `shareᴬʰ b₂` would be one point mass matching two
different letters) nor one above (the two mixtures force the identification,
and both pairings fail — `¬v xor b₂ = v` holds at `b₂ = true` and fails at
`b₂ = false`) escapes it. Deferring the draw to step 2 does not either: a
point mass and a uniform mixture are not related by `≲` in either direction.

So the corrupted-receiver hop is a DEFERRED SAMPLING, and `≈ᴹ` — the
equivalence closure of state simulations — has no way to move a draw across an
activation. The extraction half escapes because its draw and its use land in
the SAME activation (`commitˢ b₁` both samples and publishes), which is
exactly what `coin-flip` settles.

**What is delivered instead.** `GamePlaying.Defer.Run` is `GamePlaying.Defer`'s
induction against `Protocol.Machine.runᴹ`: at the RUN layer a point mass and a
mixture may agree, and the draw moves. Two reachable machines are named rather
than one — `Receiver.Reach.eagerᶜʰ` draws at `goᶜ`, `deferᶜʰ` at `shareᴬʰ` —
and each simulates into one side (`Receiver.Hybrid`, `Receiver.Machine`, the
second with `coin-flip` at exactly the step the extraction half spends it at).
`Receiver.Machine.coin-runʰ` is the agreement: exact, at every strategy, no
budget condition.

```agda
coin-runʰ         : (d : Strat (Neg Cᵗʰ) (Pos Cᵗʰ)) → runᴹ hybridᴹʰ d ≈ₚ runᴹ idealᴹʰ d
coin-hybridʳ      : (λ n → (tossʰᶠ ∙ᶠ idealʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
coin-toss-idealʳ  : realʰᶠ ≤UC^ωᵉ idealʰᶠ
                  → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
ideal-εʳ          : εᶜʳ εᵗ n q ≡ fromℕ (q + (q + q)) *ℚ inv-pow-2 n ℚ.+ inv-pow-2 n
coin-toss-idealʳᴺ : realʰᶠ ≤UC^ωᵉ idealʰᶠ
                  → Canonicalᴺ._≤UC_ (… , coinRealʰQB) (Fcoinʰᶠ , FcoinʰQB)
```

Carrying a run agreement into a CONTEXT is what costs: `UC.Model.Dominated`'s
domination charges a positive slack, paid here at `2⁻ⁿ`, so the second hop's
schedule is `0ℚ + 2⁻ⁿ` and the composed one is the hiding bound plus it. That
is the whole difference from the committer's exact hop.

Two pieces of plumbing are the price, both general and both since hoisted:
`UC.Model.Dominated.dominatedᵍ`
is `dominatedᵒ` at a NONTRIVIAL grade (the model had domination only at the
trivial one, every graded statement above it being exact), and
`UC.Graded.regrade` identifies the two spellings of a tensor grade the seal
keeps apart — `sub-graded₂` at the IDENTITY process.

The chain lemmas were still not hoisted: `hearᴴʰ`/`askᴴʰ`/`cellᴴʰ`/`lkᴴʰ` and
`upᴵʰ`/`downᴵʰ`/`bypᴵʰ`/`backᴵʰ`/`honᴵʰ` are at the receiver's own ports and
have two more legs than the extraction half's, the stage driving `F_com` here
where there it only listened.

### What this does not touch

`Abstract2.UC-compose` and the `_≈ctx[_]_` relation are untouched and
unweakened; `UC.Asymptotic.Compose` gains `≈ctx-dom`/`≤UC^ωᵉ-dom` and nothing
is changed in it. No `Simulator`, `Monitor` or `MonitoredExperiment` record and
no new category appears anywhere (`docs/uc-presheaf-preservation-plan.md` §1
decisions 1-6); the new `data` declarations are the protocols' message types
and their states plus the ideal coin's port, and the only records inhabited are
`UC.QueryBound`'s existing `QBᵢ` and `Machines.Sim`'s `_≲_`.

## 6. Module costs

`pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`, rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate. The warm column is a single-`Checking`-line run; the ~7 s agda startup
floor is in every figure.

| module | LOC | warm | rule-5 budget |
|---|---|---|---|
| `Examples.CoinToss` | 94 | 9.5 s | 83 s |
| `Examples.CoinToss.UC` | 157 | 10.9 s | 99 s |
| `Examples.CoinToss.Hiding` | 99 | 9.4 s | 85 s |
| `Examples.CoinToss.Hiding.UC` | 180 | 11.2 s | 105 s |
| `Examples.CoinToss.Compose` | 164 | 11.0 s | 101 s |
| `Examples.CoinToss.Test` | 125 → 175 | 10.7 s → 10.6 s | 103 s |
| `Examples.CoinToss.Ideal` | 152 | 9.0 s | 98 s |
| `Examples.CoinToss.Ideal.Reach` | 104 | 9.6 s | 86 s |
| `Examples.CoinToss.Ideal.Hybrid` | 248 | 12.4 s | 122 s |
| `Examples.CoinToss.Ideal.Machine` | 258 | 13.2 s | 124 s |
| `Examples.CoinToss.Ideal.UC` | 156 | 10.4 s | 99 s |
| `Examples.CoinToss.Ideal.Compose` | 93 | 10.9 s | 83 s |
| `ProbabilisticLogic.Dp.Coin` | 75 → 122 | 5.9 s | 90 s |
| `UC.Asymptotic.Compose` | 278 → 322 | 10.8 s | 140 s |
| `UC.Model.Graded` | 92 → 115 | 11.0 s | 88 s |
| `UC.Graded` | 88 → 101 | 9.7 s | 85 s |
| `UC.QueryBound.Compose.Step` | 212 → 227 | 10.3 s | 116 s |

Every edit to an existing module is additive; every figure is a forced-warm
run (`.agdai` deleted, one `Checking` line each).

The corrupted-receiver hop's own, measured the same way on a machine with
three other agents compiling — the ~30 s floor below is that contention, not
the modules (the extraction half's twins above measured 9–13 s on a free box).

| module | LOC | warm | rule-5 budget |
|---|---|---|---|
| `ProbabilisticLogic.Dp.Coin` | 122 → 152 | 22.9 s | 98 s |
| `GamePlaying.Defer.Run` | 109 | 30.1 s | 87 s |
| `Examples.CoinToss.Ideal.Receiver` | 155 | 31.4 s | 98 s |
| `Examples.CoinToss.Ideal.Receiver.Reach` | 161 | 32.6 s | 100 s |
| `Examples.CoinToss.Ideal.Receiver.Hybrid` | 270 | 46.5 s | 127 s |
| `Examples.CoinToss.Ideal.Receiver.Machine` | 441 | 50.1 s | 170 s |
| `Examples.CoinToss.Ideal.Receiver.Dominated` | 166 | 34.6 s | 101 s |
| `Examples.CoinToss.Ideal.Receiver.UC` | 179 | 35.4 s | 104 s |
| `Examples.CoinToss.Ideal.Receiver.Compose` | 139 | 38.2 s | 95 s |
| `Examples.CoinToss.Test` | 175 → 224 | 34.8 s | 116 s |

`ProbabilisticLogic.Dp.Commutative` (+16, `>>=ₚ-swap`) and
`.Dp.Reasoning` (+5, `≡⇒≈ₚ`) have no isolated warm figure — both are checked
as dependencies of `GamePlaying.Defer.Run`, whose own run is warm.
`src/CategoricalCrypto.agda`, the whole-library root, is green: 78 modules,
10 m 40 s, empty gate.

**One measured perf defect, and its fix.** `Ideal.Hybrid`'s `hashᴴ` first read
its `lookupPt t x` with `with … in …`, and the module then took **3 m 22 s**
against **10 s** without it. `with` normalises the goal to find the scrutinee,
and this goal names the composite's step, which unfolds through the ⊕-trace;
the scrutinee is an explicit argument instead and the branch equations come
from `rewrite` inside the small `hashᶜ-hit`/`hashᶜ-miss` lemmas, whose goals do
not mention the trace. Both `hashᴴ` and `hashᴵ` are written that way.

Closure: `src/CategoricalCrypto.agda` and `src/CategoricalCrypto/UC.agda` rc=0
with an empty gate, and `Examples/ChimericLedger/FactorEps.agda` — the other
`UC-composeᵉ` consumer, outside that closure — and
`UC/Approximate/LocalTests.agda` likewise.

## 7. Root-file wiring

Done on the branch, not left to the maintainer:

* `src/CategoricalCrypto.agda` gains `Examples.CoinToss.Compose`,
  `Examples.CoinToss.Ideal.Compose` and `Examples.CoinToss.Test` (which between
  them reach the other eight) and an inventory paragraph beside
  `Examples.ROCommitment.*`'s.
* `src/CategoricalCrypto/UC.agda`'s `UC.Asymptotic.Compose`, `UC.Graded` and
  `UC.QueryBound` rows name the new exports and their consumers. No `UC.*`
  module is new; `UC.Model.Graded`, `UC.Graded`, `UC.Asymptotic.Compose` and
  `UC.QueryBound.Compose.Step` are already re-exported or reachable from
  `UC.agda`.

## 8. Not delivered, precisely

1. **No EXACT corrupted-receiver hop.** `coin-toss-idealʳ` is delivered, but
   at `+2⁻ⁿ` where the committer's is at `0`, and that slack is not an
   artefact of the proof: `UC.Machine.Dominated`'s conclusion is at `ε + δ`
   with `δ` positive, so a run agreement — which is all a deferred sampling
   gives — has no zero instance to hand a context. An exact graded statement
   would need the domination to be sharp at `δ = 0`, which the machine layer
   does not claim, or a machine equality, which §5's last subsection rules
   out.
   The two general pieces it spends, `dominatedᵍ` and `regrade`, were written
   at the example (this branch not having `UC/` to edit) and have since been
   hoisted beside `dominatedᵒ` and `sub-graded₂`.
2. **No `≤UC[ c ]` form of the composed statement, and no COST-certified one.**
   `UC.Graded.≤UCᵍ` and `UC.Seam.Graded.≤UC[]ᵍ` consume a `Factors` — an exact
   machine equality — and the composed statement is approximate, exactly as
   `docs/fcom-extraction.md` §"Not delivered" 3 records for the commitment
   itself. Nothing here weakens them; they do not apply. What IS delivered is
   the qualitative `Canonicalᴺ._≤UC_` form (§5's `coin-toss-idealᴺ` /
   `coin-toss-idealʳᴺ`), which keeps the simulator but forgets its cost.
3. **No closed-game bound for the composed system.** The acceptance instance's
   attack is a machine, and the probability it is bounded by is the
   commitment's; a `Dist-ℚ` statement about the coin-toss experiment would need
   the game-layer/machine-layer bridge `docs/graded-bridge.md` builds for the
   one-level case, re-run at the composite.
4. **`recvCert`/`comCert` are not `UC.QueryBound.Exact` ledgers.** Both are
   amortised ceilings. An exact ledger for the honest receiver would weigh an
   activation by a function of the LETTER alone, and it does — one oracle call
   per `queryᴬ` and per `openᴬ`, none per `commitᴬ` — so the ledger exists and
   was simply not needed by anything: `UC-composeᵉ` reads a `QB`.
5. **No `Proc`-level `qb-oneCall`.** `UC.QueryBound.qb-oneCall` is where
   `docs/ledger-lift-eps.md` §9 item 3 asked for it, but it is stated at
   `morphism P` for a `Protocol A B`, and all five machines certified here are
   raw ones (`docs/hash-forward.md` item 5), so all five write the amortised
   certificate out by hand. A `Proc`-level analogue — "every activation from
   above emits at most one downward message and nothing is owed afterwards",
   which is what a constantly-zero potential says — would collapse
   `tossʰCert`, `recvCert`, `comCert` and `simJCert` to one line each.
6. **No closed-game bound for the ideal coin either.** `Test`'s
   `coin-round`/`sim-round` and `coin-roundʰ`/`sim-roundʰ` are live runs of
   the four new machines, not a probability statement; item 3 covers both
   hops and both corruptions.
7. **`Fcoinʰ` has no abort query.** The corrupted receiver's only way to stop
   the toss is to withhold its share, and in both worlds the honest party then
   produces nothing; `F_com`'s refusal `nakᴱ` reaches the stage only through
   the resource's `rejᴿ`, which `Hiding.downᶠʰ` never asks for, so the
   `abortedᶜʰ` branch of `tossʰ` is unreachable in this composite and the
   functionality is the stronger for not offering one.
