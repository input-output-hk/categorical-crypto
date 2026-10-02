# Blum coin-tossing over `F_com`, and the second hop to an ideal coin

Module paths are under `CategoricalCrypto.` unless prefixed.

§1–§4: **Blum coin-tossing run over the hash-based commitment emulates Blum
coin-tossing run over the ideal `F_com`, with the commitment's own ε carried
through the composition and every certificate the composition law demands
proved rather than assumed.** One theorem per corruption case.

§5 is the **second hop**, the one a textbook writes: **the same system emulates
an IDEAL COIN, exactly**, for the corrupted committer. Two things decide its
shape. The shape the composition law `≤UC[]-compose` would consume is FALSE —
its simulator is a tensor and cannot see the committed bit. The shape that is
true needs a JOINT simulator, and a joint simulator can only be compared where
the ideal functionality's memory is not the CONTEXT's to choose: the wire
placement that makes a one-level emulation affordable (`docs/hash-forward.md`,
`docs/fcom-extraction.md`) is exactly what forces the second level's
comparison boundary to be CLOSED. Closing it is free.

For the corrupted RECEIVER the coin is drawn in one activation and combined
with the adversary's share in another, so no state map — hence no
`Machines.Sim._≲_` — relates the two worlds, and the hop is a RUN equality
carried into a context. That is exact at the run layer and costs one positive
slack at the context layer, so it lands at `2⁻ⁿ` where the committer's lands
at `0` (§5, last subsection).

The commitment's own UC-level ε-statement is the one hypothesis of every
theorem here; it is an argument, not a postulate, and its resource-installed
restatement and remaining obligations are `docs/rcom-icom-b1.md`.

## 1. The placement, and the interface algebra

The composition law is `UC.Quantitative.Family.≤UC[]-compose` (at the sealed
model through `UC.Model.Family.Contextual`):

```text
  (sf : Y ⇒^ω X) (t : Q ⇒^ω P) (rf rv : ℕ → ℕ⁺) (εf εu : ℕ → ℕ → ℚ)
→ ((n : ℕ) → Image forget (rf n) (f n)) → ((n : ℕ) → Image forget (rv n) (v n))
→ f ≤UC[ sf , εf ] g → u ≤UC[ t , εu ] v
→ (u ∙ᶠ f) ≤UC[ sf ⊗^ω t , composeError rf (λ n → rv n · schedOf t n) εf εu ] (v ∙ᶠ g)
```

where `f ≤UC[ s , ε ] g` is `f ≈ctx[ ε ] subᶠ s g` by definition, and
`_∙ᶠ_ : Homᶠ B P C → Homᶠ A X B → Homᶠ A (X ⊛ω P) C`. So **`f` is the INNER
realization** (`A ⇒ X ⊛ B`, here the commitment) and **`u` the OUTER protocol**
(`B ⇒ P ⊛ C`, here the coin toss); the outer protocol's DOMAIN is the inner
one's CODOMAIN. At `Examples.ROCommitment`'s extraction half that codomain is
`ifaceᵒ Honᴵ` — the honest receiver's report port, `HonA ⇿ ⊥` — so the
coin-toss stage is

```agda
Examples.CoinToss.toss : Proc Honᴵ (Advᴵᶜ ⊗ᴵ Honᴵᶜ)
```

exactly the `Proc Resᴵ (Advᴵ ⊗ᴵ Honᴵ)` shape of `docs/hash-forward.md` with the
resource below replaced by the realized subroutine.

**The corrupted party is P1, so only P2 is protocol.** P1's whole interaction
with the commitment is `Advᴵ`, which is the inner realization's own grade; the
coin-toss stage never speaks to `F_com` at all (`Neg Honᴵ` is empty) and its
only outgoing message is the share it sends P1 in the clear. Hence

| | `Neg` | `Pos` |
|---|---|---|
| `Advᴵᶜ` | `⊥` | `shareᴬ : Bool → _` |
| `Honᴵᶜ` | `⊥` | `tossedᶜ : Bool → _`, `abortedᶜ` |

and the protocol is three states: on `rcptᴴ` sample `b₂` and publish
`shareᴬ b₂`; on `openedᴴ b₁` output `tossedᶜ (b₁ xor b₂)`; on `refusedᴴ` output
`abortedᶜ`.

**The composed grades.** With `X = ifaceᵒ Advᴵ`, `Y = ifaceᵒ Lkᴵ`,
`P = Q = ifaceᵒ Advᴵᶜ` (`Examples.CoinToss.Compose`):

```text
tossᶠ ∙ᶠ realᶠ   : Homᶠ Resᶠ (Advᶠ ⊛ω Advᶜᶠ) Honᶜᶠ
tossᶠ ∙ᶠ idealᶠ  : Homᶠ Resᶠ (Lkᶠ  ⊛ω Advᶜᶠ) Honᶜᶠ
```

— the commitment's leak port becomes the LEFT half of the composed adversary
grade, and the coin toss's own adversary port the right half. The simulator
the law produces is `simᶜᵗ sf = sf ⊗^ω Category.id Fam`, the upper stage being
compared with itself at the identity. Note its **tensor shape**: the two
simulators do not communicate. §5 is about exactly that.

**Two corruption cases, two ports, two theorems.** For a corrupted RECEIVER
the honest party is the committer, whose port `Honᴵʰ` has an INHABITED `Neg`
(`commitᴱ`, `openᴱ`), so the coin-toss stage `Examples.CoinToss.Hiding.tossʰ`
drives `F_com` and is a different protocol at a different rate
(`docs/fcom-hiding.md`). There is no way to present one as an instance of the
other.

## 2. Machines and certificates

| name | module | content |
|---|---|---|
| `toss` | `Examples.CoinToss` | the corrupt-committer case's stage |
| `tossᵒ`, `tossCert`, `tossQB` | `Examples.CoinToss.UC` | its image `gradedᵒ toss`; **`Certified 0 toss`**; `Pred 1⁺ tossᵒ` by `qb-mono` and `qb-gradedᵒ` |
| `recvCert`, `recvQB` | `Examples.ROCommitment.UC` | **`Certified 1 real`** — the honest receiver; `Pred 1⁺ (gradedᵒ real)` |
| `tossʰ` | `Examples.CoinToss.Hiding` | the corrupt-receiver case's stage |
| `tossʰCert`, `tossʰQB` | `Examples.CoinToss.Hiding.UC` | **`Certified 1 tossʰ`** |
| `comCert`, `comQB` | `Examples.ROCommitment.Hiding.UC` | **`Certified 1 realʰ`** — the honest committer |
| `simJCert` | `Examples.CoinToss.Ideal.UC` | **`Certified 1 simJ`** — §5's joint simulator |
| `simJʰCert` | `Examples.CoinToss.Ideal.Receiver.UC` | **`Certified 1 simJʰ`** — its receiver twin |

(`Certified` here is `UC.QueryBound.Certified`, the raw-machine query
certificate.) `tossCert` at rate **0** is the statement that the extraction
half's stage makes no downward call whatever: `Neg Honᴵ` is empty, so no output
of `toss` can be downward, the potential stays at zero, and the rate is zero —
the same reason `UC.QueryBound.qbᵢ-closed` gives for a closed process, at a
domain that is not the unit. `tossʰCert` at rate 1 is the hiding half's stage,
which does drive `F_com`: one `commitᴱ` or `openᴱ` per activation from above,
nothing owed afterwards.

`UC.QueryBound.qb-oneCall` does not apply to these — it is stated over a
`Protocol A B`, and these are raw machines (`docs/hash-forward.md` §"Why
`real` is a raw machine") — so `recvCert`, `comCert`,
`tossʰCert`, `simJCert` and `simJʰCert` are all `UC.QueryBound.qbᵢ-upward`,
its raw-machine counterpart: at a constantly-zero potential only the half from
below is written out.

Two mechanical notes: a `Certified` clause table must split the LETTER before
the STATE wherever the machine's own step does, or a `cohL` clause at a
variable state does not reduce; and the sampling clauses go through
`Dp.Reasoning.map-bind` + `bindᶠ` rather than a bare `>>=ₚ-identityˡ`.

## 3. The composed theorems

`Examples.CoinToss.Compose`, both instances of one generic `toss-over`:

```agda
coin-toss-from-com  : realᶠ  ≤UC^ωᵉ idealᶠ  → (tossᶠ  ∙ᶠ realᶠ)  ≤UC^ωᵉ (tossᶠ  ∙ᶠ idealᶠ)
coin-toss-from-comʰ : realʰᶠ ≤UC^ωᵉ idealʰᶠ → (tossʰᶠ ∙ᶠ realʰᶠ) ≤UC^ωᵉ (tossʰᶠ ∙ᶠ idealʰᶠ)
```

with bound forms `coin-toss-from-comᵇ`/`coin-toss-from-comʰᵇ` at the named
simulator `simᶜᵗ sf` and schedule `εᶜᵗ εf`.

**What is hypothesis and what is theorem.** The hypothesis is the commitment's
UC-level ε-statement in the canonical witness form, and nothing else; it is not
a theorem yet (`docs/fcom-extraction.md` §"Not delivered" 1,
`docs/dp-transport.md` §"Not delivered"). Everything `≤UC[]-compose` asks
about the morphisms it MOVES is proved:

| obligation | discharge |
|---|---|
| `Image forget (rf n) (f n)`, `rf n = 1⁺` | `imageᵒ recvQB` / `imageᵒ comQB` — the real `F_com` protocol's own bound |
| `Image forget (rv n) (v n)`, `rv n = 1⁺` | `imageᵒ tossQB` / `imageᵒ tossʰQB` |
| `u ≤UC[ t , εu ] v` at `t = Category.id Fam`, `εu = 0` | `≈C⇒≈ctx` off `sub-identityˡ` |
| negligibility of the composed schedule | `εᶜᵗ-negligible`, by `composeError-negligible` at `poly⁺-1` and `Negligible-0` |

Nothing is asked of the schedules' order: `≈ctx-pre` regrades its closure
certificate with `L.sub[_]` and substitutes exactly
(`UC.Quantitative.Contextual.absorb-closureᵠ`).

### The composed ε, exactly

`composeError rf (λ n → rv n · schedOf t n) εf εu`, instantiated at
`rf = rv = schedOf t = 1⁺` and `εu = 0`:

```agda
εᶜᵗ ε n q = 0ℚ ℚ.+ ε n (scale q 1⁺)
```

and `toss-overᵇ` is stated at it, so a change of the substitution stops it
checking.

### …and in closed form

The extracting simulator, its rate-2 certificate and `εᶜ` with `εᶜ-negligible`
are all in the repository, so the premise narrows to the single relation that
is not:

```agda
comSim              : Lkᶠ ⇒^ω Advᶠ
coin-toss-from-comᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ
                    → (tossᶠ ∙ᶠ realᶠ) ≤UC^ωᵉ (tossᶠ ∙ᶠ idealᶠ)
composed-ε          : (n q : ℕ) → εᶜᵗ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n
```

So the composed error is **`(q² + 2q)·2⁻ⁿ`** — `Examples.ROCommitment.Asymptotic.εᶜ`
UNRESCALED. The coin-toss stage costs the test one activation and no more: it
enters the grading at `1⁺`, which `scale` reads as `q ↦ q * 1`, and nothing
else is paid for the composition. `comSimʰ` is the corrupted receiver's
simulator, at rate 1 (it programs rather than extracts).

## 4. Acceptance

`Examples.CoinToss.Test`:

* `attack-bound`, `ideal-bound`, `ideal-boundʳ` pin the three composed
  schedules (`εᶜᵗ εᶜ`, `εᶜⁱ εᶜ`, `εᶜʳ εᵗ`) at security parameter 5 and three
  queries, where they are below 1; at `k = 3` they are 15/8, 15/8 and 5/4.
* `coin-round`/`sim-round` and `coin-roundʰ`/`sim-roundʰ` are one live round
  of each ideal coin and joint simulator, read through `UC.QueryBound.behᴾ` at
  `Fcoin`, `simJ`, `Fcoinʰ`, `simJʰ`: the ideal coin leaking before it
  delivers, and the joint simulator publishing the share that lands the toss
  on that bit.

The `F_com` premise at this instance is still the abstract one. What the
repository has is the CLOSED-GAME bound (`Examples.ROCommitment.Test.bounded`,
at `k = 5`), a `Dist-ℚ` statement about two reactive kernels; the UC relation
`coin-toss-from-comᶜ` takes is `docs/fcom-extraction.md`'s `raw-emulation`,
not proved at any `k`.

## 5. The second hop: to an ideal coin, at a CLOSED boundary

"The coin toss over `F_com` emulates an ideal coin functionality." Two shapes
are available for it: one is false, the other is true and is proved for both
corruptions.

### Form A — as `≤UC[]-compose` would consume it — is FALSE

`≤UC[]-compose`'s outer comparison is `u ≤UC[ t , εu ] v` at the SUBROUTINE'S
HONEST INTERFACE, with `t : Q ⇒^ω P`, here `Lkᴵᶜ ⇒ Advᴵᶜ`. Such a `t` sees only
the coin functionality's leak port. Blum's simulator does not: it learns the
committed bit `b₁` because in the ideal world IT is the one that hands `b₁` to
`F_com`, and it publishes the share `b₁ xor c` so that the real computation
`b₁ xor share` lands on `F_coin`'s bit `c`. In the composed simulator
`sf ⊗^ω t` the two halves are a TENSOR and do not communicate, so `t` cannot
see `b₁`.

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
once. `≤UC[]-compose` is then not the vehicle at all: the hop is a plain
`_≤UC[_,_]_` bound, and `≤UC[]-trans` puts it after §3's.

#### Why the comparison boundary has to be CLOSED

`F_com`'s ideal functionality keeps its memory in the CONTEXT. That is
`docs/fcom-extraction.md`'s cell-in-the-resource decision, and it is what makes
`ideal` a `wireᴹ` and the extraction example affordable at all. But
`_≈ctx[_]_`'s closure `m : 𝟙 ⇒ W ⊗₀ ifaceᵒ Resᴵ` is universally quantified,
so at the open domain `Resᴵ` **nothing says the cell returns the bit it was
given**. The coin toss's output reads that bit; an ideal coin's output must
not. Counterexample: let `m` answer every `getᴿ` with `outᴿ true` whatever was
stored.

* Hybrid (`tossᶠ ∙ᶠ idealᶠ`): the adversary commits `b₁` through the grade,
  `putᴿ b₁` goes down and is ignored, the stage publishes `shareᴬ b₂`, the
  opening yields `openedᴴ true`, output `true xor b₂`. The environment reads
  `share xor output = true`, always.
* Ideal (`subᶠ s Fcoinᶠ`): output is `F_coin`'s own `c`, so
  `share xor output = share xor c`. For this to be `true` always, `c` must be
  determined by the share the simulator published — which is what "ideal coin"
  forbids.

So the second level has to be handed the first level's memory rather than
quantify over it: plug `Examples.ROCommitment.Resource.resource` under both
sides and compare at the CLOSED domain.

#### …and closing it is free

```agda
≤UC[]-dom : (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → Image forget 1⁺ (p n))
          → (s : Y ⇒^ω X) (ε : ℕ → ℕ → ℚ)
          → f ≤UC[ s , ε ] g → (λ n → f n ∘ p n) ≤UC[ s , ε ] (λ n → g n ∘ p n)
```

(`UC.Quantitative.Family`.) The closure absorbs `p`, so its rate becomes
`1⁺ · r′`, and the allowance `scale q 1⁺` is `q` by `scale-unit`: a closed
factor at the unit rate costs the allowance nothing. The schedule is
**unchanged** in the second hop. The resource enters at `1⁺` by
`Examples.ROCommitment.UC.resourceQBᵒ` (`qb-closed` raised by `qb-mono`).

#### The ideal coin, and what it leaks

```agda
data CoinQ : Set where sampleᵏ deliverᵏ abortᵏ : CoinQ
data CoinR : Set where coinᵏ : Bool → CoinR
Lkᴵᶜ  = CoinR ⇿ CoinQ
Fcoin : Proc unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ)
```

(`Examples.CoinToss.Ideal`.) `sampleᵏ` draws the bit ONCE and hands it to the
simulator; only then does `deliverᵏ` release it to the honest party, or
`abortᵏ` refuse. The leak is not a weakness of the statement but its content:
Blum's corrupted committer sees the honest share before it decides whether to
open, so the coin is unfair in Cleve's sense and a FAIR ideal coin has no
simulator at all. Off-protocol activations — a second `sampleᵏ`, a `deliverᵏ`
before one — are `botₚ`, as in `Examples.ROCommitment.Resource`.

#### The joint simulator

`simJ : Proc Lkᴵᶜ (Lkᴵ ⊗ᴵ Advᴵᶜ)` is exactly what Form A cannot build: one
machine on both halves of the hybrid's grade. It runs the random oracle ITSELF
— the table is its state, nothing sits below it but the coin — answers
`hashˢ`, buys the coin at `commitˢ b₁` and publishes `shareᴬ (b₁ xor c)`,
which is what makes the hybrid's `b₁ xor share` land on `c`. Its certificate
is `Certified 1`: one downward `Lkᴵᶜ` message per activation from above,
constantly-zero potential, exactly `recvCert`'s shape.

#### The machine equality

```agda
coin-machine : hybridᴹ ≈ idealᴹ          -- in 𝒫ᴵ, at Proc unitᴵ Cᵗ
hybridᴹ = (a⇐ᴵ ∘ (T₁ᴵ Lkᴵ toss ∘ ideal)) ∘ resource
idealᴹ  = subᴵ simJ ∘ Fcoin
```

(`Examples.CoinToss.Ideal.Machine`, `…Ideal.Hybrid`.) Both sides are ⊕-traces
of two STATEFUL machines, so `UC.Machine.Wire.∘-wireᴹ` does not apply — the
obstruction `docs/hash-forward.md` §"The one structural fact that makes it
affordable" prices. What does apply is `UC.QueryBound.Compose.Step`'s reading
of a `𝒢ₚ`-composite: `Nᶜ` is the composite as ONE machine with the product
state, `unfoldᶜ` the equations for its solved loop, `eq-∘ᶜ` the equality to
the category's composite, and `UC.QueryBound.Compose`'s `Walk` (`R-bot`,
`R-down`, `F-up`) the generic per-letter walks. Nothing here unrolls a trace.

The two sides' loop objects differ — `Lkᴵ ⊗ᴵ Honᴵ` against `Lkᴵᶜ ⊗ᴵ Honᴵᶜ` —
so no simulation runs between them. `Examples.CoinToss.Ideal.Reach.coinᶜ` is a
THIRD machine naming the reachable configurations, with a simulation into
each; that is `Protocol.Machine.Compose`'s `machineᶜ` method at a loop that
unrolls twice instead of recursively. A third machine is not a convenience:
`(heldᵖ b₂ , (t , nothing))` — the stage holding a share over an empty cell —
is unreachable, but a total state map has to place it, and it refuses `openˢ`
while answering `failˢ` with `abortedᶜ`, which no state of the ideal side does.

The two state maps are
`θᴴ (midᶜ t b₁ b₂) = (heldᵖ b₂ , (t , just b₁))` and
`θᴵ (midᶜ t b₁ b₂) = (midʲ t , heldᵏ (b₁ xor b₂))`, and everything they have
to match is a `returnₚ` except ONE activation. At `commitˢ b₁` the hybrid
samples the SHARE `b₂` and the ideal side samples the COIN `c`, publishing
`b₁ xor c`; the two step distributions agree only after reindexing along the
flip. That is `ProbabilisticLogic.Dp.Coin.coin-flip`: a coin whose two branch
masses agree is blind to precomposing its branch function with `not`, because
`_≈ₚ_` compares cumulative masses and not branches. It is the one-time pad in
the delay monad, and it is the one non-structural step in the whole hop.

#### Crossing the seal

`Examples.CoinToss.Ideal.UC.coin-hop` is `coin-machine` read across the seal
through the coercions for a composed system and nothing else: `ext-graded` for
the stage on top, `graded₂-∘` for the resource under it, `≈ᴹ⇒≈ᵍ₂` for the
machine equality at a TENSOR grade, and `sub-graded₂` for the joint simulator
in front (`UC.Graded`, over `UC.Model.Graded`'s `opaque` block — the seal
hides the tensor, so these cannot be derived outside it).

#### The theorems, and the error

```agda
coin-hybridᵉ     : (λ n → (tossᶠ ∙ᶠ idealᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-toss-ideal  : realᶠ ≤UC^ωᵉ idealᶠ
                 → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-toss-idealᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ
                 → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
ideal-ε          : εᶜⁱ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n
coin-toss-idealᴺ : realᶠ ≤UC^ωᵉ idealᶠ → coinRealʷ Canonicalᴺ.≤UC Fcoinʷ
```

(`Examples.CoinToss.Ideal.Compose`; bound forms `coin-hybridᵇ`,
`coin-toss-idealᵇ` at simulator `simᶜⁱ sf = Fam [ simᶜᵗ sf ∘ simᶜᶠ ]`.) The
premise is the SAME one §3 takes. The second hop is exact, so `≤UC[]-trans`'s
`seqError` reads `εᶜᵗ ε n q + 0ℚ`: reindexing the second schedule at
`scale q (schedOf s n)` changes nothing when that schedule is constantly `0ℚ`.
The closed form is therefore §3's, unrescaled — **`(q² + 2q)·2⁻ⁿ`** — and
`Test.ideal-bound` evaluates it.

`coin-toss-idealᴺ` is the same statement in the canonical LOCAL-NEGLIGIBLE
`UCSetup` (`UC.Family.Negligible.Setup.ucSetupᴺ`), through
`UC.Model.Family.Emulation.≤UC[]⇒≤UCᴺ`: that forgetting stops at `_≈ℰⁿ_` and
reads it in `ucSetupᴺ`'s own kernel instead of going through the vanishing
collapse, so the negligible witness survives (the certified simulator and a
per-context negligible witness — not `εᶜⁱ` itself, which stays at
`coin-toss-idealᵇ`). Both compared processes are closed, so the `Fam`-homs it
wants (`Fcoinʷ`, `coinRealʷ`) carry the unit rate — `qb-closed` raised by
`qb-mono` for the coin, and the composite of `tossQB`, `recvQB` and
`resourceQBᵒ` for the real side.

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

**The route taken.** `GamePlaying.Defer.Run` is `GamePlaying.Defer`'s
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
coin-toss-idealʳᴺ : realʰᶠ ≤UC^ωᵉ idealʰᶠ → coinRealʰʷ Canonicalᴺ.≤UC Fcoinʰʷ
```

(`Examples.CoinToss.Ideal.Receiver.Compose`.) Carrying a run agreement into a
CONTEXT is what costs: `UC.Model.Dominated.dominatedᵍ` — domination at a
NONTRIVIAL grade, at every strategy — charges a positive slack, paid here at
`2⁻ⁿ` (`ηʰ n _ = 0ℚ + inv-pow-2 n`), so the second hop's schedule is `ηʰ` and
the composed one `εᶜʳ ε = εᶜᵗ ε + ηʰ`. That is the whole difference from the
committer's exact hop. `UC.Graded.regrade` identifies the two spellings of a
tensor grade the seal keeps apart (`sub-graded₂` at the IDENTITY process).

`Fcoinʰ` has no abort query: the corrupted receiver's only way to stop the toss
is to withhold its share, and in both worlds the honest party then produces
nothing (see the header of `Examples.CoinToss.Ideal.Receiver`).

## 6. Not delivered

1. **No EXACT corrupted-receiver hop.** `coin-toss-idealʳ` is at `+2⁻ⁿ` where
   the committer's is at `0`, and that slack is not an artefact of the proof:
   `UC.Machine.Dominated.dominated`'s conclusion is at `ε + δ` with `0 < δ`, so
   a run agreement — which is all a deferred sampling gives — has no zero
   instance to hand a context. An exact graded statement would need the
   domination to be sharp at `δ = 0`, which the machine layer does not claim,
   or a machine equality, which §5's last subsection rules out.
2. **No exact-factoring form.** `UC.Graded.≤UCᵍ` consumes a `Factors` — an
   exact machine equality — and the composed statement is approximate, as
   the commitment's own is. The fixed-data `ᵇ` forms keep the certified simulator and the
   schedule; the `Canonicalᴺ._≤UC_` forms keep the simulator and forget the
   schedule.
3. **No closed-game bound for the composed system or the ideal coin.** The
   acceptance instance's probability bound is the commitment's, and `Test`'s
   `coin-round`/`sim-round`/`coin-roundʰ`/`sim-roundʰ` are live runs, not
   probability statements. A `Dist-ℚ` statement about the coin-toss experiment
   would need a game-layer/machine-layer bridge re-run at the composite.
