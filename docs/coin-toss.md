# Blum coin-tossing over `F_com`: the `UC-composeᵉ` showcase, and where it stops

Branch `coin-toss`, off `protocol-rewrite` at `587999b5`. Paths are relative to
`src/CategoricalCrypto/` unless prefixed.

Nothing in the repository exercised `UC-compose` on a concrete protocol. This
branch does: **Blum coin-tossing run over the hash-based commitment emulates
Blum coin-tossing run over the ideal `F_com`, with the commitment's own ε
carried through the composition and every certificate the composition theorem
demands proved rather than assumed.** One theorem per corruption case.

What it does **not** do is reach an ideal coin functionality. That is a second
hop, it is the one a textbook writes, and §5 shows it is **false as
`UC-composeᵉ` would have to consume it** and **unprovable at this domain in the
shape that is true**. The reason is structural and is the most useful thing
here: the wire placement of an ideal functionality — the decision that makes a
ONE-level emulation affordable (`docs/hash-forward.md`,
`docs/fcom-extraction.md`) — puts that functionality's memory in the CONTEXT,
and a second protocol stacked on top has to trust it.

Everything outside §5 is a checked term. Hatches in `src/` stay at their
baseline of zero (`grep -rnE 'postulate|TERMINATING|primTrustMe|\{!' src/`:
**16 before, 16 after**, all 16 the words "postulate-free" in inherited
comments).

## 1. The placement, and the interface algebra

`UC.Asymptotic.Compose.UC-composeᵉ` (`UC/Asymptotic/Compose.agda:221`) reads

```text
  (sf : Certified Y X) (εf) → NegligibleBound εf → f ≈ctx[ εf ] subᶠ sf g
→ (t : Certified Q P) (εu) → NegligibleBound εu → Allowance-mono εu
                           → u ≈ctx[ εu ] subᶠ t v
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

certified at `(cost t n ⊔ 1) * (cost sf n ⊔ 1) = 1 * 3 = 3` when `sf` is the
commitment's `Certified 2` simulator and `t` is `idᶜ`. Note its **tensor
shape**: the two simulators do not communicate. §5 is about exactly that.

**Two corruption cases, two ports, two theorems.** `docs/fcom-hiding.md` is
right that the halves are genuinely different ports, and the difference shows
here: for a corrupted RECEIVER the honest party is the committer, whose port
`Honᴵʰ` has an INHABITED `Neg` (`commitᴱ`, `openᴱ`), so the coin-toss stage
drives `F_com` and is a different protocol at a different rate
(`CoinToss/Hiding.agda:98`). There is no way to present one as an instance of
the other.

## 2. Machines and certificates

| name | file:line | content |
|---|---|---|
| `toss` | `CoinToss.agda:93` | the corrupt-committer case's stage, `Proc Honᴵ (Advᴵᶜ ⊗ᴵ Honᴵᶜ)` |
| `tossᵒ` | `CoinToss/UC.agda:50` | its image, `gradedᵒ toss` |
| `tossCert` | `:58` | **`Certified 0 toss`** |
| `tossQB` | `:91` | `QB 0 tossᵒ`, by `UC.Model.Dominated.qb-gradedᵒ` |
| `recvCert` | `:100` | **`Certified 1 real`** — `Examples.ROCommitment`'s honest receiver |
| `recvQB` | `:156` | `QB 1 (gradedᵒ real)` |
| `tossʰ` | `CoinToss/Hiding.agda:98` | the corrupt-receiver case's stage |
| `tossʰCert` | `CoinToss/Hiding/UC.agda:51` | **`Certified 1 tossʰ`** |
| `comCert` | `:113` | **`Certified 1 realʰ`** — `Hiding`'s honest committer |

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
| `QB (cf n) (f n)`, `cf n = 1` | `recvQB` / `comQB` — the real `F_com` protocol's own bound | `CoinToss/UC.agda:156`, `Hiding/UC.agda:179` |
| `QB (cv n) (v n)`, `cv n = 0` resp. `1` | `tossQB` / `tossʰQB` | `CoinToss/UC.agda:91`, `Hiding/UC.agda:107` |
| `Poly cf`, `Poly cv` | `poly-const 1`; `poly-const 0` resp. `poly-const 1` | `Compose.agda:88-89`, `:138-139` |
| `NegligibleBound εu` | `λ _ _ → Negligible-0` | `:86` |
| **`Allowance-mono εu`** | `λ _ _ → ℚ.≤-refl` | `:86` |
| `u ≈ctx[ εu ] subᶠ t v` at `t = idᶜ` | `≈C⇒≈ctx` off `sub-identityˡ` | `:87` |

**Which side `Allowance-mono` lands on.** On `εu`, the OUTER comparison — the
one `≈ctx-pre` moves the inner process into the closure for, where
`ctxBudget-closure≤` is a bound and not an identity. Here the outer comparison
is the coin-toss stage against ITSELF (only the subroutine's world changes), so
`εu` is the zero schedule and monotonicity is `≤-refl`. That is
`Examples.ChimericLedger.FactorEps.hash-liftᵉ`'s discharge verbatim, for the
same reason: a shared upper stage.

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

* `attack-bound : εᶜᵗ εᶜ 3 3 ≡ fromℕ 15 *ℚ inv-pow-2 3` (`:60`) — the ceiling,
  evaluated.
* `bias` (`:87`), a corrupted committer that queries the oracle at `true ∷ r`,
  commits to the answer, waits for the honest share `s`, and opens at `s` — a
  bit it did not commit to unless `s ≡ true`, which forces P2's output to
  `s xor s`, i.e. constantly `false`. Its whole advantage is the commitment's
  extraction bad event, and §3's closed form says the composition carries that
  bound unchanged.
* `bias-round` (`:107`) computes one live run of it, so the words the trace
  statement quantifies over are inhabited by an attack that reaches the
  opening — `Examples.HashForward.UC.sim-round`'s role, same chain.

**The `F_com` premise at this instance is still the abstract one.** What the
repository has at `k = 3` is the CLOSED-GAME bound
(`Examples.ROCommitment.Test.bounded`), which is a `Dist-ℚ` statement about two
reactive kernels; the UC relation `coin-toss-from-comᶜ` takes is the one
`docs/fcom-extraction.md` §1 calls `raw-emulation`, and it is not proved at any
`k`.

## 5. The second hop: not delivered, and why

The statement this branch does not make is "the coin toss over `F_com` emulates
an ideal coin functionality". Two shapes are available for it and both stop.

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

### Form B — the correct shape — is the true one, and is blocked twice

The statement a textbook makes keeps the subroutine's adversary interface in the
hybrid world's grade, so the simulator is JOINT:

```agda
-- Typed residual, not built and not postulated.
F_coinᶠ     : Homᶠ Resᶠ Lkᶜᶠ Honᶜᶠ                        -- gradedᵒ of a Proc Resᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ)
coin-hybrid : Σ[ s ∈ Certified Lkᶜᶠ (λ n → Lkᶠ n ⊗₀ Advᶜᶠ n) ]
                ((n : ℕ) → (tossᶠ ∙ᶠ idealᶠ) n ≈ sub (sim s n) ∘ F_coinᶠ n)
            → (tossᶠ ∙ᶠ idealᶠ) ≤UC^ωᵉ F_coinᶠ
coin-toss-ideal : realᶠ ≤UC^ωᵉ idealᶠ → (tossᶠ ∙ᶠ realᶠ) ≤UC^ωᵉ F_coinᶠ
coin-toss-ideal w = ≤UC^ωᵉ-trans (coin-toss-from-com w) (coin-hybrid …)
```

The ASSEMBLY is already available — `≤UC^ωᵉ-trans` is one line and §3's theorem
is the first hop — so nothing about the composition layer is missing. What is
missing is `coin-hybrid`'s machine equality, and two separate things block it.

**(B1) `_∙ᶠ_` had no machine reading — DELIVERED.** `sub (procᵒ s) ∘ gradedᵒ g`
is `gradedᵒ (subᴵ′ s ∘ g)` by `UC.Model.Graded.sub-gradedᵒ`; there was no
counterpart for `ext X (gradedᵒ k) ∘ gradedᵒ f`, which is what `_∙ᶠ_` is. Two
exports now supply it, in `sub-gradedᵒ`'s own shape and beside it:

```agda
graded₂ᵒ    : {A X P C : Iface} → Proc A ((X ⊗ᴵ P) ⊗ᴵ C)
            → ifaceᵒ A G.⇒ (ifaceᵒ X G.⊗₀ ifaceᵒ P) G.⊗₀ ifaceᵒ C
ext-gradedᵒ : {A B C P X : Iface} (k : Proc B (P ⊗ᴵ C)) (f : Proc A (X ⊗ᴵ B))
            → (G.associator.to G.∘ ((G.id {ifaceᵒ X} G.⊗₁ gradedᵒ k) G.∘ gradedᵒ f))
              G.≈ graded₂ᵒ (a⇒ᴵ M.∘ (T₁ᴵ X k M.∘ f))
```

(`UC/Model/Graded.agda:60`, `:69`), and `UC.Graded.ext-graded` (`:71`) is the
reading in the grading's own vocabulary, joined to `ext` outside the seal by
`GradedKleisli.μT` (`ext u k ≈ μ u v ∘ T₁ u k`) and
`CurriedTensor.Properties.μ-α⇐` / `T₁-⊗`, over the machine readings
`UC.Machine.Dictionary.a⇒-α⇐` and `T₁-⊗₁`. So a statement about a COMPOSED
system CAN now be read back as a machine equality; nothing consumes it yet,
because (B2) is what actually stops this example.

**(B2) `F_com`'s ideal functionality keeps its memory in the CONTEXT.** That is
`docs/fcom-extraction.md`'s cell-in-the-resource decision, and it is what makes
`ideal` a `wireᴹ` and the extraction example affordable at all. But
`_≈ctx[_]_`'s closure `m : 𝟘ᵒ ⇒ T₀ W (ifaceᵒ Resᴵ)` is universally quantified,
so **nothing says the cell returns the bit it was given**. The coin toss's
output reads that bit; an ideal coin's output must not. Counterexample: let `m`
answer every `getᴿ` with `outᴿ true` whatever was stored.

* Hybrid (`tossᶠ ∙ᶠ idealᶠ`): the adversary commits `b₁` through the grade,
  `putᴿ b₁` goes down and is ignored, the stage publishes `shareᴬ b₂`, the
  opening yields `openedᴴ true`, output `true xor b₂`. The environment reads
  `share xor output = true`, always.
* Ideal (`sub s ∘ F_coinᶠ`): output is `F_coin`'s own `c`, so
  `share xor output = share xor c`. For this to be `true` always, `c` must be
  determined by the share the simulator published — which is what "ideal coin"
  forbids.

Restricting `m` to a faithful cell means plugging `Examples.ROCommitment.Resource`
below, i.e. a CLOSED domain. Then the real side is
`stage ∘ wire ∘ resource` and the ideal side `subᴵ sim ∘ F_coin ∘ resource`, and
both are ⊕-traces of two STATEFUL machines after the wire is absorbed — exactly
the obstruction `docs/hash-forward.md` §"The one structural fact that makes it
affordable" prices: `UC.Machine.Wire.∘-wireᴹ` needs one factor to be a wire and
a lazily sampled oracle is not, and `Protocol.Machine.Compose.morphism-∘` needs
both to be `morphism` images and neither is.

**The finding, in one sentence.** The wire placement of an ideal functionality,
which is what makes a one-level emulation affordable, is exactly what makes a
two-level one unstateable at an open domain: the second level has to trust the
first level's memory, and at an open domain that memory belongs to the context.
Both repairs — a stateful `F_com` ideal functionality, or a closed domain with
the concrete resource — bottom out in the SAME missing machine-layer lemma, a
readable form for the ⊕-trace of two stateful machines where neither is a
`morphism` image.

### What this does not touch

`Abstract2.UC-compose`, `UC.Asymptotic.Compose` and the `_≈ctx[_]_` relation are
untouched and unweakened; §5 is a statement about what can be PUT IN them at
this example's placement, not about them. No `Simulator`, `Monitor` or
`MonitoredExperiment` record and no new category appears anywhere on the branch
(`docs/uc-presheaf-preservation-plan.md` §1 decisions 1-6); the only new `data`
declarations are the two protocols' message types and their states, and the two
new records inhabited are `UC.QueryBound`'s existing `QBᵢ`.

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
| `Examples.CoinToss.Test` | 125 | 10.7 s | 91 s |
| `UC.Model.Graded` | 73 → 92 | 10.1 s → 11.5 s | 83 s |
| `UC.Graded` | 72 → 88 | 9.7 s → 9.8 s | 82 s |

The two `Graded` rows are the only edits to existing modules, and both are
additive; their before/after is measured on the same forced-warm basis
(`.agdai` deleted, one `Checking` line each).

Closure: `src/CategoricalCrypto.agda` rc=0 in 144 s over 113 modules with an
empty gate, `Examples/ChimericLedger/FactorEps.agda` — the other `UC-composeᵉ`
consumer, outside that closure — and `UC/Approximate/LocalTests.agda` likewise.

## 7. Root-file wiring

Done on the branch, not left to the maintainer:

* `src/CategoricalCrypto.agda` gains `Examples.CoinToss.Compose` and
  `Examples.CoinToss.Test` (which between them reach the other four) and an
  inventory paragraph beside `Examples.ROCommitment.*`'s.
* `src/CategoricalCrypto/UC.agda`'s `UC.Asymptotic.Compose` row now names its
  two consumers. No `UC.*` module is new; `UC.Model.Graded` and `UC.Graded`
  gain the §5 (B1) exports and are already re-exported by `UC.agda`.

## 8. Not delivered, precisely

1. **The second hop**, §5 — Form A refuted; Form B's bookkeeping half
   (`ext-gradedᵒ`/`ext-graded`) delivered, its substantive half — a
   trustworthy `F_com` memory — not.
2. **No `≤UC` / `≤UC[ c ]` form of the composed statement.**
   `UC.Graded.≤UCᵍ` and `UC.Seam.Graded.≤UC[]ᵍ` consume a `Factors` — an exact
   machine equality — and the composed statement is approximate, exactly as
   `docs/fcom-extraction.md` §"Not delivered" 3 records for the commitment
   itself. Nothing here weakens them; they do not apply.
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
5. **`qb-oneCall`'s relocation** to `UC.QueryBound` is still owed
   (`docs/ledger-lift-eps.md` §9 item 3); had it been there and applicable,
   neither `recvCert` nor `comCert` would have had to be written out — but it
   is stated over `Protocol A B` and these are raw machines, so it would not
   have applied anyway.
