# Lifting the hash premise through the ledger without forgetting its error

Plan step 6, the part independent of step 5 (`docs/uc-presheaf-preservation-plan.md`
§4.5, §6.6), on branch `ledger-lift-eps` off `protocol-rewrite` at `f4b1e007`. Paths
are relative to `src/CategoricalCrypto/` unless prefixed.

What was missing: `Examples.ChimericLedger.Factor.ledger-pov-from-hash` takes the
POINTWISE QUALITATIVE premise `hash ≤UC^ω oracle^ω` and lifts it with `UC.Factor.liftᵖ`
(`UC-compose` + `≤UC-sub`), so the error is forgotten *before* the factoring is crossed.
`EndToEnd.ledger-uc-to-pov-family` keeps an error but its premise sits at the LEDGER.
Nothing joined the two. `UC.Asymptotic.Compose` now provides the composition that does.

## 1. The premise shape at the hash, and why

Two shapes are available at the hash port and both are delivered.

| theorem | premise | file:line |
|---|---|---|
| `hash-liftᵉ` | `imgᶠ HashIf^ω hash ≤UC^ωᵉ imgᶠ HashIf^ω oracle^ω` — the canonical witness: simulator family, negligible schedule, contextual agreement at it | `Examples/ChimericLedger/FactorEps.agda:107` |
| `hash-liftⁿ` | `hash ≤UC^ωⁿ oracle^ω` — the direct-agreement specialization | `:124` |

**The honest shape at this port is `_≤UC^ωⁿ_`**, and it is honest by the ledger's
nature rather than by fiat. `POV.oracle` exposes no adversary interface and the ledger's
`morphism` image carries none either, so both sides of the hash boundary are graded at
`𝟘ᴳ` and every simulator there is a `𝟘ᴳ ⇒ 𝟘ᴳ` scalar — `docs/ledger-factoring.md`'s
closing section records the maintainer's reason, and `UC.Seam.Grounded.subBlind` is the
theorem that such a scalar is invisible. `_≤UC^ωⁿ_` is what a witness at a trivial
simulator degenerates to, and `UC.Asymptotic.Family.≤UC^ωⁿ⇒≤UC^ωᵉ` is the inclusion, so
`hash-liftᵉ` covers the `ωⁿ` premise too.

The general witness form is delivered anyway, because it is what plan §4.5 asks for and
because nothing about the *lift* needs the grade to be trivial: `hash-liftᵉ` is stated at
an arbitrary certified simulator family and discharges every certificate the composition
theorem demands. What the trivial grade buys is the *end* of the chain — see §5.

## 2. The ε-retaining lift

### `hash-liftᵉ` — through `UC-composeᵉ`

```agda
hash-liftᵉ : (hash : Systems HashIf^ω)
           → imgᶠ HashIf^ω hash ≤UC^ωᵉ imgᶠ HashIf^ω oracle^ω
           → imgᶠ LedgerIf^ω (Realᴴ hash vr s)
             ≤UC^ωᵉ imgᶠ LedgerIf^ω (Realᴴ oracle^ω vr s)
```

inside `module _ (vr : Variant) (s : (n : ℕ) → Ledger.LState n)`. Three steps:

1. `UC-composeᵉ` at `u = v = ledgerᶠ` (the upper stage is the SAME on both sides, so the
   second comparison is the identity witness `idᶜ` at the zero schedule):
   `(ledgerᶠ ∙ᶠ hashᶠ) ≤UC^ωᵉ (ledgerᶠ ∙ᶠ oracleᶠ)`, graded at `𝟘ᴳ ⊗₀ 𝟘ᴳ`.
2. `≤UC^ωᵉ-sub (λ⇒ᶜ _) (λ⇐ᶜ _) unitorˡ.isoˡ` regrades both sides by the unit the Kleisli
   composition introduced. This is the one new piece of metatheory (`Compose.agda:77`),
   and it is `Abstract2.Factor.≤UC-sub`'s argument quantitatively: post-composing `sub c`
   is no congruence for the order unless the simulator commutes with `c`, a retraction
   conjugates it (`c ∘ s ∘ r`), and the allowance moves by `≈ctx-sub`'s exact
   substitution.
3. `≤UC^ωᵉ-resp` (`Contextual.agda:275`) reads both sides back through
   `Factor.ledger-factor`.

### `hash-liftⁿ` — through `≈ctx-ext` and `≈ctx-sub` alone

With one upper stage there is nothing for `UC-composeᵉ`'s `≈ctx-pre` step to do (it
compares `u` with `v`, and here they are equal), so the direct route is shorter and
introduces NO simulator at all:

```text
≈ctxᴬ⇒≈ctx  →  ≈ctx-ext ledgerᶠ 1 ledgerᶠ-qb  →  ≈ctx-sub (λ⇒ᶜ _)  →  ≈ctx-resp (ledger-factor)  →  ≈ctx⇒≈ctxᴬ
```

This is the plan's permitted alternative ("`≈ctx-sub`/`≈ctx-ext` if the factoring's shape
wants the sequential law"), and at this application it is not merely shorter: having no
simulator is what lets the chain END (§5).

## 3. The exact ε, substitution by substitution

`simCost q cs = q * (cs ⊔ 1)` and `ctxBudget c c′ = c * (c′ ⊔ 1)` (`UC/Budget.agda`).

**`hash-liftⁿ`**, from a premise schedule `ε`:

| step | schedule after it | why |
|---|---|---|
| premise | `ε n q` | |
| `≈ctx-ext ledgerᶠ cv` with `cv n = 1` | `ε n (simCost q 1)` = `ε n (q * 1)` | the ledger goes into the TEST; `ctxBudget-simCost` makes this EXACT |
| `≈ctx-sub (λ⇒ᶜ _)` with `cost (λ⇒ᶜ _) n = 1` | `ε n (simCost (simCost q 1) 1)` = `ε n ((q * 1) * 1)` | the regrading goes into the test too; `ctxBudget-absorb`, also exact |

so `εᴴ n q = ε n ((q * 1) * 1)` — the premise's own schedule read at the allowance the
ledger and the unit regrading each cost one activation of. Negligible by
`NegligibleBound-simCost` twice (each spends only `poly-* (poly-⊔ (poly-const 1)
(poly-const 1))`), proved AFTER both substitutions, never before.

**`hash-liftᵉ`**, from a witness `(sf , εf , nf , ef)` and the ledger's zero schedule
`εu = λ _ _ → 0ℚ`. `UC-composeᵉ` produces `λ n q → εu′ n q + εf′ n q` with

```text
εu′ n q = εu n (simCost q (cf n))            cf n = 0   (the hash into the CLOSURE — a BOUND)
εf′ n q = εf n (simCost q (ctv n))           ctv n = (cost idᶜ n ⊔ 1) * cv n = (1 ⊔ 1) * 1
```

and `≤UC^ωᵉ-sub` then reindexes the whole thing by `simCost _ (cost (λ⇒ᶜ _) n) = simCost _ 1`:

```text
ε n q  =  0ℚ  +  εf n (simCost (simCost q 1) ((1 ⊔ 1) * 1))
       =  0ℚ  +  εf n ((q * 1) * 1)
```

Negligible by `GradedBound-+[ Negligible ] Negligible-+` over two
`NegligibleBound-simCost`s — again after the substitutions. The `εu′` summand is
identically `0ℚ`, which is the arithmetic shadow of the two sides sharing their upper
stage.

## 4. Certificates: what was proved, what was assumed

**Nothing was assumed.** Both hypotheses `UC-composeᵉ` states about the processes it
moves are theorems here, and so is the monotonicity premise.

| obligation | discharge | file:line |
|---|---|---|
| `QB (cf n) (f n)` for the real hash, `cf n = 0` | `UC.QueryBound.qb-closed` — a CLOSED process has `Neg unitᴵ` empty, so no output of its is downward and the rate is zero, whatever the hash is. Composed with `qb-λ⇐` for the `ιᴳ` in `closedᵒ` | `FactorEps.agda:81` |
| `QB (cv n) (v n)` for the ledger, `cv n = 1` | **proved**, `qb-ledger` | `Examples/ChimericLedger/QueryBound.agda:190` |
| `Poly cf`, `Poly cv` | `poly-const 0`, `poly-const 1` | `FactorEps.agda:116-117` |
| `NegligibleBound εu` | `λ _ _ → Negligible-0`: `εu` is the ZERO schedule, because the upper stage is shared and `≈C⇒≈ctx` compares it with itself at zero error | `FactorEps.agda:114` |

So the plan's "polynomial-cost premises explicitly" is met by *proving* them rather than
by carrying them: the only premise the two lifts carry is the emulation itself.

### The ledger's query bound

`qb-ledger : (vr : Variant) (s₀ : LState) → QB 1 (morphism (ledger vr s₀))` is the
instance of a general fact, `qb-oneCall` (`QueryBound.agda:169`): a protocol whose every
step factors through `OracleCall.fromCall` makes at most one downward call per activation
and the answer to that call only returns, so it is 1-bounded. The ledger's does, by
`refl` at each query constructor — `submit` hashes once, `audit` answers purely
(`ledgerCall`, `:185`).

The certificate cannot be carried by `Protocol.Machine.MSt`: its `wait` holds the parked
continuation as a FUNCTION over arbitrary `Calls` trees, and `QBᵢ` must answer at every
state, reachable or not — exactly the obstruction `Examples.MerkleDamgard.QueryBound`'s
header records. `UC.QueryBound.QB`'s `≈ᴹ`-closure is what it is for: `oneCallᴹ` is the
same relay with its suspension named by the continuation `fromCall` parks, its potential
is constantly zero, and `θ-sim` is the simulation onto `morphism P`, definitional at
every node. That is the second instance of this pattern in the repo and it follows the
first line for line.

`qb-oneCall` is stated over an arbitrary `Protocol A B` and BELONGS in `UC.QueryBound`
beside `qbᵢ-wire`/`qbᵢ-closed`; it sits in the example module only because that module is
outside this branch's edit scope. Flagged in `QUALITY-REVIEW.md`.

## 5. The end-to-end theorem from the hash

```agda
ledger-pov-from-hashⁿ : SerInj → hash ≤UC^ωⁿ oracle^ω → (p : ℕ → ℕ) → Poly p
                      → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
                        × ((n : ℕ) (d : Strat …) → asks≤ (p n) d
                           → PrHit (Realᵉ n) (badᵉ n) d ℚ.≤ f n)
```

(`FactorEps.agda:159`), routed through `EndToEnd.ledger-pov-family-negligible` — whose
premise is `_≤UC^ωⁿ_` AT THE LEDGER, which `hash-liftⁿ` supplies. Two things to read off
it:

* **Neither `TotalRun` nor `NoDeadStep` appears.** The pointwise theorem spends totality
  to collapse a per-level emulation into an agreement; the family premise is already
  quantitative and there is nothing to collapse. The conclusion is
  `ledger-pov-family-negligible`'s, i.e. `Real.ledger-pov`'s bound verbatim.
* **The forgetting happens at the END and nowhere earlier.** `ledger-pov-family-negligible`
  folds the ε into the saturated slack (`≤UC^ωⁿ⇒≈negl`, `≈negl-respects`), which is the
  last step; the error crosses the factoring intact before that. The old route forgot at
  the start.

### Why the ᵉ route does not also reach a probability here

`ledger-pov-family-negligible` wants `_≤UC^ωⁿ_`, and turning a general `_≤UC^ωᵉ_` witness
into one is `UC.Asymptotic.Family.≤UC^ωᵉ⇒≤UC^ωⁿ`, whose premise is that the witness's
simulator acts trivially on the ideal side:

```agda
(n : ℕ) → subᶠ s (imgᶠ B I) n ≈ imgᶠ B I n          -- in 𝒞's OWN equality
```

That is available for the trivial simulator and only for it. For a general `𝟘ᴳ ⇒ 𝟘ᴳ`
scalar the corresponding fact is `UC.Seam.Grounded.subBlind`, which gives
`sub s ∘ closedᵒ v ≈ᵁ closedᵒ v` (not `≈`) and only from `SimTotal`, which
`emSimTotal` extracts from `TotalRun` on the real side plus an `≈ᵁ` agreement — closeness
at EVERY positive error. A `≈ctx[ ε ]` witness supplies closeness at one fixed `ε` per
context and cannot produce it. **Typed residual** (not built, not postulated):

```agda
≤UC^ωᵉ⇒≤UC^ωⁿ-blind :
    (s : Certified (Δ 𝟘ᴳ) (Δ 𝟘ᴳ)) (ε : ℕ → ℕ → ℚ) → NegligibleBound ε
  → (ν : ℕ → ℚ) → ((n : ℕ) → 0ℚ ℚ.< ν n) → Negligible ν
  → ((n : ℕ) → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim s n)))        -- the missing input
  → imgᶠ B R ≈ctx[ ε ] subᶠ s (imgᶠ B I)
  → R ≤UC^ωⁿ I                                            -- at ε + ν
```

The body is `≈ctx-trans ε ν _ (≈ᵁ⇒≈ctx ν pos (λ n → subBlind _ (sim s n) (I n) …))` and
costs a positive slack, exactly as `uc-≤UC^ωⁿ` does; what is missing is the
`ASTotal` input, for which the repo has only `simAstotal` — off an `≈ᵁ` agreement. Since
the ledger's simulators ARE trivial, nothing at this application needs it, and it is
recorded rather than attempted.

## 6. The migration test

```agda
ledger-pov-from-hash′ : SerInj → hash ≤UC^ω oracle^ω → (p : ℕ → ℕ) → Poly p → …
ledger-pov-from-hash′ si hp = ledger-pov-from-hashⁿ a V hash si (uc-≤UC^ωⁿ tHash hp)
```

(`FactorEps.agda:177`) — `Factor.ledger-pov-from-hash`'s statement, proved the
ε-retaining way. The pointwise premise enters the family one by
`UC.Asymptotic.Family.uc-≤UC^ωⁿ`, whose totality input at the HASH is
`Protocol.Machine.Total.totalRun-morphism` off the `NoDeadStep (hash n)` the module
already carries; so the premise list is identical and nothing is added.

The identity of the two statements is MECHANICAL, not a copied signature:
`migration-pin` (`:195`) applies `at : {A : Set ℓ} → A → A → A` to
`Factor.ledger-pov-from-hash a V hash nd` and to `ledger-pov-from-hash′`, which forces
the two types to unify. A deliberate perturbation of the copied signature was checked to
break it.

`Factor.ledger-pov-from-hash` itself, the five ledger theorems in `EndToEnd`, and
`Real.ledger-pov` are byte-identical; the new theorems sit beside them in a new module.

## 7. Module costs (warm, one `Checking` line, `+RTS -M8G -H1G`)

| module | LOC | warm before | warm after | rule-5 budget |
|---|---|---|---|---|
| `UC.Asymptotic.Contextual` | 298 → 313 | — | 10.7 s | 138 s |
| `UC.Asymptotic.Compose` | 246 → 277 | 10.9 s | 11.5 s | 129 s |
| `UC.Asymptotic.Family` | 342 (untouched) | — | 23.7 s | 145 s |
| `Examples.ChimericLedger.Factor` | 116 | 12.1 s | 12.7 s | 89 s |
| `Examples.ChimericLedger.EndToEnd` | 283 | 11.8 s | 10.7 s | 130 s |
| `Examples.ChimericLedger.QueryBound` | 195 | — (new) | 10.6 s | 108 s |
| `Examples.ChimericLedger.FactorEps` | 195 | — (new) | 12.2 s | 108 s |

No "before" is claimed where none was measured on this machine: `Contextual` and
`Family` were only ever measured here after the edit, and `docs/quantitative-family.md`
§8's 9.4 s / 21.0 s are at a different heap pairing (`-M20G -H2G`).

`Factor`/`EndToEnd` are untouched and move by ±5 %, far inside the >20 % bar that would
have forced the new theorems elsewhere; they are in a new module anyway.

Closure, all green with an empty warning gate: every `Examples/ChimericLedger/*` root,
`UC/Approximate/LocalTests.agda`, `UC/Factor.agda`, `src/CategoricalCrypto/UC.agda`, and
`src/CategoricalCrypto.agda` (130 s, 84 modules).

Escape-hatch baseline
(`grep -rnE 'postulate|TERMINATING|primTrustMe|\{!' src/`): **16 before, 16 after**, all
16 being the words "postulate-free" in inherited comments.

## 8. Root-file wiring the maintainer still needs to do

`Examples.ChimericLedger.QueryBound` and `Examples.ChimericLedger.FactorEps` have no
in-repo importer, so neither is in `src/CategoricalCrypto.agda`'s closure. Both check
green standalone. To add:

- `src/CategoricalCrypto.agda`: imports of both (and of `UC.Asymptotic.Compose`, which
  `docs/quantitative-family.md` §9 already owes and which `FactorEps` is the first
  consumer of).
- `src/CategoricalCrypto/UC.agda`'s inventory: nothing new is needed under `UC.*` beyond
  the `UC.Asymptotic.Compose` row that document already asks for.

## 9. Not delivered

1. **`≤UC^ωᵉ⇒≤UC^ωⁿ-blind`**, §5's typed residual: forgetting a NON-trivial trivial-grade
   simulator after the composition. Blocked on an `ASTotal` for the simulator's
   initialization that the quantitative relation cannot produce.
2. **A nontrivially graded hash port.** Unchanged from `docs/ledger-factoring.md`'s "What
   review §3 would add": the port here is an OBJECT boundary and both stages are pure, so
   the simulator that `UC-composeᵉ` composes is still a scalar. `hash-liftᵉ` is stated at
   an arbitrary certified simulator and would carry a real one unchanged, but the ledger
   cannot supply one.
3. **`qb-oneCall`'s relocation** to `UC.QueryBound` (§4).
4. **`ledger-uc-to-pov`'s rerouting** through the family theorem — the parked maintainer
   call. Nothing here changes its calculus: `ledger-uc-to-pov` is untouched, so
   `UC.Asymptotic.uc-agree` keeps the importer the parked note is about, and
   `ledger-pov-from-hash′` reaches the family theorem without going through
   `ledger-uc-to-pov` at all.
