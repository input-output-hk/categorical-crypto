# `Rcom → Icom`: the theorem boundary (B1) and the residual obligations (B2)

Scope: steps B1 and B2 of [`docs/model-contract-and-end-to-end-plan.md`](model-contract-and-end-to-end-plan.md)
§"Workstream B", at `protocol-rewrite` `478d87f3`. This is the SPECIFICATION of
the theorem the two coin-toss headline theorems still assume; no part of it is
proved here. Every name below is a source name with its `file:line`; the
boundary itself is a checked object in
`src/CategoricalCrypto/Examples/ROCommitment/Realization/Statement.agda`.

Lines are `src/CategoricalCrypto/…` unless the path says otherwise.

## 0. The hypothesis to discharge

```agda
coin-toss-ideal  : realᶠ  ≤UC^ωᵉ idealᶠ                        -- Examples/CoinToss/Ideal/Compose.agda:76
                 → (λ n → (tossᶠ  ∙ᶠ realᶠ)  n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-toss-idealʳ : realʰᶠ ≤UC^ωᵉ idealʰᶠ                       -- Examples/CoinToss/Ideal/Receiver/Compose.agda:128
                 → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
```

Both premises are at the OPEN resource domain `Resᶠ` (`Examples/CoinToss/Compose.agda:54`),
so their closure quantifier ranges over every query-bounded
`m : 𝟙 ⇒ T₀ W (ifaceᵒ (Resᴵ n))`. The bound behind them
(`Examples/ROCommitment/Game.agda:576 extraction-bound`) is proved against ONE
resource. Per the plan's B1, the theorem to prove is the resource-INSTALLED
one, and a new assembly theorem consumes it; the two existing theorems keep
their statements and their schedule pins.

## 1. The theorem signature

### 1.1 The two compared families

`Statement.agda` pins them (no proof, no holes):

```agda
Rcom : Homᶠ (λ _ → 𝟘ᵒ) Advᶠ Honᶠ          Rcom  n = realᶠ  n ∘ resᶠ n
Icom : Homᶠ (λ _ → 𝟘ᵒ) Lkᶠ  Honᶠ          Icom  n = idealᶠ n ∘ resᶠ n
Rcomʰ : Homᶠ (λ _ → 𝟘ᵒ) Advʰᶠ Honʰᶠ       Rcomʰ n = realʰᶠ n ∘ resᶠ n
Icomʰ : Homᶠ (λ _ → 𝟘ᵒ) Lkʰᶠ  Honʰᶠ       Icomʰ n = idealʰᶠ n ∘ resᶠ n

Realization  = Rcom  ≤UC^ωᵉ Icom
Realizationʰ = Rcomʰ ≤UC^ωᵉ Icomʰ
```

Components, each already in source:

| symbol | definition | where |
|---|---|---|
| `_≤UC^ωᵉ_` | `Σ[ s ∈ Certified Y X ] Σ[ ε ] NegligibleBound ε × f ≈ctx[ ε ] subᶠ s g` | `UC/Quantitative/Family.agda:249`, at the sealed machine via `UC/Asymptotic/Contextual.agda:21` |
| `Homᶠ A X B` | `(n : ℕ) → A n ⇒ T₀ (X n) (B n)` | `UC/Quantitative/Family.agda:74` |
| `realᶠ`/`idealᶠ` | `ROU.realᵒ` / `ROU.idealᵒ` | `Examples/CoinToss/Compose.agda:61,64`; `Examples/ROCommitment/UC.agda:47,50` |
| `realʰᶠ`/`idealʰᶠ` | `ROHU.realʰᵒ` / `ROHU.idealʰᵒ` | `Examples/CoinToss/Compose.agda:120,123`; `Examples/ROCommitment/Hiding/UC.agda:46,49` |
| `resᶠ n` | `procᵒ (RR.resource n)`, `𝟘ᵒ ⇒ Resᶠ n` | `Examples/CoinToss/Ideal/Compose.agda:58`; `Examples/ROCommitment/Resource.agda:69` |
| grades `Advᶠ`/`Lkᶠ`, `Advʰᶠ`/`Lkʰᶠ` | `ifaceᵒ (RO.Advᴵ n)` etc. | `Examples/CoinToss/Compose.agda:54-59,113-118` |
| honest ports `Honᶠ`/`Honʰᶠ` | `ifaceᵒ (RO.Honᴵ n)` / `ifaceᵒ (ROH.Honᴵʰ n)` | same |

The instance is the asymptotic-family one — `_≤UC^ωᵉ_` at `𝔾ᵒ`, `observationᵒ`,
`budgetᵒ`, `Approximationᴹ` (`UC/Asymptotic/Contextual.agda:21-23`) — the same
instance the two headline theorems are stated in. Nothing here is a new
relation.

### 1.2 Closing the domain does not touch the grade

`_≤UC^ωᵉ_ {A} {X} {B} f g` reads the DOMAIN `A` and the GRADE `X` at different
places: the simulator is `Certified Y X` (`UC/Quantitative/Family.agda:182`),
indexed only by the two grades, and the domain appears only as the source of
`f n`. Replacing `A = Resᶠ` by `A = λ _ → 𝟘ᵒ` therefore leaves the simulator's
type, the adversary port and the leak port exactly as they are. Concretely: in
`_≈ctx[ ε ]_` (`UC/Quantitative/Family.agda:90`) the closure is
`m : 𝟙 ⇒ T₀ W (A n)`, and at `A n = 𝟘ᵒ` it carries the ancilla only — the
resource's memory has left the context's hands, which is the whole content of
`docs/coin-toss.md` §5 "Why the comparison boundary has to be CLOSED", while
the test `E : T₀ (W ⊗₀ X n) (B n) ⇒ Ω` still sees the full grade `X n`.

### 1.3 Parenthesization, and the assembly theorem that reconciles it

The existing chain is parenthesized as `(stage ∙ᶠ commitment) ∘ resource`
(`Examples/CoinToss/Ideal/UC.agda:150 coin-hop`, and the conclusions above);
the resource-installed premise is parenthesized as `stage ∙ᶠ (commitment ∘
resource)`. `_∙ᶠ_` is `ext (X n) (k n) ∘ f n` (`UC/Quantitative/Family.agda:357`),
so the two differ by one `∘`-associativity and by nothing else:

```text
(tossᶠ ∙ᶠ Rcom) n  =  ext _ (tossᶠ n) ∘ (realᶠ n ∘ resᶠ n)
(tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n  =  (ext _ (tossᶠ n) ∘ realᶠ n) ∘ resᶠ n
```

The composition laws that reconcile them, all existing:

1. `UC-composeᵉ` (`UC/Quantitative/Family.agda:475`, re-exported by
   `UC/Asymptotic/Compose.agda:13`) with the upper stage compared with itself
   at `idᶜ` and the zero schedule — the shape `coin-toss-from-com`
   (`Examples/CoinToss/Compose.agda:79`) already uses, with `realᶠ` replaced by
   `Rcom` and its certificate by `qb-∘ (CTU.recvQB n) (CTIU.resourceQBᵒ n) :
   QB 0 (Rcom n)`.
2. `≤UC^ωᵉ-resp` (`UC/Quantitative/Family.agda:253`) for the associativity, on
   both sides. It rebuilds the witness with the SAME simulator and the SAME
   schedule, so no allowance moves.
3. `≤UC^ωᵉ-trans` (`UC/Quantitative/Family.agda:304`) against the existing
   second hop — `coin-hybridᵉ` (`Examples/CoinToss/Ideal/Compose.agda:73`) or
   `coin-hybridʳ` (`Examples/CoinToss/Ideal/Receiver/Compose.agda:119`).

`≤UC^ωᵉ-dom` (`UC/Quantitative/Family.agda:462`) is NOT used in the new
assembly: it is what the current proof spends to close the boundary AFTER
composing, and the new premise is closed already. It stays in use for the
second hop's own domain in the existing theorems.

`Statement.agda` pins the two assembly obligations as `Set`s:

```agda
Assembly  = Realization  → (λ n → (tossᶠ  ∙ᶠ realᶠ)  n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
Assemblyʰ = Realizationʰ → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
```

Both were CHECKED GREEN as proofs against `478d87f3` and then withdrawn from
the branch (B1 is scoping): the proof is fifteen lines per corruption case
and is recorded verbatim in §6, with the schedule pins it discharges.

## 2. The simulator

`_≤UC^ωᵉ_`'s first component is `Certified Lkᶠ Advᶠ`
(`UC/Quantitative/Family.agda:182`): a family
`(n : ℕ) → ifaceᵒ (Lkᴵ n) ⇒ ifaceᵒ (Advᴵ n)` together with `q : ℕ → ℕ`,
`Poly q` and `QB (q n)` at every level.

**Corrupted committer — it exists.** `comSim` (`Examples/CoinToss/Compose.agda:150`):

```agda
comSim : Certified Lkᶠ Advᶠ
comSim = ROU.simᵒ , (λ _ → 2) , poly-const 2 , λ n → qbᵒ (ROU.simQB n)
```

with `ROU.simᵒ = procᵒ simulator` (`Examples/ROCommitment/UC.agda:53`) and
`simQB : QB 2 simulator` (`:119`) from the exact ledger `simCert` (`:66`).

**Corrupted receiver — not packaged.** `ROHU.simʰᵒ`
(`Examples/ROCommitment/Hiding/UC.agda:52`) and `simQBʰ : QB 1 simulatorʰ`
(`:134`) both exist; the `Certified Lkʰᶠ Advʰᶠ` bundling them does not
(grep: no `comSimʰ` in `src/`). Three lines, mirroring `comSim`.

**The adversarial ports the simulator must retain.** They are fixed by the two
grades and closing the domain does not narrow them:

| port | constructors | where |
|---|---|---|
| `Advᴵ = AdvA ⇿ AdvQ` | up `queryᴬ : Pt → AdvQ`, `commitᴬ : Dig → AdvQ`, `openᴬ : Bool → Dig → AdvQ`; down `ansᴬ : Dig → AdvA` | `Examples/ROCommitment.agda:86-95` |
| `Lkᴵ = LkA ⇿ LkQ` | up `hashˢ`, `commitˢ`, `openˢ`, `failˢ`; down `digˢ` | `:99-109` |
| `Advᴵʰ = AdvAʰ ⇿ AdvQʰ` | up `askᴿᶜ : Pt → AdvQʰ`; down `ansᴿᶜ`, `comᴿᶜ`, `opnᴿᶜ` | `Examples/ROCommitment/Hiding.agda:71-79` |
| `Lkᴵʰ = LkAʰ ⇿ LkQʰ` | up `relayᶠ : Pt → LkQʰ`; down `digᶠ`, `rcptᶠ`, `bitᶠ` | `:84-92` |

(`Iface`'s fields are `Pos Neg`, `Iface.agda:12-14`, so `Neg (A ⇿ B) = B` is
the "up" direction a context drives.)

Two things the simulator's retention actually requires, both readable off the
ideal functionality's wire:

* **Oracle access survives the closure.** `ideal = wireᴹ upᶠ downᶠ`
  (`Examples/ROCommitment.agda:130`) sends `hashˢ x ↦ hashᴿ x`
  (`:119`), so after `_∘ resᶠ n` the simulator still reaches the SAME oracle
  table the real receiver relays to (`realStep`'s `queryᴬ` clause,
  `:158-160`). One resource under both sides is what makes that the same
  oracle and not two copies — the plan's A1 "install a shared oracle once".
* **The extraction port survives.** `commitˢ b ↦ putᴿ b`, `openˢ ↦ getᴿ`,
  `failˢ ↦ nakᴿ` (`:120-122`); the cell is the functionality's memory
  (`Examples/ROCommitment/Resource.agda:50-64`). Closing the domain FIXES
  what the cell does (`cell-put`/`cell-get`/`cell-nak`, `:89-98`) without
  removing the simulator's ability to drive it.

## 3. The permitted context class

`Rcom ≈ctx[ ε ] subᶠ comSim Icom` unfolds to (`UC/Quantitative/Family.agda:90-97`):

```agda
(n : ℕ) (W : Channel) (E : T₀ (W ⊗₀ Advᶠ n) (Honᶠ n) ⇒ Ω) (m : 𝟙 ⇒ T₀ W 𝟘ᵒ)
{c c′ : ℕ} → QB c E → QB c′ m
→ ⟦ (E ∘ prefixᵒ W (Rcom n)) ∘ m ⟧ ≈[ ε n (ctxBudget c c′) ] ⟦ … ⟧
```

* Ancilla `W : Channel` arbitrary, per level.
* Test `E` an arbitrary model morphism with `QB c E`.
* Closure `m` an arbitrary morphism into the ancilla with `QB c′ m`; at the
  closed domain it no longer supplies a resource.
* The error is read at `ctxBudget c c′ = c ℕ.* (c′ ℕ.⊔ 1)` (`UC/Budget.agda:74-75`).
* Neither hom's own query bound is read (`UC/Quantitative/Family.agda:21-23`).

Certificates the theorem needs, and their status:

| certificate | needed for | status |
|---|---|---|
| `QB 2 simulator` → `Certified Lkᶠ Advᶠ` | the witness's first component | EXISTS, `Examples/ROCommitment/UC.agda:119`, packaged at `Examples/CoinToss/Compose.agda:150` |
| `QB 1 simulatorʰ` → `Certified Lkʰᶠ Advʰᶠ` | ditto, receiver | half exists (`Hiding/UC.agda:134`), not packaged |
| `QB 0 (procᵒ resource)` | plugging the resource at rate 0 | EXISTS, `Examples/CoinToss/Ideal/UC.agda:141` from `Resource.agda:102` |
| `QB 1 (gradedᵒ real)`, `QB 0 tossᵒ` | the assembly's moved morphisms | EXIST, `Examples/CoinToss/UC.agda:157,91` |
| `QB 1 (gradedᵒ realʰ)`, `QB 1 tossʰᵒ` | ditto, receiver | EXIST, `Examples/CoinToss/Hiding/UC.agda:179,107` |
| `PolyQB Rcom` / `PolyQB Icom` | ONLY the `Canonicalᴺ._≤UC_` consequence | not written; each is `(λ _ → 0) , poly-const 0 , λ n → qb-∘ … (resourceQBᵒ n)`, the shape of `coinRealQB` (`Examples/CoinToss/Ideal/Compose.agda:114`) |
| `PolyQB` of the composite and of `Fcoinᶠ` | the existing `coin-toss-idealᴺ` | EXIST, `Examples/CoinToss/Ideal/Compose.agda:111,114` |

No `PolyQB` (`UC/Family.agda:100`) is needed for `Realization` itself:
`_≤UC^ωᵉ_` does not carry one.

## 4. The assumption ledger

Read off the interfaces and the machines, not off the plan.

### 4.1 Resource assumptions

| # | assumption | source | intended status |
|---|---|---|---|
| R1 | The oracle is the lazily-sampled table of `resource`: a repeat point is answered from the table, a fresh one draws `uniformₚ k` and is kept | `Examples/ROCommitment/Resource.agda:53-70`, `hash-hit`/`hash-miss` `:78-85` | DISCHARGED as a definition; the theorem is about this resource and quantifies over no other |
| R2 | The commitment cell is one-shot and faithful: first `putᴿ` receipts and stores, `getᴿ` returns what was stored, `nakᴿ` refuses | `Resource.agda:58-64`, pinned by `cell-put`/`cell-get`/`cell-nak` `:89-98` | DISCHARGED at the concrete resource. This is exactly what the OPEN domain does not give — `docs/coin-toss.md` §5 exhibits a closure answering every `getᴿ` with `outᴿ true` |
| R3 | ONE resource, shared by both compared systems | the statement's shape: `_∘ resᶠ n` on both sides | structural |
| R4 | The resource is closed and asks nothing downward: `QB 0` | `Resource.agda:102 resourceQB = qb-closed resource`; `Examples/CoinToss/Ideal/UC.agda:141` | THEOREM |
| R5 | Off-protocol resource activations diverge (`botₚ`): a second `putᴿ`, a `getᴿ` before one | `Resource.agda:60,63` | part of the model; the proof must PRESERVE it, and it is residual B2-M3 below |

### 4.2 Encoding assumptions

| # | assumption | source | intended status |
|---|---|---|---|
| E1 | The digest length IS the security parameter, so the schedule is the identity and nothing reindexes `n` | `Examples/ROCommitment.agda:45` (`k : ℕ` is both), `Examples/ROCommitment/Asymptotic.agda:36-40` | structural to the family |
| E2 | `real` is the honest receiver: it relays the adversary's oracle queries, takes `commitᴬ c` on trust, and at `openᴬ b r` hashes `b ∷ᵛ r` itself and accepts iff the digest matches | `Examples/ROCommitment.agda:149-173` | definition |
| E3 | `simulator` extracts from the relay log via `extract` and releases only when digest and extracted bit both agree (`release`, `:189-191`) | `Examples/ROCommitment.agda:184-214`, `Examples/ROCommitment/Extraction.agda` | definition; its FAILURE probability is the game's `bad` (`Game.agda:187`) |
| E4 | `ideal` is a stateless relabelling `wireᴹ` of the resource's ports — the functionality's memory is the cell | `Examples/ROCommitment.agda:118-131`; rationale `docs/fcom-extraction.md` §"Where `F_com`'s memory lives" | definition |
| E5 | Off-protocol protocol activations diverge: a second `commitᴬ`, an `openᴬ` before a commitment, a resource answer `digᴿ` arriving with nothing in flight | `Examples/ROCommitment.agda:154-166`, simulator `:198-208` | model; must be preserved, not assumed away |

### 4.3 Feasibility assumptions

| # | assumption | source | intended status |
|---|---|---|---|
| F1 | Tests and closures are QUERY-bounded (`QB c E`, `QB c′ m`), and the error is read at `ctxBudget c c′` | `UC/Quantitative/Family.agda:90-97`, `UC/Budget.agda:74` | structural — there is NO uniform-polynomial local-runtime claim anywhere in the statement |
| F2 | The schedule is negligible at every POLYNOMIAL allowance (`NegligibleBound`) | `UC/Approximate.agda`; instance `εᶜ-negligible` `Examples/ROCommitment/Asymptotic.agda:39` | THEOREM for the candidate schedule of §5 |
| F3 | The simulator costs `2` downward messages per activation, `Poly`-bounded by `poly-const 2` | `Examples/ROCommitment/UC.agda:66-120`, `Examples/CoinToss/Compose.agda:151` | THEOREM |
| F4 | The game bound holds only at `asks≤ m d` for a FINITE strategy `d : Strat Q R` | `Examples/ROCommitment/Game.agda:576` | THEOREM at the game; crossing to contexts is `dominatedᵍ`, §7 B2-M5 |

### 4.4 Corruption and session scope, as the interfaces give it

* **STATIC corruption, fixed at the type level.** There is no corrupt message
  on any interface and no corruption event in any step function. Which party
  is corrupt is which MODULE is composed: `Examples.ROCommitment` puts the
  committer's three messages on `Advᴵ` and leaves `Honᴵ = HonA ⇿ ⊥`
  (`Examples/ROCommitment.agda:82`) report-only;
  `Examples.ROCommitment.Hiding` puts the receiver on `Advᴵʰ` and gives the
  honest committer a driving port `Honᴵʰ = HonAʰ ⇿ HonQʰ`
  (`Examples/ROCommitment/Hiding.agda:66`). Nothing in either supports
  adaptive corruption, and the statement must not be described as doing so.
* **ONE corrupted party per theorem.** The two cases are two theorems over two
  protocols, not two instances of one (`docs/fcom-hiding.md` §"The correction
  this document owes the brief"; `Examples/CoinToss/Compose.agda:107-112`).
* **SINGLE SESSION, SINGLE COMMITMENT.** The cell refuses a second `putᴿ`
  (`Resource.agda:58-60`), `real` refuses a second `commitᴬ`
  (`Examples/ROCommitment.agda:161-163`), and `simulator` likewise
  (`:202-205`). So each level `n` is one commitment instance; there is no
  multi-session or concurrent-instance content, and none may be claimed.
* **The environment cannot drive the extraction side through `Honᴵ`.**
  `Neg Honᴵ = ⊥`, so a `Strat (Neg Honᴵ) (Pos Honᴵ)` has no `ask`
  (`docs/dp-transport.md` A1, confirmed at `Examples/ROCommitment.agda:82`).
  The driver is the adversary port, which is the grade — which is why the
  contextual statement must keep the grade open and why `dominatedᵍ` rather
  than `dominatedᵒ` is the density lemma for it (§7 B2-M5).

## 5. The candidate error schedule

CANDIDATE, to verify at proof time; not a pin.

The game bound, merged into one numerator
(`Examples/ROCommitment/Asymptotic.agda:36-37`, from `Game.agda:566`):

```agda
εᶜ : ℕ → ℕ → ℚ
εᶜ n q = fromℕ (q * q + q + q) *ℚ inv-pow-2 n          -- (q² + 2q)·2⁻ⁿ
```

**Zero allowance.** `εᶜ n 0 = fromℕ 0 *ℚ inv-pow-2 n = 0ℚ`, so `εᶜ` is NOT
strictly positive uniformly in `q` and cannot serve as the domination's `δ`.
`ctxBudget c c′ = c ℕ.* (c′ ℕ.⊔ 1)` is `0` at `c = 0`, and `_≈ctx[_]_`
quantifies `{c c′ : ℕ}` unrestricted, so the case is not excluded.
(This refutes `docs/fcom-uc.md`:340-346, which proposes
`δ = εᶜ n q` "since `εᶜ` is strictly positive"; see §8.)

**The slack that does work.** `dominatedᵒ`/`dominatedᵍ` take `δ : ℚ` with
`0ℚ ℚ.< δ` chosen per instance (`UC/Model/Dominated.agda:119,153`), so it may
depend on `n` alone. Take `δ = inv-pow-2 n`, strictly positive at every `n`
(`UC/Approximate/Decay.agda:83 0<inv-pow-2`). This is exactly the pattern the
corrupted-receiver second hop already spends
(`Examples/CoinToss/Ideal/Receiver/Compose.agda:101-107`, `ηʰ`,
`ηʰ-negligible` via `negligible-slack`, `UC/Approximate/Decay.agda:78`).

**Candidate realization schedules.**

```agda
εᴿ  n q = εᶜ n q ℚ.+ inv-pow-2 n          -- = (q+1)²·2⁻ⁿ         (corrupted committer)
εᴿʰ n q = εᵗ n q ℚ.+ inv-pow-2 n          -- = (3q+1)·2⁻ⁿ         (corrupted receiver)
```

with `εᵗ n q = fromℕ (q + (q + q)) *ℚ inv-pow-2 n`
(`Examples/ROCommitment/Hiding/Asymptotic.agda:54-55`). The closed forms are
`fromℕ-+` plus `*-distribʳ-+`, the shape of `collect`
(`Hiding/Asymptotic.agda:66-68`) and of `merge` (`Asymptotic.agda:44-46`);
`q*q + q + q + 1 = (q+1)*(q+1)` and `q + (q+q) + 1 = 3q+1`.
Negligibility is `GradedBound-+[ Negligible ] Negligible-+ …` at
`εᶜ-negligible` (resp. `εᵗ-negligible`) and `negligible-slack`, copying
`ηʰ-negligible` (`Receiver/Compose.agda:104-107`).

**Every allowance transformation, in order.**

| step | what moves the allowance | factor |
|---|---|---|
| 1. game bound | `asks≤ m d` on `Strat Q R` (`Game.agda:576`) | — |
| 2. game ports ↔ machine ports | `Q`/`R` (`Game.agda:60,66`) against `Neg`/`Pos (Advᴵ ⊗ᴵ Honᴵ)`; the relabelling is 1:1 on asks (`idleR` is outside the image — residual B2-M3) | ×1, needs a checked bijection (§7 B2-M7) |
| 3. per-strategy → per-context | budgeted `dominatedᵍ`: hypothesis at `asks≤ (ctxBudget c c′) d`, conclusion read at `ε (ctxBudget c c′)` — exactly `_≈ᵁᵠ[_]_`'s convention (`UC/Quantitative/Contextual.agda:58-62`) | identity |
| 4. domination slack | `+ δ`, taken as `+ inv-pow-2 n` | `+ 2⁻ⁿ` |
| 5. bracket change | `≈ctxᴬ⇒≈ctx` (`UC/Quantitative/Family.agda:123`) | identity |
| 6. assembly, inner leg | `UC-composeᵉ`'s `εf′ n q = εf n (simCost q (ctv n))` with `ctv n = (cost idᶜ n ℕ.⊔ 1) ℕ.* cv n` ∈ {0,1}; `simCost q 0 = simCost q 1 = q ℕ.* 1` (`UC/Budget.agda:80-81`) | identity |
| 7. assembly, outer leg | the upper stage compared with itself at the zero schedule | `+ 0ℚ` |
| 8. second hop | `≤UC^ωᵉ-trans` reads it at `simCost q (cost s₁ n)`; the hop's own schedule is `0ℚ` (committer, `Ideal/Compose.agda:74`) or `ηʰ`, which ignores its allowance (receiver, `Receiver/Compose.agda:101`) | `+ 0ℚ` / `+ 2⁻ⁿ` |

Composed candidates, in the existing pins' own expressions
(`εᶜⁱ`, `Examples/CoinToss/Ideal/Compose.agda:87`; `εᶜʳ`,
`Receiver/Compose.agda:135`):

```text
committer :  εᶜⁱ εᴿ  n q  =  (q+1)²·2⁻ⁿ
receiver  :  εᶜʳ εᴿʰ n q  =  (3q+1)·2⁻ⁿ + 2⁻ⁿ  =  (3q+2)·2⁻ⁿ
```

Neither replaces `ideal-ε` (`Ideal/Compose.agda:101`) or `ideal-εʳ`
(`Receiver/Compose.agda:146`): those pin the schedule as a FUNCTION of the
premise's schedule and keep checking unchanged. The new numbers are the
instances at `εᴿ`/`εᴿʰ` and get their own pins.

## 6. The assembly proof, verified

Checked green against `478d87f3` (`--safe --without-K --guardedness`, rc=0,
empty `ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing` gate) in
a scratch module over `Statement.agda`, then withdrawn. Recorded verbatim so
the proof agent does not re-derive it:

```agda
RcomQB  : (n : ℕ) → QB 0 (Rcom n)
RcomQB  n = qb-∘ (CTU.recvQB n) (CTIU.resourceQBᵒ n)
RcomʰQB : (n : ℕ) → QB 0 (Rcomʰ n)
RcomʰQB n = qb-∘ (CTHU.comQB n) (CTIU.resourceQBᵒ n)

coin-from-Rcom : Realization → (tossᶠ ∙ᶠ Rcom) ≤UC^ωᵉ (tossᶠ ∙ᶠ Icom)
coin-from-Rcom (sf , εf , nf , ef) =
  UC-composeᵉ sf εf nf ef
              idᶜ (λ _ _ → 0ℚ) (λ _ _ → Negligible-0)
              (≈C⇒≈ctx λ n → Equiv.sym (sub-identityˡ (tossᶠ n)))
              (λ _ → 0) (poly-const 0) RcomQB
              (λ _ → 0) (poly-const 0) CTU.tossQB

assembly : Assembly
assembly w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-resp (λ _ → sym-assoc) (λ _ → sym-assoc) (coin-from-Rcom w))
               coin-hybridᵉ

pin : (w : Realization) → proj₁ (proj₂ (assembly w)) ≡ εᶜⁱ (proj₁ (proj₂ w))
pin _ = refl
```

`coin-from-Rcomʰ`/`assemblyʰ`/`pinʰ` are the same with `tossʰᶠ`, `RcomʰQB`,
`(λ _ → 1) (poly-const 1) CTHU.tossʰQB`, `coin-hybridʳ` and `εᶜʳ`. The two
`pin`s are the point: the assembly carries the SAME schedule expression as
`schedule-pinⁱ` (`Ideal/Compose.agda:90`) and `schedule-pinʳ`
(`Receiver/Compose.agda:140`), so switching the headline theorems' premise from
open to resource-installed changes no number.

## 7. B2 — the residual obligations, checked against source

`docs/fcom-uc.md` and `docs/dp-transport.md` carry historical status claims.
Each item below says what was verified and where.

### Delivered (verified present)

| item | claim | verdict |
|---|---|---|
| B2-1 | `Settles` at a loop junction: `Settles-stepᵢ`, `Settles-stepᵢˢ`, `Settles-stepᵢ⋆`, `Ranked`, `Settles-iter` | DONE — `ProbabilisticLogic/Dp/Settle/Iter.agda:100,112,134,171,174` |
| B2-2 | `StepSettles` at a traced machine | DONE — `Protocol/Machine/Trace.agda:95 trace-settles`, hypotheses `kS` (body settles) and `rank`/`rk : Ranked`/`f`/`rb` |
| B2-3 | the `Dₚ`→kernel transport at an arbitrary closed machine | DONE — `Protocol/Machine/Raw.agda:61 StepSettles`, `:67 rawAgree`, `:112 rawPr`, `:126 rawKernel` |
| B2-4 | the RESOURCE's own instance of it | DONE — `Examples/ROCommitment/Transport.agda:66 resK`, `:181 resource-settles`, `:198 resource-run`, with `:80 resKᵀ-fetchT` identifying it with the game's oracle |
| B2-5 | the partial-kernel game toolkit | DONE — `GamePlaying/Partial.agda`: `badProb⊥`:46, `SuperCert⊥`:69, `badProb⊥-super`:84, `FLGP⊥`:143, `StepBisim⊥`:206, `runWith⊥-bisim`:211, `embedᵏ`:239, `total⇒⊥`:242, `prune`:249, `prune-cert`:252, `hop-bound⊥`:284 |
| B2-6 | the closed game and its supermartingale | DONE — `Examples/ROCommitment/Game.agda:525 keep-or-sample`, `:543 rare-raise`, `:569 cert`, `:576 extraction-bound`; total-kernel bisimulations `:306 stepR`, `:360 stepI` |
| B2-7 | the density lemma at the TRIVIAL grade | DONE — `UC/Model/Dominated.agda:114 ContextDominatedᵒ`, `:125 dominatedᵒ` |
| B2-8 | the density lemma at a NONTRIVIAL grade | DONE and IN USE — `UC/Model/Dominated.agda:150 dominatedᵍ`, consumed at `Examples/CoinToss/Ideal/Receiver/Compose.agda:113`. This supersedes `docs/fcom-uc.md`:371-378, which calls re-opening the grade "not proved, and not obviously cheap" (see §8) |
| B2-9 | the run-agreement deferred-sampling engine | DONE — `GamePlaying/Defer/Run.agda:58 DeferStep`, `:70 runFrom-defer`, `:101 run-defer`; consumed at `Examples/CoinToss/Ideal/Receiver/Machine.agda:47` |

### Missing (verified absent)

| item | statement | verdict |
|---|---|---|
| B2-M1 | `compose-settles` / `Settles-∘`: identify `𝒢ₚ`'s `_∘_` with a `traceᴹ` whose step has a kernel, so `trace-settles` applies to `real 𝒫.∘ resource` and to `subᴵ simulator 𝒫.∘ (ideal 𝒫.∘ resource)` | DONE — `Protocol/Machine/Trace/Compose.agda`: `Kᴳ`/`kᴳ-settles` give `Machines.Collapse.kᴳ` a kernel, `ranked-from-kᴳ` reduces `Ranked` to the dispatch, `compose-settles` is `trace-settles` at it, and `compose-StepSettles`/`compose-pr` are the closed instance. The `S.≈ᴹ` to `𝒢ₚ`'s own `_∘_` is crossed ONCE, at the closed run's `cum` reading, by the new `ProbabilisticLogic.Dp.Settle.cum-settled-≈ₚ` — which is what `docs/fcom-uc.md` §1 calls the escape hatch that does exist. No `Settles` witness rides an `_≈ₚ_`, so §1's verdict stands; what it did not notice is that the run-level conclusion may |
| B2-M2 | `Ranked` instances at `real`, `ideal`, `subᴵ simulator`, and the two composites | DONE — `Examples/ROCommitment/Realization/Machine.agda`: `rankedᴿ` (`real 𝒫.∘ resource`, rank 1/0, fuel 2), `rankedᴵⁿ` (`ideal 𝒫.∘ resource`, same), `rankedᴵ` (`subᴵ simulator` over that, rank `suc (Φˢ+Φˢ)`/`Φˢ+Φˢ`, fuel 4, reusing `Examples.ROCommitment.UC.Φˢ`). The step-table facts are `real-up`, `ideal-up`, `sub-up`; the three generic support clauses they need are `Dp.Support.Supp-bot`/`Supp-return`/`Supp-bind` |
| B2-M3 | the example's two `StepBisim⊥`s against pruned kernels, with `deadR`/`deadI` naming the off-protocol activations | REAL SIDE DONE — `Examples/ROCommitment/Realization/Bisim.agda:deadR`, `respR⊥`, `_≋ᴿ_`, `bisimᴿ : StepBisim⊥ʳ toQ fromR Kᴿ respR⊥ _≋ᴿ_`, read through the trace by `enterᴿ`/`oracleᴿ`/`digest-relay`/`digest-check`. IDEAL SIDE IMPOSSIBLE as the machines stand: `simulator` conses `(x , d)` onto its log at EVERY relayed answer (`Examples/ROCommitment.agda:195`), including one the oracle served from its table, so after a repeated query the log holds the digest twice and `extract` reads `false` (`Bisim.extract-relog`) where `Game.comI`'s `extract c t` reads the committed bit (`Bisim.extract-table`) — and the game's bad event is `dup` of the ORACLE's answer log, which a repeat does not raise. `Extraction.agda`'s header claim "the simulator's log IS the oracle's table" is false for this machine. Maintainer call: either `simStep` caches (`waitˢ (if the point is already tabulated then L else (x , d) ∷ L) m`) or `Game.respI` is restated over the relay log — the second makes `Game.cert` false |
| B2-M4 | `binding-bound`: the two-sided `cum` bound between the real and simulated-ideal CLOSED machines at every `asks≤ m d` | BLOCKED on B2-M3's ideal side; the real leg is DONE — `Examples/ROCommitment/Realization/Bound.agda:real-run` (the machine's `cum` family reaches `Pr₁⊥ (runWith⊥ respR⊥ sR₀ (mapStrat toQ fromR d))` exactly), `game-bound⊥` (`Game.cert` through `prune-cert` and the new `hop-boundᵇ⊥`/`badProb⊥-cong`, because pruning the COUPLING and pruning its marginal are only `E⊥`-equal), and `binding-real`, which bounds the closed real MACHINE against the pruned ideal GAME by `Game.ε m` at every `asks≤ m d`. Replacing that ideal game by the ideal machine is exactly what B2-M3 blocks |
| B2-M5 | a BUDGETED `dominatedᵍ` | MISSING as a name, but trivial: `dominatedᵍ`'s body already calls `dominated … (λ d _ → h d)` (`Dominated.agda:160`), discarding the budget hypothesis `dominated` accepts. The budgeted variant is the same proof with `(λ d q → h d q)` and hypothesis `… → asks≤ (ctxBudget c c′) d → runᴹ u d ≈ₚ[ ε ] runᴹ v d`, matching `dominatedᵒ`:120. Without it the game bound (restricted to `asks≤`) cannot be fed to `dominatedᵍ` at all |
| B2-M6 | `graded-∘ᵒ : gradedᵒ f ∘ procᵒ g ≈ gradedᵒ (f 𝒫.∘ g)` at a SINGLE grade | MISSING — `UC/Model/Graded.agda` exports `graded₂-∘ᵒ` (`:79`) for a TENSOR grade only, and its body is `G.Equiv.refl`. Needed to read `Rcom n = gradedᵒ real ∘ procᵒ resource` as `gradedᵒ (real 𝒫.∘ resource)`, i.e. as the `Proc unitᴵ (Advᴵ ⊗ᴵ Honᴵ)` that `dominatedᵍ` consumes. One line inside the existing `opaque unfolding gradedᵒ procᵘ` block |
| B2-M7 | the ask-preserving relabelling `Neg (Advᴵ ⊗ᴵ Honᴵ) ↔ Game.Q`, `Pos (Advᴵ ⊗ᴵ Honᴵ) ↪ Game.R` | DONE — `Examples/ROCommitment/Realization/Bisim.agda`: `toQ`/`fromQ` with `toQ-fromQ`/`fromQ-toQ`, `toR` and its section `fromR` with `fromR-toR`, `verdict-realOpen`. `idleR` is outside `toR`'s image and `fromR` sends it anywhere, which is sound because `prune deadR` removes exactly the activations that produce it. The strategy-level half is generic: `Strategy.mapStrat` with `asks≤-mapStrat` (one ask stays one ask) and `GamePlaying.Partial.runWith⊥-bisimʳ`, the alphabet-changing `runWith⊥-bisim` |
| B2-M8 | `comSimʰ : Certified Lkʰᶠ Advʰᶠ` | MISSING (§2), three lines |
| B2-M9 | `PolyQB Rcom`, `PolyQB Icom` (and the receiver twins) | MISSING, one line each; needed only for the `Canonicalᴺ._≤UC_` consequence |

### The route, once B2-M1..M7 are in

1. `binding-bound` (B2-M4) at `u = real 𝒫.∘ resource`,
   `v = subᴵ simulator 𝒫.∘ (ideal 𝒫.∘ resource)`, both `Proc unitᴵ (Advᴵ ⊗ᴵ Honᴵ)`.
2. Budgeted `dominatedᵍ` (B2-M5) at `P = Advᴵ`, `B = Honᴵ` → `_≈ᵁᵠ[ εᴿ n ]_`
   for every ancilla `W` and every budgeted `E`, `m`.
3. `≈ctxᴬ⇒≈ctx` (`UC/Quantitative/Family.agda:123`) → `_≈ctx[ εᴿ ]_`.
4. `≈ctx-resp` (`:139`) against `graded-∘ᵒ` (B2-M6) and `sub-gradedᵒ`
   (`UC/Model/Graded.agda:60`) to bring the two sides into the `Rcom` /
   `subᶠ comSim Icom` spelling.
5. Package: `comSim , εᴿ , εᴿ-negligible , (4)` — that is `Realization`.
6. `assembly` (§6).

Note the closure quantifier that `docs/fcom-uc.md`:324-333 and
`docs/dp-transport.md`:412-413 leave OPEN is closed by construction here: the
resource-installed boundary has `A n = 𝟘ᵒ`, so there is no resource left for a
closure to supply. That is the entire reason B1 moves the boundary.

## 8. Contradictions between the plan/docs and the code

1. **`docs/fcom-uc.md`:340-346 — the proposed slack is unsound at zero
   allowance.** It takes `δ = εᶜ n q` on the ground that "`εᶜ … ` is strictly
   positive". `εᶜ n 0 = fromℕ 0 *ℚ inv-pow-2 n = 0ℚ`, and `ctxBudget c c′ = 0`
   whenever `c = 0`, so `0ℚ ℚ.< δ` fails on an instance `_≈ctx[_]_`'s
   `{c c′ : ℕ}` does not exclude. The plan's
   B3 already flags this; the fix is §5's `δ = inv-pow-2 n`, which is what
   source already does at the receiver hop.
2. **`docs/fcom-uc.md`:371-378 — "re-opening the grade … not proved, and not
   obviously cheap" is out of date.** `UC/Model/Dominated.agda:150 dominatedᵍ`
   is exactly that, with a live consumer at
   `Examples/CoinToss/Ideal/Receiver/Compose.agda:113`. What is actually
   missing is narrower and cheaper: its budgeted variant (B2-M5).
3. **`docs/coin-toss.md`:316 cites `UC/Asymptotic/Compose.agda:219,251`
   for `≈ctx-dom`/`≤UC^ωᵉ-dom`.** `UC/Asymptotic/Compose.agda` is now 13 lines
   and re-exports `UC.Quantitative.Family.Compose`; the two live at
   `UC/Quantitative/Family.agda:438` and `:462`.
4. **The plan's `Rcoin → Hcoin` is "a generic contextual replacement" — it is,
   but not at the parenthesization the existing chain uses.** `UC-composeᵉ`
   produces `tossᶠ ∙ᶠ (realᶠ ∘ resᶠ)` where `coin-hybridᵉ` wants
   `(tossᶠ ∙ᶠ realᶠ) ∘ resᶠ`. The gap is one `sym-assoc` under
   `≤UC^ωᵉ-resp` (§1.3, §6) and costs nothing, but it is not automatic.
5. **The plan's B4 "corruption scope" wording should not be read as more than
   §4.4 gives.** The interfaces support static corruption of one party and a
   single commitment per level; there is no adaptive or multi-session content
   in any machine.
