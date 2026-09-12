# Direct model extraction

Branch `direct-extraction`, off `protocol-rewrite` at `4d4679a0` (plus the
cherry-picked `ROCommitment.Transport` merge-skew fix `245f314d`). This is
[`docs/uc-presheaf-preservation-plan.md`](uc-presheaf-preservation-plan.md)
§6 step 5: §4.1's direct observation lemma, §4.3's direct consequence and
re-routed probability endpoint, §4.2's sliding lemma, and a
retirement-readiness audit. Nothing is retired here (that is step 7) and no
consumer is edited (step 6b).

Everything below is a checked term unless it is in "Not delivered, precisely".
Hatches in `src/` stay at their baseline of zero: the
`postulate|TERMINATING|primTrustMe|\{!` grep counts **16 hits before and 16
after**, all of them the words "postulate-free" in inherited comments.

## §4.1 — the direct observation lemma

`src/CategoricalCrypto/UC/Seam/Audit/Context.agda:203,211,223`

```agda
ctxObs : {B : Iface} → Protocol unitᴵ B → Strat (Neg B) (Pos B) → Dₚ Bool
ctxObs {B} P e = obs (tv₁ 𝟘ᴳ (closedᵒ (morphism P)) (auditTest B e)) auditClose

extract-obs : {B : Iface} (P : Protocol unitᴵ B) (e : Strat (Neg B) (Pos B)) (c : ℚ)
            → ((n : ℕ) → Pr≤ n (ctxObs P e) ℚ.≤ c) → Pr P e ℚ.≤ c

extract-bounded : {B : Iface} (P : Protocol unitᴵ B)
                  (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
                → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d
                   → (n : ℕ) → Pr≤ n (ctxObs P (bad d)) ℚ.≤ ε q)
                → Bounded P bad ε
```

### Why this shape

* **No event class.** `AuditEvent`, `AuditBound`, `watched`, `watchedᵖ` and
  `absorb` do not occur in either statement. The only UC vocabulary left is the
  extraction context itself (`auditTest`/`auditClose`, kept per §4.1), and that
  is a *machine* object, not a designation.
* **A bound, not a domination, at the hypothesis.** §4.1 offers either. The
  numeric-bound form is what both consumers need — the membership route reads
  `AuditBound`'s conclusion, which is already a bound, and the direct route
  reaches one through `dominate` — so the one-sided domination stays where it
  belongs, at the ideal side (`sim-prefixed` below) rather than in the
  extraction lemma's own premise.
* **Universally quantified `n`.** `extract`'s old proof used the bound at one
  index (`proj₁ reach`, produced by `≼ₚ`'s witness). Making it a `∀ n` premise
  is free for every supplier — an `AuditBound` and a `Pr≤` bound are both
  already `∀ n` — and removes the only place where the extraction had to know
  which index the identification landed on.
* **`c : ℚ` rather than `ε : ℕ → ℚ`.** The allowance bookkeeping is the
  *caller's*; `extract-obs` compares one run against one number.
  `extract-bounded` is the `Bounded`-shaped repackaging, and it exists because
  both routes consume that shape (it is not single-use scaffolding).
* **What stayed in `Bounded`.** `PrAgree`, the budget matching and the
  rational-order arguments of `UC.Seam.Audit.Bounded.supply` are untouched;
  `supply` is now used by BOTH routes and must not be retired. `prAgree` itself
  appears in `extract-obs` because that is the step that reads layer 1's
  probability off the machine run — it was already in `Context.extract` and did
  not move.

### `extract` is re-routed, not restated

`Context.agda:234` — the signature is byte-identical to the one on
`protocol-rewrite`. The proof is now

```agda
extract {B} P bad ε bad-asks mem bnd = extract-bounded P bad ε λ q d a n →
  subst (λ k → Pr≤ n (ctxObs P (bad d)) ℚ.≤ ε k) (ℕP.*-identityʳ q)
        (bnd 𝟘ᴳ (auditTest B (bad d)) auditClose
             (audit-qb B (bad d) q (bad-asks q d a)) qb-λ⇐ (mem q d a) n)
```

i.e. the new lemma plus exactly the membership plumbing (`audit-qb`, `qb-λ⇐`,
the `q * 1` allowance, the class membership `mem`). That is the disposition
§4.1 asks for: re-routed, same statement, with the numerical content now
reusable by a route that has no membership to supply.

## §4.3 — the prefix route's direct consequence

`src/CategoricalCrypto/UC/Seam/Audit/Prefix.agda:87,180`

```agda
prefix-absorbᵒ : (B : Iface) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (W : Channel)
                 (Et : W ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ) {D : Channel}
                 (g : D ⇒ W ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B)) (m : 𝟘ᵒ ⇒ D)
               → Obs (((Et ∘ id ⊗₁ sub s) ∘ g) ∘ m)
                 ≈ₚ (pointᵒ 𝟘ᴳ 𝟘ᴳ s >>=ₚ λ _ → Obs ((Et ∘ g) ∘ m))

sim-prefixed : (B : Iface) (I : Protocol unitᴵ B) (e : Strat (Neg B) (Pos B))
               (s : 𝟘ᴳ ⇒ 𝟘ᴳ)
             → obs (tv₁ 𝟘ᴳ (sub s ∘ closedᵒ (morphism I)) (auditTest B e)) auditClose
               ≼ₚ[ 0ℚ ] runᴹ (morphism I) e
```

`prefix-absorbᵒ` is `subPrefixedˢ` read off the observation by
`prefixedᵒ-bind`, hoisted out of `absorb-watchedᵖ`'s own proof (which now calls
it, so the bracketing argument exists once). `sim-prefixed` is the mass
consequence: the simulator-fronted ideal monitored observation is dominated by
the ideal monitored run **with zero slack**, by `Dp.Mass.const-bind-≼` — a
prefix is never seen to add mass.

**The totality premise is not consumed by this direction, and that is a
finding.** `ASTotal` is what the two-sided `≈ₚ[ ε ]` of `prefixedᵒ-obs` needs;
the one-sided half needs nothing. The premise is nevertheless kept verbatim in
the public theorem below (the brief's instruction, and the right call: it is
part of `uc-audit-bounded`'s interface and of `UC.Asymptotic.Audit`'s).

### The re-routed public theorem

`Prefix.agda:227`, beside `uc-audit-bounded` (`:154`), which is untouched.

```agda
uc-audit-bounded′ : (B : Iface) (R I : Protocol unitᴵ B)
                    (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) {cs : ℕ}
                    (em : closedᵒ (morphism R) ≤UC[ cs ] closedᵒ (morphism I))
                    (ε : ℕ → ℚ) (ν : ℚ) → 0ℚ ℚ.< ν
                  → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim em))
                  → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
                  → Bounded I bad ε
                  → Bounded R bad (λ q → ε (simCost q cs) ℚ.+ ν)
```

#### Old versus new, side by side

| | `uc-audit-bounded` (`:154`) | `uc-audit-bounded′` (`:227`) |
|---|---|---|
| interfaces/protocols | `B`, `R I : Protocol unitᴵ B` | identical |
| monitor | `bad : Strat … → Strat …` | identical |
| emulation | `closedᵒ (morphism R) ≤UC[ cs ] closedᵒ (morphism I)` | identical |
| error schedule | `ε : ℕ → ℚ` | identical |
| carry slack | `ν : ℚ`, `0ℚ < ν` | identical |
| initialization totality | `ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim em))` | identical (present, not consumed) |
| monitor budget law | `(q)(d) → asks≤ q d → asks≤ q (bad d)` | identical (present, not consumed) |
| ideal bound | `Bounded I bad ε` | identical |
| **conclusion** | `Bounded R bad (λ q → ε (simCost q cs) ℚ.+ ν)` | **identical** |
| route | `boundedIsAuditᵖ` → `audit-carry` + `absorb-absorbs` → `auditIsBoundedᴬ` (→ `ctx-absorb`, `absorb-watchedᵖ`, `extract`) | `bounded-carry` = `dominate` + `sim-prefixed` + `supply` + `extract-obs` |

The two hypothesis lists and the two conclusions are the same Agda type,
argument for argument; `uc-audit-bounded′` is a drop-in for
`uc-audit-bounded` at every call site. Neither the charged allowance
`simCost q cs` nor the totality premise was touched.

#### The strictly more general statement

`Prefix.agda:208` — what the route actually consumes, of which the theorem
above is an instance:

```agda
bounded-carry : (B : Iface) (R I : Protocol unitᴵ B)
                (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
                (s : 𝟘ᴳ ⇒ 𝟘ᴳ) → closedᵒ (morphism R) ≈ℰᶜ (sub s ∘ closedᵒ (morphism I))
              → (p : ℕ → ℕ) → ((q : ℕ) → q ℕ.≤ p q)
              → (ε : ℕ → ℚ) (ν : ℚ) → 0ℚ ℚ.< ν
              → Bounded I bad ε → Bounded R bad (λ q → ε (p q) ℚ.+ ν)

uc-audit-bounded′ B R I bad {cs} em ε ν ν>0 _ _ =
  bounded-carry B R I bad (sim em) (emulate em)
                (λ q → simCost q cs) (λ q → q≤simCost q cs) ε ν ν>0
```

Three things the budgeted route spends are not spent here, and each is worth
recording rather than hiding:

1. **No query certificate.** `sim-qb` is never used. An environment agreement
   holds at EVERY test — `_≈ℰᶜ_` carries no budget — so nothing on this route
   has to pay for the simulator's queries out of a context's allowance. The
   whole `QB`/`ctxBudget`/`ctxBudget-absorb` arithmetic of `audit-carry`
   exists because `AuditBound` quantifies over *budgeted tests*; `Bounded`
   quantifies over *strategies*, and that is the quantifier the allowance moves
   in.
2. **No `bad`-budget law.** `Bounded I bad ε` already charges `ε` at the budget
   of `d`, not of `bad d`, and `supply` consumes it at exactly that budget. The
   premise is kept in `uc-audit-bounded′` only to match the statement beside it.
3. **The allowance inflation is a parameter.** Any `p` with `q ≤ p q` works;
   `simCost` is the instance the migration test needs. The uncharged reading
   (`p = id`) is a **different theorem**, not a weakening and not a
   strengthening: an arbitrary `ε` is monotone in no direction
   (`docs/quantitative-family.md`, "error reindexing"), so neither implies the
   other. `bounded-carry` is the statement of which both are instances, and it
   is the one that says what is true.

## §4.2 — structural sliding

`src/CategoricalCrypto/UC/Seam/Slide.agda` (new, 44 LOC).

```agda
run-subᵒ : (W : Channel) (s : Y ⇒ X) (g : A ⇒ T₀ Y B) (e : Env (T₀ (W ⊗₀ X) B))
         → run W (sub s ∘ g) e ≈ run W g (regradeEnv W s e)
run-subᵒ W s g e = (refl⟩∘⟨ sub-decomp s g W) ○ sym-assoc

slide⊗ : (W : Channel) (h : B ⇒ C) (k : A ⇒ B) → id {W} ⊗₁ (h ∘ k) ≈ id ⊗₁ h ∘ id ⊗₁ k
```

`run-subᵒ` is the §4.2 identification, once: `Abstract2.Action.regradeEnv W s`
at `UC.Model.Setup.StdSetup` is precomposition with `sub (id ⊗₁ s)`, and the
slide holds at REPRESENTATIVES — a categorical `≈` in `∣𝔾ᵒ∣`, off
`Abstract2.sub-decomp`, which is `run-sub`'s own ingredient. It is stated there
and not in the environment setoid for the reason the plan gives: `≈Env` at this
model is `≋`, closeness of closed observations at every positive error, which
retains no exact mass, so a `Pr` bound or an advantage does not transport along
it. The numerical consumers below transport an exact `≈ₚ` along the
representative equality instead.

`slide⊗` is the operational wire: the ancilla in front of a composite is two
ancilla wires in sequence. It is stated in the tensor's vocabulary rather than
at `T₁` because the graded action a *test* is built with is `gradingᵗ 𝔾ᵒ`'s,
whose record is not the curried tensor's even though the two agree on the nose
(`docs/graded-bridge.md`, "One measured obstacle worth recording"); a statement
mixing the two is rejected with `MismatchedProjectionsError`, which is how this
was found.

Three copies of that merge are now one call:

| site | was | is |
|---|---|---|
| `UC.Seam.Audit.Context.plug-runᵍ`'s `merge` | `(⟺ T₁-⊗ ⟩∘⟨ ⟺ T₁-⊗) ○ ⟺ T-homomorphism` | `⟺ (slide⊗ …) ○ ⟺ (T₁-⊗ …)` |
| `UC.Seam.Grounded.subPrefixed`'s `split` | `⟺ T₁-⊗ ○ T-homomorphism ○ (T₁-⊗ ⟩∘⟨ T₁-⊗)` | `slide⊗ Y (sub s) wire` |
| `UC.Seam.Audit.Prefix.sim-prefixed`'s `slide` | (would have been a fourth) | `slide⊗ 𝟘ᴳ (sub s) f₀` |

### The optional item is declined, with a reason

§4.2's optional item — replace `UC/Robust/Observation.agda`'s `robust-sub`
slide with a `run-sub`-based one — is **not cheap and not clean**, and the plan
itself says why. `UC.Robust.Observation` is stated at an arbitrary `UCBase`
(its header, and §5's `UC.Robust` row), where there is no graded Kleisli triple
and hence no `μ`, no `prefix`, no `run` and no `run-sub`: `run-sub` lives at a
`UCSetup`. Rewriting `robust-sub` through it would mean moving that module to a
`UCSetup`, which is exactly the scope change §3.1 forbids ("Keep the old
generic proof content in an observation-specific module unless a
scope-preserving replacement is supplied"). The statement is left verbatim and
its two-line slide stays. See the residuals for what *is* duplicated there.

## Retirement readiness (§5 gates) — nothing is retired here

Importers are in-repo and transitive through `open … public`. `UC.Seam.Audit`
re-exports `UC.Audit`'s names publicly; `UC.Seam.Audit.TrivialGrade` is a
different module from `UC.Seam.Grounding.TrivialGrade` (same name, disjoint
content — `Grounded.agda`'s `module TG = TrivialGrade 𝟘ᴳ ιᴳ` is the Grounding
one and is NOT an importer of the audit one).

| name | in-repo importers | §5 gate | satisfied given items 1–2? |
|---|---|---|---|
| `absorb-watchedᵖ` (`Prefix:99`) | `ctx-absorb` (same module) only | `UC.Seam.Audit.Prefix`: retire after the unchanged probability endpoint is recovered | **Yes.** `uc-audit-bounded′` recovers it verbatim. Retires together with `uc-audit-bounded`'s current proof. |
| `ctx-absorb` (`Prefix:129`) | `auditIsBoundedᴬ` (same module) only | same row | **Yes**, same argument. |
| `auditIsBoundedᴬ` (`Prefix:141`) | `uc-audit-bounded` (same module) only | same row | **Yes**, same argument. |
| `watchedᵖ` (`Audit:90`) | `Audit` (`AuditIsBoundedᵖ`/`BoundedIsAuditᵖ`), `Audit.Bounded` (`auditIsBoundedᵖ`, `boundedIsAuditᵖ`), `Audit.Prefix` (the three above) | `UC.Seam.Audit`: retire after exact and prefix consumers migrate | **Yes for the prefix side.** No module outside the `UC.Seam.Audit` cone mentions `watchedᵖ`; every conclusion stated at it is recovered by `uc-audit-bounded′`. |
| `AuditIsBoundedᵖ` / `auditIsBoundedᵖ` | none (`auditIsBoundedᵖ` has no consumer at all today) | same row | **Yes** — already dead before this step; `uc-audit-bounded′` removes any future need. |
| `BoundedIsAuditᵖ` / `boundedIsAuditᵖ` | `Prefix.uc-audit-bounded` only | same row | **Yes**, with `uc-audit-bounded`'s route. |
| `watched` (`Audit:76`) | `Audit.Bounded` (`ctx-watched`, `watched⇒watchedᵖ`, `auditIsBounded`, `boundedIsAudit`), `UC.Asymptotic.Audit` (`uc-audit-carry`'s conclusion), `Examples/ChimericLedger/Audit` (`auditEvent`, `audit-bound`, `audit-bounded`, `audit-target`) | same row | **No.** Two exported consumer statements are stated *at* `watched` — `Examples.ChimericLedger.Audit.auditEvent` and `uc-audit-carry` — and their migration is step 6b. `ledger-audit-carry` (`EndToEnd:215`) consumes the latter and its conclusion has no direct replacement here. |
| `TrivialGrade` (`Audit:67`) | `Audit.Bounded`, `Audit.Prefix`, `UC.Asymptotic.Audit`, `Examples/ChimericLedger/Audit` | same row | **No** — it is the module `watched` lives in; it retires with `watched`. |
| `uc-audit-carry` returning only `AuditBound` (`Asymptotic/Audit:57`) | `Examples/ChimericLedger/EndToEnd.ledger-audit-carry` | `UC.Asymptotic.Audit`: retire the `AuditBound`-only return; keep existing probability results as proved specializations until migrated | **No.** `ledger-audit-carry` is an exported statement at `AuditBound … (absorb … (watched …))`; nothing in this step gives it a direct form, and §5's `UC.Audit` row independently requires `audit-carry`'s generic quantitative content to be retained. |

Two things that look retirable and are NOT:

* **`UC.Seam.Audit.Bounded.supply`** is now load-bearing for *both* routes
  (`boundedIsAudit`, `boundedIsAuditᵖ`, and `bounded-carry`). §4.1 says its
  arithmetic stays in `Bounded`; it does.
* **`UC.Audit.audit-carry`, `pinned`, `pinned-bound`, `absorb`,
  `absorb-absorbs`** are generic over `UCBase`/`Budget`/`Mass` with arbitrary
  event data. Nothing in this step reaches that scope, and §5's `UC.Audit` row
  gates them on a direct theorem *at that scope*. Untouched.

## Module costs

Canonical check, `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`,
rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate on every run. Warm figures are single-`Checking`-line runs, forced by
deleting the module's `.agdai` under `_build/` (agda 2.8 keys staleness on
content, so `touch` does nothing).

| module | LOC before → after | warm before | warm after | rule-5 budget |
|---|---|---|---|---|
| `UC.Seam.Slide` | — → 44 | — | 9 s | 71 s |
| `UC.Seam.Audit.Context` | 229 → 245 | 10 s | 10 s | 121 s |
| `UC.Seam.Audit.Bounded` | 104 → 104 | 10 s | 10 s | 86 s |
| `UC.Seam.Audit.Prefix` | 143 → 237 | 11 s | 11 s | 118 s |
| `UC.Seam.Grounded` | 281 → 280 | — | 10 s | 130 s |

No module moved by more than a second; nothing is near the 20 % regression bar
or its rule-5 budget. (A large part of each figure is interface
deserialization, which is why 90 added lines in `Prefix` cost nothing
measurable.)

## Not delivered, precisely

Typed residuals — signatures, never holes or postulates in `src/`.

### 1. The `UCBase`-level test-absorption slide is still duplicated

```agda
slide : (Et ∘ T₁ W (sub s ∘ g)) ∘ m ≈ ((Et ∘ T₁ W (sub s)) ∘ T₁ W g) ∘ m
slide = ∘-resp-≈ˡ (Equiv.trans (∘-resp-≈ʳ T₁-∘) sym-assoc)
```

occurs verbatim in `UC.Audit.audit-carry` (`:177`) and
`UC.Robust.Observation.robust-sub` (`:99`). Its natural home is
`UC.Environment`/`UC.Emulation`, where `tv₁` is defined — modules this step
does not own. `UC.Seam.Slide` cannot serve: `UC.Robust.Observation` must not
import the seam. One line, two copies, no soundness content.

### 2. `uc-audit-bounded′` has no consumer yet

`UC.Asymptotic.Audit.uc-audit-boundedᵖ` and, through it,
`Examples.ChimericLedger.EndToEnd.ledger-uc-to-pov-simCost` still go through
`uc-audit-bounded`. Migrating them is step 6b and needs an edit to files this
step does not own. The drop-in is:

```agda
uc-audit-boundedᵖ … = uc-audit-bounded′ _ (R n) (I n) (bad n) (em n) (ε n) (ν n)
                                        (pos n) (tot n) (qp n) (bi n)
```

— the argument list is unchanged, since the two theorems have the same type.

### 3. No direct form of `uc-audit-carry`'s `AuditBound` conclusion

`uc-audit-carry` ends at a graded bound by design (`UC.Asymptotic.Audit`'s
header). `bounded-carry` is the probability-valued analogue and does not
subsume it: an `AuditBound` is a statement about every budgeted *test*, and a
`Bounded` about every budgeted *strategy*, with `StratIsEnv` in one direction
only (`docs/graded-bridge.md` §2). The `watched`/`TrivialGrade` gate above is
blocked on this, not on proof work in this step.

### 4. Nothing here touches the nontrivial grade

§4.4 is untouched: `sim-prefixed` is a trivial-grade statement
(`s : 𝟘ᴳ ⇒ 𝟘ᴳ`), and `scalar-blindᵒ` is why it holds. The nontrivial-grade
`Pr` bound is `UC.Seam.Audit.Context.extractᵍ`, which this step leaves alone.

## Root-file inventory rows to update

Reported, not edited — `src/CategoricalCrypto/UC.agda` and
`src/CategoricalCrypto.agda` are outside this step's file scope.

* `src/CategoricalCrypto/UC.agda`, the `UC.Seam.Audit.Prefix` row: it currently
  describes the budgeted route's consumer end as the membership route. It now
  has two ends — `uc-audit-bounded` (membership) and `uc-audit-bounded′`
  (direct), the same statement — and additionally carries `sim-prefixed` and
  `bounded-carry`, which is where the route's real premises are visible.
* `src/CategoricalCrypto/UC.agda`, the `UC.Seam.Audit.Context` row: add
  `extract-obs`/`extract-bounded` as the event-class-free half of `extract`.
* `src/CategoricalCrypto/UC.agda` and `src/CategoricalCrypto.agda`: a new
  inventory line for `UC.Seam.Slide` (the model's `regradeEnv` identification
  and the ancilla composition slide).
