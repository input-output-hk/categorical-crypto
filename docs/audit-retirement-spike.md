# Retiring `UC.Audit`'s event-bound layer — spike

Base `52abe89d` (protocol-rewrite), branch `audit-spike`. New, unwired modules:
`UC/Spike/AuditContext.agda` (44 lines), `UC/Spike/AuditRated.agda` (102),
`UC/Spike/AuditBounds.agda` (107). `--safe --without-K` (`--guardedness` for the
machine one); escape-hatch count 16 before and after.

## Verdicts

**A — what generalises.** `Context`/`observeᶜ`/`_∙ᶜ_`/`≈ᵁ-at` are `AbstractUC`-level
and are already almost all in `UCSetup`: a context is `Σ[ Y ∈ ℐ.Obj ] Env (T₀ (Y ⊗₀ X) B)`,
`observeᶜ (Y , d) f = run Y f d`, `_∙ᶜ_` is `regradeEnv`, and `≈ᵁ-at` is `run-sub`. The
equivalence `f ≈ᵁ g ⇔ ∀ k → observeᶜ k f ≈ observeᶜ k g` is the constructor/projection of
`KE._∼_` (one line each way). `UC.Audit.Context`'s closure `m` is `Evaluation`'s reading
of `Env` at `StdSetup`, not part of the context. `Certified` has real content (the rates)
and stays at the rated level, beside `_≤UC[_]_`; rebuilt on `L`'s data it has no cast
fields and forgetting is definitional. Answer to (i): only `Certified` is needed as a
notion; `Context` is `UCSetup`'s `(Y , d)` pair.

**B — GO** for deleting `Permitted`, `AuditBound`, `pinned`, `pinned-bound`, `absorb`,
`Absorbs`, `audit-carry`, `Seam/Audit/Context.{auditCtxᵍ, extractᵍ}` and the graded half
of `Seam/Audit/Context`. Its one consumer, `hf-pr-bound`, gets a strictly stronger,
hypothesis-free, slack-free replacement at the machine (`AuditBounds.HashForward`), and
the open-system carry `audit-carry` existed for becomes `bounded-absorb`, a
`BoundedAt` statement. Answer to (iii): `AuditBound` was a mass bound over a class of
certified contexts at a general base; its only instance was a singleton class pinned to a
designation, and its `δ` slack was the price of reading the qualitative readout (`∼ᵃ`,
all positive slacks) as a lower real, which the machine-level `Upper` does not pay.

## A. Context and Certified

`AuditContext` (any `UCSetup`):

| name | statement | proof |
|---|---|---|
| `Context X B` | `Σ[ Y ∈ ℐ.Obj ] Env (T₀ (Y ⊗₀ X) B)` | — |
| `observeᶜ` | `(k : Context X B) → A ⇒ T₀ X B → Env (T₀ (proj₁ k) A)` | `run Y f d` |
| `≈ᵁ⇔observeᶜ` | `f ≈ᵁ g ⇔ (∀ k → observeᶜ k f Env.≈ observeᶜ k g)` | `mk⇔` of `KE.run∼`/`KE.mk∼` |
| `_∙ᶜ_` | `Context X B → Z ℐ.⇒ X → Context Z B` | `regradeEnv` |
| `∙ᶜ-∘` | `(k ∙ᶜ a) ∙ᶜ s ≈ k ∙ᶜ (a ∘ s)` | `regrade-∘` |
| `≈ᵁ-at` | `f ≈ᵁ sub s ∘ g → observeᶜ k f ≈ observeᶜ (k ∙ᶜ s) g` | `≈ᵁ` then `run-sub` |

`AuditRated` (same parameters as `UC.Audit`, at `StdSetup M ℰᴼ`):

- `Closed A X B = Σ[ k ∈ Context X B ] Closure (T₀ (proj₁ k) A)`,
  `observeᴱ (k , m) f = observe (observeᶜ k f) m`, and `≈ᵁ⇔observeᴱ` (two lines): at
  `ℰᴼ`, `Env.≈` is `∀ m → observe _ m ≈ observe _ m`, so the closure is the
  `Evaluation`'s quantifier.
- `fromAudit : Aud.Context A X B → Closed A X B` sends `(Y, Et, m)` to
  `((Y , Et ∘ α⇒) , m)` and `observe-fromAudit` proves the readings agree (`read-resp` of
  `UC.Audit`'s own cast). The only difference is the bracketing of the test's domain.
- `Certified A X B`: fields `Y`, `c r′ : ℕ⁺`, `Êt : L.Hom c (T₀ (Y ⊗₀ X) B) Ω`,
  `m̂ : L.Hom r′ J (T₀ Y A)`, and `budget = value (c · r′)` — i.e. a `Closed` in `L`.
  `forget k = (Y , ⌊ Êt ⌋) , ⌊ m̂ ⌋`. `Êt≈`/`m̂≈` are gone.
- `_∙ˢ_ : Certified A X B → L.Hom r Z X → Certified A Z B` is post-composition in `L`
  with `(L.id ⊗ʰ s) ⊗ʰ L.id` (= `sub (id ⊗₁ s)`), regraded by `sub[ ≤-reflexive … ]`.
  `forget-∙ˢ : proj₁ (forget (k ∙ˢ s)) ≡ proj₁ (forget k) ∙ᶜ ⌊ s ⌋` is `refl`;
  `budget-∙ˢ` is unchanged; `≈ᵁ-atˢ : (em : f ≤UC[ r ] g) → observeᴱ (forget k) f ≈
  observeᴱ (forget (k ∙ˢ proj₁ em)) g` is `≈ᵁ-at` applied, no cast.

Placement and size after the move:

| name | level | lives in | LOC now → after |
|---|---|---|---|
| `Context`, `observeᶜ`, `≈ᵁ⇔observeᶜ`, `_∙ᶜ_`, `≈ᵁ-at` | `AbstractUC` | `Abstract2` (beside `_≈ᵁ_`) | 4+2+2+9 → 2+2+2+2+3 |
| `∙ᶜ-∘` | `AbstractUC` | `Abstract2` | — → 3 |
| `Closed`, `observeᴱ`, `≈ᵁ⇔observeᴱ` | `StdSetup` + `Evaluation` | `UC/Audit` | — → 7 |
| `Certified`, `forget`, `_∙ˢ_`, `budget-∙ˢ`, `≈ᵁ-atˢ` | rated (`GradedSubCat`) | `UC/Audit` | 11+0+7+3+0 → 8+2+6+3+3 |

`Context` could also be dropped as a name (it is `UCSetup.run`'s arguments); kept here
because `Certified` forgets to it.

## B. Retiring `AuditBound`

`AuditBounds` (machine level):

- `advReader a : Reader B (X ⊗ᴵ B)`, `advReader a Y E = E ∘ T₁ᴵ Y (plugᴹ a)` — the
  machine spelling of `auditTestᵍ` (the adversary between test and process).
- `readRun-absorb : f ≈ subᴵ s ∘ g → readRun Y f (advReader a) E m ≈ₚ
  readRun Y g (advReader (a ∘ s)) E m` (`ctxRun-∘` twice around `plug-absorb`).
- `AdvBoundedAt k q r f = (a : Proc X 𝟭ᴵ) → QB k a → BoundedAt q r f (advReader a)`.
- `bounded-absorb : f ≈ subᴵ s ∘ g → QB t s → AdvBoundedAt (k * t) q r g →
  AdvBoundedAt k q r f` — `audit-carry` with no `Permitted`, no `Absorbs`, no `δ`.
  The simulator's rate multiplies the **adversary's** allowance; the context cap `q` is
  untouched. `hf-pr-bound`'s `scale (value (c · q · c′)) 2⁺` is the same product read
  with the adversary's `c` folded into the context's budget.
- `readRun-closed : readRun unitᴵ f (advReader a) (stratTest B d) (conjᴵ w) ≈ₚ
  runᴹ ((plugᴹ a ∘ f) ∘ w) d` (`T₁-∘`, `λ-nat`, `embeds`, `adequacy`), and
  `closed-bound` reads an `AdvBoundedAt` off at that context; a closed `w` costs
  `QB 0`, so the cap is exactly the strategy's `asks≤ q`.

At the toy (`module HashForward`):

```agda
hf-bounded  : AdvBoundedAt (k * 2) q r ideal → AdvBoundedAt k q r real
hf-exact    : runᴹ ((plugᴹ a ∘ real) ∘ w) d ≈ₚ runᴹ ((plugᴹ (a ∘ simulator) ∘ ideal) ∘ w) d
hf-pr-bound : Upper (runᴹ ((plugᴹ (a ∘ simulator) ∘ ideal) ∘ w) d) r
            → Upper (runᴹ ((plugᴹ a ∘ real) ∘ w) d) r
```

`(plugᴹ a ∘ real) ∘ w` is `closedᵍ Honᴵ e a real w` by definition. `Near` is not needed:
`real-factors` is an exact machine equality, so `Transport.transport` at `ε = 0` collapses
to `upper-≈`. Comparison with the current `hf-pr-bound`
(`… → absorb simᶜ (pinned idealᵒ μ) (auditCtxᵍ …) → Pr≤ n (runᴹ (closedᵍ …) e) ≤
(ε (scale (value (c · q · c′)) 2⁺) + δ) + η`): its premises `mem`+`bnd` say exactly that
the ideal run with the simulator absorbed is pinned to a `μ` bounded by `ε`; the new
statement takes any `Upper` of that run and pays neither `δ` nor `η`. A verbatim
re-derivation of the old statement from the new one needs one sealed lemma, not built:
`procᵘ a ∘ simᵒ ≈ procᵘ (a ∘ simulator)` at `𝔾ᵒ` (to turn `mem` into `Upper` via
`audit-runᵍ`) — but deleting the old statement makes this moot.

### Deletion list

| file :: name | LOC | replaced by |
|---|---|---|
| `UC/Audit` :: `Permitted` | 2 | — (the reader is the class) |
| `UC/Audit` :: `AuditBound` | 2 | `AdvBoundedAt` / `BoundedAt` |
| `UC/Audit` :: `pinned`, `pinned-bound` | 2+4 | — (designations unneeded) |
| `UC/Audit` :: `absorb`, `Absorbs` | 2+2 | `readRun-absorb` |
| `UC/Audit` :: `audit-carry` | 7 | `bounded-absorb` |
| `UC/Audit` :: `mass` parameter, `LowerReal`/`ℚ` imports, header | ~8 | — |
| `UC/Model/Enrichment` :: `massᵒ` (+ comment, import) | 7 | — |
| `UC/Model/Audit` :: re-export list | 3 lines shrink | — |
| `UC/Seam/Audit/Context` :: `auditTestᵍ`, `audit-qbᵍ`, `closedᵍ`, `plug-runᵍ`, `audit-runᵍ`, `auditCtxᵍ`, `extractᵍ` | 64 | `advReader`, `readRun-closed`, `closed-bound` |
| `Examples/HashForward/Audit` :: `absorbed-budget`, `hf-audit-carry`, `silent`, `silent-bound`, `hf-audit-silent`, `hf-pr-bound` | ~50 | `hf-bounded`, `hf-exact`, `hf-pr-bound` (~15) |

The ungraded half of `Seam/Audit/Context` (`auditClose`, `auditTest`, `audit-qb`,
`audit-run`) stays: `UC/Model/Family/Emulation.≈ᶠ-runs` uses it. `hf-emul`/`simᶜ` stay as
the rated emulation's example. Comments naming `UC.Audit`'s classes in
`UC/Machine/EventBounds` (header, `ctxRun-∘`, `boundedᶠ⇒boundedᴺ`) need rewording.

Afterwards `UC/Audit.agda` holds `_≤UC[_]_`, `≤UC[]⇒≤UC`, `Closed`/`observeᴱ`,
`Certified`, `forget`, `_∙ˢ_`, `budget-∙ˢ`, `≈ᵁ-atˢ` (~45 lines, parameters `M R Rg`).
The machine half goes beside `BoundedAt` (`UC/Machine/EventBounds`, or `…/Transport`,
which already imports `Seam`/`Monitor.Agree`); `embeds` (in `StateEvent.Agree`) belongs
next to `stratTest` in `Monitor.Agree`.

### Estimate

One session. Branch 1 (`UC/Audit`, `Abstract2`) is a new branch-1 ref with the
`AuditContext`/`AuditRated` content moved in; the machine half and the `HashForward`
reshape are protocol-rewrite edits on top. Measured costs here are small (warm, single
module, `-M3G -H1G`): `AuditContext` 2.8 s, `AuditRated` 7.8 s, `AuditBounds` 10.1 s.

Not settled: composing `advReader` with `flagReader` (a flagged open system with a
simulator, `docs/state-event-transport-spike.md` §1(c)) — readers compose, but no
`StateBoundedAt` instance was built.
