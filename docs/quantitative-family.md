# The quantitative family layer — steps 3 and 4

What steps 3 and 4 of `docs/uc-presheaf-preservation-plan.md` delivered, on branch
`quantitative-family` off `protocol-rewrite` at `ac8b018f`. Paths are relative to
`src/CategoricalCrypto/` unless prefixed.

## 1. The relation, and why it is spelled this way

`UC/Asymptotic/Contextual.agda` is the new home of the plan's `f ≈ctx[ε] g`.

| Name | file:line | content |
|---|---|---|
| `Homᶠ A X B` | `:62` | `(n : ℕ) → A n ⇒ T₀ (X n) (B n)` — a family of GRADED semantic morphisms, one per level, each at its own domain, adversary grade and codomain |
| `prefixᵒ` | `:70` | `μ W X′ ∘ T₁ W f` |
| `_≈ctx[_]_` | `:79` | `∀ n W E m {c c′} → QB c E → QB c′ m → Obs ((E ∘ prefixᵒ W (f n)) ∘ m) ≈ₚ[ ε n (ctxBudget c c′) ] Obs ((E ∘ prefixᵒ W (g n)) ∘ m)` |
| `_≈ctxᴬ[_]_` | `:89` | the same experiment at the operational bracket `W ⊗ (X ⊗ B)`, with `T₁ᵒ` in place of `prefixᵒ` |

Two spelling decisions, both measured.

**The `μ`/`T₁` shape, not `Abstract2.Action.prefix`.** `prefix W f` is *definitionally*
`μ W X ∘ T₁ W f`, so the two relations are the same type; what differs is the cost of
having `Abstract2.Action StdSetup` in the import graph, which is a module application of
the whole action at the standard setup. Measured on this module: **+22 s** (38.1 s against
15.6 s for the identical file with the application removed). Every lemma the proofs
consume — `Abstract2.sub-decomp`, `Abstract2.∙-decomp`, `UC.Core.Bridge.shuffle⇒/⇐` —
is already stated at the `μ ∘ T₁` spelling, so naming the generic action would have bought
nothing but the name. `prefixᵒ`'s header comment records this.

**`Certified` is a Σ and not a record.** The natural

```agda
record Certified (A B : ℕ → Channel) : Set₁ where
  field sim : (n : ℕ) → A n ⇒ B n ; cost : ℕ → ℕ ; cost-poly : Poly cost
        sim-qb : (n : ℕ) → QB (cost n) (sim n)
```

**exhausts a 20 GiB heap** — the field `sim-qb`, whose type applies the model's `QB` to two
earlier *fields*, is the trigger; the same type as a standalone definition over two
*parameters* checks in seconds, and so does the record without that field. `UC.Audit`'s
`_≤UC[_]_` record has the same shape and is fine because its `QB` is a module parameter;
here `QB` is `Budget.QB budgetᵒ`, whose transport across the seal cannot be inverted.
The Σ version (`:178`-`:192`, with `sim`/`cost`/`cost-poly`/`sim-qb` as accessors) checks
in 9.4 s. This is a new member of the eta-cliff family the repo already tracks.

**What the relation does NOT read** is the compared homs' own query bounds — only the
context's, exactly as `_≈ᶠ[_]_` did. `PolyQB`/`Imageᶠ` premises appear on the packaging
adapters and nowhere else.

## 2. Rebracketing, and its proved cost

| Name | file:line |
|---|---|
| `≈ctx⇒≈ctxᴬ` | `UC/Asymptotic/Contextual.agda:105` |
| `≈ctxᴬ⇒≈ctx` | `:112` |

The adapter is `UC.Core.Bridge`'s associator shuffle, used once. It transports the query
certificate as well as the observation: the test becomes `E ∘ α⇒` (resp. `E ∘ α⇐`), whose
certificate is `qb-∘ qE qb-a⇐` (resp. `qb-a⇒`) — the structural morphism certifies at
`QB 1`, so the test's budget `c` becomes `c * 1`. The resulting allowance is
`ctxBudget (c * 1) c′`, and `*-identityʳ` is what puts it back at `ctxBudget c c′`; that
`subst` is why the two relations carry the *same* `ε` rather than a rescaled one. No
preservation is inferred from an uncosted isomorphism.

## 3. The presentation map

| Old name | Status |
|---|---|
| `UC.Asymptotic.Family._≈ᶠ[_]_` (`:102`) | **definitional alias** of `imgᶠ B R ≈ctxᴬ[ ε ] imgᶠ B I`. Every existing statement about it typechecks verbatim: `≤UC^ωⁿ-refl/-sym/-trans`, `≈ᶠ-runs`, `admits-inv-pow-2`, `rejects-inv-suc`, `uc-≈ᶠ[_]`, `uc-≤UC^ωⁿ`, `pointwise-exact`, `pointwise-rejects` are unchanged |
| `≈ᶠ⇒≈ℰ[]` (`:155`) | statement unchanged; now the instance of `≈ctxᴬ⇒≈ℰ[]` (`:149`) |
| `UC.Model.Family._≈ℰ[_]_` | **untouched**. `≈ctxᴬ⇒≈ℰ[]` is a NAMED implication into it, not an identification: `_≈ℰ[_]_` quantifies levelwise *families* of contexts carrying one polynomial, the contextual relation quantifies each level's context separately. The packaging premises (`PolyQB` for each side) stay explicit |
| `UC.Approximate.Local._∼ᴺ_`, `UC.Family.Negligible._≤UCᴺ_` | **untouched**. The local-negligible tier is a different relation and is not identified with the uniform one anywhere (plan §3.2) |

## 4. The witness forms

| Name | file:line | content |
|---|---|---|
| `Certified A B` | `Contextual:178` | simulator family + polynomial + `QB` certificate |
| `idᶜ`, `_∘ᶜ_`, `subᶠ` | `:196`, `:199`, `:204` | identity, composition (`qb-∘`/`poly-*`), the levelwise action |
| `_≤UC^ωᵉ_` | `:262` | `Σ[ s ∈ Certified Y X ] Σ[ ε ] NegligibleBound ε × f ≈ctx[ ε ] subᶠ s g` |
| `_≤UC^ωᵉ⁺_` | `:270` | `∀ {X′} (a : Certified X X′) → Σ[ s ] Σ[ ε ] NegligibleBound ε × subᶠ a f ≈ctx[ ε ] subᶠ s g` |
| `≤UC^ωᵉ⇒⁺` | `:280` | `dummy-complete` WITH ITS COST: the schedule becomes `ε n (simCost q (cost a n))` |
| `≤UC^ωᵉ⁺⇒` | `:295` | `≤UC⇒dummy` at the identity adversary; the schedule is untouched |

`_≤UC^ωᵉ⁺_` keeps `Abstract2._≤UC_`'s quantifier order (adversary first, simulator after).
It departs from it in one respect, deliberately: the adversary carries a certificate,
because absorbing it into the test is what `≤UC^ωᵉ⇒⁺` charges. The qualitative order needs
no such thing, and is untouched.

**`_≤UC^ωⁿ_` is the direct-agreement specialization.** `UC.Asymptotic.Family`:

- `≤UC^ωⁿ⇒≤UC^ωᵉ` (`:189`) — unconditional, at `idᶜ`;
- `≤UC^ωᵉ⇒≤UC^ωⁿ` (`:198`) — under the explicit premise
  `(n : ℕ) → subᶠ s (imgᶠ B I) n ≈ imgᶠ B I n`. Direct agreement has nowhere to put a
  simulator, so this premise is the difference between the two, not a defect of the
  implication.

Intended instantiation for a sibling's RO-commitment example: its raw statement — level
`k`, `realᵒ k` against `sub (simᵒ k) ∘ idealᵒ k`, compared at `≈ₚ[ ε k (ctxBudget c c′) ]`,
with the simulator's `≤UC[]ᵍ` certificate and `NegligibleBound ε` as separate components —
is `realᵒ ≈ctx[ ε ] subᶠ s idealᵒ` with `s = (simᵒ , cs , Pcs , qs) : Certified …`, i.e.
exactly the four components of `_≤UC^ωᵉ_`. Nothing about its shape has to change; the
`Certified` packaging is `(sim , cost , poly , qb)` in that order.

## 5. The enrichment kit

| Name | file:line | note |
|---|---|---|
| `≈C⇒≈ctx` | `Contextual:140` | zero error, from the ambient hom equality (`obs-resp` is EXACT at this model) |
| `≈ctx-refl` | `:143` | at the zero schedule |
| `≈ᵁ⇒≈ctx` | `:161` | from the inherited `_≈ᵁ_`, at a chosen POSITIVE schedule |
| `≈ctx-sym` | `:146` | |
| `≈ctx-trans` | `:149` | error addition |
| `≈ctx-≤` | `:155` | domination of SCHEDULES (needs nothing of `ε`) |
| `≈ctx-resp` | `:129` | respect for the ambient hom equality on both sides |
| `≈ctx-sub` | `:215` | context pullback with its cost |

A correction to the plan's wording worth recording: **`≈ctx[0]` does not follow from
`≈ᵁ`.** At this model `_≈ᵁ_`'s observation relation is `∼ᴼ`, closeness at every *positive*
error, which has no zero instance to hand over — the same reason `uc-≈ᶠ[_]` takes a
schedule parameter. Zero error is the ambient hom equality (`≈C⇒≈ctx`), which the model
observes exactly. `≈ᵁ⇒≈ctx` is the `≈ᵁ` entry point, and it costs a positive schedule.

**The context pullback's allowance substitution.** `≈ctx-sub s ε` turns `f ≈ctx[ ε ] g`
into `subᶠ s f ≈ctx[ (λ n q → ε n (simCost q (cost s n))) ] subᶠ s g`. `sub-decomp` slides
`sub (id_W ⊗ s)` off the process and in front of the test; `qb-T₁`/`qb-sub` certify it at
`(cs ⊔ 1) ⊔ 1`, so the test's budget is `c * ((cs ⊔ 1) ⊔ 1)` and

```text
ctxBudget (c * ((cs ⊔ 1) ⊔ 1)) c′ ≡ simCost (ctxBudget c c′) cs
```

is `UC.Budget.ctxBudget-absorb` — an **identity**, not a bound. So no monotonicity is
spent here.

## 6. The composition theorems

`UC/Asymptotic/Compose.agda`.

### Sequential — `≤UC^ωᵉ-trans` (`:56`)

`f ≤UC^ωᵉ g → g ≤UC^ωᵉ h → f ≤UC^ωᵉ h`, following `Abstract2.≤UC-trans` with every `≈ᵁ`
comparison replaced by the kit.

- simulator `s₁ ∘ᶜ s₂`, certificate `qb-∘`, polynomial `poly-*`;
- **allowance substitution:** the second comparison is pulled back along `s₁`, so
  `ε₂` is read at `simCost q (cost s₁ n)`;
- composed schedule `ε₁ n q + ε₂ n (simCost q (cost s₁ n))` — the sum AFTER the
  substitution, negligible by `GradedBound-+[ Negligible ] Negligible-+` on top of
  `NegligibleBound-simCost`;
- no monotonicity premise: every step here substitutes exactly.

### The two plugging congruences

`Abstract2.UC-compose` does two things a relational transitivity does not: it moves a
continuation into the test and an earlier process into the closure. Each is a separate
lemma whose premise is that morphism's own certificate.

| Name | file:line | moved | allowance substitution | extra premise |
|---|---|---|---|---|
| `≈ctx-ext` | `:89` | continuation `k` into the TEST | `q ↦ simCost q (ck n)`, **exact** (`ctxBudget-simCost`) | `QB (ck n) (k n)` |
| `≈ctx-pre` | `:126` | process `f` into the CLOSURE | `q ↦ simCost q (cf n)`, **exact** (`ctxBudget-closure`) | `QB (cf n) (f n)` |

Absorbing into the test multiplies the test's own budget, and
`ctxBudget c c′ = c * (c′ ⊔ 1)` is linear in `c`, so the substitution is an identity.
Absorbing into the closure hits the leg `ctxBudget` *guards*: at the closure's own
`(cf ⊔ 1) * c′` only `≤` holds. `≈ctx-pre` therefore certifies the new closure one step
higher — `qb-mono` always affords it, budgets being upper bounds — and there the guard is
inside and the substitution is exact:

```text
ctxBudget c ((cs ⊔ 1) * (c′ ⊔ 1)) ≡ simCost (ctxBudget c c′) cs   (UC.Budget.ctxBudget-closure)
```

so no theorem here reads `ε` at an inequality of allowances.

### Graded — `UC-composeᵉ` (`:190`)

```text
  (sf : Certified Y X) (εf) → NegligibleBound εf → f ≈ctx[ εf ] subᶠ sf g
→ (t : Certified Q P) (εu) → NegligibleBound εu → u ≈ctx[ εu ] subᶠ t v
→ (cf) → Poly cf → ((n : ℕ) → QB (cf n) (f n))
→ (cv) → Poly cv → ((n : ℕ) → QB (cv n) (v n))
→ (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
```

Construction, step for step against `Abstract2.UC-compose` at the identity adversary:

1. `≈ctx-pre f cf qf εu eu` — `∙-cong-arg`'s step, moving `f` into the closure:
   `(u ∙ᶠ f) ≈ctx[ λ n q → εu n (simCost q (cf n)) ] ((subᶠ t v) ∙ᶠ f)`.
2. `≈ctx-ext (subᶠ t v) ctv qtv εf ef` — `ext-cong`'s step, moving the *simulated*
   continuation into the test, at `ctv n = (cost t n ⊔ 1) * cv n` (its certificate is
   `qb-∘ (qb-sub (sim-qb t n)) (qv n)`, its polynomial `poly-* (poly-⊔ …) Pcv`):
   `((subᶠ t v) ∙ᶠ f) ≈ctx[ λ n q → εf n (simCost q (ctv n)) ] ((subᶠ t v) ∙ᶠ (subᶠ sf g))`.
3. `≈ctx-resp … strict-final` — `UC-compose`'s own `strict-final` chain
   (`sub-commute₂`, `sub-commute₁`, `sub-homomorphism`) levelwise, rewriting the right side
   to `subᶠ s (v ∙ᶠ g)` with `s n = (id ⊗₁ sim t n) ∘ (sim sf n ⊗₁ id)`, certified at
   `(cost t n ⊔ 1) * (cost sf n ⊔ 1)`.
4. `≈ctx-trans` of 1 and 3.

**The two exact allowance substitutions are therefore**

```text
εu  ↦  λ n q → εu n (simCost q (cf n))          -- f into the closure     (exact)
εf  ↦  λ n q → εf n (simCost q ((cost t n ⊔ 1) * cv n))   -- sub t ∘ v into the test (exact)
```

and the conclusion's schedule is their sum. Negligibility is proved AFTER both, by
`NegligibleBound-simCost` (which is `UC.Approximate.GradedBound-reindex` at
`Negligible`, spending only `poly-*`/`poly-⊔`/`poly-const`) and then `GradedBound-+[_]`.

`Abstract2.UC-compose` is untouched and stays unconditional. The raw relation's domain is
untouched too: the certificates are hypotheses of this theorem, never of `_≈ctx[_]_`.

## 7. Reindexing discipline, and the allowance-uniform conclusion

Three reindexing facts are used and all three are proved:

| Fact | where | kind |
|---|---|---|
| `ctxBudget (c * 1) c′ ≡ ctxBudget c c′` | `*-identityʳ`, inline in the rebracketings | identity |
| `ctxBudget (c * ((cs ⊔ 1) ⊔ 1)) c′ ≡ simCost (ctxBudget c c′) cs` | `UC/Budget.agda:107` (`ctxBudget-absorb`) | identity |
| `ctxBudget c ((cs ⊔ 1) * (c′ ⊔ 1)) ≡ simCost (ctxBudget c c′) cs` | `UC/Budget.agda:116` (`ctxBudget-closure`) | identity, after a `qb-mono` bump |

`UC.Approximate.GradedBound-reindex` (`:189`) is the grade-level closure: a bound read at
`r n q` in place of `q` keeps its grade exactly when `r` preserves polynomials. It assumes
nothing about `ε`'s order.

The allowance-uniform conclusion, in `UC/Asymptotic/Family.agda`:

| Name | file:line | content |
|---|---|---|
| `subQB` | `:212` | a certified simulator carries one side's `PolyQB` packaging to the other |
| `certᶠ` | `:221` | a `Certified` IS a `Fam`-hom (`_⇒^ω_`), by its own polynomial certificate |
| `≤UC^ωᵉ⇒≈ℰⁿ` | `:232` | `(f , qf) ≈ℰⁿ (subᶠ s g , subQB s qg)` — ONE schedule, negligible at every polynomial allowance, read by every level's context |
| `≤UC^ωᵉ⇒≈ℰᶠ` | `:240` | the vanishing collapse, `absorb-negl` |
| `≤UC^ωᵉ⇒≤UCᵁ` | `:244` | `(f , qf) ≤UCᵁ (g , qg)`, the INHERITED order, by `dummy-complete` at `certᶠ s` |

The order is the plan's: the quantitative evidence is packaged first and the qualitative
statements are corollaries of it. Nowhere is `∀ context, ∃ negligible ε` traded for
`∀ allowance, ∃ ε, ∀ strategy` — the witness's `ε` is fixed before any context is seen,
and `carried-negligible` merely reads that fixed schedule at the allowance a context
carries.

## 8. Module cost (warm, single `Checking` line, `+RTS -M20G -H2G`)

| Module | LOC | warm before | warm after |
|---|---|---|---|
| `UC.Asymptotic.Family` | 278 → 342 | 15.3 s | 21.0 s |
| `UC.Asymptotic.Contextual` | 298 | — (new) | 9.4 s |
| `UC.Asymptotic.Compose` | 246 | — (new) | 10.6 s |
| `UC.Model.Family` | 31 | 9.4 s | 8.7 s |
| `UC.Family` | 316 | 4.5 s | 4.6 s |
| `UC.Budget` | 73 → 127 | 2.0 s | 2.6 s |
| `UC.Approximate` | 267 → 280 | — | 4.4 s |
| `UC.Audit` | 214 → 190 | — | 4.5 s |

Budget is `60 s + LOC/4`; every row is far inside it. `UC.Asymptotic.Family`'s +5.7 s buys
+64 lines of new content (the two presentation bridges, the two `_≤UC^ωⁿ_` implications and
the five allowance-uniform/forgetting statements); it had no documented header cost before
and none is claimed now. Closure `CategoricalCrypto`: 324.6 s from the state after the
`UC.Budget`/`UC.Approximate` edits (which invalidate the whole cone), 15.7 s incremental
afterwards.

## 9. Root-file wiring the maintainer still needs to do

`UC.Asymptotic.Contextual` is reached from the closure already, through
`UC.Asymptotic.Family` (which `Examples/ChimericLedger/*` import). **`UC.Asymptotic.Compose`
is not imported by anything yet** — it is the module a consumer of the composition
theorems will import. It checks green standalone (10.6 s). Two things to add:

- `src/CategoricalCrypto/UC.agda`'s inventory: rows for `UC.Asymptotic.Contextual` (the
  canonical quantitative relation and the emulation witness) and `UC.Asymptotic.Compose`
  (its composition laws), beside the existing `UC.Asymptotic.Family` row.
- `src/CategoricalCrypto.agda`: an import of `UC.Asymptotic.Compose` if the root index is
  meant to be a full closure, and optionally the two names in its inventory comment.

Checked green, unedited: `src/CategoricalCrypto.agda`, `UC.agda`, `UC/Model.agda`,
`UC/Approximate/LocalTests.agda`, all `Examples/ChimericLedger/*` roots, both
`Examples/HashForward/*`.

## 10. Not delivered

1. ~~**A monotone envelope for `ε`.**~~ RESOLVED 2026-09-21, and no envelope was needed:
   the monotonicity premise itself is gone. A query bound is an UPPER bound, so `qb-mono`
   lets `≈ctx-pre` certify its new closure at `(cf n ⊔ 1) * (c′ ⊔ 1)` instead of
   `(cf n ⊔ 1) * c′`, which puts `ctxBudget`'s guard inside the product and makes the
   allowance substitution an identity (`UC.Budget.ctxBudget-closure`). `Allowance-mono`
   is deleted; `≈ctx-pre` and `UC-composeᵉ` no longer take it.

2. ~~**A packaged `f ≤UC^ωᵉ g → u ≤UC^ωᵉ v → (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)`.**~~ RESOLVED
   2026-09-21 by item 1: the obstacle was stating `Allowance-mono εu` about a schedule
   existentially bound inside `u ≤UC^ωᵉ v`, and there is no such premise any more.
   `≤UC^ωᵉ-∙` is the packaged form, a three-line wrapper over `UC-composeᵉ`. It still
   takes the two moved morphisms' query certificates explicitly — `_≤UC^ωᵉ_` bounds the
   SIMULATOR, not the homs it compares — and `_≤UC^ωᵉ_` gained no fifth component, so
   `≤UC^ωⁿ⇒≤UC^ωᵉ` is unchanged.

3. **Consumer migration (plan step 6).** `ledger-uc-to-pov-family`,
   `ledger-pov-family-negligible`, `ledger-uc-to-pov-simCost`, `ledger-pov-simCost-negligible`
   and `ledger-pov` are unchanged and green; nothing was migrated onto the new witness form.
