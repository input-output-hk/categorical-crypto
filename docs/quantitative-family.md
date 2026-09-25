# The quantitative family layer — steps 3 and 4

What steps 3 and 4 of `docs/uc-presheaf-preservation-plan.md` delivered, on branch
`quantitative-family` off `protocol-rewrite` at `ac8b018f`. Paths are relative to
`src/CategoricalCrypto/` unless prefixed.

Module names in §§1-11 are the CURRENT ones; the `file:line` references in those
sections are the ones that landing recorded and have since drifted. §14 is the
source-backed map at `cee4efca` and is what to read for a current location.

## 1. The relation, and why it is spelled this way

`UC/Quantitative/Family.agda` is the home of the plan's `f ≈ctx[ε] g`; the machine
instance is one module application of it, `UC/Model/Family/Contextual.agda`.

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
consume — `Abstract2.sub-decomp`, `Abstract2.∙-decomp`, and the associator casts
`pullʳ (cancelˡ associator.isoʳ)`/`assoc` that `μ ∘ T₁ ≡ α⇐ ∘ id ⊗₁ _` makes of the
rebracketing — is already stated at the `μ ∘ T₁` spelling, so naming the generic action
would have bought nothing but the name. `prefixᵒ`'s header comment records this.

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
| `≈ctx⇒≈ctxᴬ` | `UC/Quantitative/Family.agda:141` |
| `≈ctxᴬ⇒≈ctx` | `:147` |

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
| `UC.Model.Family.Emulation._≈ᶠ[_]_` (`:88`) | **definitional alias** of `imgᶠ B R ≈ctxᴬ[ ε ] imgᶠ B I`. Every existing statement about it typechecks verbatim: `≤UC^ωⁿ-refl/-sym/-trans`, `≈ᶠ-runs`, `admits-inv-pow-2`, `rejects-inv-suc`, `uc-≈ᶠ[_]`, `uc-≤UC^ωⁿ`, `pointwise-exact`, `pointwise-rejects` typechecked verbatim. Of those only `≈ᶠ-runs` survives the 2026-09-22 retirement (§14) |
| `≈ᶠ⇒≈ℰ[]` (`:155`) | statement unchanged; now the instance of `≈ctxᴬ⇒≈ℰ[]` (`:149`) |
| `UC.Model.Family._≈ℰ[_]_` | **untouched**. `≈ctxᴬ⇒≈ℰ[]` is a NAMED implication into it, not an identification: `_≈ℰ[_]_` quantifies levelwise *families* of contexts carrying one polynomial, the contextual relation quantifies each level's context separately. The packaging premises (`PolyQB` for each side) stay explicit |
| `UC.Approximate.Local._∼ᴺ_`, `UC.Family.Negligible._≤UCᴺ_` | **untouched**. The local-negligible tier is a different relation and is not identified with the uniform one anywhere (plan §3.2) |

## 4. The witness forms

| Name | file:line | content |
|---|---|---|
| `Certified A B` | `Quantitative/Family:206` | simulator family + polynomial + `QB` certificate |
| `idᶜ`, `_∘ᶜ_`, `subᶠ` | `:224`, `:227`, `:237` | identity, composition (`qb-∘`/`poly-*`), the levelwise action |
| `_≤UC^ωᵉ_` | `:290` | `Σ[ s ∈ Certified Y X ] Σ[ ε ] NegligibleBound ε × f ≤UC[ s , ε ] g` (WP2 factored the body out as `_≤UC[_,_]_`, §12.1) |
| `_≤UC^ωᵉ⁺_` | `:304` | `∀ {X′} (a : Certified X X′) → Σ[ s ] Σ[ ε ] NegligibleBound ε × subᶠ a f ≈ctx[ ε ] subᶠ s g` |
| `≤UC^ωᵉ⇒⁺` | `:280` | `dummy-complete` WITH ITS COST: the schedule becomes `ε n (simCost q (cost a n))` |
| `≤UC^ωᵉ⁺⇒` | `:295` | `≤UC⇒dummy` at the identity adversary; the schedule is untouched |

`_≤UC^ωᵉ⁺_` keeps `Abstract2._≤UC_`'s quantifier order (adversary first, simulator after).
It departs from it in one respect, deliberately: the adversary carries a certificate,
because absorbing it into the test is what `≤UC^ωᵉ⇒⁺` charges. The qualitative order needs
no such thing, and is untouched.

**`_≤UC^ωⁿ_` is the direct-agreement specialization.** `UC.Model.Family.Emulation`:

Both directions were RETIRED 2026-09-22 (§14); what they said:

- `≤UC^ωⁿ⇒≤UC^ωᵉ` — unconditional, at `idᶜ`;
- `≤UC^ωᵉ⇒≤UC^ωⁿ` — under the explicit premise
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

`UC/Quantitative/Family.agda`'s `module Compose`, re-exported at
`UC/Model/Family/Contextual/Compose.agda`.

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

The allowance-uniform conclusion, in `UC/Model/Family/Emulation.agda`:

| Name | file:line | content |
|---|---|---|
| `subQB` | `:212` | a certified simulator carries one side's `PolyQB` packaging to the other |
| `certᶠ` | `:221` | a `Certified` IS a `Fam`-hom (`_⇒^ω_`), by its own polynomial certificate |
| `≤UC[]⇒≈ℰⁿ` | `:141` | `(f , qf) ≈ℰⁿ (subᶠ s g , subQB s qg)` — ONE schedule, negligible at every polynomial allowance, read by every level's context. Named `≤UC^ωᵉ⇒≈ℰⁿ` at this landing; renamed by WP2 (§12.2) |
| `≤UC^ωᵉ⇒≈ℰᶠ` | — | the vanishing collapse, `absorb-negl`. RETIRED 2026-09-22 (§14) |
| `≤UC^ωᵉ⇒≤UCᵁ` | — | `(f , qf) ≤UCᵁ (g , qg)`, the INHERITED order, by `dummy-complete` at `certᶠ s`. RETIRED 2026-09-22 (§14) |

The order is the plan's: the quantitative evidence is packaged first and the qualitative
statements are corollaries of it. Nowhere is `∀ context, ∃ negligible ε` traded for
`∀ allowance, ∃ ε, ∀ strategy` — the witness's `ε` is fixed before any context is seen,
and `carried-negligible` merely reads that fixed schedule at the allowance a context
carries.

## 8. Module cost (warm, single `Checking` line, `+RTS -M20G -H2G`)

| Module | LOC | warm before | warm after |
|---|---|---|---|
| `UC.Model.Family.Emulation` (then `UC.Asymptotic.Family`) | 278 → 342 | 15.3 s | 21.0 s |
| `UC.Quantitative.Family` (then `UC.Asymptotic.Contextual`) | 298 | — (new) | 9.4 s |
| its `module Compose` (then `UC.Asymptotic.Compose`) | 246 | — (new) | 10.6 s |
| `UC.Model.Family` | 31 | 9.4 s | 8.7 s |
| `UC.Family` | 316 | 4.5 s | 4.6 s |
| `UC.Budget` | 73 → 127 | 2.0 s | 2.6 s |
| `UC.Approximate` | 267 → 280 | — | 4.4 s |
| `UC.Audit` | 214 → 190 | — | 4.5 s |

Budget is `60 s + LOC/4`; every row is far inside it. The emulation module's +5.7 s buys
+64 lines of new content (the two presentation bridges, the two `_≤UC^ωⁿ_` implications and
the five allowance-uniform/forgetting statements); it had no documented header cost before
and none is claimed now. Closure `CategoricalCrypto`: 324.6 s from the state after the
`UC.Budget`/`UC.Approximate` edits (which invalidate the whole cone), 15.7 s incremental
afterwards.

## 9. Root-file wiring (DONE)

The wiring this section asked for is in the tree: `src/CategoricalCrypto/UC.agda`
carries rows for `UC.Model.Family.Contextual` (`:223`), `UC.Model.Family.Contextual.Compose`
(`:229`) and `UC.Model.Family.Emulation` (`:241`), and opens the latter two publicly
(`:287`, `:288`). `src/CategoricalCrypto.agda` still imports no `Examples/ChimericLedger`
module, deliberately (`docs/consumer-migration.md` §5).

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

3. ~~**The filtered layer as the relation's actual home.**~~ RESOLVED 2026-09-21 on
   branch `filtered-qsetup`; see §11.

4. **Consumer migration (plan step 6).** `ledger-uc-to-pov-family`,
   `ledger-pov-family-negligible` and `ledger-pov` are unchanged and green; nothing was
   migrated onto the new witness form. (`ledger-uc-to-pov-simCost` and
   `ledger-pov-simCost-negligible` stood here too until the budgeted route was retired
   2026-09-21, `docs/end-to-end.md` §4.)

## 11. The relation as a filtered instance (2026-09-21, `filtered-qsetup`)

`Approx/Filtered.agda` and `UC/Quantitative/Query.agda` built a `Filt`-valued test
presheaf that nothing consumed. It is now what the contextual relation *is*.

### 11.1 The generic notion

`Approx.Filtered._≈ᵃ[_]_` — two maps into a filtered space agreeing on the **admitted**
elements, at an error indexed by the allowance:

```agda
record _≈ᵃ[_]_ (u : X.Carrier → Y.Carrier) (Ε : ℕ → Error) (v : X.Carrier → Y.Carrier) where
  field admitted : {q : ℕ} {x : X.Carrier} → X.Admit q x → u x Y.≈[ Ε q ] v x
```

A **record**, not a definition: the two spaces are projections of the unfolded
quantifier, so a use site recovers neither, and the first cut of this as a definition
left every `X`/`Y` meta blocked (`_Y.space.approx._≈[_]__1065`).

The two clauses with content are one field of a filtered map each, and this is the whole
point of the file's "two independent indices":

| | statement | spends |
|---|---|---|
| `≈ᵃ-pre κ` | precomposing reindexes the **allowance** the bound is read at | `Filtered.admits` |
| `≈ᵃ-post k` | postcomposing transforms the **error** by the control | `Controlled.preserves` |

### 11.2 The identification

`UC.Quantitative.Contextual.Agreeᵠ ε r r′` is `_≈ᵃ[_]_` for `filteredᵠ`, at
`λ q c′ → ε (ctxBudget q c′)` — the test's admitted allowance in `ctxBudget`'s first
leg, the closure's own budget in its second, inside `_≈ᵠ[_]_`. It is stated on
test-**pullback maps**, not on one bracket's relation, so both brackets use it:

| relation | its pullback | bridge |
|---|---|---|
| `Contextual._≈ᵁᵠ[ ε ]_` | `runᵠ W f = _∘ id ⊗₁ f` | `ctx⇒agree` / `agree⇒ctx` |
| `Family._≈ctx[ ε ]_` | `_∘ prefixᵒ W (f n)`, levelwise | `≈ctx⇒agreeᵠ` / `agreeᵠ⇒≈ctx` |

**The identification is not definitional, and cannot be made so.** `_≈ᵁᵠ[_]_` takes the
closure `m` *before* the test's certificate (`W E m {c c′} → QB c E → QB c′ m → …`),
where the generic relation must take the admittance first and leaves `m` inside the
schedule-valued `_≈ᵠ[_]_` (`W {q} {E} → QB q E → ∀ m c′ → QB c′ m → …`). Reordering
`_≈ᵁᵠ[_]_` changes `_≈ctxᴬ[_]_` and hence `UC.Model.Family.Emulation._≈ᶠ[_]_`, which every
`Examples/ChimericLedger` consumer applies positionally — rule 1 forbids it. Each bridge
is a one-line curry shuffle.

### 11.3 The two absorptions

```agda
absorb-testᵠ    : QB (cs ⊔ 1) k → (∀ E → s E ≈ r (E ∘ k))     → Agreeᵠ ε r r′
                → Agreeᵠ (λ q → ε (simCost q cs)) s s′
absorb-closureᵠ : QB 1 k → QB (cs ⊔ 1) t → (∀ E → s E ≈ r (E ∘ k) ∘ t) → Agreeᵠ ε r r′
                → Agreeᵠ (λ q → ε (simCost q cs)) s s′
```

- `absorb-testᵠ` = `≈ᵃ-pre (pullᵠ …)`; the allowance map is `_* (cs ⊔ 1)` and
  `Query.absorb-test` (i.e. `ctxBudget-simCost`) is the exact substitution.
- `absorb-closureᵠ` = `≈ᵃ-post (pullᵠ⁺ …)` after `≈ᵃ-pre (pullᵠ …)`. `Query.guardᵠ` is
  new: the identity on tests, `_⊔ 1` on the schedule, legitimate because a budget is an
  upper bound. `pullᵠ⁺ h = composeᶠ (guardᵠ _) (pullᵠ h)`, whose control is therefore
  `reindex (ctxBudget (budget h))` — and *that* is what puts `ctxBudget`'s own guard
  inside the product, so `Query.absorb-closure` applies and the substitution is exact.
  The only inexact step in either is `q * 1 ≡ q` for the structural test leg.

Both `absorb-test` and `absorb-closure` had no consumer before; they are exactly what
the two `≈ᵃ-mono` steps spend.

### 11.4 What became an instance

| name | now |
|---|---|
| `ctx-refl`, `ctx-sym`, `ctx-trans`, `ctx-mono`, `ctx-resp` | `≈ᵃ-refl`/`-sym`/`-trans`/`-mono`/`-resp₀` through the bridge |
| `ctx-absorb` | `absorb-testᵠ` |
| `ctx-sub`, `Family.≈ctx-sub`, `Family.≈ctx-ext` | `ctx-absorb`, unchanged above it |
| `Family.≈ctx-pre` | `absorb-closureᵠ` — lost `qE′`, the `qb-mono` bump in `qm′` and `inner`'s `subst` |
| `Family.≈ctx-dom` | `≈ᵃ-post (pullᵠ …)` at a rate-zero plug — lost `qm′`'s and `inner`'s `subst` |
| `at-trans`, `≤UC^ωᵉ-trans`, `UC-composeᵉ`, `≤UC^ωᵉ-∙`, `≤UC^ωᵉ-sub` | unchanged; they were already assemblies of the above |

Still bespoke on purpose: `Family`'s own congruence kit (`≈ctx-refl`/`-sym`/`-trans`/
`-≤`/`-resp`, `≈C⇒≈ctx`, `≈ᵁ⇒≈ctx`) is one line each at the `prefixᵒ` bracket and
routing it through the bridge is the same length with one more indirection.

### 11.5 The shape that was rejected

One `QUCSetup` over a family base does not close. The presheaf would have to act on
*every* morphism of the base, so the base must be budgeted (`𝒞ᵇ`), and then `run` for
the deliberately UNcertified compared homs has no filtered structure to be the action
of. What works — and is what landed — is: presheaf `Filt`-valued over `𝒞ᵇ`, relation a
plain carrier map quantified over **admitted** tests, filtered structure only on the
certified morphisms a theorem actually moves into a context.

## Consumer and signature inventory (2026-09-23, baseline ba1878ca)

WP0 of `docs/quantitative-theory-consolidation-review-plan.md`: the statements and
the consumer map frozen before any work package edits source. Every signature is
copied verbatim from the tree at `ba1878ca`, `file:line` being that tree's line of
the signature's first token. Paths are relative to `src/CategoricalCrypto/` unless
prefixed. **Callers** lists in-repo use sites only — mentions inside comments are
excluded, and a name used only inside its own defining module is marked so.
**Replacement** is the body the plan's WP1/WP2 intends, or `none` for a leaf.

This section is a FREEZE and is not re-based: names and `file:line` are as of
`ba1878ca`. WP2 renamed `≤UC^ωᵉ⇒≈ℰⁿ`/`≤UC^ωᵉ⇒≤UCᴺ` to `≤UC[]⇒≈ℰⁿ`/`≤UC[]⇒≤UCᴺ`
(§12.2) and `upper-run`/`run-upper` moved to `Protocol.Machine.Agree` (WP3);
§14 is the current map.

### 1. `UC/Audit.agda` — the generic audit-form carry

Everything in this module is generic: the enclosing module takes
`(M : MonoidalCategory o ℓ e) (R : Evaluation …) (bud : Budget M qs) (mass : Mass R)`
(`UC/Audit.agda:49`-`:52`). Nothing below reads the machine model. The one
application is `UC/Seam/Audit.agda:25`-`:31` (`𝔾ᵒ evaluationᵒ budgetᵒ massᵒ`), which
re-exports every name in this section.

#### `AuditEvent` — `UC/Audit.agda:86`

```agda
AuditEvent : (w : Level) (A X B′ : Obj) → Set (o ⊔ ℓ ⊔ suc w)
AuditEvent w A X B′ =
  (Y : Obj) → Test (Y ⊗₀ (X ⊗₀ B′)) → Closure (Y ⊗₀ A) → ℕ → Set w
```

- Content: DATA, not a proposition — which contexts (ancilla `Y`, test, closure) are
  trusted to read the event, and at which budget. Event **selection**, to be kept
  distinct from event **construction** (`UC.Model.EventBounds.Readout`); the plan's
  WP3 instruction 3 forbids asserting an equivalence between the two.
- Callers: `UC/Seam/Audit/Context.agda:154` (`extractᵍ`'s implicit `𝔈`);
  `Examples/HashForward/Audit.agda` through `pinned`/`absorb`.
- Replacement: none (leaf datum).

#### `AuditBound` — `UC/Audit.agda:94`

```agda
AuditBound : {A B′ X : Obj} → A ⇒ X ⊗₀ B′ → AuditEvent w A X B′ → (ℕ → ℚ)
           → Set (o ⊔ ℓ ⊔ qs ⊔ w)
AuditBound {A = A} {B′ = B′} {X = X} f 𝔈 ε =
  (Y : Obj) (Et : Test (Y ⊗₀ (X ⊗₀ B′))) (m : Closure (Y ⊗₀ A)) {c c′ : ℕ}
  → QB c Et → QB c′ m → 𝔈 Y Et m (ctxBudget c c′)
  → (n : ℕ) → at n (obs (tv₁ Y f Et) m) ℚ.≤ ε (ctxBudget c c′)
```

- Contexts: every ancilla object, every test, every closure — restricted by the
  `𝔈 Y Et m (ctxBudget c c′)` membership premise, which is the whole of the
  restriction.
- Certificates: `QB c Et`, `QB c′ m`; the bounded hom `f` carries none.
- Error: one budget-indexed `ε`, read at the CARRIED allowance `ctxBudget c c′` (not
  at a cap). Quantifier order: `ε` before every context; no slack, no polynomial cap.
- Callers: `UC/Seam/Audit/Context.agda:157` (`extractᵍ`);
  `Examples/HashForward/Audit.agda:90`, `:108`.
- Replacement: none — it is the `Bound`/`holds` side of WP1's `ExperimentTransfer`,
  not a thing that theorem replaces.

#### `pinned` / `pinned-bound` — `UC/Audit.agda:105`, `:112`

```agda
pinned : {A B′ X : Obj} → A ⇒ X ⊗₀ B′ → (ℕ → Obs) → AuditEvent ℓs A X B′
pinned f μ Y Et m q = obs (tv₁ Y f Et) m ∼ μ q
```

```agda
pinned-bound : {A B′ X : Obj} (f : A ⇒ X ⊗₀ B′) (μ : ℕ → Obs) (ε : ℕ → ℚ)
               (δ : ℚ) → 0ℚ ℚ.< δ → ((q n : ℕ) → at n (μ q) ℚ.≤ ε q)
             → AuditBound f (pinned f μ) (λ q → ε q ℚ.+ δ)
```

- Event class: a context reads the event when what it observes IS the designated
  `μ q`. Available at any grade; the monitor run of the model's layer 1 is abstracted
  away.
- Error: `ε q + δ`, the `δ` being the `Mass.dominate` price of reading an `∼` as a
  numeric comparison — one-sided only up to a POSITIVE slack. Quantifier: `δ` chosen
  before every context.
- Callers: `Examples/HashForward/Audit.agda:90`, `:94`, `:95`, `:96` (`pinned-bound`
  at `:96` only), `:108`, `:131`, `:138`.
- Replacement: none.

#### `Absorbs` / `absorb` / `absorb-absorbs` — `UC/Audit.agda:133`, `:127`, `:141`

```agda
Absorbs : {A B′ X Y : Obj} (s : Y ⇒ X) (cs : ℕ)
        → AuditEvent w A X B′ → AuditEvent w′ A Y B′ → Set (o ⊔ ℓ ⊔ w ⊔ w′)
Absorbs {A = A} {B′ = B′} {X = X} s cs 𝔈 𝔉 =
  (W : Obj) (Et : Test (W ⊗₀ (X ⊗₀ B′))) (m : Closure (W ⊗₀ A)) (q : ℕ)
  → 𝔈 W Et m q → absorb s cs 𝔉 W Et m q
```

- `absorb s cs 𝔈 W Et m q = 𝔈 W (Et ∘ id ⊗₁ (s ⊗₁ id)) m (simCost q cs)` (`:128`):
  ancilla and closure stay, the simulator goes in front of the test, the budget is
  rescaled by `simCost`.
- This is exactly the plan's `closed : ∀ i → AdmR i → AdmI (absorb i)`.
  `absorb-absorbs` (`:141`) says `absorb s cs 𝔉` is the largest class closed into `𝔉`.
- Callers: `absorb-absorbs` at `Examples/HashForward/Audit.agda:95`; `absorb` at
  `:90`, `:94`, `:108`, `:131`, `:138`. `Absorbs` itself appears only as the type of
  those arguments.
- Replacement: none — WP1 keeps `Absorbs` as the `closed` parameter.

#### `carry-obs` — `UC/Audit.agda:152`

```agda
carry-obs : (f : A ⇒ X ⊗₀ B′) (g : A ⇒ Y ⊗₀ B′) (s : Y ⇒ X) → f ≈ℰ (s ⊗₁ id ∘ g)
          → (W : Obj) (Et : Test (W ⊗₀ (X ⊗₀ B′))) (m : Closure (W ⊗₀ A))
            (δ : ℚ) → 0ℚ ℚ.< δ → (n : ℕ)
          → Σ[ k ∈ ℕ ] at n (obs (tv₁ W f Et) m)
                       ℚ.≤ at k (obs (tv₁ W g (tv₁ W (s ⊗₁ id) Et)) m) ℚ.+ δ
```

- The carry's structural content with no event class and no budget on it: what a
  context observes of the real process is dominated, at `δ`, by what the SAME context
  with the simulator in front of it observes of the ideal one.
- Body: `dominate (∼-trans (em W Et m) (⟦⟧-resp-≈ (∘-resp-≈ˡ (tv₁-∘ …)))) δ δ>0`.
- Callers: `UC/Audit.agda:215` only (inside `audit-carry`).
- Replacement: none — in the plan's scheme it supplies `Near (error i) (real i)
  (ideal (absorb i))` at a constant error.

#### `audit-carryᵉ` — `UC/Audit.agda:172` (WP1's first signature test)

```agda
audit-carryᵉ : (f : A ⇒ X ⊗₀ B′) (g : A ⇒ Y ⊗₀ B′) (s : Y ⇒ X) {cs : ℕ} → QB cs s
             → {𝔈 : AuditEvent w A X B′} {𝔉 : AuditEvent w′ A Y B′}
             → Absorbs s cs 𝔈 𝔉 → (ε δ : ℕ → ℚ)
             → ((W : Obj) (Et : Test (W ⊗₀ (X ⊗₀ B′))) (m : Closure (W ⊗₀ A))
                {c c′ : ℕ} → QB c Et → QB c′ m → (n : ℕ)
                → Σ[ k ∈ ℕ ] at n (obs (tv₁ W f Et) m)
                             ℚ.≤ at k (obs (tv₁ W g (tv₁ W (s ⊗₁ id) Et)) m)
                                 ℚ.+ ε (ctxBudget c c′))
             → AuditBound g 𝔉 δ → AuditBound f 𝔈 (λ q → δ (simCost q cs) ℚ.+ ε q)
```

- Premise relation: NOT a symmetric approximate equality — an unnamed, directed,
  one-sided MASS domination (`near`, the fourth argument), plus the ideal-side
  `AuditBound g 𝔉 δ`. The plan's WP1 forbids strengthening this to a symmetric
  premise.
- Contexts: every `(W, Et, m)` with certificates; admission is `𝔈` on the real side,
  `𝔉` on the ideal side, joined by `Absorbs`.
- Certificates: `QB cs s` on the simulator (essential — the simulator ends up inside
  the environment leg); `QB c Et`, `QB c′ m` on the context legs. `f` and `g` carry
  none. The absorbed test's certificate is built internally as
  `qEt′ = qb-∘ qEt (qb-T₁ (qb-sub qs)) : QB (c * ((cs ⊔ 1) ⊔ 1)) Et′` (`:191`).
- Error and allowance transformation: conclusion `λ q → δ (simCost q cs) + ε q`. The
  two allowances stay visible and different — `ε` at the real context's
  `ctxBudget c c′`, `δ` at the absorbed one, which `ctxBudget-absorb c c′ cs`
  identifies with `simCost (ctxBudget c c′) cs`. The substitution is EXACT
  (`subst`, twice: `:183` and `:195`); no schedule monotonicity is spent.
- Quantifier order: `s` explicit (no simulator existential), `ε δ` fixed before every
  context, no polynomial cap, no positive slack.
- Generic/model split: entirely generic; the instance supplies only `M`, `O`, `bud`,
  `mass`.
- Callers: `UC/Audit.agda:214` (inside `audit-carry`); re-export at
  `UC/Seam/Audit.agda:31`. No other in-repo caller.
- Replacement (WP1): the specialization of the observation-level `ExperimentTransfer.
  preserve` at `MassNear`/`MassUpper`/`mass-carry`, with `absorb` the existing
  simulator absorption, `closed` the supplied `Absorbs`, and the numerical
  normalization left as the existing `ctxBudget-absorb`. Acceptance requires the
  premises and conclusion above unchanged and `Examples/HashForward/Audit.agda` still
  checking.

#### `audit-carry` — `UC/Audit.agda:208`

```agda
audit-carry : (f : A ⇒ X ⊗₀ B′) (g : A ⇒ Y ⊗₀ B′) {cs : ℕ} (em : f ≤UC[ cs ] g)
              {𝔈 : AuditEvent w A X B′} {𝔉 : AuditEvent w′ A Y B′}
            → Absorbs (sim em) cs 𝔈 𝔉
            → (ε : ℕ → ℚ) (δ : ℚ) → 0ℚ ℚ.< δ
            → AuditBound g 𝔉 ε → AuditBound f 𝔈 (λ q → ε (simCost q cs) ℚ.+ δ)
```

- Premise relation: the QUALITATIVE emulation record `_≤UC[_]_` (`:73`) — fields
  `sim : Y ⇒ X`, `sim-qb : QB cs sim`, `emulate : f ≈ℰ (sim ⊗₁ id ∘ g)`.
- Error: `ε (simCost q cs) + δ`. Note the summands swap roles against `audit-carryᵉ`:
  here `δ` is a CONSTANT positive slack (the `dominate` price) and `ε` the schedule.
- Quantifier order: `δ` before every context; simulator carried by the premise, not
  existential at the conclusion.
- Body (`:213`-`:215`): already a specialization of `audit-carryᵉ` at `(λ _ → δ)` and
  `carry-obs`. Plan WP1 instruction 5: preserve it in that form.
- Callers: `Examples/HashForward/Audit.agda:93` (the single consumer of the whole
  carry stack).
- Replacement: keep — it becomes a specialization of the replaced `audit-carryᵉ`.

### 2. `UC/Quantitative/Family.agda` — transport, composition, witness packaging

Generic in `(M, O, Bg, Ap, reflects, obs-resp)` (`:50`-`:60`). `UC/Model/Family/
Contextual.agda:21`-`:23` is the one application; see §3 for what that adds.

#### `_≈ctx[_]_` — `UC/Quantitative/Family.agda:95`

```agda
_≈ctx[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≈ctx[_]_ {A} {X} {B} f ε g =
    (n : ℕ) (W : Channel) (E : T₀ (W ⊗₀ X n) (B n) ⇒ Ω) (m : 𝟙 ⇒ T₀ W (A n))
    {c c′ : ℕ} → QB c E → QB c′ m
  → ⟦ (E ∘ prefixᵒ W (f n)) ∘ m ⟧ ≈[ ε n (ctxBudget c c′) ]
    ⟦ (E ∘ prefixᵒ W (g n)) ∘ m ⟧
```

- Contexts: quantified PER LEVEL — `W`, test and closure are chosen after `n`, not as
  a family carrying one polynomial. That is the uniform refinement the ledger needs;
  `_≈ℰ[_]_` is the coarser family-of-contexts relation and the passage between them
  is a named implication only (§3, `≈ctxᴬ⇒≈ℰ[]`).
- Certificates: the CONTEXT's `QB c E`, `QB c′ m`; the compared homs carry none.
- Error: `ε n (ctxBudget c c′)`, read at the allowance the context's two legs CARRY.
- Callers: `UC/Model/Family/Emulation.agda:127`;
  `Examples/CoinToss/Compose.agda:160`; `Examples/CoinToss/Ideal/Compose.agda:98`.
- Replacement (WP2): stays; WP2 exposes `At s ε f g = f ≈ctx[ ε ] subᶠ s g` over it
  (qualified so as not to clash with `UC.Quantitative.Witness.At`).

#### `_≈ctxᴬ[_]_` and the rebracketing pair — `:104`, `:136`, `:142`

```agda
_≈ctxᴬ[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
f ≈ctxᴬ[ ε ] g = (n : ℕ) → f n ≈ᵁᵠ[ ε n ] g n
```

```agda
≈ctx⇒≈ctxᴬ : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g → f ≈ctxᴬ[ ε ] g
≈ctxᴬ⇒≈ctx : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctxᴬ[ ε ] g → f ≈ctx[ ε ] g
```

- Cost: one structural morphism in front of the test, `QB 1`, so `c ↦ c * 1`; the
  allowance is restored by `*-identityʳ`, hence the SAME `ε` on both sides. Query
  certificates are transported (`qb-∘ qE qb-a⇐` / `qb-a⇒`), not assumed to survive.
- Callers of `≈ctx⇒≈ctxᴬ`: `UC/Model/Family/Emulation.agda:131`;
  `Examples/ChimericLedger/Transfer.agda:171`; internally at `:245`, `:329`, `:356`.
  Callers of `≈ctxᴬ⇒≈ctx`: `Examples/ChimericLedger/Transfer.agda:174`;
  `Examples/CoinToss/Ideal/Receiver/Compose.agda:123`; internally at `:244`, `:327`,
  `:354`. `_≈ctxᴬ[_]_` itself: `UC/Model/Family/Emulation.agda:81` (`_≈ᶠ[_]_`);
  `Examples/CoinToss/Ideal/Receiver/Compose.agda:111`.
- Replacement: none.

#### `≈ctx⇒agreeᵠ` / `agreeᵠ⇒≈ctx` — `:110`, `:115`

```agda
≈ctx⇒agreeᵠ : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g
            → (n : ℕ) (W : Channel)
            → Agreeᵠ (ε n) (_∘ prefixᵒ W (f n)) (_∘ prefixᵒ W (g n))
agreeᵠ⇒≈ctx : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B}
            → ((n : ℕ) (W : Channel)
               → Agreeᵠ (ε n) (_∘ prefixᵒ W (f n)) (_∘ prefixᵒ W (g n)))
            → f ≈ctx[ ε ] g
```

- The identification of `_≈ctx[_]_` with `UC.Quantitative.Contextual.Agreeᵠ` (`UC/Quantitative/Contextual.agda:77` — the
  admitted agreement of two test-pullbacks, `Approx.Filtered`) at the `prefixᵒ`
  bracket. This is the existing structure WP1/WP2 must review before adding another
  contextual-comparison interface.
- Callers: **none outside `UC/Quantitative/Family.agda`**; used internally at `:374`,
  `:377` (`≈ctx-pre`) and `:409`, `:413` (`≈ctx-dom`).
- Replacement: none.

#### `Certified` and `subᶠ` — `:201`, `:232`

```agda
Certified : (A B : ℕ → Channel) → Set (ℓ ⊔ qs)
Certified A B =
  Σ[ s ∈ ((n : ℕ) → A n ⇒ B n) ] Σ[ q ∈ (ℕ → ℕ) ] Poly q × ((n : ℕ) → QB (q n) (s n))
```

```agda
subᶠ : Certified Y X → Homᶠ A Y B → Homᶠ A X B
subᶠ {B = B} s g n = sub (sim s n) {B n} ∘ g n
```

- A Σ, not a record, for the measured eta-cliff reason recorded in §1 of this note.
  Accessors `sim`/`cost`/`cost-poly`/`sim-qb` at `:205`-`:215`; `idᶜ` `:219`,
  `_∘ᶜ_` `:222`, `λ⇒ᶜ` `:228`.
- Callers of `Certified`: `UC/Model/Family/Emulation.agda:109`, `:118`, `:124`;
  `Examples/CoinToss/Compose.agda:152`, `:157`;
  `Examples/CoinToss/Ideal/Compose.agda:66`;
  `Examples/CoinToss/Ideal/Receiver/Compose.agda:89`, `:92`.
  (Distinct from `UC.QueryBound.Certified`, `UC/QueryBound.agda:276`, which is the
  machine-level intrinsic certificate; the two names do not interact.)
- Callers of `subᶠ`: `UC/Model/Family/Emulation.agda:110`, `:127`, `:129`, `:139`;
  `Examples/CoinToss/Compose.agda:160`; `Examples/CoinToss/Ideal/Compose.agda:98`;
  `Examples/ChimericLedger/Transfer.agda:156`; internally at `:242`, `:267`, `:283`,
  `:454`.
- Replacement: none — WP2 builds `At` on top of `Certified`/`subᶠ` unchanged, and
  explicitly forbids repackaging the resource dependencies into a new record.

#### Contextual transport — `≈ctx-sub` `:241`, `≈ctx-ext` `:350`, `≈ctx-pre` `:370`, `≈ctx-dom` `:406`

```agda
≈ctx-sub : (s : Certified Y X) (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A Y B} → f ≈ctx[ ε ] g
         → subᶠ s f ≈ctx[ (λ n q → ε n (simCost q (cost s n))) ] subᶠ s g
```

```agda
≈ctx-ext : (k : Homᶠ B P C) (ck : ℕ → ℕ) → ((n : ℕ) → QB (ck n) (k n))
         → (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g
         → (k ∙ᶠ f) ≈ctx[ (λ n q → ε n (simCost q (ck n))) ] (k ∙ᶠ g)
```

```agda
≈ctx-pre : (f : Homᶠ A X B) (cf : ℕ → ℕ) → ((n : ℕ) → QB (cf n) (f n))
         → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ B P C} → u ≈ctx[ ε ] v
         → (u ∙ᶠ f) ≈ctx[ (λ n q → ε n (simCost q (cf n))) ] (v ∙ᶠ f)
```

```agda
≈ctx-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → QB 0 (p n))
         → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ A X B} → u ≈ctx[ ε ] v
         → (λ n → u n ∘ p n) ≈ctx[ ε ] (λ n → v n ∘ p n)
```

- Allowance transformations, all EXACT (no `≈ctx-≤`, no `Allowance-mono`): simulator
  installation and continuation plugging both reindex by `simCost _ c`; domain
  installation at rate `0` leaves the schedule UNCHANGED (control is `reindex (1 *_)`,
  `*-identityˡ`). These are the three operations WP1's "Resource-sensitive
  comparison" endpoint must account for by one construction; each is already
  `UC.Quantitative.Contextual`'s `ctx-sub`/`ctx-absorb`/`absorb-closureᵠ` plus a
  `pullᵠ` at a rate-zero plug (see §11.4 above).
- Callers: `≈ctx-sub` — `Examples/ChimericLedger/Transfer.agda:173`,
  `Examples/CoinToss/Ideal/Receiver/Compose.agda:123`, internally `:295`.
  `≈ctx-ext` — `Examples/ChimericLedger/Transfer.agda:174`, internally `:454`.
  `≈ctx-pre` — **no caller outside the module**; internally `:452` only.
  `≈ctx-dom` — internally `:428` only (`≤UC^ωᵉ-dom` is the exported form).
- Replacement (WP2): `at-dom` / `at-resp` shapes stated over `At`; the bodies stay.

#### The congruence kit — `≈ctx-resp` `:158`, `≈C⇒≈ctx` `:168`, `≈ctx-refl` `:171`, `≈ctx-sym` `:174`, `≈ctx-trans` `:177`, `≈ctx-≤` `:182`, `≈ᵁ⇒≈ctx` `:187`

```agda
≈ctx-trans : (ε δ : ℕ → ℕ → ℚ) {f g h : Homᶠ A X B} → f ≈ctx[ ε ] g → g ≈ctx[ δ ] h
           → f ≈ctx[ (λ n q → ε n q ℚ.+ δ n q) ] h
```

| name | callers |
|---|---|
| `≈ctx-resp` | `Examples/ChimericLedger/Transfer.agda:172`; `Examples/CoinToss/Ideal/Receiver/Compose.agda:122`; internally `:273`, `:294`, `:306`, `:428`, `:453` |
| `≈C⇒≈ctx` | `Examples/CoinToss/Compose.agda:86`, `:136`; `Examples/CoinToss/Ideal/Compose.agda:75`; `Examples/ROCommitment/Realization/Assembly.agda:86`, `:94` |
| `≈ctx-trans` | no caller outside the module; internally `:452` |
| `≈ctx-refl` | **CONSUMER-FREE** |
| `≈ctx-sym` | **CONSUMER-FREE** |
| `≈ctx-≤` | **CONSUMER-FREE** (nothing in the tree reads a schedule at an inequality) |
| `≈ᵁ⇒≈ctx` | **CONSUMER-FREE** |

- Replacement: none. Per the plan's working rule 5 these are public results of the
  generic layer, not abandoned obligations; the last four are recorded as
  consumer-free so a retirement decision is explicit rather than inferred.

#### `NegligibleBound-simCost` — `:250`

```agda
NegligibleBound-simCost : (cs : ℕ → ℕ) → Poly cs → (ε : ℕ → ℕ → ℚ)
                        → NegligibleBound ε
                        → NegligibleBound (λ n q → ε n (simCost q (cs n)))
```

- Callers: `Examples/ChimericLedger/Transfer.agda:169`, `:170`; internally `:293`,
  `:326`, `:450`, `:451`.
- Replacement (WP2): the second half of `seqError-negligible` /
  `composeError-negligible`; its own body is unchanged.

#### `_≤UC^ωᵉ_` — `:265`

```agda
_≤UC^ωᵉ_ : Homᶠ A X B → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≤UC^ωᵉ_ {X = X} {Y = Y} f g =
  Σ[ s ∈ Certified Y X ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × f ≈ctx[ ε ] subᶠ s g
```

- Quantifier order: simulator first, then ONE schedule for all levels and all
  allowances, then negligibility, then the contextual agreement. The polynomial cap
  lives inside `NegligibleBound` and is quantified after the schedule; no slack.
- Callers: `Examples/ROCommitment/Realization/Statement.agda:51`, `:52`, `:58`, `:59`;
  `Examples/CoinToss/Compose.agda:81`, `:82`, `:131`, `:132`, `:102`, `:140`, `:161`;
  `Examples/CoinToss/Ideal/Compose.agda:74`, `:77`, `:78`, `:91`, `:99`, `:124`;
  `Examples/CoinToss/Ideal/Receiver/Compose.agda:119`, `:128`, `:129`, `:140`, `:166`;
  `Examples/ROCommitment/Realization/Assembly.agda:82`, `:90`.
- `≤UC^ωᵉ-resp` (`:269`) callers: `Examples/ROCommitment/Realization/Assembly.agda:103`,
  `:108`.
- Replacement (WP2 instruction 8): retire the notation after migrating consumers to
  the explicit-data `At`, or retain as a convenience bundle if a caller genuinely
  needs the witness hidden. Every caller above is a migration target.

#### `_≤UC^ωᵉ⁺_`, `≤UC^ωᵉ⇒⁺`, `≤UC^ωᵉ⁺⇒` — `:279`, `:289`, `:303`

```agda
_≤UC^ωᵉ⁺_ : Homᶠ A X B → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≤UC^ωᵉ⁺_ {X = X} {Y = Y} f g =
    {X′ : ℕ → Channel} (a : Certified X X′)
  → Σ[ s ∈ Certified Y X′ ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ]
      NegligibleBound ε × subᶠ a f ≈ctx[ ε ] subᶠ s g
```

- The adversary-quantified form at `Abstract2._≤UC_`'s quantifier order; the adversary
  carries a certificate because absorbing it costs `simCost _ (cost a n)`.
- `≤UC^ωᵉ⇒⁺` and `≤UC^ωᵉ⁺⇒` are both **CONSUMER-FREE**, and so is the relation
  `_≤UC^ωᵉ⁺_` itself.
- Replacement: none.

#### `≤UC^ωᵉ-trans`, `≤UC^ωᵉ-dom`, `UC-composeᵉ`, `≤UC^ωᵉ-∙` (module `Compose`, `:315`)

```agda
≤UC^ωᵉ-trans : {f : Homᶠ A X B} {g : Homᶠ A Y B} {h : Homᶠ A Z B}
             → f ≤UC^ωᵉ g → g ≤UC^ωᵉ h → f ≤UC^ωᵉ h
```
`:320`. Simulator `s₁ ∘ᶜ s₂`; schedule `λ n q → ε₁ n q + ε₂ n (simCost q (cost s₁ n))`
— the second comparison is pulled back along the FIRST simulator. Callers:
`Examples/CoinToss/Ideal/Compose.agda:80`;
`Examples/CoinToss/Ideal/Receiver/Compose.agda:131`;
`Examples/ROCommitment/Realization/Assembly.agda:103`, `:108`.

```agda
≤UC^ωᵉ-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → QB 0 (p n))
           → {f : Homᶠ A X B} {g : Homᶠ A Y B} → f ≤UC^ωᵉ g
           → (λ n → f n ∘ p n) ≤UC^ωᵉ (λ n → g n ∘ p n)
```
`:424`. Simulator and schedule UNTOUCHED. Callers:
`Examples/CoinToss/Ideal/Compose.agda:80`;
`Examples/CoinToss/Ideal/Receiver/Compose.agda:131`.

```agda
UC-composeᵉ :
    {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
    (sf : Certified Y X) (εf : ℕ → ℕ → ℚ) → NegligibleBound εf
  → f ≈ctx[ εf ] subᶠ sf g
  → (t : Certified Q P) (εu : ℕ → ℕ → ℚ) → NegligibleBound εu
  → u ≈ctx[ εu ] subᶠ t v
  → (cf : ℕ → ℕ) → Poly cf → ((n : ℕ) → QB (cf n) (f n))
  → (cv : ℕ → ℕ) → Poly cv → ((n : ℕ) → QB (cv n) (v n))
  → (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
```
`:437` — this IS the graded-composition theorem; there is no other name for it.
- Simulator built at `:469`-`:473`:
  `λ n → id {X n} ⊗₁ sim t n ∘ sim sf n ⊗₁ id {Q n}` at cost
  `(cost t n ⊔ 1) * (cost sf n ⊔ 1)`.
- Schedule: `λ n q → εu n (simCost q (cf n)) + εf n (simCost q ((cost t n ⊔ 1) * cv n))`.
- Extra hypotheses are exactly the certificates for the two morphisms it MOVES: `f`
  into the closure, `v` (with `t` in front) into the test.
- Callers: `Examples/CoinToss/Compose.agda:84`, `:134`;
  `Examples/ROCommitment/Realization/Assembly.agda:84`, `:92`.

```agda
≤UC^ωᵉ-∙ : {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
           (cf : ℕ → ℕ) → Poly cf → ((n : ℕ) → QB (cf n) (f n))
         → (cv : ℕ → ℕ) → Poly cv → ((n : ℕ) → QB (cv n) (v n))
         → f ≤UC^ωᵉ g → u ≤UC^ωᵉ v → (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
```
`:498`. The packaged form of `UC-composeᵉ`. **CONSUMER-FREE** — every caller uses
`UC-composeᵉ` directly. (The plan's list of six consumer-free lemmas does not include
this one; recorded here as a seventh, with `_≤UC^ωᵉ⁺_` an eighth.)

- Replacement (WP2): `at-trans` + `seqError`/`seqError-negligible` for
  `≤UC^ωᵉ-trans`; `at-compose` + `composeSim`/`composeError`/`composeError-negligible`
  for `UC-composeᵉ`, with the schedule projection pinned by `refl`. The existing
  witness theorems become packaging of the new ones while callers migrate.

### 3. `UC/Model/Family/{Contextual,Contextual/Compose,Emulation}.agda` — the machine instance

#### What `Contextual` and `Contextual.Compose` add

`UC/Model/Family/Contextual.agda:21`-`:23` is one module application and nothing else:

```agda
open import CategoricalCrypto.UC.Quantitative.Family
  𝔾ᵒ qevaluationᵒ budgetᵒ (ApproxSpace.∼ᵃ-isEquivalence Qr.X) (zero⇒positive Qr.X)
  (λ h → h) public
```

The model-specific input is `UC.Model.Observation.qevaluationᵒ`, whose `eval₀` reads
the seal's hom equality EXACTLY — the zero-error input the generic module asks for.
Its qualitative readout is `Approx.Evaluation.qual₊`, so `_∼_` already IS closeness at
every positive error and `reflects` is the IDENTITY; the coarsening arguments are
spelled exactly as `qual₊` spells them, which is what makes the readout landed at
`evaluationᵒ` itself. No new theorem, no
new quantifier. `UC/Model/Family/Contextual/Compose.agda:13` is `open Compose public`
and adds nothing at all. Both are candidates for the plan's rule-19 scrutiny only if
a WP retires the generic/instance split.

#### `Systems`, `imgᶠ`, `_≈ᶠ[_]_`, `_≤UC^ωⁿ_`

```agda
Systems : (ℕ → Iface) → Set₁                               -- Emulation.agda:58
Systems B = (n : ℕ) → Protocol unitᴵ (B n)

imgᶠ : (B : ℕ → Iface) (R : Systems B) (n : ℕ) → 𝟘ᵒ ⇒ gradedᶠ B n   -- :72
imgᶠ B R n = Gr.closedᵒ (morphism (R n))

_≈ᶠ[_]_ : Systems B → (ℕ → ℕ → ℚ) → Systems B → Set₁        -- :80
_≈ᶠ[_]_ {B} R ε I = imgᶠ B R ≈ctxᴬ[ ε ] imgᶠ B I

_≤UC^ωⁿ_ : Systems B → Systems B → Set₁                     -- :87
R ≤UC^ωⁿ I = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × R ≈ᶠ[ ε ] I
```

- Systems compared: CLOSED protocol images at the TRIVIAL grade
  (`gradedᶠ B = Δ Gr.𝟘ᴳ ⊛ω ifaceᶠ B`, `:69`). No simulator is retained by `_≤UC^ωⁿ_` —
  there is none to retain at the trivial grade.
- Quantifier order: one schedule, negligible at every polynomial allowance, then the
  per-level contextual agreement.
- Callers: `Systems` — `Examples/ChimericLedger/{Property.agda:126,:149,:155,:178;
  Transfer.agda:91,:119,:124,:131,:137,:155,:165,:183,:210,:220,:235,:271,:277,:289;
  ReplayFamily.agda:53}`. `imgᶠ` — `Examples/ChimericLedger/Transfer.agda:156`, `:157`.
  `_≈ᶠ[_]_` — only inside `_≤UC^ωⁿ_` and `≈ᶠ-runs`. `_≤UC^ωⁿ_` —
  `Examples/ChimericLedger/Transfer.agda:92`, `:165`, `:166`, `:183`, `:221`, `:236`.
- Replacement: none.

#### `≤UC^ωᵉ⇒≤UCᴺ` — `Emulation.agda:137` (in the `module _` opened at `:124`)

```agda
module _ {A X Y B : Obj^ω} (s : Certified Y X) (ε : ℕ → ℕ → ℚ)
         (neg : NegligibleBound ε) {f : Homᶠ A X B} {g : Homᶠ A Y B}
         (qf : PolyQB {A} {X ⊛ω B} f) (qg : PolyQB {A} {Y ⊛ω B} g)
         (e : f ≈ctx[ ε ] subᶠ s g) where

  ≤UC^ωᵉ⇒≈ℰⁿ : _≈ℰⁿ_ {A} {X ⊛ω B} (f , qf) (subᶠ s g , subQB s qg)

  ≤UC^ωᵉ⇒≤UCᴺ : Cᴺ._≤UC_ (f , qf) (g , qg)
```

- Premise: FIXED simulator data `s`, a fixed schedule `ε` with its negligibility, the
  two compared families' `PolyQB` certificates, and the contextual comparison. Already
  the fixed-data shape WP2 instruction 6 asks for; what is missing is only that the
  public entry point be stated over `At`.
- Route: stops at `_≈ℰⁿ_` and is read in `ucSetupᴺ`'s own kernel
  (`UC.Family.Negligible.Setup.rel-agree`); it does NOT go through vanishing and
  spends no `absorb-negl`. The canonical negligible order retains a certified
  simulator family and context-local negligible witnesses; it does not re-expose the
  single global schedule (the plan's WP2 "Review point").
- Quantifier order: simulator, schedule, negligibility, caps — all before the
  conclusion; no slack.
- Generic/model split: `≈ctxᴬ⇒≈ℰ[]` (`:100`), `subQB` (`:109`), `certᶠ` (`:118`) are
  the model-side plumbing (`PolyQB`, `_⇒^ω_`, `qb-∘`/`qb-sub`, `poly-*`/`poly-⊔`);
  the mathematical content is the generic `≈ctx⇒≈ctxᴬ`.
- Callers: `Examples/CoinToss/Ideal/Compose.agda:129`;
  `Examples/CoinToss/Ideal/Receiver/Compose.agda:171`. `≤UC^ωᵉ⇒≈ℰⁿ`, `subQB`, `certᶠ`,
  `≈ctxᴬ⇒≈ℰ[]`, `gradedᶠ` have no caller outside `Emulation.agda`.
- Replacement (WP2): become `at⇒canonical-negligible s ε qf qg neg h`, with the
  implementation moved to the chosen public entry point and the forwarding alias
  removed once callers migrate.

#### `≈ᶠ-runs` — `Emulation.agda:149`

```agda
≈ᶠ-runs : (ε : ℕ → ℕ → ℚ) → R ≈ᶠ[ ε ] I
        → (n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
        → runᴹ (morphism (R n)) d ≈ₚ[ ε n q ] runᴹ (morphism (I n)) d
```

- Reads the contextual `ε` back OUT at the EMBEDDED-STRATEGY contexts of
  `UC.Seam.Audit.Context`: an embedded strategy behind the two unitors that kill the
  grade and the ancilla, budget `ctxBudget q 1 = q * 1` (hence the `*-identityʳ`
  `subst`), observation `audit-run`.
- Allowance: `ε n q`, exactly the strategy's own ask-depth. No exact agreement
  anywhere in the route.
- Callers: `Examples/ChimericLedger/Transfer.agda:97`.
- Replacement: none — WP3's `comparison-at-watched-strategy` in the plan's schematic
  ledger body stands for this plus the watch-budget proof; it is not a new premise.

### 4. `Examples/ChimericLedger` — the concrete consumer

#### `Property.PreservesValue` — `Property.agda:149`

```agda
PreservesValue : Systems LedgerIf^ω → Set₁
PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴹ
```

with `εᴹ n q = εᴸ n (q ℕ.+ 1)` (`:107`) and
`εᴸ n q = fromℕ (q * q + q) * inv-pow-2 n` (`:85`), i.e. the birthday bound at hash
width `n`. `auditMonitorᶠ n = monitorᴹ (Watched.reportsLoss n (genesisAt n))` (`:142`).
- Unfolded (`UC.Model.EventBounds.Boundedᴺ`): `(p : ℕ → ℕ) → Poly p → Σ[ ν ] Negligible ν
  × ((n : ℕ) → BoundedAt (p n) (εᴹ n (p n) + ν n) (morphism (R n)) (readoutᴹ …))`.
  Cap first, slack after the cap and before the level.
- The headline reads the COMPILED observable event, not hidden-state conservation.
- Callers: `Property.agda:178`, `:194`; `Transfer.agda:92`, `:184`, `:292`, `:312`,
  `:350`; `ReplayFamily.agda:71`; `Serialize.agda:48`.
- Replacement: none — WP3 instruction 5 requires its cap and slack quantifiers
  unchanged.

#### `hitsᴸ` — `Property.agda:155`

```agda
hitsᴸ : (R : Systems LedgerIf^ω) (n q : ℕ) {r : ℚ}
      → ((d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ (q ℕ.+ 1) d
         → Upper (runᴹ (morphism (R n)) (auditWatch n d)) r)
      → HitsAt q r (morphism (R n)) (auditMonitorᶠ n)
```

- `hitsᵘ` at the ledger's report/watch pair. The `q + 1` is the monitor accumulator's
  unit (see §7). Callers: `Transfer.agda:96`, `:294`; `Property.agda:170`.

#### `ledger-hitsᵘ` — `Property.agda:165`

```agda
ledger-hitsᵘ : (n : ℕ) (vr : Variant) {ε : ℕ → ℚ}
             → Bounded (AtLevel.Sys n vr (genesisAt n)) (auditWatch n) ε → (q : ℕ)
             → HitsAt q (ε (q ℕ.+ 1)) (morphism (AtLevel.Sys n vr (genesisAt n)))
                        (auditMonitorᶠ n)
```
Callers: `Property.agda:196`.

#### `preservesValue⇒saturated` — `Property.agda:177`

```agda
preservesValue⇒saturated :
    (R : Systems LedgerIf^ω) → PreservesValue R → (p : ℕ → ℕ) → Poly p
  → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν
    × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ (p n) d
       → Pr (R n) (auditWatch n d) ℚ.≤ εᴹ n (p n) ℚ.+ ν n)
```

- The way back, at the context an ordinary strategy embeds to. Nothing is spent
  returning — the extra query was charged going out (`hits⇒bounded`).
- Callers: `ReplayFamily.agda:73`; `Transfer.agda:226`.

#### `ideal-preserves-value` — `Property.agda:194`

```agda
ideal-preserves-value : SerInj → PreservesValue Ideal
```
Assumes only `SerInj` (per-level injectivity of `ser`); proved from
`ideal-bounded` (the birthday theorem through the watch, `:190`) by
`hitsᶠ⇒hitsᴺ ∘ ledger-hitsᵘ`. Callers: `Serialize.agda:49`.

#### `preserves-value-transfer` — `Transfer.agda:91`

```agda
preserves-value-transfer : (a V : ℕ) (R : Systems LedgerIf^ω) → SerInj
                         → R ≤UC^ωⁿ Ideal a V → PreservesValue a V R
```

- Premise relation: `_≤UC^ωⁿ_` — allowance-uniform emulation with negligible error at
  the CLOSED protocol images, no simulator.
- Contexts / adversary class: the ideal side is read at the embedded-strategy
  contexts, the conclusion at every certified machine context the cap admits.
- Certificates: none on `R`; the compiled test's certificate is deliberately NOT
  read — the flag is an internal port, so a strategy extracted from the compiled
  context can spend only the honest allowance.
- Error and allowance: the comparison and the ideal bound are BOTH read at `p n + 1`;
  the premise's `ε` becomes the saturated slack `λ n → ε n (p n + 1)`, quantified
  after the allowance, so the conclusion's own number is the ideal `εᴹ`. Both
  allowances are exact; no schedule monotonicity is spent.
- Quantifier order: `(p, Poly p)` first, then slack, then level, then context.
- Callers: `Transfer.agda:186` (`ledger-preserves-value-from-hash`), `:227`
  (`ledger-uc-to-pov-family`).
- Replacement (WP3, schematic): the plan's `preserves-value-transfer` body with
  `comparison-at-watched-strategy` = `≈ᶠ-runs` + `auditWatch-preserving` and
  `ideal-watched-upper-bound` = `upper-run` + `ideal-bounded`; a WP1 specialization
  may replace the bound transport, and the operational lift and its `q + 1` stay
  explicit.

#### `hash-liftⁿ` — `Transfer.agda:165` (in `module _ (vr : Variant) (s : (n : ℕ) → Ledger.LState n)`)

```agda
hash-liftⁿ : (hash : Systems HashIf^ω) → hash ≤UC^ωⁿ oracle^ω
           → Realᴴ hash vr s ≤UC^ωⁿ Realᴴ oracle^ω vr s
```

- Route: `≈ctx-ext` absorbs the ledger stage into the test at its own budget
  (`ledgerᶠ-qb : QB 1`, one hash call per transaction plus the `stageᵒ` regrading),
  `≈ctx-sub` the unit regrading `λ⇒ᶜ` (also `QB 1`), and `ledger-factor` reads both
  sides back as the closed systems `_≤UC^ωⁿ_` compares.
- Allowance: `εᴴ n q = ε n (simCost (simCost q 1) 1)` (`:176`-`:178`), two exact
  `simCost` reindexings. With one upper stage there is no simulator to compose.
- Callers: `Transfer.agda:187`.
- Replacement (WP2 instruction 7): migrate to the `At` bound lemmas, keeping the
  public hypothesis and the schedule pin intact.

#### `ledger-preserves-value-from-hash` — `Transfer.agda:182`

```agda
ledger-preserves-value-from-hash :
    (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≤UC^ωⁿ oracle^ω
  → PreservesValue a V (Realᴴ hash inputConsuming (genesisAt a V))
```
No in-repo caller (it is a public headline). Replacement: none.

#### The trajectory conclusion — `Transfer.agda:219` and `:234`

```agda
ledger-uc-to-pov-family :
    SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool)
  → R ≤UC^ωⁿ Ideal a V → TruthfulAudit R badR → (p : ℕ → ℕ) → Poly p
  → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν
    × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ (p n) d
       → PrHit (R n) (badR n) d ℚ.≤ εᴹ n (p n ℕ.+ p n) ℚ.+ ν n)
```

```agda
ledger-pov-family-negligible :
    SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool)
  → R ≤UC^ωⁿ Ideal a V → TruthfulAudit R badR
  → (p : ℕ → ℕ) → Poly p
  → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
    × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
       → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
```

- **CURRENT schedule: `εᴹ n (p n + p n)`, that is `εᴸ n (q + q + 1)`.** The doubling
  is `Watched.withAudits`' — the honest interface's instrumentation, which makes the
  watch see every boundary the trajectory inspects — and the `+ 1` inside `εᴹ` is the
  monitor accumulator's. This is the maintainer's ruling of **2026-09-22**, taken when
  the strategy-level route was retired: the appendix now reads claim 1's contextual
  bound back at the embedded strategies (`preservesValue⇒saturated`) instead of
  proving a second transfer. An older document's sharper strategy-level statement is
  **not** the public type; do not treat the plan's "trajectory conclusion" as the
  older number.
- Extra premise: `TruthfulAudit R badR` (`:210`) — UC identifies no internal state
  trajectory, so the bound comes back only from the implementation's own audit
  truthfulness. `ideal-truthful` (`:215`) discharges it for the ideal family.
- Quantifier order: cap `(p, Poly p)` first, then slack, then level, then strategy.
- Callers: `ledger-uc-to-pov-family` at `Transfer.agda:242`;
  `ledger-pov-family-negligible` has no in-repo caller (public headline).
- Replacement: none. WP3 instruction 6 protects it from being weakened, and WP6 check
  1 requires the truthfulness premise stay visible.

#### `ReplayFamily.chimeric-not-preserving` — `ReplayFamily.agda:71`

```agda
chimeric-not-preserving : ¬ PreservesValue a (suc (suc V)) (Chimericᶠ V)
```

- The negative side: three queries at every level (`λ _ → 3`, `poly-const 3`),
  probability one at every level (`chimeric-loses-value^ω`), so no negligible slack
  over a polynomial allowance can cover it. The allowance is quantified FIRST, as the
  property quantifies it; no single security parameter is picked.
- It is not a refutation at the positive theorem's INITIALIZATION: `Chimericᶠ` starts
  account-funded, `Property.Ideal` at the UTxO genesis; `funded-total` is the
  equal-total side condition that lets one watch serve both.
- No in-repo caller. Replacement: none.

### 5. The resource-installed commitment/coin assembly and its schedule pins

#### `Realization/Statement.agda`

```agda
Rcom : Homᶠ (λ _ → 𝟘ᵒ) Advᶠ Honᶠ          -- :34
Rcom n = realᶠ n ∘ resᶠ n
Icom : Homᶠ (λ _ → 𝟘ᵒ) Lkᶠ Honᶠ           -- :37
Icom n = idealᶠ n ∘ resᶠ n

Realization Realizationʰ : Set _           -- :50
Realization  = Rcom  ≤UC^ωᵉ Icom
Realizationʰ = Rcomʰ ≤UC^ωᵉ Icomʰ

Assembly Assemblyʰ : Set _                 -- :57
Assembly  = Realization  → (λ n → (tossᶠ  ∙ᶠ realᶠ)  n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
Assemblyʰ = Realizationʰ → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
```

- The resource-installed boundary: `Examples.ROCommitment.Resource.resource` below
  both sides, hence CLOSED in the domain and still graded by the corrupted party's
  port. `Rcomʰ`/`Icomʰ` (`:41`, `:44`) are the corrupted-receiver twins.
- `Realization`/`Realizationʰ` are ASSUMPTIONS, not theorems: the game bound behind
  them (`Examples.ROCommitment.Game.extraction-bound`) is proved against one lazily
  sampled oracle and one-shot cell, and the machine-level bridge is blocked (see
  "Decisions recorded"). WP6 check 5: this is not a full machine realization.
- Callers: `Realization` at `Assembly.agda:82`, `:111`; `Realizationʰ` at `:90`,
  `:114`; `Assembly`/`Assemblyʰ` at `:101`, `:106`.

#### `Realization/Assembly.agda`

```agda
coin-from-Rcom : Realization → (tossᶠ ∙ᶠ Rcom) ≤UC^ωᵉ (tossᶠ ∙ᶠ Icom)   -- :82
coin-from-Rcomʰ : Realizationʰ → (tossʰᶠ ∙ᶠ Rcomʰ) ≤UC^ωᵉ (tossʰᶠ ∙ᶠ Icomʰ)  -- :90

assembly : Assembly                                                     -- :101
assembly w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-resp (λ _ → sym-assoc) (λ _ → sym-assoc) (coin-from-Rcom w))
               coin-hybridᵉ

pin : (w : Realization) → proj₁ (proj₂ (assembly w)) ≡ εᶜⁱ (proj₁ (proj₂ w))   -- :111
pin _ = refl
pinʰ : (w : Realizationʰ) → proj₁ (proj₂ (assemblyʰ w)) ≡ εᶜʳ (proj₁ (proj₂ w)) -- :114
pinʰ _ = refl
```

- `coin-from-Rcom` is `UC-composeᵉ` with the upper stage compared with ITSELF (`idᶜ`
  at the zero schedule) and the two moved morphisms now CLOSED: `(λ _ → 0)
  (poly-const 0) RcomQB` and `(λ _ → 0) (poly-const 0) CTU.tossQB`. Its
  corrupted-receiver twin uses `(λ _ → 1) (poly-const 1) CTHU.tossʰQB`.
- `≤UC^ωᵉ-dom` is NOT spent here — the premise is closed already; the associativity
  gap is repaired by `≤UC^ωᵉ-resp`, which keeps the SAME simulator and schedule.
- The two pins are `refl`: moving the boundary changes no number.
- Certificates: `RcomQB`/`RcomʰQB : QB 0` (`:56`, `:59`) from the resource's `QB 0`
  swallowing the product; `RcomPolyQB`/`IcomPolyQB`/`RcomʰPolyQB`/`IcomʰPolyQB` all
  `(λ _ → 0) , poly-const 0 , …` (`:62`-`:74`). `RcomPolyQB`, `IcomPolyQB`,
  `RcomʰPolyQB`, `IcomʰPolyQB` have **no in-repo caller**.
- Replacement: none for the pins; `UC-composeᵉ` under them is a WP2 migration target,
  and the pins are the regression that will catch a schedule change.

#### `Examples/CoinToss/Compose.agda` (the open-premise first hop)

```agda
coin-toss-from-com : realᶠ ≤UC^ωᵉ idealᶠ
                   → (tossᶠ ∙ᶠ realᶠ) ≤UC^ωᵉ (tossᶠ ∙ᶠ idealᶠ)          -- :81
εᶜᵗ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ                                           -- :97
εᶜᵗ ε n q = 0ℚ ℚ.+ ε n (simCost q 0)
schedule-pin : (w : realᶠ ≤UC^ωᵉ idealᶠ)
             → proj₁ (proj₂ (coin-toss-from-com w)) ≡ εᶜᵗ (proj₁ (proj₂ w))  -- :102
composed-ε : (n q : ℕ) → εᶜᵗ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n   -- :167
```
plus the corrupted-receiver twins `coin-toss-from-comʰ` (`:131`), `schedule-pinʰ`
(`:140`), and the narrowed premises `comSim : Certified Lkᶠ Advᶠ` at cost 2 (`:152`),
`comSimʰ` at cost 1 (`:157`), `coin-toss-from-comᶜ` (`:160`).
Callers: `coin-toss-from-com` — `CoinToss/Ideal/Compose.agda:80`;
`coin-toss-from-comʰ` — `CoinToss/Ideal/Receiver/Compose.agda:131`;
`εᶜᵗ` — `Ideal/Compose.agda:89`, `Ideal/Receiver/Compose.agda:136`.

#### `Examples/CoinToss/Ideal/Compose.agda` (corrupted committer)

```agda
coin-hybridᵉ : (λ n → (tossᶠ ∙ᶠ idealᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ        -- :74
coin-hybridᵉ = simᶜᶠ , (λ _ _ → 0ℚ) , (λ _ _ → Negligible-0) , ≈C⇒≈ctx CTIU.coin-hop

coin-toss-ideal : realᶠ ≤UC^ωᵉ idealᶠ
                → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ     -- :77
coin-toss-ideal w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-dom resᶠ CTIU.resourceQBᵒ (coin-toss-from-com w)) coin-hybridᵉ

εᶜⁱ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ                                           -- :88
εᶜⁱ ε n q = εᶜᵗ ε n q ℚ.+ 0ℚ
schedule-pinⁱ : (w : realᶠ ≤UC^ωᵉ idealᶠ)
              → proj₁ (proj₂ (coin-toss-ideal w)) ≡ εᶜⁱ (proj₁ (proj₂ w))  -- :91

coin-toss-idealᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ
                 → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ    -- :98
ideal-ε : (n q : ℕ) → εᶜⁱ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n  -- :102
```

- Second hop EXACT (zero schedule): `Ideal.Machine` is the machine equality,
  `CTIU.coin-hop` reads it across the seal. The whole error is the first hop's, itself
  the commitment's, unrescaled. Simulator `simᶜᶠ : Certified Lkᶜᶠ (Lkᶠ ⊗ᶠ Advᶜᶠ)` at
  cost 1 (`:66`).
- `≤UC^ωᵉ-dom` at the resource is FREE (rate `0`, schedule unchanged) and is what
  closes the comparison boundary — required, because at an open domain
  `_≈ctx[_]_`'s closure quantifier owns `F_com`'s memory.
- The `≤UC^ωᵉ⇒≤UCᴺ` use: `coin-toss-idealᴺ` (`:123`), with `coinRealQB`/`FcoinQB` both
  `(λ _ → 0) , poly-const 0 , …` (`:112`, `:115`).
- Callers: `coin-hybridᵉ` — `Realization/Assembly.agda:104`; `εᶜⁱ` —
  `Realization/Assembly.agda:111`, `Examples/CoinToss/Test.agda:76`; `ideal-ε` —
  `Test.agda:54`. `coin-toss-ideal`, `coin-toss-idealᶜ`, `coin-toss-idealᴺ`,
  `schedule-pinⁱ` have no in-repo caller (public headlines and regressions).

#### `Examples/CoinToss/Ideal/Receiver/Compose.agda` (corrupted receiver)

```agda
ηʰ : ℕ → ℕ → ℚ                                                          -- :101
ηʰ n _ = 0ℚ ℚ.+ inv-pow-2 n

coin-hybridʳ : (λ n → (tossʰᶠ ∙ᶠ idealʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ    -- :119
coin-toss-idealʳ : realʰᶠ ≤UC^ωᵉ idealʰᶠ
                 → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ -- :128

εᶜʳ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ                                           -- :135
εᶜʳ ε n q = εᶜᵗ ε n q ℚ.+ ηʰ n q
schedule-pinʳ : (w : realʰᶠ ≤UC^ωᵉ idealʰᶠ)
              → proj₁ (proj₂ (coin-toss-idealʳ w)) ≡ εᶜʳ (proj₁ (proj₂ w))  -- :140
ideal-εʳ : (n q : ℕ) → εᶜʳ εᵗ n q ≡ fromℕ (q + (q + q)) *ℚ inv-pow-2 n ℚ.+ inv-pow-2 n -- :146
```

- The second hop is NOT exact here: the honest committer's share is drawn one
  activation earlier than the ideal coin's, so what is exact is the two systems' RUNS
  (`Receiver.Machine.coin-runʰ`), and carrying a run agreement into a context costs
  the domination's positive slack `2⁻ⁿ`. Hence `ηʰ` and the extra summand.
- `≈ctx-sub flatᶜʰ` regrades at cost 1, which changes nothing because `ηʰ` ignores its
  allowance.
- The `≤UC^ωᵉ⇒≤UCᴺ` use: `coin-toss-idealʳᴺ` (`:165`), with `coinRealʰQB`/`FcoinʰQB`
  at `(λ _ → 0) , poly-const 0 , …` (`:156`, `:159`).
- Callers: `coin-hybridʳ` — `Realization/Assembly.agda:109`; `εᶜʳ` —
  `Realization/Assembly.agda:114`, `Test.agda:82`; `ideal-εʳ` — `Test.agda:56`.
  `coin-toss-idealʳ`, `coin-toss-idealʳᴺ`, `schedule-pinʳ`: no in-repo caller.

### 6. `Examples/HashForward/Audit.agda` — the audit-carry consumer

```agda
hf-witness : AuditWitness 2 realᵒ idealᵒ                                -- :67
hf-witness = audit⇒witness (≤UC[]ᵍ simQB real-factors)

hf-emul : realᵒ ≤UC[ 2 ] idealᵒ                                         -- :70
hf-emul = witness⇒audit hf-witness
```

```agda
hf-audit-carry : (μ : ℕ → Dₚ Bool) (ε : ℕ → ℚ) (δ η : ℚ) → 0ℚ ℚ.< δ → 0ℚ ℚ.< η
               → ((q n : ℕ) → Pr≤ n (μ q) ℚ.≤ ε q)
               → AuditBound realᵒ (absorb simᵒ 2 (pinned idealᵒ μ))
                   (λ q → (ε (simCost q 2) ℚ.+ δ) ℚ.+ η)
```
`:88`.

```agda
hf-audit-silent : (δ η : ℚ) → 0ℚ ℚ.< δ → 0ℚ ℚ.< η
                → AuditBound realᵒ (absorb simᵒ 2 (pinned idealᵒ silent))
                    (λ _ → (0ℚ ℚ.+ δ) ℚ.+ η)
```
`:107`.

```agda
hf-pr-bound : (μ : ℕ → Dₚ Bool) (ε : ℕ → ℚ) (δ η : ℚ) → 0ℚ ℚ.< δ → 0ℚ ℚ.< η
            → ((q n : ℕ) → Pr≤ n (μ q) ℚ.≤ ε q)
            → (e : Strat (Neg Honᴵ) (Pos Honᴵ)) (a : Proc Advᴵ 𝟭ᴵ) (w : Proc unitᴵ Resᴵ)
              {q c c′ : ℕ} → asks≤ q e → QBᴹ c a → QBᴹ c′ w
            → absorb simᵒ 2 (pinned idealᵒ μ) 𝟘ᴳ (auditTestᵍ Honᴵ e a) (closedᵒ w)
                (ctxBudget (q * ((c ⊔ 1) ⊔ 1)) c′)
            → (n : ℕ)
            → Pr≤ n (runᴹ (closedᵍ Honᴵ e a real w) e)
              ℚ.≤ (ε (simCost (ctxBudget (q * ((c ⊔ 1) ⊔ 1)) c′) 2) ℚ.+ δ) ℚ.+ η
```
`:127`.

- Premise relation: the qualitative graded emulation `realᵒ ≤UC[ 2 ] idealᵒ`, obtained
  from `Examples.HashForward.real-factors` through `UC.Seam.Graded.≤UC[]ᵍ` and
  `UC.Audit.Canonical`'s two adapters. The grade is `ifaceᵒ Advᴵ` — NOT trivial, which
  is the point of the example.
- Adversary class: `a : Proc Advᴵ 𝟭ᴵ` with `QBᴹ c a`, honest strategy `e` with
  `asks≤ q e`, resource `w : Proc unitᴵ Resᴵ` with `QBᴹ c′ w`; the permitted contexts
  are `UC.Seam.Audit.Context`'s graded audit tests.
- Resource certificates: simulator `simQB` at cost 2 (one `peekᴬ` buys the leak fetch
  and the hash query; `Examples.HashForward.UC.simExactAll` says 2 is exact, not a
  ceiling). `absorbed-budget` (`:80`) states the absorbed test's certificate
  `QB (c * ((2 ⊔ 1) ⊔ 1))` explicitly, so the accounting is visible.
- Error: TWO positive slacks, `δ` from `pinned-bound`'s `dominate` and `η` from
  `audit-carry`'s, plus the designated bound `ε` read at `simCost q 2`. At the toy's
  own designation (`silent`, an ideal monitored experiment reporting `false`) the
  designated bound is `0` and the real side's error is the two slacks alone.
- Quantifier order: `μ`, `ε`, `δ`, `η` all fixed before any context; no polynomial cap
  (the toy has no security parameter).
- Generic/model split: everything mathematical is `UC.Audit`'s; model-specific are the
  sealed application (`UC.Seam.Audit`), `auditTestᵍ`/`closedᵍ`/`extractᵍ`, and `Pr≤` of
  a raw machine's run — `real` is a raw machine, so layer 1's `Bounded` is not
  available to it.
- Callers: `hf-witness` at `:71`; `hf-audit-carry` at `:111`, `:139`. `hf-emul`,
  `hf-audit-silent`, `hf-pr-bound` have no in-repo caller (public results).
- Replacement: none for these; WP1 instruction 6 requires them to keep proving the
  same result — event conditions, simulator cost, and both slacks — after
  `audit-carryᵉ`'s body is replaced.

### 7. The event-bound / monitor / lift layer

#### `UC/Model/EventBounds.agda`

```agda
Readout : Iface → Set₁                                                  -- :59
Readout B = (Y : Iface) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B) Ωᴵ

readRun : (Y : Iface) → Proc A B → Readout B → Proc (Y ⊗ᴵ B) Ωᴵ
        → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool                                -- :62
readRun Y f 𝔠 E m = ctxRun Y (𝔠 Y E) m f

BoundedAt : ℕ → ℚ → Proc A B → Readout B → Set₁                        -- :73
BoundedAt {A = A} {B = B} q r f 𝔠 =
    (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m → ctxBudget c c′ ℕ.≤ q → Upper (readRun Y f 𝔠 E m) r
```

```agda
module _ {A B : ℕ → Iface} (f : (n : ℕ) → Proc (A n) (B n))
         (𝔠 : (n : ℕ) → Readout (B n)) where                            -- :81

  Boundedᶠ : (ℕ → ℕ → ℚ) → Set₁                                        -- :84
  Boundedᶠ ε = (n q : ℕ) → BoundedAt q (ε n q) (f n) (𝔠 n)

  Boundedᴺ : (ℕ → ℕ → ℚ) → Set₁                                        -- :89
  Boundedᴺ ε = (p : ℕ → ℕ) → Poly p
             → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν
             × ((n : ℕ) → BoundedAt (p n) (ε n (p n) ℚ.+ ν n) (f n) (𝔠 n))

  boundedᶠ⇒boundedᴺ : (ε : ℕ → ℕ → ℚ) → Boundedᶠ ε → Boundedᴺ ε        -- :99
```

- `BoundedAt` reads the schedule at a CAP (`ctxBudget c c′ ≤ q`), where
  `UC.Audit.AuditBound` reads it at the carried allowance — the two are not
  identified, and bridging them is the sealed model's job.
- `Boundedᴺ`'s slack is chosen AFTER the polynomial allowance and BEFORE the level,
  uniform over every context that allowance admits. `boundedᶠ⇒boundedᴺ` is the
  zero-slack collapse; a bound whose slack is chosen inside the context quantifier
  would yield no `Boundedᴺ`, which is why the carry takes its error before the context.
- Callers: `Readout` — `UC/Machine/Monitor.agda:108`, `UC/Model/EventBounds.agda:62`,
  `:73`, `:82`. `readRun` — `UC/Machine/Monitor.agda:113`. `BoundedAt` —
  `UC/Quantitative/EventLift.agda:83` (`HitsAt`). `Boundedᶠ`/`Boundedᴺ` —
  `EventLift.agda:87`, `:91`. `boundedᶠ⇒boundedᴺ` — `EventLift.agda:96`.
  `ctxRun-∘` (`:112`) is **CONSUMER-FREE**.
- Replacement: none (WP3 keeps this layer; the plan's table assigns it "concrete event
  readouts and capped contextual bounds").

#### `UC/Machine/Monitor.agda`

```agda
monitorᴹ : {B : Iface} → (Neg B → Pos B → Bool) → Proc B (B ⊗ᴵ Flagᴵ)  -- :74
flagReadᴹ : Proc (Ωᴵ ⊗ᴵ Flagᴵ) Ωᴵ                                      -- :94
compileᴹ : (Y B : Iface) → Proc B (B ⊗ᴵ Flagᴵ) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B) Ωᴵ -- :101
compileᴹ Y B μ E = flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ (a⇒ᴵ 𝒫.∘ T₁ᴵ Y μ))
readoutᴹ : (B : Iface) → Proc B (B ⊗ᴵ Flagᴵ) → Readout B               -- :108
eventRun : {A B : Iface} (Y : Iface) → Proc A B → Proc B (B ⊗ᴵ Flagᴵ)
         → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool           -- :111
```

- This is the plan's "observer state and initialization + query/answer update rules +
  completion readout → monitored machine". The observer scope is the Boolean
  accumulator parameterized by `report : Neg B → Pos B → Bool`
  (`MonSt B = Bool × Maybe (Neg B)`, `monitorStep` `:63`); the ledger's
  `Watched.reportsLoss` is the one instance. WP3 should make these the public
  interface.
- Certificate: `qbᵢ-monitor : (B : Iface) (report : …) → Certified 1 (monitorᴹ report)`
  (`:118`), `Φ ≡ 0`. **CONSUMER-FREE** as a name; the cost it records is what
  `EventLift.Cov` re-derives.
- Callers: `monitorᴹ` — `Monitor/Agree.agda:242`, `:246`, `:248`-`:250`, `:534`,
  `:544`, `:556`; `Monitor/Slide.agda:51`, `:77`, `:109`; `EventLift.agda:105`, `:111`,
  `:114`, `:132`, `:150`, `:164`, `:213`; `EventLift/Cov.agda:311`, `:322`;
  `Examples/ChimericLedger/Property.agda:142`. `compileᴹ` — `Monitor.agda:109`,
  `Monitor/Slide.agda:77`, `:80`, `Monitor/Agree.agda:534`, `EventLift.agda:105`,
  `:114`, `EventLift/Cov.agda:311`, `:322`. `flagReadᴹ` — `Monitor.agda:102`,
  `Monitor/Slide.agda:51`, `:82`-`:102`, `Monitor/Agree.agda:130`-`:393`. `readoutᴹ` —
  `Monitor.agda:113`, `EventLift.agda:83`, `:87`, `:91`. `eventRun` —
  `Monitor/Agree.agda:556`, `EventLift.agda:111`, `:132`, `:150`.
- `monitor-query` (`:160`), `monitor-answer` (`:165`), `monitor-flag` (`:170`) are the
  three traffic pins at the steps deciding them, all `refl`, and all
  **CONSUMER-FREE** — they are checks, not the agreement theorem.
- Replacement: none.

#### `UC/Machine/Monitor/Agree.agda:553`

```agda
agree : (B : Iface) (report : Neg B → Pos B → Bool)
        (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
      → (u : Proc unitᴵ B) (d : Strat (Neg B) (Pos B))
      → eventRun unitᴵ u (monitorᴹ report) (stratTest B d) m₀ ≈ₚ runᴹ u (w false d)
```

- The semantic agreement of the compiled experiment with the strategy-level watch, at
  the strategy-embedding context `stratTest B d` and the closed `m₀`. Divergence is
  inside the `≈ₚ` (a test that diverges leaves `flagReadᴹ` in `waitE`); there is no
  separate divergence theorem.
- Callers: `UC/Quantitative/EventLift.agda:217`.
- Replacement: none.

#### `UC/Quantitative/EventLift.agda`

```agda
HitsAt : {A B : Iface} → ℕ → ℚ → Proc A B → Proc B (B ⊗ᴵ Flagᴵ) → Set₁  -- :82
HitsAt {B = B} q r f μ = BoundedAt q r f (readoutᴹ B μ)
Hitsᶠ : … → Set₁                                                        -- :85
Hitsᴺ : … → Set₁                                                        -- :89
hitsᶠ⇒hitsᴺ : … → Hitsᶠ ε f μ → Hitsᴺ f μ ε                             -- :93
```

```agda
eventDominatedᶜ :
    {B : Iface} (report : Neg B → Pos B → Bool)
    (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
  → (u : Proc unitᴵ B) (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ)
    (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) (k : ℕ)
    (kb : QB k (Kctx (openedᴹ Y B report E) m)) → CovCtx B k report kb
  → (r : ℚ)
  → ((d : Strat (Neg B) (Pos B)) → asks≤ k d → Upper (runᴹ u (w false d)) r)
  → Upper (eventRun Y u (monitorᴹ report) E m) r
```
`:124`. The lift with the accumulator invariant and the compiled context's own
certificate taken as PREMISES. No slack.

```agda
eventDominatedᵘ :
    {B : Iface} (report : Neg B → Pos B → Bool)
    (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
  → (u : Proc unitᴵ B) (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ)
    (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) {c : ℕ} → QB c E → (r : ℚ)
  → ((d : Strat (Neg B) (Pos B)) → asks≤ (c ℕ.+ 1) d → Upper (runᴹ u (w false d)) r)
  → Upper (eventRun Y u (monitorᴹ report) E m) r
```
`:144`. Those premises discharged by `covCtx`, at the one rate it can be: `c + 1`.
The closure is recertified at rate zero (`qb-closed`), so the compiled context's
allowance depends on the TEST's own rate `c` and not on `ctxBudget c c′`.

```agda
hitsᵘ : {B : Iface} (report : Neg B → Pos B → Bool)
        (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
      → (u : Proc unitᴵ B) (q : ℕ) {r : ℚ}
      → ((d : Strat (Neg B) (Pos B)) → asks≤ (q ℕ.+ 1) d → Upper (runᴹ u (w false d)) r)
      → HitsAt q r u (monitorᴹ report)
```
`:160`. The public capped shape; `c ≤ ctxBudget c c′ ≤ q` rescales the test's own rate
to the cap.

```agda
hits⇒bounded :
    {B : Iface} (report : Neg B → Pos B → Bool)
    (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
  → (P : Protocol unitᴵ B) (q : ℕ) {r : ℚ}
  → HitsAt q r (morphism P) (monitorᴹ report)
  → (d : Strat (Neg B) (Pos B)) → asks≤ q d → Pr P (w false d) ℚ.≤ r
```
`:209`. The way back: the closure is closed, `ctxBudget q 0 = q`, so the strategy keeps
the whole cap and nothing is spent returning.

```agda
qb-stratTest : (B : Iface) {q : ℕ} (d : Strat (Neg B) (Pos B)) → asks≤ q d
             → QB q (stratTest B d)
```
`:197`.

- Callers: `HitsAt` — `EventLift.agda:164`, `:213`,
  `Examples/ChimericLedger/Property.agda:158`, `:167`. `Hitsᶠ` — `EventLift.agda:95`
  only. `Hitsᴺ` — `EventLift.agda:95`, `Property.agda:150`. `hitsᶠ⇒hitsᴺ` —
  `Property.agda:196`. `hitsᵘ` — `Property.agda:159`. `hits⇒bounded` —
  `Property.agda:184`. `eventDominatedᵘ` — `EventLift.agda:166` only.
  `eventDominatedᶜ` — `EventLift.agda:152` only. `qb-stratTest` — `EventLift.agda:218`
  only. `upper-run` (`:174`) — `Property.agda:171`, `Transfer.agda:99`, `:294`.
  `run-upper` (`:185`) — `EventLift.agda:216` only. `openedᴹ` (`:103`) and
  `eventRun-closed` (`:108`) — internal.
- Replacement: none; WP4 is a bounded review of the `q + 1`, not a mandate to change it.

#### `UC/Quantitative/EventLift/Cov.agda:308` and `UC/Machine/Dominated.agda:211`, `:239`

```agda
covCtx : (Y B : Iface) (report : Neg B → Pos B → Bool) {c : ℕ}
         (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) → QB c E
       → Σ[ kb ∈ QB (c ℕ.+ 1)
                    (Kctx (compileᴹ Y B (monitorᴹ report) E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m) ]
           CovCtx B (c ℕ.+ 1) report kb
```

```agda
CovCtx : (B : Iface) {K : Proc B Ωᴵ} (q : ℕ) → (Neg B → Pos B → Bool) → QB q K → Set
CovCtx B q report (N , cert , _) =
  (f : ℕ) (z : AtMost Φ 0) → Cov false f (Φ (proj₁ z) ℕ.+ q) (onRᵍ (proj₁ z) tt)
```

```agda
eventSkeleton : EventSkeleton                                    -- Dominated.agda:239
-- EventSkeleton (:224) =
--     (B : Iface) (K : Proc B Ωᴵ) {q : ℕ} (report : Neg B → Pos B → Bool)
--     (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
--   → (the three `IsWatch` equations, spelled out)
--   → (kb : QB q K) → CovCtx B q report kb
--   → (u : Proc unitᴵ B) (r : ℚ) → …
```

- `CovCtx` quantifies over EVERY zero-potential state (`z : AtMost Φ 0`) and every
  fuel — not over supported initial states or reachable configurations. That
  quantification is WP4 instruction 1's subject; the extra unit of allowance is the
  accumulator's potential, and at the test's own rate `c` the premise is not merely
  unproved but FALSE (a context spending its whole allowance before its answer reports
  leaves the accumulator raised with no potential left).
- Callers: `covCtx` — `EventLift.agda:154` only. `CovCtx` — `EventLift.agda:129`,
  `EventLift/Cov.agda:312`, `Dominated.agda:233`. `eventSkeleton` —
  `EventLift.agda:135` only.
- Replacement: none. WP4 may propose a localized refactor; the discharged `c + 1`
  theorem stays until both halves of any alternative are checked.

### Representation boundaries

| Boundary | Construction (source) | Proved law |
|---|---|---|
| Raw processes → certified families | `Certified` `UC/Quantitative/Family.agda:201`, `idᶜ` `:219`, `_∘ᶜ_` `:222`, `λ⇒ᶜ` `:228`, `subᶠ` `:232`; admissibility is the context's `QB c E`/`QB c′ m` in `_≈ctx[_]_` `:95`; carried certificates are required only of morphisms a theorem MOVES into a context (`Certified`, and `UC-composeᵉ`'s `cf`/`cv`), never of the compared homs | `≈ctx-sub` `:241` (exact `simCost`), `NegligibleBound-simCost` `:250`, `≤UC^ωᵉ-trans` `:320`, `UC-composeᵉ` `:437` — no single theorem; the shared absorption underneath them is `UC/Quantitative/Contextual.agda`'s `ctx-sub` `:189` / `ctx-absorb` `:171` / `absorb-closureᵠ` `:153`, with `Agreeᵠ` `:77` and `at-trans` `:203` |
| Protocols → machines | `Protocol.Machine.morphism`; `imgᶠ` `UC/Model/Family/Emulation.agda:72`; `UC.Seam.Grounded.closedᵒ` | operational adequacy: `Protocol.Machine.Agree.prAgree`, used as `upper-run` `UC/Quantitative/EventLift.agda:174` and `run-upper` `:185` |
| Watched strategies → monitored experiments | `monitorᴹ` `UC/Machine/Monitor.agda:74`, `flagReadᴹ` `:94`, `compileᴹ` `:101`, `readoutᴹ` `:108`, `eventRun` `:111`; strategy side `stratTest`/`m₀` `UC/Machine/Monitor/Agree.agda` | `agree` `UC/Machine/Monitor/Agree.agda:553`; termination and divergence are inside its `≈ₚ` (a diverging test leaves `flagReadᴹ` in `waitE`) — no separate divergence theorem |
| Quantitative bounds → negligible observation | two distinct collapses: capped family bound `UC/Model/EventBounds.agda:84`-`:92`, and the witness packaging `UC/Model/Family/Emulation.agda:124`-`:139` | `boundedᶠ⇒boundedᴺ` `UC/Model/EventBounds.agda:99` (order: cap `p`, then slack `ν`, then level `n`, then context) and `≤UC^ωᵉ⇒≤UCᴺ` `UC/Model/Family/Emulation.agda:137` (order: simulator, schedule, negligibility, caps; route via `_≈ℰⁿ_`, not via vanishing) — no single theorem |
| One observational reading → another | `prefixᵒ` vs the operational bracket: `≈ctx⇒≈ctxᴬ` `UC/Quantitative/Family.agda:136`, `≈ctxᴬ⇒≈ctx` `:142` (cost one `QB 1` structural morphism, `c ↦ c * 1`, restored by `*-identityʳ`); per-level vs family-of-contexts: `≈ctxᴬ⇒≈ℰ[]` `UC/Model/Family/Emulation.agda:100`, a named implication and NOT an identification; setup-to-setup: `UC/Family/Quantitative.agda:71`-`:96`, `UC/Family/Negligible/Quantitative.agda:76`-`:101` | `≈ctx⇒≈ctxᴬ`/`≈ctxᴬ⇒≈ctx` are an equivalence; the setup-level transfers are one-way (`≈ᵁ^ω⇒≈ᵁ₊`/`≈ᵁ₊⇒≈ᵁ^ω` both directions, `uniform⇒local` one direction only) — no single theorem, see WP5 |

### Decisions recorded

1. **The appendix schedule is `q + q + 1`** (2026-09-22). `ledger-uc-to-pov-family`
   (`Examples/ChimericLedger/Transfer.agda:219`) concludes at
   `εᴹ n (p n + p n) + ν n`, i.e. `εᴸ n (q + q + 1)`: the doubling is `withAudits`'
   honest-interface instrumentation, the `+ 1` is the monitor accumulator's. Ruled by
   the maintainer when the strategy-level route was retired — the appendix now reads
   claim 1's contextual bound back at the embedded strategies rather than proving a
   second transfer. An older document's sharper strategy-level number is not the
   public type.
2. **`UC.Saturated` and `UC.Asymptotic*` are retired** (2026-09-22), together with the
   standalone `Hits` module and the model's old carried-bound/`Charge` interface.
   Confirmed absent from the tree at `ba1878ca`. New code targets the current
   consumers; the mathematical distinctions those layers expressed may still matter,
   but they are not to be restored because an older plan mentions them.
3. **`robust-quant` is not merged.** Its tip is `eaa45bf8`. Its reusable core is the
   `BoundedProperty` record's `carry` law
   (`robust-quant:src/CategoricalCrypto/UC/Robust/Quantitative.agda:47`-`:57`):
   `carry : u ≈[ ε ] v → holds r v → holds (r ⊕ ε) u`, plus `mono`. That is the
   plan's rule 6 assessment: reuse the bound-transport law if it fits, do not retain
   the record merely to rename one projection, and do not merge its adapters
   (`UC/Audit/Robust.agda`, `UC/Model/EventBounds/Robust.agda`, `QRobust`) — its
   comparison premise covers every environment, where the actual audit/ledger
   evidence is allowance-sensitive and selects test/closure pairs.
4. **The `simStep` re-logging defect still blocks the coin chain's premise.**
   `Examples/ROCommitment.agda:193`-`:214`'s `simStep` conses `(x , d)` onto the
   simulator's log at EVERY relayed answer, including one the oracle served from its
   table, so after a repeated query the log holds the digest twice and `extract` reads
   `false` (`Examples/ROCommitment/Realization/Bisim.agda`, `extract-relog` vs
   `extract-table`). `docs/rcom-icom-b1.md` row B2-M3 records the maintainer call:
   either `simStep` caches, or `Game.respI` is restated over the relay log (which
   makes `Game.cert` false). Until then `Realization`/`Realizationʰ`
   (`Examples/ROCommitment/Realization/Statement.agda:51`-`:52`) remain hypotheses,
   `assembly`/`assemblyʰ` remain conditional, and the commitment result must not be
   described as a full machine realization (WP6 check 5).

## 12. Explicit-error API (2026-09-23)

WP2 of `docs/quantitative-theory-consolidation-review-plan.md`. The primary
quantitative interface is the FIXED-DATA bound, not the existential witness:
every composition theorem is proved at a named simulator and a named schedule,
and the witness forms package it. Nothing below is a new mathematical result —
the proofs are the ones §6 describes, moved.

### 12.1 The relation

`UC/Quantitative/Family.agda`:

```agda
_≤UC[_,_]_ : Homᶠ A X B → Certified Y X → (ℕ → ℕ → ℚ) → Homᶠ A Y B → Set _
f ≤UC[ s , ε ] g = f ≈ctx[ ε ] subᶠ s g
```

It is a definitional alias, so every existing comparison inhabits it with no
transport and no new assumption, and `_≤UC^ωᵉ_` is literally
`Σ[ s ] Σ[ ε ] NegligibleBound ε × f ≤UC[ s , ε ] g`. The bound itself asks
nothing of `ε`.

The name is not `At`. `UC.Quantitative.Witness.At` is the nonexpansive
single-level construction at a `QUCSetup` and is a different relation, and
`UC.Quantitative.Contextual` — which this module opens unqualified — already
owns `at-trans`, so an `at-*` family here would clash outright.
`_≤UC[_,_]_` follows `UC.Audit._≤UC[_]_`'s bracketed-witness spelling while
being a distinct name from it.

### 12.2 The published formulas, and what packages them

```agda
seqError s ε δ n q = ε n q + δ n (scale q (cost s n))

composeSim sf t =
    (λ n → cost sf n · cost t n) , …
  , λ n → L.sub[ … ] ((L.id ⊗ʰ hom t n) L.∙ (hom sf n ⊗ʰ L.id))

composeError rf rtv εf εu n q = εu n (scale q (rf n)) + εf n (scale q (rtv n))
```

| fixed-data name | the existential-witness name that now packages it |
|---|---|
| `≤UC[]-resp` | `≤UC^ωᵉ-resp` |
| `seqError`, `seqError-negligible`, `≤UC[]-trans` | `≤UC^ωᵉ-trans` |
| `≤UC[]-dom` | `≤UC^ωᵉ-dom` |
| `composeSim`, `composeError`, `composeError-negligible`, `≤UC[]-compose`, `≤UC[]-compose′` | `UC-composeᵉ` (through `≤UC[]-compose′`), hence `≤UC^ωᵉ-∙` |
| `≤UC[]⇒≈ℰⁿ`, `≤UC[]⇒≤UCᴺ` (`UC/Model/Family/Emulation.agda`) | renamed from `≤UC^ωᵉ⇒≈ℰⁿ` / `≤UC^ωᵉ⇒≤UCᴺ`; both callers migrated, so no alias is kept |

The split is exactly negligibility: `≤UC[]-trans` and `≤UC[]-compose` take no
`NegligibleBound` and no `Poly⁺` (the simulator carries its own polynomial
through `Certified`); `seqError-negligible` and `composeError-negligible` are
where `NegligibleBound-scale` and `GradedBound-+[_]` are spent, and where
`Poly⁺ rf`/`Poly⁺ rtv` are consumed.

### 12.3 Migrated consumers

| consumer | fixed-data name | packaged name it now feeds |
|---|---|---|
| `Examples.CoinToss.Compose` | `coin-toss-from-comᵇ`, `coin-toss-from-comʰᵇ`, `εᶜᵗ-negligible` | `coin-toss-from-com`, `coin-toss-from-comʰ` |
| `Examples.CoinToss.Ideal.Compose` | `coin-hybridᵇ`, `simᶜⁱ`, `coin-toss-idealᵇ` | `coin-hybridᵉ`, `coin-toss-ideal`, `coin-toss-idealᴺ` |
| `Examples.CoinToss.Ideal.Receiver.Compose` | `coin-hybridʳᵇ`, `simᶜʳ`, `coin-toss-idealʳᵇ` | `coin-hybridʳ`, `coin-toss-idealʳ`, `coin-toss-idealʳᴺ` |
| `Examples.ChimericLedger.Transfer` | `εᴴ`, `εᴴ-negligible`, `hash-liftᵇ` | `hash-liftⁿ` |

Every schedule pin — `schedule-pin`, `schedule-pinʰ`, `schedule-pinⁱ`,
`schedule-pinʳ`, `Realization.Assembly.pin`/`pinʰ` — still checks by `refl`
and at the same expression: the new formulas are definitional unfoldings of
the lambdas that were inlined before.

`_≤UC^ωᵉ_` is NOT retired. Its remaining callers are
`Examples.ROCommitment.Realization.Statement`'s `Realization`/`Realizationʰ`
and `Assembly`/`Assemblyʰ`, which must hide the simulator and the schedule
because the commitment proof has not yet chosen them, and the coin headline
theorems stated against that boundary. It owns no metatheory of its own any
more — each of its lemmas is three lines over the fixed-data ones.

### 12.4 What the canonical corollary does and does not say

`≤UC[]⇒≤UCᴺ` keeps the certified simulator family. It does NOT expose the
bound's global schedule: `≈ℰⁿ⇒≈ℰᴺ` specializes that one schedule to the
allowance each context carries, so `Canonicalᴺ._≤UC_` records only a
negligible witness chosen inside the contextual quantification, and no theorem
recovers a global one from it. A consumer that needs the number keeps the
`_≤UC[_,_]_` data — which is why the coin modules publish `coin-toss-idealᵇ`
beside `coin-toss-idealᴺ`. Comments in `UC/Model/Family/Emulation.agda`,
`UC.agda` and `Examples/CoinToss/Ideal/Compose.agda` claiming the schedule
survived the crossing were corrected here.

## 13. Observational transport (2026-09-23)

`Abstract2.Morphism` gained the degenerate case of setup transport: two setups
over the SAME `𝒞`, `ℐ` and `ℳ`, differing only in the environment presheaf.

```agda
reobserve : (𝕊 : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
          → Presheaf (UCSetup.𝒞 𝕊) (Setoids cs′ ℓs′)
          → UCSetup o ℓ e o′ ℓ′ e′ cs′ ℓs′

module Refine (𝕊 : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
              (ℰ′ : Presheaf (UCSetup.𝒞 𝕊) (Setoids cs′ ℓs′))
              (refineℰ : {A B : Category.Obj (UCSetup.𝒞 𝕊)}
                         {f g : UCSetup.𝒞 𝕊 [ A , B ]}
                       → UCSetup._≈ℰ_ 𝕊 f g → UCSetup._≈ℰ_ (reobserve 𝕊 ℰ′) f g)
  ≈ᵁ-refine  : {f g : A ⇒ T₀ X B} → f S.≈ᵁ g → f S′.≈ᵁ g
  ≤UC-refine : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f S.≤UC g → f S′.≤UC g
```

The hypothesis is a refinement of the BARE kernel, not of environments: both
setups read `_≈ᵁ_` at the same prefix contexts `μ ∘ T₁`, so `≈ᵁ-refine` is that
hypothesis applied pointwise and no carrier correspondence has to be stated.
`≤UC-refine` is `≤UC⇒dummy` followed by `dummy-complete`, so the simulator and
its certificates cross unchanged. Nothing here needs `GradeStable` or the
epi/mono side conditions `Transfer` (transport along a `UCSetupMorphism`) does:
`Transfer` moves the homs by `κ ∘ F₁ _` and can only preserve `_≈ℰ_`, while here
the compared homs are the original ones.

Now instances, with statements byte-identical:

| theorem | module | instance |
|---|---|---|
| `≈ᵁ^ω⇒≈ᵁ₊` | `UC.Family.Quantitative` | `R₊.≈ᵁ-refine`, kernel step `≋⇒∼₊` |
| `≤UC^ω⇒≤UC₊` | `UC.Family.Quantitative` | `R₊.≤UC-refine` |
| `≈ᵁ₊⇒≈ᵁ^ω` | `UC.Family.Quantitative` | `R^ω.≈ᵁ-refine`, kernel step `∼₊⇒≋` |
| `≤UC₊⇒≤UC^ω` | `UC.Family.Quantitative` | `R^ω.≤UC-refine` |
| `≈ᵁˢ⇒≈ᵁᴺ` | `UC.Family.Negligible.Quantitative` | `Rᴺ.≈ᵁ-refine`, kernel step `uniform⇒local` |
| `≤UCˢ⇒≤UCᴺ` | `UC.Family.Negligible.Quantitative` | `Rᴺ.≤UC-refine` |

`≈ᵁ^ω⇔≈ᵁ₊` still packages the two agreement directions by hand; the vanishing
pair has both, the uniform/local pair has only one and no uniformization
premise was introduced for the converse.

Carrier/action compatibility is not asserted, it is elaborated: each `Refine`
application forces `reobserve 𝕊 ℰ′` to be convertible with the target setup, so
Agda checks `𝒞`, `ℐ` and `ℳ` agree on the nose (the `refl` counterpart already
recorded as `UC.Family.Negligible.Setup.shared-computational`), and each kernel
step forces the two presheaves' carriers and `F₁` to agree — for both pairs
`Test A` and `_∘ h`.

Not migrated: `UC.Quantitative.Bridge`'s `zero-emulation`, `positive-emulation`
and `small-emulation⇐` are the same sandwich between ONE setup's `_≤UC_` and a
`Witness` record, not between two setups, so `Refine` does not apply and each is
already a one-line `dummy-complete`. `UC.Family.Negligible.Setup` has no
`dummy-complete` of its own — it delegates to `UC.Core.Bridge.≈ᵁ⇒≤UC`.

Cost (warm, one `Checking` line, `+RTS -M8G -H2G`; wall-clock is unusable here
because a sibling worktree held the memory gate, so these are `user` CPU):

| Module | LOC | warm before | warm after |
|---|---|---|---|
| `Abstract2.Morphism` | 98 → 135 | 6.6 s | 7.3 s |
| `UC.Family.Quantitative` | 101 → 97 | 45.3 s | 37.0 s |
| `UC.Family.Negligible.Quantitative` | 106 → 105 | 36.8 s | 31.9 s |

Both bridges are shorter and cheaper; the shared lemma costs +37 lines, so the
pass is +32 lines overall. What it buys is that the three copies of
`≤UC⇒dummy`-transport-`dummy-complete` and the three of
`runs⇒≈ᵁ`-transport-`run-resp-≈ᵁ` are now one each, and the bridges supply only
their kernel step.

## 14. Public theorem map (2026-09-23, baseline `cee4efca`)

WP6 of `docs/quantitative-theory-consolidation-review-plan.md`. One record per
public headline, each read off the tree at `cee4efca`; `file:line` is that
tree's line of the signature's first token, paths relative to
`src/CategoricalCrypto/`. Where an earlier section of this file or of
`docs/end-to-end.md` disagrees, this section is current.

On this branch the generic API of §14.4 is stated over the resource grading
(§16); its records below are rewritten to it, and their line numbers are
omitted. The example and model records (§14.1-§14.3, checks 1-6, §14.6)
describe `protocol-rewrite`'s instances, which still take `UC.Budget`: read
their `simCost q cs` as `scale q (positive cs)` and `ctxBudget c c′` as
`value (c · positive c′)` at a test rate `c : ℕ⁺` (numerically their
`scale c (positive c′)`, `refl`; a zero-query context has no counterpart), and
their `QB` certificates as the model-level ones the §16 adapter turns into
`Image` certificates.

Field key, the plan's:

- **Compared / resources** — the two systems (or the one bounded system) and
  what is installed below them.
- **Contexts / certificates** — the admitted context class and the resource
  certificates it must carry.
- **Simulator** — the simulator evidence and whether the statement retains it.
- **Error / allowance** — the explicit error and the allowance transformations
  spent on it.
- **Quantifiers** — the order of simulator, schedule, polynomial cap and slack.
- **Assumptions** — what is left assumed, and its status.
- **Kind** — conditional, instantiated, or compatibility.

### 14.1 The ledger example

#### `Property.PreservesValue` — `Examples/ChimericLedger/Property.agda:150`

```agda
PreservesValue : Systems LedgerIf^ω → Set₁
PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴹ
```

in `module _ (a V : ℕ)` (`:122`), with `auditMonitorᶠ n = monitorᴹ
(Watched.reportsLoss n (genesisAt n))` (`:142`), `εᴹ n q = εᴸ n (q + 1)`
(`:108`) and `εᴸ n q = (q·q + q)·2⁻ⁿ` (`:86`).

- **Compared / resources** — not a comparison: a bound on ONE family of closed
  protocol images `R : Systems LedgerIf^ω`. Nothing is installed below it; the
  monitor is the compiled observer, not a resource.
- **Contexts / certificates** — `Hitsᴺ` is `Boundedᴺ` at `readoutᴹ`
  (`UC/Quantitative/EventLift.agda:87`, `UC/Model/EventBounds.agda:89`), and
  `BoundedAt q r f 𝔠` (`EventBounds.agda:73`) quantifies every ancilla `Y`,
  every test `E` with `QB c E`, every closure `m` with `QB c′ m`, subject to
  `ctxBudget c c′ ℕ.≤ q`. The compared system carries no certificate. The event
  read is the COMPILED observable flag — `compileᴹ`
  (`UC/Machine/Monitor.agda:101`) wraps the context's own test, so the
  experiment's verdict IS the flag, and no internal state is read.
- **Simulator** — none; there is none at the trivial grade.
- **Error / allowance** — `εᴹ n (p n) + ν n`, read at the CAP `p n`, not at the
  carried `ctxBudget c c′`.
- **Quantifiers** — cap `(p , Poly p)` first, negligible slack `ν` second
  (uniform over every context that cap admits), level third, context last. The
  other order is deliberately not what is proved (`docs/end-to-end.md` §4).
- **Assumptions** — none in the definition.
- **Kind** — definition. It is the statement `ideal-preserves-value`,
  `preserves-value-transfer` and `chimeric-not-preserving` are about.

#### `ideal-preserves-value` — `Property.agda:195`

`SerInj → PreservesValue Ideal`, with `Ideal n = AtLevel.Sys n inputConsuming
(genesisAt n)` (`:127`).

- **Compared / resources** — the repaired ledger over the lazily sampled random
  oracle, closed. No second system.
- **Contexts / certificates** — `PreservesValue`'s, above. The route in is
  `ideal-bounded` (`:191`, the birthday theorem through the watch) then
  `ledger-hitsᵘ` (`:166`) then `hitsᶠ⇒hitsᴺ`
  (`UC/Quantitative/EventLift.agda:91`); `ledger-hitsᵘ` reads the strategy
  bound at `q + 1`.
- **Simulator** — none.
- **Error / allowance** — exactly `εᴹ`, with slack `0` before `hitsᶠ⇒hitsᴺ`
  inserts the (zero) `Boundedᴺ` slack. No UC and no approximation step is spent.
- **Quantifiers** — `SerInj` first, then `PreservesValue`'s own order.
- **Assumptions** — `SerInj` (`:73`), per-level injectivity of `ser`.
  DISCHARGED for one encoding by `Serialize.serInj` (`Serialize.agda:44`),
  giving `Serialize.ideal-preserves-value′` (`:48`) with nothing assumed.
- **Kind** — instantiated (unconditional at the supplied serializer).

#### `preserves-value-transfer` — `Transfer.agda:91`

```agda
preserves-value-transfer : (a V : ℕ) (R : Systems LedgerIf^ω) → SerInj
                         → R ≤UC^ωⁿ Ideal a V → PreservesValue a V R
```

- **Compared / resources** — `R` against `Ideal a V`, both CLOSED protocol
  images at the trivial grade (`imgᶠ`, `UC/Model/Family/Emulation.agda:80`).
- **Contexts / certificates** — the premise `_≤UC^ωⁿ_`
  (`Emulation.agda:95`) is read at the embedded-strategy contexts through
  `≈ᶠ-runs` (`:161`), budget `ctxBudget q 1 = q · 1`; the conclusion is at every
  certified machine context the cap admits. `R` carries no certificate, and the
  certificate of the compiled TEST is deliberately not read — the flag is an
  internal port, so a strategy extracted from the compiled context spends only
  the honest allowance.
- **Simulator** — none retained, because `_≤UC^ωⁿ_` is direct agreement and has
  none to retain.
- **Error / allowance** — comparison and ideal bound BOTH read at `p n + 1`; the
  premise's `ε` becomes the saturated slack `λ n → ε n (p n + 1)`, quantified
  after the cap, so the conclusion's own number stays the ideal `εᴹ`. Both
  allowances exact; no schedule monotonicity spent (an arbitrary
  `NegligibleBound` has none).
- **Quantifiers** — `(p , Poly p)` first, slack second, level third, context
  last.
- **Assumptions** — `SerInj`; the emulation, which is the premise.
- **Kind** — conditional (on the emulation).

#### `ledger-preserves-value-from-hash` — `Transfer.agda:190`, with `hash-liftⁿ` `:184` and `hash-liftᵇ` `:176`

```agda
ledger-preserves-value-from-hash :
    (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≤UC^ωⁿ oracle^ω
  → PreservesValue a V (Realᴴ hash inputConsuming (genesisAt a V))
```

- **Compared / resources** — the premise compares two HASH families, `hash`
  against `oracle^ω` (`:119`); the conclusion is about the ledger built over
  `hash`. The factoring `ledger-factor` (`:131`, on `UC.Factor.factorᵖ`) is what
  exposes the hash port of the otherwise closed system.
- **Contexts / certificates** — `hash-liftᵇ` is the fixed-data lift
  (`hash ≈ᶠ[ ε ] oracle^ω → Realᴴ hash vr s ≈ᶠ[ εᴴ ε ] Realᴴ oracle^ω vr s`);
  `≈ctx-ext` (`UC/Quantitative/Family.agda:391`) absorbs the ledger stage into
  the test at its own certificate `ledgerᶠ-qb : QB 1` (`Transfer.agda:163`, one
  hash call per transaction plus the `stageᵒ` regrading), and `≈ctx-sub`
  (`Family.agda:246`) the unit regrading `λ⇒ᶜ`, also `QB 1`.
- **Simulator** — none: with one upper stage there is nothing to compose and
  nothing to forget. The port is provably blind (`docs/ledger-factoring.md`).
- **Error / allowance** — `εᴴ ε n q = ε n (simCost (simCost q 1) 1)` (`:143`),
  two EXACT `simCost` reindexings; `εᴴ-negligible` (`:146`) is two
  `NegligibleBound-simCost` applications.
- **Quantifiers** — `hash-liftᵇ` takes the schedule as an explicit parameter;
  `hash-liftⁿ` is its existential packaging, which is where negligibility is
  spent.
- **Assumptions** — `SerInj`; `hash ≤UC^ωⁿ oracle^ω`, RECORDED AND NOT
  DISCHARGED — no named hash construction in the repository supplies it
  (`docs/end-to-end.md` §7).
- **Kind** — conditional.

#### `preservesValue⇒saturated` — `Property.agda:178`

The way back: `PreservesValue R` gives, per polynomial cap, a negligible `ν`
with `Pr (R n) (auditWatch n d) ℚ.≤ εᴹ n (p n) + ν n` at every `asks≤ (p n) d`.

- **Compared / resources** — one system, read at the strategy contexts an
  ordinary strategy embeds to.
- **Contexts / certificates** — `hits⇒bounded`
  (`UC/Quantitative/EventLift.agda:186`): the closure is closed, so
  `ctxBudget q 0 = q` and the strategy keeps the whole cap.
- **Simulator** — none.
- **Error / allowance** — the same `εᴹ n (p n) + ν n`. NOTHING is spent
  returning; the monitor's extra query was charged on the way out
  (`ledger-hitsᵘ` / `hitsᵘ`).
- **Quantifiers** — the property's own (cap, slack, level, strategy).
- **Assumptions** — none beyond the property.
- **Kind** — compatibility (the strategy-level reading of the contextual bound).

#### `ledger-uc-to-pov-family` — `Transfer.agda:227`; `ledger-pov-family-negligible` `:242`; `TruthfulAudit` `:218`

```agda
ledger-uc-to-pov-family :
    SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool)
  → R ≤UC^ωⁿ Ideal a V → TruthfulAudit R badR → (p : ℕ → ℕ) → Poly p
  → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν
    × ((n : ℕ) (d : …) → asks≤ (p n) d
       → PrHit (R n) (badR n) d ℚ.≤ εᴹ n (p n ℕ.+ p n) ℚ.+ ν n)
```

- **Compared / resources** — as claim 1, but the CONCLUSION is about `R`'s own
  internal state trajectory (`PrHit`), which UC does not identify.
- **Contexts / certificates** — strategies at `asks≤ (p n) d`; the route is
  `preserves-value-transfer` → `preservesValue⇒saturated` at the doubled cap
  `λ n → p n + p n` → `Watched.withAudits` → `TruthfulAudit`.
- **Simulator** — none retained.
- **Error / allowance** — `εᴹ n (p n + p n) + ν n`, i.e. `εᴸ n (q + q + 1)`:
  the doubling is `withAudits`' honest-interface instrumentation, the `+ 1`
  inside `εᴹ` is the monitor accumulator's. This is the maintainer's 2026-09-22
  ruling (§"Decisions recorded" 1, `docs/event-bounds-in-setup.md` "Plan item 6
  — the trajectory ruling"); the older, sharper strategy-level route was retired
  deliberately and its number is NOT the public type.
- **Quantifiers** — cap first, slack second, level third, strategy last.
- **Assumptions** — `SerInj`; the emulation; **`TruthfulAudit R badR`**, which
  stays in the statement. `ideal-truthful` (`:223`) discharges it for the ideal
  family only; `liar-not-truthful` (`:363`) shows it genuinely fails of some `R`
  satisfying claim 1.
- **Kind** — conditional. `ledger-pov-family-negligible` is the same conclusion
  read as one negligible number (`Negligible-+` of `εᴹ-negligible` and `ν`).

#### `chimeric-not-preserving` — `ReplayFamily.agda:71`; `Replay.chimeric-loses-value` `Replay.agda:184`

`¬ PreservesValue a (suc (suc V)) (Chimericᶠ V)` — the negative side.

- **Compared / resources** — `Chimericᶠ V n = AtLevel.Sys n chimeric (At.s₀ V n)`
  (`:53`), the broken variant at the ACCOUNT-FUNDED initialization.
- **Contexts / certificates** — the attack strategy `At.replay V n` with
  `At.replay-asks : asks≤ 3` (`Replay.agda:105`), so the allowance is the
  constant `3` with `poly-const 3`; it is handed back a bound by
  `preservesValue⇒saturated`.
- **Simulator** — none.
- **Error / allowance** — probability exactly `1ℚ` at every level
  (`chimeric-loses-value^ω`, `ReplayFamily.agda:64`, on
  `Replay.Attack.chimeric-loses-value`, `Replay.agda:184`), against
  `εᴹ n 3 + ν n`, which both being negligible falls eventually below `½`.
- **Quantifiers** — the allowance is quantified FIRST, as the property
  quantifies it; no single security parameter is picked, so the refutation is
  asymptotic, not one numerical instance.
- **Assumptions** — none. But it is NOT a refutation at the positive theorem's
  initialization: `funded-total` (`:60`) is the equal-total side condition that
  lets one watch serve both, while `Chimericᶠ` starts account-funded and `Ideal`
  at the UTxO genesis, which `System.ledger-keeps-accts-[]` (`System.agda:119`)
  shows never reaches a funded account.
- **Kind** — instantiated negative result.

#### `ideal-spends-genesis` — `Transfer.agda:267`

```agda
ideal-spends-genesis : (a V n : ℕ)
  → Pr (Ideal a V n) (Live.spend a V n) ≡ 1ℚ
  × ((h : Ledger.Hash n) → Live.moved a V n h ≡ (((h , 0) , (a , V)) ∷ [] , []))
```

- **Compared / resources** — the ideal family alone, through the oracle.
- **Contexts / certificates** — one named strategy per level
  (`Replay.Genesis.spend`), no context quantification.
- **Simulator** — none. **Error / allowance** — none; the two components are
  exact (`≡ 1ℚ`, `≡` on the state).
- **Quantifiers** — `(a V n)` then the two conjuncts.
- **Assumptions** — NONE, at every level.
- **Kind** — instantiated positive-behaviour result. It is acceptance plus its
  state effect, not global liveness, and neither safety claim takes it as a
  premise.

#### The `Mute` / `Liar` pins — `Transfer.agda:279`, `:285`

Two checked counterexamples, both `Systems LedgerIf^ω`, both satisfying claim 1
through `never-reports` (`:297`) at slack `0`:

- `mute-preserves-value` (`:320`) with `mute-never-accepts` (`:323`): the
  observable bound does not imply responsiveness, so claim 3 is a separate job
  and not a premise of claim 1.
- `liar-preserves-value` (`:358`) with `always-bad` (`:288`) and
  `liar-not-truthful` (`:363`): a trajectory conclusion genuinely needs the
  audit connection claim 2 assumes.

**Kind** — instantiated separations. They bound what claims 1 and 2 say; they
assume nothing.

### 14.2 The audit-carry consumer — `Examples/HashForward/Audit.agda`

#### `hf-emul` — `:70`; `hf-audit-carry` — `:88`; `hf-pr-bound` — `:127`

- **Compared / resources** — `realᵒ` against `idealᵒ` at a NONTRIVIAL grade
  (`ifaceᵒ Advᴵ`), which is the point of the example; the resource
  `w : Proc unitᴵ Resᴵ` sits in the closure.
- **Contexts / certificates** — `UC.Seam.Audit.Context`'s graded audit tests:
  honest strategy `e` with `asks≤ q e`, adversary `a : Proc Advᴵ 𝟭ᴵ` with
  `QBᴹ c a`, resource `w` with `QBᴹ c′ w`. The absorbed test's certificate is
  stated explicitly, `absorbed-budget : QB (c * ((2 ⊔ 1) ⊔ 1))` (`:80`).
- **Simulator** — RETAINED and named: `simᵒ` at cost 2
  (`simQB : QB 2 simulator`, `Examples/HashForward/UC.agda:103`), and
  `simExactAll` (`:166`) says 2 is exact, not a ceiling. The
  qualitative record `_≤UC[_]_` (`UC/Audit.agda:73`) carries `sim`, `sim-qb`
  and `emulate`.
- **Error / allowance** — `(ε (simCost q 2) + δ) + η`: the designated bound `ε`
  read at the absorbed allowance, plus TWO positive slacks — `δ` from
  `pinned-bound`'s `dominate` (`UC/Audit.agda:112`) and `η` from
  `audit-carry`'s (`:208`). At the toy's own designation (`silent`) the
  designated bound is `0` and the error is the two slacks alone
  (`hf-audit-silent`, `:107`).
- **Quantifiers** — `μ`, `ε`, `δ`, `η` all fixed BEFORE any context; no
  polynomial cap (the toy has no security parameter); no simulator existential.
- **Assumptions** — none beyond `Examples.HashForward.real-factors`, which is
  proved.
- **Kind** — instantiated. `hf-pr-bound` is the same bound read as a probability
  of a raw machine's run (`Pr≤`): `real` is a raw machine, so layer 1's
  `Bounded` is not available to it.

### 14.3 The coin / commitment chain

#### `coin-toss-idealᵇ` — `Examples/CoinToss/Ideal/Compose.agda:94`; `coin-toss-ideal` `:103`; `coin-toss-idealᴺ` `:145`; `coin-hybridᵇ` `:74`; `coin-toss-idealᶜ` `:118`; `schedule-pinⁱ` `:111`

- **Compared / resources** — `(λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n)` against
  `Fcoinᶠ`, with `Examples.ROCommitment.Resource.resource` INSTALLED below both
  (`resᶠ`, `:59`), hence closed in the domain and still graded by the corrupted
  committer's port.
- **Contexts / certificates** — `_≈ctx[_]_` (`UC/Quantitative/Family.agda:100`):
  per level, every ancilla `W`, every test with `QB c E`, every closure with
  `QB c′ m`, error read at `ctxBudget c c′`. `≤UC[]-dom` at the resource
  (`Family.agda:465`) is what CLOSES the comparison boundary and is free (rate
  `0`, schedule unchanged) — required, because at an open domain the closure
  quantifier owns `F_com`'s memory.
- **Simulator** — RETAINED and named in the `ᵇ` form: `simᶜⁱ sf = simᶜᵗ sf ∘ᶜ
  simᶜᶠ` (`:91`), with `simᶜᶠ : Certified Lkᶜᶠ (Lkᶠ ⊗ᶠ Advᶜᶠ)` at cost 1
  (`:66`). `coin-toss-ideal` is the existential packaging.
- **Error / allowance** — `εᶜⁱ ε n q = εᶜᵗ ε n q + 0ℚ` (`:86`), with
  `εᶜᵗ ε n q = 0ℚ + ε n (simCost q 0)` (`Compose.agda:82`). The second hop is
  EXACT (zero schedule, `CTIU.coin-hop` across the seal), so the whole error is
  the first hop's, itself the commitment's, UNRESCALED: `ideal-ε` (`:122`) pins
  `εᶜⁱ εᶜ n q ≡ (q·q + q + q)·2⁻ⁿ`. `schedule-pinⁱ` (`:111`) is `refl`.
- **Quantifiers** — in `coin-toss-idealᵇ` the simulator and the schedule are
  explicit parameters and no negligibility is asked; `coin-toss-ideal` adds the
  existentials and `seqError-negligible`, which is where the polynomials are
  spent.
- **Assumptions** — `realᶠ ≤UC^ωᵉ idealᶠ`, the commitment's own emulation,
  UNDISCHARGED (see `binding-real` below). `coin-toss-idealᶜ` (`:118`) narrows
  the premise to the single relation the repository does not have,
  `realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ`, the other three components
  (`comSim` `Compose.agda:171`, its certificate, `εᶜ` with its negligibility)
  being present.
- **Kind** — conditional. `coin-toss-idealᴺ` (`:145`) is the same result in the
  canonical negligible `UCSetup`; it keeps the certified simulator but NOT the
  schedule (§12.4).

The corrupted-receiver twins are `Ideal/Receiver/Compose.agda`:
`coin-hybridʳᵇ` (`:119`), `coin-toss-idealʳᵇ` (`:138`), `coin-toss-idealʳ`
(`:148`), `schedule-pinʳ` (`:158`), `coin-toss-idealʳᴺ` (`:183`). The one
difference is that the second hop is NOT exact there: the honest committer's
share is drawn one activation earlier than the ideal coin's, so what is exact is
the two systems' RUNS (`Receiver.Machine.coin-runʰ`), and carrying a run
agreement into a context costs the domination's positive slack `2⁻ⁿ` — hence
`ηʰ n _ = 0ℚ + 2⁻ⁿ` (`:101`), `εᶜʳ ε n q = εᶜᵗ ε n q + ηʰ n q` (`:132`), and
`ideal-εʳ` (`:164`) pins `(q + (q + q))·2⁻ⁿ + 2⁻ⁿ`.

#### `assembly` — `Examples/ROCommitment/Realization/Assembly.agda:101`; `coin-from-Rcom` `:82`; `pin` `:111`

- **Compared / resources** — `Rcom n = realᶠ n ∘ resᶠ n` against
  `Icom n = idealᶠ n ∘ resᶠ n` (`Realization/Statement.agda:34`, `:37`), the
  resource-installed boundary; `Assembly` (`:57`) is the implication from
  `Realization` to the coin conclusion.
- **Contexts / certificates** — `RcomQB`/`RcomʰQB : QB 0` (`:56`, `:59`), the
  resource's `QB 0` swallowing the product; `coin-from-Rcom` is `UC-composeᵉ`
  with the upper stage compared with ITSELF (`idᶜ` at the zero schedule) and
  both moved morphisms closed.
- **Simulator** — the premise's, unchanged: `≤UC^ωᵉ-dom` is NOT spent here (the
  premise is closed already), and the associativity gap is repaired by
  `≤UC^ωᵉ-resp`, which keeps the same simulator and schedule.
- **Error / allowance** — unchanged: `pin`/`pinʰ` are `refl`, so moving the
  boundary changes no number.
- **Quantifiers** — `Assembly` is stated as an implication, so the premise's
  existentials are consumed and re-emitted.
- **Assumptions** — `Realization`/`Realizationʰ`
  (`Statement.agda:50`-`:52`) are HYPOTHESES, not theorems.
- **Kind** — conditional.

#### `binding-real` — `Examples/ROCommitment/Realization/Bound.agda:203`

```agda
binding-real : (m : ℕ) (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ))) → asks≤ m d
             → Σ[ n ∈ ℕ ] ((i : ℕ) → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ (mapStrat toQ fromR d))
                                       -ℚ cum (n + i) (runᴹ (real 𝒫.∘ resource) d) (indᵇ true) ∣ℚ
                                     ≤ℚ ε m)
```

- **Compared / resources** — the closed real MACHINE `real 𝒫.∘ resource` against
  the PRUNED IDEAL GAME `runWith⊥ respI⊥ sI₀`, over the concrete resource.
  These are not two machines: one side is a game.
- **Contexts / certificates** — distinguishers `d` with `asks≤ m d`, relabelled
  to the game's alphabet by the checked bijection `toQ`/`fromR`
  (`Realization/Bisim.agda`, B2-M7) with `asks≤-mapStrat` (one ask stays one
  ask).
- **Simulator** — none on this leg; the ideal side is `Game`'s, not the UC
  simulator.
- **Error / allowance** — `Game.ε m` (`Game.agda:566`), through `Game.cert`
  (`:569`) and `prune-cert`.
- **Quantifiers** — `m` and `d` first, then the `cum` index.
- **Assumptions** — none added; but see the defect below.
- **Kind** — instantiated, and PARTIAL. It is a real-machine/ideal-GAME bound.
  It is NOT a full machine realization: the ideal leg of the bisimulation
  (B2-M3, `docs/rcom-icom-b1.md` §7) is blocked by the `simStep` defect, so
  `Realization` is not obtained from it.

### 14.4 The generic API

#### `_≤UC[_,_]_` — `UC/Quantitative/Family.agda`

`f ≤UC[ s , ε ] g = f ≈ctx[ ε ] subᶠ s g`. A definitional alias, so every
existing comparison inhabits it with no transport and no new assumption, and
`_≤UC^ωᵉ_` is literally
`Σ[ s ∈ Certified Y X ] Σ[ ε ] NegligibleBound ε × f ≤UC[ s , ε ] g`. The bound
itself asks nothing of `ε`. **Kind** — definition; the primary quantitative
interface (§12).

#### `≤UC[]-trans`; `≤UC[]-compose`, `≤UC[]-compose′`

- **Compared / resources** — three (resp. four) families; nothing installed.
- **Contexts / certificates** — `_≈ctx[_]_`'s: an `Image forget c E` (`c : ℕ⁺`) for
  the test and an `Image forget r′ m` for the closure. `≤UC[]-compose` additionally
  requires certificates for the two morphisms it MOVES: `Image forget (rf n) (f n)`
  (into the closure) and `Image forget (rtv n) (subᶠ t v n)` (the simulated
  continuation, into the test); `≤UC[]-compose′` takes `Image forget (rv n) (v n)`
  instead and certifies the composite at `rv n · cost t n`. None takes a
  certificate of the compared homs.
- **Simulator** — OUTPUT DATA, named: `s ∘ᶜ t` for `≤UC[]-trans`;
  `composeSim sf t` for `≤UC[]-compose`, at rate `cost sf n · cost t n`.
- **Error / allowance** — `seqError s ε δ n q = ε n q + δ n (scale q (cost s n))`;
  `composeError rf rtv εf εu n q = εu n (scale q (rf n)) + εf n (scale q (rtv n))`.
  Every substitution is EXACT; no schedule monotonicity and no `Allowance-mono`
  premise anywhere. `≤UC[]-compose′` reads `εf` at `q · rv n · cost t n`, which
  at a zero-count `v` is coarser than the old `q · (cost t n ⊔ 1) · cv n`; a
  sharper certificate of the composite goes through `≤UC[]-compose` as it stands.
- **Quantifiers** — the split IS negligibility: neither theorem takes a
  `NegligibleBound` or a `Poly⁺`; `seqError-negligible` and
  `composeError-negligible` are where `NegligibleBound-scale` and
  `GradedBound-+[_]` are spent and where `Poly⁺ rf`/`Poly⁺ rtv` are consumed.
  The existential forms `≤UC^ωᵉ-trans` and `UC-composeᵉ` package them, the
  latter through `≤UC[]-compose′`, whose existential error absorbs the coarser
  `rtv`.
- **Assumptions** — none. **Kind** — unconditional metatheory.

#### `≤UC[]⇒≤UCᴺ` — `UC/Model/Family/Emulation.agda:149` (module opened at `:134`)

- **Compared / resources** — two families certified levelwise at a `Poly⁺` rate
  schedule, as `Famᴹ` arrows.
- **Contexts / certificates** — the premise's `≈ctx`, plus such a schedule on
  each compared family — the only thing this boundary adds.
- **Simulator** — RETAINED: `certᶠ s` (`:126`) is a `Fam`-hom, which is what the
  inherited order asks a simulator to be.
- **Error / allowance** — the route stops at `_≈ℰⁿ_` (`≤UC[]⇒≈ℰⁿ`, `:141`) and
  is read in `ucSetupᴺ`'s own kernel; it does NOT go through vanishing and
  spends no `absorb-negl`. The single GLOBAL schedule does not survive: `≈ℰⁿ⇒≈ℰᴺ`
  specializes it to the allowance each context carries, so `Canonicalᴺ._≤UC_`
  records only a negligible witness chosen INSIDE the contextual quantification,
  and no theorem recovers a global one (§12.4). A consumer that needs the number
  keeps the `_≤UC[_,_]_` data.
- **Quantifiers** — simulator, schedule, negligibility, caps, all before the
  conclusion; no slack.
- **Assumptions** — none. **Kind** — compatibility (a forgetful crossing).

#### `Refine.≈ᵁ-refine` / `≤UC-refine` — `Abstract2/Morphism.agda:131`, `:134` (module `:117`, `reobserve` `:106`)

- **Compared / resources** — the SAME two homs, read in two setups over the same
  `𝒞`, `ℐ`, `ℳ` and differing only in the environment presheaf. Carrier/action
  compatibility is not asserted, it is ELABORATED: each application forces
  `reobserve 𝕊 ℰ′` to be convertible with the target setup.
- **Contexts / certificates** — both setups read `_≈ᵁ_` at the same prefix
  contexts `μ ∘ T₁`; the hypothesis `refineℰ` is a refinement of the BARE
  kernel, not of environments.
- **Simulator** — crosses UNCHANGED, with its certificates: `≤UC-refine` is
  `≤UC⇒dummy` followed by `dummy-complete`.
- **Error / allowance** — none; this layer is qualitative.
- **Quantifiers** — `refineℰ` fixed at module application, before any hom.
- **Assumptions** — `refineℰ`, supplied by each instance's kernel step. No
  `GradeStable` and no epi/mono side condition, unlike `Transfer`.
- **Kind** — compatibility. Six instances, statements byte-identical
  (`UC.Family.Quantitative:75,79,89,94`; `UC.Family.Negligible.Quantitative:89,93`).
  The vanishing pair has both directions; the uniform/local pair has only
  `uniform⇒local`, and no uniformization premise was introduced for the converse.

#### `audit-carryᵉ` — `UC/Audit.agda:172`; `audit-carry` — `:208`

- **Compared / resources** — `f : A ⇒ X ⊗₀ B′` against `g : A ⇒ Y ⊗₀ B′` at an
  arbitrary monoidal base with an `Evaluation`, a `GradedSubCat` over `Rates`
  and a `Mass`;
  the one application is `UC/Seam/Audit.agda:25`-`:31`.
- **Contexts / certificates** — every `(W, Et, m)` with `Image forget c Et`,
  `Image forget r′ m`; ADMISSION is the event class `𝔈` on the real side and
  `𝔉` on the ideal side, joined by `Absorbs s r 𝔈 𝔉`. The simulator's
  `Image forget r s` is essential, because the simulator ends up inside the
  environment leg.
- **Simulator** — RETAINED: `s` is explicit in `audit-carryᵉ` (no existential);
  `audit-carry` carries it in the `_≤UC[_]_` record (`:73`).
- **Error / allowance** — `audit-carryᵉ` concludes at `λ q → δ (scale q r) +
  ε q`: the two allowances stay visible and DIFFERENT, `ε` at the real context's
  `value (c · r′)` and `δ` at the absorbed one's `value (r · c · r′)`, which
  `*-assoc`/`*-comm` identify with `scale (value (c · r′)) r`; the substitution
  is exact (`subst`, twice).
  `audit-carry` concludes at `λ q → ε (scale q r) + δ` —
  the summands swap roles, `δ` there being a CONSTANT positive slack from
  `dominate`.
- **Quantifiers** — `ε`, `δ` fixed before every context; no polynomial cap.
- **Assumptions** — the premise relation is NOT a symmetric approximate
  equality: it is an unnamed, directed, one-sided MASS domination, plus the
  ideal-side `AuditBound g 𝔉 δ`. WP1 forbids strengthening it to a symmetric
  premise; WP1's verdict (`docs/uc-presheaf-preservation-plan.md`) kept the
  local proof after measuring the generic alternative at net +67 lines.
- **Kind** — unconditional metatheory, with one in-repo client each.

#### `UC.Robust.uc-preserves` — `UC/Robust.agda:110`

- **Compared / resources** — `f` against `g` at an arbitrary `UCSetup`; nothing
  numerical is in play.
- **Contexts / certificates** — `Admissible B d` (`:56`), a class of
  environments; no query bound, no resource certificate.
- **Simulator** — supplied by `≤UC⇒dummy` and immediately passed to
  `uc-preserves-at` (`:104`), which takes it EXPLICITLY — because a class that
  is not closed under arbitrary simulators must not obtain closure merely from
  `f ≤UC g`.
- **Error / allowance** — none.
- **Quantifiers** — `((s : Y ℐ.⇒ X) → ClosedUnder Adm s)` is quantified over
  every simulator, before the order.
- **Assumptions** — `ClosedUnder Adm s`, a PREMISE. Nothing is claimed about a
  simulator being silent, total or bounded.
- **Kind** — unconditional metatheory. `uc⁺-preserves` (`:120`) is the
  adversary-attached form at `_≤UC_`'s own quantifier order.

#### `UC.Core.Bridge.≤UCᶜ⇔≤UC` — `:33`

A two-way identification between the core's dummy-form order and the inherited
one, at one setup. No error, no certificate, no simulator existential beyond
`≤UC⇒dummy`/`dummy-complete`. **Kind** — compatibility (equivalences, so nothing
is lost either way).

#### The point-level arrows, and which of them are equivalences

The chain from ambient machine equality down to the numerical comparison, with
its kind on each arrow:

| from | to | by | kind |
|---|---|---|---|
| ambient machine equality `_≈ᴹ_` | exact equality of closed readings | `UC.Model.Observation.obs-resp` (`:78`) | implication |
| exact observation equality | zero-error Boolean comparison `≈ₚ[ 0 ]` | `≈ₚ⇒≈ₚ[0]` | implication |
| zero-error comparison | all-positive-error closeness | identity — the model's readout is `qual₊`, so `_∼_` already IS closeness at every positive error and `UC/Model/Family/Contextual.agda` supplies `reflects = λ h → h` | definitional |
| `_≈ctx[_]_` | `_≈ctxᴬ[_]_` (operational bracket) | `≈ctx⇒≈ctxᴬ`, `≈ctxᴬ⇒≈ctx` (`UC/Quantitative/Family.agda`) | **equivalence**, at the cost of one structural morphism at rate `1⁺` (the test's certificate `c ↦ 1⁺ · c`, regraded back to `c` by `L.sub[_]`) |
| `_≈ctxᴬ[_]_` (per level) | `_≈ℰ[_]_` (family of contexts, one polynomial) | `≈ctxᴬ⇒≈ℰ[]` `UC/Model/Family/Emulation.agda:108` | implication ONLY — not an identification |
| `_≤UCᶜ_` | `_≤UC_` | `UC/Core/Bridge.agda:33` | **equivalence** |
| one setup's `_≈ᵁ_`/`_≤UC_` | a reobserved setup's | `Refine` `Abstract2/Morphism.agda:131`, `:134` | implication, conditional on `refineℰ` |
| `_≤UC[_,_]_` (global schedule) | `Canonicalᴺ._≤UC_` (per-context witness) | `≤UC[]⇒≤UCᴺ` `Emulation.agda:149` | implication ONLY — the schedule is not recoverable (§12.4) |

No arrow is drawn between expressions of different types without its
interpretation map: the two family bridges that look like they compare
different setups (`UC.Family.Quantitative`, `UC.Family.Negligible.Quantitative`)
are `Refine` instances, which forces the two setups' `𝒞`, `ℐ` and `ℳ` to be
convertible on the nose (§13).

### 14.5 The six checks

1. **The ledger headline uses the compiled observable event, and trajectory
   conclusions retain their truthfulness premises.** PASS.
   `PreservesValue R = Hitsᴺ … auditMonitorᶠ εᴹ` (`Property.agda:150`) is
   `BoundedAt` at `readoutᴹ` of `monitorᴹ (Watched.reportsLoss …)`, a process on
   the ledger interface that reads only queries and answers; the compiled
   experiment's verdict IS the flag. `TruthfulAudit` (`Transfer.agda:218`) is an
   explicit premise of `ledger-uc-to-pov-family` (`:227`) and
   `ledger-pov-family-negligible` (`:242`), discharged only for the ideal family
   (`ideal-truthful`, `:223`) and refuted for `Liar` (`liar-not-truthful`,
   `:363`).
2. **The `q + 1` route is not described as a universal lower bound.** PASS after
   the correction below. Established: `eventDominatedᵘ`
   (`UC/Quantitative/EventLift.agda:142`) and `hitsᵘ` (`:158`) are `--safe`
   theorems at `c + 1` / `q + 1`, and the `c + 1` lift is discharged by
   `covCtx` (`EventLift/Cov.agda:308`). The rate-`c` refutation is a SCHEME
   about `covCtx`'s certificate — the collapsed tower — not a machine-checked
   `¬`, and not a statement about every `QB c` certificate of the compiled
   context. NOT established: any lower bound over certificates (`QB c M`
   quantifies the representative, and `eventDominatedᶜ` (`:122`) quantifies both
   the rate `k` and the certificate `kb`), and any lower bound over lifts (the
   all-zero-potential-state quantifier is a design choice forced by
   `dom≤-bind`'s everywhere-quantification, and the refutation does not survive
   restriction to the initial support). Source correction made by this work
   package: `EventLift.agda:135`-`:143`. The historical line "`c + 1` is optimal
   for the invariant" in `docs/event-bounds-in-setup.md` "Stage B status,
   corrections 2026-09-22 (2)" is left as a dated record and is superseded by
   this check.
3. **Global quantitative schedules, local negligible witnesses and vanishing
   observations are not conflated.** PASS. Three tiers, named apart:
   `_≤UC[_,_]_`/`_≤UC^ωᵉ_` carry ONE global schedule read at each context's
   carried allowance; `≤UC[]⇒≤UCᴺ` (`Emulation.agda:149`) lands in
   `Canonicalᴺ._≤UC_`, which keeps only a per-context negligible witness and
   from which no theorem recovers the global schedule (§12.4); the vanishing
   collapse is NOT on this route — `≤UC[]⇒≤UCᴺ` spends no `absorb-negl`
   (`UC/Family.agda:313`, which survives for other callers), and the route that
   did, `≤UC^ωᵉ⇒≈ℰᶠ`, was retired 2026-09-22.
   `≈ctxᴬ⇒≈ℰ[]` (`Emulation.agda:108`) is a named implication from the
   per-level relation to the family-of-contexts one, not an identification (§3).
4. **Query certificates are not described as polynomial local-runtime bounds.**
   PASS. `QB c M` (`UC/QueryBound.agda:287`) is
   `Σ[ N ] Certified c N × N ≈ᴹ M` — a bound on downward QUERIES per activation
   of some representative, nothing about time. `Poly`/`Poly⁺` classify how a
   query count or rate grows in the security parameter, and `scale` (on this
   branch; `ctxBudget`/`simCost` on `protocol-rewrite`) is arithmetic on query
   allowances. No module claims a runtime, and
   `docs/end-to-end.md` §7 records the absence of a bounded-machine notion as
   not delivered. In particular `qb-closed : (M : Proc unitᴵ B) → QB 0 M`
   (`UC/QueryBound.agda:293`) says a closed process makes no DOWNWARD query; it
   does not say it does no internal computation, and it does not characterize
   faithful resources. The `QB 0` certificates the coin assembly rests on
   (`RcomQB`, `IcomPolyQB`, `FcoinQB`, `resourceQBᵒ`) are all of that kind.
5. **The commitment result is not called a full machine realization.** PASS.
   `binding-real` (`Realization/Bound.agda:203`) bounds the closed real MACHINE
   against the pruned ideal GAME. `Realization`/`Realizationʰ`
   (`Realization/Statement.agda:50`-`:52`) remain hypotheses and
   `assembly`/`assemblyʰ` remain conditional. **BLOCKER, still listed:** the
   repeated-query simulator-log defect at `Examples/ROCommitment.agda:193`-`:214`
   — `simStep` conses `(x , d)` onto the simulator's log at EVERY relayed
   answer, including one the oracle served from its table, so after a repeated
   query the log holds the digest twice and `extract` reads `false`
   (`Realization/Bisim.agda`, `extract-relog` vs `extract-table`), while the
   game's bad event is `dup` of the ORACLE's answer log, which a repeat does not
   raise. Maintainer call recorded at `docs/rcom-icom-b1.md` §7 row B2-M3: either
   `simStep` caches, or `Game.respI` is restated over the relay log — the second
   makes `Game.cert` false. B2-M4 (`binding-bound`) is blocked behind it.
6. **Retired proof routes are not cited as current gate evidence.** PASS for the
   two current documents. No module under `src/` names `UC.Saturated`,
   `UC.Asymptotic*`, `UC.Quantitative.Hits`, `UC.Machine.Monitor.Tight`,
   `UC.Seam.Carry`, `Protocol.Live` or `Charge` (grepped; the last such comment,
   on `covCtx`, was corrected in WP3). `docs/end-to-end.md` and §§1-13 above were
   brought to `cee4efca` by this work package. The remaining occurrences are in
   historical plans and logs, listed in §14.7; none of them is cited by a
   current statement as evidence.

### 14.6 Deferred assumptions

1. **The real-hash assumption.** `hash ≤UC^ωⁿ oracle^ω`, the premise of
   `ledger-preserves-value-from-hash` (`Transfer.agda:190`). RECORDED, NOT
   DISCHARGED: no named hash construction in the repository supplies it.
   `Examples.MerkleDamgard.indistinguishable` (`MerkleDamgard.agda:253`) is
   stated at `≈adv[_]` over fixed-length messages where the ledger hashes
   bitstrings, so an instance wants a padding adapter and then a `_≤UC^ωⁿ_`
   proof. This consolidation neither discharges nor replaces the premise.
2. **The `simStep` defect.** `Examples/ROCommitment.agda:193`-`:214`, as in
   check 5. Until it is resolved, `Realization`/`Realizationʰ` stay hypotheses
   and the whole coin chain above them is conditional.
3. **The chimeric verdict at the UTxO genesis.** `chimeric-not-preserving`
   refutes the family property at an ACCOUNT-FUNDED initialization, and
   `System.ledger-keeps-accts-[]` (`System.agda:119`) shows a run started at an
   empty account table never reaches one (the per-activation statement is what
   is checked; the induction along a whole run is not a theorem here). Whether
   the chimeric variant preserves value AT the UTxO genesis is open.

### 14.7 Historical documents naming retired modules

Each of these is a dated plan, verdict or migration log and keeps the names that
were current when it was written. None is a current statement of the theory; the
retirement ledger itself is `docs/event-bounds-in-setup.md` §"Retired 2026-09-22"
and its two orphan sweeps.

- `docs/coin-toss.md` — `UC.Asymptotic.Compose`, `UC.Asymptotic.Family.≤UC^ωᵉ⇒≤UCᴺ`.
- `docs/consumer-migration.md` — `UC.Asymptotic.Audit`/`.Compose`, `Allowance-mono`.
- `docs/direct-extraction.md` — `UC.Asymptotic.Audit`.
- `docs/dp-transport.md` — `UC/Asymptotic/`.
- `docs/event-bounds-in-setup.md` — all of them; it is the retirement log.
- `docs/fcom-extraction.md` — `UC.Asymptotic.Family`.
- `docs/fcom-hiding.md` — `UC.Asymptotic.Family`.
- `docs/fcom-uc.md` — `UC/Asymptotic/Contextual.agda`.
- `docs/graded-bridge.md` — `UC.Asymptotic.*`.
- `docs/graded-observation-redesign.md` — `UC.Saturated`, `SaturatedBoundedᴺ`.
- `docs/hash-forward.md` — `UC.Asymptotic.Audit._≤UC^ω[_]_`.
- `docs/issue-quantitative-uc-resources-and-migration.md` — `UC.Asymptotic.Contextual`/`.Compose`.
- `docs/ledger-factoring.md` — `UC.Asymptotic._≤UC^ω_`, `UC.Asymptotic.Audit.uc-audit-carry`.
- `docs/ledger-lift-eps.md` — `UC.Asymptotic.Compose`/`.Contextual`/`.Family`.
- `docs/prefix-tolerant-audit-plan.md` — `UC.Saturated`, `UC.Asymptotic.Audit`.
- `docs/protocol-implementation-review.md` — `SaturatedBoundedᴺ`.
- `docs/protocol-rewrite-abstraction-notes.md` — `UC.Saturated`.
- `docs/protocol-rewrite.md` — `UC.Asymptotic`/`.Audit`, `SaturatedBoundedᴺ`, `Seam.Carry`, `Allowance-mono`.
- `docs/rcom-icom-b1.md` — `UC/Asymptotic/Compose.agda` (`:91`), `UC/Asymptotic/Contextual.agda` (`:49`), both as the sealed-instance path beside the still-correct `UC/Quantitative/Family.agda`; read them as `UC/Model/Family/Contextual{,/Compose}.agda`.
- `docs/retirement-negligible-order.md` — `UC.Asymptotic.Audit`.
- `docs/retirement.md` — `UC.Asymptotic.Audit`/`.Family`, `Allowance-mono`.
- `docs/rewrite-verdict.md` — `UC.Saturated`, `UC.Seam.Carry`.
- `docs/stduc-supersession-plan.md` — `UC.Saturated`, `UC.Seam.Carry`.
- `docs/uc-observation-and-relation-consolidation.typ` — `UC.Asymptotic*`.
- `docs/uc-presheaf-preservation-plan.md` — `UC.Asymptotic.Family`/`.Audit`/`.Contextual`.

## 15. Observable and Evaluation (2026-09-23)

`UC.Core.Observation` — a record bundling `𝟙 Ω : Obj`, `Obs : Set`, `⟦_⟧`, an
equivalence `_∼_` and `⟦⟧-resp-≈` — is gone. What the UC layer asks of its
ambient category is now split in two tiers.

### 15.1 Tier 1, generic: `Observable` and `Im θ`

`UC.Core.Observable 𝒞 c ℓ′` is a result object, a setoid-valued presheaf of what
a test may show, and a readout out of the representable:

```agda
record Observable {o ℓ e} (𝒞 : Category o ℓ e) (c ℓ′ : Level) where
  field
    Ω : Obj
    P : Presheaf 𝒞 (Setoids c ℓ′)
  module P = Functor P
  field
    θ         : {A : Obj} → Func (hom-setoid {A} {Ω}) (P.₀ A)
    θ-natural : {A B : Obj} (f : B ⇒ A) (t : A ⇒ Ω)
              → Setoid._≈_ (P.₀ B) (θ ⟨$⟩ (t ∘ f)) (P.₁ f ⟨$⟩ (θ ⟨$⟩ t))
```

`θ` is a per-object setoid map plus its naturality equation rather than a
natural transformation, so that `P` may live in `Setoids c ℓ′` at levels of its
own — which is what lets the instance below use the stdlib `Func` setoid. The
transformation is derived inside the record as

```agda
Θ : NaturalTransformation (LiftSetoids c ℓ′ ∘F Hom[ 𝒞 ][-, Ω ]) (LiftSetoids ℓ e ∘F P)
```

— both sides lifted to the join, since `P` and the representable live in
different `Setoids` universes. That definition is the only place `LiftSetoids`
or `Lift` appears in `UC/`. `P` is not in general a `Presheaf 𝒞 (Setoids ℓ e)`,
so the library Yoneda lemma does not instantiate and `θ ≅ P Ω` stays a remark in
`UC/Test.agda`'s header.

`UC.Test 𝒞 T` builds the environment presheaf as the IMAGE of `θ`:

```
ℰᴼ = Im θ = Hom[-, Ω ] / ker θ,     t ≋ u  =  θ t ≈_{P A} θ u
```

`P` itself must NOT be used as `ℰ`: its equality compares arbitrary elements of
`P A` and is strictly finer than observational agreement.

`UC.Environment` (`SameTV`, `Tests`, `tv₁`, `ℰᵗᵛ`, `_≈ℰ_`, the two
congruences, `grade-stable`) and `UC.Core.Bridge` (`plug`, `shuffle⇒`,
`shuffle⇐`, `≈ℰᶜ⇔≈ᵁ`, `≈ᴳ*`, `≤UCᶜ⇔≤UC`) are parameterized by `Observable`
alone. No closure is named in either: every reassociation of a closure under an
ancilla became one `pull`/`P.F₁`, and the closure quantifier is internal to
`P`. `shuffle⇒`/`shuffle⇐` lost their spectator `∘ m`; a consumer recovers the
old bracketing with one `⟩∘⟨refl`.

### 15.2 Tier 2, the instance: `Evaluation`

```agda
record Evaluation {o ℓ e} (𝒞 : Category o ℓ e) (cs ℓs : Level) where
  field
    J Ω  : Obj
    S    : Setoid cs ℓs
    eval : Func (hom-setoid {J} {Ω}) S
```

with `read = Func.to eval`, `read-resp = Func.cong eval`, `read-cast`,
`Closure A = J ⇒ A`, `observe t m = read (t ∘ m)`, `transpose`, and

```agda
P₀ A = Function.Relation.Binary.Setoid.Equality.setoid (hom-setoid {J} {A}) S
```

— the stdlib `Func` setoid, written out rather than as `Hom[ Setoids ][-, S ]`
because `S` and the hom-setoids live in different `Setoids` universes.
`Pᴱ : Presheaf 𝒞 (Setoids _ _)` has `F₁ f k = k ∘ (f ∘_)`, and
`observable : Observable 𝒞 (ℓ ⊔ e ⊔ cs ⊔ ℓs) (ℓ ⊔ ℓs)` is `Pᴱ` with `θ` the
transpose. `J` is NOT assumed to be the monoidal unit; the only place the unit
appears is `UC.Core.Bridge.plug`, where it is the trivial ANCILLA.

Because `P₀`'s equality IS `∀ m → k ⟨$⟩ m S.≈ k′ ⟨$⟩ m`, `UC.Test._≋_` at this
instance IS `(m : Closure A) → observe t m S.≈ observe u m`: there is no
unfolding lemma and no conversion at any consumer. `UC.Evaluation M R` is
`UC.Core.Bridge` at `Evaluation.observable R` plus the two statements that do
name a closure and cannot be phrased through `P`: `≈ℰ-at` and `≈ᴳ-at`.

### 15.3 The quantitative twin

`Approx.Evaluation E` (over an `OrderedErrorAlgebra`) carries

```agda
record QEvaluation (𝒞 : Category o ℓ e) (cs ℓa : Level) where
  field
    J Ω   : Obj
    X     : ApproxSpace cs ℓa
    eval₀ : Func (hom-setoid {J} {Ω}) (zeroSetoid X)
```

— the reading lands in an APPROXIMATE space and observes the ambient hom
equality EXACTLY. Forgetting the error leaves the reading untouched and only
coarsens its equality: `qualBy Q eqv coarsen` takes any equivalence that zero
error already implies, `qual = qualBy Q (zeroSetoid …) id`, and
`qual₊ = qualBy Q ∼ᵃ-isEquivalence zero⇒positive`. Because `qualBy` never
touches the carrier or the reading, `Evaluation.read (qualBy Q _ _)` IS
`QEvaluation.read Q`.

`UC.Approximate` keeps `ErrorAlgebra`, `Approximation` and `Mass` (now over an
`Evaluation`); `ApproximateObservation`, `Induced`, `induces` and `⟦⟧-resp-≈₀`
are deleted. The two constructors that used `Induced` are now `QEvaluation`s:
`UC.Machine.QEvaluationᴹ` (with `Evaluationᴹ = qual₊ QEvaluationᴹ`) and
`UC.Model.Observation.qevaluationᵒ` (with `evaluationᵒ = qual₊ qevaluationᵒ`).
The asymptotic family's is `UC.Family.QEvaluation^ω` /
`Evaluation^ω = qual₊ QEvaluation^ω`, and the negligible tier's
`UC.Family.Negligible.Evaluationᴺ` is `qualBy` of `QEvaluationᴺ` at the
negligible class instead of at `qual₊`.

`UC.Quantitative.Observed` is parameterized by `(E, qro, ∼-isEquivalence,
∼-from-zero)` — the readout plus the coarsening — and forms the same
`Approx`-valued test presheaf `Q` as before.

### 15.4 The compatibility theorems

Both forgetful functors of `Approx.Forget` say the same thing: forgetting the
error from the quantitative tests gives the qualitative test setoid of the
corresponding coarsening. At `qual` the two sides are now the SAME relation —
`⟦ spaceᵗ A ⟧₀`'s equality and `UC.Test._≋_` at `qual qro` are one and the same
`∀ m → observe E₁ m ≈[ ε₀ ] observe E₂ m`, so the former `Q₀⇔ℰ₀` has no content
left and is gone. At `qual₊` the quantifier order still differs, and that is the
statement, with `Plus = Evaluation (qual₊ qro)`:

```agda
Q₊⇔ℰ₊ : {E₁ E₂ : Test A}
      → Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E₁ E₂
      ⇔ Setoid._≈_ (Plus.P₀ A) (Plus.transpose E₁) (Plus.transpose E₂)
Q₊⇔ℰ₊ = mk⇔ (λ h m ε pos → h ε pos m) (λ h ε pos m → h m ε pos)
```

It is unconditional (it does not cost `induces`). Both models use the `F₊`
reading: `evaluationᵒ`, `Evaluationᴹ` and `Evaluation^ω` are all `qual₊`.

Small-error collapse stays one-way: `Absorbing.absorbᵘ` and `∼₊⇒≋` need
`induces`, `≋⇔∼₊` needs `reflects` as well, and nothing here claims a converse
for an existentially quantified slack.

### 15.5 Dependency structure

```
category 𝒞 + Ω + (P, θ)                          -- UC.Core.Observable
      → observational test presheaf Im θ         -- UC.Test
      → UC.Environment / UC.Core.Bridge          -- generic, no closures
      → Std(Q)UCSetup and the inherited theory   -- Standard2 / Abstract2
```

and the instance leg

```
Evaluation (J, Ω, S, eval)   → Observable        -- UC.Core
QEvaluation (J, Ω, X, eval₀) → Evaluation        -- Approx.Evaluation (qual/qual₊/qualBy)
                             → UC.Quantitative.Observed
```

## 16. Resource grading (2026-09-25)

`UC.Budget` is gone from the integration branches; the resource interface is a
graded wide subcategory `Rg : GradedSubCat Rates.monoidalCategory M qs` over the
positive naturals `ℕ⁺` (`Data.Nat.Positive`), which every consumer takes and
opens itself: a process certified at RATE `r` is an `L.Hom r`, interpreted by
`⌊_⌋`; composition and `_⊗ʰ_` multiply rates and the structural maps sit at
`1⁺`. Test allowances are rates as well: a test is admitted at `c : ℕ⁺` by an
`Image forget c E` certificate, a test moved along a certified morphism by the
`L`-composite, and a hom at its own rate by `(h , Equiv.refl)`. A separate
`ℕ`-valued count interface would be redundant — every count was a quantified
hypothesis or read off a rate — so zero-query tests have no allowance of their
own. A context's allowance is `value (c · r′)`, the test's rate times the
closure's; the error schedules stay indexed by `ℕ` and are reindexed by
`scale q r = q * value r`, with `scale-·`, `scale-comm`, `scale-unit`.
`Approx.Filtered` is generic in its allowance poset, which the query model
instantiates at `ℕ⁺`. A moved process is asked for `Image forget r f` and the
theorem stays about the bare `f`. The family category and its monoidal
structure are `Categories.LocallyGraded.Family` at `Poly⁺`.

Statements changed, by item of the migration plan: 9-14 (`PolyQB`, `qb1`,
`qb-⊗₁`, `ctxQB` deleted; `_⇒^ω_` at a `Poly⁺` rate schedule; `qbOf` ↦
`schedOf`); 15-18 (`_≈ℰ[_]_`, `CarriedNegligible` quantify every polynomial rate
`pc : ℕ → ℕ⁺` certifying the test, read at `value (pc n · schedOf m n)`); 19-20
(the two absorptions, as schedule equalities in the closure rate); 21-22
(`QueryBounds`, `fromBudget`, `guardᵠ`, `pullᵠ⁺` deleted; closure schedules
indexed by `ℕ⁺`; `𝒞ᵇ` the Σ-total of `L`); 23-29 (`Image` hypotheses at
`c : ℕ⁺`, allowance `value (c · r′)`); 30 (`≈ctx-dom`, `≤UC[]-dom`, `≤UC^ωᵉ-dom` at
`Image forget 1⁺`, strictly weaker); 31-35 (`composeSim` at `cost sf n · cost t n`,
`composeError rf rtv`, `≤UC[]-compose′`, `UC-composeᵉ`/`≤UC^ωᵉ-∙` from `v`'s
certificate).
