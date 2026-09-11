# Superseding the qualitative UC core by StdUC

Maintainer's ruling: the hand-rolled qualitative core (`UC.Core`, `UC.Environment`,
`UC.Emulation`) is to be **superseded** by the inherited metatheory — `UCSetup` +
`Abstract2.AbstractUC`, reached at the machine model through `Standard2.StdUC`.
This reverses the direction recorded in `docs/protocol-rewrite.md`'s
"Reconciliation with the inherited abstract layer" section, which concluded
"supersession, then, is one-way: … the new core supersedes them for anything
built on this branch".  That section's *dictionary* is still correct; its
*verdict* is superseded by this file, and one row of the dictionary is wrong
(see finding F1).

Phase 1 (this file's subject) is the foundation: the unit bridge, the bridge
theorem, and this inventory.  Nothing was deleted or re-homed.  One existing
module was touched, and only to name the two new ones: `UC/Model.agda` gains two
`import` lines and two header rows, so that it stays the single closure root for
the whole cone.  Nothing else in `src/` changed; the escape-hatch grep over
`src/` is 21, the baseline.

## 1. Phase-1 deliverables

### 1.1 The unit bridge — `UC/Model/Unit.agda`

`UC.Model.Observation`'s header records that closures are taken at
`𝟘ᵒ = ifaceᵒ unitᴵ` rather than at `𝔾ᵒ`'s monoidal unit `𝟘ᵘ`, that the two are
the empty interface spelled with two different empty types, and that

> That the two objects are isomorphic in `𝔾ᵒ`, hence that the choice is
> immaterial, is NOT proved here … Nothing downstream depends on it.

The honest phase-1 result is the second half of that sentence: **no iso is
needed, and the reason is structural rather than accidental.**  Two halves.

`AnyEnvironment` — *the metatheory is blind to the closure object.*  `StdUC`
consumes `ℰ` abstractly, so the whole inherited output (`≤UC-refl`,
`dummy-complete`, `≤UC-trans`, `UC-compose`, `≈ᵁ⇒≈ℰ`) is available at an
**arbitrary** presheaf over `𝔾ᵒ`:

```agda
module AnyEnvironment (ℰ : Presheaf ∣𝔾ᵒ∣ (Setoids (suc 0ℓ) (suc 0ℓ))) where
  open StdUC 𝔾ᵒ ℰ
  refl-at … dummy-at … trans-at … compose-at … collapse-at
```

Whatever closures `ℰ` quantifies over never enter a statement.  `𝟘ᵘ` *does*
enter — it is `ℐ.unit`, and `≈ᵁ⇒≈ℰ` spends `λ⇒`/`λ⇐`/`return` at it — but only
in **grade** position, and the grade position never meets the closure position.
That is the whole content of "everything factors through `𝟘ᵒ`".

`Interconvert` — *what the identification would buy*, proved over an abstract
iso rather than a constructed one:

```agda
module Interconvert (unit-≅ᵒ : 𝟘ᵒ ≅ 𝟘ᵘ) where
  at𝟘     : Closureᵘ X → Closure X        -- _∘ from
  atᵘ     : Closure X → Closureᵘ X        -- _∘ to
  at𝟘-atᵘ : at𝟘 (atᵘ m) ≈ m
  Obsᵘ    : Closureᵘ Ωᵒ → Dₚ Bool          -- defined by factoring through 𝟘ᵒ
  ≋⇔≋ᵘ   : e ≋ e′ ⇔ e ≋ᵘ e′
```

`≋⇔≋ᵘ` says `ℰᵒ`'s test agreement is the **same relation** whichever of the two
empty objects its closures are quantified over.  Its hypothesis is exactly what
the identification adds, and no consumer in the cone asks for it — so the
parameterization *is* the measurement of the gap.  (`Obsᵘ` has to be defined by
factoring: the model owns one closed run, at `unitᴵ`, `UC.Machine.⟦_⟧ᴼ`.)

#### The iso itself: constructible, not affordable

The pessimism about `isoˡ` is misplaced — the ⊕-trace never has to be evaluated,
because `GConstructionEmbedding` already absorbs it generically.  Three steps:

1. `Data.Empty.⊥` is an initial object of the base `𝒱ₚ 0ℓ` (a Kleisli map out of
   it is `⊥-elim`, and `!-unique` is the same), so
   `Categories.Object.Initial.up-to-iso` compares it with `𝒱ₚ`'s own initial
   object — the one `Mealy-Monoidal`'s unit, hence `unitᴳ`, is built from.
2. `pureᴹ` is a functor (`pureᴹ-id`, `pureᴹ-∘`, `pureᴹ-cong`), so it carries
   that iso to the Mealy layer.
3. `GConstructionEmbedding.⌜⌝-≅` carries a pair of Mealy isos to a G-iso.

This was built and it does not fit the perf bar: **>150 s and 6.7 GiB resident
at `-M6G -H1G`, still running when killed**, in a module quarantined from the
whole Model cone.  Two measurements from the attempt are worth keeping.

* **Instantiating `Embed.WithTrace` as a module exhausts 8 GiB.**  A module
  application copies every sibling definition, and `Embed.WithTrace`'s siblings
  are `absorbˡ`/`absorbʳ`/`⌜⌝-∘`, whose *types* mention `G._∘_` — hence the
  trace.  `open M args using (f)` desugars to a module application and does not
  help.  Applying the one lemma through its qualified name —
  `GE.Embed.WithTrace.⌜⌝-≅ Mealy-Category Mealy-Monoidal Mealy-Traced p₁…p₄ …` —
  forms only that lemma's own type, which mentions no composite.
* With that fixed the module still runs past 150 s, so a second cost remains
  unlocated.  Unattempted diagnostics, cheapest first: (a) re-check with
  `unit-≅ᴳ` commented out, separating the cost of the machine-layer `open`s from
  the cost of `⌜⌝-≅`; (b) `opaque` on `empty-≅ᴹ`/`pure-≅` (the eta-cliff lever
  for conversion-side blowups on composite definitions); (c) state `unit-≅ᴳ` at
  literal object pairs so that `MonoidalCategory.unit (𝒢ₚᴹ 0ℓ)` is projected
  exactly once, in the seal-crossing `opaque` block, instead of being unified
  against inside `⌜⌝-≅`'s application.

The source is kept at `docs/stduc-supersession-plan/Unit-Empty.agda` — outside
`src/`, so outside the build.  Since `AnyEnvironment` shows that nothing needs
it, landing it is optional cleanup and not a phase-2 prerequisite.

### 1.2 The bridge theorem — `UC/Model/Bridge.agda`

The module assembles the core's `UCBase` at the sealed model, without unfolding
anything:

```agda
observationᵒ : Observation ∣𝔾ᵒ∣ 0ℓ 0ℓ                -- 𝟘ᵒ, Ωᵒ, Obs, ∼ᴼ, obs-resp
ucBaseᵒ      : UCBase (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) 0ℓ 0ℓ
             -- 𝒞 = ∣𝔾ᵒ∣, grading = UC.Core.Standard.gradingᵗ 𝔾ᵒ
module E = UC.Emulation ucBaseᵒ
_≈ℰᶜ_ = E._≈ℰ_     _≤UCᶜ_ = E._≤UC_
```

and then proves, for `f g : A ⇒ T₀ X B` (graded homs of the model):

```agda
≈ℰᶜ⇔≈ᵁ  : f ≈ℰᶜ g ⇔ f ≈ᵁ g                        -- both directions
≤UCᶜ⇔≤UC : f ≤UCᶜ g ⇔ f ≤UC g                      -- both directions
```

Direction-by-direction:

* `≈ℰᶜ ⇒ ≈ᴬ ⇒ ≈ᵁ` and back.  The middle step is `UC.Model.Reading`'s already
  proved `≈ᵁ⇔≈ᴬ`; the outer step is **one `assoc`** — the core reads an ancilla
  context as `(E ∘ T₁ Y f) ∘ m`, the operational reading as `E ∘ id ⊗₁ f ∘ m`,
  and `gradingᵗ`'s `T₁ Y f` *is* `id ⊗₁ f`.  Nothing else separates them.
* `≤UCᶜ ⇒ ≤UC`: the core's `dummy-complete` supplies the universal
  quantification over dummy adversaries that StdUC's `_≤UC_` carries in its
  *statement* (`∀ {X′} (a : X ⇒ X′) → Σ[ s ] sub a ∘ f ≈ᵁ sub s ∘ g`), then
  `≈ℰᶜ⇒≈ᵁ` pointwise.  Note `sub` needs no translation: `sub α ≈ α ⊗₁ id`
  holds by `Equiv.refl` (`CurriedTensor.Properties.sub-⊗`), so the core's `sub`
  and StdUC's are the *same term*.
* `≤UC ⇒ ≤UCᶜ`: `≈ᵁ⇒≈ℰᶜ` pointwise, then the core's `≤UC⁺⇒≤UC` (which
  instantiates the dummy at `id` and cancels `sub id`).

Two corollaries land with it:

* `≈ℰᶜ⇒≈ℰ` — the core's relation is strictly finer than StdUC's *bare* kernel
  (`≈ᵁ⇒≈ℰ`).  The converse is `Abstract2.bridge` and wants `GradeStable`, which
  this model does not supply (finding F2).
* `UC-composeᶜ : E.UC-compose` — **the core's one open metatheorem, discharged.**
  `UC.Emulation` states `UC-compose` as a `Set` rather than proving it, because
  the chain needs a `sub`/`T₁` interchange and `a⇒`-naturality that `Grading`
  does not ask for.  At the model the graded composite *is* the Kleisli one:
  `ext X h ≈ α⇐ ∘ id ⊗₁ h` holds by `Equiv.refl`
  (`CurriedTensor.Properties.ext-⊗`) and `gradingᵗ`'s `a⇒` is `associator.to`
  `= α⇐`, so `E._⊙_ h f` and `h ∙ f` differ by exactly one `sym-assoc`
  (`⊙-∙`) and the inherited theorem transports.

## 2. Inventory

Every public name of `UC.Core` (with the fields of its three records),
`UC.Core.Standard`, `UC.Environment` and `UC.Emulation` — 65 names — against
its status under supersession:

| category | count |
|---|---|
| **S** — StdUC counterpart (direct or up to a named lemma) | 44 |
| **B** — derived via the bridge / collapses on supersession | 4 |
| **K** — no counterpart; must be kept or ported by hand | 17 |

Per module: `UC.Core` 30 (14 S, 16 K) + `gradingᵗ` (S); `UC.Environment` 23
(19 S, 2 B, 2 K); `UC.Emulation` 11 (7 S, 2 B, 2 K).  The enrichment stack
(**E**, §2.6) is outside the three modules and survives untouched.

### 2.1 `UC.Core` — `Grading` (record + 13 fields): all **S**

| core | StdUC | via |
|---|---|---|
| `Grading` | `GradedKleisliTriple ℐ 𝒞` | `Grading` is the weakening (no unitors, no `return`/`ext`) |
| `_⊛_` | `T₀` / `ℐ._⊗₀_` | definitional at `StdSetup` |
| `T₁` | `T₁` | `CurriedTensor.Properties.T₁-⊗` (NOT definitional) |
| `sub` | `sub` | `sub-⊗` — definitional (`Equiv.refl`) |
| `a⇒` | `μ X Y` | `μ-α⇐`; both are `associator.to` = `α⇐` |
| `a⇐` | `α⇒` (`= θ` of `GradeStableFromTests`) | definitional |
| `T₁-resp-≈` | `T-resp-≈` | |
| `T₁-id` | `T-identity` | |
| `T₁-∘` | `T-homomorphism` | |
| `sub-resp-≈` | `sub-resp-≈` | |
| `sub-id` | `sub-identity` | |
| `sub-∘` | `sub-homomorphism` | |
| `a-isoˡ` | `associator.isoʳ` (`θ-μ`) | |
| `a-nat` | `μ-commute` | |

### 2.2 `UC.Core` — `Observation` (record + 7 fields + 4 derived): all **K**

`UCSetup` takes the presheaf `ℰ` as *given*.  `Observation` is the datum the
model *builds* one from — `𝟙`, `Ω`, `⟦_⟧`, `_∼_` and their laws, out of which
`UC.Model.Environment` assembles `ℰᵒ`.  The abstract layer has no counterpart
and needs none.  **Keep the record, whole**: `Observation`, `𝟙`, `Ω`, `Obs`,
`⟦_⟧`, `_∼_`, `∼-isEquivalence`, `⟦⟧-resp-≈`, `∼-refl`, `∼-sym`, `∼-trans`,
`∼-cast` (12 **K**).

It is also load-bearing for three enrichment modules that are parameterized by
it and have no `Abstract2` counterpart: `UC.Approximate`
(`ApproximateObservation`, `Induced`, `Mass`), `UC.Environment.Approximate`,
`UC.Audit`.

### 2.3 `UC.Core` — `UCBase` + `UC.Core.Standard`

| core | status | note |
|---|---|---|
| `UCBase` | **S** | ↔ `UCSetup` (rule 29 kept the names apart deliberately) |
| `UCBase.𝒞` | **S** | ↔ `UCSetup.𝒞` |
| `UCBase.grading` | **S** | ↔ `UCSetup.ℳ` |
| `UCBase.observation` | **K** | ↔ `UCSetup.ℰ` only *after* the `Observation → Presheaf` construction |
| `gradingᵗ` | **S** | ↔ `Standard2.StdUC.ℳ-standard` |

### 2.4 `UC.Environment` (23 names)

| core | status | StdUC / note |
|---|---|---|
| `Test`, `Closure` | **S** | `UC.Model.Observation.Test`/`Closure` — already exist, same definition |
| `obs` | **S** | `Obs (E ∘ m)` |
| `SameTV`, `same`, `Tests` | **S** | `UC.Model.Environment._≋_`, `ℰ₀` (role-for-role; the core's is at a fixed ancilla, `ℰᵒ`'s is ancilla-free) |
| `same-≈` | **S** | `≈ᵒ⇒≋` |
| `tv₁`, `tv₁-cong` | **S** | `ℰᵒ.F₁` and its `cong` |
| `ℰᵗᵛ` | **S** | `ℰᵒ` |
| `_≈ℰ_` | **S** | **`_≈ᵁ_`, not `_≈ℰ_`** — `≈ℰᶜ⇔≈ᵁ` (finding F1) |
| `≈ℰ-refl/-sym/-trans` | **S** | `≈ᵁ-refl/-sym/-trans` |
| `≈ℰ-isEquivalence`, `≈ℰ-setoid` | **S** | `≈ᵁ-setoid` |
| `≈⇒≈ℰ` | **S** | `≈C⇒≈ᵁ` |
| `≈ℰ-congˡ` | **S** | `sub-cong` / `ext-cong` (and `≈ℰ-cong-post` for the bare kernel) |
| `≈ℰ-congʳ` | **S** | `≈ℰ-cong-pre` |
| `≈ℰ⇒tv`, `tv⇒≈ℰ` | **B** | identity pair relating two core spellings; collapses |
| `≈ℰ-at` | **K** | no counterpart — an instrument against the machine-layer eta cliff (`UC.Seam.Grounding`'s header prices it).  Must be restated over `≈ᵁ` |
| `grade-stable` | **K** | `GradeStable` is the *same statement about a different relation* (F2) |

### 2.5 `UC.Emulation` (11 names)

| core | status | StdUC / note |
|---|---|---|
| `_≤UC_` | **S** | `_≤UC_` — `≤UCᶜ⇔≤UC` |
| `_≤UC⁺_` | **S** | `_≤UC_` — StdUC's order *is* the ⁺ (dummy-universal) form |
| `≤UC-refl` | **S** | `≤UC-refl` |
| `≤UC-trans` | **S** | `≤UC-trans` |
| `dummy-complete` | **S** | `dummy-complete` |
| `≤UC⁺⇒≤UC` | **B** | the ← half of the core's own `≤UC`/`≤UC⁺` equivalence; consumed by the bridge, then dead |
| `_⊙_` | **S** | `_∙_` — `⊙-∙`, one `sym-assoc` |
| `_⊛₁_` | **S** | `UC-compose`'s internal `ℐ.id ⊗₁ t ∘ sf ⊗₁ ℐ.id` |
| `UC-compose` | **B** | a `Set` here, a theorem there — `UC-composeᶜ` |
| `blind-grade` | **K** | no counterpart — degeneracy at a simulator-blind grade |
| `unit-grade` | **K** | no counterpart — the premise `UC.Seam.pov-carry` consumes, via `UC.Seam.Grounding.StratIsEnv` |

### 2.6 Enrichment: no `Abstract2` counterpart, survives untouched

`UC.Approximate`, `UC.Budget`, `UC.Family`, `UC.Environment.Approximate`,
`UC.Audit`, `UC.Saturated`, `UC.Seam{,.Carry,.Adequacy,.Grounding,.Audit}`,
`UC.QueryBound{,.Counting,.Compose*}`, `UC.Machine{,.Run,.Dictionary,.Grading,.Bridge}`.

Two of them are *not* passive consumers and set the shape of phase 2 — see F3
and F4.

## 3. Findings that shape phase 2

**F1 — the `_≈ℰ_` name collision is a trap, and `docs/protocol-rewrite.md` has
one row wrong.**  That file's dictionary maps the core's `_≈ℰ_` to "the kernel
congruence of `ℰ`", i.e. to StdUC's `_≈ℰ_`.  It is not: the core's relation
quantifies over an ancilla and StdUC's bare kernel does not, so at graded homs
the core's `_≈ℰ_` is StdUC's **`_≈ᵁ_`**.  The inclusion `≈ℰᶜ ⊆ ≈ℰˢ` is proved
(`≈ℰᶜ⇒≈ℰ`, through `≈ᵁ⇒≈ℰ`); the reverse needs `GradeStable`.  Any phase-2
rename that maps `≈ℰ ↦ ≈ℰ` is silently *weakening* every statement it touches.

**F2 — `GradeStable` for `ℰᵒ` is still open, and the bridge does not close it.**
`GradeStable` is about StdUC's bare kernel at *arbitrary* homs `B ⇒ C′`, where
`≈ℰᶜ⇔≈ᵁ` does not apply (the codomain need not be a `T₀`).  The core sidesteps
it by building the ancilla into the relation, which is why `grade-stable` is a
theorem there and a hypothesis here.  Consequence: `Abstract2.bridge` — the
ingestion of a bare `≈ℰ` artifact into the compositional world — remains
unavailable at this model, and every phase-2 statement should land in `≈ᵁ`
directly (which the bridge makes free, since `≈ℰᶜ` *is* `≈ᵁ`).

**F3 — `UC.Family` *constructs* a `UCBase`, it does not consume one.**
`Grading^ω`, `Observation^ω`, `UCBase^ω` at the levelwise category `Fam`, then
`Em UCBase^ω`.  Superseding the core at the machine instance does **not**
supersede it there: porting `UC.Family` needs a `UCSetup` at `Fam`, i.e. a
monoidal category of grades and a graded Kleisli triple levelwise (the D2⁺
shape).  That is a separate piece of work, not a re-spelling.  Until it is
done, `UC.Core`'s three records cannot be deleted.

**F4 — the seam is spelled in `ucBaseᴹ`, not in the seal.**
`UC.Seam.Grounding` and `UC.Seam.Audit` open `Em ucBaseᴹ` and pin their object
implicits as `⟦ unitᴵ ⟧ᴵ` / `⟦ B ⟧ᴵ` / `⟦ 𝟘 ⊗ᴵ B ⟧ᴵ`.  `ucBaseᴹ` (over the
transparent `𝒢ₚ 0ℓ`) and `ucBaseᵒ` (over the sealed `∣𝔾ᵒ∣`) have the same `𝒞`,
the same `grading` (`gradingᵗ` of the same bundle) and the same
`𝟙`/`Ω`/`⟦_⟧`/`_∼_` — they differ only by the seal and by the proof term in
`⟦⟧-resp-≈`.  Re-homing the seam means re-spelling those object implicits
through `ifaceᵒ` and the processes through `procᵒ`/`unprocᵒ`, which is exactly
what `UC.Model.Seal`'s coercions are for.  This is mechanical but it is where
the eta-cliff risk lives: `UC.Seam.Grounding`'s header measures a bare
`≈ℰ` between machine composites at a 3 GiB heap, and the reason it is
affordable today is that `_⊛_` is *abstract* there.  Under the seal `_⊗₀_` is
abstract too, so the cliff should stay closed — but it must be measured, not
assumed.

There may be a shortcut worth a spike first: the two bases look `refl`-equal
under `unfolding 𝔾ᵒ ifaceᵒ`.  Their `⟦⟧-resp-≈` fields are
`λ eq _ pos → ≈[]-mono (ε₀-least pos) (resp eq)` (from `Approximate.Induced`)
and `λ e → ≈ₚ⇒∼ᴼ (obs-resp e)`, and at `ℚ-errors` `ε₀-least` *is* `<⇒≤` and
`≈[]-mono` *is* `≈ₚ[]-mono` — so the two unfold to the same term modulo the
opaque identity `≈ᵒ⇒≈ᴹ`.  If `ucBaseᵒ ≡ ucBaseᴹ` holds by `refl` inside an
`opaque unfolding 𝔾ᵒ ifaceᵒ ≈ᵒ⇒≈ᴹ` block, P2 can `subst` the seam's statements
along one equation instead of re-spelling every object implicit.

**F5 — the bridge lives at the sealed base, deliberately.**  Stating it at
`ucBaseᴹ` instead would require transporting the ancilla quantifier across the
seal (`Obj ∣𝔾ᵒ∣` vs `Obj (𝒢ₚ 0ℓ)`), which needs `unfolding 𝔾ᵒ` in a module
that also opens `StdUC` — the exact configuration measured at 12 GiB / 50 s on
`spike-stduc-perf`.  `ucBaseᵒ` avoids it: the core's `UCBase` is assembled
entirely from names that mention the seal without opening it.

## 4. Phase-2 execution plan

Ordered so that every step is green before the next, and so that nothing is
deleted before its consumers have moved.

**P1 — re-home `≈ℰ-at`, `blind-grade`, `unit-grade` over `≈ᵁ` (the three **K**
lemmas the seam consumes).**  Add them to `UC/Model/Bridge.agda` (or a sibling
`UC/Model/Degenerate.agda` if the module grows past the perf bar) as statements
in StdUC vocabulary, each proved by transporting the core's version across
`≈ℰᶜ⇔≈ᵁ`.  No existing module changes.  Expected: cheap (each is a
`∼ᴼ-resp`/`≈ᵁ-trans` shuffle at abstract objects).

**P2 — re-spell `UC/Seam/Grounding.agda` at the seal.**  `Em ucBaseᴹ` →
`UC.Model.Setup` + `UC.Model.Bridge`; `⟦ · ⟧ᴵ` → `ifaceᵒ ·`; `Proc` → `procᵒ` /
`unprocᵒ` at the boundary.  `Agreeˢ`, `EnvAsCtx`, `StratIsEnv`, `Reflect` keep
their statements; only the vocabulary moves.  **This is the perf gate** (F4):
measure before and after, and keep the module's `_⊛_`-abstractness by never
unfolding the seal.  Owner conflict: the seam agent currently owns this file —
sequence after that work lands.

**P3 — re-spell `UC/Seam/Audit.agda` and `UC/Audit.agda`'s instantiation.**
`UC.Audit` is parameterized by `UCBase` + `Budget` + `Mass`; the cheapest move
is to keep `UC.Audit` abstract and feed it `ucBaseᵒ` instead of `ucBaseᴹ`,
which requires `Budget (∣𝔾ᵒ∣) (gradingᵗ 𝔾ᵒ)` — see P4.

**P4 — `Budget` at the seal.**  `UC.Machine.Grading`'s header records that a
`Budget (𝒢ₚ 0ℓ) gradingᴹ` assembly is *owed*, priced at >250 s because each of
nine fields re-indexes its objects.  Under the seal those objects are abstract,
so the re-indexing disappears: this is a *cheaper* target at `ucBaseᵒ` than at
`ucBaseᴹ`, and it should be re-priced there before any other route is tried.
(Coordinate with the budget agent, who owns `UC/QueryBound.agda`.)

**P5 — retire the duplicate spellings inside `UC.Environment`/`UC.Emulation`.**
Once P1–P3 land, `≈ℰ⇒tv`, `tv⇒≈ℰ`, `≤UC⁺⇒≤UC`, `_≤UC⁺_` and the `UC-compose`
obligation have no consumers (category **B**).  Delete them and `_⊙_`/`_⊛₁_`,
keeping `_≈ℰ_`/`_≤UC_` and the four metatheorems only as long as `UC.Family`
needs them (F3).

**P6 — `UCSetup` at `Fam` (the real remaining work).**  Build the levelwise
monoidal category of grades and the graded Kleisli triple at `Fam`, so
`UC.Family` produces a `UCSetup` rather than a `UCBase`.  Only then can
`UC.Core`'s `Grading`/`UCBase` be deleted.  `Observation` stays regardless
(§2.2).  (Executed; the deletion clause turned out to be wrong — §6.)

**P7 — fold the correction into `docs/protocol-rewrite.md`.**  Reverse the
verdict paragraph, fix the `_≈ℰ_` row (F1), and point the reader here.

### Not in scope for phase 2

* Deleting `UC.Core.Observation` or the enrichment stack.  There is no
  `Abstract2` counterpart and none is wanted: the abstract layer's `ℰ` is the
  *output* of that construction.
* Deleting `grade-stable` (F2).
* `UC.Core.Standard.gradingᵗ`: it is the reconciliation itself and should stay
  as the proof that `Grading` is a weakening of the inherited triple.

## 5. Perf ledger (phase 1)

Measured with `--profile=modules`, warm (one `Checking` line), at
`-M3G -H1G` / `-M4G -H1G`.  The ~9–11 s "Miscellaneous" figure is the Model
cone's fixed interface-deserialization floor, the same one
`docs/protocol-rewrite.md` records for `UC.Model.Setup`/`Reading`.

| module | LOC | own | total warm |
|---|---|---|---|
| `UC.Model.Bridge` | 131 | 0.42 s | 9.3 s |
| `UC.Model.Unit` | 129 | 0.24 s | 11.1 s |

Both are an order of magnitude inside the 150 s bar; neither adds measurable
cost of its own.  Not landed: the empty-object iso (§1.1), >150 s.

Roots green: `UC/Model.agda` (whole cone), `UC/Model/Pin.agda` and `UC.agda`
(unchanged — phase 1 edited no existing module, so no importer moved).

## 6. Phase 2, executed

P1–P7 landed.  Everything is green under
`pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS` with the warn gate
empty, and the escape-hatch grep over `src/` is 21 throughout.

### What moved

**P1** — `UC/Model/Bridge.agda` gains `_≈ᴳ_`, the bare kernel read at every
ancilla, with `≈ᴳ-refl/-sym/-trans/-congˡ/-congʳ`, `≈C⇒≈ᴳ`, `≈ᴳ⇔≈ᵁ` at graded
homs and `≈ᴳ⇔≈ℰᶜ` everywhere; then the three **K** lemmas over it — `≈ᴳ-at`,
`blind-gradeᵁ`, `unit-gradeᵁ`.  `_≈ᴳ_` is what F1 forces: `_≈ᵁ_` is stated only
at `A ⇒ T₀ X B`, the core's relation at every codomain, and StdUC's own `_≈ℰ_`
is strictly coarser, so a name was needed for the ungraded case and it is the
grade-stable refinement `GradeStable` asks `_≈ℰ_` to be.

**P2** — `UC/Seam/Grounding.agda` and `UC/Seam/Grounded.agda` are read at the
seal: `UC.Model.Setup` + `UC.Model.Bridge` instead of `Em ucBaseᴹ`, `ifaceᵒ`
instead of `⟦_⟧ᴵ`, `procᵒ` at the boundary.  `StratIsEnv` and `IotaBlind`'s
conclusion are `_≈ᴳ_`; `SubBlind` and `IotaBlind`'s hypothesis are `_≈ᵁ_`;
`UnitGrade` is the inherited `_≤UC_`.  `EnvCtx.anc` and `TrivialGrade`'s grade
widen from `Iface` to `Channel`, which restores content rather than changing it:
an agreement's ancilla quantifier ranges over every object, and transparently
`retᴵ` inverts `⟦_⟧ᴵ` on the nose, so the `Iface` spelling was no restriction
before and would have become one under the seal.  `UC.Model.Seal` gains
`unprocᵒ-∘` (`procᵒ` is functorial on the nose) so that `plug-run` can observe a
sealed composite.

At the seal the trivial grade is the bundle's own unit, so `plug-λ` is the
unitor's naturality and its own iso.  That is why `EnvAsCtx` and `StratIsEnv`
— blocked at 300 s / 8 GiB and re-measured at 2400 s when the grade was
`unitᴵ` and the equation fell through to the ⊕-trace — are now discharged in
`UC.Seam.Grounded` at the startup floor.

**P3 + P4** — `UC/Seam/Audit.agda` loses its `Budget` parameter and opens
`UC.Audit ucBaseᵒ budgetᵒ massᵒ`.  New module `UC/Model/Enrichment.agda` holds
the two: `massᵒ` needs no crossing (`Mass` mentions only `Obs` and `_∼_`, shared
on the nose), `budgetᵒ` does.  The plan's "the seal makes the re-indexing
disappear" is confirmed, but NOT by retyping — see the measurement below.

**P5** — deleted, all consumer-free: `≈ℰ⇒tv`, `tv⇒≈ℰ` (`UC.Environment`);
`≤UC⁺⇒≤UC`, `_⊙_`, `_⊛₁_`, `UC-compose` (`UC.Emulation`); and with the last two,
`UC.Model.Bridge`'s `⊙-∙`, `≤UCᶜ-resp` and `UC-composeᶜ`, whose types mention
them.  `_≤UC⁺_` is KEPT against P5's prose: it is category S and
`dummy-complete`'s stated type mentions it.  `UC.Family`'s public re-export list
drops the four dead names.

Deleting `UC-composeᶜ` is the one place phase 2 removes a proved statement.
Nothing is lost — the composition theorem is `Abstract2.UC-compose`, applied at
the model in `UC.Model.Pin.compose-at`, and `≤UCᶜ⇔≤UC` carries it to any core
`_≤UC_` statement — but it is a deletion and not a re-spelling.

**P7** — `docs/protocol-rewrite.md`: the verdict paragraph and the M4 closing
paragraph reversed, the `_≈ℰ_` dictionary row corrected in place with the F1
warning, a pointer to this file at the head of the section, and the rows P2–P5
made stale brought up to date.  `docs/rewrite-verdict.md` untouched.

### The two measurements worth keeping

**P2, the declared perf gate.**  Warm, one `Checking` line, `-M8G -H1G`:
`UC.Seam.Grounding` 9.4 s → 9.1 s and `UC.Seam.Grounded` 12.0 s → 9.1 s, both
at the Model cone's ~8.5 s interface-deserialization floor.  The eta cliff stays
closed: under the seal the conversion has nothing to unfold.  Nothing outside
`UC.Model.Seal`'s own `opaque` block unfolds the seal except
`UC.Model.Enrichment`, which opens no `StdUC` (F5).

**P4, and a new rule for crossing the seal.**  `budgetᵒ = budgetᴹ` inside
`opaque unfolding 𝔾ᵒ` **exhausts 8 GiB in 39 s**.  Retyping makes the conversion
checker meet `Grading ∣𝔾ᵒ∣` against `Grading (𝒢ₚ 0ℓ)`; `Grading` is a record, so
it eta-expands both and forms the thirteen law types that `UC.Machine`'s header
prices at ~470 s apiece at this instance.  The cure is to cross
PROPOSITIONALLY: `UC.Model.Seal` exports `sealᵒ : 𝔾ᵒ ≡ 𝒢ₚᴹ 0ℓ` from inside the
block, and `budgetᵒ` is a `subst` along it — 9.6 s.  Generally: **a datum
derived from the whole bundle crosses by `subst` along `sealᵒ`; only data
derived from a HOM cross by retyping** (`procᵒ`, `gradedᵒ`, `unprocᵒ-∘`).

### P6 — executed

All four of `UCSetup`'s fields are available at `Fam`, in the new
`UC/Family/Monoidal.agda` (125 LOC), which takes a monoidal base `M`, an
`Observation` over it, an `ApproximateObservation`, a `Budget` over
`gradingᵗ M`, and `(Ix , κ , κ-cofinal)`:

```agda
ucSetup^ω : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetup^ω = Std2.StdUC.StdSetup Famᴹ ℰ^ω
```

* `𝒞 = Fam` and `ℰ = ℰ^ω` — as recorded above.  `UC.Environment.ℰᴼ` is the
  general `Observation → Presheaf` construction (tests into `Ω` modulo closed
  observation, no ancilla in the carrier), proved once over an arbitrary
  `UCBase`; `UC.Family` re-exports it at `UCBase^ω`.  This is §2.3's one row
  that runs from the core INTO the inherited layer, and
  `UC.Model.Environment.ℰᵒ` is the same construction written out at the sealed
  model (it cannot be re-based onto `ℰᴼ`: `ucBaseᵒ` is downstream of it).
* `ℐ = Famᴹ` — below.
* `ℳ` — the plan's one-liner, taken through `Standard2.StdUC.StdSetup` by its
  QUALIFIED name, so only that definition's own type is formed (§1.1's
  module-application measurement).

The module is built BESIDE `UC.Family`'s statements, for the reason the spec
gave: `UC.Family.absorb` lands in `Em UCBase^ω`'s ancilla-quantified `_≈ℰ_`,
and the same statement at `ucSetup^ω` would land in `_≈ᵁ_`/`_≈ᴳ_`.  Those agree
— `UC.Model.Bridge` proves it at the model and the argument is generic in the
base — but the kernel congruence is a `no-eta-equality` record, so re-basing
`absorb` in place would change its stated type.  Nothing in `UC.Family` moved.

**The four certificates, and the field the spec did not foresee.**  Step 2 is
executed as authorized, with one correction.  `Budget`'s four new fields cannot
be *stated* over a `Grading`: `qb-λ⇒ : QB 1 (λ⇒ {A})` needs `λ⇒` in scope, and
`Grading` has neither a unit nor unitors.  So `UC.Core.Grading` grows the five
DATA `𝟭`/`λ⇒`/`λ⇐`/`ρ⇒`/`ρ⇐` — with no laws, exactly as `a⇒`/`a⇐` carry only
the two the core needs — and `UC.Budget.Budget` grows the four authorized
certificates over them.  Putting the unit and unitors in `Budget` instead was
rejected: `Famᴹ`'s unitor LAWS are `M`'s read levelwise, so the certificates
have to be about `M`'s unitors, and only `gradingᵗ M`'s fields are
definitionally that; a `Budget`-owned `λ⇒` would need an extra hypothesis
identifying it with `M`'s, which is the same thing spelled worse.

The inhabitants, and what each cost:

| site | cost |
|---|---|
| `UC.Core.Standard.gradingᵗ` | five projections of the bundle — free |
| `UC.Family.Grading^ω` | four `qb1` wrappers of the new `Budget` fields |
| `UC.Machine.Dictionary` | `𝟭ᴵ`, `drop⇒ˡ`/`drop⇒ʳ`, four purity lemmas (one clause each), four zigzags |
| `UC.Machine.Grading` | `qb-λ⇒ᴳ`…`qb-ρ⇐ᴳ` and four `-object` wrappers, `qb-a⇒ᴳ`'s shape verbatim |
| `UC.Machine.Budget.budgetᴹ` | four field lines |
| `UC.Model.Enrichment.budgetᵒ` | **nothing** — the `subst` along `sealᵒ` carries the wider record unchanged, as §6's P4 rule predicts |

`UC.Machine.Dictionary` also gained the generalization its zigzags share:
`wire-pure`, "a G-embedding of two PURE base maps is the wire they name".
`wire-⌜⌝`, `a⇒-α⇐` and `a⇐-α⇒` are now one application of it each, and so are
the four new ones.  No new machinery was needed, because
`GConstructionMonoidal`'s `unitorˡᴳ`/`unitorʳᴳ` are `⌜⌝-≅` of the base unitors
just as `associatorᴳ` is, and `𝒱ₚ`'s cocartesian unitors are pure: `to` is an
injection on the nose, and `from` is the copairing whose empty leg has no
clause.  Note `𝟭ᴵ` is NOT `unitᴵ` — §1.1's two empty types again — and nothing
here needs the iso between them.

**`Famᴹ`'s shape**, as the spec predicted, with no content:

* `⊗` — objects levelwise `_⊛ω_`; on homs, the base's `_⊗₁_` levelwise at
  budget `(c ⊔ 1) * (c′ ⊔ 1)`, certified by `qb-⊗₁`, which is the
  `sub f ∘ T₁ _ g` factorization (`serialize₁₂`) and not a new `Budget` field.
  `identity`/`homomorphism`/`F-resp-≈` are `λ _ → ⟨base law⟩`.
* `unit` and the three isos — `Grading^ω`'s own
  `𝟭`/`λ⇒`/`λ⇐`/`ρ⇒`/`ρ⇐`/`a⇒`/`a⇐`, which already carry their budgets; each
  `iso` field is `λ _ → ⟨base iso⟩`.
* the three naturality squares, `triangle`, `pentagon` — `λ _ → ⟨base law⟩`.

**What could NOT be deleted.**  P6's last sentence — "only then can `UC.Core`'s
`Grading` and `UCBase` be deleted" — does not survive contact with the rest of
this file, and nothing was deleted.

* `Grading` — `UC.Core.Standard.gradingᵗ`'s type is `Grading U`, and §4's
  not-in-scope list keeps `gradingᵗ`.  Six further consumers:
  `UC.Budget.Budget` (its second parameter), `UCBase.grading`,
  `UC.Machine.gradingᴹ`, `UC.Machine.Grading`, `UC.Family.Grading^ω`,
  `UC.Family.Monoidal`.
* `UCBase` — `UC.Environment` is PARAMETERIZED by it, and `UC.Environment.ℰᴼ`
  is what hands `ucSetup^ω` its own `ℰ` field.  Deleting `UCBase` would mean
  re-parameterizing the construction that P6 exists to consume.  Seven further
  consumers: `UC.Emulation`, `UC.Audit`, `UC.Environment.Approximate`,
  `UC.Family`, `UC.Family.Monoidal`, `UC.Machine.ucBaseᴹ`,
  `UC.Model.Bridge.ucBaseᵒ`.

So the supersession is complete in the sense the ruling asked — every
qualitative statement has an inherited counterpart, now at `Fam` as well as at
the model — and not in the sense of a deletion: the core's two records are
load-bearing for the enrichment stack (§2.6) and for the
`Observation → Presheaf` construction that hands the inherited layer its `ℰ`.

### Perf ledger (P6)

Warm, one `Checking` line, `-M8G -H1G`; the bar is 150 s.

| module | LOC | warm |
|---|---|---|
| `UC.Core` | 112 | 2.1 s |
| `UC.Core.Standard` | 54 | 2.2 s |
| `UC.Budget` | 73 | 2.0 s |
| `UC.Family` | 267 | 4.6 s |
| `UC.Family.Monoidal` | 125 | 7.1 s |
| `UC.Machine.Dictionary` | 417 | 24.9 s |
| `UC.Machine.Grading` | 164 | 14.8 s |
| `UC.Machine.Budget` | 56 | 9.4 s |
| `UC.Model.Enrichment` | 50 | 10.1 s |

The last four sit on the machine cone's ~9 s interface-deserialization floor,
and `budgetᵒ` is where P4 left it (9.6 s).  Roots green: `UC.agda` 9.6 s,
`UC/Model.agda` 13.6 s, `UC/Model/Pin.agda` 9.3 s, `UC/Seam{,/Audit,/Grounded}`
9.2/9.8/9.7 s, `UC/Audit.agda` 4.4 s, `UC/Environment/Approximate.agda` 4.5 s.
