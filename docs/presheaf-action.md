# UC preservation through the presheaf action — steps 1 and 2

What steps 1 and 2 of `docs/uc-presheaf-preservation-plan.md` delivered, on branch
`presheaf-action` off `protocol-rewrite` at `89e09091`. Paths are relative to
`src/CategoricalCrypto/` unless prefixed.

## 1. The generic action (plan §2.1)

`Abstract2/Action.agda` — parameterized by an arbitrary `UCSetup` and nothing else. It
opens `Abstract2.AbstractUC` (so the action is stated in that vocabulary) and adds the
abbreviations and four lemmas the plan asks for. Kept beside `Abstract2` rather than
inside it so that the cone under `Abstract2` pays nothing for it; the measured cost of
`Abstract2` itself moves 5.0 s → 4.7 s (noise), see §4.

| Name | file:line | content |
|---|---|---|
| `Env` | `Abstract2/Action.agda:47` | the carrier of `ℰ D` |
| `_≈Env_`, `≈Env-refl/sym/trans` | `:52`, `:55`-`:61` | equality in the setoid `ℰ D` |
| `pull` | `:65` | `ℰ h e`, contravariant |
| `pull-cong`, `pull-resp-≈`, `pull-∘` | `:68`, `:71`, `:74` | `ℰ`'s `cong`, `F-resp-≈`, `homomorphism`, at elements |
| `prefix` | `:81` | `μ W X ∘ T₁ W f` |
| `run` | `:84` | `pull (prefix W f) e` |
| `regradeEnv` | `:87` | `pull (sub (id ⊗ s)) e` |
| `run-sub` | `:90` | `run W (sub s ∘ g) e ≈Env run W g (regradeEnv W s e)` |
| `run-resp-≈ᵁ` | `:98` | `f ≈ᵁ g → ∀ W e. run W f e ≈Env run W g e` |
| `runs⇒≈ᵁ` | `:102` | the converse |

`run-sub`'s whole proof is `pull-resp-≈ (sub-decomp s g W) e` followed by `pull-∘`: the
absorption of a simulator is the presheaf's action on `sub`, and no new operation is
introduced for it. The two run-agreement laws are one line each (`KE.run∼` and `KE.mk∼`),
which is the point: `run` is the element-level reading of the *U-kernel*, so this
presentation does not silently replace `_≈ᵁ_` by the bare kernel `_≈ℰ_`.

`≤UC⇒dummy` (`Abstract2.agda:181`) is the converse of `dummy-complete`, placed beside it.
It replaced the three inlined identity-adversary normalizations, with no statement change:

- `Abstract2.agda:207`/`:209` (`t`/`eh` in `UC-compose`)
- `Abstract2.agda:212`/`:214` (`sf`/`ef` in `UC-compose`)
- `UC/Model/Bridge.agda:176` (`≤UC⇒≤UCᶜ`) — the one permitted edit to `Bridge`.

### Plan acceptance checks, with evidence

| Check | Evidence |
|---|---|
| grades and category objects stay distinct parameters | `Abstract2/Action.agda:37-39`: the `private variable` block declares `A B D D′ D″ : 𝒞.Obj` **and** `W X Y : ℐ.Obj` separately; every signature carries both sorts (`prefix : (W : ℐ.Obj) → A 𝒞.⇒ T₀ X B → …`). No definition equates them. |
| no `Observation`, verdict object or closed-run observation | the module's complete import list is `Categories.Functor`, `Function.Bundles`, `Level`, `Relation.Binary.Bundles`, `CategoricalCrypto.UCSetup`, `CategoricalCrypto.Abstract2` (`:22`-`:34`). `grep -nE "GradeStable\|Observation\|Ω\|observe\|verdict" ` over the module is empty. |
| no `GradeStable` assumed | same grep; `GradeStable` is in scope (it is a definition of `UCSetup`) and is used by nothing. `bridge` is never invoked. |
| no invertibility of `μ` | `μ` occurs once, in `prefix` (`:82`). `grep -nE "α⇒\|α⇐\|iso"` over the module is empty — no associator inverse, no retraction `θ`. |

## 2. Generic preservation (plan §2.2, §3.1)

### `UC/Robust.agda` — the canonical API, over an arbitrary `UCSetup`

| Name | file:line | note |
|---|---|---|
| `SaturatedProperty p D` | `:48` | `holds : Env D → Set p`, `saturated : u ≈Env v → holds u → holds v` |
| `Admissible B d` | `:56` | `(W X : ℐ.Obj) → Env (T₀ (W ⊗ X) B) → Set d` |
| `⊤ᴬ` | `:59` | pinned at `0ℓ` — a level-polymorphic `⊤` leaves `d` unsolved at every use site |
| `Respects≈Env` | `:64` | stated apart from `ClosedUnder`, as the plan requires |
| `ClosedUnder Adm s` | `:69` | `∀ W e. Adm W X e → Adm W Y (regradeEnv W s e)` |
| `Robust P Adm f` | `:78` | `P : (W : ℐ.Obj) → SaturatedProperty p (T₀ W A)`; `P W` does **not** see the resource grade `X` |
| `robust-resp-≈ᵁ` | `:86` | saturation + `run-resp-≈ᵁ` |
| `robust-sub` | `:92` | premise `ClosedUnder Adm s`; saturation + `run-sub` |
| `uc-preserves-at` | `:104` | at an EXPLICIT witness `s` with `f ≈ᵁ sub s ∘ g` |
| `uc-preserves` | `:110` | all-simulators corollary: `(∀ s → ClosedUnder Adm s) → f ≤UC g → …`, via `≤UC⇒dummy` |
| `uc⁺-preserves` | `:120` | adversary-attached, using `le a` directly at `Abstract2._≤UC_`'s quantifier order |

Both `P` and `Adm` are **explicit** at every use site, for the reason the previous
`UC.Robust` records: `Robust P Adm f` reduces to a Π type whose body applies
`holds (P W)`, which no use site can invert.

`uc-preserves-at` exists separately from `uc-preserves` precisely so that a class that is
*not* closed under arbitrary simulators cannot obtain closure merely from `f ≤UC g`.

### `UC/Robust/Observation.agda` — the independently scoped `UCBase` theorem

The previous `UC/Robust.agda` moved **verbatim** (`git mv`; the only diff is the module
name and five header lines saying why it is not an instance of the new theorem). Its
`SaturatedProperty`, `⊤ᴾ`, `∼[_]`, `Robust`, `robust-resp-≈ℰ`, `robust-sub`,
`uc-preserves`, `uc⁺-preserves` are byte-identical. The name says the scope: it is the
theorem for an observation-generated base, where an arbitrary `UCBase` supplies no graded
Kleisli triple and an arbitrary `UCSetup` no closed observation.

Its only importer was `UC.Robust.Model`, which is updated. (`grep -rn "UC.Robust" src/`
otherwise reaches only comments in the two root index files; see §5.)

### `UC/Robust/Selected.agda` — a nontrivial admissible class

`Factors V` (`:41`) is the class of environments that reach the resource port only through
a designated interface `V`: `e` is pulled back along **some** grade morphism `a : X ⇒ V`
from a grade-`V` environment. Supporting lemmas: `regrade-∘` (`:45`, the action's
functoriality), `factors-resp` (`:53`, `≈Env`-respect), `factors-closed` (`:56`, the
closure obligation), `uc-preserves-factors` (`:60`).

### `UC/Robust/Model.agda` — the model recovery

`module Gen = Sel StdSetup` (`:46`) is the canonical theorem at `UC.Model.Setup`; the
observation-scoped names stay unqualified and are re-exported unchanged.

- `propᵒ` (`:67`) is the plan's adapter: `holds (P W) t = ∀ m : 𝟙 → T_W A. Q (⟦ t ∘ m ⟧)`,
  with saturation `λ eq h m → saturated 𝔓 (eq m) (h m)` — literally the test-setoid
  equality of `UC.Environment.Presheaf._≋_` evaluated at each closure. Its input is an
  observation-invariant predicate packaged as the existing (observation-scoped)
  `SaturatedProperty`, so no second notion of "invariant predicate" appears.
- `robust⇒robustᵍ` / `robustᵍ⇒robust` (`:74`, `:79`) carry robustness between the core's
  bracketing `Y ⊗ (X ⊗ B)` and the inherited `(Y ⊗ X) ⊗ B`. They reuse
  `UC.Model.Reading.shuffle⇒`/`shuffle⇐` and spend one `assoc` each; no machine fact is
  reproved and `μ` is not required to be invertible anywhere in the generic layer.
- `uc-preservesᵒ` (`:87`) keeps its statement and is now a direct instance of
  `Gen.uc-preserves`. The `≤UC⇒≤UCᶜ` detour is gone from this proof. The Bridge lemma
  itself stays — but note that after this change `grep -rn "≤UC⇒≤UCᶜ\|≤UCᶜ⇔≤UC" src/`
  finds **no** in-repo consumer; it was this proof's only one. It is deliberately kept
  (plan §5: retirement is gated on replacement *and* importer migration, and the two
  orders' agreement is the seam's own statement, not a wrapper). Flagged in
  `QUALITY-REVIEW.md`.
- `⊤-robust` (`:93`) and `verdict-preservedᵒ` (`:98`) keep their exact statements.
- `relay-selectedᵒ` (`:110`) is the selected-environment acceptance test: see §3.

`UC/Model/Reading.agda:48`/`:57` — `shuffle⇒`/`shuffle⇐` stopped being `private`. Nothing
about them changed; this is the single-source alternative to copying eight lines of
associator shuffling into `UC.Robust.Model`.

## 3. The selected-environment acceptance test, and what it does not show

`relay-selectedᵒ` instantiates `uc-preserves-factors` with

- `Adm = Gen.Factors V` — a genuine subset of the environment fiber, not `⊤`;
- `s = relayᵒ 𝔄` (`UC.Model.Pin`) — a real machine, the stateless relay that exposes its
  own caller interface as its adversary grade, so `s : ifaceᵒ 𝔄 ⇒ T₀ (ifaceᵒ 𝔄) (ifaceᵒ unitᴵ)`
  is a simulator at a **nontrivial** grade, not an identity;
- `factors-closed V s` — a proved `ClosedUnder`, whose content is the presheaf's
  functoriality and `sub`'s homomorphism, not a `⊤` introduction;
- the preservation applied at that explicit witness, by `uc-preserves-factors`, i.e. NOT
  through the all-simulators corollary.

**An honest caveat.** `Factors V` happens to be closed under *every* simulator, and no
purely qualitative class can avoid this: `ClosedUnder Adm s` **is** closure of the
attacker collection under precomposition by `s`, so any class cut out by a
precomposition-closed condition on the attacker is closed at every `s`. A class that
separates the two — a fixed query budget, which the simulator's own queries can exhaust —
needs the quantitative enrichment (plan §2.2's "fixed-budget context classes", and §4),
which is steps 3-5 of the plan and not in scope here. What steps 1-2 deliver is that the
premise is a real, dischargeable obligation rather than a definition, and that
`uc-preserves-at` exists so that a budgeted class will be able to use the theorem without
claiming all-simulator closure. This is recorded in `UC/Robust/Selected.agda`'s header.

## 4. Module cost (warm, single `Checking` line, `+RTS -M8G -H1G`)

| Module | LOC | warm before | warm after |
|---|---|---|---|
| `Abstract2` | 244 | 5.0 s | 4.7 s |
| `Abstract2.Action` | 105 | — (new) | 3.5 s |
| `UC.Robust` (canonical) | 125 | — (new) | 3.6 s |
| `UC.Robust.Selected` | 64 | — (new) | 3.6 s |
| `UC.Robust.Observation` | 120 | not measured | 2.7 s |
| `UC.Robust.Model` | 116 | not measured | 13.9 s |
| `UC.Model.Reading` | 77 | not measured | 12.6 s |
| `UC.Model.Bridge` | 193 | not measured | 13.0 s |

Only `Abstract2` had a before/after pair taken on the same warm basis, because it is the
one module the whole `UC.Model` cone pays for; it moved −0.3 s (noise, and in the good
direction). The four "not measured" rows had no pre-change warm baseline on this worktree
(a clean one would have cost a 13-minute cold rebuild in a second worktree); two of them
are content-unchanged (`Observation` is verbatim, `Reading` differs only by a `private`
keyword) and `Bridge` lost two proof steps.

Everything is far inside the `60 s + LOC/4` budget. The ≈13 s floor in the machine-model
cone is interface deserialization behind the seal, not new content: `UC.Model.Reading` at
77 LOC costs the same as `UC.Robust.Model` at 116, and `Bridge` at 193 the same again.

Closure `CategoricalCrypto`: 86 s (cold from scratch on this worktree: 13 min).

## 5. Root-file wiring the maintainer still needs to do

Nothing is missing from the *import* closure: `CategoricalCrypto.agda:62` imports
`UC.Robust.Model`, which reaches `UC.Robust`, `UC.Robust.Selected`,
`UC.Robust.Observation` and `Abstract2.Action` transitively. Both root index modules check
green unchanged, as do `UC.agda`, `UC/Model.agda`, `UC/Approximate/LocalTests.agda` and
the `Examples/ChimericLedger/*` roots.

What is now stale is `src/CategoricalCrypto/UC.agda`'s inventory, lines 19-25: it lists
`UC.Robust` under the **core** tier as the `UCBase` theorem. That row should split — the
`UCBase` theorem is now `UC.Robust.Observation` (core tier), while `UC.Robust` is the
`UCSetup` theorem and belongs with the inherited-layer rows. `src/CategoricalCrypto.agda`
needs no change beyond, optionally, naming the new modules in its own inventory comment.

## 6. Not delivered

- Plan steps 3-7 (quantitative consolidation onward) are out of scope for this task.
- An `Adm` that is closed under one simulator but not all — see the caveat in §3 for the
  exact obstruction.
