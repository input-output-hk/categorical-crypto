# Spike: the reading as a lower real (simplification-options §2.2, cheap version)

Base `19ec4c6b` (protocol-rewrite), branch `memo22-spike`. Unwired, new files only:
`src/ProbabilisticLogic/Dp/Spike/LowerRealReading.agda` (Dp level) and
`src/ProbabilisticLogic/Dp/Spike/LowerRealModel.agda` (the sealed model). Both
`--safe --without-K --guardedness`, green, warning-clean, no escape hatches.

## Verdict

- **(a) D4 via LowerReal: DONE already** (`20a32eef` D4, `b8b3c802` LowerReal). Left:
  three fossil names that said `dom₀`, since renamed (`cd6c6915`; below).
- **(b) Full cheap version (`S := 𝕃` at the model): NO-GO.** With one lower real
  (`Pr[true]`) the readout gets coarser: a changed semantics, not a simplification
  (`one-sided-coarser`). With a lower real per verdict (`𝕃² = Bool → ℕ → ℚ`) the readout
  is faithful, but the model's ε-layer is **already** the pullback of `𝕃²`'s along
  `read`, definitionally (`≈ₚ[]-pullback = refl`), and `massᵒ` is **already**
  `mass𝕃 ∘ read` (`massᵒ-factors = refl`). Nothing folds away: the mass is a
  projection, not the identity. Net LOC ≈ 0.

## Q1: D4 status

`Dom₀` is gone. `Cofinal P Q d e = cumₛ d P ≼ cumₛ e Q` and
`Dom P ε d e = cumₛ d P ≼[ ε ] cumₛ e P` are LowerReal's relations at `cumₛ`, and
every `cofinal-*`/`dom-*` lemma is a single application of a LowerReal lemma. Of D4's
table: `Mass._≼ᵐ_ = Cofinal (λ _ → 1ℚ) (λ _ → 1ℚ)`, `_≼ₚ_`, `Advantage._≼ₚ[_]_` are
one-line applications. That covers everything D4 asked for.

Keep `Cofinal`/`Dom` as named notions. They are thin, but they are the
**inference adapters**: LowerReal's lemmas must take their sequences explicitly
(its header: a `cum` instance strands the meta), and `dom-trans`/`dom-resp`/… take
the runs implicitly instead. Inlining them would give ~33 call sites
(`grep -rnwF`: `Cofinal` 19 occurrences in 6 files, `Dom` 14 excluding `Dom≤` and
the unrelated `GConstructionCoherence`/`APROP` `Dom`s) a `cumₛ d P ≼ cumₛ e Q` spelling
and six generic lemmas their explicit sequence arguments, for about −6 LOC.

Residue, since closed: the fossil names `Dp.dom₀⇒dom`, `Dominate.dom≤⇒dom₀` and
`Dominate.dom₀-bind` are now `Dp.cofinal⇒dom`, `Dominate.dom≤⇒cofinal` and
`Dominate.cofinal-bind` (`cd6c6915`).

`≈ₚ⇒cumₛ-≈ : NNF P → d ≈ₚ e → cumₛ d P ≈ cumₛ e P` was missing; it is proved in the
spike from `≼⇒≲`. It needs `NNF P`, because `_≈ₚ_` quantifies only over
non-negative tests. The converse fails: `_≼_` is strictly finer than `_≲_`
(LowerReal's header). That is why the hom equality stays `_≈ₚ_` and not
LowerReal's `_≈_`.

`_≲_` has no named `Dp` counterpart. Its uses are open-coded:
`Mass.squeeze-astotal`'s hypothesis `∀ ε > 0 → x ≼ₚ[ ε ] z` is `_≲_` per verdict (one
site), and the model's `S.≈` (`AllPositive._∼ᵃ_` at `Approximationᴹ`) is `_≈_` per
verdict (Q2).

## Q2: the evaluation setoid

`LowerRealModel.evaluation𝕃 : Evaluation ∣𝔾ᵒ∣ 0ℓ 0ℓ` takes `S = 𝕃²-setoid` (a
LowerReal per verdict, pointwise `≈`), with `eval = read ∘ Obs`. It is built as
`qualBy` of a `QEvaluation` on the `𝕃²` space, the same way `evaluationᵒ` is built as
`qual₊`. It recovers the existing relation on the nose:

- `S-recovered : d Eᵒ.S.≈ e ⇔ read d E𝕃.S.≈ read e` for every pair of runs,
- `read-factors : E𝕃.read u ≡ read (Eᵒ.read u)` (`refl`),
- `≋-recovered : t ≋ᵒ t′ ⇔ t ≋𝕃 t′` on tests. The test presheaves identify the same
  tests, so every UC relation stated over `ℰᴼ` is unchanged.

The underlying fact is `∼ᵃ⇔≈`: all-positive closeness on `𝕃²` is pointwise LowerReal
equality. It is only a swap of the `∀ε` and `∀b` quantifiers.

**Why not `S := LowerReal` with `eval = Pr[true]`.** `one-sided-coarser` proves that
`read (returnₚ false) true ≈ read botₚ true`, and yet
`¬ ∀ ε > 0 → returnₚ false ≈ₚ[ ε ] botₚ`. In words, answering `false` and diverging are
identified. That is exactly the collapse `Dp.Advantage`'s header forbids.

Whether the collapse reaches `≈ᵁ` is open. An environment could negate its verdict,
which would move the `false`-mass onto `true`. Settling it needs a lemma
`⟦ wireᴹ not id ∘ u ⟧ᴼ ≈ₚ mapₚ not ⟦ u ⟧ᴼ` over the Elgot composite, and the repo has
no such lemma. Even if it holds, a test-level equivalence gets coarser and ≈ᵁ has to
be re-proved. That is a semantic change to argue for, not a simplification.

There is no level problem: `S` is at `0ℓ 0ℓ`, as `evaluationᵒ`'s is. There is no
`Func`-shape problem either. And the `qual₊` positive-error readout is not an
obstruction: it **is** LowerReal's `_≈_`, which is itself every-δ.

## Q3: the ε-layer on 𝕃

`approx𝕃 : Approximation 𝕃² ℚ-ordered 0ℓ` has
`x ≈𝕃[ ε ] y = (∀ b → x b ≼[ ε ] y b) × (∀ b → y b ≼[ ε ] x b)`. The layer is two-sided,
per verdict. Its laws are LowerReal's `≼[]-refl/-trans/-mono`.
`≈ₚ[]-pullback : _≈ₚ[_]_ ≡ (λ d ε e → read d ≈𝕃[ ε ] read e)` holds by `refl`.

`UC.Audit`'s `mass` does **not** become the identity. The audit reads the
probability of an event, which is one-sided, so on `𝕃²` it is the `true` projection
`mass𝕃 = _$ true`, and `massᵒ-factors : massᵒ ⟨$⟩ d ≡ mass𝕃 ⟨$⟩ read d` holds by `refl`.
The `mass` parameter of `UC.Audit` stays. It is generic over `R`, and an `R` whose
`S` is `LowerReal` would be exactly the coarse readout above.

## Q4: inventory of the cheap version (S := 𝕃² at the model)

| file :: name | LOC | fate |
|---|---|---|
| `UC/Machine.agda :: Approximationᴹ` | 8 | → `approx𝕃` (+15 moved in; the laws `≈ₚ[]-*` stay for Dₚ-typed consumers) |
| `UC/Machine.agda :: spaceᴹ`, `QEvaluationᴹ` | 8 | retyped (`Carrier = 𝕃²`, `to = read ∘ ⟦_⟧ᴼ`), same size |
| `UC/Model/Observation.agda :: qevaluationᵒ`, `∼ᴼ-resp` | 8 | retyped; `∼ᴼ-resp` needs a `read` wrapper |
| `UC/Model/Enrichment.agda :: massᵒ` | 2 | → `mass𝕃` (same size) |
| `UC/Audit.agda :: mass` parameter | — | stays (see Q3) |
| `UC/Seam/**` | 0 | untouched: no `Mass` structure is left in `Seam` (deleted before this base); `Transfer`/`EventTransfer`/`Budget` compare `Dₚ` runs at a test through `Cofinal`/`Dom≤`, never the readout |
| `Dp :: Cofinal`, `Dom`; `Dp/Mass :: _≼ᵐ_` | 0 | stay (Q1) |

The model files come to about −2..+10 LOC net. Statements whose shape changes:
the model-specific sites typed at the readout carrier. These are
`UC/Robust/Model :: relay-selectedᵒ` (`r : S.Carrier`), `Enrichment :: massᵒ`, and the
`QEvaluation`/`Tests` instantiations in `UC/Model/{Observation,Quantitative}`. The generic
`UC/**` code (`Core`, `Audit`, `Family`) is polymorphic in the carrier and does not
change. The 41 `≈ₚ[ ]`/`≼ₚ[ ]` uses in
12 files keep their types, because the relation is definitionally the pullback, but a
hypothesis on a bare `𝕃²` element can no longer be fed to `≈ₚ[]-*`.

Estimate: (a)'s residue is a rename, under ¼ session. (b) is about ½ session of
retyping with nothing deleted.

## What would actually remove structure

The Seam/Mass/Approximants layer the memo counted is already gone: D4, the LowerReal
merge, and the earlier `Mass` deletions removed it. What is left of §2.2's promise needs
the full version, where the supremum lives in the carrier and `_≼ₚ_` is pointwise ≤.
Only there do `cum`, `cumₛ`, `Cofinal`, `Dom`, `Dom≤` and the `ASTotal`/`squeeze` ε/2
arithmetic go, and that is the 4k-LOC `Dp/**` rebuild.
