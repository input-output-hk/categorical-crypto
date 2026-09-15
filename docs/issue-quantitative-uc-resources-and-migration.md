# Model resource-sensitive quantitative UC and migrate the existing relations

## Summary

Extend the approximate-space-valued approach to preserve query-sensitive error schedules, construct the required family models and qualitative collapses, and replace the handwritten UC presentations only after proving the appropriate equivalences.

Depends on [the Approx-valued UC foundation](issue-quantitative-uc-foundation.md). The resource-aware construction must be established before treating it as an instance or reusing the foundation's unchanged-error theorem statements.

## Background

The nonexpansive foundation compares all environments at a fixed error. Existing query-sensitive relations instead restrict tests and closures and transform allowances when processes or simulators are absorbed into contexts.

Those requirements belong in a controlled/filtered category of quantitative spaces, or an appropriate indexed base. They must not reappear as dozens of unrelated fields in a foundational `QUCSetup` record.

See [the quantitative UC plan](quantitative-uc-setup-plan.typ), sections 7–10. Source references were reviewed at `protocol-rewrite`, `92479a31`; recheck the actual implementation and importer inventory before migration. Signatures below are schematic.

## Scope

### Construct the resource-aware category

Generalize approximation to a fixed ordered additive commutative monoid `V`. Error schedules use pointwise order and addition. Preserve the existing signed rational schedule domain where required by an old/new equivalence; do not silently replace it with nonnegative schedules.

A proposed controlled map carries its error transformation:

```agda
record Controlled (X Y : ApproxSpace V) : Set where
  field
    map : X.Carrier → Y.Carrier
    control : OrderedAdditiveEndomorphism V
    preserves : X._≈[_]_ x ε y →
                Y._≈[_]_ (map x) (control ε) (map y)

(g , ψ) ∘ (f , φ) = (g ∘ f , ψ ∘ φ)
identity = (id , id)
```

Initially use equality of controls together with pointwise zero-error equality of functions. Allowance reindexing induces the additive control `φρ ε = ε ∘ ρ`.

Tests also need an increasing family of admitted elements `Admit q x`. A filtered controlled map carries a monotone allowance map `α` and a proof:

```agda
AdmitX q x → AdmitY (α q) (map x)
```

Choose a filtered-target or indexed-base presentation by constructing the intended model. Prove category and presheaf coherence, including controls. If the existing cost arithmetic supplies only inequalities, explicitly formulate and justify the ordered/lax construction instead of claiming exact functoriality.

This design-validation step is a gate: do not begin broad importer migration until the category, model, and resulting quantitative theorem statements are established.

### Reproduce the query-sensitive comparison

The intended element-level model compares tests through certified closures:

```agda
E ≈[ τ ] F = ∀ m c′ → QB c′ m →
  Obs (E ∘ m) ≈ₚ[ τ c′ ] Obs (F ∘ m)
```

Process comparison additionally bounds the test by `c` and specializes the schedule through `τ c′ = ε (ctxBudget c c′)`.

Derive the controlled/filtered quantitative laws from the categorical construction. Preserve the actual bounds of the existing family model:

```agda
-- Sequential emulation composition
λ n q → ε₁ n q + ε₂ n (simCost q (cost s₁ n))

-- Graded composition
λ n q → εu n (simCost q (cf n))
      + εf n (simCost q ((cost t n ⊔ 1) * cv n))
```

Retain the simulator, its cost evidence, and any real process-certificate or allowance-monotonicity premises. Removing a premise requires a stronger proved transport lemma. Preserve unchanged-error domain precomposition where the current zero-query resource-closing certificate justifies it.

Do not assume arbitrary processes induce controlled maps on bounded tests. Construct admitted morphism categories or appropriate indexing explicitly. The computation category and grade category may differ; polynomially certified simulators need not force every compared process to be certified.

### Family models and collapse

Construct the models needed to compare levelwise arbitrary process families, certified simulator families, and the existing category of polynomially certified process families. Prove the context-domain comparisons; a level tag alone does not establish them.

For existential collapse, use an error class containing zero and closed under addition:

```agda
x ∼Small y = Σ[ ε ∈ V ] (Small ε × x ≈[ ε ] y)
```

Restrict controlled maps to those preserving `Small`. For negligible schedules, establish polynomial-preserving reindexing. Keep this construction distinct from all-positive-error collapse.

Preserve the position of the negligible witness:

```text
∃ negligible ε. ∀ closures m. compare E F m ε
```

is stronger than the existing local-negligible form:

```text
∀ closure families m. ∃ negligible ε. compare E F m ε.
```

Apply collapse at the correct stage of the observation/test-presheaf construction. Do not assume it commutes with the closure quantifier.

Build separate canonical `Abstract2` instances for vanishing and local-negligible observation. Prove transfers from uniformly retained schedules using explicit certificates for the compared process families. The evident base functor forgets certificates; reverse promotion is not automatic. Agreement against filtered tests requires coverage or a proved restriction/transfer before it can imply an unrestricted target relation.

### Equivalences and retirement

Establish the relevant comparisons before switching consumers:

```agda
Old.≤UC^ωᵉ f g ↔ ControlledFamilyUC f g
Old.≤UC^ωᵉ⁺ f g ↔ ControlledFamilyUC⁺ f g
Old.≤UCᴺ f g ↔ CanonicalNegligibleUC f g
```

The new names above denote the future instances, not already established definitions. Preserve adversary → simulator and schedule → environment quantifier order.

Keep `_≤UC^ωⁿ_` as direct negligible agreement, with an identity-simulator embedding. Keep pointwise `_≤UC^ω_` distinct from emulation in a family category. Recognize `_≤UCᵁ_` as an inherited alias and `≤UCᵍ`/`≤UC[]ᵍ` as constructors, not new relations requiring their own metatheory.

Replace audit emulation with a cost-certified canonical qualitative dummy witness:

```agda
AuditWitness cs f g =
  Σ[ s ∈ I [ Y , X ] ] (QBᴵ cs s × (f ≈ᵁ₊ (sub s ∘ g)))

Old.Audit.≤UC[ cs ] f g ↔ AuditWitness cs f g
```

This is not exact zero-error quantitative emulation. Preserve event membership, event absorption, simulator-cost substitution, and positive slack in the audit carry result.

Follow `docs/retirement.md`: recompute importers, prove replacements, migrate clients, and only then remove duplicate bodies. Do not retain a new parallel API without completing the agreed retirement gate.

## Acceptance Criteria

- [ ] The resource-aware target/indexing and its equality/coherence laws are specified and implemented without new postulates.
- [ ] The concrete query model supplies a genuine instance; exact and ordered/lax laws are not conflated.
- [ ] Generic quantitative composition retains the selected simulator and reproduces the existing schedule expressions.
- [ ] Levelwise contexts, certified context families, and polynomial simulator certification are related by explicit proofs, not quantifier exchanges.
- [ ] Canonical vanishing and local-negligible `UCSetup` instances are constructed and inherit `Abstract2`.
- [ ] Transfers from retained quantitative evidence expose process certificates, admitted contexts, and the target observation.
- [ ] Old/new quantitative and audit comparisons are proved before importer migration.
- [ ] `hash-liftⁿ`, `coin-toss-ideal`, and audit carry consumers typecheck with their required definitional schedule pins intact.
- [ ] Tests or checked separating examples retain zero/all-positive, vanishing/negligible, and pointwise/family distinctions.
- [ ] The documentation and signatures preserve fixed-simulator and local/global error-witness quantifier order.
- [ ] Importers are migrated and handwritten duplicate bodies retired under the repository's retirement protocol.
- [ ] The affected build is verified using the shared Agda toolchain, with significant elaboration regressions recorded.

## Reuse and Non-Goals

Reuse `UC.Budget`, `UC.Asymptotic.Contextual`, `UC.Asymptotic.Compose`, `UC.Family`, `UC.Family.Negligible`, `UC.Approximate`, and existing bridge proofs as model witnesses and migration references.

Do not claim uniform polynomial runtime from query certificates, manufacture polynomial bounds for arbitrary processes, weaken negligible security to vanishing security, or change exact error semantics to make an equivalence easier. New cryptographic realizations and a broad quantitative setup-morphism framework are not prerequisites for completing this migration.
