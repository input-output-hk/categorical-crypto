// Standalone: typst compile docs/quantitative-uc-setup-plan.typ
#set document(title: "Quantitative UC from approximate-space-valued presheaves")
#set page(numbering: "1", margin: 2.1cm)
#set text(size: 10pt)
#set par(justify: true)
#set heading(numbering: "1.1")
#show raw.where(block: true): it => block(fill: luma(96%), inset: 8pt, breakable: false)[
  #set text(size: 8.5pt)
  #it
]

#align(center)[
  #text(size: 16pt, weight: "bold")[Quantitative UC from approximate spaces]

  Revised implementation plan and expected interfaces

  15 September 2026
]

This revision replaces the earlier large-record proposal. The foundation is a
presheaf valued in a category of approximate spaces, not an ordinary `UCSetup`
with separate `ApproximateCarriers`, `Certificates`, `ResourceAction`, and
collapse-compatibility records attached.

The implementation references were reviewed at `protocol-rewrite`, `92479a31`.
This is a mathematical design and migration plan, *not a completed or typechecked
Agda implementation*. Signatures are schematic: universe levels and implicit
variables are omitted. See `docs/uc-observation-and-relation-consolidation.typ`
for the account of `Obs` and the inventory of existing relations. The present
document supersedes that note's earlier implementation direction where they differ.

= The foundational construction

The computational data stay unchanged: a category of computations, a monoidal
category of grades, and a graded Kleisli triple. Replace the qualitative
environment presheaf by an approximate-space-valued presheaf:

```agda
Q : Functor (op C) Approx
```

A forgetful functor `F : Approx → Setoids` then gives the ordinary presheaf
`F ∘F Q`. Use it to construct a `UCSetup` and inherit `Abstract2` unchanged.
Quantitative comparisons are evaluated in `Q`, before forgetting.

This is genuinely a smaller definition. The approximation category packages
nonexpansiveness, composition, and equality of maps once; the presheaf laws
supply their coherence. Resource accounting is a separate extension of the
quantitative-space category or its indexing, not mandatory structure in every
quantitative UC setup.

= The category Approx

== Objects: bounds rather than real-valued distances

Initially take nonnegative rational errors. An object is a carrier with an
error-indexed approximation relation and four laws:

```agda
record ApproxSpace : Set where
  field
    Carrier : Set
    _≈[_]_ : Carrier → ℚ≥0 → Carrier → Set
    refl  : x ≈[ 0 ] x
    sym   : x ≈[ ε ] y → y ≈[ ε ] x
    trans : x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε + δ ] z
    mono  : ε ≤ δ → x ≈[ ε ] y → x ≈[ δ ] y
```

An extended pseudometric supplies such an object by taking `x ≈[ ε ] y` to
mean that its distance is at most `ε`. But no distance function, supremum, real
number construction, or separation axiom is required.

The current `UC.Approximate.Approximation` already provides the main relation
and laws. Reuse its implementation rather than independently recoding them.
The rational arithmetic supplies the zero and additive laws needed below.

== Morphisms and their equality

```agda
record Nonexpansive (X Y : ApproxSpace) : Set where
  field
    map : X.Carrier → Y.Carrier
    preserves : X._≈[_]_ x ε y → Y._≈[_]_ (map x) ε (map y)

f ≈map g = ∀ x → Y._≈[_]_ (f.map x) 0 (g.map x)

identity : Nonexpansive X X
compose  : Nonexpansive Y Z → Nonexpansive X Y → Nonexpansive X Z
```

Identity and composition use the ordinary functions. Pointwise zero-error
comparison is an equivalence, and composition respects it: use nonexpansiveness
and the triangle law at zero. Thus this defines the hom setoids of `Approx`.

Zero-error identification also preserves every fixed error bound on points.
For example, zero-error changes at the two endpoints of an error-`ε` comparison
give error `0 + ε + 0 = ε`. No independently specified fine equality is needed.

Expected first proofs:

```agda
zero-isEquivalence : IsEquivalence (λ x y → x ≈[ 0 ] y)
map-isEquivalence : IsEquivalence _≈map_
compose-resp : f ≈map f′ → g ≈map g′ → compose g f ≈map compose g′ f′
Approx : Category
```

= Two forgetful functors

Keep zero-error and all-positive-error identification distinct:

```agda
x ∼₀ y = x ≈[ 0 ] y
x ∼₊ y = ∀ ε → 0 < ε → x ≈[ ε ] y

F₀ F₊ : Functor Approx Setoids
```

Both functors retain the carriers and functions, changing only the equality.
The equivalence proof for `∼₊` uses positive rational halving. Nonexpansiveness
preserves both relations, and pointwise zero-error equality of maps implies
pointwise `∼₊` equality. Consequently both are well-defined functors.

There is an identity-on-carriers natural transformation `F₀ ⇒ F₊`, since zero
error implies agreement at every positive error. It need not be an isomorphism.

The existing finite-stage observation distinguishes immediate return from an
almost-sure geometric return at zero error, while all-positive-error observation
identifies them. Therefore exact quantitative comparisons must remain in
`Approx`; do not require them to respect the coarser equality of `F₊ X`.

== Optional closedness

The more specifically metric-like objects may satisfy:

```agda
Closed X = ∀ x y ε →
  (∀ δ → 0 < δ → x ≈[ ε + δ ] y) → x ≈[ ε ] y

closed-zero⇔positive : Closed X → (x ∼₀ y ↔ x ∼₊ y)
```

This is optional, not a field of `ApproxSpace`. The branch's exact finite-stage
relation fails it. Adding a slack closure would change bounds at their boundary,
including positive boundaries, and is not an incidental migration step.

= The quantitative setup

```agda
record QUCSetup : Set where
  field
    C : Category
    I : MonoidalCategory
    M : GradedKleisliTriple I C
    Q : Functor (op C) Approx

underlying₀ underlying₊ : QUCSetup → UCSetup
underlying₀ S = setup S.C S.I S.M (F₀ ∘F S.Q)
underlying₊ S = setup S.C S.I S.M (F₊ ∘F S.Q)
```

Use the existing computational structures; factor out their common packaging
only if that avoids duplication in practice. These four conceptual fields are
the setup. There are no foundational query-budget or simulator-certificate
records, and no separately supplied qualitative presheaf to reconcile with `Q`.

The ordinary theory is available by instantiation of `Abstract2`. For the current
limiting-observation model, `underlying₊` is the intended qualitative choice.
`underlying₀` is also legitimate, but generally stronger.

= Quantitative observational agreement and UC

== Use the existing graded action

```agda
Hom A X B = C [ A , T₀ X B ]
Env A = ApproxSpace.Carrier (Q.₀ A)
prefix W f = μ W X ∘ T₁ W f
run W f e = Nonexpansive.map (Q.₁ (prefix W f)) e

f ≈ᵁ[ ε ] g =
  ∀ W (e : Env (T₀ (W ⊗₀ X) B)) →
    run W f e ≈[ ε ] run W g e
```

The comparison takes place in `Q.₀ (T₀ W A)`. This is the quantitative version
of `Abstract2._≈ᵁ_`, not the bare presheaf kernel. `run` merely names presheaf
pullback along the graded prefix; it is not another operational interpreter.

No budget premise restricts the environments in this foundational definition.
Presheaf identity, composition, and hom-congruence hold at pointwise zero error,
so they transport every quantitative bound exactly. Pullback is nonexpansive.
The existing graded decomposition identities therefore supply the following
theorems; these are to be proved, not added as setup fields.

```agda
ctx-refl  : f ≈ᵁ[ 0 ] f
ctx-sym   : f ≈ᵁ[ ε ] g → g ≈ᵁ[ ε ] f
ctx-trans : f ≈ᵁ[ ε ] g → g ≈ᵁ[ δ ] h → f ≈ᵁ[ ε + δ ] h
ctx-mono  : ε ≤ δ → f ≈ᵁ[ ε ] g → f ≈ᵁ[ δ ] g
ctx-resp  : f ≈C f′ → g ≈C g′ → f ≈ᵁ[ ε ] g → f′ ≈ᵁ[ ε ] g′

ctx-sub : f ≈ᵁ[ ε ] g → (sub s ∘ f) ≈ᵁ[ ε ] (sub s ∘ g)
ctx-ext : f ≈ᵁ[ ε ] g → (u ∙ f) ≈ᵁ[ ε ] (u ∙ g)
ctx-pre : u ≈ᵁ[ ε ] v → (u ∙ f) ≈ᵁ[ ε ] (v ∙ f)
```

These bounds are unchanged because this section uses nonexpansive maps. They
must not be advertised as unchanged-budget versions of the existing query-aware
theorems. That model requires the extension described below.

== Witnesses and composition

```agda
At s ε f g = f ≈ᵁ[ ε ] (sub s ∘ g)
Witness ε f g = Σ[ s ∈ I [ Y , X ] ] At s ε f g
Witness⁺ ε f g = ∀ X′ (a : I [ X , X′ ]) →
                   Witness ε (sub a ∘ f) g

dummy⇒universal : Witness ε f g → Witness⁺ ε f g
universal⇒dummy : Witness⁺ ε f g → Witness ε f g
at-trans : At s ε f g → At t δ g h → At (s ∘I t) (ε + δ) f h
```

For `f : Hom A X B`, `g : Hom A Y B`, `u : Hom B P C`,
`v : Hom B R C`, `s : Y → X`, and `t : R → P`, the composition theorem is:

```agda
at-compose : At s εf f g → At t εu u v →
  At ((id_X ⊗₁ t) ∘I (s ⊗₁ id_R)) (εu + εf) (u ∙ f) (v ∙ g)
```

Simulators remain proof-relevant morphisms. If feasibility is already part of
the grade category, it is inherited here without a second predicate. For an
instance with resource controls, retain the controls carried by these morphisms
as well; forgetting cost evidence is not part of witness composition.

== Exact links to the ordinary theory

Writing `≈ᵁ₀, ≤UC₀` for `Abstract2 (underlying₀ S)` and `≈ᵁ₊, ≤UC₊` for
`Abstract2 (underlying₊ S)`, the expected characterizations are:

```agda
zero-agreement : (f ≈ᵁ₀ g) ↔ (f ≈ᵁ[ 0 ] g)
positive-agreement : (f ≈ᵁ₊ g) ↔ (∀ ε → 0 < ε → f ≈ᵁ[ ε ] g)
zero-emulation : (f ≤UC₀ g) ↔ Witness 0 f g
positive-emulation : (f ≤UC₊ g) ↔
  Σ[ s ∈ I [ Y , X ] ] (∀ ε → 0 < ε → At s ε f g)
```

The agreement results unfold the forgetful functors and commute universal
quantifiers. The emulation results use the existing dummy-adversary theorem.
Never replace the final expression by `∀ ε > 0. Witness ε f g`: that permits
an accuracy-dependent simulator. Fixed positive-error closeness is not transitive
at the same error and is not itself an equality for a `UCSetup`.

= An immediate model and existing ingredients

Let `O` be an approximation space of closed observations, with an observation
map that respects ambient hom equality at zero error:

```agda
Obs : C [ K , Ω ] → O.Carrier
obs-resp₀ : p ≈C q → Obs p ≈O[ 0 ] Obs q
```

The carrier of `Q A` is tests `A → Ω`, with:

```agda
E ≈[ ε ] F = ∀ (m : K → A) → Obs (E ∘ m) ≈O[ ε ] Obs (F ∘ m)
Q.₁ h E = E ∘ h
```

All closures are admitted here. Pullback is nonexpansive because `h ∘ m` is
another closure; categorical laws are observed at zero error. This supplies
an `Approx`-valued presheaf, whose `F₊` image recovers the existing qualitative
test presheaf, subject to checking the precise representation agreement.

Reuse `UC.Approximate.Approximation`, its all-positive equivalence proof,
`UC.Environment.Presheaf`, `UC.Model.Observation.obs-resp`, and the action and
decomposition lemmas in `Abstract2` and `Abstract2.Action`. Do not introduce
new executions or reprove the machine model's trace laws.

This gives a concrete first instance of the clean theory. It does *not* identify
the unrestricted comparison above with the old budget-restricted `_≈ctx[_]_`.

= Resource-sensitive spaces: a separate categorical extension

This section is a construction target, not a claim that the old query model
already defines the required functor. The extension must be established before
claiming equivalence with the resource-sensitive APIs.

== Schedule-valued approximation

Generalize `Approx` to `Approx(V)` for a fixed ordered additive commutative
monoid `V`, using the same four approximation laws. Schedules with pointwise
order and addition are one example. The base category `Approx` uses rational
nonnegative errors; `V = ℚ` is also possible and can preserve the old APIs'
unrestricted signed error type. Do not silently restrict old schedule domains
during an equivalence proof.

Unlike the rational all-positive construction, a general `V` does not by itself
specify a notion of approaching zero. Supply and prove the relevant collapse
functor separately, using an appropriate small-error class or basis.

== Controlled maps

A resource-sensitive pullback may change the error schedule rather than preserve
it. Use maps carrying an explicit error control:

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

As an initial hom equality, require equal controls and pointwise zero-error
equality of functions. This respects composition because controls preserve zero.
Controls are not erased from the categorical data.

For a schedule `ε : Allowance → ℚ≥0` and an allowance transformation `ρ`,
the control `φρ ε = ε ∘ ρ` preserves zero, addition, and order. This explains
schedule substitution as composition of controlled maps, not as a UC-specific
axiom. In particular:

```agda
φρ(ε)(q) = ε(ρ(q))
φρ₂(φρ₁(ε)) = ε ∘ ρ₁ ∘ ρ₂
```

Zero-error identification always forgets controlled maps to setoid maps.
Other collapses require their own preservation condition. All-positive constant
errors, for example, are preserved by pure reindexing of allowances; arbitrary
additive controls need not preserve that notion of smallness.

Construct an actual presheaf into the controlled category, including its control
composition and equality laws. Existing upper-bound arithmetic is not
automatically an exact functor. If it supports only an ordered/lax construction,
state that construction and prove its quantitative theorem rather than silently
treating inequalities as equalities.

== Admitted tests are another index

A distance between tests does not determine the cost of running them. If tests
are restricted by allowance, equip spaces with an increasing family of admitted
elements `Admit q x`. A controlled map then also carries a monotone allowance map
`α` and a proof:

```agda
AdmitX q x → AdmitY (α q) (map x)
```

Compose allowance maps along with the error controls. This defines a filtered
version of the quantitative-space category; alternatively encode allowances in
the presheaf's base category. Choose between these presentations by constructing
the intended model, not by adding a new list of UC-specific resource fields.

For the query model, closure-indexed closeness of tests reads:

```agda
E ≈[ τ ] F = ∀ m c′ → QB c′ m →
  Obs (E ∘ m) ≈ₚ[ τ c′ ] Obs (F ∘ m)
```

Process comparison also restricts the test at allowance `c`, with
`τ c′ = ε (ctxBudget c c′)`. The compatibility of test and closure allowances
with the combined schedule is an instance theorem. It must reproduce the
current `ctxBudget`, `simCost`, and any required monotonicity premises.

An unbounded process may not induce a controlled map on these bounded tests.
Choose admitted morphisms or a suitable indexed construction accordingly; do
not manufacture polynomial certificates for arbitrary processes. Computation
and grade categories may still differ.

== Required resource-aware theorem behavior

The controlled/filtered theory must derive, rather than assume, its transformed
composition bounds. In the current family model the sequential bound is:

```agda
λ n q → ε₁ n q + ε₂ n (simCost q (cost s₁ n))
```

For graded composition it must reproduce:

```agda
λ n q → εu n (simCost q (cf n))
      + εf n (simCost q ((cost t n ⊔ 1) * cv n))
```

These do not follow by calling the controlled maps nonexpansive at unchanged
error. The generalization from `Approx` must explicitly use the controls and
the filtered environment domains. Preserve the exact simulator, cost evidence,
and domain-precomposition behavior used by the existing examples.

= Negligible collapse and quantifier placement

For `Approx(V)`, an existential collapse can use a class `Small` containing zero
and closed under addition:

```agda
x ∼Small y = Σ[ ε ∈ V ] (Small ε × x ≈[ ε ] y)
```

This is an equivalence. Nonexpansive maps preserve it. For controlled maps,
restrict to controls satisfying `Small ε → Small (control ε)` to obtain the
corresponding forgetful functor. Negligible schedules are preserved by the
appropriate polynomial-preserving reindexings, not by arbitrary controls.

This existential construction is not all-positive-error collapse.
`Small = everything` gives existence of some error bound; it is indiscrete when
every pair admits a bound, as for the bounded Boolean observation distance. It
does not generally recover the intended qualitative observation.

Crucially, choose *where* to apply the functor. Collapsing a uniform comparison
of tests against all closures can yield:

```agda
∃ negligible ε. ∀ closures m. compare E F m ε
```

The existing local-negligible environment equality instead allows:

```agda
∀ closure families m. ∃ negligible ε. compare E F m ε
```

Applying the negligible collapse to outcomes before constructing the test
presheaf preserves the latter order. Do not assert that existential collapse
commutes with the universal closure quantifier. A uniformly retained
budget-indexed schedule implies a local conclusion under the appropriate
allowance proofs; the converse requires a separate uniformization theorem.

Likewise, a theorem against filtered tests does not automatically imply the
unrestricted relation of another setup. Establish coverage or transfer to a
target whose admitted contexts match the theorem. For certified families,
the natural base functor forgets certificates; reverse promotion requires
explicit certificates for the compared processes.

= Migration targets and acceptance gates

The desired end state is unchanged: qualitative emulation is always inherited
from `Abstract2` at a specified setup. Quantitative witnesses retain their errors
and simulators and map to the appropriate qualitative instance through proved
collapse or transfer constructions.

Expected migration statements, after their instances have been constructed:

```agda
core-machine⇔canonical : OldCore.≤UC f g ↔ MachineSetup.≤UC f g
local-negligible⇔canonical : Old.≤UCᴺ f g ↔ NegligibleSetup.≤UC f g
budgeted-quantitative⇔generic : Old.≤UC^ωᵉ f g ↔ ControlledFamilyUC f g
```

`ControlledFamilyUC` here names the future controlled/filtered instance, not
the nonexpansive scalar-error relation. Its precise definition and equivalence
are acceptance obligations, not already established results.

Keep `_≤UC^ωⁿ_` as direct negligible agreement, with its identity-simulator
embedding. Keep pointwise `_≤UC^ω_` distinct from emulation in a family category.
Treat `≤UCᵍ` and `≤UC[]ᵍ` as constructors, not additional relations.

Audit emulation becomes a cost-certified qualitative dummy witness:

```agda
AuditWitness cs f g =
  Σ[ s ∈ I [ Y , X ] ] (QBᴵ cs s × (f ≈ᵁ₊ (sub s ∘ g)))

audit⇔canonical : Old.Audit.≤UC[ cs ] f g ↔ AuditWitness cs f g
audit-forget : AuditWitness cs f g → f ≤UC₊ g
```

It is not `Witness 0` for the finite-stage approximation. Preserve event
membership, event absorption, simulator-cost substitution, and the existing
positive slack in safety transport.

= Implementation phases

+ *Approx and forgetting.* Reuse `Approximation`; implement nonexpansive maps,
  pointwise zero-error hom equality, `Approx`, `F₀`, and `F₊`. Verify the example
  separating zero error from all-positive error. Do not impose closedness.
+ *Presheaf and clean UC theory.* Construct the four-field quantitative setup,
  its two underlying setups, and the contextual/witness theorems above. Derive
  them from nonexpansiveness and the existing graded identities, not new UC axioms.
+ *Unrestricted machine instance.* Build the test presheaf from exact observation
  comparison over all closures. Prove its qualitative identification with the
  existing setup. This validates the core independently of resource accounting.
+ *Resource-aware category and instance.* Construct schedule-valued controlled
  spaces and the needed filtered/indexed form. Verify control coherence, admitted
  morphisms, and the actual model before claiming old/new quantitative equivalence.
  Reuse existing budget proofs as instance witnesses.
+ *Family collapse and transfers.* Construct vanishing and local-negligible
  canonical setups with the correct quantifier order. Prove transfers from
  globally retained schedules and explicit process-family certificates.
+ *Equivalences and retirement.* Prove the old/new relations equivalent where
  their semantics coincide. Recompute importers and follow `docs/retirement.md`.
  Migrate consumers before deleting duplicate bodies; retain real distinctions.

Keep `hash-liftⁿ`, `coin-toss-ideal`, and audit carry as regression targets, with
their exact schedule pins. Also check the distinctions between zero and positive
collapse, negligible and vanishing error, a fixed simulator and accuracy-dependent
simulators, and local versus uniform bounds. Successful example retyping alone
does not validate the abstraction's quantifier order.

Place approximate-space categories and forgetful functors in general-purpose
modules; put only the setup, graded comparison, and UC results under
`UC.Quantitative`. Do not turn the resource instance into another foundational
`QUCSetup` record with dozens of fields. No existing Agda source is to be retired
based solely on this design document.
