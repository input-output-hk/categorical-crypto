// Standalone mathematical review note; no external Typst packages required.
// typst compile docs/uc-observation-and-relation-consolidation.typ
#set document(title: "Observation and a single UC theory")
#set page(numbering: "1", margin: 2.2cm)
#set text(size: 10.5pt)
#set par(justify: true)
#set heading(numbering: "1.1")
#let tensor = sym.times.o
#let source(body) = block(fill: luma(96%), inset: 9pt)[
  #set text(size: 9pt)
  #set par(justify: false)
  *Source and status.* #body
]

#align(center)[
  #text(size: 17pt, weight: "bold")[Observation and a single UC theory]

  Mathematical review and consolidation proposal

  14 September 2026
]

This note has two purposes: expose the elementary operation hidden behind
`UC.Model.Observation.Obs`, and explain how the collection of UC relations can
be reduced to one qualitative theory and one quantitative refinement of it.
It reviews *`protocol-rewrite` at `92479a3`*. Statements about existing proofs
mean proof terms inspected in source, not a fresh typecheck. Sections describing
the target architecture are proposals, not claims that its generic theorems
are already implemented.

Module references below have prefix `CategoricalCrypto.` unless they begin with
`ProbabilisticLogic.`. Replace dots by slashes under `src/` and append `.agda`.
References are to the reviewed branch, and this note now lives in the
`protocol-rewrite` worktree.

= Observation without the implementation indirection

== The operation

A closed verdict machine has no externally visible lower interface. Its upper
interface accepts one activation and returns a Boolean. After eliminating empty
message summands, its relevant data are
$
  i : 1 -> D S, quad
  k : S times 1 -> D(S times "Bool").
$
Here $D$ is the probabilistic delay representation, not a rational-valued
probability distribution. Write $x >>= f$ for its Kleisli bind. The observation is
$
  "Obs"(M) = i(*) >>= (s arrow.r k(s,*) >>= ((s',b) arrow.r "return"(b))).
$
That is: *initialize, activate once, and return the Boolean while forgetting the
new state*. Initialization or the transition can diverge. A composite machine's
transition can already contain feedback and arbitrarily much internal
interaction. One activation is not a bounded-time execution.

No further feedback operator, recursive scheduler, or sequence of observations
is introduced by this definition.

#source[
  `UC.Model.Observation`: `Obs u = ⟦ unprocᵒ u ⟧ᴼ`.
  `UC.Machine`: `⟦ M ⟧ᴼ = runᴹ M (ask tt out)`.
  `Protocol.Machine`: unfold `runᴹ`, then the `ask` and `out` cases of
  `runᴹFrom`, to obtain the displayed two-bind expression, with the empty
  summand eliminated by `resumeᴹ`.
]

== Why the source takes the long route

`unprocᵒ` crosses the sealed monoidal category's opacity boundary. It is an
identity retyping behind that boundary, not another interpreter. The seal
exists for elaboration performance.

The general strategy runner supports many interactions, but observation uses
only the strategy that asks once and returns the answer. Reusing it also reuses
its simulation-invariance proof. These are reasonable implementation choices;
they need not define the mathematical presentation.

A direct helper implementing the displayed equation could be related to the
runner once. The existing observation-congruence theorem could then be reused.
This is a proposed refactoring, not a newly checked proof.

#source[
  `UC.Model.Seal`: `unprocᵒ` and the documented opacity boundary.
  `UC.Machine.Run`: `runᴹ-resp-≈ᴹ`.
  `UC.Model.Observation`: `obs-resp` establishes exact observation agreement
  from the sealed category's hom equality.
]

== Forgetting state is not executing stored discard

The general machine record also carries $d:S -> D 1$. The current runner does
*not* call this stored discard when it returns its verdict:

```agda
runᴹFrom m (out b) = returnₚ b
```

Executing $d(s')$ before returning $b$ would be a different observation. For
singleton state, let initialization succeed, let the transition return `true`,
and let discard diverge. Current observation returns `true` with probability
one; discard-aware observation diverges. These disagree even qualitatively.

The omission is not itself a correctness defect: forgetting the final state
after observing a verdict is a legitimate convention, and the existing
`obs-resp` proves that convention respects hom equality. But the convention
must be explicit. Adding stored discard is a semantic change, not a cleanup.
For machines whose discard is pointwise equivalent to pure discard, the two
conventions agree up to the probabilistic monad's equality, not necessarily as
literal delay trees.

#source[
  `Machines.Core`: `State` contains `obj`, `point`, and `discard`.
  `Protocol.Machine`: compiled protocols choose pure discard; `runᴹFrom` ignores
  final state. The general machine category does not impose that choice.
]

== Execution and observational equality are separate definitions

`Obs` produces a `Dₚ Bool`. The next question is when two such representations
count as the same observation. The model compares *both* Boolean outcome masses;
otherwise returning `false` would be indistinguishable from divergence.

There are three levels to keep separate:

+ Literal probabilistic delay representations.
+ Exact cofinal comparison of finite-depth masses, allowing a change of depth.
+ Comparison at every positive rational slack, which forgets the distinction
  between approaching a mass and attaining it at finite depth.

For example, immediate return attains mass one at finite depth; an almost-surely
terminating geometric loop need not. Exact finite-depth comparison distinguishes
them, while the positive-slack observation identifies them when their verdicts
agree. Computing `Obs` does not itself compute a limiting real probability.

#source[
  `ProbabilisticLogic.Dp`: `cum` and `_≈ₚ_`.
  `ProbabilisticLogic.Dp.Advantage`: error-indexed Boolean comparison.
  `UC.Approximate`: `Approximation._∼ᵃ_` and its equivalence proof.
  `UC.Model.Observation`: `_∼ᴼ_`, `observationᵒ`, and `approximateᵒ`.
]

= How many UC relations are really present?

The concern is justified: independently defining qualitative emulation over and
over enlarges the mathematical and code audit. However, some of the apparent
relations are merely aliases, and some retain information that qualitative UC
cannot carry. A consolidation must distinguish these cases.

#set table(inset: 5pt, stroke: 0.4pt + luma(75%))
#table(columns: (1.05fr, 1.8fr),
  table.header([*Current name*], [*What it actually denotes*]),
  [`Abstract2._≤UC_`], [The canonical qualitative emulation preorder for a `UCSetup`.],
  [`UC.Emulation._≤UC_`, `_≤UC⁺_`], [Separate dummy and adversary-quantified
    definitions over the weaker `UCBase` interface. Genuine qualitative duplication.],
  [`_≤UCᴺ_`], [An instance/renaming of the core emulation relation with local
    negligible observation on the family category.],
  [`_≤UCᵁ_`], [An import-site alias of inherited `Abstract2` on the family setup;
    the current instance uses vanishing, not negligible, observation.],
  [`_≤UC^ω_`], [A pointwise wrapper: each protocol-family member satisfies the
    single-level inherited order. Not the order in the family category.],
  [`_≤UC^ωⁿ_`], [Direct contextual agreement with a retained negligible schedule.
    No simulator field; despite its name, it is symmetric.],
  [`_≤UC^ωᵉ_`, `_≤UC^ωᵉ⁺_`], [Quantitative emulation retaining a certified simulator
    family and a context-uniform negligible error schedule; in the universal
    form, both witnesses may depend on the adversary.],
  [`UC.Audit._≤UC[_]_`], [Qualitative dummy emulation with a certificate for the
    chosen simulator at a specified query budget.],
  [`≤UCᵍ`, `≤UC[]ᵍ`], [Theorem constructors from exact machine factorization,
    not additional relations.],
)

#source[
  Definitions: `Abstract2`; `UC.Emulation`; `UC.Family.Negligible`;
  `UC.Model.Family.Uniform`; `UC.Asymptotic`; `UC.Asymptotic.Family`;
  `UC.Asymptotic.Contextual`; `UC.Audit`; `UC.Graded`; `UC.Seam.Graded`.
]

There are already links to the canonical order. `UC.Model.Bridge.≤UCᶜ⇔≤UC`
proves equivalence of core and inherited machine emulation.
`UC.Asymptotic.Family.≤UC^ωᵉ⇒≤UCᵁ` forgets quantitative evidence into inherited
family UC, provided the compared process families have the certificates needed
to be morphisms of that category. Audit witnesses also forget to core emulation
and then use the machine bridge. The problem is not absence of every bridge;
it is that equivalences and forgetful maps are scattered around a parallel API.

= Target: one qualitative definition

Keep one public definition of the qualitative emulation preorder:
$
 f <=_("UC") g
 quad <=> quad
 forall a:X -> X'. exists s:Y -> X'.
 "sub"(a) compose f approx^U "sub"(s) compose g.
$
This is `Abstract2`, parameterized by a setup. The dummy-witness characterization
is a theorem, not another independent order:
$
 f <=_("UC") g
 quad <=> quad
 exists s:Y -> X. f approx^U "sub"(s) compose g.
$
The existential here is proof-relevant: the simulator is available to later
proofs. No truncation or minimization over simulators is intended.

The concrete machine model, the vanishing family model, and the negligible
family model should each supply a `UCSetup` and inherit the same definition and
theorems. Vanishing and negligible observations remain different presheaves on
the same family category; consolidation must not identify their equalities.

The machine and vanishing-family inherited setups already exist. The
negligible observation exists, but its public emulation route still goes through
`UC.Emulation`. The intended change there is to supply the corresponding
standard setup and use its inherited order, with conversion lemmas for existing
consumers. It is not to redefine negligible security as vanishing security.

There is one qualification: a bare `UCBase` has less structure than a
`UCSetup`. Arbitrary clients of that weaker interface cannot be silently
rebased. Audit its actual consumers. Concrete monoidal clients should migrate;
if genuine weaker clients remain, keep a clearly scoped small result for them
rather than presenting it as a competing universal-composition theory.

#source[
  `Abstract2`: `dummy-complete`, `≤UC⇒dummy`, `≤UC-trans`, `UC-compose`.
  `UC.Model.Setup` instantiates `Standard2`.
  `UC.Core.Bridge` and `UC.Model.Family.Uniform` give inherited family machinery.
  `UC.Family.Negligible` supplies `Observationᴺ` but exports core emulation.
]

= Target: a generic quantitative refinement

This section proposes an interface and theorem organization. It does not claim
that merely renaming the current quantitative definitions proves these results.

== Start with an approximate presheaf

The metric-valued-presheaf idea is the right organizing principle. For a genuine
pseudometric-valued presheaf with nonexpansive pullbacks, zero-distance
identification gives a setoid-valued presheaf, hence the presheaf required by
`UCSetup`. Separation is unnecessary.

For this branch, an error-indexed relation is preferable to a numerical metric.
Limiting probabilities need not be rational, and the existing approximation
interface does not construct their suprema. Equip each environment carrier
$E(A)$ with $x approx[epsilon] y$, with zero reflexivity, symmetry, an additive
triangle rule, and error monotonicity. Require pullback to preserve this relation.
Functor laws and ambient hom equality must transport quantitative comparisons
without changing their bounds. A proof of merely qualitative equality is not
enough for that obligation.

The qualitative presheaf is then obtained by a specified collapse. For instance,
$x tilde.op y$ may mean $forall epsilon > 0. x approx[epsilon] y$.
Fixed positive-error closeness is generally not transitive: two error-$epsilon$
steps give error $epsilon + epsilon$, not error $epsilon$. It therefore cannot
simply be used as the equality of a `UCSetup` presheaf. This is why a genuine
quantitative refinement remains necessary alongside the qualitative instances.
Other collapses use an admissible class of small error schedules, such as
negligible functions. Each collapse needs an equivalence proof and preservation
by pullback; these are generic mathematical obligations, not per-protocol proofs.
For all-positive-error collapse, the existing `ErrorAlgebra` supplies zero below
positive errors and positive-error splitting (`half-pos`, `half-sum`), which
justify the usual halving argument for transitivity. General quantitative
composition also needs the appropriate laws for zero and addition; this minimal
record is not by itself a full ordered additive monoid.

Keep the quantitative carriers and their sufficiently fine representation
equality available before collapsing. In this model, positive-slack equivalence
does not imply exact zero-error finite-depth agreement. One must not quotient by
the former and then assume every exact quantitative bound descends unchanged.
The warning applies to exact boundary bounds at positive errors as well as to
zero error; these relations are not automatically closed balls of a metric.

#source[
  Existing reusable pieces: `UC.Approximate.ErrorAlgebra`, `Approximation`,
  `Induced.observation`, and `Induced.approximate`;
  `UC.Environment.Presheaf.ℰᴼ`; `UC.Environment.Approximate.absorbᵘ`.
  These construct an observation-derived presheaf and its collapse. A fully
  general metric/approximate-valued presheaf interface was not located in the
  reviewed sources; do not mistake that specific construction for an already
  implemented arbitrary-presheaf theorem.
]

== Quantify the existing graded action, not a new experiment calculus

Use the existing operation
$
 "prefix"_W (f) = mu_(W,X) compose T_W (f), quad
 "run"(W,f,e) = E("prefix"_W (f))(e).
$
For $f,g:A -> T_X B$, define its quantitative contextual comparison by
$
 f approx^U [epsilon] g
 quad <=> quad
 forall W. forall e in E(T_(W tensor X) B).
 "run"(W,f,e) approx[epsilon] "run"(W,g,e).
$
Here $tensor$ denotes the grade tensor. This is the quantitative version of the
same action used by `Abstract2._≈ᵁ_`, not of the bare kernel of the presheaf.
Ancillas must not disappear during generalization, and `GradeStable` must not
be silently assumed.

An explicit quantitative witness at simulator $s$ and error $epsilon$ is simply
$f approx^U [epsilon] "sub"(s) compose g$. Keep $s$, its resource certificate
when required, and $epsilon$ as data. The simulator-existential and
adversary-quantified presentations should be derived from this one construction,
with their relationship proved once under the stated action and resource laws.
In the universal form the quantifiers are adversary, then simulator and error
schedule, then environments. No single schedule shared by all adversaries is
asserted.

#source[
  `Abstract2.Action`: `prefix`, `run`, `run-sub`, `run-resp-≈ᵁ`, and `runs⇒≈ᵁ`.
  `UC.Asymptotic.Contextual` currently implements a machine-specific quantitative
  contextual relation and the two certified-simulator presentations. Their
  abstraction should be extracted, not supplemented by a third implementation.
]

== Resource bounds require reindexing, not just nonexpansiveness

A single unbudgeted nonexpansive presheaf does not explain all the current
query-sensitive bounds. Pulling a context across a certified process changes
its allowance. A budget-indexed version needs a context transformation
$"Env"(B,q) -> "Env"(A,rho_h (q))$, with appropriate identity, composition,
and graded-action laws. Error schedules transform by substitution along $rho_h$.
In particular, the decompositions for simulator substitution and graded
composition, and substitution's identity and composition laws, must preserve
every error bound. Validity only after qualitative collapse is insufficient.

Thus sequential emulation composition carries the bound
$
 epsilon_1 (n,q) + epsilon_2 (n,rho_(s_1) (n,q)).
$
For the current query model,
$rho_s (n,q) = "simCost"(q,c_s (n)) = q dot max(c_s (n),1)$.
Certifying the compared processes themselves is needed when they move into
contexts, or when they must become morphisms of a restricted family category;
it is not needed merely to state agreement of their observations.

The generic quantitative theorem must retain these substitutions and prove that
the chosen small-error class is closed under them and addition. A plain
qualitative composition proof cannot recover that evidence. The achievable
consolidation is *one reusable quantitative proof*, instantiated by models,
not deletion of quantitative composition altogether.

#source[
  `UC.Budget`: `ctxBudget`, `simCost`, and absorption laws.
  `UC.Approximate`: `GradedBound-reindex` and negligible closure lemmas.
  `UC.Asymptotic.Compose`: `≤UC^ωᵉ-trans` and `UC-composeᵉ` currently retain the
  actual substitutions. The explicit `Allowance-mono` premise the latter carried
  at this snapshot is gone since 2026-09-21 — the certificate-enlargement proof
  was done, and `≈ctx-pre` now substitutes exactly.
]

= What forgetting quantitative evidence can prove

== The bridge to classical UC

Prove a generic comparison theorem saying that quantitative agreement with an
admissibly small error implies agreement in the collapsed presheaf. Applying it
at the same simulator gives a witness-preserving map into `Abstract2._≤UC_`.
The target setup, its collapse, and its admitted morphisms must be explicit.

For a metric zero-distance collapse, a fixed positive error does not imply
classical UC. A sufficient witness is
$
 exists s. forall epsilon > 0.
 f approx^U [epsilon] "sub"(s) compose g.
$
For a negligible-family collapse, a retained schedule negligible at every
admitted polynomial allowance supplies the corresponding qualitative witness.
The output may instead use a vanishing observation, but that forgets more
information and must be named accordingly.

Where the collapsed equivalence is *defined* by all positive errors, the
fixed-simulator all-positive-error formulation agrees with the classical dummy
characterization, by commuting universal quantifiers, using the same carriers,
admitted environments, and simulator morphisms on both sides. This does not equate
arbitrary fixed-error witnesses with classical UC.

== Two invalid quantifier exchanges

First,
$ exists s. forall epsilon > 0. P(s,epsilon) $
must not be replaced by
$ forall epsilon > 0. exists s. P(s,epsilon). $
The second permits a different simulator at every accuracy. Taking the infimum
of simulator distances and finding zero does not supply an attaining simulator.

Second, a local-negligible presheaf allows the negligible witness to depend on
the fixed context family. Its classical dummy order has the pattern
$
 exists s. forall "context family". exists delta in "Negl".
 P(s,"context family",delta).
$
The retained global quantitative schedule has the stronger pattern
$
 exists s. exists epsilon. forall n. forall "context at n".
 P(s,n,"context at n",epsilon(n,q_"context")).
$
Here $epsilon$ must be negligible along all admitted polynomial allowances.
The first pattern does not generally provide the second. A reverse bridge
requires a real uniformization theorem, not a notation change. There is also a
domain distinction: the first ranges over admitted families of contexts, whereas
the second quantifies contexts independently at each level. A reverse bridge
must address both distinctions.

Likewise, ordinary emulation does not manufacture a cost certificate for its
chosen simulator. Certificates can be built into the grade category when its
morphisms compose appropriately, but a fixed budget need not be closed under
composition. Budget-indexed witness refinements still have a role.

= Consolidation plan and acceptance criteria

+ *Make setup instances canonical.* Route machine, vanishing-family, and
  negligible-family qualitative emulation through `Abstract2`. State and prove
  conversions before migrating existing consumers; do not delete behavior or
  weaken observation merely to remove a name.
+ *Expose one dummy-witness characterization.* Use it for certificate-carrying
  refinements, rather than independently redefining a qualitative order and
  reproving its laws in each module.
+ *Extract one quantitative action theorem.* Reuse approximation, prefix, and
  resource-reindexing laws. Instantiate it for machines and families. Export a
  generic forgetting theorem to the chosen classical setup.
+ *Name agreement as agreement.* The current symmetric `_≤UC^ωⁿ_` should be
  presented as negligible contextual agreement; its identity-simulator map to
  emulation is a theorem, not a reason to call it another UC order.
+ *Keep pointwise assertions visibly pointwise.* `_≤UC^ω_` need not be a public
  foundational relation. Its relationship to family security has actual
  premises, including totality in the existing protocol comparison theorem.
+ *Keep audit data, not a second audit theory of emulation.* A budget certificate
  belongs to the selected dummy simulator witness. Event membership and event
  absorption remain separate hypotheses of safety transport. They cannot be
  erased with the duplicate qualitative definition.
+ *Label constructors as constructors.* `≤UCᵍ` and `≤UC[]ᵍ` can remain useful
  exact-factorization lemmas without being counted as independent relations.

The mathematical audit should end with one diagram: quantitative witnesses map
to the canonical qualitative order of an explicitly named setup; observation
changes map between setup instances under proved preservation laws. Every
remaining refinement must say exactly what extra data it retains and what its
forgetful map loses. No new concrete UC relation should require another copy of
the qualitative dummy-adversary and universal-composition proofs.

This is fixable without a second experiment category, a foundational simulator
record, or a different UC definition for each example. The unavoidable extra
theory concerns quantitative error and resource transport. The avoidable part
is repeatedly rebuilding qualitative UC around that data.
