# Categorical Cryptography

A framework for universally composable (UC) cryptography built on category
theory, implemented in Agda (`--safe --without-K` throughout). Protocols,
functionalities, adversaries, and environments are all categorical data; UC
emulation and its metatheory (reflexivity, transitivity, completeness of the
dummy adversary, universal composition) are proved once, abstractly, and then
instantiated at concrete models.

Documentation can be found [here](https://input-output-hk.github.io/categorical-crypto/).

The development is organized in four layers, from generic category theory down
to executable machines. Each layer only imports the ones above it.

## 1. Categorical substrate (`src/Categories/`)

General-purpose category theory, independent of cryptography:

- `Monad.Graded` — graded monads as graded Kleisli triples over a monoidal
  grading category ℐ (`T₀`, `sub`, `return`, `ext`, and derived `T₁`, `μ`);
  `Monad.Graded.Pullback` — change of grading along a lax monoidal functor.
- `GradedKleisli` (+ `.Regrade`) — the *grade-on-object* graded Kleisli
  category: objects are pairs ⟨A, X⟩ of a carrier and an interface, homs are
  a coend `∃ k. 𝒞[A, T₀ k B] × ℐ[X ⊗ k, Y]` quotiented by `Slide`, with the
  forgetful/free adjunction `F ⊣ U`. `Regrade` is the change-of-grading
  functor between such categories.
- `LocallyGraded` — locally ℐ-graded categories (categories enriched in
  presheaves on ℐ under Day convolution, in elementary presentation; Wood
  1976/78), the *grade-on-morphism* point of view. `LocallyGraded.Kleisli` is
  the naive graded Kleisli presentation of a triple; `LocallyGraded.Collage`
  the collage `∮` of a locally graded category; and
  `LocallyGraded.Collage.Kleisli` the **bridge theorem**: the collage of the
  naive presentation *is* `GradedKleisli` — objects, homs, identities and
  composition agree on the nose. This connects the two points of view and is
  the formal backbone of the two UC formulations below.
- `KernelCongruence` — the kernel congruence of a functor (`f ∼ g` iff
  `F₁ f ≈ F₁ g`), the notion of observational equality used everywhere.
- `Diagram.Coend.Setoids` — concrete Setoid-valued coends with a definitional
  mapping-out principle (the substrate for the collage).
- `Functor.Monoidal.CurriedTensor` (+ `.Properties`) — the tensor `X ⊗ −` as
  a graded monad; this is the graded monad of the standard instantiations.
- `CoherenceIsos` — the wide subcategory `Coh(ℐ)` of coherence isomorphisms.
- `Coherence.Monoidal` — decision procedures for morphism equality in
  monoidal categories. Has an optional reflection front-end.
- `Coherence.Symmetric` — same as the previous, but for SMCs and no
  reflection so far.

## 2. Abstract UC layer (`src/CategoricalCrypto/`, parametric)

Everything here is parametric over a single record, `UCSetup`: a base category
𝒞 (machines), a monoidal category ℐ (adversary interfaces), a graded Kleisli
triple ℳ over them (how an interface is attached to a machine), and a
presheaf ℰ on 𝒞 (the environments). Security is always relative to the
kernel congruence `≈ℰ` of ℰ — two morphisms are equal when no environment
distinguishes them.

Two equivalent formulations of UC emulation are developed:

- `Abstract` — the *grade-on-object* formulation. Protocols live in the
  graded Kleisli category `OAP` (open adversarial protocols) of ℳ, whose
  morphisms carry an explicit attack component; `OP` restricts that component
  to coherence isomorphisms ("attack-free" protocols). `_≤UC_` compares
  OP-morphisms with two simulators (output-side and input-side), and the four
  metatheorems are proved, with `UC-compose` using the invertibility of
  OP-interface parts. `Abstract2.OAPEmulation` shows `_≤UC_` is definitionally
  the same relation stated on OAP-homs, so OP earns its existence exactly at
  the composition theorem.
- `Abstract2` — the *locally graded* (one-sided) formulation. A protocol is a
  bare graded-Kleisli morphism `f : A ⇒ T₀ X B` (the adversary interface X is
  the grade), and an adversary/simulator acts by reindexing (`sub`).
  Observational equivalence is the U-kernel `_≈ᵁ_` — all prefix-context
  components `μ ∘ T₁ Y f` agree under `≈ℰ` — and over it all four
  metatheorems, including universal composition, are **hypothesis-free**.
  `GradeStable` (ℰ is a lax ℳ-module, equivalently bare kernel = U-kernel)
  is needed only by `bridge`, which ingests a bare `≈ℰ` security artifact
  into the compositional world: a conservation law paid once at artifact
  ingestion, never in the metatheory.
- `Abstract2.Equivalence` — the machine-checked hierarchy connecting the two:
  `≤UC` over `≈ᵁ` implies OAP-`≤UC` at unit input grade implies the bare
  one-sided relation, unconditionally; both converses cost exactly
  `GradeStable`.

`Standard` / `Standard2` instantiate the respective layers at 𝒞 = ℐ = a
monoidal category of machines with ℳ = the curried tensor (attaching an
interface = tensoring a channel on). `RandomOracle` / `RandomOracle2` package
a Merkle–Damgård-vs-random-oracle security proof as a record of concrete
artifacts (`ROData`) and derive `MD≤UC-RO` from it.

## 3. Probabilistic model over axiomatized machines

The concrete environment model — machines indexed by a security parameter,
distinguished up to vanishing total-variation distance under polynomial query
budgets — is built parametrically over an *axiomatized* machine layer, so it
is independent of any particular machine implementation:

- `MachineAxioms` — one security level as a record: a monoidal category 𝕄, a
  verdict channel, observation semantics (`⟦_⟧`, a pseudometric `adv` on
  observations), and a query-budget instrument `QB` with its composition laws.
- `Data.Nat.Poly` — polynomial bounds on ℕ-functions and their closure
  properties.
- `FamilyCategory` — the security-parameter family category `𝒞^ω`: objects
  are ℕ-indexed families of 𝕄-objects, morphisms carry a (proof-irrelevant)
  polynomial query-budget witness `PolyQB`.
- `VanishingTV` — the vanishing-TV setoid `⇝` on observation sequences; the
  environment presheaf `ℰᵗᵛ` on `𝒞^ω` whose tests are budgeted *joint
  ancilla tests*; the proof that this ℰ is grade-stable, given uniqueness of
  identity proofs for 𝕄's objects (so `≈ᵁ = ≈ℰ` here and the `Abstract2`
  bridge is free); and the ε-bounded relation `_≈ℰ[_]_`
  with `absorb`, the ingestion gate turning concrete vanishing bounds into
  kernel equalities.
- `StandardTV` — everything plugged together: the `Standard2` setup at
  𝒞 = ℐ = `𝒞^ω`, with `GradeStable` discharged and `≈ᵁ ⇔ ≈ℰ` as the
  headline corollary.

## 4. Concrete machine layer

The executable model (predating the layers above; connecting it to
`MachineAxioms` is planned work):

- `Channel/` — channels (typed communication ports), their category, and a
  wiring DSL (`Selection`).
- `Machine/` — stateful machines communicating over channels, with UC
  security notions stated directly on them; `Constraints` adds extra
  side conditions.
- `SFunM` — the category of stateful, monadic functions.
- `Examples/` — commitment, signature, and basic protocol examples.
- `CategoricalCrypto` — the root module re-exporting this layer.

## 5. String-diagram solver contracts

`Coherence.Symmetric.Solver` exposes `solveH!` for free-SMC coherence.
Its internal `APROP.Hypergraph.Solver.Split.solveTerm?`
search is sound but incomplete: `just pf` certifies `f ≈Term g`, while `nothing`
proves neither inequality nor the absence of a graph isomorphism. This search
is not a public frontend diagnostic and does not describe driver firing.
`solveH!` transports a successful certificate into the target category; it
does not decide arbitrary target-category equality. Leave its implicit
`T (is-just …)` success witness inferred rather than supplying `{tt}` or
introducing explicit-`refl` variants (see the
[matched witness comparison](docs/smc-solver-performance.md#matched-success-witness-comparison-2026-10-09)).

`rewriteH!` takes an explicit context. `rewriteAutoₙ!` and `rewriteDeepₙ!`
compute the rewritten endpoint from a syntactic or deep occurrence,
respectively; their frame helpers are private. For chained proofs, use
`rewriteDeepTo!` with a caller-stated endpoint. `drive` returns a term with its
proof and `normalize!` proves the computed endpoint; `normalizeTo!` proves a
caller-stated endpoint. All are available through `Solver C objects generators`.

The full-isomorphism facade `Solver.Match.FindIso.findIso` rejects unequal
vertex or edge counts before interface seeding or DFS. `findIsoᵀ` delegates
through tabulation. This is a necessary condition for finite two-sided inverses,
not a completeness guarantee. The shared search and partial-bijection machinery
remain size-independent: `Rewrite.SubMatch.subMatch` still searches unequal-size
embeddings.

`Model.PrunedCompose.hComposeP` is label-preserving pruned boundary reindexing,
not an unrestricted pushout on raw graphs with repeated boundaries. Its seam
contract is: equal `K.dom` vertices imply equal corresponding `G.cod` vertices.
`hComposeP-impl.remapP-seam` proves the pointwise seam under `SeamCompatible`;
`Unique K.dom` suffices. `Unique G.cod` has a separate injectivity role.
Translated linear graphs supply the stronger invariants used by soundness;
the raw composition API and its boundary-label theorems do not gain premises.

The bare decoder skips edges whose inputs cannot be extracted. Its final
boundary permutation alone does not certify acyclicity or linearity of a raw
graph; translated-term guarantees use separate linearity and order proofs.
The rewrite driver tries directional `Rule`s in list order at each rule's first
deep focus, firing only when that focus certifies, and restarts after a firing.
Fuel bounds the number of certified firings, not the amount of progress: a
reflexive or recreating rule can consume fuel without advancing the diagram.
It stops at zero fuel or when no tried focus certifies; neither stopping case
guarantees a complete sweep or a normal form. `normalizeTo!` additionally
certifies the driver's result against the caller-stated endpoint.

### Cardinality-rejection benchmark

```sh
python3 benchmarks/find-iso-size-mismatch.py build
python3 benchmarks/find-iso-size-mismatch.py run --label sample --repetitions 3
```

The fixture translates a chain of identical nullary scalar generators and
tabulates its hypergraphs. Before the cardinality guard, every injection prefix
can survive label and endpoint checks; this motivates the fixture, not an exact
search-node count or a general graph-isomorphism complexity claim.
The bounded kernel suite `FindIsoSizeMismatchTests` covers both directions,
equal-size controls, both cardinalities and unequal-size submatching.

Each sample uses a fresh process. The `search` setup forces counts, ordered
boundaries and every edge's endpoints, rather than just the graph constructor,
then forces `is-just (findIso H J)` separately. Its scalar label code is constant:
MAlonzo erases that projection, so setup does not force the label records or
their proof fields. The independent `full` phase forces
`is-just (findIsoᵀ ⟪s⟫ ⟪t⟫)` including construction. Neither phase forces every
proof field of a successful certificate; kernel tests separately exercise
soundness. Wall and process-CPU times are milliseconds.
The runner records source/binary hashes, compiler, raw samples and process
occupancy under `_build/find-iso-size-mismatch/`; construction, generated-symbol
adaptation and compilation are outside the measured phases.

Sizes are bounded by nine edges, with a ten-second cutoff per process.
A timeout is not a rejection. The runner observes other toolchain jobs every
250 ms without controlling them; overlapping jobs invalidate timing claims,
and very short intervening jobs can escape sampling. Use matched, uncontended
before/after builds on the same machine, compiler and RTS settings
(`-O2`, `-M3G -H64M`) for any quantitative comparison.

On Linux/aarch64 with pinned GHC 9.10.3, three fresh-process samples per
case gave the following median wall times. The baseline used the current
`integrate/2-coherence-solver.review9` snapshot at `07d5bc9c6ae7`, not the
review's older measurements; both runs observed no other toolchain jobs.

| Scalar edges | Accepted | Search before (ms) | Search after (ms) | Full before (ms) | Full after (ms) |
| --- | --- | ---: | ---: | ---: | ---: |
| 9 → 8 | no | 653.683251 | 0.001708 | 642.728250 | 0.007250 |
| 8 → 9 | no | 0.044084 | 0.002000 | 0.055792 | 0.006959 |
| 8 → 8 | yes | 0.050917 | 0.053917 | 0.056958 | 0.061625 |
| 9 → 9 | yes | 0.063292 | 0.068500 | 0.072125 | 0.076292 |

For 9 → 8, separately forced setup took 0.026209 ms before and 0.025167 ms
after. These measurements establish the avoidable rejection cost for this
bounded scalar family, not a general solver speedup; microsecond controls
and occupancy sampling do not support precise relative-overhead claims.

# Contributing

Contributions are welcome, however please make sure that the
contribution is of reasonable quality. AI contributions are welcome,
but they must clear a higher quality bar than human
contributions. **If you have access to AI tools, you should use them
to do better work, not just more work.**

# AI disclaimer

AI tools were used in the development of this project. All code and
designs were extensively reviewed manually, but while the maintainer
tries very hard to keep this codebase free from AI slop there is no
guarantee that there doesn't sit some low quality bit somewhere that
was missed.
