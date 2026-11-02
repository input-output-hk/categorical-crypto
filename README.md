# Categorical Cryptography

A framework for universally composable (UC) cryptography built on
category theory, implemented in Agda. Protocols, functionalities,
adversaries, and environments are all categorical data; UC emulation
and its metatheory (completeness of the dummy adversary, universal
composition) are proved abstractly, and instantiated at concrete
models.

Documentation can be found [here](https://input-output-hk.github.io/categorical-crypto/).

## 1. General category theory (`src/Categories/`)

- `GradedKleisli` (+ `.Regrade`): the [graded Kleisli
  category](https://www.irif.fr/~mellies/papers/fossacs2016-final-paper.pdf)
  , with the forgetful/free adjunction `F ⊣ U`. `Regrade` is the
  change-of-grading functor, i.e. functoriality of `Kl` in the grading.
- `GradedKleisli.Functorial.Category`: the category of graded
  monads. Also shows functoriality of `Kl` in the graded monad itself.
- `LocallyGraded`: [locally `ℐ`-graded categories](https://ncatlab.org/nlab/show/locally+graded+category) in their elementary presentation.
  - `LocallyGraded.Kleisli` is the locally-graded Kleisli construction
  - `LocallyGraded.FreeActegory` freely constructs an actegory from a locally graded category
    `LocallyGraded.FreeActegory.Kleisli` the **bridge theorem**: the
    free actegory of the locally graded Kleisli is equivalent to `GradedKleisli`.
- `KernelCongruence`: the kernel congruence of a functor (`f ∼ g` iff
  `F₁ f ≈ F₁ g`).
- `Coherence.Monoidal` — solvers for morphism equality in monoidal
  categories. Has an optional reflection front-end.
- `Coherence.Symmetric` — same as the previous, but for SMCs and no
  reflection so far.

## 2. Abstract UC layer (`src/CategoricalCrypto/`)

- `UCSetup` packages a base category 𝒞 of computations, a monoidal
  category ℐ of adversarial interfaces, a graded Kleisli triple ℳ,
  and an environment presheaf ℰ. The kernel congruence `≈ℰ` expresses
  observational equivalence: no environment distinguishes the two
  computations.

- `Abstract2` develops UC security in the locally graded presentation.
  A protocol is a graded Kleisli morphism `f : A ⇒ T₀ X B`, where X
  is its adversarial interface; adversaries and simulators act by
  regrading. Security uses contextual observational equivalence
  `≈ᵁ`: two protocols agree under `≈ℰ` after every prefix context
  `μ ∘ T₁ Y −`. UC emulation `_≤UC_` requires every adversary against
  the real protocol to have a simulator against the ideal protocol.
  The theory proves reflexivity, transitivity, completeness of the
  dummy adversary, and universal composition for sequential
  graded-Kleisli composition.

  `GradeStable` says that each graded action `T₁ Y` preserves `≈ℰ`.
  Under this assumption `≈ᵁ` is equivalent to `≈ℰ`, otherwise `≈ᵁ` is
  finer.

- `Abstract2.Operation` proves that an operation on an indexed family of
  protocols preserves `_≤UC_` if it preserves `≈ᵁ` and commutes with
  regrading through a supplied map of simulators. This implies
  compatibility with parallel composition and traces, but their manual
  proofs are shorter.

- `Abstract2.Parallel` proves compatibility of `_≤UC_` with parallel
  composition. Note that this requires a monoidal structure on `𝒞` and
  an effect-combination map `χ : T X B ⊗ T Y D ⇒ T (X ⊗ Y) (B ⊗ D)`,
  both of which need some compatibility laws.

- `Abstract2.Trace` proves compatibility of `_≤UC_` with a lifted feedback
  operation that commutes with regrading and preserves `≈ᵁ`.

- `UCSetup.Morphism` defines structure-preserving maps between setups,
  combining a graded-monad morphism with a map of environment
  presheaves. `Abstract2.Morphism` proves preservation and reflection
  of UC emulation under suitable hypotheses on these maps and
  grade stability.

- `Abstract2.WideSubcategory` restricts a setup to an admissible class
  of computations closed under the graded-monad operations, and
  relates security in the restricted and ambient setups.

- `Standard2` specializes the theory to a monoidal category with
  𝒞 = ℐ and `T₀ X B = X ⊗ B`: attaching an adversarial interface
  is tensoring with it. `Standard2.Morphism` constructs maps between
  these setups from strong monoidal functors and compatible maps
  of environment presheaves.
  `Standard2.Parallel` is an optional extension for symmetric monoidal
  categories, deriving `ParallelStable` and `UC-⊠` without extra
  assumptions on the environment presheaf.
  `Standard2.Trace` lifts a trace on the computation category to protocols,
  assuming trace congruence and output naturality (absent from the current
  library's `Traced` record), with contextual trace preservation required
  separately for `UC-trace`.

`Abstract` and `Standard` are the older grade-on-object presentation.
`Abstract2.Equivalence` and `Abstract2.OAPEmulation` relate it to the
locally graded theory.

## 3. Concrete machine layer

The executable model, predating the abstract layers above:

- `Channel/` — channels (typed communication ports), their category, and a
  wiring DSL (`Selection`).
- `Machine/` — stateful machines communicating over channels.  `Machine.Core`
  still carries the original hand-rolled UC notions, but they are shadowed by,
  and definitionally agree with, the abstract ones `Machine.UC` imports;
  `Constraints` adds extra side conditions.  `Machine.Iso` is the state
  isomorphism `_≅ᴹ_`, a bijection of state spaces preserving the step relation
  in both directions, with its congruences and the associativity of trace
  composition; `Machine.Category` assembles the category of machines, the
  identity laws being instances of the relay lemmas of
  `Machine.Reindex.Post` (composing with a forwarder relabels the other
  machine); `Machine.MonoidalCategory` bundles it as a symmetric monoidal
  category, with the coherence laws proved as forwarder computations
  (`Machine.Monoidal.*`) and the naturality of the Kleisli shuffles discharged
  by the coherence solver.  `Machine.UC` instantiates `Standard2` at the
  reversed monoidal category of machines (hence the grade on the right, with
  environments as joint ancilla tests), proves `GradeStable`, and so has
  `≈ᵁ ⇔ ≈ℰ` and the UC metatheorems for concrete machines;
  `Machine.UC.Kleisli` identifies the hand-rolled `_∘ᴷ_` with the abstract
  Kleisli composition up to the grade swap.
- The proof engineering behind all of that, and the bulk of the layer:
  `Machine.Forwarder` (forwarders are the stateless, total, deterministic
  machines, closed under all three machine builders, so an equation between
  composites of forwarders collapses to a finite message-level case split),
  `Machine.Reindex` and its submodules (`Reindex`/`Pair`/`Trc`, the three
  primitives every builder decomposes into, with the structural lemmas
  relating them), `Machine.Message` (the shared message-level inversion
  lemmas) and `Machine.NAry` (the n-ary rewiring laws a multi-party transfer
  argument needs).  These stay internal; the root module does not re-export
  them.
- `SFunM` — the category of stateful, monadic functions.
- `Examples/` — commitment, signature, and basic protocol examples;
  `Examples.Channels` is the first worked UC statement on concrete machines.
  It proves the monotonicity direction: the length-leaking secure channel
  realizes the message-leaking one, the ideal specification being permissive
  enough that the simulator can discard what it is given.  The converse
  non-realization is not proved.
- `CategoricalCrypto` — the root module, re-exporting the public surface of
  this layer.

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
