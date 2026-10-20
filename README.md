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

- `Abstract2.Parallel` proves compatibility of `_≤UC_` with parallel
  composition. Note that this requires a monoidal structure on `𝒞` and
  an effect-combination map `χ : T X B ⊗ T Y D ⇒ T (X ⊗ Y) (B ⊗ D)`,
  both of which need some compatibility laws.

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

`Abstract` and `Standard` are the older grade-on-object presentation.
`Abstract2.Equivalence` and `Abstract2.OAPEmulation` relate it to the
locally graded theory.

## 3. Concrete machine layer

The executable model, predating the abstract layers above:

- `Channel/` — channels (typed communication ports), their category, and a
  wiring DSL (`Selection`).
- `Machine/` — stateful machines communicating over channels, with UC
  security notions stated directly on them; `Constraints` adds extra
  side conditions.
- `SFunM` — the category of stateful, monadic functions.
- `Examples/` — commitment, signature, and basic protocol examples.
- `CategoricalCrypto` — the root module re-exporting this layer.

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
