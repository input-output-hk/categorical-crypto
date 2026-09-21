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
- `Coherence.Monoidal` (literate entry point) — reflection-based decision
  procedures for morphism equality in (symmetric) monoidal categories
  (`Structural` / `Mor` / `Symmetric`), used as proof engineering throughout;
  `FreeMonoidal` and `FreeStrictMonoidal` are their term languages.

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
- `UC.Family` / `UC.Family.Vanishing` — the security-parameter family category
  and the vanishing-bound layer over it.
- `UC.Environment` — the environment presheaf and the adaptive single-ancilla
  indistinguishability `_≈ℰ_`, with `grade-stable` a theorem rather than a
  hypothesis.
- `UC.Quantitative.Observed` — the ε-indexed form of that relation and its
  collapse; `UC.Machine` plugs the whole stack into the machine model.

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
