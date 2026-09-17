# Categorical Cryptography

A framework for universally composable (UC) cryptography built on category
theory, implemented in Agda (`--safe` throughout; the generic and abstract
layers are also `--without-K`).  Protocols,
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
  category: objects are pairs ⟨X, A⟩ of an interface and a carrier, homs are
  a coend `∃ k. 𝒞[A, T₀ k B] × ℐ[X ⊗ k, Y]` quotiented by `Slide`, with the
  forgetful/free adjunction `F ⊣ U`. `Regrade` is the change-of-grading
  functor between such categories.
- `LocallyGraded` — locally ℐ-graded categories (categories enriched in
  presheaves on ℐ under Day convolution, in elementary presentation; Wood
  1976/78), the *grade-on-morphism* point of view. `LocallyGraded.Kleisli` is
  the naive graded Kleisli presentation of a triple; `LocallyGraded.FreeActegory`
  the free ℐ-actegory `∮` on a locally graded category; and
  `LocallyGraded.FreeActegory.Kleisli` the **bridge theorem**: the free
  actegory on the naive presentation *is* `GradedKleisli`; objects, homs,
  identities and composition agree on the nose.  This connects the two points
  of view and is the formal backbone of the two UC formulations below.
- `KernelCongruence` — the kernel congruence of a functor (`f ∼ g` iff
  `F₁ f ≈ F₁ g`), the notion of observational equality used everywhere.
- `Diagram.Coend.Ext.Setoids` — concrete Setoid-valued coends with a
  definitional mapping-out principle (the substrate for the free actegory).
- `Functor.Monoidal.CurriedTensor` (+ `.Properties`) — the tensor `X ⊗ −` as
  a graded monad; this is the graded monad of the standard instantiations.
- `CoherenceIsos` — `Coh(ℐ)`, the free monoidal category on `Ob ℐ` with no
  morphism generators, so every hom is a structural coherence iso; the
  interpretation functor into ℐ is faithful.
- `Coherence.Monoidal` (literate entry point) — reflection-based decision
  procedures for morphism equality in (symmetric) monoidal categories
  (`Structural`, `MorRewrite`/`MorSolve`, `SymRewrite`/`SymSolve`), used as
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
  `GradeStable`, the ℳ-module property of ℰ, is sufficient for the converse
  of `≈ᵁ ⇒ ≈ℰ` but not equivalent to it, and is needed only by `bridge`,
  which ingests a bare `≈ℰ` security artifact into the compositional world:
  a conservation law paid once at artifact ingestion, never in the metatheory.
- `Abstract2.Equivalence` — the machine-checked hierarchy connecting the two:
  `≤UC` over `≈ᵁ` implies OAP-`≤UC` at unit input grade implies the bare
  one-sided relation, unconditionally; both converses hold under
  `GradeStable`, which is sufficient but not known to be necessary.

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
- `VanishingTV` — the vanishing-TV relation `_∼ᵛ_` on observation sequences; the
  environment presheaf `ℰᵗᵛ` on `𝒞^ω` whose tests are budgeted *joint
  ancilla tests*; the proof that this ℰ is grade-stable, given
  `MachineAxioms.HomTransportTrivial`, that transport along an object loop is
  invisible on closures, which `UIP Obj` implies (so `≈ᵁ = ≈ℰ` here and the
  `Abstract2` bridge is free); and the ε-bounded relation `_≈ℰ[_]_`
  with `absorb`, the ingestion gate turning concrete vanishing bounds into
  kernel equalities.
- `StandardTV` — everything plugged together: the `Standard2` setup at
  𝒞 = ℐ = `𝒞^ω`, with `GradeStable` discharged from that hypothesis and
  `≈ᵁ ⇔ ≈ℰ` as the headline corollary.

## 4. Concrete machine layer

The executable model (predating the layers above; connecting it to
`MachineAxioms` is planned work):

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
