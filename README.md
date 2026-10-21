# Categorical Cryptography

A framework for universally composable (UC) cryptography built on category
theory, implemented in Agda (`--safe --without-K` throughout). Protocols,
functionalities, adversaries, and environments are all categorical data; UC
emulation and its metatheory (reflexivity, transitivity, completeness of the
dummy adversary, universal composition) are proved once, abstractly, and then
instantiated at concrete models.

Documentation can be found [here](https://input-output-hk.github.io/categorical-crypto/).

The development is organized in five layers, from generic category theory down
to executable machines. Each layer only imports the ones above it.

## 1. Categorical substrate (`src/Categories/`)

General-purpose category theory, independent of cryptography:

- `Monad.Graded` — graded monads as graded Kleisli triples over a monoidal
  grading category ℐ (`T₀`, `sub`, `return`, `ext`, and derived `T₁`, `μ`);
  `Monad.Graded.Pullback` — change of grading along a lax monoidal functor;
  `Monad.Graded.FromMonad` — a graded monad read as a triple whose `T₁`/`μ`
  are the monad's own action and multiplication.
- `GradedKleisli` (+ `.Regrade`) — the *grade-on-object* graded Kleisli
  category: objects are pairs ⟨A, X⟩ of a carrier and an interface, homs are
  a coend `∃ k. 𝒞[A, T₀ k B] × ℐ[X ⊗ k, Y]` quotiented by `Slide`, with the
  forgetful/free adjunction `F ⊣ U`. `Regrade` is the change-of-grading
  functor between such categories.
- `LocallyGraded` — locally ℐ-graded categories (categories enriched in
  presheaves on ℐ under Day convolution, in elementary presentation; Wood
  1976/78), the *grade-on-morphism* point of view. `LocallyGraded.Kleisli` is
  the naive graded Kleisli presentation of a triple; `LocallyGraded.FreeActegory`
  the free actegory `∮` on a locally graded category; and
  `LocallyGraded.FreeActegory.Kleisli` the **bridge theorem**: `∮` of the
  naive presentation *is* `GradedKleisli` — objects, homs, identities and
  composition agree on the nose. This connects the two points of view and is
  the formal backbone of the two UC formulations below.
- `KernelCongruence` — the kernel congruence of a functor (`f ∼ g` iff
  `F₁ f ≈ F₁ g`), the notion of observational equality used everywhere.
- `Diagram.Coend.Ext.Setoids` — concrete Setoid-valued coends with a definitional
  mapping-out principle (the substrate for `∮`).
- `Functor.Monoidal.CurriedTensor` (+ `.Properties`) — the tensor `X ⊗ −` as
  a graded monad; this is the graded monad of the standard instantiations.
- `CoherenceIsos` — the wide subcategory `Coh(ℐ)` of coherence isomorphisms.
- `Coherence.Monoidal` (literate entry point) — reflection-based decision
  procedures for morphism equality in (symmetric) monoidal categories
  (`Structural` / `Mor` / `Symmetric`), used as proof engineering throughout;
  `FreeMonoidal` and `FreeStrictMonoidal` are their term languages.

## 2. Abstract UC layer (`src/CategoricalCrypto/`, parametric)

Everything here is parametric over a single record, `UCSetup`: a base category
𝒞 (machines), a monoidal category ℐ (adversary interfaces), a graded monad
ℳ over them (how an interface is attached to a machine), and a
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
  `GradeStable` (ℰ is a lax ℳ-module; sufficient, not necessary, for the bare
  kernel to coincide with the U-kernel) is needed only by `bridge`, which ingests a bare `≈ℰ` security artifact
  into the compositional world: a conservation law paid once at artifact
  ingestion, never in the metatheory.
- `Abstract2.Equivalence` — the machine-checked hierarchy connecting the two:
  `≤UC` over `≈ᵁ` implies OAP-`≤UC` at unit input grade implies the bare
  one-sided relation, unconditionally; both converses cost exactly
  `GradeStable`.

`Standard` / `Standard2` instantiate the respective layers at 𝒞 = ℐ = a
monoidal category of machines with ℳ = the curried tensor (attaching an
interface = tensoring a channel on). `RandomOracle` / `RandomOracle2` derive
`MD ≤UC RO` from the dummy-adversary theorem, given a record `ROData` of the
open artifacts; the Merkle–Damgård statement is one of its fields, a stand-in
not instantiated from `Examples.MerkleDamgard`.

## 3. Probabilistic model over axiomatized machines

The concrete environment model — machines indexed by a security parameter,
distinguished up to vanishing total-variation distance under polynomial query
budgets — is built parametrically over an *abstract* machine layer, so it
is independent of any particular machine implementation:

- `Data.Nat.Poly` — polynomial bounds on ℕ-functions and their closure
  properties.
- `UC.Evaluation` — observables, their test presheaf `ℰᴼ`, and evaluations; each
  consumer instantiates `Standard2.StdUC` at `ℰᴼ`, whose `_≈ᵁ_` is the
  ancilla-quantified indistinguishability.
- `UC.Family` — the security-parameter family category, and the negligible
  tier over it.
- `Approx.*` and `UC.Quantitative.*` — quantitative UC: approximate-space-valued
  test presheaves, the query-sensitive contextual comparison with an explicit
  error schedule, and its family form.
- `UC.Machine` plugs the whole stack into the machine model of §4.

## 4. Probabilistic machine model and examples

- `ProbabilisticLogic.Dp` — the rational probabilistic delay monad `Dₚ`.
- `Machines.*` — Mealy machines in the Kleisli category of `Dₚ`, composed by
  Elgot iteration, with interface polarity from the G-construction
  (`Machines.G`).
- `Strategy`, `Protocol` — protocols in plain Agda and their machine images.
  For closed protocols, read `Protocol.Observe` for activation-boundary kernels,
  then `Protocol.Reachability` for finite positive-probability reachability and
  the invariant theorem from `GamePlaying.Partial.Preserved⊥`.
  `Protocol.ReachabilityTests` exercises random branches, repeated activations,
  zero-weight exclusion and abort; `Protocol.Safety` supplies quantitative
  bad-event bounds.
- `GamePlaying` — game-hopping: the supermartingale bound and the fundamental
  lemma in coupled form.
- `Examples/` — the chimeric ledger (`docs/end-to-end.md`), a random-oracle
  commitment, Blum coin-tossing over it, hash-then-forward and Merkle–Damgård.

`docs/README.md` indexes the documentation; `docs/mathematical-guide.md` is the
entry point to the model's mathematics.

## 5. Channel/machine layer

A second, executable model, independent of the layers above:

- `Channel/` — channels (typed communication ports), their category, and a
  wiring DSL (`Selection`).
- `Machine/` — stateful machines communicating over channels, with UC
  security notions stated directly on them; `Constraints` adds extra
  side conditions.
- `Examples/{Basic,Commitment,Signatures}` — commitment, signature, and basic
  protocol examples.
- `CategoricalCrypto` — the library root: its `public` re-exports are this
  layer, and its other imports put the rest of the library in the build
  closure.
