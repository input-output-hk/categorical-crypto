# The landscape of UC setups and the morphisms between them

Findings of a 2026-10-09 study of the `UCSetup` instances that exist in the tree
(after merging `protocol-rewrite` and `machine-iso`) and of those worth adding:
interactive Turing machines, random systems, state-separating proofs (SSP) and IPDL.
The question throughout is which `UCSetupMorphism`s exist, which are blocked, and by
what.  Nothing in this document was typechecked beyond the merged tree itself; every
claim about a *not-yet-written* setup is a design claim.

## 1. What a morphism costs

`UCSetup/Morphism.agda:UCSetupMorphism 𝕊 𝕊′` is a `GradedKleisliMorphism S.triple
S′.triple` — a functor `F : 𝒞 → 𝒞′`, a monoidal functor `Φ : ℐ → ℐ′` and components
`κ : F (T X A) ⇒ T′ (Φ X) (F A)` with the return/ext/sub laws
(`Categories/Monad/Graded/Morphism.agda:47-64`) — plus `ν : PresheafMorphism F S.ℰ
S′.ℰ`, i.e. a natural transformation `S.ℰ ⇒ S′.ℰ ∘ F.op`: source tests on `A` go to
target tests on `F A`, compatibly with precomposition.  Source and target share the
test levels `cs ℓs` literally.

Every setup discussed here is `Standard2.StdUC 𝕄 ℰ` (𝒞 = ℐ = 𝕄, ℳ = the curried
tensor), so the morphism shape is `Standard2/Morphism.agda:StdUCMorphism`: a
**strong monoidal** `F : 𝕄 → 𝕄′` and `ν`.  The general record only relaxes "strong" to
*oplax* — `κ` runs `F (X ⊗ A) ⇒ Φ X ⊗ F A` — never to lax.  This matters in §3.

The existing constructors are `changeKernel` (same 𝒞/ℐ/ℳ, new tests), `idᵁ`,
`composeᵁ`, the epi/mono `Factorization`, `Abstract2/WideSubcategory` (restrict to a
wide subcategory of admissible morphisms, pull tests back) and `StdUCMorphism`.  No
concrete cross-model instance exists in the tree.

## 2. The two concrete setups in the tree

| | `Machine/UC.agda` (`machine-iso`) | `UC/Model/Setup.agda` (`protocol-rewrite`) |
|---|---|---|
| objects | `Channel = in ⇿ out`, ⊗ = ⊎ | `Iface = Pos ⇿ Neg`, ⊗ = ⊎ — same shape, `in ↦ Pos`, `out ↦ Neg` |
| morphism | relation `S → In → Maybe Out → S → Type`; **no initial state**; nondeterministic; may be silent | Mealy `S × In → Dₚ (S × Out)` with `point`; probabilistic, delay/divergence; always answers |
| composition | inductive `TraceRel` ping-pong | G-construction `trace` in the Kleisli category of `Dₚ` |
| hom-equality | `_≅ᴹ_` = state **bijection** preserving steps (finer than bisimulation, `Machine/Iso.agda:42-51`) | `_≈ᴹ_` = equivalence closure of pure functional simulations (`Machines/Sim.agda`) |
| tests | `(Y , E : A ⊗ Y → ℰ-Out)` up to `≅ᴹ` (joint ancilla) | `A ⇒ Ωᵒ` up to "every closure `𝟘ᵒ → A` gives `Dₚ Bool`s equal within every ε > 0" |
| grade order | reversed tensor: `T₀ X B = B ⊗ X` | `T₀ X B = X ⊗ B` |
| levels | `UCSetup 1 1 0 1 1 0 1 1` | all `suc 0ℓ` |
| OPTIONS | `--safe` with K (`same⁻¹` needs it) | `--safe --without-K --guardedness` |

The reversed tensor is not an obstacle: `Reverse-MonoidalCategory` makes `A ⊗ʳ B :=
B ⊗ A` definitionally, and ⊎ on objects is symmetric on the nose.

### `protocol-rewrite → machine-iso`: blocked

A functor needs `f ≈ᴹ g ⇒ F f ≅ᴹ F g`.  Simulation-equivalent Procs with different state
spaces (pad a state space by `Bool`) have no state bijection.  The target equality is too
fine; no choice of `F` on morphisms helps.  Only a coarsened `machine-iso` can receive
this — the `machine-category` branch ("construction-based machine categories and the
trace-equivalence bridge") is the candidate, and §4 says where *that* can go.

### `machine-iso → protocol-rewrite`: three model changes away

`≅ᴹ ⇒ ≈ᴹ` holds (a bijection is a pure simulation both ways) and objects coincide.
What is missing is on the morphism side, and each gap has one fix:

1. **Initial state.** `point` needs one, and `_≅ᴹ_` must gain `to init ≡ init′`;
   otherwise one machine with two initial states is `≅ᴹ` but its images are not `≈ᴹ`
   (`θ-point` fails) and `F-resp-≈` breaks.  Cost: one field threaded through
   `∘-resp-≅ᴹ`, `⊗₁-resp-≅ᴹ` and the coherence isos (structural ones have
   `⊤`-product states, so mostly `refl`).  `SetupSubcategory.W` cannot substitute for
   this: it can carry data, but the restricted hom-equality stays `≅ᴹ` on the underlying
   machine.
2. **Determinism, as a wide subcategory.** Nondeterministic relations have no `Dₚ`
   image.  `W f := "stepRel has at most one successor"` is a valid
   `SetupSubcategory` (`Abstract2/WideSubcategory.agda:50-57`): closed under `∘` (a
   deterministic ping-pong is determined even when it livelocks), `⊗` (interleaving is
   input-selected), `id`, `return`, `sub`, `ext`.  It is determinism, not productivity,
   that closes: a livelocked composite has an empty relation and maps to `botₚ`, which is
   what the `𝔾ᵒ` traced composite does too.
3. **Silence.** `Maybe out` has no counterpart; a G-construction activation always
   answers.  The only `Dₚ` image of a silent step is `botₚ`, which is absorbing for the
   whole run, while a silent `machine-iso` machine keeps serving later inputs.  The
   functor laws survive (a silent last link makes the `TraceRel` composite silent), but
   `F` identifies "no answer now" with "dead forever".  If that matters, remove `Maybe`
   from the deterministic fragment rather than special-case it.

With 1–3: `F` = run in `Dₚ` from the initial state, `ν (Y , E) = F E ∘ (id ⊗ ⊥_Y) ∘
ρ⁻¹` (close the ancilla with the divergent process; `cong` by `F-resp-≈` then
`≈ᵒ⇒≋`; naturality by functoriality and interchange).

Without the changes, the only fragment that maps is the **stateless deterministic**
one (`State` contractible, so the initial state is canonical).

## 3. Classical setups: Turing machines, and why `Rel` is where the cartesian one goes

**Cartesian reading** — objects `Bitstring^n`, morphisms TM-computable functions — is
monoidal under `×`.  It cannot map strongly or oplaxly into any ⊎-tensored reactive
setup: `κ` would be a machine receiving one pair and emitting two messages, and a
`stepRel` emits at most one `Maybe out` per input with no spontaneous steps.  The same
obstruction separates `Examples/RelSetup.agda` (`Rels` under `×`, tests `Hom[-, ⊤]`)
from the reactive world.  The cartesian TM setup *does* map into `Rel`: function ↦
graph (strong, `× → ×`), computable predicate ↦ subset.  That is `Rel`'s relevance: it is
the possibilistic one-shot model, the target of the cartesian classical setup, and a
cheap sanity check of the abstract theory (`ℰ-faithful`, hence `≈ᵁ` = relation
equality).  It is not a model of reactive UC and is not related to `machine-iso` by a
morphism.

**Ports reading** (the intended one) — `n` positive / `m` negative bitstring ports,
`F (n ⇿ m) = (Fin n × Bits) ⇿ (Fin m × Bits)`, `⊗` = `+` on port counts — is
⊎-tensored, so `F (n + n′) ≅ F n ⊗ F n′` by stateless relabelling wires that compose to
`id` up to the target equality.  Morphisms are then **interactive** TMs: stateful,
reactive, with the blank tape as the canonical initial configuration.  This setup has
two natural targets:

- **`→ protocol-rewrite`**, the better fit.  One activation = run the TM until it
  halts, as guarded corecursion in `Dₚ` (`laterₚ`, non-halting = `botₚ`,
  `ProbabilisticLogic/Dp.agda:66-74`); the random tape = `coinₚ ½` per bit; exactly one
  output per activation = the G-construction discipline.  Hom-equality on the ITM side
  is a design choice: pull back `≈ᴹ` along `F` (then `F-resp-≈` is free and `F` is
  `Mono`: the ITM setup is a non-wide, non-full subcategory of `𝔾ᵒ`, packaged through
  `StdUCMorphism` with the inclusion), or an intrinsic syntactic equality.  The real work
  is `F (g ∘ f) ≈ᴹ F g ∘ F f` — TM-side ping-pong versus the Kleisli `trace`.  The module
  carries `--guardedness` (infective).  `Abstract2/WideSubcategory.agda:3-6` already
  names "feasible machines ⇒ computational security" as its purpose, so the alternative
  packaging as a *restriction* of the ambient setup is equally in scope; it is not wide
  (non-codable objects have no computable identities), hence the inclusion route.
- **`→ machine-iso`**: forget the TM witness, `State = Config`, silence unused; tests =
  computable environments, `ν` = their inclusion into all environments (`Mono`).  With
  §2's three changes the triangle `ITM → machine-iso(det) → protocol-rewrite` commutes
  up to `≈ᴹ` by construction.

## 4. Random systems, SSP, IPDL

All three are `StdUC` instances differing in what a step is and in the hom-equality.

- **Random systems** (Maurer).  Objects `(X, Y)` alphabet pairs = `Iface`; morphism =
  `p_{Y_i | X^i Y^{i-1}}`, a probabilistic Mealy machine **modulo behaviour**;
  converters/resources = the G-construction.  This is `𝔾ᵒ` with `≈ᴹ` replaced by
  behavioural equivalence, tests unchanged.  `protocol-rewrite → RS` is identity on
  objects and morphisms, `F-resp-≈` = "simulation ⇒ behavioural equality", `ν = id`.
  Whether `ℰᵒ`'s kernel already *is* behavioural equivalence is a full-abstraction
  question, i.e. whether this morphism is `Mono`.
- **SSP** (Brzuska et al.).  Packages = stateful oracle sets, composition by matching
  import/export, parallel composition, equality = perfect/ε game indistinguishability.
  The structural difference from `𝔾ᵒ` is that an oracle call is a synchronous
  call/return.  The tree already has that layer: `Protocol A B` (`Protocol.agda:59-63`,
  `step : St → Neg B → Calls A (St × Pos B)` with `call`/`coin`/`dead`) is an SSP
  package with export `B` and import `A`, and `Protocol/Machine.agda:morphism :
  Protocol A B → 𝒢ₚ [⟦A⟧,⟦B⟧]` compiles it to a reactive machine.  An SSP setup is
  `StdUC` over protocols with distinguisher tests into `Ωᴵ`, and `morphism` is `F` for
  `SSP → protocol-rewrite`; the paper's algebraic laws become the obligations that
  `morphism` preserves composition up to `≈ᴹ` (`Protocol/Machine/Compose.agda` is where
  to look first).
- **IPDL** (Gancher et al.).  Objects = typed channel sets, tensor = disjoint union
  (⊎-shaped), morphisms `I → O` = reaction networks where each channel fires at most
  once, composition = parallel + hide, equality `≈_ε`.  Semantically a probabilistic
  kernel from input-channel values to output-channel values, so IPDL embeds into random
  systems (or `𝔾ᵒ`) as the single-use fragment: channel read = query, memoise the first
  value.  Strong monoidal because both tensors are ⊎.  The content of the morphism is the
  soundness of IPDL's equational theory under that compilation; `Abstract2/Morphism`'s
  preservation results then transport IPDL proofs into the common model.

### Coarser machine equalities go to random systems, not to `𝔾ᵒ`

Trace equivalence (the `machine-category` branch) is coarser than `≈ᴹ`: trace-equivalent
deterministic machines are bisimilar, but exhibiting a zigzag of *functional*
simulations needs the minimal automaton as a `Set`, i.e. a quotient, which `--without-K`
Agda without HITs does not have.  So `F-resp-≈` fails into `𝔾ᵒ`, and the right target for
any trace-quotiented machine setup is the behavioural random-systems setup.

## 5. The morphism graph

```
cartesian / one-shot world          reactive / ⊎ world
──────────────────────────          ──────────────────────────────────────────────
TM functions (×) ──▶ Rel            ITM (ports) ──▶ machine-iso + init, det. fragment
                                      │                      │
                                      ▼                      ▼
                                    protocol-rewrite 𝔾ᵒ ◀── SSP = Protocol A B
                                      │
                                      ▼
                       IPDL ──▶ random systems ◀── machine-category (trace-equiv)
```

No `StdUCMorphism` crosses between the two worlds: the crossing (one message = one
value) is a lax functor, which `UCSetupMorphism` cannot express.

## 6. Recommended order of construction

1. **`ITM → protocol-rewrite`** — self-contained, no change to `machine-iso`, gives the
   "feasible machines" setup directly.
2. **`SSP → protocol-rewrite`** — `F = Protocol.Machine.morphism` exists; objects
   coincide; the branch carries composition lemmas for it already.
3. **`protocol-rewrite → random systems`** — a pure quotient; also settles whether `ℰᵒ`
   is fully abstract.
4. **`machine-iso → protocol-rewrite`** — after the three model changes of §2, or via the
   `machine-category` coarsening into random systems instead.
