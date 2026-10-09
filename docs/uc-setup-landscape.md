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
B ⊗ A` definitionally, and a functor into it may be chosen strict (the ITM plan does
this via `fromMC Iso.machines`).  Note `A ⊎ B ≢ B ⊎ A`, and `Channel.Core`'s `⊗₀` is
opaque, so nothing is symmetric "on the nose".

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

**Ports reading** (the intended one; plan: [uc-setup-itm.md](uc-setup-itm.md)).  The
ITM setup is `StdUC 𝕋ᴹ ℰᵀ` where `𝕋ᴹ` is the **free monoidal category**
(`src/Categories/FreeMonoidal.agda`) generated by finite-table TMs between port
interfaces (trees of bitstring ports `⁺`/`⁻`), hom-equality the generated congruence
`_≈Term_` (intrinsic, *not* pulled back — a pulled-back `≈ᴹ` would block the arrow into
`machine-iso`), tests `ℰᵀ = ℰᵒ ∘F Fᴾ.op`.  `itm⇒prot : 𝕋ᴹ → 𝔾ᵒ` is a `StdUCMorphism` with
`Fᴾ` strict (`freeStrongMonoidal`; leaf = run the TM by the Elgot `iterₚ`, non-halting
= `botₚ`), `κ = id`, `ν = pullbackᵛ` (Epi and Mono); `F (g ∘ f) = F g ∘ F f` is
definitional and `F-resp-≈` is the existing `⟦⟧-resp-≈`.  Corrections to the first
draft: `WideSubcategory` fails not on identities but because `W-sub` must hold at every
ambient adversary and `subSetup` keeps `ℐ`; runtime bounds (PPT) are not a category
(`hofheinz2013` §1.5), so "feasible" is a side condition, not a sub-setup; the arrow
`ITM → machine-iso` exists only from a second observation `ℰᴵˢᵒ = ℰ-tests ∘F Fᴿ.op`
(module with K), and the triangle with `protocol-rewrite` commutes only on
deterministic leaves, up to a mirror iso of wires.

## 4. Random systems, SSP, IPDL

- **Random systems** (plan: [uc-setup-random-systems.md](uc-setup-random-systems.md)).
  Carrier = `𝔾ᵒ`'s machines with the **adaptive** behavioural setoid `_≈ᴿ_` (every
  `Strat` distinguisher gets `∼ᵃ`-equal `Dₚ Bool`, `maurer2002` Defs 9–10); the
  non-adaptive version is derived; `_≈ₚ_` itself is too fine (rejection sampling vs
  `coinₚ`).  Congruence for G-composition and tensor is Maurer's Lemmas 4–5, proved by
  absorbing the context into a budget-truncated distinguisher.  The setup is
  `StdUC 𝔾ᴿ ℰᴿ` with `𝔾ᴿ = quotient 𝔾ᵒ congᴿ` via a new generic
  `Categories.Category.Monoidal.Construction.Quotient` and `ℰᴿ = descend ℰᵒ`.
  `rewrite⇒RS : 𝔾ᵒ → 𝔾ᴿ` is a `StdUCMorphism` (`F` identity on the nose, `κ = id`, `ν`
  identity; `F-resp-≈` = simulation ⇒ `≈ᴿ`, an induction on the strategy with
  `>>=ₚ-cong`); the payoff is `≈ᴿ ⇒ ≈ᵁ` by `mono⇒reflects`.  **Corrections:** "full
  abstraction = `Mono`" was wrong (`Mono` compares tests and is trivial for `ν = id`);
  and `ℰᵒ` is **not `GradeStable`** — two reveal machines are `≈ℰ`-equal but separated
  by `T₁ (Bool ⇿ ⊥)` (§5.3 there) — so `bridge` is unusable at `ℰᵒ` and `≈ᴿ⇒≈ᵁ` is the
  route to `≈ᵁ`.  `𝔾ᴿ` has no `QEvaluation` (slack 0 is unavailable), hence no family
  or negligible tier on RS.
- **SSP / the call-return discipline** (plan: [uc-setup-ssp.md](uc-setup-ssp.md)).  A
  standalone setup `StdUC Protᴹ ℰᵖ` in namespace `CategoricalCrypto.SSP` with
  **channel-indexed** interfaces (`Iface = Ch/Q/R`; the flat `Pos ⇿ Neg` is the
  one-channel case), `_⊗ᵖ_` dispatching on the queried channel, hom-equality `≈ᶜ`
  (simulations of call trees), tests = closed protocols into `Ωᴵ` read to `Dist⊥ Bool`;
  all `--without-K`, no `Dₚ`.  `StdUC` over the *flat* `Protocol` is impossible
  (`wireᵖ ⊗ᵖ wireᵖ ≠ wireᵖ`).  **There is no `UCSetupMorphism` `SSP → protocol-model`
  with `F = Protocol.Machine.morphism`**: `morphism wireᵖ ≉ᴹ 𝒢.id`
  (`Protocol/Machine.agda:14-19`) and `𝔾ᵒ`'s `⊗` interleaves (`Machines/Tensor.agda:98-99`)
  while `_⊗ᵖ_` cannot; both are observable through an ancilla and both counterexamples
  are non-well-bracketed contexts.  The connection is the chain
  `SSP ─StdUCMorphism─▶ PM[wb] ◀─q─ 𝒲[ℰᵂ]` and `𝒲[ι*ℰᵒ] ─ι─▶ PM`, where `𝒲` is the
  (non-wide) monoidal subcategory of well-bracketed machines, `ℰᵂ` the well-bracketed
  tests (not a sub-presheaf of `ι*ℰᵒ` in either direction), and `PM[wb]` the quotient of
  `𝒲` by `ℰᵂ`'s U-kernel.  Headline obligations: `morphism wireᵖ ≈ σ⇒` and
  `morphism (P ⊗ᵖ Q) ≈ morphism P ⊗ morphism Q` under well-bracketed environments.
  Escape hatch for asynchronous events: pollable state (`lochbihler2019cc` §IV-A,
  `maurer2011cc` §5.1).
- **IPDL** (plan: [uc-setup-ipdl.md](uc-setup-ipdl.md)).  `StdUC 𝕀ᴹ ℰⁿ` with polarised
  typed channel contexts, reaction networks in flat form, composition `new B in (f ∥ g)`,
  hom-setoid = IPDL's exact theory as an inductive relation, tests = IPDL protocols into
  `Ωⁿ` read by lazy memoised evaluation into `Dₚ Bool`.  **IPDL is an island**: the
  compile into `𝔾ᵒ`/RS fails `F.identity` and `F-resp-≈` because `exch` and `unused`
  hold only against IPDL-shaped environments (a closure with advantage 1, §4.1 there),
  and the "probabilistic kernel per partial input assignment" semantics is not
  compositional.  What survives is a semifunctor: attacks transfer from IPDL to `𝔾ᵒ`,
  security does not.

### Coarser machine equalities go to random systems, not to `𝔾ᵒ`

Trace equivalence (the `machine-category` branch) is coarser than `≈ᴹ`: trace-equivalent
deterministic machines are bisimilar, but exhibiting a zigzag of *functional*
simulations needs the minimal automaton as a `Set`, i.e. a quotient, which `--without-K`
Agda without HITs does not have.  So `F-resp-≈` fails into `𝔾ᵒ`.  Its `≈ᵗ` is
possibilistic, so only the deterministic fragment maps into RS (`det-≈ᴮ⇒≈ᴿ`).

## 5. Causal boxes, symbolic, nondeterminism, and the other candidates

- **Causal boxes** (plan: [uc-setup-causal-boxes.md](uc-setup-causal-boxes.md)).
  Classical fragment, positions `ℕ`, one message per wire per position; objects `Face =
  Pos ⇅ Neg` with `⊗ = ×` (Portmann Def. 6.1 concurrency), two-phase `Box` records
  parametric in a `DiscreteMonad`, composition per position with no fixpoint or
  coinduction, behavioural equality under adaptive environments, tests via `Evaluation`.
  **Corrections:** `portmann2017` proves no SMC-with-trace theorem (the identity is not
  causal); and **causal boxes are an island** — no `UCSetupMorphism` in either direction
  with `𝔾ᵒ`, RS, `machine-iso`, SSP, IPDL, ITM or `Rel`: internal G-composition rounds cost
  ≥1 causal-box position so `F (g ∘ f) ≈ F g ∘ F f` fails, and the synchronous `⊗` has no
  image under interleaving.  Reachable only laxly (Portmann §9).  RSIM/task-PIOA live
  here because the scheduler is a policy over the closed collection, not a morphism.
- **Symbolic / Dolev–Yao** (plan: [uc-setup-symbolic.md](uc-setup-symbolic.md)).
  `𝔻𝕐` = free monoidal category generated by DY roles (token-passing programs whose
  outputs are recipes over their frame), hom-equality `_≈Term_`, observation evaluated in
  `𝔾ᵒ` at term alphabets with global freshness by located names, kernel = DY trace
  (may-testing) equivalence, tests with an ancilla as in `Machine/UC.agda`,
  `GradeStable` hypothesis-free.  **Corrections:** it is not "possibilistic next to
  `machine-iso`" (deterministic up to names); `Sym → machine-iso` does not exist, only
  the coarse variant `Sym≅ → machine-iso` (via `freeStrongMonoidal` into `Reverse`
  machines) and `Sym≅ → Sym` by `changeKernel`; there is no `symbolic → RS` (names are
  guessed with positive probability, so exact soundness fails).  Computational
  soundness is a `StdUCMorphism` `Sym≅ → UC.Model.Family.ucSetupᴺ` (the negligible
  tier over `𝔾ᵒ`) plus a side-conditioned pointwise theorem `sound⁺` over it
  (hypothesis table: IND-CPA+INT-CTXT or IND-CCA2/EUF-CMA, sorts, tags, …); `ν Mono`
  gives completeness, not soundness.  Needs a new `transfer⁺` in `Abstract2/Morphism`
  since `ℰᵒ` is not `GradeStable`.
- **Nondeterministic choice** (plan: [uc-setup-nondeterministic.md](uc-setup-nondeterministic.md)).
  The SSP setup plus `choose : (Fin (suc n) → Calls A X) → Calls A X`, schedulers
  resolved only at observation of a closed system, outcome space `Sched → Dist⊥ Bool`
  under image equality (Segala-style ∀-scheduler semantics; a probability×nondeterminism
  monad exists only as the convex powerset, `bonchi2022`, rejected there; no
  distributive law, `varacca2006`, `zwart2019nogo`).  `Sched` must be history-dependent
  and see coin tosses, else `choose`-commutativity under a coin fails.  The `choose` laws
  (`choose-set`, `-unit`, `-join`, `coin-comm`, `coin-dead`) are best made constructors
  of the call-tree equality with one soundness proof against `run⁺`, so "order does not
  matter" is a hom-equality reaching `≈ᵁ` by `≈C⇒≈ᵁ` without `GradeStable`.
  **Corrections:** `SSP → ND` with constant-in-σ tests is **not** a presheaf morphism —
  a demonic closure sees an SSP test's toss (task-PIOA's leak); what exists is a trivial
  pullback morphism and a one-way reflection (`ND f ≤UC g ⇒ SSP f ≤UC g` for
  `choose`-free `f, g`).  The Kleisli-valued generalisation (2b) has no instance
  (`GradedKleisli` carries no monoidal structure); the recommended relation to SSP is a
  threaded routing functor with a pointwise transfer theorem.  `P ∥ Q` is not derivable
  from `choose` and `_⊗ᵖ_` (caller-scheduled interleaving is `(P ⊗ᵖ Q) ∘ ∇`).  Open
  decision before the first module: global vs site-local scheduler information.
- **Robust compilation** (plan, on `main`: `docs/uc-robust-compilation.md`).  Not a
  setup: a theorem about the order.  `f ≤UC g ⇔ ∀ H : Predᵁ. Robustᵁ H g → Robustᵁ H f`
  over `≈ᵁ`-respecting predicates on *attacked* programs (UC = RHP; the converse by a
  Yoneda-style instance `Hyp g`).  The naive version over outcome-only `Predℰ` fails
  right-to-left (`Examples/RelSetup.agda:leaky-not-secure` is the counterexample).
  Across two setups the compiler is a `UCSetupMorphism`, preservation = `Transfer.transfer`
  (`ν.Epi` + target `GradeStable`), reflection = `ν.Mono` + full `Φ`; the RC criteria
  hierarchy is a family of presheaves on one `𝒞/ℐ/ℳ`.
- **Effectful Mealy machines** (`bonchidilavore2025`) and **categorical composable
  cryptography** (`broadbent2022`, `broadbent2023`): the generic shape; a comparison
  document showing `StdUC` is their construction, or where it differs, is still open.
- **GNUC / iUC / SUC**: restrictions of the ITM setup (`changeKernel` /
  `WideSubcategory`), not separate setups.  **ILC**, **CryptHOL CC**: cross-checks.
  **Indifferentiability**: a theorem schema over RS.  **Game-based / pRHL**: `Rel`'s
  probabilistic sibling, the target of SSP's `≈_ε` reductions.

## 6. The morphism graph

Verdicts after the plans.  `──▶` = `StdUCMorphism`; `⇢` = restricted or conditional.

```
cartesian / one-shot        reactive / ⊎ world
─────────────────────       ──────────────────────────────────────────────────────────
TM functions (×) ──▶ Rel    Sym≅ ──▶ machine-iso ◀── ITM(det, ℰᴵˢᵒ)
                             │             ⇢ (+ init, det. fragment)
                             │                   ▼
                             │   𝒲[ι*ℰᵒ] ──▶ protocol-rewrite 𝔾ᵒ ◀── ITM 𝕋ᴹ
                             │    ▲                   │
                             │  SSP ──▶ PM[wb] ◀── 𝒲[ℰᵂ]           ▼
                             │   ┆ (≤UC reflection only)    random systems 𝔾ᴿ ◀⇢ machine-category (det.)
                             ▼   ▼
              ucSetupᴺ (negligible tier over 𝔾ᵒ)    ND (nondeterministic)

islands: IPDL;  causal boxes (RSIM / task-PIOA inside)
```

No `StdUCMorphism` crosses between the two worlds (the crossing is lax).  Three edges
hypothesised in the first draft are **gone**: `SSP → 𝔾ᵒ` directly, `IPDL → RS`, and
`RS → causal boxes`.

## 7. Plans

| Setup | Plan |
|---|---|
| interactive Turing machines (ports) | [uc-setup-itm.md](uc-setup-itm.md) |
| random systems | [uc-setup-random-systems.md](uc-setup-random-systems.md) |
| state-separating proofs / call-return discipline | [uc-setup-ssp.md](uc-setup-ssp.md) |
| IPDL | [uc-setup-ipdl.md](uc-setup-ipdl.md) |
| causal boxes | [uc-setup-causal-boxes.md](uc-setup-causal-boxes.md) |
| symbolic / Dolev–Yao | [uc-setup-symbolic.md](uc-setup-symbolic.md) |
| nondeterministic choice | [uc-setup-nondeterministic.md](uc-setup-nondeterministic.md) |
| robust compilation (theorem, not a setup) | `docs/uc-robust-compilation.md` on `main` |

Shared infrastructure the plans agree on: `Categories.Category.Monoidal.Construction.Quotient`
(RS, SSP), `freeStrongMonoidal` in `Categories/FreeMonoidal.agda` (ITM, symbolic),
`transfer⁺` in `Abstract2/Morphism.agda` (symbolic, RS), and the `GradeStable`
counterexample for `ℰᵒ` (RS §5.3), which every plan relying on `bridge` must route around.

## 8. Recommended order of construction

1. **`protocol-rewrite → random systems`** (`rewrite⇒RS`) — pure quotient, identity `F`;
   brings the generic `Quotient` module and `≈ᴿ⇒≈ᵁ`, which replaces `bridge` at `ℰᵒ`.
2. **ITM `𝕋ᴹ → 𝔾ᵒ`** — definitional functoriality, reuses `FreeMonoidal`; gives the
   "feasible machines" setup and `freeStrongMonoidal` for the symbolic plan.
3. **SSP standalone setup** (channel-indexed `Iface`, `_⊗ᵖ_`) — the interaction
   discipline; then its chain into `PM[wb]` (the two headline lemmas).
4. **Nondeterministic choice** on top of SSP.
5. **Symbolic** (`Sym≅ → ucSetupᴺ`, `sound⁺`) and the **robust compilation** lemma.
6. `machine-iso → protocol-rewrite` only after the three model changes of §2; IPDL and
   causal boxes as standalone setups when wanted — no morphisms are lost by deferring them.
