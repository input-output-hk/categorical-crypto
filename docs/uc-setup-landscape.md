# The landscape of UC setups and the morphisms between them

Findings of a 2026-10-09 study of the `UCSetup` instances that exist in the tree
(after merging `protocol-rewrite` and `machine-iso`) and of those worth adding:
interactive Turing machines, random systems, state-separating proofs (SSP), IPDL,
causal boxes, the symbolic model, nondeterministic choice, and robust compilation.
The question throughout is which `UCSetupMorphism`s exist, which are blocked, and by
what.  §1–§2 are checked against the tree; §3–§5 summarise the per-setup plans of §7,
which are design documents — nothing in them is typechecked.

**Provenance.** Branch `uc-setup-landscape` = `origin/protocol-rewrite` with
`origin/machine-iso` merged.  Two semantic conflicts beyond git's: `protocol-rewrite`'s
solver refactor removed the symmetric variant `SymSolve`/`solveMorσ!`, so
`Machine/Monoidal/Naturality.agda` now proves its two naturality laws by hand from
`σ-natural`/`assoc-commute-from` and `Machine/UC/Kleisli.agda` passes its single
crossing to the monoidal solver as an opaque generator; and `UCSetup`'s `T₁` became the
graded monad's own action (`FromMonad`), so `Machine/UC.agda:T₁-⊗ʳ` is `≅ᴹ-refl`.  The
root closure `src/CategoricalCrypto.agda` checks (353 modules, warning gate empty).
`docs/kb` is the knowledge base from branch `pagda`, extended by the plans' sources.

## 0. Status, major findings, decisions pending

**Built and green per module** (three branches merged into `uc-setup-landscape`, and the
symbolic steps of `uc-setup-symbolic.md` §6; escape-hatch baseline unchanged):

| setup | what exists | key exports |
|---|---|---|
| random systems `𝔾ᴿ` | `Categories/…/Construction/Quotient` (generic), `UC/Machine/Behaviour*` (`_≈ᴿ_`, congruence for G-composition and tensor), `UC/RandomSystems/{Seal,Setup,Morphism,FullAbstraction,Advantage,Composition,Construction,Quantitative,Availability}` | `rewrite⇒RS : UCSetupMorphism`, `≈ᴿ⇒≈ᵁ`, **`≈ᵁ⇒≈ᴿ`**, **`¬gradeStableᵒ`**, `≈ᴮ⇒≈ᴿ-fin`, `Δ`, `absorbs-Δ`, `hybrid`, security-only `≤UC⇔Constructs₀` / `≤UCᴿ[]⇔Constructs`, full `SecurelyConstructs` with designated modes |
| ITM `𝕋ᴹ` | `ITM/{Core,Run,Functor,Setup,Relational}`, `FreeMonoidal.freeStrongMonoidal`, `Seal.unitᵒ` | `itm⇒prot` (`ν` Epi+Mono), `≈ℰ⇔`, `itm⇒iso` |
| SSP (call/return) | `SSP/{Iface,Protocol,Protocol/Category,Protocol/Monoidal,Observation,Setup,Reduction,Compile,Semantics,Cut,Dense,Dense/Tests}`, `Standard2/UKernel`, `Protocol/{Sim,Machine/Resp,Machine/Oracle}`, `UC/Bracket{,/Category}` | `StdSetup`, `Protᴹ`/`Protˢ`, `toProtocol`, `morphism-resp`, `W`, `morphism-W`, `𝒲`, `ι`, **`games-dense`**, **`SSP→PM[wb]`**, **`preserves-≤UC`** |
| nondeterministic choice (over any symmetric 𝕄; at SSP and PM) | `Abstract2/Regrade{,/Pin,/Unit}`, `Categories/…/Construction/Transport` (`Closed`, `weaken`), `ND/{Grade,A,Relabel}`, `ND/SSP/{Choice,Choice/Compose,Choice/Pin,Choice/Dist,Setup,Laws,Reflect}`, `UC/Model/Symmetric`, `ND/PM/{Factor,Read,Relabel,Setup,Choice,Choice/Compose,Choice/Pin}` | `regraded`, `inclusion`, `𝔾ˢ`, `NDB`, `NDA`, **`A⇒B`**, `≤UC-B⇔≤UC`, `≤UC⇒relabel`, PM online request/resume and compilation laws; SSP `swap-ᵖ`, **`order-indep`**, **`¬reflect`** |
| symbolic `𝔻𝕐` (steps 3–9; fixed-message step 10) | `Symbolic/{Term,Term/PairEnc,Deduction,Role,Fine,Semantics,Setup,Static,Static/PairEnc,Test,StaticTests,Example/SecureChannel}`, `FreeMonoidal/Decorated`, `Machines/Sim/Relational`, `UC/{Machine,Model}/Relational` | `Sym≅`, `Sym`, `fine→sym` (`coarse` Epi), **`grade-stable`** (hypothesis-free), `≈ᵁ⇔≈ℰ`, **`emit-≈E`**, **generic `≈ₛ⇒≈ℰ`**, **E₀ `≈ℰ⇔≈ₛ`**; fixed-public-message **`smt≤ideal`** with a non-identity simulator, `real≈simulated`, `real≤simulated`; the unrestricted static converse is false (unsorted cross-sort name sharing), and environment-selected interactive messages are not covered |

**Major findings** (proven unless marked; finding 3's non-existence claim is argued in
`Protocol/Machine.agda:14-19`'s header, not a theorem):

1. **`≈ᵁ` at protocol-model IS behavioural equivalence of random systems**
   (`≈ᵁ⇒≈ᴿ` + `≈ᴿ⇒≈ᵁ`).  This fixes the meaning of the library's security notion.
2. **`ℰᵒ` is not `GradeStable`** (`¬gradeStableᵒ`: a stateless reveal machine).
   `Abstract2.bridge` is unusable at protocol-model; `≈ᴿ⇒≈ᵁ` replaces it.
3. **No direct `SSP → 𝔾ᵒ` morphism**: `morphism wireᵖ ≉ᴹ 𝒢.id` and the G-tensor
   interleaves.  The call/return discipline reaches protocol-model only through the
   well-bracketed quotient `PM[wb]` (§4).  Built: `W`, `𝒲ᴹ` with its tensor
   (`UC/Bracket/{Tensor,Monoidal}`, generic `Construction/Transport`), `ιᴹ`,
   `ι⇒prot : UCSetupMorphism` into protocol-model, `PM[wb]`'s setup and the quotient
   morphism `q` (`UC/Bracket/Setup`), the monitor lemmas (`UC/Bracket/{Monitor,Relabel}`),
   and `Fᵂ : StrongMonoidalFunctor Protᴹ PM[wb]ᴹ` with `wire≈σ` and `⊗≈⊗` (`SSP/Semantics`).
   **`SSP→PM[wb] : UCSetupMorphism` is built unconditionally** (`SSP/Dense`): SSP games
   are dense among well-bracketed closures (`games-dense`), so SSP-indistinguishable
   tests stay so against every well-bracketed closure.  **The `≤UC` transfer is
   unconditional too** (`SSP/Dense/Tests.preserves-≤UC`): compiled distinguishers are
   dense among well-bracketed tests (`tests-dense`), which gives `Preserves-≈ℰ`; no
   `ν.Epi` is used.  Both densities approximate from below, by depth-cut call trees.
   Status: `docs/uc-setup-ssp.md` §6, C7.
   The separate inclusion `𝒲[ι*ℰᵒ] → PM` also preserves `≤UC`
   (`UC/Bracket/InclusionTransfer.ι-preserves-≤UC`): every PM object `X` is
   isomorphic to the image of `oneᴵ (objᵒ X)` by wires adding/removing the singleton
   channel tag. Essential surjectivity and `νι-epi` give `Preserves-≈ᵁ`, then
   `Abstract2/Morphism.transfer⁺` applies without target grade stability.
   Its source retains **all PM tests and closures**, unlike `𝒲[ℰᵂ]` and `PM[wb]`;
   this is not a reflection theorem or a reverse transport of SSP's OTP security.
4. **IPDL and causal boxes are islands** for `UCSetupMorphism` (design-level proofs in
   their plans); **symbolic** reaches only the negligible tier; the first-draft edges
   `SSP → 𝔾ᵒ`, `IPDL → RS`, `RS → causal boxes` are withdrawn.
5. **Nondeterminism** [built over any symmetric monoidal 𝕄 and at SSP and PM;
   plan [uc-setup-nondeterministic.md](uc-setup-nondeterministic.md)]: the scheduler is a choice factor of
   the *grade*, not an effect.  Model B (adversary-resolved, Canetti) is `Std(𝕄)` restricted to the
   designated grades X ⊗ C_{S₁} ⊗ … ⊗ C_{Sₙ} (`ND/Grade`: `𝒢B`, `ιB`, `NDB`), the `choose` constructor
   compiled pick-ahead at SSP (`ND/SSP/Choice`) or on demand at PM (`ND/PM/Choice`); ιB is full and essentially surjective, so
   B-emulation is `Std(𝕄)`-emulation (`≤UC-B⇔≤UC`).  Model A (environment-resolved, "order does not
   matter") is the restriction of B to relabellings (`ND/A`: `closedA`, `𝒢A`, `incl` by
   `Transport.weaken`, `NDA`).  Both are instances of the generic *restriction of a setup along a
   monoidal functor of grades*, `Abstract2/Regrade` (`regraded`, the inclusion (Id, ι, id, `idᵛ`), the
   dual of `WideSubcategory`): it preserves `≤UC` when ι is essentially surjective with split
   comparisons (`Preserves.unrestrict-≤UC`) or the setup is grade-stable, and reflects it when ι is
   full (`restrict-≤UC`); along the unit at PM the U-kernels differ (`Examples/RegradeUnit`).
   **`A⇒B`**: A-emulation ⇒ B-emulation for all `f, g`, with the same simulator (both
   `ND/SSP/Setup` and `ND/PM/Setup`, with `A⇒SSP`/`A⇒PM` down to the ambient `≤UC`).
   Not conversely at SSP: one site copied to two is a B-emulation and no A-emulation
   (`ND/SSP/Reflect.¬reflect`); the optional PM witness is unproved. In SSP the request
   cannot be raised inside a step, so `choose` compiles pick-ahead and SSP's B is weaker than PM's; its
   laws are `ND/SSP/Laws` (the two orders of a choice equal after swapping the picks, `swap-ᵖ`, hence
   mutual A-emulations, `Swap.order-indep`).  The mathematical statement is `docs/uc-models.typ` §4.
   PM uses the sealed G-construction symmetry (`UC/Model/Symmetric.𝔾ˢ`) and partial stateless
   relabelling wires (`ND/PM/Relabel`); `Choice/Compose` and `Choice/Pin` check its online compiler
   against sequential/tensor composition and concrete request/resume behavior.
6. **Robust compilation** holds: `≤UC⇔robustᵁ` (UC = RHP over `≈ᵁ`-respecting
   predicates on attacked programs; `UC/Robust/Compilation.agda`), its trace form, and
   the two-setup version along a `UCSetupMorphism` (`robustᵁ-transfer` needs `ν.Epi` +
   target `GradeStable`; `robustᵁ-reflect` needs `ν.Mono` + full `Φ`); the
   outcome-only version is refuted (`Examples/RelSetup.agda:blind-incomplete`).
7. **`≤UC` is constructive cryptography's security-only emulation condition**:
   Maurer 2011 Definition 3(2), at ε = 0
   (`UC/RandomSystems/Construction.agda:≤UC⇔Constructs₀`) and exactly at every ε
   on the quantitative setup over `𝔾ᴿ` with the closed readout
   (`Quantitative.agda:≤UCᴿ[]⇔Constructs`, `≈ᵁᴿ[]⇔∼ᴿ[]`). It is not the full
   Definition 3: `Availability.agda:SecurelyConstructs` additionally compares
   the executions under designated no-adversary converters, with a separate
   availability error. Shared converters and equal errors specialize to the paper.
   `Examples/RandomSystems/Availability.agda` proves a mode-bit security-only
   counterexample and compatible full constructions. The toolkit includes Δ,
   nonexpansive composition and hybrids; `𝔾ᵒ`'s own `≈ᵁ[ε]` matches up to every
   positive slack. Amplification (`maurer2007`) is out of reach: `Dₚ` masses are
   lower reals, with no conditional probabilities.
8. **The one-time pad is proven in SSP** (`Examples/SSP/OneTimePad.agda:otp≤ideal`, and
   `leaky-not-secure` refuted via `≈ᵁ`), but **not by call-tree simulation**:
   `no-tree-simulation` shows syntactic `≈ᵖ` cannot move the key draw from `send` to
   `poll` (deferred sampling), so the core is a run-level induction.  The call/return
   discipline buys clean composition, not clean probabilistic reasoning at `≈ᵖ`; the
   formal distributional quotient `SSP.Dist.Setup` supplies that reasoning (§10). The pad crosses
   to PM[wb] (`Examples/SSP/OneTimePad/WB.otp≤idealᵂ`, by `preserves-≤UC`); to `𝔾ᵒ` it
   waits on the bridge.
9. **Performance** (resolved): the `UC.Graded` hang after the merges came from
   `UC/Machine/Run.agda:runᴹ-resp-≈ᴹ` being re-derived transparently; made `opaque`
   (>1800 s → 24 s).  Every new module is within budget at `-M3G` (worst 24.8 s);
   invalidated rebuild 997 s, root closure 517 s.  `UC.Model.Family` needs 5.4 GiB and
   is checked alone first — pre-existing, now in its header.  Known traps: unfolding
   `⟦A ⊗ B⟧` at the transparent machine category (ITM's `⊗-step` abstract target) and
   `pullbackᵛ` against a named presheaf (35 s+; write `ν` by hand).
10. **SSP up to distributions** ([uc-setup-ssp-dist.md](uc-setup-ssp-dist.md)): `≈ᵈ`, `UKernel`'s kernel
    of `ℰᵖ`, makes deferred sampling and fair-coin relabelling laws via sampling simulations; the
    one-time pad's core becomes nine per-activation squares, local but no shorter (51 vs 53 lines).
    `otp≤idealᵈ` still names a source-setup result. The actual quotient is exercised by the
    target-qualified `otp≤ideal-dist` and `leaky-not-secure-dist`, with the concrete simulator
    under all adversaries, ancillas, tests and games, and reflection for the negative result.

**Decisions pending from the maintainer:**

- **Interaction discipline**: standalone SSP setup (built) vs the `W`-restricted
  `𝒲 ⊆ 𝔾ᵒ` (built) — both halves exist and `SSP→PM[wb]` links them, transferring `≤UC`
  (finding 3).  Which one do examples get written in?
- **Hom-equality for RS**: adaptive `≈ᴿ` (built) was chosen over Maurer's
  non-adaptive `≈ᴮ` because congruence under feedback needs decidable message
  equality; `≈ᴮ⇒≈ᴿ-fin` covers finite alphabets.  Accept, or require `≈ᴮ` generally?
- **ITM tests**: pulled back `ℰᵒ` (built) vs own computable tests `ℰᶜ` (needs a
  density theorem; `hofheinz2013`: PPT is not a category, so "feasible" stays a side
  condition).
- **`W` reads the step's support**, so it does not respect `≈ₚ` and `𝒲` uses a
  saturation `W̃`.  Acceptable, or should well-bracketedness be behavioural?
- **SSP namespace**: parallel `CategoricalCrypto.SSP` with channel-indexed `Iface`
  (95 importers of the flat one untouched) — keep parallel, or migrate the flat layer?
- **Disk/memory**: the nix store is 15 GiB of a 20 GiB overlay (`nix-collect-garbage`
  is yours); `UC.Model.Family` needs >6 GiB to rebuild, which caps parallel agent work.

**In progress** (branches off `uc-setup-landscape`): `ssp-bridge` (𝒲 tensor,
`SSP→PM[wb]`, transfer corollary; finished by `games-dense`), `rs-toolkit` (advantage Δ, composition theorem,
hybrid lemma, security-only CC emulation), `otp-example` (one-time pad in SSP, transported),
`robust-lemma` (`≤UC ⇔ robust preservation`), plus the performance investigation.

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
wide subcategory of admissible morphisms, pull tests back) and `StdUCMorphism`.  Concrete
cross-model instances now in the tree: `rewrite⇒RS`, `itm⇒prot`, `itm⇒iso`, `ι⇒prot`
(§0 table; the complete list with their data is `docs/uc-models.typ` §5).

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
  route to `≈ᵁ`.  `𝔾ᴿ` now has a `QEvaluation` with the closed readout
  (`UC/RandomSystems/Quantitative.agda`); a family/negligible tier over RS still needs
  a resource grading on `𝔾ᴿ`.
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
- **Symbolic / Dolev–Yao** (plan: [uc-setup-symbolic.md](uc-setup-symbolic.md); steps 3–9
  and fixed-public-message step 10 built: `Sym≅`, `Sym`, `fine→sym`, relational frame
  emitters and `smt≤ideal`).
  `𝔻𝕐` = free monoidal category generated by DY roles (token-passing programs whose
  outputs are recipes over their frame), hom-equality `_≈Term_`, observation evaluated in
  `𝔾ᵒ` at term alphabets with global freshness by located names, kernel = DY trace
  (may-testing) equivalence, tests with an ancilla as in `Machine/UC.agda`,
  `GradeStable` hypothesis-free (`grade-stable`).  Roles emit and store canonical forms of a
  convergent theory, so programs equal modulo E are kernel-equal (`emit-≈E`). The
  machine layer's relational spans imply generic `≈ₛ⇒≈ℰ` on frame emitters and E₀
  `≈ℰ⇔≈ₛ`; the unrestricted multi-sort converse is false because unsorted foreign
  names can be shared across sorts (§3.7 of the symbolic plan). `smt≤ideal` uses a
  non-identity encryption-of-zero simulator for a fixed public message, not an
  environment-selected interactive message. **Corrections:** it is not "possibilistic next to
  `machine-iso`" (deterministic up to names); `Sym → machine-iso` does not exist, only
  the coarse variant `Sym≅ → machine-iso` (via `freeStrongMonoidal` into `Reverse`
  machines) and `Sym≅ → Sym` by `changeKernel`; there is no `symbolic → RS` (names are
  guessed with positive probability, so exact soundness fails).  Computational
  soundness is a `StdUCMorphism` `Sym≅ → UC.Model.Family.ucSetupᴺ` (the negligible
  tier over `𝔾ᵒ`) plus a side-conditioned pointwise theorem `sound⁺` over it
  (hypothesis table: IND-CPA+INT-CTXT or IND-CCA2/EUF-CMA, sorts, tags, …); `ν Mono`
  gives completeness, not soundness.  Needs the pointwise transfer in
  `Abstract2/Morphism` (`Preserves-≈ᵁ`/`transfer⁺`, landing with the SSP bridge) since
  `ℰᵒ` is not `GradeStable`.
- **Nondeterministic choice** (plan: [uc-setup-nondeterministic.md](uc-setup-nondeterministic.md),
  rewritten 2026-10-10 around finding 5 and `docs/uc-models.typ` §4).  Its generic piece is built:
  `Abstract2/Regrade`, a setup restricted along a monoidal functor of grades, with its inclusion,
  `≤UC` preserved (ι essentially surjective with split comparisons, or the ambient setup
  grade-stable) and reflected (ι full); causal boxes' `regrade` is the same morphism.
  ND_B is `Std(𝕄)` over designated grades X ⊗ C_{S₁} ⊗ … ⊗ C_{Sₙ} (via
  `Construction/Transport`), ND_A its restriction to relabellings; A → B preserves `≤UC`
  and does not reflect it (at SSP, `ND/SSP/Reflect`), and undesignation B → A is a section.  `choose` is site-indexed;
  SSP compiles it pick-ahead (the request cannot be raised inside a step), PM online; both are built,
  with PM's compilation laws and concrete two-site pins in `ND/PM/Choice/{Compose,Pin}`. Kept
  from the 2026-10-09 plan: the `choose` constructor with its `graft`/`serve` clauses, the
  no-go for a probability×nondeterminism monad (`varacca2006`, `zwart2019nogo`; `bonchi2022`
  not needed), and `P ∥ Q` not derivable from `choose` and `_⊗ᵖ_`.
- **Robust compilation** (plan: [uc-robust-compilation.md](uc-robust-compilation.md)).  Not a
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
                             │   │                           random systems 𝔾ᴿ ◀⇢ machine-category (det.)
                             ▼   ▼
              ucSetupᴺ (negligible tier over 𝔾ᵒ)    ND_A ──▶ ND_B = Std(𝕄)  (built at SSP and PM)

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
| SSP up to distributions (`≈ᵈ`, deferred sampling) | [uc-setup-ssp-dist.md](uc-setup-ssp-dist.md) |
| IPDL | [uc-setup-ipdl.md](uc-setup-ipdl.md) |
| causal boxes | [uc-setup-causal-boxes.md](uc-setup-causal-boxes.md) |
| symbolic / Dolev–Yao | [uc-setup-symbolic.md](uc-setup-symbolic.md) |
| nondeterministic choice | [uc-setup-nondeterministic.md](uc-setup-nondeterministic.md) |
| robust compilation (theorem, not a setup) | [uc-robust-compilation.md](uc-robust-compilation.md) |

A self-contained mathematical account of the setups, morphisms, non-morphisms and major theorems,
each linked to its Agda identifier: [uc-models.typ](uc-models.typ).

Shared infrastructure the plans agree on: `Categories.Category.Monoidal.Construction.Quotient`
(RS, SSP), `freeStrongMonoidal` in `Categories/FreeMonoidal.agda` (ITM, symbolic),
`Preserves-≈ᵁ`/`transfer⁺` in `Abstract2/Morphism.agda` (symbolic, SSP bridge), the generic
grade-side restriction `Abstract2/Regrade` (built; nondeterminism, causal boxes' `regrade`), and the
`GradeStable` counterexample for `ℰᵒ` (RS §5.3), which every plan relying on `bridge` must route around.

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
