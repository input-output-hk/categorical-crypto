# The landscape of UC setups and the morphisms between them

Findings of a 2026-10-09 study of the `UCSetup` instances that exist in the tree
(after merging `protocol-rewrite` and `machine-iso`) and of those worth adding:
interactive Turing machines, random systems, state-separating proofs (SSP), IPDL,
causal boxes, the symbolic model, nondeterministic choice, and robust compilation.
The question throughout is which `UCSetupMorphism`s exist, which are blocked, and by
what. Checked definitions and theorems below are linked to their implementation;
the per-setup plans of §7 also contain explicitly unimplemented designs and obligations.

**Historical provenance (2026-10-09).** Branch `uc-setup-landscape` = `origin/protocol-rewrite` with
`origin/machine-iso` merged.  Two semantic conflicts beyond git's: `protocol-rewrite`'s
solver refactor removed the symmetric variant `SymSolve`/`solveMorσ!`, so
`Machine/Monoidal/Naturality.agda` now proves its two naturality laws by hand from
`σ-natural`/`assoc-commute-from` and `Machine/UC/Kleisli.agda` passes its single
crossing to the monoidal solver as an opaque generator; and `UCSetup`'s `T₁` became the
graded monad's own action (`FromMonad`), so `Machine/UC.agda:T₁-⊗ʳ` is `≅ᴹ-refl`.  The
root closure then checked (353 modules, warning gate empty).
`docs/kb` is the knowledge base from branch `pagda`, extended by the plans' sources.

## 0. Status, major findings, decisions pending

**Built and green per module** (three branches merged into `uc-setup-landscape`, and the
symbolic steps of `uc-setup-symbolic.md` §6; escape-hatch baseline unchanged):

**Earlier checked update (2026-10-15; preserved).** The local-negligible→vanishing and
full-CSP→trace-CSP refinements, certified→ordinary symbolic erasure, and the scheduled
TaskPIOA→SSPᵈ operational adapter below have passed their integrated dedicated-consumer
checks and the full `CategoricalCrypto.agda` root closure. The warning gate is empty
and the 13 new source modules introduce no escape-hatch matches. The historical root
census in the provenance and original construction reports is not a count of this update.

**Current checked construction update (2026-10-15).** All four later slices are
integrated: the justified TaskPIOA→**scheduled NativeSSP** setup bridge and exact
fixed/padded/adaptive test boundary; arbitrary-QUC designated two-budget availability
with native RS/PM→QRS consumers; local native CSP ready refinement with supported
operations/represented contextual readouts; and structural coverage with actual
ITM/SSPdist migrations. Parent targeted checks and the final full
`CategoricalCrypto.agda` root closure passed without warnings. The isolated
escape-hatch baselines did not grow.
[Exact checked APIs and integration evidence](construction-generality-report.md#postscript-checked-construction-priorities-after-the-research-snapshot)
are later postscripts, not a rewrite of the historical 89-record census or a
replacement of the prior 13-module results.

| setup | what exists | key exports |
|---|---|---|
| random systems `𝔾ᴿ` | `Categories/…/Construction/Quotient` (generic), `UC/Machine/Behaviour*`, `UC/RandomSystems/{Seal,Setup,Morphism,FullAbstraction,Advantage,Composition,Construction,Quantitative,Availability,Availability/Rewrite}`, `UC/Quantitative/Availability` | `rewrite⇒RS`, **`≈ᵁ⇔≈ᴿ`**, **`¬gradeStableᵒ`**, `≈ᴮ⇒≈ᴿ-fin`, `Δ`, composition/hybrids, security-only `Constructs` bridges; generic two-budget `SecureAvailable`, native `SecurelyConstructs` equivalence, measured PM→QRS cap transport, compatible/mismatched-cap replacement and mode/drop/nonzero consumers |
| ITM `𝕋ᴹ` | `ITM/{Core,Run,Functor,Setup,Transfer,Relational,Relational/Tests}`, `UCSetup/Coverage`, `Standard2/Coverage`, `UC/Model/Coverage`, `Machine/Initialized`, `FreeMonoidal.freeStrongMonoidal`, `Seal.unitᵒ` | `itm⇒prot`, `≈ℰ⇔`, actual epi/mono test witnesses, `dual-context` (partial image-dual basis), **`preserves-≈ᵁ`**, **`reflects-≈ᵁ`**, **`preserves-≤UC`**; UC reflection only with a supplied simulator lift; structural `Relational.Uninitialized.⇒iso` and separate initialized trace consumers |
| SSP (call/return) | `SSP/{Iface,Protocol,Protocol/Category,Protocol/Monoidal,Observation,Setup,Reduction,Compile,Semantics,Cut,Dense,Dense/Tests}`, `Standard2/UKernel`, `Protocol/{Sim,Machine/Resp,Machine/Oracle}`, `UC/Bracket{,/Category}` | `StdSetup`, `Protᴹ`/`Protˢ`, `toProtocol`, `morphism-resp`, `W`, `morphism-W`, `𝒲`, `ι`, **`games-dense`**, **`SSP→PM[wb]`**, **`preserves-≤UC`** |
| symbolic `𝔻𝕐` (steps 3–9; static and conservative transmitting step 10) | `Symbolic/{Term,Term/PairEnc,Deduction,Role,Fine,Semantics,Setup,Static,Static/PairEnc,Test,TheoryTests,StaticTests,Example/SecureChannel,Example/SecureChannel/Interactive}`, `Symbolic/RunFollowing`, `FreeMonoidal/Decorated`, `Machines/Sim/{Relational,RunFollowing}`, `UC/{Machine,Model}/Relational` | `Sym≅`, `Sym`, `fine→sym` (`coarse` Epi), **`grade-stable`** (hypothesis-free), `≈ᵁ⇔≈ℰ`, **`emit-≈E`**, **generic `≈ₛ⇒≈ℰ`**, **E₀ `≈ℰ⇔≈ₛ`**; admissible `EqTheory` closes under sorted name-to-term substitution, with `fresh-name`, `distinct-names`, `⊬-fresh`; fixed-public-message **`smt≤ideal`** retained, plus **`Interactive.smt≤ideal`** for one environment-selected plaintext with conservative ciphertext-controlled delivery and actual decryption; `leaky≉real`/`leaky≉simulated` are observational separators, not all-simulator impossibility; no multi-sort static converse or computational-crypto theorem |
| nondeterministic choice (over any symmetric 𝕄; at SSP and PM) | `Abstract2/Regrade{,/Pin,/Unit}`, `Categories/…/Construction/Transport` (`Closed`, `weaken`), `ND/{Grade,A,Relabel}`, `ND/SSP/{Choice,Choice/Compose,Choice/Pin,Choice/Dist,Setup,Laws,Reflect}`, `UC/Model/Symmetric`, `ND/PM/{Factor,Read,Relabel,Setup,Choice,Choice/Compose,Choice/Pin}` | `regraded`, `inclusion`, `𝔾ˢ`, `NDB`, `NDA`, **`A⇒B`**, `≤UC-B⇔≤UC`, `≤UC⇒relabel`, PM online request/resume and compilation laws; SSP `swap-ᵖ`, **`order-indep`**, **`¬reflect`** |
| certified symbolic `𝔻𝕐ᶜ` | `Symbolic/Computational{,/Run,/Obstruction}`, `Symbolic/{InterpretationTests,Erasure,ErasureTests}` | distinct `CertifiedSource.Sym≅ᶜ.StdSetup`; `fine→comp : UCSetupMorphism` into `ucSetupᴺ`; **`Erasure.certified→fine`** into ordinary `Sym≅`, erasing generator rate/query certificates and mapping tests `(Y,T) ↦ (FY,FT)`; no U/UC preservation/reflection for erasure; unrestricted rate-one runtime certificates are refuted by `no-backwards-certificate`; no crypto soundness or PPT setup is asserted |
| computational family tiers | `UC/Family/Negligible/{Setup,Vanishing,Tests}` and `UC/Family/Vanishing` | **`negligible⇒vanishing : UCSetupMorphism ucSetupᴺ ucSetup^ω`**; identity computational data and native test representatives; preserves `≈ℰ`, `≈ᵁ`, `≤UC`, retaining each supplied source simulator by `same-simulator = refl`; no uniform bound or endpoint UC-nonreflection theorem |
| SSPᵈ | `SSP/Dist{,/Setup,/Compile}`, `SSP/Dense/Tests`, `UCSetup/Coverage`, `Standard2/Coverage`, `Examples/SSP/OneTimePad/{Dist,WB}` | `ssp⇒dist` preserves/reflects UC; **`dist⇒PM[wb]`** derives `≈ℰ`, `≈ᵁ`, `≤UC` preservation from actual finite-approximation test density and total literal `Iface` coverage; the actual `composeᵁ` triangle agrees pointwise, including return/ext/sub comparisons; categorical and security OTP consumers; no full SSP reflection |
| finite exact task-PIOA | `TaskPIOA/{Core,Product,Setup,Simulation,Security,Tests,SSPAdapter,SSPAdapterTests,Adaptive*,Marker*}`, `SSP/Dist/{Sampling,FiniteTesting}` | actual **`UC.StdSetup`**, native plugging/correspondence, same-signature/unit-leakage UC→contextual theorem; exact all-source-tests→fixed padded↔finite Tick Calls→actual composed consumers; bare compact-word pair separated by an actual source marker, not UC/contextual nonreflection |
| scheduled native SSP | `TaskPIOA/NativeSSP/{Core,Product,Protocol,ProtocolTests,Setup,Morphism,Security,Tests}`, `SSP/Dist/Coins`, `TaskPIOA/Simulation/Properties` | distinct **`NativeSSP.Setup.UC.StdSetup`** and **`Morphism.bridge`** from TaskPIOA; actual SSP tensor/connector joint square at every input/task channel; constructive native test backtranslation and total ancillary coverage derive E/U/UC preservation; noncanonical/native/masked/nonidentity-simulator/composed-protocol consumers; **not full SSPdist** |
| typed open-network CSP | `CSP/{Category,Monoidal,SemanticInvariance,Observation,Testing,Setup,Security,SecurityNetwork,SetupTests,MonoidalTests}`, native correspondences and eleven ready/refinement modules | actual **`OpenCSPᴹ`**, derived **`structural→operational`** / **`observations-respect`**, native **`ℰᶜˢᵖ`**, **`StdSetup`**, all-adversary **`f≤UCg`**, independent local ready simulation with full raw-triple inclusion, supported hiding/Par/family/linking and actual represented-consumer contextual results; not UC/native-refinement identification or a PM/SSP bridge |
| trace-observed CSP | `CSP/Trace/{Observation,Testing,Setup,Morphism,Security,Tests}` | new **`Trace.Setup.StdSetup`** and **`fullCSP→traceCSP : UCSetupMorphism`**; same `OpenCSP` carriers, grades, tensor action, consumers and resource closures; raw observation triple projected to traces; `≈ℰ`/U/UC preservation, pointwise same simulator; ready/choice refusal witness proves observation information loss only, not UC nonreflection |
| finite IPDL API interpreter — not a setup | `IPDL/{Syntax,Native,SSP,Tests,ReadOrder,Linker}` | `Correspondence.agreement` for finite adaptive Boolean-verdict strategies including private coins; persistent/read-order and correlation witnesses; concrete hidden-channel, copy and feedback squares |

**Major findings** (proven unless marked; finding 3's raw-compiler obstruction is
argued in `Protocol/Machine.agda:14-19`'s header, not a universal no-morphism theorem):

1. **`≈ᵁ` at protocol-model IS behavioural equivalence of random systems**
   (`≈ᵁ⇒≈ᴿ` + `≈ᴿ⇒≈ᵁ`).  This fixes the meaning of the library's security notion.
2. **`ℰᵒ` is not `GradeStable`** (`¬gradeStableᵒ`: a stateless reveal machine).
   `Abstract2.bridge` is unusable at protocol-model; `≈ᴿ⇒≈ᵁ` replaces it.
3. **The raw compiler does not supply an `SSP → 𝔾ᵒ` morphism**:
   `morphism wireᵖ ≉ᴹ 𝒢.id` and the G-tensor interleaves. The implemented call/return
   compiler targets the quotient `PM[wb]`, not full PM (§4). Built: `W`, `𝒲ᴹ` with its tensor
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
4. **Native boundaries are not universal no-map theorems.** IPDL now has a checked
   finite Fig. 9 resource interpreter and concrete linking witnesses, but no source setup
   morphism. Finite task-PIOA is an independent implemented setup with a checked scheduled
   operational adapter to SSPᵈ, not a setup-morphism or U/UC-transfer edge.
   Causal-box/RSIM bridges remain proposals. Typed open-network CSP is linked by a
   checked observation refinement to the new trace-observed CSP setup, but has no
   PM/SSP bridge. The certified symbolic source has its formal family
   interpretation and a checked certificate-erasure morphism into ordinary `Sym≅`; `Sym≅`
   has its relational interpretation. No security direction is claimed for erasure.
   The old raw `SSP → 𝔾ᵒ`, `IPDL → RS` and `RS → causal boxes` arrows remain withdrawn for those candidates.
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
   The new generic
   [`SecureAvailable`](../src/CategoricalCrypto/UC/Quantitative/Availability.agda#L41)
   pairs a fixed-simulator security witness with unit-grade capped U-agreement
   in **any QUCSetup**, without a base tensor, `T_I B ≅ B`, or cap for every grade.
   Common middle caps add errors independently; distinct caps require an actual
   `κ` comparison and availability error **`((εa ⊕ κ) ⊕ δa)`**, literally
   parenthesized because neither associativity nor commutativity is assumed.
   The directed mode law is `a ∘ s ≈ b`.
   [Native RS equivalence](../src/CategoricalCrypto/UC/RandomSystems/Availability.agda#L99)
   uses exact QRS full abstraction and both directions of the standard unitor;
   [PM→QRS transport](../src/CategoricalCrypto/UC/RandomSystems/Availability/Rewrite.agda#L31)
   uses the actual measured bridge and cap square, not the qualitative morphism alone.
   Mode-bit consumers include incompatible perfect edges and genuine security0/
   availability1 composition; literal `alwaysDrop` has perfect security but fails
   designated availability, while reliable double-flip gives a native true reply.
   FaultFlag's proved passive cap adds genuine `(¼,¼)` + `(¼,¼)` → `(½,½)`
   full constructions with the strict smaller-security-error control retained.
   HashForward remains security-only. None is arbitrary-adversary liveness,
   fairness or a general availability-qualified honest-protocol composition theorem.
   The toolkit includes Δ, nonexpansive composition and hybrids; `𝔾ᵒ`'s own
   `≈ᵁ[ε]` matches up to every positive slack. Amplification (`maurer2007`)
   remains out of reach: `Dₚ` masses are lower reals, with no conditional probabilities.
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
    The compiler now [descends to `SSPᵈ → PM[wb]`](../src/CategoricalCrypto/SSP/Dist/Compile.agda#L71),
    preserving `≈ℰ`, `≈ᵁ` and `≤UC`. Its actual
    [`composeᵁ` triangle](../src/CategoricalCrypto/SSP/Dist/Compile.agda#L88)
    agrees with the direct bridge pointwise on objects/homs/tests, grades, κ,
    tensor/unit comparisons, computations and return/ext/sub law expressions—not as
    equality or an isomorphism of bundled morphism records.
    [`lazy≈realᵂ`, `otp≈idealᵂ` and `otp≤ideal-distᵂ`](../src/CategoricalCrypto/Examples/SSP/OneTimePad/WB.agda#L19)
    consume this categorical/security route. No UC reflection or full-PM security follows.

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
cross-model instances now in the tree: `rewrite⇒RS`, `itm⇒prot`, `ITM.Relational.Uninitialized.⇒iso`, `ι⇒prot`
(§0 table; the complete list with their data is `docs/uc-models.typ` §5).

### 1.1 Structural coverage, with actual compiler instances

The checked [`UCSetup.Coverage.TestCoverage`](../src/CategoricalCrypto/UCSetup/Coverage.agda#L26)
uses the existing morphism's natural test compiler `ν`. Its sole `complete` field
is **target-action density**: for arbitrary target arrows `h,k : A′ → F B`,
agreement on all explicit compiled tests `ν B t` implies agreement on every target
test of `F B`. The domain and arrows need not be source images. An actual test
epi constructs coverage; [`covered-≈ℰ`](../src/CategoricalCrypto/UCSetup/Coverage.agda#L36)
derives bare-kernel preservation from density and naturality. No E/U/UC-preservation
theorem is stored as coverage data.

For a standard strong-monoidal compiler,
[`ContextRepresentation`](../src/CategoricalCrypto/Standard2/Coverage.agda#L54)
stores a **source ancillary object and an actual target isomorphism** `F V ≅ W`.
`covered-context` derives target E-agreement at that represented prefix.
Total `AncillaCoverage` gives `covered-≈ᵁ` and `covered-≤UC`; essential
surjectivity is a constructor for total coverage, not a necessary hypothesis.
The separate `reflects-≈ᵁ` uses `ν.Mono`, cancelling the strong image-prefix
comparisons. `SimulatorRepresentation s′ s` compares the two substitutions'
E-actions on **arbitrary target computations and prefixes**, independently of a
desired source security conclusion. Conditional UC reflection additionally consumes
that representation and the explicit source simulator. No target `GradeStable`
or unrestricted simulator backtranslation is introduced.

Actual instances retain their old theorem contracts:

* [`ITM.Transfer`](../src/CategoricalCrypto/ITM/Transfer.agda#L50) constructs test
  coverage from `νᵀ-epi`, reflects U with `νᵀ-mono`, and represents only
  `dualPorts A` via `image-dual-iso`. The independent, target-only
  [`dual-prefix⇒≈ᵁ`](../src/CategoricalCrypto/UC/Model/Coverage.agda#L11)
  turns that one PM dual-prefix comparison into U-equivalence for arbitrary PM
  computations. This is **not** total representation of arbitrary PM ancillas.
  General UC preservation and behavioral-lift-conditioned UC reflection remain.
* [`SSP.Dense.Tests.test-coverage`](../src/CategoricalCrypto/SSP/Dense/Tests.agda#L476)
  is constructed directly from `tests-dense` for arbitrary WB target arrows and
  input closures, using real finite truncation/depth/call/positive-rational
  approximation witnesses—not an old transfer theorem and not exact test epi.
  [`SSP.Dist.Compile`](../src/CategoricalCrypto/SSP/Dist/Compile.agda#L78)
  reuses this density on identical test representatives and represents every
  target `Iface` literally with a reflexive isomorphism. Its generic E/U/UC
  proofs no longer detour through source quotient reflection.

The ITM transported/reflected simulator/security clients and the categorical and
security OTP clients retain their statements. The full pointwise SSP compiler
triangle, including return/ext/sub law-expression comparisons, remains checked;
this is not equality of dependent morphism records or proof fields.
The parent checked the integrated `Examples.ITM.Tests` and
`Examples.SSP.OneTimePad.WB` closures at source `f0d6ba39c`, rebuilding all seven
changed modules and affected dependencies (18 Checking lines), with paired
`-M6G -H1G`, no warnings. Root validation belongs to the later combined closure;
the observed 92.90 s combined run is not an uncontended performance claim.

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
`ITM.Relational.Uninitialized.⇒iso` uses the second, all-state structural observation
`Uninitialized.ℰ = ℰ-tests ∘F Uninitialized.F.op` (module with K); it is not an initialized
or probability-sensitive security interpretation. Separately, `initializedLeaf` and
`Machine.Initialized.Executes` retain `blank`/`start` and thread finite activation traces.
`ITM.Relational.Tests` proves same-table/different-start output separation and positive
one- and two-query executions. This execution boundary is not another `UCSetup`.
A categorical comparison with `protocol-rewrite` needs additional initialization,
deterministic realizers, and a mirror iso of wires; the trace API does not provide it.

The separate [`ITM.Transfer`](../src/CategoricalCrypto/ITM/Transfer.agda#L40) now
preserves and reflects U-kernel equality and
[generally preserves `≤UC`](../src/CategoricalCrypto/ITM/Transfer.agda#L62).
The source domain's dual-port ancilla interprets as its PM dual; that U-component
gives target behavioural equality and hence target U-equivalence. `transfer⁺` then
applies without the false PM grade-stability premise. Reflection of UC additionally
needs a target dummy simulator with an explicitly supplied source lift up to
[behavioural equality](../src/CategoricalCrypto/ITM/Transfer.agda#L72).
[`transported-secure` and the reflection consumers](../src/CategoricalCrypto/Examples/ITM/Tests.agda#L49)
exercise these exact contracts. U-kernel reflection alone is not unconditional
simulator backtranslation or UC reflection.

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
- **IPDL** (plan: [uc-setup-ipdl.md](uc-setup-ipdl.md)). The proposed open
  `StdUC 𝕀ᴹ ℰⁿ` remains unimplemented. Separately, the finite typed Fig. 9 API is now
  a checked [`SSPᵈ` resource interpretation](../src/CategoricalCrypto/IPDL/SSP.agda#L29):
  inputs assign once, `Get` reads before saturation, absence is `None`, and blocked reads
  retain their residual state. Each query reaches quiescence by decreasing work.
  [`Correspondence.agreement`](../src/CategoricalCrypto/IPDL/SSP.agda#L90) covers every
  finite typed adaptive **Boolean-verdict** strategy, including private rational coins,
  comparing the native exact run lifted by `return⊥` with the SSP partial-verdict run.
  [`ReadOrder.all-strategies`](../src/CategoricalCrypto/IPDL/ReadOrder.agda#L103)
  hides internal read order, unlike the separately separated demand-exposing pull encoding.
  Persistent shared samples and the three-way correlated/independent
  [`feedback-test`](../src/CategoricalCrypto/IPDL/Tests.agda#L81) are checked.
  The separate two-residual saturation linker proves fixed
  [hidden-channel](../src/CategoricalCrypto/IPDL/Linker.agda#L123),
  [copy-identity](../src/CategoricalCrypto/IPDL/Linker.agda#L193), and
  [seeded/blocked feedback](../src/CategoricalCrypto/IPDL/Linker.agda#L257) witnesses.
  The copy result is not SSP wire identity; there is no arbitrary flattening,
  open-functor or source-UC transfer theorem. The target resources can use the descended
  WB compiler without creating an IPDL source setup or repairing the old pull compiler.

### Coarser machine equalities go to random systems, not to `𝔾ᵒ`

Trace equivalence (the `machine-category` branch) is coarser than `≈ᴹ`: trace-equivalent
deterministic machines are bisimilar, but exhibiting a zigzag of *functional*
simulations needs the minimal automaton as a `Set`, i.e. a quotient, which `--without-K`
Agda without HITs does not have.  So `F-resp-≈` fails into `𝔾ᵒ`.  Its `≈ᵗ` is
possibilistic, so only the deterministic fragment maps into RS (`det-≈ᴮ⇒≈ᴿ`).

## 5. Causal boxes, symbolic, nondeterminism, and the other candidates

- **Causal boxes** (plan: [uc-setup-causal-boxes.md](uc-setup-causal-boxes.md)).
  The classical two-phase `Box` design uses positions `ℕ`, slot-alphabet pairs and
  product tensor. It is a proposed category of resource-preserving converters with
  structural zero-delay wires, not the native strictly causal boxes: native identity
  is not causal. Delay-sensitive sequential linking and synchronous product expose
  candidate-specific obstructions to the old direct PM interpretations, not universal
  no-map theorems. Resource correspondence, lawful plugging and observation transport
  remain unproved. Explicit RSIM buffering is a separate operational design; the
  now-built finite task-PIOA setup below is neither a causal-box submodel nor PM choice.
- **Finite exact task-PIOA** (implemented; [plan §4.3](uc-setup-causal-boxes.md#43-other-setups-asynchronous-models)).
  [`UC.StdSetup`](../src/CategoricalCrypto/TaskPIOA/Setup.agda#L95) uses a free
  **non-symmetric monoidal** category of typed installation and compatible-product
  wiring contexts. An automaton is a native value at a signature slot; `install`
  embeds it as a generator and `connect` performs native synchronization. Hom equality
  is free monoidal congruence, not native trace equivalence. Tests close these contexts
  with a fixed finite task word and rational trace reward, comparing expected rewards
  on every native assignment. [`plugging` and `native-correspondence`](../src/CategoricalCrypto/TaskPIOA/Setup.agda#L82)
  connect them directly to native product runs, not pulled-back PM tests.
  Native inputs are enabled, disabled tasks stutter, repeated tasks execute again,
  and a joint tagged word retains order while environment automata adapt.
  [`Contextual`](../src/CategoricalCrypto/TaskPIOA/Security.agda#L33) has
  `∀ environment E, ∀ real word ρ, ∃ ideal word ρ′`; a fixed same-signature
  state-map/lumping simulation separately implies equal traces, this inclusion and
  [`simulation⇒≤UC`](../src/CategoricalCrypto/TaskPIOA/Security.agda#L78).
  The reverse-facing [`resource-≤UC⇒contextual`](../src/CategoricalCrypto/TaskPIOA/Security.agda#L84)
  is only for designated same-signature resources at unit leakage, with the same word.
  No UC/native equivalence, contextual-to-UC converse or non-unit theorem is asserted.
  [`masked-output-secure`](../src/CategoricalCrypto/TaskPIOA/Tests.agda#L125) is a
  probabilistic positive; repeated sends share its one sampled ciphertext.
  Synchronized/order-sensitive and adaptive-echo witnesses exercise the native semantics;
  their negatives separate named distributions, not all simulators or UC emulation.
  The checked [`SSPAdapter`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L47)
  interprets a native automaton as an actual SSP tick protocol. Its exact finite rational
  sampler, [`rationalCoins`](../src/CategoricalCrypto/SSP/Dist/Sampling.agda#L102),
  covers non-dyadic probabilities as well as fair coins. It samples the **joint**
  successor-state/optional-output law, with disabled tasks returning successful stutter,
  not failure. [`run-agreement`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L183)
  holds for every finite word and initial state;
  [`reward-agreement`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L203)
  preserves arbitrary rational trace rewards. The actual composed SSP
  [`consumer`/`experiment-agreement`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L214)
  matches the native Boolean verdict distribution.
  [`all-calls-agreement`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L150)
  additionally gives individual tick-interface adequacy for every finite adaptive/partial
  `Calls` tree through existing `Samples`/`sample-⟦⟧`; this does not change the
  source's fixed-word scheduler or prove source-UC preservation.
  The independently defined [`Synchronized`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L275)
  target protocol includes connected receiver-input updates as well as sender kernels.
  Its general step/tree/joint-schedule correspondence is not ordinary SSP tensor and
  is not an alias for compiling an already-evaluated source product.
  [Native computation consumers](../src/CategoricalCrypto/TaskPIOA/SSPAdapterTests.agda#L149)
  give send-first/read-first acceptance 1 and 0, disabled-then-enabled acceptance 1,
  persistent correlated output/state and non-dyadic acceptance 2/3.
  **Exact finite test relationship:**
  [`source-tests-imply-padded`](../src/CategoricalCrypto/TaskPIOA/Marker.agda#L171)
  uses actual marker contexts for arbitrary signatures, including inputs, to recover
  activation timestamps. All actual source tests equal ⇒ every fixed padded-word
  law equal ↔ every finite Tick `Calls` final-result law equal ⇒ actual
  `runᵖ (D ∘ᵖ resource M)` task-consumer equality.
  Only the [padded/finite-Calls step](../src/CategoricalCrypto/TaskPIOA/AdaptiveFinite.agda#L69)
  is an iff. Adaptive task choices, rational coins, early return and failure are
  included; successful silent replies and outer failure are distinct, with no
  submass renormalization. The generic cylinder proof needs total finite-support
  rational kernels, unit queries and decidable replies—not finite state/global
  reply enumeration or an all-calls premise.
  The [raw pulse pair](../src/CategoricalCrypto/TaskPIOA/Adaptive.agda#L82)
  agrees for every silence-erased fixed word/reward, but a fixed padded tester
  already gives `1/0`, an adaptive tester `½/0`, and an actual source marker `1/0`.
  This is activation-timing information loss, **not** source contextual equality,
  an adaptive-power theorem or UC nonreflection.
  The positive adaptive consumer uses different Bool/Bool×Unit state representations,
  two reachable different-next-task branches of probability `½`, actual composed
  true probability `½`, and an explicit failure branch of probability `½`.
- **Scheduled native SSP — justified new setup bridge.**
  [`NativeSSP.Morphism.bridge`](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Morphism.agda#L154)
  targets **new `NativeSSP.Setup.UC.StdSetup`**, not full `SSP.Dist.Setup.StdSetup`.
  Independent finite owned `Coins` machines expose boundary-input and task channels;
  a proved bidirectional state/kernel-simulation congruence quotients native wiring.
  Target tests execute actual `Protocol.step`/`Calls` with rational trace rewards,
  rather than aliasing source evaluation.
  [`Protocol.connector`/`installed`](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Protocol.agda#L48)
  uses real sender/receiver-input calls, ordinary SSP tensor and actual composition.
  `joint-square` preserves the whole successor-state/reply law at every paired state
  and every public-input/left-task/right-task channel. Right-sender coin commutation
  is applied only after deterministic output selection. Actual scheduled execution
  and arbitrary SSP closing-consumer implementation congruence follow for the two
  concrete corresponding implementations; this does not enlarge the setup's
  scheduled test class.
  Constructive `sampleMachine`/context/value/test backtranslation covers **every
  native valuation**, including noncanonical coin trees, justifying natural `ν`
  and `ν-epi`. Explicit total object/ancillary isomorphisms and actual test coverage
  [derive E/U/UC preservation](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Security.agda#L20);
  no coverage record assumes the conclusion.
  Consumers exercise masked U/UC transfer (closing reward `½`), a genuinely
  nonidentity installation simulator (observed reward `1`), actual Boolean SSP
  `runᵖ` results `just true`/`just false` by schedule order, public-input broadcast,
  persistent correlation and right-sender non-dyadic receiver reward `2/3`.
  The older SSPᵈ tick adapter remains operational. No full SSPdist context/ancilla/
  simulator coverage, reflection, full native-refinement equivalence, PM/causal-box
  morphism, PPT, infinite-trace or fairness theorem is supplied.
- **CSP typed open networks — implemented and checked.** Source `3c3e3caf7`, registered
  at root `b535ea092`, supplies the actual
  [`OpenCSPᴹ`](../src/CategoricalCrypto/CSP/Monoidal.agda#L94).
  Objects are finite typed/polarised interfaces; arrows are finite networks whose
  guarded, unit-returning components may have arbitrary small payloads, arbitrary
  internal branching and infinite behavior. Identities are transparent zero-box
  aliases, composition is fresh-tagged flattened gluing, and tensor is disjoint union.
  Hom [`_≅_`](../src/CategoricalCrypto/CSP/Structure.agda#L44) consists of mutual
  boundary/incidence-preserving structural embeddings, inverse on boxes and up to
  connectivity on names—not literal graph isomorphism or a native behavioral quotient.
  The associator/unitors, naturality, triangle and pentagon are proved.
  [`structural→operational`](../src/CategoricalCrypto/CSP/SemanticInvariance.agda#L319)
  derives bidirectional LTS transport; `observations-respect` preserves raw finite
  traces, stable failures and silent divergence after the **exact** trace.
  Stability excludes both τ and pending joint completion; this is not
  divergence-flooded FD chaos. A connected-class `Gather` has inhabited support and
  one selected class port per incident box, so a blocked participant cannot be bypassed.
  Hidden steps additionally require a boundary-free class, a unique selected output
  box and a distinct input listener. Visible steps instead enforce boundary compatibility.
  Nonempty all-returned families complete jointly once; empty aliases add neither
  a completion participant nor a phantom step.
  [`ℰᶜˢᵖ`](../src/CategoricalCrypto/CSP/Testing.agda#L25) compares consumers `A → Ω`
  on **every actual resource** `I → A`, with composition as pullback.
  [`Setup.StdSetup`](../src/CategoricalCrypto/CSP/Setup.agda#L13) is the actual
  `Standard2.StdUC` instance, with `T₀ X B = X ⊗ B` and `T₁ X r = id X ⊗ r`.
  [`Security.f≤UCg`](../src/CategoricalCrypto/CSP/Security.agda#L53) covers every
  arbitrary actual adversary `a : Network X X′`; its simulator is `a ∘ h`, uniformly
  before tests and ancillary contexts. The grades are unequal and nonempty:
  `X` has Bool challenge/response ports, `Y` a Unit output. The independently defined
  [flat two-box real network](../src/CategoricalCrypto/CSP/SecurityNetwork.agda#L111)
  has a payload-reading Bool consumer with an exhibited four-private-rendezvous run,
  visible true and joint completion; the ideal experiment has the same whole triple.
  Native correspondence covers a unit-returning single box, nonempty finite
  common-private-channel families with arbitrary payloads and a unique producer/
  distinct listener, namespaced disjoint tensor pairs, and concrete plugging.
  [Strong native interchange](../src/CategoricalCrypto/CSP/NativeInterchange.agda#L240)
  is for four processes with persistent `OffersOnly` in Boolean-disjoint namespaces,
  using all-sync/all-interleave operators and an all-hide lifting, not arbitrary hiding.
  These are source-faithful to the `ret/sil/react` core at external pin
  [`9a40d1de330f376c3a102e7c9f1282f4fa830a7e`](https://github.com/input-output-hk/agda-cardano-common/blob/9a40d1de330f376c3a102e7c9f1282f4fa830a7e/src/ITree-CSP/Process_Trees.agda#L112),
  retaining the native outside-synchronization post-event commitment τ.
  Supplied sort-code equality and local finite-index equality derive code/index-only
  UIP, not arbitrary payload, branch, process or function UIP.
  The constructive closure imports no classical DR/FD postulates. `Network` and
  `PortIso` no longer have definitional record η; constructor/projection β and actual
  category/tensor/grade computations remain checked, with explicit payload transports
  where opaque typing proofs require them.
  The new [`Trace.Setup.StdSetup`](../src/CategoricalCrypto/CSP/Trace/Setup.agda#L14)
  has the **same** `OpenCSP` computation category, `OpenCSPᴹ` grades/tensor action,
  `I`, `Ω`, native consumer representatives `A → Ω`, and actual resource closures.
  Only its observation equality changes to mutual implication of finite visible-trace
  predicates. [`project`](../src/CategoricalCrypto/CSP/Trace/Observation.agda#L32)
  keeps exactly `NativeObservation.traces`, forgetting stable failures and exact-trace divergence.
  [`fullCSP→traceCSP`](../src/CategoricalCrypto/CSP/Trace/Morphism.agda#L45)
  is a complete `changeKernel` setup morphism, with identity computational data and
  an identity-on-representatives natural test map (proved epi, no mono claim).
  [`≈ℰ-preserved`](../src/CategoricalCrypto/CSP/Trace/Morphism.agda#L48) and the public
  `Refine.≈ᵁ-refine`/`≤UC-refine` give forward security;
  [`≤UC-pointwise`](../src/CategoricalCrypto/CSP/Trace/Morphism.agda#L70)
  additionally retains each supplied per-adversary simulator. The concrete
  [`concrete-simulator`](../src/CategoricalCrypto/CSP/Trace/Security.agda#L29)
  equation is `proj₁ … a ≡ a ∘ h` by `refl`.
  The checked [ready/choice witness](../src/CategoricalCrypto/CSP/Trace/Tests.agda#L52)
  has equal projected evaluations but different raw observations via an empty-trace
  stable refusal. This is observation/evaluation information loss, **not** an
  endpoint contextual or UC-nonreflection theorem.
  The later checked
  [`ReadyRefinement._⊑_`](../src/CategoricalCrypto/CSP/ReadyRefinement.agda#L24)
  is an **independent local strong ready simulation**, oriented **SPEC ⊑ IMPL**.
  `match` matches every implementation step with a same-labelled specification
  step and related successor; `ready` reverses immediate enabledness. Both τ and
  `√` are included. Reflexivity/transitivity and complete implementation-to-
  specification raw trace/stable-failure/exact-divergence inclusion are derived,
  not fields; mutual refinement gives raw agreement. This is sufficient, not
  completeness for extensional raw FD.
  [`hide-refines`](../src/CategoricalCrypto/CSP/NativeRefinement.agda#L67)
  supports every Boolean mask.
  [`Separated.par-refines`](../src/CategoricalCrypto/CSP/NativeRefinement.agda#L137)
  retains persistent `OffersOnly` at all four operands and disjointness outside
  synchronization, excluding the actual overlapping-offer commitment case.
  Pointwise refinement lifts through same-shape nonempty common-channel families
  and all-hide; [`ClosedReadout`](../src/CategoricalCrypto/CSP/NativeReadout.agda#L28)
  transports execution, stability/refusals and exact divergence both ways through
  the real native/network correspondence, retaining sole producer, distinct
  listener and all-participant ownership.
  [`Plugged.flattening`](../src/CategoricalCrypto/CSP/NativeContextRefinement.agda#L87)
  is an explicit two-sided structural isomorphism to actual
  `consumer q ∘ producer p`.
  [`consumer-refinement`/`mutual-context-equality`](../src/CategoricalCrypto/CSP/NativeContextRefinement.agda#L121)
  quantify over every represented native one-input consumer, **not** arbitrary
  network contexts or ancillary systems. Supported Boolean-disjoint persistent
  Quad [`hidden-link-refines`](../src/CategoricalCrypto/CSP/NativeInterchangeRefinement.agda#L62)
  and `hidden-link-agreement` are history-sensitive, not initial-step-only or
  arbitrary fan-in rules.
  Actual [`Testing.Test`/`pull`/`Evaluation.read` consumers](../src/CategoricalCrypto/CSP/NativeRefinementTests.agda#L55)
  prove a genuine hidden handshake, exact `[√]` success and terminal refusals.
  A divergent-branch-elimination refinement has a
  [strict same-tester exact-divergence inequality](../src/CategoricalCrypto/CSP/NativeRefinementTests.agda#L146);
  this is not UC nonrealizability.
  [`RawHidingBoundary`](../src/CategoricalCrypto/CSP/RawHidingBoundary.agda#L157)
  proves that raw-triple inclusion alone is **not a hiding congruence**: a
  countably infinite root choice of `n` followed by `n` visible events and STOP
  has the same finite traces as a visible loop and includes its failures, with
  neither diverging before hiding; only the loop diverges after all-hide.
  It is not a finitely branching counterexample. The ready rule rejects it at
  the root τ mismatch; no divergence flooding/choice/compactness principle is used.
  The parent integrated all eleven new modules at `cdf2c11e0` + `fb7099bc5` and
  checked `NativeRefinementTests` with paired `-M3G -H1G`: rc0, 21.28 s combined,
  empty warning gate. The isolated native/setup/trace importer checks and unchanged
  zero escape baseline are retained in the handoff; no uncontended timing is claimed.
  No arbitrary-network native FD full abstraction, zero-box/Skip correspondence,
  all-return-type network parallel theorem, UC/native-refinement identification,
  unseparated overlapping-Par or arbitrary-fan-in interchange, probability/PPT,
  fairness or CSP→PM/SSP bridge is supplied. Arbitrary-mask hiding is proved for
  strong ready simulation, not extensional raw-triple inclusion. The pinned
  library's broader weak/DR/FD limitations remain separate.
- **Local-negligible → vanishing family observation.** The checked
  [`negligible⇒vanishing`](../src/CategoricalCrypto/UC/Family/Negligible/Vanishing.agda#L70)
  uses `changeKernel` between the existing endpoints. `F`, `Φ` and `κ` are identity
  computational data; the consumer map leaves native test representatives unchanged.
  [`observationsᴺ⇒observationsω`](../src/CategoricalCrypto/UC/Family/Negligible/Vanishing.agda#L58)
  opens each closure's own negligible witness and applies `Negligible⇒→0` to that
  same function, inside its original test/closure/ancilla context.
  [`≈ᵁᴺ⇒≈ᵁω`](../src/CategoricalCrypto/UC/Family/Negligible/Vanishing.agda#L85)
  and [`≤UCᴺ⇒≤UCω`](../src/CategoricalCrypto/UC/Family/Negligible/Vanishing.agda#L88)
  preserve the original arrows, without grade stability or epi/mono assumptions.
  The UC function maps every source witness `le a = (s,h)` to `(s,h′)`;
  [`same-simulator`](../src/CategoricalCrypto/UC/Family/Negligible/Vanishing.agda#L94)
  proves its simulator-projection equality by `refl`, not just at the dummy adversary.
  The [native offset-family consumer](../src/CategoricalCrypto/UC/Family/Negligible/Tests.agda#L105)
  uses distinct rational readouts, context-dependent negligible witnesses and a
  nonidentity simulator. No global bound is selected or quantifier exchanged.
  The checked inverse-linear sequence separates scalar decay classes only; no
  endpoint UC-nonreflection theorem or PPT correspondence follows.
- **Symbolic / Dolev–Yao** (plan: [uc-setup-symbolic.md](uc-setup-symbolic.md); steps 3–9
  and static/conservative transmitting step 10 built: `Sym≅`, `Sym`, `fine→sym`,
  relational frame emitters, original `smt≤ideal` and `Interactive.smt≤ideal`).
  `𝔻𝕐` = free monoidal category generated by DY roles (token-passing programs whose
  outputs are recipes over their frame), hom-equality `_≈Term_`, observation evaluated in
  `𝔾ᵒ` at term alphabets with global freshness by located names, kernel = DY trace
  (may-testing) equivalence, tests with an ancilla as in `Machine/UC.agda`,
  `GradeStable` hypothesis-free (`grade-stable`).  Roles emit and store canonical forms of a
  convergent theory, so programs equal modulo E are kernel-equal (`emit-≈E`). The
  machine layer's relational spans imply generic `≈ₛ⇒≈ℰ` on frame emitters and E₀
  `≈ℰ⇔≈ₛ`; the multi-sort converse for admissible theories is not established.
  `EqTheory` requires sorted name-to-term substitution closure, excluding fresh-name
  collapse and the historical cross-sort obstruction (§3.2, §3.7 of the symbolic plan).
  Raw name identity and ownership still lack sorts. The original `smt≤ideal` retains
  its non-identity encryption-of-zero simulator for a fixed public message.
  Separately, the checked **[`Interactive.smt≤ideal : smt Sym.≤UC ideal`](../src/CategoricalCrypto/Symbolic/Example/SecureChannel/Security.agda#L117)** (source
  `5cd63401`, integrated `2d9741ef`) handles an environment-selected arbitrary
  plaintext, one fresh shared symmetric key and fresh encryption coins. The attacker
  sees ciphertext and controls conservative delivery/drop: the receiver decrypts and
  delivers only on return of the original ciphertext modulo E₀; a nonmatching return
  emits the error/drop outcome `cst 2`. Run-following relations lift the selected-message
  invariant through every syntactic `Sym` test and closure; an actual nonidentity
  ideal/simulator composition supplies the dummy witness.
  Public [acceptance/delivery/trace consumers](../src/CategoricalCrypto/Symbolic/Example/SecureChannel/Tests.agda#L95)
  and [`leaky≉real`/`leaky≉simulated`](../src/CategoricalCrypto/Symbolic/Example/SecureChannel/Negative.agda#L177)
  exercise this existing `Sym` setup. The negatives are observation-kernel separators,
  **not** impossibility against every UC simulator. Ordinary `Sym` execution remains
  total with explicit stopped/error clauses; absorption belongs only to the opt-in
  terminal runner. This is one-send conservative delivery/drop, not unrestricted
  chosen-ciphertext, multi-session, native applied-pi or computational security.
  **Corrections:** it is not "possibilistic next to
  `machine-iso`" (deterministic up to names). The formal relational interpretation
  `Symbolic/Machine.sym≅→iso` starts from coherence equality in `Sym≅`, not from `Sym`'s
  observational kernel; it deliberately forgets freshness. Unrestricted role execution
  `Computational/Run.Execution.Fᶜ η` lands in `𝔾ᵒ`. A **distinct certificate-bearing**
  `CertifiedSource.Sym≅ᶜ` has `fine→comp : UCSetupMorphism` into `ucSetupᴺ`; one emission
  per activation is not a universal query bound (`no-backwards-certificate`).
  [`Erasure.certified→fine`](../src/CategoricalCrypto/Symbolic/Erasure.agda#L65)
  is now a complete `UCSetupMorphism` from that certified source to ordinary `Sym≅`.
  Its free strong monoidal functor keeps object trees, role bodies and unit-free
  boundaries while erasing each generator's positive rate and query-bound certificate;
  its natural test map is `(Y,T) ↦ (FY,FT)`. The
  [rate-one verdict-forwarding consumer](../src/CategoricalCrypto/Symbolic/ErasureTests.agda#L63)
  exercises generator/composition/tensor erasure, test congruence and pullback naturality.
  No U/UC preservation/reflection or test-map epi/mono property is supplied for
  this erasure; its setup-morphism arrow has no security decoration.
  `Soundness.Derived.sound⁺` derives feasible indistinguishability from a context-uniform,
  one-system operational `Backtranslation`; that prerequisite has not been constructed
  from joint IND-CPA/INT-CTXT. `sound-≤UC` returns an explicit symbolic dummy simulator
  with feasible contextual agreement, not the target's canonical UC order. The exact
  deterministic trace lemma is not a correspondence with applied-π observational
  equivalence. Thus game-based soundness and full computational UC transfer remain
  unproved (`uc-setup-symbolic.md` §4.3); `ν Mono` gives reflection, not preservation.
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

This overview shows implemented setup-morphism existence only. In
`docs/uc-models.typ`, a double head means **UC preservation**, a hook **UC reflection**,
both mean both directions, and a plain arrow claims neither direction (not their falsity).
These decorations have no categorical mono/epi meaning and do not merely mean `ν.Mono`/`ν.Epi`.
ITM→PM, SSPᵈ→PM[wb], PMᴺ→PM^ω, full-CSP→trace-CSP and TaskPIOA→scheduled
NativeSSP preserve UC; none gets an unconditional reflection hook.
Certified→ordinary symbolic erasure is plain.

```text
Sym≅ᶜ ──erase──▶ Sym≅ ──coarse──▶ Sym
Sym≅ᶜ ──cs──▶ PMᴺ ──van──▶ PM^ω
Sym≅ ──sym≅──▶ Iso ◀── ITM(uninitialized)
ITM ──▶ PM ──▶ RS

W(full tests) ──▶ PM
      │
      ▼
W(restricted) ──▶ PM[wb]

       ╭──q──▶ SSPᵈ ──wbᵈ──╮
SSP ───┤                    ▼
       ╰──────wb────────▶ PM[wb]

ND_A(PM) ──▶ ND_B(PM) ──▶ PM
CSP(full observations) ──tr──▶ CSP(trace observations)
TaskPIOA(finite exact) ──native──▶ NativeSSP(scheduled)

Separate implemented node:
  Rel
```

The SSP triangle agrees pointwise in target hom/test equality, not by bundled
record equality. The checked finite-IPDL-API→SSPᵈ-resource and scheduled
TaskPIOA→SSPᵈ-protocol/consumer connections remain **operational**, not setup-
morphism or U/UC-transfer edges. TaskPIOA's new **black setup edge** targets the
distinct scheduled `NativeSSP.Setup.UC.StdSetup`, with constructive coverage and
U/UC preservation—not full SSPdist. CSP's setup edge changes observation; its
native ready refinement is a separate represented-fragment relation.
Native IPDL, RSIM and causal-box bridges remain proposals. The old raw `SSP → PM`,
`IPDL → RS` and `RS → causal boxes` candidates remain withdrawn; none is a universal
impossibility theorem.

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
5. **Symbolic**: formal `Sym≅ → machine-iso`, certified-source `Sym≅ᶜ → ucSetupᴺ`, and the
   derived `Backtranslation → sound⁺`; the game-based reduction and full UC transfer
   remain unavailable. The **robust compilation** lemma is independent of that reduction.
6. `machine-iso → protocol-rewrite` only after the three model changes of §2; IPDL and
   causal boxes as standalone setups when wanted — no morphisms are lost by deferring them.
