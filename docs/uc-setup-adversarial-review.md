# UC setup adversarial review

## Provenance and scope

This is the durable synthesis of **16 read-only adversarial reports covering 15 setup instances**, plus the completed symbolic static/channel extension. It records theory correspondence, source-derived semantic counterexamples, public-API coverage, and engineering observations separately. It is not a replacement model plan and does not change the implementations or existing plans.

- **Baseline:** `4c9bf3e1eb4f841a26a6f9234a26a9116d6cac1e` (`4c9bf3e1`), the integration snapshot reviewed by the first 15 reviewers. Baseline findings are **UAR-001–UAR-036**.
- **Symbolic static/channel supplement:** `97bfae72a09be1390b609eee73103a8ff8789f6e` (`97bfae72`), reviewed separately by `ReviewSymStaticChannel`. Its additional findings are **UAR-037–UAR-039**. These sources were available in the extension worktree but were not present in the baseline integration tree when this document was written. Extension-only links are therefore commit-pinned repository links, not broken local links; publication of that commit to the remote has not been verified.
- **Computational-symbolic work:** `SymbolicSoundness3` is still running in isolation. No completed computational-symbolic adversarial report is included or implied. See the [append-only review status](#append-only-review-status).
- The starting local summary was checked against all 16 full reports and their recorded submissions. In particular, the incremental findings omitted from the final payloads of `ReviewQRS` and `ReviewWRestrictedTests` were recovered. Later follow-ups supersede earlier readiness verdicts without discarding their still-relevant technical evidence.
- The reviewers performed source/primary-literature inspection and mathematical derivations. **No new Agda counterexample was typechecked in these reviews.** This documentation task runs only the requested documentation smoke, not Agda, builds, or benchmarks. Existing checked declarations are inspected artifacts, not newly exercised verification.

A negative reviewer verdict means that the **whole-setup correspondence or claimed readiness needs qualification**. It does **not** mean that Agda is inconsistent, that a checked internal categorical theorem is false, or that every example using the setup is invalid. No report established such a contradiction.

### Evidence and priority legend

| Mark | Meaning | What it does not establish |
|---|---|---|
| **T — theory mismatch** | The implemented notion differs from a cited primary theory or a stronger advertised interpretation. | A false theorem about the implemented definitions. |
| **D — source-derived witness** | A concrete counterexample or useful construction derived from exported definitions/signatures; explicitly unformalized unless a later entry says otherwise. | A newly checked Agda lemma. |
| **C — coverage/API gap** | The reviewed snapshot lacks a concrete client at the actual setup boundary, or leaves a necessary bridge unexercised. | Nonexpressibility, a type error, or impossibility of supplying that client. |
| **E — engineering/documentation** | An inspected implementation property, status drift, API caveat, or static scaling observation. | An observed runtime regression or benchmark. |

**P1** means correct the security interpretation before relying on it. **P2** means a substantive model boundary, missing premise, useful comparison, or target-coverage obligation. **P3** means an engineering caveat without a demonstrated semantic failure. Deduplicated priorities take account of the strongest relevant report; they are not Agda-proof failure severities. Findings are **OPEN** as correspondence/coverage matters unless a later append explicitly records a resolution. Intentional restrictions remain valid restrictions, not automatically implementation bugs.

Stable IDs are permanent. Later work should append a dated, snapshot-pinned disposition citing an ID, rather than renumbering findings or erasing the baseline. A later theorem may supersede a finding's scope without changing what was true of the reviewed snapshot.

## Executive priorities

1. **Separate initialization and availability from simulation.** PM/RS/QRS and PM-based ND admit global initialization effects, including an unactivated portless simulator that aborts honest behavior ([UAR-001](#uar-001)). RS/QRS construction expresses the security clause, not Maurer's separate availability clause ([UAR-002](#uar-002)). These are independent problems.
2. **Do not identify relational ITM security with initialized execution security.** Initialization is forgotten, redundant state remains observable, and probabilities/termination mass disappear ([UAR-003](#uar-003)–[UAR-005](#uar-005)). Both ITM interpretations also lack silent deactivation/master reactivation and resource-bounded UC correspondence ([UAR-006](#uar-006)–[UAR-008](#uar-008)).
3. **Correct choice ownership and activation claims.** A's arbitrary payload functions can select a constant branch; SSP choice is preloaded FIFO consumption, not online scheduling; starvation can erase an already performed imported call ([UAR-019](#uar-019)–[UAR-022](#uar-022)). PM constant-pick refinement needs a total-initialization premise, and its public chooser is lifetime-once and fail-stop ([UAR-023](#uar-023)–[UAR-026](#uar-026)).
4. **Keep all three W setups distinct and retain the useful discoveries.** Conditional respectfulness is not hostile-input enforcement or liveness. The alleged no-map/no-transfer obstructions overlook a natural observation coarsening and an essentially-surjective inclusion ([UAR-014](#uar-014)–[UAR-017](#uar-017)). Both discoveries remain source-derived, not formalized results in this record; isolated implementations are in progress. Density is pointwise/cofinal, not uniform over tests ([UAR-018](#uar-018)).
5. **Qualify generic symbolic security and the new channel headline.** The generic equational interface permits fresh-name collapse; names/ownership are not sort-indexed; `Simple` does not express the cited terminal behavior; fixed token-passing circuits are not general applied-pi concurrency or indexed replication ([UAR-027](#uar-027)–[UAR-033](#uar-033)). The extension has a useful static-opacity result, but its factorized realization is not a transmitting/decrypting channel construction ([UAR-037](#uar-037)–[UAR-039](#uar-039)).
6. **Exercise the actual public targets.** Native SSP has meaningful positive/negative results, and PM[wb] has a genuine positive OTP transfer. Most other setup boundaries do not yet have both an acceptance and rejection client. In particular, `otp≤idealᵈ` currently proves original SSP security, not `Dist.Setup` security ([UAR-034](#uar-034)). **Reject the stale scout claim “SSPᵈ is absent”: its congruence and setup exist** ([UAR-035](#uar-035)).

## The 15 setup assessments

The setup name matters: a theorem in a neighbor, a build-closure import, or a generic transport declaration is not automatically an example of the named target.

| # | Setup and public boundary | Actual model and theory qualification | Existing useful evidence / remaining boundary |
|---|---|---|---|
| 1 | Probabilistic ITM — [`ITM.Setup.StdSetup`, `itm⇒prot`][itm-setup] | Finite tables on static signed bitstring-port trees, free monoidal syntax, perfect PM observations; always-reply activations and no PPT/family restriction. PM tests need not have source ITM realizers. | `runᵀᴹ-send`, codec round trips, free interpretation and identity test pullback are substantive. No actual ITM security client; PM grade stability cannot simply be assumed. UAR-006–009, 034. |
| 2 | Relational ITM — [`Rel.StdSetup`, `itm⇒iso`][itm-rel] | Unpointed existential halting transitions; whole-composite state isomorphism against arbitrary relational tests, not initialized traces. Probability is erased but representation state is retained. | Free interpretation and `νᴿ-epi`/`νᴿ-mono` support the stated structural comparison; `Iso.grade-stable` supplies a possible forward transfer premise. No public positive/negative relational-ITM client. UAR-003–006, 009, 034. |
| 3 | RS — [`RandomSystems.Setup`][rs-setup], [`Constructs`][rs-construction] | Adaptive behavioral quotient of globally initialized partial PM machines. It is not automatically a normalized reactive random system; construction is security-only. | Independent congruence/full-abstraction arguments and zero-error construction equivalences remain useful. HashForward has a source-derived transport route, but no actual RS acceptance/rejection pair. UAR-001–002, 034. |
| 4 | QRS — [`QSetupᴿ`, `≤UCᴿ[]⇔Constructs`][qrs] | Positive-slack-closed exact-epsilon emulation over the same quotient, with one simulator before all slacks/tests. All well-founded adaptive strategies, not a fixed query budget. | Endpoint closure, additive error and contextual/behavioral agreement are substantive. No nonzero-error target client; neither availability nor probabilistic termination follows. UAR-001–002, 010–011, 034. |
| 5 | SSP — [`SSP.Setup.StdSetup`][ssp-setup] | Stateful, finite-rational, well-founded, synchronous partial call/return protocols; unrestricted information-theoretic observation, not general samplers or resource-sensitive SSP. | `otp≤ideal` and `leaky-not-secure` are real public results. The resource is passive, reliable, one-bit, first-send-only; it does not cover adversarial delivery/drop. UAR-011–013, 034. |
| 6 | SSPᵈ — [`Dist.Setup.StdSetup`, `ssp⇒dist`][ssp-dist-setup] | The contextual quotient by `≈ᵈ`, with a joint-state distributional simulation proof principle fixed before all oracles. Same finite-rational call/return boundary. | Congruence, quotient, descended tests and stochastic OTP proof exist. The OTPᵈ client concludes native SSP security rather than target-qualified quotient security. UAR-034–035. |
| 7 | W / full PM tests — [`StdUC.StdSetup 𝒲ᴹ ι*ℰᵒ`, source of `ι⇒prot`][w-monoidal] | W-saturated arrows/adversaries/simulators with PM simulation hom-equality, but **all PM tests and closures**. W is conditional safety, not monitoring. | Compiled hom-equalities give a positive route; hostile wrong-channel replies separate admitted copycat and compiled wire. Natural coarsening and forward PM security transfer are source-derived discoveries, not yet checked additions. UAR-014–017, 034. |
| 8 | W / restricted closures — [`𝒲ᵂ.StdSetup`, source of `q`][w-setup] | Same W arrows and original hom-equality, observed only under W closures. Every verdict test can itself be given W because its output has one channel; the effective restriction is the closure class. | Test action and monitor-invisibility arguments are noncircular. No direct source-security client or exercised `q` round-trip; not ordinary-PM security. UAR-014–017, 034. |
| 9 | PM[wb] — [public quotient `StdSetup`, `q`][w-setup] | W category quotiented by the two-sided contextual kernel; arbitrary saturated partial W machines as simulators. Pointwise/cofinal SSP approximation. | Genuine [`otp≤idealᵂ`][otp-wb] through `SSP→PM[wb]`; no target-negative theorem. Stronger all-test-uniform approximation is false. UAR-015–018, 034. |
| 10 | Sym≅ — [`Fine`][sym-fine] | Free syntactic role-circuit emulation, without an execution or `EqTheory` parameter in its observation. A proof/interpretation IR, not observational DY security. | Coherence/occurrence machinery is useful; `fine→sym` preserves fine proofs but has no concrete security consumer. Generic runtime dependencies have the name and `Simple` issues below. UAR-027–030, 032, 034. |
| 11 | Sym — [`Symbolic.Setup.Sym`][sym-setup] | Deterministic fixed role-circuit token-passing may-testing over canonical terms; no general races, replication, or contextual-bisimulation identification. | `eval-cong`, grade stability, `≈ᵁ⇔≈ℰ`, `emit-≈E` and coarse interpretation remain meaningful. Baseline examples are echo/normalization, not confidentiality; the separate extension adds static/opacity results with UAR-037–039. UAR-028–034. |
| 12 | SSP ND A — [`NDA`, `relabel-≤UC`][nd-ssp-setup] | Environment-triggered FIFO picks after a simulator-selected partial-injective site routing with arbitrary payload functions. This is translated/refined choice, not literal preservation of environmental alternatives. | FIFO/starvation pins, branch permutation, commuting-counter law and copying non-reflection are substantive within this model. Not an unchanged-schedule multi-recipient proof or online scheduler. UAR-019–022, 034, 036. |
| 13 | SSP ND B — [`NDB`, `≤UC-B⇔≤UC`][nd-grade] via [SSP instance][nd-ssp-setup] | Full/essentially-surjective regrading of ambient SSP; not limited to the choice compiler image. Re-presentation adds no online activation power. | Real FIFO and copying witnesses, with distinct repeated-site indices and queues. Starvation is `dead`, not false or resumable pending; imported prefixes can disappear. UAR-020–022, 034, 036. |
| 14 | PM ND A — [`ND.PM.Setup.NDA`, `A⇒PM`][nd-pm-setup] | Partial stateless routing plus an unrestricted ordinary PM factor, whose eager initialization can globally abort even matched sites. All PM contexts permit adaptive public choices. | Generic factorization/regrading and sealed routing remain useful, but no concrete PM NDA security/refutation client or PM non-reflection theorem was found. UAR-001, 019, 023–024, 034. |
| 15 | PM ND B — [`NDB`, `≤UC-B⇔≤UC`][nd-grade] via [PM instance][nd-pm-setup] | Full regrading of exact unrestricted PM. Public `choose` requests once on first activation, initializes the selected branch lazily, then retains that branch for life. Invalid traffic globally aborts. | Local request/resume and transport pins exist; no closed scheduling/security client. Unrestricted constant-pick refinement is refuted by partial initialization. UAR-023, 025–026, 034. |

### Shared quantifier and transport boundaries

[`Abstract2._≤UC_`][abstract2] has the intended order

\[
  \forall\,\text{adversary}\;\exists\,\text{simulator}\;\forall\,\text{ancilla, test, closure}.
\]

A simulator is not chosen separately for each environment. In QRS, the same simulator also precedes every positive slack. Regrading A further fixes its ordinary factor `u` and routing/payload map `ρ` before all tests. These correct quantifiers make the two-test counterexample in UAR-023 decisive.

A setup morphism, Epi/Mono on tests, equality preservation, full abstraction, security preservation, and security reflection are different claims. The PM bare observation kernel is not generally grade-stable ([`FullAbstraction`][rs-full]); declaring an identity test pullback does not supply a missing ancilla theorem. Conversely, absence of target grade stability is not a universal no-transfer theorem: UAR-017 identifies an essentially-surjective route. Likewise, positive preservation alone never transports a negative security result to a target with more simulators.

## Detailed baseline findings

### Initialization and construction

<a id="uar-001"></a>
### UAR-001 — Global initialization can abort untouched honest interfaces

**P1 · T, D · RS, QRS, PM ND A/B and their shared PM base.**

[`runˢ`][machine-run] binds `MC.point` before inspecting even `out true`; [state tensor][machine-pointwise] eagerly pairs component initializations. Take two zero-port machines with the same impossible step and points `botₚ` and `returnₚ tt`. The zero-query strategy `out true` observes true mass 0 versus 1. More strongly, a scalar simulator `s : I ⇒ I` with divergent point makes `sub s ∘ g` have zero mass in every strategy even if `g` has no adversarial port and always serves its honest port. A dead real process can therefore satisfy zero-error construction/emulation of that ideal. In PM NDA, choose `u = s` and `ρ = idʳ`: all sites are matched, yet the ordinary factor suppresses their behavior without receiving a message. Portlessness does not imply inertness.

This is a source-derived consequence of the partial-initialization model, not a checked counterexample or a defect in the equality proofs. [Maurer 2002][m02], Definitions 2–3, assumes normalized random systems; [CryptHOL CC][ch19], §IV-A and footnote 1, starts from a state and requires probabilistic termination for its presented theorems. [Task-PIOA][task06] has a designated start state; [SUC][suc15], §2.2, activates the environment first.

**Action:** either supply admissible total-initialization simulator/resource classes and closure proofs, with appropriate complete-activation termination for the reactive specialization, or explicitly retain the globally initialized partial-mass semantics in every correspondence claim. **Still valid:** PM/RS/QRS equivalences for those actual partial machines and the generic ND factorization. Sources: `ReviewRS`, recovered `ReviewQRS`, `ReviewNDPMA`, `ReviewNDPMB`.

<a id="uar-002"></a>
### UAR-002 — Security-only construction omits availability

**P1 · T, D · RS/QRS; relevant to channel examples.**

[`Constructs`][rs-construction] and [`QUCᴿ.Witness`][q-witness] carry the simulator/security condition. [Maurer 2011][m11], §5.1 Definition 3 (PDF p. 16), separately requires the designated no-adversary/availability comparison. A real channel that never delivers passes the security condition using an ideal-world simulator that always deletes, but fails availability. Equivalently, let ideal `g` ask its adversary port which bit to return, let its no-adversary converter answer true, and let `s` answer false. Defining `f = sub s ∘ g` gives `Constructs 0 f g` by reflexivity, while the prescribed no-adversary executions differ with advantage 1.

**Action:** describe `≤UC⇔Constructs₀` and `≤UCᴿ[]⇔Constructs` as exact characterizations of the security clause, and require designated no-adversary converters plus availability in any full secure-construction predicate. This qualification is independent of UAR-001: even normalized resources can fail availability. **Still valid:** the substantive internal behavioral/contextual equivalences and their lifting through the simulator existential; neither exact epsilon nor zero error supplies the missing clause. Sources: `ReviewRS`, recovered `ReviewQRS`; see also `ReviewSSP`.

### Interactive Turing machines

<a id="uar-003"></a>
### UAR-003 — Relational ITM forgets the initialized execution

**P1 · T, D · relational ITM.**

[`leafᴿ`][itm-rel] retains all `Mem M` but does not use [`TM.start` or `blank`][itm-core]. [Machine isomorphism][machine-iso] has no initial-state condition. Use one finite table with two disjoint routines: append 0, send, and return to the first routine; append 1, send, and return to the second. Let `M` and `N` differ only in `start`. Their relational images have identical memory types and equivalent `Halts` relations, hence identity state isomorphism and equal tests in every prefix context; `Rel.≈ᵁ⇒≤UC` yields mutual emulation. An initialized one-query environment distinguishes their outputs perfectly, even possibilistically.

**Action:** use a pointed interpretation and initial-state-preserving comparison for execution fidelity, or explicitly call this an **unpointed transition-system interpretation**, not initialized ITM security. **Still valid:** the free functor and structural emulation on its declared target. The source witness is not newly typechecked. Primary comparison: [Hofheinz–Unruh–Müller-Quade][hum13], §2, pp. 13–14; [IITM][iitm20], §3.3, pp. 1475–1478. Source: `ReviewITMRel`.

<a id="uar-004"></a>
### UAR-004 — Relational observation detects representation, not just behavior

**P1 · T, D · relational ITM.**

[`Machine.UC` tests][machine-uc] compare the whole composite state by a bijection. A one-control-state TM can copy its input to the output buffer and send at the first blank, preserving its work tape. It behaves as a wire on every activation but has relational state `Fin 1 × Tape`; the syntactic wire has singleton state. A permitted singleton-state test with empty transition relation separates their composites by state cardinality despite neither producing a verdict. At unit grade, source simulators have inhabited state and cannot remove the redundant tape factor, so the wire cannot emulate this forwarder in the indicated direction.

**Action:** distinguish all-state contextual isomorphism from reachable/behavioral testing; a behavioral quotient and environment correspondence are additional work, not consequences of `νᴿ-epi`/`νᴿ-mono`. **Still valid:** the intentionally structural machine-iso category. Primary comparison: [IITM][iitm20], §4.3 Definition 9, and [HUM][hum13], §2. Source: `ReviewITMRel`; derivation, not a checked new lemma.

<a id="uar-005"></a>
### UAR-005 — Relational emulation erases probability and divergence mass

**P2 · T, D · relational ITM.**

[`toss` and `Halts`][itm-rel] keep possible finite branches without weights. Use common states `q,t,z,o,e`, with `t ↦ flip z o`, `z` appending 0 before `e`, `o` appending 1 before `e`, and `e` sending and returning to `q`. Let one table have `q ↦ flip z o`, the other `q ↦ flip t o`. Their possible output/next-memory pairs agree at every memory/input, but a one-query output-bit test has true probabilities 1/2 and 3/4. Similarly, with a sending state `s` and looping state `d`, direct send versus `flip s d` can have the same halting relation but termination masses 1 and 1/2.

**Action:** prohibit statistical/computational UC conclusions from this unweighted abstraction without an independent probability-preserving bridge. It is not a generally stronger sufficient condition for probabilistic security. **Still valid:** relational transition transport and its structural composition. Primary comparison: [IITM][iitm20], §§3.4–3.5 Definition 4; [HUM][hum13], §2 Definition 1. Source: `ReviewITMRel`; both witnesses are mathematical derivations.

<a id="uar-006"></a>
### UAR-006 — Both ITM interpretations omit silent deactivation and master control

**P2 · T, D · both ITM setups.**

[`TM` instructions][itm-core] are run/flip/send; [`runᵀᴹ`][itm-run] and relational `Halts` finish only at send. At `Gen unit (Var ⁻)`, the output type is empty, so no activation can return control. Yet a deterministic fixed-party polynomial-time ITM with an input and no output can halt its activation, after which the environment/master outputs true in [HUM][hum13], §2, pp. 13–14, and [IITM][iitm20], §3.3. Here the waiting context gets no true verdict. A machine that silently stores a bit, yields, and answers a later query likewise has no silent state-update transition. Sending an empty string is still an observable message, not deactivation.

The implemented fragment also has static wiring rather than built-in fresh-instance allocation, dynamic identities, corruption, or an adversarial scheduler resource. **Action:** retain the explicit always-reply, static-port boundary, or prove an execution-preserving yield/master-control encoding and hiding theorem before identifying this with Canetti/IITM or GNUC/iUC restrictions. A different test kernel or wide subcategory alone cannot add the missing transition. **Still valid:** finite-table execution and codec/functor laws for the supported instructions. Sources: `ReviewITMProb`, `ReviewITMRel`.

<a id="uar-007"></a>
### UAR-007 — Finite programs do not make ITM emulation computational UC

**P2 · T, D · probabilistic ITM.**

[`ITM.Setup`][itm-setup] has neither a security-parameter family nor admissibility/runtime predicates; [PM observation][pm-observation] compares exact verdict masses through every positive slack and discards finite runtime. For a family indexed by `n`, let the first response be true only if `n` fair flips are all true, then answer false forever. Against always-false, each fixed instance is rejected by the read-first-bit test with advantage `2^-n`, while the corresponding uniform one-shot-leak family has negligible distinguishing advantage. Conversely, being a finite program says nothing about the simulator's running time.

**Action:** classify this as perfect, unbounded emulation. Computational correspondence requires a uniform parameter interface, the source theory's validity quantifiers, negligible observation, and preservation of validity under composition. **Still valid:** exact finite-instance probabilities and the exported interpretation. The reviewed source really uses finite port/table domains; there is **no** arbitrary-alphabet or uncomputable-transition defect in `StdSetup` merely because the general helper `TM I O` is more general. Primary comparison: [HUM][hum13], Definitions 5–8, pp. 22–25; [IITM][iitm20], §§3.5–4. Source: `ReviewITMProb`; separation is source-derived.

<a id="uar-008"></a>
### UAR-008 — Pulled-back PM tests are not intrinsic computable ITM environments

**P2 · T, C · probabilistic ITM.**

[`ℰᵀ`][itm-setup] pulls back arbitrary [PM tests and closures][uc-core]. A test can send an empty query and return `χ w` for an arbitrary supplied `χ : Bits → Bool`, without a TM realizer or runtime bound. [IITM][iitm20], §4.3 Definitions 8–9, restricts environments differently. The identity test map being Epi/Mono and `≈ℰ⇔` agree with the same PM test class by construction; they do not establish density of computable source environments.

**Action:** define an intrinsic computable observation and prove the appropriate refinement/density or context theorem before asserting environment equivalence. **Still valid:** the PM-test pullback equivalence. No strict separation of perfect kernels from computable environments was established; this is an unresolved correspondence obligation, not a claimed noncomputability attack on finite-table source programs. Source: `ReviewITMProb`.

<a id="uar-009"></a>
### UAR-009 — The unrestricted ITM test-presheaf no-go has a degenerate counterexample

**P2 · D, E · comparison of ITM observations.**

The claim that no natural map out of the probabilistic test classes can respect relational equality is too broad. [Relational machines][machine-core] permit empty state. At every object choose `(I,E_A)` where `E_A` has state `⊥` and empty transitions, and map every source test to it. Restriction has state `(State(Fᴿ h) × ⊤) × ⊥`, canonically isomorphic to `⊥`; the map is congruent and natural. This defeats the unrestricted no-map claims in the [ITM plan](uc-setup-itm.md), §4.2, and [model presentation](uc-models.typ), not the absence of a useful observation-preserving bridge.

**Action:** state the desired nondegeneracy, observation preservation, Epi/Mono, or security-transfer properties in any impossibility theorem. **Still valid:** this constant map is not Epi/Mono and does not provide useful security transfer or recover erased probabilities. Source: `ReviewITMRel`; unformalized construction.

### Quantitative and SSP boundaries

<a id="uar-010"></a>
### UAR-010 — Boolean readout distance is not total variation including divergence

**P2 · T, D · QRS and shared partial-probability readings.**

[`Dp.Advantage`][dp-advantage] compares both Boolean singleton masses, with missing terminal mass representing divergence rather than conditioning on termination. It distinguishes `returnₚ false` from `botₚ` by distance 1. But terminal masses `(1/2,1/2)` and `(1/4,1/4)` are readout-close at 1/4 while their termination-event difference is 1/2. Calling this individual readout relation total variation on `Bool + divergence` is therefore incorrect.

This does **not** refute QRS security: the uniform [strategy][strategy] quantifier includes the same interaction with every terminating verdict replaced by true, which sees the 1/2 gap. **Action:** name the per-readout and all-strategy notions separately. **Still valid:** `ε₀ = 0`, positive-slack endpoint closure, lower-cut equality rather than exact finite-depth cofinal domination, and additive composition by splitting auxiliary slack; no endpoint loss or simulator/slack swap was found in [`QSetupᴿ`][qrs] and [rational approximation][approx-rational]. Source: recovered `ReviewQRS`; numerical examples are mathematical checks, not executed tests.

<a id="uar-011"></a>
### UAR-011 — Unrestricted advantage does not supply query/resource-sensitive SSP or RS

**P2 · T, D · SSP/QRS.**

[`_≈ᵍ[_]_`][ssp-reduction] uses one scalar epsilon for every unrestricted protocol test. [Brzuska et al.][ssp18], §2.3 Definition 8, instead admits an adversary-dependent advantage `ε_G(D)`. A game returning false forever and a game returning false on the first query and true on the second agree against all one-query adversaries, but the public unrestricted zero-error relation rejects them using a two-query adversary.

Similarly, [QRS absorption/composition][rs-composition] quantifies over all well-founded adaptive strategies and requires one uniform bound over all cutoffs. It does not prove an `asks≤` transformation or a reduction invocation bound `m_C(k)`, as needed to identify it with [Maurer 2002][m02], Definitions 9–10 and Lemma 5. The [SSP plan](uc-setup-ssp.md) itself leaves the rated-protocol ingredient open.

**Action:** expose adversary-indexed/budgeted bounds and their reduction transport before claiming PRF, birthday-bound, fixed-query, or computational correspondence. **Still valid:** unrestricted perfect/information-theoretic statements and exact-epsilon additive laws under their actual uniform premises. Sources: `ReviewSSP`, recovered `ReviewQRS`.

<a id="uar-012"></a>
### UAR-012 — SSP has a finite-rational closed sampling language

**P2 · T, D · SSP/SSPᵈ.**

[`Calls` and `coin`][ssp-protocol] are well-founded call trees with rational Boolean sampling. A closed activation evaluated by [`evalC`][ssp-observation] therefore has finite support and rational masses. A closed oracle sampling a geometric natural number, or returning true with probability `1/√2`, is not exactly representable. Moving that sampler behind an imported oracle does not fix the closed-game restriction, and compilation into a richer PM[wb] target does not enlarge the source.

Arbitrary finite sequential interaction is supported; recursive/reentrant activation, spontaneous output, and unbounded internal sampling are not. [SSProve][ssprove23], §§3.1–3.2, permits a more general parameterized sampling interface; [CryptHOL CC][ch19], §§II-A and IV-B, uses almost-surely terminating GPVs.

**Action:** expose the finite-rational partial call/return fragment as the completed contract, or supply a generalized sampler/evaluator and preservation bridge. **Still valid:** finite-key OTP and the present stochastic-simulation laws. Source: `ReviewSSP`, with `ReviewSSPDist` qualifications.

<a id="uar-013"></a>
### UAR-013 — Native OTP covers passive reliable delivery, not adversarial channel control

**P2 · T, C, D · SSP examples.**

[`OneTimePad.channel`][otp] lets Eve only read through `Pollᴵ`, and gives Bob the stored bit immediately after Alice's first send, independently of Eve. The trace `send(m); Bob.poll` returns `just m` before any Eve delivery. In the adversary-controlled channels of [CryptHOL CC][ch19], §§III–IV-A, it returns `None` until delivery; this example has no Eve drop command at all.

**Action:** keep the existing theorem scoped to a passive, reliable, one-bit, first-send-only channel. A stronger example needs explicit pending/delivered/dropped state, Eve commands, simulator preservation of those commands, and separate availability. **Still valid:** the native `otp≤ideal` proof, its fresh/pending/revealed invariant and fixed private uniform key, plus `leaky-not-secure` using two probes and simulator blindness. This is a legitimate no-deletion special case of [Maurer 2011][m11], §§3.2–3.3; it does not validate asynchronous scheduling ownership. Source: `ReviewSSP`, supported by `ReviewSSPDist`.

### The three well-bracketed setups

<a id="uar-014"></a>
### UAR-014 — W is conditional structural respectfulness, not hostile-context enforcement

**P2 · T, D · especially W with full PM tests.**

[`W.I-step`][w] requires an `Opp` proof. It imposes no obligation after an unsolicited return, wrong-channel return, or reentrant query. The inclusion and [tensor][w-tensor] do not install a monitor. With two unit query/reply channels, let a test query channel 0 and an unrestricted closure answer on channel 1. Admitted copycat forwards the answer and the test returns true; the also-admitted compiled `wireᵖ` aborts at [`Compile.reply`][ssp-compile] and [`Protocol.Machine`][protocol-machine], producing no verdict. Both have W witnesses.

**Action:** call the full-test source W-restricted arrows **under full PM testing**, not enforced SSP interaction. Use W closures for the conditional discipline or prove a separate enforcement construction with identity/tensor laws. In the restricted/quotient setups, an unsolicited ancillary return can likewise separate copycat and an idle compiled monitor in ordinary PM, while the attacking closure is excluded by W; this explains why restricted security is not ordinary-PM security. **Still valid:** conditional safety under legal input and the inspected routing/closure proofs. Primary comparison: [CryptHOL CC][ch19], §IV-B Definition 3 and §VI-A. Sources: `ReviewWFullTests`, `ReviewWRestrictedTests`.

<a id="uar-015"></a>
### UAR-015 — W does not imply successful initialization or eventual return

**P2 · T, D · all W setups and density's primary-theory interpretation.**

A machine with pure point and every step `botₚ` satisfies [`W`][w] using invariant `⊤` and `Supp-bot`. With divergent point, invariant `⊥` can make initialization and subsequent obligations vacuous even for arbitrary steps. An indefinitely calling converter is also allowed. Support checking is syntactic, including zero-weight branches before saturation; it is not a probability-one liveness theorem.

A test immediately returning true and one making one call before returning true agree on every terminating game in [Brzuska et al.][ssp18], Definition 1, but a diverging W closure separates them with masses 1 and 0. The implemented density theorem avoids this contradiction because its source includes abort-capable games, including cut games. [CryptHOL CC][ch19], footnote 1 and Definitions 1/3, assumes probabilistic termination and probability-one valid responses for the presented correspondence.

**Action:** call W a partial-response extension of respectfulness and state total-initialization/complete-activation termination hypotheses for the primary-theory slice. **Still valid:** observation distinguishes false from divergence, and monitor invisibility is not a claim of liveness. Sources: all three W reviewers.

<a id="uar-016"></a>
### UAR-016 — A natural full-test-to-W observation coarsening is available

**P2 · D, E · useful discovery; OPEN, not yet formalized here.**

The [model presentation](uc-models.typ) and [SSP plan](uc-setup-ssp.md), §4.2, claim no natural map `ι*ℰᵒ → ℰᵂ`. But [`Ωᴵ`][ssp-iface] has one channel. For every `t : Proc (flat A) (flat Ωᴵ)`, take invariant `I s φ = ⊤`: after a legal opponent move every possible output is a call or an answer on the unique channel. `Supp-all` supplies both W obligations. Thus every PM verdict test has a W witness after the [`ωʷ` verdict-interface respelling][w-setup].

The map `t ↦ ω⁻¹ ∘ t` is congruent by restricting equality from all PM closures to W closures, natural by associativity/precomposition closure, and componentwise surjective on test classes. It gives the missing observation-change leg into `𝒲ᵂ.StdSetup`, then `q` into PM[wb]. No monitor, termination premise, or new scheduling hypothesis is needed for this derivation.

**Action:** replace the unrestricted no-map/incomparability claim with the directional coarsening once formalized. **Still valid:** the reverse underlying-test inclusion need not respect equality; this does not establish Mono or security reflection. `WObservationCoarsening` is attempting an isolated implementation, but no checked result is recorded here. Sources: independent derivations by `ReviewWFullTests`, recovered `ReviewWRestrictedTests`, `ReviewPMWB`.

<a id="uar-017"></a>
### UAR-017 — Essential surjectivity gives a forward full-test inclusion route

**P2 · D, E · useful discovery; OPEN, not yet formalized here.**

For each PM object `X`, take [`oneᴵ (objᵒ X)`][ssp-iface]. Its flattened positive and negative types differ from `X` only by singleton tags. The stateless wires adding/removing `(tt,_)`, with [`wire∘wire`, `wire-cong`, `wire-id`][wire-algebra] and [`ifaceᵒ-onto`][pm-seal], give target-category inverse isomorphisms. Hence `ιᴹ` is essentially surjective even though not full.

Together with `νι-epi`, this supplies [`surjective⇒preserves-≈ᵁ`][standard-morphism], followed by [`Transfer.transfer⁺` / preservation of `≤UC`][abstract-morphism]. The source dummy simulator can be transported and composed with an arbitrary target adversary. Failure of PM grade stability therefore does **not** rule out this forward bridge.

**Action:** formalize the witness and corollary and correct “transports nothing more.” **Still valid:** non-fullness concerns reflection; no security reflection follows. This applies **only** to `StdUC.StdSetup 𝒲ᴹ ι*ℰᵒ`, not to `𝒲ᵂ.StdSetup` or PM[wb]. The resulting diagram is a **fork** from the full-test source to PM and to `𝒲ᵂ → PM[wb]`, not a path from restricted security to PM. `WInclusionSecurity` is attempting isolated implementation; no checked success is asserted. Sources: `ReviewWFullTests`, recovered independent confirmation from `ReviewWRestrictedTests`.

<a id="uar-018"></a>
### UAR-018 — SSP density is pointwise/cofinal, not uniform over all tests

**P2 · T, D · PM[wb] density.**

Take a stateless one-channel W closure that answers with probability 1/2 and otherwise repeats its delay node. It answers almost surely, but the depth-`n` [`cut`][ssp-cut] used by [`games-dense`][ssp-dense] answers each call with mass `1 - 2^-n`. A finite test making `k` calls then returning true has mass 1 against the original and `(1 - 2^-n)^k` against the cut. The discrepancy

\[
  1-(1-2^{-n})^k
\]

approaches 1 as `k` grows for every fixed `n`. Thus no cutoff gives a useful error bound uniformly over all tests, even with singleton query/reply alphabets.

The implemented argument chooses cofinal witnesses for each fixed finite-depth observation/support and takes finite maxima; it uses the same approximating game for the pair under comparison. A test-independent cut **family** is not test-uniform convergence. **Action:** replace uniform-error/runtime wording with those actual quantifiers. **Still valid:** qualitative density and positive SSP-to-PM[wb] equality/security transfer; no quantitative efficiency theorem is supplied. Source: `ReviewPMWB`; mathematical counterexample, no benchmark or new proof check.

### Nondeterministic choice

<a id="uar-019"></a>
### UAR-019 — A's arbitrary payload maps can select a constant ideal branch

**P1 · T, D · generic ND A; concrete SSP specialization, PM shared contract.**

[`Relabel`][nd-relabel] restricts site routes to partial injections but permits arbitrary payload functions. [`permute-≤UC`][nd-ssp-laws] accepts any `π`, not just a permutation. Set `S = Bool`, `A = unitᴵ`, `B = Ωᴵ`, `k p = ret (tt,p)`, and `π = const true`. A process consuming a pick and always returning true A-emulates the process returning its pick: the simulator maps every environmental pick to true, so the ideal false branch is unreachable even when the environment supplies false.

[`ND.A`][nd-a] characterizes emulation using existentially chosen `u` and `ρ` outside all tests. The actual notion is environment-triggered, simulator-translated deterministic payload refinement, not preservation of the environment's alternatives in both worlds. The site maps forbid fan-in/fan-out and may absorb unmatched inputs with the model's response behavior; those facts do not constrain a matched payload map to be invertible.

**Action:** use bijective payload maps or an ownership-preserving relation for choice equivalence, and expose arbitrary-map refinement separately. **Still valid:** the intended arbitrary-map preorder, generic regrading, and A-to-B preservation. [Task-PIOA][task06], Definition 2 and §5, has separate environment/schedule quantifiers, not this fixed relabeling semantics. Sources: `ReviewNDSSPA`, `ReviewNDSSPB`; PM shares the generic permission, alongside UAR-001.

<a id="uar-020"></a>
### UAR-020 — SSP choices require preloaded tokens and may be unsimulatable even when redundant

**P1 · T, D · SSP ND A/B.**

[`resolve`][nd-ssp-choice] turns a missing FIFO pick into terminal `dead`. Compare a site-free real process returning true with an ideal process that consumes a Boolean choice and returns true on either branch. A dummy simulator has type `Protocol C unitᴵ`, with no callable export. `sub s = s ⊗ᵖ wireᵖ` routes the honest query around it, so the ideal queue stays empty for every simulator. The immediate-query test gets real true mass 1 and ideal mass 0. Even a fixed predetermined ideal schedule cannot be supplied without activation. A same-declared-site version distinguishes `plain` from redundant token consumption when the test never calls the grade.

**Action:** state an externally activated preload/token-availability premise; otherwise retain pick-ahead FIFO semantics, not online adversarial request/response or idempotent nondeterministic choice. Starvation is neither false nor a resumable pending request; surplus tokens do not imply fairness/progress. [SUC][suc15], §§2.2 and 3.1, hands control to an adversary for pending communication; [Varacca–Winskel][vw06], §2.3, has idempotent offered choice `A ∪ A = A`; [Segala][segala95], §5.6.1, treats fairness separately.

**Still valid:** `≤UC-B⇔≤UC` is an equivalence with ambient SSP, not a scheduler adequacy theorem; B is not limited to the compiler image. Sources: `ReviewNDSSPA`, `ReviewNDSSPB`; source-derived witnesses.

<a id="uar-021"></a>
### UAR-021 — Starvation can erase a communication prefix from SSP observation

**P1 · T, D · SSP ND laws.**

[`call-choose` / `call-choose-ᵈ`][nd-ssp-dist] commute a call past an unanswered choice using `call-dead` on the empty queue. [`Dist.Kernel`][ssp-dist-kernel] discards the oracle state on `nothing`, and [`Observation`][ssp-observation] reads only the final return. Hence a prior imported interaction is forgotten when the continuation starves.

An unrestricted online environment could instead receive a report from the adversarial recipient of that first call and immediately output true without waiting for the protocol to return. In the choice-first world the call has not occurred, so the same environment separates the two orders. Such online adversary/environment interaction and environment-controlled termination are explicit in [SUC][suc15], §2.2, pp. 12–13.

**Action:** scope these laws to well-bracketed, return-observing contexts; general-UC use needs an interaction/prefix-observation bridge, not only a more adaptive scheduler. **Still valid:** the checked law for the defined SSP kernel and its `≈ᵈ⇒≈ᵁ` lifting. Source: `ReviewNDSSPB`; this does not claim that the internal Agda law is false.

<a id="uar-022"></a>
### UAR-022 — Branch permutation is not unchanged-schedule order independence

**P2 · T, D, C · SSP ND examples.**

[`Swap.order-indep`][nd-ssp-laws] works for arbitrary `t₀,t₁` because its simulator applies `not`. With `t₀ = ret (tt,true)` and `t₁ = ret (tt,false)`, mutual emulation still holds, but the same environment supplying true and querying distinguishes the unwrapped protocols perfectly. This is equivalence after alternative-label permutation, not commutation of observable execution orders.

[`Callee.either-order`][nd-ssp-laws] supplies the stronger equality for particular private counters returning `tt`; it does not establish “send to A, B, C in any order” for arbitrary observable recipient effects. [Task-PIOA][task06], §1, explicitly distinguishes essential delivery order from inessential scheduling.

**Action:** retain the branch-permutation theorem under that name and add a concrete multi-recipient example with a callee-specific unchanged-schedule commutation premise and an order-sensitive negative case. **Still valid:** the current counter example, FIFO pins and copying non-reflection witness. Sources: `ReviewNDSSPA`, `ReviewNDSSPB`.

<a id="uar-023"></a>
### UAR-023 — PM constant-pick refinement fails with partial branch initialization

**P1 · T, D · PM ND A/B and advertised A/B separation.**

[`choose`][nd-pm-choice] initializes its fresh wrapper totally, but initializes the selected branch only after the pick. Let site-free `p` have singleton state, initial surviving mass 1/2, and a total first ordinary step returning true. Compare `plain p` with `choose (λ (_ : ⊤) → p)` (or two identical `plain p` branches).

The zero-interaction strategy `out true` sees real mass 1/2, so any one simulator matching it must initialize with surviving mass 1/2. On the first ordinary activation the ideal additionally has to survive the independent deferred point of `p`, giving mass **at most 1/4**, whereas the real remains at **1/2**. The simulator has only the choice grade and cannot manufacture the ordinary output. [Full abstraction][rs-full] realizes both strategies as genuine PM observations, and the simulator must be the same for both.

**Action:** require total branch initialization for the advertised constant-pick/idempotence law and proposed PM non-reflection example, or align and justify the real/ideal lazy initialization semantics. Existing `Pin.branch` is total, but that does not validate the unrestricted `Proc` claim. **Still valid:** generic B regrading and local operational pins; no general refinement theorem was found and refuted after checking. Sources: `ReviewNDPMB`, `ReviewNDPMA`; this is an unformalized two-strategy refutation. Primary quantifier comparison: [SUC][suc15], §2.5 Definition 1; start-state comparison: [Task-PIOA][task06], §2.

<a id="uar-024"></a>
### UAR-024 — PM A exposes adaptive public choices, not oblivious task schedules

**P2 · T, D · PM ND A.**

[`ND.PM.Setup`][nd-pm-setup] retains every PM context. Let an environment sample a private fair bit `b`, activate [`Pin.one`][nd-pm-pin], receive its request, supply `b`, and check the returned bit. The check succeeds with probability 1; a pick fixed independently before that coin succeeds with probability 1/2. This uses public interaction, not another component's hidden state. Request occurrence, site identity, and control flow are observable too.

[Task-PIOA][task06], §1 and §2, instead uses static/oblivious residual task sequences independent of runtime information, separately quantified from environments. [SUC][suc15], §2.2, assigns adaptive delivery to an explicit adversary/router. **Action:** describe a distinct adaptive public-choice model, or supply restricted schedulers/tests and a correspondence theorem before invoking task-schedule independence. **Still valid:** A⇒B transfers between the implemented grade restrictions; it is not a literature-scheduler identification. Source: `ReviewNDPMA`.

<a id="uar-025"></a>
### UAR-025 — The PM chooser is a lifetime selector, not a reusable site request

**P2 · T, C, D · PM ND B public API.**

After a first pick, every [`choose` transition][nd-pm-choice] remains `active s t′`, and branch requests are shifted to the old-site tail. The newly allocated head site can never request again. `Pin.one` followed by activation/pick true returns true; another ordinary activation returns true without requesting a new pick. Sending false at the original site diverges (`no-repeat-pick`). Nesting/combining choosers allocates new sites rather than revisiting one.

**Action:** retain the explicit one-shot/lifetime contract and supply a site-indexed request/resume operation with persistent continuation/state if repeated scheduling is claimed. Demonstrate two visits to one site with different replies. **Still valid:** the ambient `Proc`/NDB model can encode such a scheduler manually, and `≤UC-B⇔≤UC` is unaffected; this is not a general nonexpressibility theorem. Repeated scheduling is part of [SUC][suc15], §2.2, and [Task-PIOA][task06], §2. Source: `ReviewNDPMB`.

<a id="uar-026"></a>
### UAR-026 — Invalid PM choice traffic kills the whole run, not just the request

**P2 · T, D · PM ND A/B.**

Early/repeated head-site picks and overlapping activation produce [`botₚ`][nd-pm-choice]. [`runˢ`][machine-run] binds the rest of the run to that result. Send an unsolicited left-site pick to [`Pin.parallel`][nd-pm-pin] before either component starts, then attempt a valid right-side activation: the first zero-mass step prevents the unrelated right component from answering in that run.

[SUC][suc15], §2.2, ignores invalid router delivery instructions and allows scheduling to continue; [Task-PIOA][task06], §2, imposes input enabling. **Action:** explicitly call this fail-stop partial interaction, not an ordinary scheduler no-op. Input-enabled correspondence needs a yield/acknowledgement layer and an interpretation theorem. **Still valid:** intentional rejection clauses and PM's one-answer continuation semantics. Source: `ReviewNDPMB`; not an accidental missing dispatcher case.

### Symbolic models

<a id="uar-027"></a>
### UAR-027 — Sym≅ observes circuit syntax rather than operational DY behavior

**P2 · T, D · fine symbolic setup.**

[`SameTerm` and `Fine`][sym-fine] compare full role-circuit syntax without `EqTheory` or execution. Let `p : void → verdict` constantly return true and `q : verdict → verdict` forward flags/ticks. `p` and `q ∘ p` execute alike, but every free monoidal congruence constructor preserves the number of `var` occurrences (one versus two). A syntactic test separates them. At unit grade, `UnitFree` prevents a unit-to-unit simulator from inserting generators to repair the dummy-adversary obligation.

**Action:** preserve the useful free syntax as a proof/interpretation IR, but call its relation syntactic emulation. [`fine→sym`][sym-setup] transports already proved fine security; it cannot turn coarse E-rewriting or confidentiality facts into fine proofs. **Still valid:** fine composition and interpretation into the operational setup. Primary comparison: [Böhl–Unruh][bu13], Definition 4.3. Source: `ReviewSymFine`; count argument is source-derived.

<a id="uar-028"></a>
### UAR-028 — Generic EqTheory permits fresh names to collapse to public data

**P1 · T, D · shared symbolic theory interface.**

[`EqTheory.ren-cong`][sym-term] only substitutes names by names. In one sort with distinct public constants `c0,c1`, canonicalize every `name n` to `c0`, keep both constants distinct, and define equality by canonical forms. Decidability, congruence under renaming, and nontriviality all hold. Every fresh secret is nevertheless E-equal to public `c0`; an attacker can satisfy its equality guard without receiving it. The alternative normalizer sending all names to one raw name, while leaving public constants distinct, likewise lets an attacker execute `new` to obtain an E-equal secret; `⊢-owned` plus conversion derives other occurrences' names.

Injective occurrence decoration separates raw supplies, not their E-classes. [Applied pi][applied18], §2.2, requires substitution of terms for names: substituting `c1` into `name n ≈E c0` rules out the first instance.

**Action:** add the intended sort-preserving term-substitution congruence, or explicitly restrict the theory class with appropriate name-separation laws. An injective-name premise alone should not be advertised as proving the whole applied-pi equational contract. **Still valid:** the concrete [`PairEnc.E₀`][sym-pairenc] is not this counterexample, and occurrence-bijection/fresh-allocation proofs are not refuted. Sources: `ReviewSymFine`, `ReviewSymCoarse`; see UAR-038 for the distinct extension claim about substitution.

<a id="uar-029"></a>
### UAR-029 — Name identity and ownership are not indexed by sort

**P2 · T, D · multisorted symbolic API.**

[`Name`][sym-term] is a pair of naturals and `name : Name → Tm s` is polymorphic in `s`. [`Recipe.mine`][sym-deduction] grants any sort from one proof of `own n`; name occurrence sets and `Foreign` erase sorts. An intended ownership set containing only `n : Key` therefore also permits `mine n p : Recipe [] own Nonce`. Restricting that raw code excludes it from both sorts. Static recipes may reuse the same raw name at different sorts even though separate `Role.new` operations cannot allocate that same raw pair twice.

**Action:** index names/ownership by sort or enforce a unique-sort/disjoint-encoding invariant through terms, renaming, frames, allocation and static tests. **Still valid:** no attack on single-sort E₀ was demonstrated; generic static recipes should not simply be assumed realizable by role tests. Primary comparison: [Applied pi][applied18], §2.1, pp. 4–6. Source: `ReviewSymCoarse`.

<a id="uar-030"></a>
### UAR-030 — Simple permits varying terminal output and is not enforced by the setup

**P2 · T, D · symbolic role restriction.**

A one-state [`Role`][sym-role] with empty registers may take that state as `halt`, forward each incoming flag `b` as flag `b`, and answer ticks with a fixed flag. Every reaction satisfies `Halts halt` (`GroundPayload flag _ = ⊤`) and `Guarded`, so this indefinitely responsive bit-forwarder satisfies `Simple`. Different failing guards may likewise emit different ground constants and leak which guard failed.

This does not enforce “answers every activation in the same way” or the fixed terminal `cout(⊥) · 0` behavior of [Comon-Lundh–Cortier][clc08], §3.3 (text lines 627–648). `Simple` is not consumed by `Fine.symData`, `runᴿ`, or the baseline examples.

**Action:** require uniform terminal emission and a semantics-preserving account of termination before using this predicate as the CLC restriction, or rename/qualify the weaker guard-failure property. Keep unrestricted DY attackers unrestricted. **Still valid:** no existing computational-soundness theorem is refuted by this baseline finding. Source: `ReviewSymFine`; witness unformalized.

<a id="uar-031"></a>
### UAR-031 — Coarse Sym is token-passing may-testing, not general symbolic UC

**P1 · T, D · coarse symbolic setup.**

[`Agree`][sym-setup] and [`eval`][sym-semantics] compare possible terminal verdicts against deterministic role circuits. [Böhl–Unruh][bu13], Definitions 2.4 and 4.3, instead use contextual observational bisimulation and reduction matching. The private applied-pi race

```text
νc.(c⟨0⟩ | c⟨1⟩ | c(x).a⟨x⟩)
```

can output either constant under the same unchanged environment. `Role.react`/`Run.exec` and the `returnₚ` interpretation at E₀ have no internal choice realizing that race. Fresh-name choice is not a scheduler; exposing scheduling as input changes the context/adversary interface.

**Action:** describe the fixed deterministic token-passing may-testing model, and require a translation plus context/equivalence theorem for general applied-pi or Böhl–Unruh identification. **Still valid:** `eval-cong`, ancilla-based grade stability, `≈ᵁ⇔≈ℰ`, same-shape `emit-≈E` and fine-to-coarse interpretation for the declared class. No verdict-canonicalization or separate-naming-witness counterexample was established. Source: `ReviewSymCoarse`.

<a id="uar-032"></a>
### UAR-032 — Unbounded indexed sessions need an actual state-routing construction

**P2 · T, C, D · both symbolic setups.**

A [`Role`][sym-role] has finite control, finitely many register sorts at each control point, and a finite reaction selected before frame evaluation; a circuit has finitely many roles. Terms can grow, so this is **not** merely a finite-state model. Nevertheless, for an admitted signature with only names and public constants and no non-nullary constructors, a fixed circuit can retain only finitely many unrelated received names. Its inaccessible fresh counter cannot reconstruct discarded inputs. It cannot implement arbitrary live sessions retaining independent received secrets and answering later SID-specific challenges in that signature.

Pairing-rich signatures might support an encoded table, but unbounded storage is not yet an implemented lookup/update mechanism. A single finite reaction has no unbounded internal lookup loop; a multi-role encoding and its behavior must be supplied. [Böhl–Unruh][bu13], Definition 5.11 and its implementation discussion, requires fresh independent instances and SID routing for `!!`.

**Action:** provide executable session machinery with explicit signature assumptions and composition/behavior proofs, or limit claims to fixed circuits. **Still valid:** this is not a nonexpressibility theorem for every pairing-rich role circuit. Sources: `ReviewSymFine`, `ReviewSymCoarse`.

<a id="uar-033"></a>
### UAR-033 — Static frames currently treat every occurring name as restricted

**P2 · T, D · generic static-frame applicability.**

With the free name-only theory, frames `{a/x}` and `{b/x}` for distinct **public** names `a,b`, with no restrictions, are distinguished by `x = a`. In [`_≈ₛ_`][sym-deduction], `Foreign` excludes all names appearing in either tuple, so `mine a` and `mine b` are unavailable and the remaining equality recipes agree. [Applied pi][applied18], Definitions 4.2–4.3, instead separately carries the restricted-name list in `νñ.σ` and excludes only those names.

**Action:** carry restrictions independently for general public-name frames, or explicitly expose a private-frame subclass and require public constants/input resources for public identities. `Knowledge`'s ownership parameter does not repair a tuple-only static-equivalence API. **Still valid:** the private fresh-name frame interpretation and native observations on it; the extension's theorem must be read at its stated generated-emitter boundary, not as arbitrary public-frame correspondence. Source: `ReviewSymCoarse`. The baseline had no static-emitter theorem; the later supplement below changes that coverage, not this historical fact.

### Coverage and engineering

<a id="uar-034"></a>
### UAR-034 — Public-target acceptance and rejection coverage is uneven

**P2 · C · all 15 setups, scoped to the pinned baseline.**

These are evidence-backed missing clients, not claims of type errors or impossible proofs. Source-traced routes below were **not newly elaborated** during review. Every row identifies the actual boundary rather than counting a neighboring theorem as coverage.

| Setup | What exists | Missing target exercise / recommended client |
|---|---|---|
| Probabilistic ITM | [`runᵀᴹ-send`][itm-run] and implementation/root closure imports. A source-derived true/false finite-table pair is separated by a PM reply-bit test, so tests are not globally vacuous. | Build `Gen → var → Fᴾ → observation → ≤UC` with a nontrivial simulator and an explicit negative. Exercise `itm⇒prot`/`≈ℰ⇔`; supply an ITM-specific ancilla/behavioral route rather than assuming false PM `GradeStable`. Negative-only interfaces may need an ancilla to relay observations. |
| Relational ITM | `leafᴿ → freeStrongMonoidal → StdUCMorphism`; no external use beyond root closure. [`Examples.RelSetup`][rel-example] is a different relation setup. | Formalize initialized-output, biased-coin/divergence and forwarder-state witnesses, plus a positive simulator. Exercise `Transfer.transfer itm⇒iso νᴿ-epi Iso.grade-stable`; this would not give probability preservation or a converse simulator translation. |
| RS | [`HashForward.real-≤UC`][hash-uc] in PM, with inhabited adversary grade and a three-state leak-fetching/hash simulator. | Transport through `≤UC⇒Constructs₀` and `Constructs₀⇒≤UCᴿ`, add a genuine rejection by a strategy and a behavioral equality not already source simulation. [`RegradeUnit`][regrade-example] is a PM kernel negative, not RS construction rejection. SSP/WB OTP still needs a PM/RS bridge. |
| QRS | Zero-error HashForward route via `Constructs⇒≤UCᴿ[]`; a source-derived zero-error non-vacuity route combines `reveal-≉ᵁ` and the full-abstraction/zero bridges. Only root imports consume the exact module externally. | Prove one-shot Bernoulli 1/2 versus 3/4 agreement at 1/4, reject smaller bounds, and compose errors with `≤UCᴿ[]-∙`. Start at raw machines and cross opaque `unhomᵒ`: existing [`Seal`][rs-seal] coercions visibly cover qualitative equality, not an exercised positive-error client. |
| SSP | [`otp≤ideal`, `leaky-not-secure`][otp], native positive and all-simulator negative. The positive uses explicit inlining/state invariants and dummy completeness; the negative compares real verdicts 1/0 with identical simulated-ideal verdicts. | Add active delivery/drop and separate availability (UAR-013), and resource-sensitive bounds if claimed (UAR-011). No blanket “no SSP examples” conclusion is justified. |
| SSPᵈ | [`otp≤idealᵈ`][otp-dist] uses `SSP.Dist.≈ᵈ⇒≈ᵁ` but imports **`SSP.Setup`**. It proves native SSP security with a new distributional principle. Native leaky impossibility is also SSP. | Import [`SSP.Dist.Setup`][ssp-dist-setup] and state target-qualified positive and negative corollaries, exercising `ssp⇒dist` and the appropriate preservation/reflection comparison. Do not rename the source theorem as quotient-target coverage. |
| W / full tests | Compiled hom-equality can use `morphism-W`, [`⟦⟧ᵂ-resp`][ssp-semantics], `≈C⇒≈ᵁ`, `≈ᵁ⇒≤UC`. No exact-source positive/negative security example was found. | Exercise compiled `wireᵖ-identityˡ`, the wrong-channel copycat/compiled-wire separation, and the inclusion's security bridge after UAR-017 is formalized. PM[wb] OTP does not discharge full-PM-context obligations. |
| W / restricted closures | Sound test action and monitor argument; no direct client of `q` or `𝒲ᵂ.StdSetup`. | State source-qualified security, exercise the `q` emulation round-trip without assuming grade stability, and give legal negative probes plus the ordinary-PM unsolicited-return separator. |
| PM[wb] | [`otp≤idealᵂ`][otp-wb] via [`SSP→PM[wb]`][ssp-dense-tests] is genuine target security. | Refute the compiled `aut ≤UC ideal` directly using compiled two-probe/flip-ideal readings, or prove suitable reflection. Positive transfer cannot negate a theorem over arbitrary saturated W simulators by considering only finite SSP simulators. |
| Sym≅ | Generic composition instantiated with assumed emulations; no caller of `fine→sym`/`coarse-epi` proving actual fine security. | Export a positive simulator and negative at the fine boundary, then exercise `Transfer fine→sym` with `coarse-epi` and coarse grade stability. Coarse confidentiality does not produce fine syntax equality. |
| Sym | [`Symbolic.Test`][sym-test] checks correct/wrong-key normalization, one-step encryption/deducibility and private echo/`π₁⟪x,x⟫` equality. The composed tester discards its challenge and returns true on every reply, so a different fresh responder still passes. | Export challenge-equality-guard acceptance and a bad/fresh-versus-replayed responder rejection at `SameObs`/`≈ᵁ`/`≤UC`, not merely deduction. [Canetti–Herzog][canetti-herzog06], §5, distinguishes these obligations. The extension adds a bridge and opacity example; UAR-037–039 qualify what that closes. |
| SSP ND A | FIFO scripts, `order-indep`, commuting-counter law, and [`Reflect`][nd-ssp-reflect] copying non-reflection. | Add observable multi-recipient unchanged-schedule commutation and an order-sensitive negative. Formalize redundant-choice starvation rather than treating it as conventional choice idempotence. |
| SSP ND B | [`Choice.Pin`][nd-ssp-pin] follows `veto ∘⁺ pick`, queues `[true,false]` and `[false,false]`, yielding true then false and final true mass 1. Feeding only the upper/veto site produces no Boolean verdict. Copying fills two ideal queues while every A one-real-site route leaves one empty. | Preserve these as preloaded-input witnesses; provide an activation/observation correspondence for online claims. Formalize the constant-versus-constant-choice starvation witness; do not replace it with another favorable preload script. |
| PM ND A | Only root external importer; generic `relabel-≤UC`, `≤UC⇒relabel`, `A⇒PM` and local operational pins. | A Boolean-pick permutation client needs the explicit grade insertion/unitor seam: compiler output is `C⟦S⃗⟧ ⊗ B`, while the public grade is `(I ⊗ C⟦S⃗⟧) ⊗ B`. Prove a positive through `A⇒PM` and a negative under the full U-kernel, handling ordinary scalars/initialization. No PM non-reflection follows from SSP copying or non-fullness alone. |
| PM ND B | [`two-compiled`, `parallel-compiled`][nd-pm-pin] instantiate transport equations; local first-request/resume and malformed-input pins exist. | Give independently specified closed sequential/tensor runs, out-of-order replies, correlations, activation-sensitive/state-updating branches, and a total-initialized constant-pick B positive/A negative. Use [`plugᴹ`][machine-dictionary] and observation/strategy APIs, then public NDB with explicit grades. Shape equations remain true even for a divergent process; the current stateless input-ignoring fixture cannot detect replayed input or lost updates. |

For SSPᵈ specifically, the stochastic OTP proof preserves the correlated pair `(c, c xor m)` and makes the exposed/polled ciphertext deterministic thereafter, rather than resampling it. A cached fair bit and freshly resampled bits are separated by a two-query equality test with probabilities 1 and 1/2. That source-derived sanity check supports the importance of the joint-state obligation, not a newly executed example. The sampling proof principle requires a total kernel on all source states (the example supplies a reachable `Phase` restriction); no completeness theorem from `≈ᵈ` back to a sampling witness is claimed.

<a id="uar-035"></a>
### UAR-035 — SSPᵈ exists; its “designed/absent” status is documentation drift

**P2 · E · SSPᵈ inventory.**

**Explicitly rejected:** the stale scout claim that SSPᵈ, its congruence, or its setup is absent. [`SSP.Dist`][ssp-dist] supplies `congᵈ` and observation respect; [`Standard2.UKernel`][u-kernel] supplies the two-sided contextual congruence; [`SSP.Dist.Setup`][ssp-dist-setup] defines `Protᵈ`, descended `ℰᵈ`, `StdSetup`, and `ssp⇒dist`. The quotient retains protocol/test representatives and descends equality rather than inventing a second semantics.

The [Typst presentation](uc-models.typ) still labels SSPᵈ designed at the baseline. **Action:** reconcile that status when model documentation is next updated; this review records the defect but does not edit the plan. **Still valid:** the implementation and joint-state proof principle. The real open issue is actual-target client coverage in UAR-034, not absent construction. Source: `ReviewSSPDist`.

<a id="uar-036"></a>
### UAR-036 — FIFO append has an unmeasured preload scaling caveat

**P3 · E · SSP ND implementation.**

[`Choice` enqueue][nd-ssp-choice] appends at the list tail. Repeatedly preloading `n` picks into one growing queue has a source-level quadratic aggregate list-traversal pattern. This is a static complexity observation, **not** a measured regression or a claim about whole-proof/build time.

**Action:** if long preload batches matter, assess the representation against that workload before making efficiency claims; do not infer resource preservation from regrading. **Still valid:** the FIFO semantics and queue/state equations. Sources: `ReviewNDSSPA`, `ReviewNDSSPB`; no benchmark was run.

## Completed symbolic static/channel supplement — 97bfae72

This supplement is already reviewed, not deferred to the pending computational-symbolic review. It adds a generic [`Static.≈ₛ⇒≈ℰ`][ext-static] emitter implication and an E₀-specific converse in [`Static.PairEnc`][ext-static-pairenc], supported by pure-map relational simulation through contexts, trace and the PM interpretation. The reviewer found no source-level failure in that pure-interface path, fresh-name transfer, or positive/negative tester routing. This narrows the baseline's “no static bridge” coverage statement; it does not establish a converse for every generic theory or unrestricted public-name frame.

<a id="uar-037"></a>
### UAR-037 — Generic stochastic interface legs do not give an ordinary coupling contract

**P2 · T, D · extension relational simulation API.**

[`Machines.Sim.Relational._≲[_∣_]_`][ext-relsim] requires purity of the **state** leg but not input/output legs. In the deployed Kleisli category those latter arrows may sample. Let `μ : ⊤ → Dₚ Bool` be a fair coin. `idᴹ-≲[] μ` is admitted; two copies give `RelSim μ μ μ μ idBool idBool` with apex `id⊤`. The apex's deterministic singleton output is not itself a joint endpoint-output distribution with deterministic marginal projections: its alphabet legs perform additional sampling.

This is a valid stochastic commuting square, not automatically the ordinary joint-distribution/marginal coupling described by [Barthe et al.][coupling17] (text lines 107–111). **Action:** require pure interface legs in the coupling-facing wrapper/record, or qualify the generic contract and restrict coupling language to pure-interface instances. **Still valid:** current symbolic consumers are insulated: [`UC.Machine.Relational.HSim`][ext-hsim] and [`Static.Same.apex≲`][ext-static-same] use `K.pureᵏ`, and `trace-relsim` explicitly requires pure output/loop maps. Source: `ReviewSymStaticChannel`; counterinstance derived from signatures, not freshly typechecked.

<a id="uar-038"></a>
### UAR-038 — The extension's multisort counterexample is only established for the weak theory law

**P2 · T, D, E · extension documentation; related to UAR-028–029.**

The [extension symbolic plan][ext-plan] claims its role/static converse counterexample survives substitution closure. The exhibited normalizer distinguishes

```text
open(seal(x,y), f(name n,name n)) = x
open(seal(x,y), f(name a,name b))   -- stuck when a ≠ b
```

For the current polymorphic-name presentation, arbitrary **sorted term substitution** can send `name {s₁} n` to `name {s₁} a` and `name {s₂} n` to `name {s₂} b`. Applying that substitution to the first equation forces the second term to equal `x`. Closing the theory under [Applied pi][applied18], §2.2's law therefore destroys the proposed distinction and lets independently allocated names open those tokens.

**Action:** remove/qualify the assertion of survival and state precisely the renaming-only assumptions under which the counterexample works. **Still valid:** the counterexample to an unrestricted converse under the **current weaker `EqTheory`** interface. This is not merely a repeat of missing substitution closure in UAR-028, nor a proof that adding that law alone solves every generic converse/name-sorting issue. Source: `ReviewSymStaticChannel`; mathematical derivation only.

<a id="uar-039"></a>
### UAR-039 — Factorized static opacity is not a transmission/decryption construction

**P2 · T, D, C · extension `SecureChannel` example.**

[`smt n`, `ideal n`, `smt≤ideal`][ext-channel] have the shapes

```text
smt n   = eₙ ⊗ honest n
ideal n = id ⊗ honest n
```

where `eₙ` emits `enc(n,k,r)` and `honest n` independently emits the fixed public constant `n`. For each `n`, choosing **`eₙ` itself** as simulator proves the factorized realization by tensor interchange, reflexivity and dummy completeness; no encryption property is needed. The same realization argument works if `eₙ` emits public plaintext. Thus `∀ n, smt n ≤UC ideal n` by itself does not test confidentiality or cryptographically enforce honest delivery.

The separately proved comparison to the **single encryption-of-zero simulator**, [`real≈simulated` and `smt≈simulated`][ext-channel], is nontrivial equality-only ciphertext opacity under E₀. Do not discard that result. But beyond the acknowledged fixed-public-message restriction, no receiving role consumes/decrypts attacker-supplied ciphertext and no adversarial delivery/acceptance condition determines the honest answer. [Böhl–Unruh][bu13], Definitions 8.5–8.6/Lemma 8.7 (text lines 7897–7905), makes Bob decrypt such ciphertext.

**Action:** present this as a two-port static-opacity example, not completion of plan step 10's intended secure-channel construction. A transmitting/decrypting role and its actual delivery/acceptance simulation are additional obligations. **Still valid:** `smt≤ideal` for the factorized resource and the stronger uniform encryption-of-zero opacity fact. Source: `ReviewSymStaticChannel`; no claim that the checked realization theorem is false.

## What remains valid, and code-quality caveats

The following positives are scoped source-review conclusions, not fresh validation or benchmarks.

- **Generic UC and interpretation reuse:** reviewers found the adversary/simulator/context quantifier order intact. Free-monoidal, standard-setup, quotient, regrading, observed-presheaf, approximation and witness machinery are reused rather than duplicated. Identity test pullbacks explain Epi/Mono without circular cryptographic premises, but do not prove correspondence to a different test class.
- **ITM implementation:** all inspected run/flip/send cases reach continue/finish branches, mirrored polarity codecs have both round trips, and free interpretation/seal transports are coherent. No independent routing/drop defect was found. Its intentionally missing transitions and relational information loss remain semantic limitations.
- **RS/QRS:** behavioral congruence and full abstraction are independent, not a circular assumption of security. Context absorption and the dual/cup/play realization make `≈ᵁᴿ[]⇔∼ᴿ[]` substantive; construction equivalence then lifts it through the same simulator existential. Errors and simulators are forwarded on inspected paths. Lower-real positive-slack closure preserves endpoints; no new negative-slack or additive-error defect was found.
- **SSP and SSPᵈ:** private state, adaptive state-threading, correctly tagged call/return and off-protocol rejection are explicit. Observation retains abort separately from false. Related-configuration proofs do not assume function extensionality. The distributional principle preserves the **joint** return/package/oracle state with one total kernel fixed before all oracles; bind, tensor and closed-run proofs retain correlations. `Coins` is total and oracle-blind: coin-drop/commutation cannot silently discard abort mass or oracle-correlated randomness. Deferred sampling still requires initial and every per-activation square, including queue state; it is not an arbitrary rewrite rule or complete relational proof system.
- **W:** no additional defect was found in initialization invariants, saturation, composition routing, tensor's four dispatch cases, coherence transport or inclusion. The two-sided kernel explicitly quantifies both left and right padding; it does not assume a bare-kernel/UC equivalence. [`Monitor`][w-monitor] consumes W in a reachable-configuration absorption proof before deriving `closures⇒∼`/`monitored⇒∼`, so the monitor argument is noncircular. Its conclusion is not hostile-input enforcement or liveness.
- **ND:** generic B inclusion is full/essentially surjective and the regrading equivalence does not assume PM grade stability. [Fujii–Katsumata–Melliès][fujii16], §2, supports graded pullback, not a scheduling adequacy theorem. SSP repeated Boolean site types remain distinct by sum-tagged indices and `splitQ`; no accidental sharing/duplication was found. The copying witness uses queue invariant `(q,q)` and exhausts the permitted one-site routes. The coin/choice law quantifies over every queue and does not reveal hidden coin outcomes to a scheduler. PM request/resume retains the triggering input, routes old requests/replies, and tensor retains the inactive component; independent pending choices and shared-adversary correlations are supported without exposing private states. Its compiler laws are legitimate isomorphism transports, not independent operational acceptance tests.
- **Symbolic:** free/decorated syntax and occurrence renaming are reused; inspected input-kind, reaction and occurrence cases showed no silent-drop defect. Generic raw freshness and concrete E₀ normalization remain meaningful within their contracts. The extension's pure-interface relational/static proof path survived source review; the stochastic-leg caveat does not by itself infect those pure consumers.
- **Performance and scope:** no reviewer measured proof time, runtime, memory, warning gates or escape-hatch changes. UAR-036 is only a source-level scaling observation. Earlier green imports or reported historical checks were not used as evidence of theory correspondence. Absence of a found dispatch defect is not a completeness proof of the implementation.

## Report-to-finding coverage index

The durable content is above; these session identifiers preserve provenance rather than requiring access to an ephemeral session to understand a finding. Recovered incremental/follow-up evidence is included where final payloads omitted it. An early “code-correct” verdict does not override a later whole-setup theory qualification.

| Report | Stable finding coverage and retained qualifications |
|---|---|
| `ReviewITMProb` | UAR-006–008, 034; finite source tables, codecs, no strict computable-kernel separation, bare-kernel versus security-transfer caveat. |
| `ReviewITMRel` | UAR-003–006, 009, 034; structural rather than behavioral interpretation and usable but unexercised iso-target transfer. |
| `ReviewRS` | UAR-001–002, 034; independent behavioral quotient and HashForward transport route. |
| `ReviewQRS` | UAR-001–002, 010–011, 034; **recovered incremental** global-scalar, availability and nonzero-error coverage findings; exact endpoint and simulator/slack quantifiers retained. |
| `ReviewSSP` | UAR-011–013, 034; meaningful native positive/negative OTP and finite-rational partial call/return scope. |
| `ReviewSSPDist` | UAR-034–035; joint-state/oracle correlations, total-kernel/all-state obligations, no sampling completeness, stale “absent” scout claim rejected. |
| `ReviewWFullTests` | UAR-014–017, 034; exact full-test source kept distinct from both W-observed setups. |
| `ReviewWRestrictedTests` | UAR-014–017, 034; **recovered incremental** source coverage and termination findings plus independent essential-surjectivity follow-up; fork direction retained. |
| `ReviewPMWB` | UAR-015–018, 034; genuine positive target transfer, nonuniform density witness and missing target negative. |
| `ReviewSymFine` | UAR-027–030, 032, 034; syntactic fine relation, operational restrictions, and absent fine-transfer consumer. |
| `ReviewSymCoarse` | UAR-028–029, 031–034; generic-theory, sorting, public-frame, race, session and weak-tester details. |
| `ReviewNDSSPA` | UAR-019–020, 022, 034, 036; latest theory verdict supersedes earlier narrow code-correct verdict; FIFO/copying positives and fairness boundaries retained. |
| `ReviewNDSSPB` | UAR-019–022, 034, 036; representational B equivalence, activation failure and prefix-loss distinction. |
| `ReviewNDPMA` | UAR-001, 019, 023–024, 034; scalar shutdown despite matched sites, public adaptive choices and grade-insertion seam. |
| `ReviewNDPMB` | UAR-023, 025–026, 034; lifetime choice, global fail-stop, partial-initialization refutation, independent closed-run coverage. |
| `ReviewSymStaticChannel` | UAR-037–039; pure-interface static positives, E₀-only converse, substitution qualification and factorized-versus-decrypting distinction. |

All 16 reports and their relevant history submissions were reachable. The ND review noted that a cited **Canetti 2020** primary text was not in the local archive; its scheduling comparison instead used the archived SUC 2015 source linked here. No claim in this synthesis depends on having inspected that unavailable 2020 text. The extension commit's remote publication was not checked; its report and source worktree were available.

## Primary references

These are archived primary sources, with the sections relied on by the reviews. The [paper index](kb/sources/papers/INDEX.md) and [bibliography](kb/refs.bib) provide full metadata.

- [Hofheinz–Unruh–Müller-Quade, *Polynomial runtime and composability*][hum13]: full ePrint version, §2 and Definitions 5–8.
- [Küsters–Tuengerthal–Rausch, *The IITM model*][iitm20]: §§3.1–3.5 and §4.3 Definitions 8–9.
- [Maurer, *Indistinguishability of random systems* (2002)][m02]: Definitions 2–3, 9–10 and Lemma 5.
- [Maurer, *Constructive cryptography* (2011)][m11]: §§3.2–3.3 and §5.1 Definition 3, including independent availability.
- [Lochbihler–Sefidgar–Basin–Maurer, *Formalizing constructive cryptography using CryptHOL*][ch19]: footnote 1; §§II-A, III, IV–VI; Definitions 1 and 3.
- [Brzuska et al., *State separation for code-based game-playing proofs*][ssp18]: Definitions 1, 3–8, especially adversary-dependent advantage.
- [Haselwarter et al., *SSProve*][ssprove23]: §§3.1–3.2, 4.1–4.2, 5.2–5.3; losslessness and state/result correlations.
- [Canetti–Cohen–Lindell, *A simpler variant of universally composable security*][suc15]: §§2.1–2.5 and §3.1; activation, router behavior and simulator quantifiers.
- [Canetti et al., *Task-structured probabilistic I/O automata*][task06]: §§1–2 and §5; start state, input enabling, environment/task-schedule distinction.
- [Varacca–Winskel, *Distributing probability over non-determinism*][vw06]: §2.3, offered-choice idempotence; [Segala's thesis][segala95], §5.6.1, fairness restrictions.
- [Fujii–Katsumata–Melliès, *Towards a formal theory of graded monads*][fujii16]: §2; categorical regrading background, not scheduler correspondence.
- [Backes–Pfitzmann–Waidner, *The reactive simulatability framework for asynchronous systems*][rsim07]: §1.6, asynchronous-model comparison.
- [Abadi–Blanchet–Fournet, *The applied pi calculus*][applied18]: §§2.1–2.3 and Definitions 4.2–4.3, sorted names/substitution and frames.
- [Böhl–Unruh, *Symbolic universal composability*][bu13]: Definitions 2.4, 4.3, 5.11, 8.5–8.6 and Lemma 8.7. The [text extract](kb/sources/papers/bohlunruh2013.txt) is useful where the PDF font encoding loses letters.
- [Comon-Lundh–Cortier, *Computational soundness of observational equivalence*][clc08]: §3.3, the simple-process terminal behavior.
- [Abadi–Cortier, *Deciding knowledge in security protocols under equational theories*][ac06]: recipe/deduction characterization; it is not by itself real/ideal security.
- [Canetti–Herzog, *Universally composable symbolic analysis of mutual authentication and key-exchange protocols*][canetti-herzog06]: §5, pp. 395–398, the distinction between deduction examples and simulation security.
- [Barthe et al., *Coupling proofs are probabilistic product programs*][coupling17]: joint distributions and marginal projections; also [text extract](kb/sources/papers/barthe2017.txt), lines 107–111.

## Append-only review status

**Computational-symbolic review: pending.** `SymbolicSoundness3` has not supplied a completed computational-symbolic result/review to this synthesis. The reviewed static/channel extension above is not that missing computational layer, and this document does not claim the overall symbolic correspondence complete. There are deliberately no placeholder “findings” or fabricated success entries for it.

When the computational-symbolic review becomes available, append its reviewed commit, exact interpretation/admissibility assumptions, evidence class, affected setup/API boundary, counterexamples or positive evidence, and dispositions that cite existing UAR IDs. Allocate subsequent IDs only for genuinely new findings; record overlap or narrowed/superseded scope without erasing the baseline. In particular, compare any eventual name, `Simple`, static, coupling, channel, resource and simulator claims against UAR-007–008, 028–033 and 037–039.

**Useful W discoveries: implementation in progress, not resolved here.** The isolated `WObservationCoarsening` and `WInclusionSecurity` efforts concern UAR-016 and UAR-017. Until their checked, integrated results are supplied, these remain source-derived OPEN constructions. A later disposition must separate the baseline documentation correction, newly checked comparison theorem, integrated importer/closure verification, and any still-missing public security client.

<!-- Baseline source links: repository-relative, named symbols at their uses above. -->
[abstract2]: ../src/CategoricalCrypto/Abstract2.agda
[abstract-morphism]: ../src/CategoricalCrypto/Abstract2/Morphism.agda
[standard-morphism]: ../src/CategoricalCrypto/Standard2/Morphism.agda
[u-kernel]: ../src/CategoricalCrypto/Standard2/UKernel.agda
[uc-core]: ../src/CategoricalCrypto/UC/Core.agda
[itm-core]: ../src/CategoricalCrypto/ITM/Core.agda
[itm-run]: ../src/CategoricalCrypto/ITM/Run.agda
[itm-setup]: ../src/CategoricalCrypto/ITM/Setup.agda
[itm-rel]: ../src/CategoricalCrypto/ITM/Relational.agda
[machine-core]: ../src/CategoricalCrypto/Machine/Core.agda
[machine-iso]: ../src/CategoricalCrypto/Machine/Iso.agda
[machine-uc]: ../src/CategoricalCrypto/Machine/UC.agda
[machine-run]: ../src/CategoricalCrypto/UC/Machine/Run.agda
[machine-pointwise]: ../src/CategoricalCrypto/Machines/Pointwise.agda
[machine-dictionary]: ../src/CategoricalCrypto/UC/Machine/Dictionary.agda
[pm-observation]: ../src/CategoricalCrypto/UC/Model/Observation.agda
[pm-seal]: ../src/CategoricalCrypto/UC/Model/Seal.agda
[rs-setup]: ../src/CategoricalCrypto/UC/RandomSystems/Setup.agda
[rs-construction]: ../src/CategoricalCrypto/UC/RandomSystems/Construction.agda
[rs-composition]: ../src/CategoricalCrypto/UC/RandomSystems/Composition.agda
[rs-full]: ../src/CategoricalCrypto/UC/RandomSystems/FullAbstraction.agda
[rs-seal]: ../src/CategoricalCrypto/UC/RandomSystems/Seal.agda
[qrs]: ../src/CategoricalCrypto/UC/RandomSystems/Quantitative.agda
[q-witness]: ../src/CategoricalCrypto/UC/Quantitative/Witness.agda
[dp-advantage]: ../src/ProbabilisticLogic/Dp/Advantage.agda
[approx-rational]: ../src/CategoricalCrypto/Approx/Rational.agda
[strategy]: ../src/CategoricalCrypto/Strategy.agda
[ssp-setup]: ../src/CategoricalCrypto/SSP/Setup.agda
[ssp-protocol]: ../src/CategoricalCrypto/SSP/Protocol.agda
[ssp-observation]: ../src/CategoricalCrypto/SSP/Observation.agda
[ssp-reduction]: ../src/CategoricalCrypto/SSP/Reduction.agda
[ssp-iface]: ../src/CategoricalCrypto/SSP/Iface.agda
[ssp-compile]: ../src/CategoricalCrypto/SSP/Compile.agda
[ssp-semantics]: ../src/CategoricalCrypto/SSP/Semantics.agda
[ssp-dist]: ../src/CategoricalCrypto/SSP/Dist.agda
[ssp-dist-kernel]: ../src/CategoricalCrypto/SSP/Dist/Kernel.agda
[ssp-dist-setup]: ../src/CategoricalCrypto/SSP/Dist/Setup.agda
[ssp-cut]: ../src/CategoricalCrypto/SSP/Cut.agda
[ssp-dense]: ../src/CategoricalCrypto/SSP/Dense.agda
[ssp-dense-tests]: ../src/CategoricalCrypto/SSP/Dense/Tests.agda
[protocol-machine]: ../src/CategoricalCrypto/Protocol/Machine.agda
[otp]: ../src/CategoricalCrypto/Examples/SSP/OneTimePad.agda
[otp-dist]: ../src/CategoricalCrypto/Examples/SSP/OneTimePad/Dist.agda
[otp-wb]: ../src/CategoricalCrypto/Examples/SSP/OneTimePad/WB.agda
[hash-uc]: ../src/CategoricalCrypto/Examples/HashForward/UC.agda
[regrade-example]: ../src/CategoricalCrypto/Examples/RegradeUnit.agda
[rel-example]: ../src/CategoricalCrypto/Examples/RelSetup.agda
[w]: ../src/CategoricalCrypto/UC/Bracket.agda
[w-setup]: ../src/CategoricalCrypto/UC/Bracket/Setup.agda
[w-monoidal]: ../src/CategoricalCrypto/UC/Bracket/Monoidal.agda
[w-monitor]: ../src/CategoricalCrypto/UC/Bracket/Monitor.agda
[w-tensor]: ../src/CategoricalCrypto/UC/Bracket/Tensor.agda
[wire-algebra]: ../src/CategoricalCrypto/UC/Machine/Wire/Algebra.agda
[nd-grade]: ../src/CategoricalCrypto/ND/Grade.agda
[nd-a]: ../src/CategoricalCrypto/ND/A.agda
[nd-relabel]: ../src/CategoricalCrypto/ND/Relabel.agda
[nd-ssp-setup]: ../src/CategoricalCrypto/ND/SSP/Setup.agda
[nd-ssp-choice]: ../src/CategoricalCrypto/ND/SSP/Choice.agda
[nd-ssp-dist]: ../src/CategoricalCrypto/ND/SSP/Choice/Dist.agda
[nd-ssp-laws]: ../src/CategoricalCrypto/ND/SSP/Laws.agda
[nd-ssp-pin]: ../src/CategoricalCrypto/ND/SSP/Choice/Pin.agda
[nd-ssp-reflect]: ../src/CategoricalCrypto/ND/SSP/Reflect.agda
[nd-pm-setup]: ../src/CategoricalCrypto/ND/PM/Setup.agda
[nd-pm-choice]: ../src/CategoricalCrypto/ND/PM/Choice.agda
[nd-pm-pin]: ../src/CategoricalCrypto/ND/PM/Choice/Pin.agda
[sym-term]: ../src/CategoricalCrypto/Symbolic/Term.agda
[sym-role]: ../src/CategoricalCrypto/Symbolic/Role.agda
[sym-deduction]: ../src/CategoricalCrypto/Symbolic/Deduction.agda
[sym-fine]: ../src/CategoricalCrypto/Symbolic/Fine.agda
[sym-setup]: ../src/CategoricalCrypto/Symbolic/Setup.agda
[sym-semantics]: ../src/CategoricalCrypto/Symbolic/Semantics.agda
[sym-test]: ../src/CategoricalCrypto/Symbolic/Test.agda
[sym-pairenc]: ../src/CategoricalCrypto/Symbolic/Term/PairEnc.agda

<!-- Extension-only source links: absent from baseline; pinned to the reviewed commit. -->
[ext-static]: https://github.com/input-output-hk/categorical-crypto/blob/97bfae72a09be1390b609eee73103a8ff8789f6e/src/CategoricalCrypto/Symbolic/Static.agda#L175-L177
[ext-static-pairenc]: https://github.com/input-output-hk/categorical-crypto/blob/97bfae72a09be1390b609eee73103a8ff8789f6e/src/CategoricalCrypto/Symbolic/Static/PairEnc.agda
[ext-relsim]: https://github.com/input-output-hk/categorical-crypto/blob/97bfae72a09be1390b609eee73103a8ff8789f6e/src/CategoricalCrypto/Machines/Sim/Relational.agda#L158-L196
[ext-hsim]: https://github.com/input-output-hk/categorical-crypto/blob/97bfae72a09be1390b609eee73103a8ff8789f6e/src/CategoricalCrypto/UC/Machine/Relational.agda
[ext-static-same]: https://github.com/input-output-hk/categorical-crypto/blob/97bfae72a09be1390b609eee73103a8ff8789f6e/src/CategoricalCrypto/Symbolic/Static/Same.agda
[ext-plan]: https://github.com/input-output-hk/categorical-crypto/blob/97bfae72a09be1390b609eee73103a8ff8789f6e/docs/uc-setup-symbolic.md#L481-L486
[ext-channel]: https://github.com/input-output-hk/categorical-crypto/blob/97bfae72a09be1390b609eee73103a8ff8789f6e/src/CategoricalCrypto/Symbolic/Example/SecureChannel.agda#L49-L114

<!-- Archived primary references. -->
[hum13]: kb/sources/papers/hofheinz2013-eprint-full.pdf
[iitm20]: kb/sources/papers/kusters2020iitm.pdf
[m02]: kb/sources/papers/maurer2002.pdf
[m11]: kb/sources/papers/maurer2011cc.pdf
[ch19]: kb/sources/papers/lochbihler2019cc.pdf
[ssp18]: kb/sources/papers/brzuska2018.pdf
[ssprove23]: kb/sources/papers/ssprove2023.pdf
[suc15]: kb/sources/papers/canetti2015suc.pdf
[task06]: kb/sources/papers/canetti2006taskpioa.pdf
[vw06]: kb/sources/papers/varacca2006.pdf
[segala95]: kb/sources/papers/segala1995.pdf
[fujii16]: kb/sources/papers/fujii2016.pdf
[rsim07]: kb/sources/papers/backes2007rsim.pdf
[applied18]: kb/sources/papers/abadi2018applied.pdf
[bu13]: kb/sources/papers/bohlunruh2013.pdf
[clc08]: kb/sources/papers/comonlundhcortier2008.pdf
[ac06]: kb/sources/papers/abadicortier2006.pdf
[canetti-herzog06]: kb/sources/papers/canettiherzog2006.pdf
[coupling17]: kb/sources/papers/barthe2017.pdf
