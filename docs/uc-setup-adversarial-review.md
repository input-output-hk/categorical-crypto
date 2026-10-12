# UC setup adversarial review

## Provenance and scope

This is the durable synthesis of the initial **16 read-only adversarial reports covering 15 baseline setup instances and the symbolic static/channel extension**, plus the completed computational-symbolic review and later checked dispositions. It records theory correspondence, source-derived semantic counterexamples, public-API coverage, and engineering observations separately. It is not a replacement model plan and does not change the implementations.

- **Baseline:** `4c9bf3e1eb4f841a26a6f9234a26a9116d6cac1e` (`4c9bf3e1`), the integration snapshot reviewed by the first 15 reviewers. Baseline findings are **UAR-001–UAR-036**.
- **Symbolic static/channel supplement:** `97bfae72a09be1390b609eee73103a8ff8789f6e` (`97bfae72`), reviewed separately by `ReviewSymStaticChannel`. Its additional findings are **UAR-037–UAR-039**. These sources were available in the extension worktree but were not present in the baseline integration tree when this document was written. Extension-only links are therefore commit-pinned repository links, not broken local links; publication of that commit to the remote has not been verified.
- **Computational-symbolic supplement:** `fd212866d1ca3ff663e23019a401c1112e5c3f44` (`fd212866`), the completed `SymbolicSoundness3` implementation reviewed by `ReviewSymbolicComputational` and its three supporting reviewers. The [completed assessment](#review-fd212866) preserves UAR-040 and adds the explicitly conditional, unformalized eligibility boundary UAR-041. It reviews exactly one new setup schema, `CertifiedSource sch .Sym≅ᶜ.StdSetup`, not another newly created target setup.
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

**Computational-symbolic review: completed at `fd212866`.** The [completed report](#review-fd212866) replaces the initial pending status. Its result is a qualified negative readiness assessment because of UAR-040, not a rejection of the conditional Agda implication or the certified interpretation. The malformed-projection boundary UAR-041 is source-derived and unformalized. The full game-based computational-soundness and target-UC correspondence remain unproved.

For subsequent reviews, append the reviewed commit, exact interpretation/admissibility assumptions, evidence class, affected setup/API boundary, counterexamples or positive evidence, and dispositions citing existing UAR IDs. Allocate subsequent IDs only for genuinely new findings; record overlap or narrowed/superseded scope without erasing the baseline. Compare later name, `Simple`, static, coupling, channel, resource and simulator claims against UAR-007–008, 028–033 and 037–041.

**Historical W-status superseded by checked dispositions.** UAR-016 and UAR-017 were source-derived OPEN constructions at the initial review. Their [later integrated disposition](#resolution-dc3f817e) records the checked comparisons and keeps their public-client limits separate. The baseline assessments above retain their original snapshot scope.

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

<a id="resolution-dc3f817e"></a>
## Checked integrated dispositions — dc3f817e

**Integrated snapshot:** `dc3f817ea4060295658747f4929037799654481d` (`dc3f817e`).
This append records completed implementation and integration evidence for the
specific slices below. It preserves the baseline findings, their original evidence
classes, and the static/channel supplement. In particular, the earlier
“implementation in progress” status for UAR-016–017 is historical: the comparison
theorems are now checked and integrated at this snapshot. No symbolic or PM-choice
finding is marked resolved by this entry.

The proof claims below are supported by the named implementors' completed reports
and Main's integrated checks, not by a new Agda invocation from the documentation
worker. **Checked** here distinguishes these new Agda results from the original
source-derived review witnesses; it does not broaden their theorem statements or
erase the remaining theory boundaries.

### Integrated provenance and verification

| Slice | Integration commit(s) | Disposition scope |
|---|---|---|
| Full-test W inclusion | `124ecf8833d6866241462e248501253f53ea1776` | UAR-017; positive full-test/PM clients in UAR-034. |
| SSPᵈ target examples | `5ae3c2d8a8cd4bb5c135f46ef6c00a2622150a96` | SSPᵈ row of UAR-034 and status drift in UAR-035. |
| Availability-qualified construction | `f2cfe47e5943ae56bcf99c8388520213afbc01e6`, `d744aed738d5b6d189578d2162d0fde6383acc9a` | UAR-002 at the compiled-resource boundary; RS acceptance/full-construction evidence in UAR-034. |
| W observation coarsening | `a30c4bd5d41a8d48d4729d5771f041a66cdca908`, `7a8f7a1dd9fd4c03c451ad1af4a3ff16578dcbab`, `0cdf781b83d09dca0ab19c7b9ebc71d8442db3b4` | UAR-016; positive restricted/coarsened clients in UAR-034. |
| Concrete positive-error QRS construction | `dc3f817ea4060295658747f4929037799654481d` | QRS nonzero-error client/sealing/composition/rejection gap in UAR-034. |

Main reported the following integrated checks through this snapshot:

- The actual SSP quotient OTP target leaf passed at `-M3G -H1G`, with an observed
  wall time of **16.70 s**.
- The combined W observation-restriction consumer and availability-example leaf
  checks passed at `-M3G -H1G`, **53.29 s** total.
- The QRS `Examples/FaultFlag/UC.agda` leaf first exhausted `-M3G` while rebuilding
  `UC.Model.Quantitative`; its `-M6G -H1G` retry passed in **27.76 s**.
- The integrated root first exhausted `-M6G` while rebuilding `UC.Model.Family`.
  After separately staging that dependency at `-M6G -H1G`, the staged
  Family/root run passed at `-M6G -H1G`, **84.18 s** total (parent job `bg206`).
  Main reports this as the successful full integrated closure through
  `dc3f817e`, with no warnings.
- The implementors' named warning gates were empty and their escape-hatch scans
  retained the existing **16** matches without growth. Main introduced no new
  source patch while performing these integrated checks.

The resource-limited attempts are recorded separately from the successful retries;
they are not type-error diagnoses or successful root checks. These times describe
the reported runs, not uncontended compute measurements, performance improvements,
or a promise that every cold root fits 3 GiB. The documentation worker did not rerun
Agda, these gates, or the reported failures.

### Construction and availability: UAR-002

**Disposition: the missing availability API and overbroad identification are
addressed at the explicitly compiled-resource boundary.** Existing `Constructs`
and `≤UC` remain security-only; their definitions and existing equivalences were
not silently changed.

[`UC.RandomSystems.Availability`][availability-api] now exports:

- `no-adversary a f`, obtained by applying the designated converter `a` to the
  adversary grade and removing the resulting unit interface;
- `Available a b f g` and `AvailableWithin ε a b f g`, comparing those closed
  honest resources behaviorally and at quantitative error `ε`;
- `SecureConstruction a b f g`, containing both security `f ≤UC g` and
  `Available a b f g`;
- `SecurelyConstructs εₛ εₐ a b f g`, containing both security
  `Constructs εₛ f g` and availability `AvailableWithin εₐ a b f g`;
- the qualitative/zero-error equivalences
  `Available⇔AvailableWithin₀` and `SecureConstruction⇔SecurelyConstructs₀`,
  plus introductions/projections and replacement-transitivity theorems.

The literal [Maurer Definition 3][m11] specialization requires **both**
`εₛ = εₐ = ε` and the **same** designated no-adversary converter
`a = b = ⊥` on the same Eve interface. Allowing distinct typed converters is an
explicit resource-specific-mode generalization, not an unnoticed identification
with the paper's literal statement. The honest protocol is already compiled into
the compared resource (`f = πR`); honest boundaries are fixed and Eve is represented
by one aggregate grade.

The former source-derived mode-bit witness is now a checked
[`Examples.RandomSystems.Availability`][availability-example] counterexample:
`mode-bit` and `bit-run` compute the designated honest readings; `security-only`
proves zero-error simulation with the forced-false converter, while
`not-available`, `not-full`, and `not-full₀` refute availability/full construction
under the designated true mode. Thus the distinction recorded in UAR-002 is now
exercised, rather than being removed by weakening the example.

`forced-true-full` and `forced-true-full₀` also give a nonidentity forced-true
simulator with the **same** `mode true` on both sides. `flipped-full`/
`flipped-full₀` exercise compatible distinct modes, and `twice-full`/
`twice-full₀` consume qualitative and additive-error composition, returning to
a shared designated mode. The APIs `secure-construction-trans` and
`securely-constructs-trans` require behavioral compatibility of the middle
designated converters; the examples prove that compatibility rather than assume it.

**Boundary retained:** this is replacement transitivity, not a newly proved
serial/parallel honest-protocol composition theorem for all of Maurer's TT1.
The records do not establish AB-converter syntax, initialized-state alignment,
normalized or terminating behavior, query bounds, or computational feasibility.
[UAR-001](#uar-001) therefore remains open. Neither the construction records nor
the checked examples justify treating a portless divergent simulator as inert.

### Full-test observation coarsening: UAR-016

**Disposition: the useful discovery is formalized and integrated; the forward
no-map claim is corrected.**

[`UC.Bracket.ObservationRestriction`][w-observation-restriction] supplies the exact
all-tests witness `verdict-W` and its sealed version `verdict-Wᵒ`. With invariant
`I s φ = ⊤`, the single verdict channel makes every output after either legal
`Opp` case admissible; `Supp-all` discharges the obligations. No monitor or
scheduler is inserted.

The module proves the verdict-interface inverse laws, `restrict-read`,
`restrict-cong`, and `restrict-natural`, then packages

```text
ν-restrict     : PresheafMorphism idF ι*ℰᵒ ℰᵂ
ν-restrict-epi : PresheafMorphism.Epi ν-restrict
restriction⇒wb : UCSetupMorphism Full.StdSetup 𝒲ᵂ.StdSetup
full⇒PM[wb]    : UCSetupMorphism Full.StdSetup UC.Bracket.Setup.StdSetup
```

Here `Full = Standard2.StdUC 𝒲ᴹ ι*ℰᵒ`, exactly the full-test source of `ι⇒prot`.
`restriction⇒wb` is `changeKernel` with the natural epi, and `full⇒PM[wb]`
is its composition with `q`. Shared computational structure and prefix contexts
give `full-≈ᵁ⇒wb-≈ᵁ`, `full-≤UC⇒wb-≤UC`, the corresponding PM[wb] results,
and the exact composed `full-preserves-≤UC`. No `GradeStable` premise is added.

**Boundary retained:** all-PM-test and W-closure setups remain distinct.
`full-test` repacks representatives; it is deliberately **not** a reverse setoid
map. This result gives neither security reflection nor a PM[wb]-to-ordinary-PM
bridge. Conditional safety and termination findings
[UAR-014](#uar-014)–[UAR-015](#uar-015), and nonuniform density
[UAR-018](#uar-018), are not resolved by this comparison theorem.

### Essentially-surjective full-test inclusion: UAR-017

**Disposition: the forward-security discovery is formalized and integrated;
PM grade instability does not block this particular route.**

[`UC.Bracket.InclusionTransfer`][w-inclusion-transfer] constructs `oneᵒ`, an
actual isomorphism in the sealed PM target between `ιᴹ (oneᴵ (objᵒ X))`
and each target object `X`, using the singleton-tag adding/removing wires and
both inverse laws. It exports:

```text
ι-essentially-surjective : EssentiallySurjective (StrongMonoidalFunctor.F ιᴹ)
ι-preserves-≈ℰ           : Transfer.Preserves-≈ℰ ι⇒prot
ι-preserves-≈ᵁ           : Transfer.Preserves-≈ᵁ ι⇒prot
ι-preserves-≤UC          : Transfer.Preserves-≤UC ι⇒prot
```

The proof uses `νι-epi`, the existing
`Standard2.Morphism.surjective⇒preserves-≈ᵁ`, and `Transfer.transfer⁺`.
It does not assume target grade stability or fullness.

**Boundary retained:** its source is exactly
`StdUC.StdSetup 𝒲ᴹ ι*ℰᵒ`, with all PM tests and closures, **not**
`𝒲ᵂ.StdSetup` or PM[wb]. There is no UC-reflection claim and no reversal
of the coarsening leg. Together with UAR-016, the proved comparisons form the
previously proposed **fork** from the full-test source; they do not make restricted
security a premise for ordinary-PM security.

### Public-target examples: partial disposition of UAR-034

**Disposition: several concrete target gaps are closed; UAR-034 as a whole remains
partially open.** The following replaces the indicated *current* coverage claims,
not the historical baseline table.

| Boundary | Newly checked public evidence | Scope still not supplied by this slice |
|---|---|---|
| RS / availability construction | [`HashForwardConsumer.hash-security` and `hash-rs`][availability-example] consume the existing inhabited-grade, three-state HashForward PM proof and transport it to `Constructs 0` and the actual RS setup. The same module provides full-construction positive and negative mode-bit examples described above. | No HashForward availability theorem is asserted. The availability/full-construction rejection is not a rejection of the original security-only `Constructs₀`—that relation deliberately holds for the counterexample. Do not count it as an independently exported RS security-only negative or a new behavioral-equality-versus-simulation separation. |
| QRS | [`Examples.FaultFlag.UC`][faultflag-uc] exports `first-security` at 1/4, `second-security` at 1/4, `composed-security` through `≤UCᴿ[]-trans`, `half-security`, `security-condition`, and `no-small-security` rejecting every bound below 1/2 for every sealed simulator. | Security-only replacement/construction chain, not availability, a parameterized computational family, query-budget transformation, or parallel-resource theorem. |
| SSPᵈ | [`otp≤ideal-dist`, `otp≤ideal-image-dist`, and `leaky-not-secure-dist`][otp-dist] are explicitly qualified at `SSPᵈ = SSP.Dist.Setup`. `otp-simulator-dist` fixes the actual simulator `a ∘ᵖ sim` for every adversary; `otp-observations-dist` quantifies every ancilla/distinguisher/game; `leaky-no-simulator-dist` quantifies every simulator. | The original `otp≤idealᵈ` remains explicitly a native `SSP.≤UC` theorem. The resource is still finite-rational, one-bit/one-message and passive/reliable as in UAR-012–013; no general sampler, adversarial delivery or corruption claim follows. |
| W / full PM tests and ordinary PM | [`Examples.SSP.OneTimePad.FullTests`][otp-fulltests] exports `otp≈real-full`, `otp≤real-full`, and the transported `otp≤real-PM`, using nontrivial probabilistic/stateful OTP **inlining**. `ideal-with-sim≤ideal-full` and `ideal-with-sim≤ideal-PM` use the actual compiled random simulator across different grades. | This is **not** full-context OTP confidentiality `compiled-otp Full.≤UC compiled-ideal`. `ideal-with-sim` is formed with the W category's actual action/tensor; no unproved full-test compilation tensor law or reverse use of PM[wb] confidentiality is assumed. Full-test negative/hostile-channel witnesses are still not supplied by this slice. |
| W / restricted closures and PM[wb] comparison | [`Examples.SSP.OneTimePad.ObservationRestriction`][otp-observation-restriction] consumes those exact full-test premises in `otp≤real-restricted`, `otp≤real-coarsened`, and `ideal-with-sim≤ideal-coarsened`. This is a direct positive source/composed-morphism client, not just a declaration of Epi/Mono. | It does not add a `q` security round-trip, a restricted-W negative, or the missing leaky-channel negative in PM[wb]. The pre-existing `otp≤idealᵂ` remains a genuine PM[wb] positive but is not an input to the full-test inclusion. |

The QRS example is not a weakened zero-error theorem. Its raw
[`FaultFlag`][faultflag] resources cache one initialized Boolean for their lifetime:
the real resource has true probability 1/2, the intermediate resource 1/4, and
the ideal always answers false. Both probabilistic initial laws have checked
mass exactly one at depth 2; repeated adaptive reads return the same bit rather
than amplify independent trials. `half-quarter-cache` and
`quarter-false-cache` prove the two quarter bounds uniformly over strategies
using finite cumulative-mass arithmetic.

Its simulator performs live tag translation (`latest → previous → original`);
the composed witness is the actual `simᵒ ∘ simᵒ`. Raw and composed simulator
transactions, and their zero-error nonidentity refutations, are proved.
`composed-simulator`/`composed-simulator-image` expose the witness.
`no-small-construction` and `no-small-security` reject **every rational
`ε < 1/2` and every simulator**, including partially initialized ones:
one honest read has real true mass 1/2 and simulated-ideal true mass zero.
The same simulator must precede all positive slacks and adaptive strategies.
New [`Composition` sealing bridges][rs-composition] (`procᵒ-≈ᴿ[]`,
`unprocᵒ-∼ᴿ[]`, `gradedᵒ-≈ᴿ[]`, `ungradedᵒ-∼ᴿ[]`), together with
[`procᵒ-unprocᵒ`][pm-seal], preserve epsilon and carry the rejection across
arbitrary sealed simulators, closing the baseline's concrete sealing seam.

For SSPᵈ, the negative transport now has the missing justification:
[`Dist.Setup.dist≈ᵁ⇒ssp≈ᵁ`, `dist≤⇒ssp≤`, and `reflects-≤UC`][ssp-dist-setup]
use `descendᵛ-mono` at every unchanged prefix and reflect the full security
quantification. Therefore `leaky-not-secure-dist` legitimately uses the native
probe contradiction; it is **not** inferred from positive preservation of a
negation. The same API also supplies preservation, `G≈id`, and
`ssp≤⇒dist≤`. Security reflection does not assert `≈ᵈ ⇒ ≈ᵖ`, an inverse
functor, or completeness of the stochastic-sampling proof principle.

### SSPᵈ documentation status: UAR-035

**Disposition: the status drift is corrected at the integrated snapshot.**
The [Typst model source](uc-models.typ), [SSPᵈ plan](uc-setup-ssp-dist.md),
[SSP plan](uc-setup-ssp.md), [example guide](examples-ssp-otp.md), and
[landscape](uc-setup-landscape.md) now distinguish the already existing quotient
from designed work and distinguish the native `otp≤idealᵈ` from actual target
`otp≤ideal-dist`. The formal quotient, bidirectional security comparison and
target examples are documented. This entry does not claim that Typst rendering
or PDF regeneration was exercised.

The original rejection of “SSPᵈ absent” remains correct: the setup existed at
`4c9bf3e1`; the new work supplies clients/comparison corollaries and corrects the
status text, rather than retrospectively making the baseline setup appear.

### Remaining review status after this integration

- UAR-002 is addressed only with the availability, converter, and compiled-resource
  qualifications above; UAR-001's initialization/normalization issue remains.
- UAR-016 and UAR-017 are now checked comparisons in the stated directions.
  UAR-014–015, UAR-018, the missing W negatives and reverse/reflection boundaries
  remain as stated.
- UAR-034 is partially superseded by the concrete RS/QRS/W/SSPᵈ evidence above.
  No unmentioned setup gains example coverage by association.
- UAR-035's documentation-status defect is addressed. SSP sampling, delivery,
  budget and primary-theory limitations remain.
- **No symbolic or PM-choice resolution is included in this snapshot-pinned
  disposition.** Candidate isolated reports do not by themselves establish
  integration. The computational-symbolic adversarial review remains pending;
  UAR-023 and UAR-028–033/037–039 are not marked resolved here.

<!-- Sources added by the checked integrated disposition. -->
[availability-api]: ../src/CategoricalCrypto/UC/RandomSystems/Availability.agda
[availability-example]: ../src/CategoricalCrypto/Examples/RandomSystems/Availability.agda
[w-inclusion-transfer]: ../src/CategoricalCrypto/UC/Bracket/InclusionTransfer.agda
[w-observation-restriction]: ../src/CategoricalCrypto/UC/Bracket/ObservationRestriction.agda
[otp-fulltests]: ../src/CategoricalCrypto/Examples/SSP/OneTimePad/FullTests.agda
[otp-observation-restriction]: ../src/CategoricalCrypto/Examples/SSP/OneTimePad/ObservationRestriction.agda
[faultflag]: ../src/CategoricalCrypto/Examples/FaultFlag.agda
[faultflag-uc]: ../src/CategoricalCrypto/Examples/FaultFlag/UC.agda

<a id="resolution-d898f3f0"></a>
## Checked symbolic contract dispositions — d898f3f0

**Integrated proof snapshot:** `d898f3f090d19c0add98b3d6c27a306dc3cd4909`
(`d898f3f0`). This snapshot integrates the previously reviewed static/relational
extension, the five assigned computational-interpretation/soundness commits,
and the two theory-contract commits. The original contract changes were
`8aac2ebb379fe26c601e499fb9abd541a46f0a11` and
`3d18e3570effcf2255549c051704ec611e64ee22`; the integration snapshot, rather
than those isolated commits alone, is the closure boundary for this disposition.
The static extension's formerly extension-only source files are now present in
integration; their old `97bfae72` citations remain historical provenance.

Main reports that the targeted `Symbolic/InterpretationTests.agda` check first
exhausted 5 GiB while rebuilding `UC.Model.Family`. Staging Family at
`-M6G -H1G`, followed by InterpretationTests at `-M5G -H1G`, passed in
**46.02 s** combined. The full integrated `CategoricalCrypto.agda` root then
passed at `-M6G -H1G` in **269.40 s** (parent job `bg221`), rebuilding the
static, `TheoryTests`, `InterpretationTests`, and affected existing clients,
with no warnings. The implementor's escape-hatch inventory remained the same
16 existing comment matches. These are attributed check observations, not new
documentation-worker Agda runs or uncontended performance claims.

### Fresh-name admissibility: UAR-028

**Disposition: checked resolution for the generic theory contract and its
literal-absence freshness consequences.** The existing [`EqTheory`][sym-term]
now requires sort-preserving name-to-term substitution congruence:

```text
Substitution = ∀ {s} → Name → Tm s
subst-cong : ∀ σ {s} {t u : Tm s}
           → t ≈E u → substᵗ σ t ≈E substᵗ σ u
```

This is a mandatory field of the supported theory, not an optional wrapper or
parallel weak interface. Uniform `ren-cong` and sort-indexed `renˢ-cong` are
derived from it. Per-sort `nontrivial` is retained. If `name n ≈E t` and `n`
does not occur in `t`, substituting either of two inequivalent same-sort witnesses
for `n` fixes `t` and would identify those witnesses. The derived `fresh-name`,
`name-injective`, and `distinct-names` make that reasoning available to clients.

[`Terms.recipe-names`][sym-term] and [`Deduction.⊬-fresh`][sym-deduction] connect this law to
recipes: a name absent from the exposed frame and not granted by `own` cannot be
deduced. [`Role.Run.emits≉fresh`][sym-role] applies the result to actual role
emissions using the received-frame and ownership hypotheses. The concrete
[`PairEnc.E₀`][sym-pairenc] proves the stronger substitution law with its existing
normalization relation; substitution preserves its rewrite steps, including
repeated decryption keys. No weaker cryptographic assumption is substituted for
the missing algebraic law.

The original counterexample is now explicitly exercised in
[`TheoryTests.Collapse`][symbolic-theory-tests]. The module proves the former
renaming-only fields separately, including nontriviality and canonical-form
support, without retaining an obsolete `EqTheory` record. `public-forgery`,
`owned-forgery`, and `guard-accepts-forgery` witness the old attack.
`collapse-not-subst-closed` and `collapse-not-EqTheory` show why that relation
cannot satisfy or represent the new admissible contract.
`TheoryTests.Supported` consumes E₀ deduction and `Role.Run.exec`: public
guesses and another occurrence's fresh name are rejected, same-name equality
still succeeds, and an actual fresh-emitting role consumes `emits≉fresh`.

**Boundary retained:** the theorem requires literal absence from the
exposed/received frame and lack of ownership. A key occurring inside a ciphertext
is not literally absent. This is not ciphertext confidentiality, an IND-CPA/
INT-CTXT reduction, or a quantitative guessing bound for a concrete nonce sampler.
`Role.Own κ` still grants every counter at occurrence `κ`, including counters
not yet allocated; the theorem protects an unseen name outside that conservative
ownership approximation, not every future counter of the same role.

### Stronger-class converse claim: UAR-038

**Disposition: the unsupported impossibility claim is withdrawn for the
substitution-closed class; the generic converse remains UNPROVED.**

The historical cross-sort shared-name rewrite is not closed under the mandatory
substitution above: occurrences of one raw code at distinct sorts may be sent to
different names. The old normalizer distinction therefore cannot establish
impossibility for admissible theories. The [symbolic plan](uc-setup-symbolic.md),
§3.7, and corresponding [model presentation](uc-models.typ) now state this
qualification instead of claiming the obstruction survives the stronger law.
The old multisort obstruction was a source-derived semantic argument, not an
Agda counterinstance; this disposition does not retroactively label it checked.

`EqTheory.renˢ-cong` supplies `Deduction.SortBlind` for every admissible theory.
The implemented converse is still the concrete
[`Static.PairEnc.≈ℰ⇔≈ₛ`][symbolic-static-pairenc] theorem at E₀.
Generalizing its tester and naming-recovery proof to arbitrary sorted signatures
has not been done. Neither **proved generally** nor **impossible generally** is
the correct status.

### Representation and channel limitations that remain

| Existing finding | Status after the strengthened contract |
|---|---|
| [UAR-029](#uar-029), names and ownership by raw code | **Unresolved, with a checked witness now available.** `TheoryTests.SortedOccurrences.free` is an admissible two-sort free theory; `split-first`/`split-second` exercise independent sorted substitution images and `owned-at-two-sorts` constructs recipes at both sorts from one raw ownership code. This is not a sorted-name representation migration. |
| [UAR-033](#uar-033), public versus restricted frame names | **Unchanged.** Private-frame APIs still do not carry an independent restriction list. The new freshness law does not make a public name occurring in a frame available to recipes excluded by `Foreign`. |
| [UAR-037](#uar-037), stochastic interface legs | **Unchanged.** The generic [`RelSim` API][symbolic-relsim-current] is still more general than a deterministic-projection coupling contract; checked pure-interface symbolic consumers do not resolve the generic qualification. |
| [UAR-039](#uar-039), factorized channel | **Unchanged.** [`SecureChannel`][symbolic-channel-current] still supplies independent ciphertext/honest emitters for a fixed public message, not a receiver decrypting an adversarially delivered ciphertext. Its uniform encryption-of-zero opacity result remains useful. |
| [UAR-030](#uar-030) and [UAR-031](#uar-031), `Simple` and operational correspondence | **Unchanged.** The theory repair does not strengthen the terminal-behavior predicate, add applied-pi races/replication, or prove a context/observational correspondence. |

### Formal interpretation status and the separate computational review

The checked [`sym≅→iso`][symbolic-machine] is a formal interpretation of fine
coherence equality; it deliberately forgets global freshness and initialization.
It is not preservation of the coarse `Sym` observation. The checked
[`CertifiedSource.Sym≅ᶜ.StdSetup` and `fine→comp`][symbolic-computational]
use a **distinct certificate-bearing syntactic source**. Its generators carry
unit-free boundaries, positive constant-rate schedules, and direct certificates
for the actual runtime at every parameter. This is an additional source setup
beyond the 15 baseline instances, not a retroactive renaming of unrestricted
`Sym≅`. Given a sort and an inhabitant of the scheme's `Bits` carrier,
[`no-backwards-certificate`][symbolic-obstruction] rejects direct certificates
at every natural rate for the backwards role, without claiming the stronger
obstruction for `QB`'s machine-equivalence closure.

The accompanying narrow correction in [uc-models.typ](uc-models.typ) moves these
interpretations out of the designed-only paragraph, makes their diagram arrows
solid, and gives the computational arrow its actual `Sym≅ᶜ` source. No
unconditional `Sym≅ → PMᴺ` arrow is asserted. These formal morphisms are not a
cryptographic reduction. [`Soundness.Derived`][symbolic-soundness] still requires
an operational `Backtranslation`; `sound-≤UC` returns a symbolic dummy witness
with feasible contextual agreement, not the target's canonical adversary-
quantified UC order.

The completed `ReviewSymbolicComputational` assessment of
`fd212866d1ca3ff663e23019a401c1112e5c3f44` is incorporated in the
[computational-symbolic supplement](#review-fd212866) below. Main identifies
those source proofs with the ones integrated here. Its adversarial evidence
remains separate from the green checks above: typechecking does not establish
theory correspondence or resolve the remaining cryptographic prerequisites.

[symbolic-theory-tests]: ../src/CategoricalCrypto/Symbolic/TheoryTests.agda
[symbolic-static-pairenc]: ../src/CategoricalCrypto/Symbolic/Static/PairEnc.agda
[symbolic-relsim-current]: ../src/CategoricalCrypto/Machines/Sim/Relational.agda
[symbolic-channel-current]: ../src/CategoricalCrypto/Symbolic/Example/SecureChannel.agda
[symbolic-machine]: ../src/CategoricalCrypto/Symbolic/Machine.agda
[symbolic-computational]: ../src/CategoricalCrypto/Symbolic/Computational.agda
[symbolic-obstruction]: ../src/CategoricalCrypto/Symbolic/Computational/Obstruction.agda
[symbolic-soundness]: ../src/CategoricalCrypto/Symbolic/Soundness.agda

<a id="pm-choice-leaf-disposition"></a>
## Checked PM-choice leaf disposition — 63b3d702 (isolated)

**Implementation evidence, not a new read-only-review claim.** The
`PMChoiceInitialization` implementor reports green source commits `06f9de06`,
`2fdb879c`, and `63b3d702`, based on the original `4c9bf3e1` baseline. The three
new modules are `ND/PM/Choice/Initialization.agda`,
`ND/PM/Choice/Initialization/Graded.agda`, and
`ND/PM/Choice/Initialization/Example.agda`. Their declarations were inspected
in the isolated implementation workspace. The implementor reports targeted
`pagda -M3G -H1G` checks passing, an empty warning gate, and the escape-hatch
baseline unchanged at 16. Its root-importer retry at 6G was still pending after
a 3G dependency-memory exhaustion when this evidence was received. This
paragraph does **not** report integrated-parent or completed root validation.

### UAR-023: formal counterexample and correctly delimited replacement law

The original unrestricted constant-pick claim remains false; its failure is
now expressed at the actual public PM `NDB` UC boundary, not only by an
operational sketch. `Example.half-initialization-≰UC-B` refutes emulation from
the half-initialized branch to its singleton choice, at grades `(I, [])` and
`(I, ⊤ ∷ [])`. The branch starts with mass 1/2 and returns true after activation.
`Graded.B-emulation⇒closed-resolver` extracts **one arbitrary resolver** from a
purported `NDB` emulation, using the public regrading equivalence, dummy
completeness, and `FullAbstraction.≈ᵁ⇒≈ᴿ`. The same resolver must match both the
zero-query and one-query strategies:

- Matching the branch's zero-query verdict forces resolver initial mass at most
  1/2 (`SameResolver.initial-mass≤½`).
- A successful activation still requires the chosen branch's independent
  half-initialization. The resulting true mass is at most 1/4
  (`activated-mass≤¼`), whereas the original branch has mass 1/2.

Thus the proof excludes every resolver, including partial, stateful ones. It
does not assume an inert simulator or select a different simulator for each
test.

The replacement `Graded.constant-pick-≤UC-B` requires an explicit selected
`s : S` and `Constant.TotalInitialization branches s`, defined as `ASTotal` of
**that selected branch's initialization**. The branches have no further choice
sites (`S → Proc⁺ [] A B`); no totality premise is imposed on unselected
branches, and the theorem does not require all later transitions to terminate.
It proves the public graded `NDB` emulation at `(I, [])` versus `(I, S ∷ [])`,
via `Constant.constant-pick-≈ᴿ`. This is the delimited repair, not restoration
of the unrestricted idempotence law.

### UAR-034: actual PM-B security and stateful closed-run coverage

`Example.stateful-≤UC-B` instantiates the positive theorem with a total Boolean
toggle branch. On input `a` and retained state `t`, it emits `a xor t` and
updates to `not t`. Starting from true, the two **distinct** activations false
then true both return true. `stateful-closed-run` checks the actual
`plugᴹ (constant-pick true)` execution; `stateful-observed-run` reaches the
closed `cupᵒ`/`playᵒ`/`Obs` boundary and observes their conjunction as true.
Reinitializing the branch before its second activation would instead make
that conjunction false. These are genuine positive/negative `NDB` clients and
a retained-state observation, improving the PM-B row of UAR-034.

This does not supply a PM-A negative, PM A/B non-reflection, arbitrary
sequential/tensor scheduling clients, or a repeated-request chooser. UAR-024,
UAR-025, and UAR-026 remain model boundaries; the original global-abort
observation in UAR-001 is not repaired.

**Subsequent isolated closure and partial integration.** The implementor's final
report includes docs commit `ff134350` and root-registration commit `226a4fbd`.
After the 3G root and first 6G root attempts exhausted dependency memory, the
documented `UC/Model/Family.agda` priming step passed at 6G, followed by the full
isolated root at 6G with an empty complete-output warning gate. These are
reported validation runs, not uncontended performance measurements. Main has
integrated the three source commits as `f07a63a8`, `0595cf6d`, and `e70c33c3`
and reports `Initialization/Example.agda` passing at `-M3G -H1G` in 14.63 s.
That is an affected-client check, not a parent root check. The docs/root-
registration commits and **parent integrated closure are still pending** at
this append. This updates the earlier pending isolated-root status without
conflating the two workspaces' checks.

<a id="review-fd212866"></a>
## Computational-symbolic adversarial findings — fd212866

**Reviewed source snapshot:** `fd212866d1ca3ff663e23019a401c1112e5c3f44`
(`fd212866`), the completed preserved workspace reviewed by
`ReviewSymbolicComputational` (GPT-6-Astra). Main identifies these source proofs
with those integrated through `d898f3f0`. Review evidence remains distinct from
the integration checks recorded above.

**Completed assessment:** the certificate-bearing setup and its formal
interpretation are appropriately scoped. The operational `Backtranslation`
contract nevertheless needs the uniform-error correction in UAR-040 before it
can serve the intended cryptographic development. The counterexample refutes
attainability of that premise under its stated conventional instantiation
assumptions, not the checked conditional implication.

There is **exactly one new setup schema**:
`CertifiedSource sch .Sym≅ᶜ.StdSetup`. `ucSetupᴺ` is an existing target;
`sym≅→iso` targets the existing relational-isomorphism setup; and
`Execution.Fᶜ`, `FeasibleComparison`, and `Backtranslation` are interpretations,
relations, or prerequisites, not further setup constructions needing another
setup assessment. The three supporting reports' full relevant evidence is
incorporated below. No Agda counterexample or execution check was run by these
read-only reviewers.

<a id="uar-040"></a>
### UAR-040 — One extraction error cannot be uniform over every honest circuit

**P1 · T, D · computational-symbolic operational prerequisite.**

[`Extraction.error` and `Extraction.realizes`][symbolic-soundness] choose
`error : ℕ → ℚ` and its negligibility proof **before** the honest circuit `f`.
The resulting bound must hold for every `SimpleC f`, without a shared bound on
circuit size, nonce draws, or runtime. Sharing the extracted context across
systems is useful; requiring this one error to work for every system is a
strictly stronger and generally unattainable requirement for the intended
cryptographic instantiation.

**Source-derived counterexample, not a new Agda theorem:** assume independent
uniform `η`-bit nonce sampling with injective tags, and a feasibility class
admitting the ordinary one-query verdict observer. Take a finite circuit with
`N` simple testers. Each draws two fresh names, tests equality, and reports
collision; a failing tester emits false and halts. A guard-free Boolean
aggregator reports whether any pair collided. These components satisfy the
actual `Simple` contract. Symbolically, fresh pairs are distinct, so every
such circuit is kernel-equal to an always-false circuit. The admitted fixed
one-query computational context instead observes true with probability

```text
1 - (1 - 2^(-η))^N .
```

The shared extracted contexts, exact `classifies` fields, and source kernel
equality force the sampled symbolic results to agree. The two `realizes`
bounds would therefore bound that real-world gap by `2 · error(η)`.
Because the record ranges over **every finite `N` at each `η`**, take
`N = 2^η`: the gap is at least 1/2, so `error(η) ≥ 1/4` for every `η`,
contradicting negligibility. This does not require one exponential-time honest
family to be admitted: each fixed-`N` circuit is finite and uses a constant
number of draws; the contradiction exploits the bound being uniform over all
of them simultaneously. Excluding all such one-query contexts would make the
intended cryptographic comparison weaker rather than repair the quantifier.

[Comon-Lundh–Cortier][clc08], Lemmas 24–25 (the
[archived text](kb/sources/papers/comonlundhcortier2008.txt), lines 2005–2150),
fixes the honest processes and uses process-dependent errors `ν₁,ν₂`.
The repository's own [`NegligibleBound` discussion][approximate-bounds] likewise
avoids a bound uniform over arbitrary budgets.

**Action:** keep context extraction shared, but index the approximation error
and its negligibility proof by the honest circuit or an explicitly fixed
admissible polynomial resource budget. Derive the final comparison with the
sum of the two applicable errors rather than necessarily twice one universal
error. State the relevant honest-system admissibility and feasible-context
quantifiers together.

**Still valid:** `Derived.sound⁺` is a genuine derivation from the current
strong `Backtranslation` hypothesis; no field simply assumes kernel
preservation, and the checked implication is not refuted. The issue is that
its operational prerequisite cannot be obtained from the intended finite-nonce
cryptographic assumptions at this uniform scope. No actual `Backtranslation`
instance or game-based reduction is thereby shown incorrect—none has been
constructed. Source: the completed `ReviewSymbolicComputational` assessment
and its previously published incremental finding.

**Disposition at this append: NOT FIXED in the reviewed integration snapshot.**
`ComputationalErrorResume` continues the error-contract repair; no checked
repair is recorded here. Likewise, the terminal-behavior overclaim remains the
existing UAR-030; its resumed implementation work is neither a new finding nor
a recorded resolution.

[approximate-bounds]: ../src/CategoricalCrypto/UC/Approximate.agda

### Supplementary public-boundary inventory

These are the implemented boundaries relevant to the computational review, not
four interchangeable computational-security theorems.

| Boundary | Actual source/target and evidence | What is not supplied |
|---|---|---|
| [`Machine.sym≅→iso`][symbolic-machine] | Unrestricted fine syntax to relational machine isomorphism; `InterpretationTests.relational-consumer` instantiates it at Σ₀/E₀. | Freshness or initial-state preservation, coarse observational-kernel preservation, or a tested Epi/Mono/UC-transfer result. |
| [`Computational.Run.Execution`][symbolic-runtime] | Every role executes as an actual PM process; `Fᶜ η` extends it freely at each parameter. Guards use concrete equality, `new` samples independently, and no symbolic normalizer runs on bitstrings. | A family query-bound certificate, correct equations, injective/disjoint tags, uniform nonce sampling, PPT, or a game-security assumption merely from the `Scheme` record. |
| [`CertifiedSource.fine→comp`][symbolic-computational] | The additional certificate-bearing `Sym≅ᶜ` source maps into `ucSetupᴺ`. `InterpretationTests.CertifiedForward` constructs a real forwarding generator and rate-one certificate for every scheme, pins its carried schedule, and consumes the backwards obstruction. | A certificate for every unrestricted role, a PPT source setup, or cryptographic soundness from the formal setup morphism. |
| [`FeasibleComparison` and `Derived`][symbolic-soundness] | Honest systems are raw PM families. An externally supplied `Feasible` predicate restricts QB-admissible family tests/closures; comparison quantifies each feasible context and all spectator families. `sound⁺` and `sound-≤UC` consume `Backtranslation`. | A constructed feasible cryptographic instance or attacker-extraction reduction, closure under arbitrary computational adversaries, or the target setup's canonical UC order. UAR-040 additionally challenges the current prerequisite's uniform error scope. |

The actual [`InterpretationTests`][symbolic-interpretation-tests] supplies
`normalized-kernel` and `normalized-UC` for an E₀ echo versus a projected-pair
echo. `ConditionalConsumer.normalized-output` and `normalized-dummy` consume
these proofs, but remain parameterized by `Backtranslation`; they are not an
instantiated confidentiality proof. The chosen symbolic dummy simulator is
retained explicitly, and its `SimpleC` proof is required separately.

The exact [`Deterministic.trace⇒bisim`][symbolic-deterministic] theorem uses
total deterministic Mealy transitions and literal equality of output lists
for every input list. Taking `Related = TraceEqual`, the head and tail of a
nonempty trace establish output agreement and closure of related states.
`ExactEcho.echo-determinate` is an actual role-transition consumer. This useful
proof is not the missing CLC/applied-pi correspondence involving static-equivalent
frames, contextual verdicts, or weak observational behavior.

The derived soundness proof is not a circular field assuming its own conclusion:
`classifies` handles one honest system at a time, `maybe-ext` recovers equality
of sampled `Maybe Bool` outcomes from both verdict classifications, and the
approximation bounds are then composed. Retaining `nothing` separately from
`just false` matters. UAR-040 concerns the quantification of those bounds,
not this conditional algebraic argument.

<a id="uar-041"></a>
### UAR-041 — Conventional projection errors need a source-eligibility contract

**P2 · T, D · conditional realization boundary, not an additional defect in the
stated conditional theorem.**

The current `SimpleC` restriction permits the ground guard
`π₁(c₀) = π₁(c₁)`. In E₀, projections of those distinct constants are distinct
irreducible terms, so the symbolic guard is false. Ordinary concrete parsing
can instead make the guard true: if the encodings of both constants are
malformed as pairs and projection returns the **same error value** on both,
their concrete projections compare equal.

**Explicit assumptions for this source-derived, unformalized witness:**
the two constant encodings are non-pairs; the concrete projection has that
common-error behavior; the two Boolean reply branches are concretely
distinguishable; the ground-guard role and its always-false reduction are
eligible under `SimpleC`; and `Feasible` admits the ordinary one-query observer
of that reply. Put true on the successful branch and false on a ground
failure/halt branch. Symbolic execution always takes the latter, while the
concrete guard takes the former. This gives a constant observation gap from
the always-false reduction. No concrete `Scheme`, observer, or Agda
counterexample for this pattern was constructed or checked in the review.

This is not an attack on encryption. Primitive security and correct projection
of *well-formed* pairs alone do not rule it out. A conventional realization
needs a well-formedness/error-aware eligibility contract, or symbolic error
semantics that matches concrete parsing, before claiming a backtranslation for
all admitted source circuits. The unrestricted `Scheme` interface and the
conditional implication never claim that such a realization exists. This
boundary is distinct from UAR-040's error quantifier and UAR-030's terminal
behavior; neither repair alone establishes this missing correspondence.

### Resource certificates and the test-map boundary

[`Certified c M`][symbolic-query-bound] is a direct potential certificate for
the actual state, initialization and transition of `M`. Its potential starts
at most at zero; a left/domain activation returning downwards requires a
strict potential decrease, whereas a right/codomain activation receives the
rate allowance. This measures interaction/query resources, **not** CPU time,
bit complexity, or distinguishing advantage.

`Generator` fixes one positive natural rate per role and supplies a direct
certificate at **every** parameter; the certificate proof may depend on that
parameter. `leafᶠ` installs a constant polynomial schedule and explicitly
consumes the proof through `certified⇒QB` and `qbᵒ`. The free interpretation
extends these generators to circuits. Family composition/tensor combine
schedules multiplicatively, while hom-equality forgets their annotations.
Thus rates are admissible upper bounds, not exact/minimal costs. Composite
homs carry `QB`; no direct certificate for every displayed composite runtime
is promised.

`QB c M` permits a machine-equivalent representative with a direct certificate,
so failure of `Certified c M` cannot silently be strengthened to failure of
`QB c M`. The inhabited backwards theorem is already sufficient to exclude
that role from this particular `Generator` interface. Its failure at parameter
zero contradicts the generator's universal certificate requirement.

The source test `(Y,T)` maps to `F(T)` closed with the query-certified
`deadᶠ (FY)`. Naturality under source pullback is a genuine forward test-map
law, **not** coverage of arbitrary target tests or an attacker backtranslation.
There is no test-map Epi or observational/UC-security preservation artifact.
The generic transfer route needs additional hypotheses, including test-map
Epi and target grade stability. No extra silent-drop or certificate-consumption
defect was found in the inspected codec/dispatch paths; that is read-only
inspection evidence, not an execution test.

### Feasibility, admitted schemes, and the exact conditional conclusion

The [existing local-negligible target][symbolic-local-negligible] and the
separate feasible raw-family comparison must not be merged. For a fixed pair
of honest systems, the latter has quantifier order
`∀ spectator W. ∀ feasible context c. ∃ negligible ε. ∀ η`.
The error may depend on that context and pair. It is neither one error uniform
over all contexts nor per-parameter unrelated witnesses. UAR-040 concerns the
stronger honest-system uniformity imposed by `Extraction`.

Family tests and closures are **QB-admissible** arrows, not necessarily direct
`Certified` witnesses for their displayed runtime. The extra `Feasible`
predicate is externally supplied; no current instance proves that it covers
all PPT attackers. With the empty predicate there are no context values,
`extract` can eliminate an impossible feasibility witness, and both premise
and conclusion are vacuous. The supporting backtranslation review initially
flagged this as a defect; the completed review classifies it instead as a
transparent conditional theorem's **instantiation/coverage limitation**, not
another implementation finding. A meaningful application must supply a
nonvacuous, adequately covering feasibility class.

A second **source-derived, unformalized** countermodel explains why arbitrary
`Scheme` values cannot imply backtranslation: take `Bits = Bool`, identity
tags, a nonce always returning false, `impl pair` always returning false and
`impl fst` always returning true. The source-equal echo/projected-pair example
then returns respectively false and true on input false. If `Feasible`
admits the finite reply observer, the gap is constant. This deliberately
equation-inconsistent interpretation is allowed by the bare interface; it is
not a cryptographic instance or a defect in the conditional theorem. UAR-041
is the stronger eligibility warning for otherwise conventional parsing.

`sound-≤UC` retains **one source dummy simulator before all** spectator/feasible
contexts, with a separate `SimpleC` obligation. It still lacks target-family
honest/simulator arrows and a feasibility-closure argument absorbing arbitrary
computational adversaries. It therefore does not establish
`∀ target adversary. ∃ target simulator` UC security. The normalized E₀ source
clients are substantive, but their computational consumers remain conditional
on an unconstructed `Backtranslation`. `ExactEcho` applies the exact-trace
theorem to one transition function compared with itself, not to a newly
proved nontrivial cross-system trace equivalence.

### Primary-theory correspondence: the bridges are not interchangeable

| Primary result | Actual scope | What this slice does not establish |
|---|---|---|
| [Abadi–Rogaway, Theorem 1][ar02-text], archived lines 757–812 | Acyclic expressions under type-0 secure encryption; formal expression equivalence implies indistinguishable ensembles. | This is passive expression-level soundness, not active UC. `Scheme` supplies no type-0 game, key-generation/correctness laws, length model or acyclicity evidence. |
| [Comon-Lundh–Cortier, Theorem 12][clc08], [archived text](kb/sources/papers/comonlundhcortier2008.txt), lines 1245–1248, 1303–1323, 2004–2155 | Restricted simple processes with key hierarchy and joint IND-CPA/INT-CTXT; applied-pi observational equivalence implies computational indistinguishability. Lemmas 15/19/24/25 use computation trees, concrete-attacker trace lifting and process-dependent errors. | E₀ shares the algebraic ingredients, but current verdict may-testing and `Role.Simple` have no checked translation to CLC's process class or equivalence. Exact traces/static equivalence alone are not the adaptive-attacker proof. |
| [Canetti–Herzog][canetti-herzog06], pp. 394–395 | Restricted simple public-key protocols using ideal certified encryption `Fcpke`; concrete traces map to valid DY traces with negligible failure. | No `Fcpke`, PKE/certification/session machinery, protocol translation or trace-mapping lemma is constructed. The operational `Backtranslation` record is not this mapping lemma. |
| [BPW, Theorem 7.1][bpw03-text], archived lines 1808–1811; [Böhl–Unruh][bu13], Definition 4.3 and Lemma 4.4 | A reactive cryptographic library/simulator for polynomial-time users and adversaries, and explicit symbolic simulation/UC quantifiers. | The required chosen-route primitives, reductions and arbitrary-adversary simulator are not supplied by a symbolic dummy with filtered contextual agreement. |

For a selected literature route, the missing prerequisites include concrete
primitive realization/correctness, tags and parsing, lengths and nonce
security; appropriate key hierarchy/acyclicity and one-use randomness
conditions; cryptographic games and attacker-extraction reductions; and a
checked correspondence between the role/may-testing semantics and the chosen
process/tree/frame semantics. CH/BPW routes require their additional library
primitives rather than merely the current symmetric-encryption syntax.
Nothing in the completed review treats these explicitly excluded results as
defects of the narrower formal declarations. No concrete `Scheme`,
nonvacuous `Backtranslation`, game reduction, or computational-UC
acceptance/rejection client was found.

### Completed-review provenance and documentation disposition

The completed assessment incorporates `ReviewCertifiedComp` (certificates,
actual test map, closure distinction and clients), `ReviewBacktranslation`
(exact quantifiers, independent proof content, vacuity and realization
countermodel), and `ReviewSymbolicLiterature` (primary-theory hypotheses and
documentation status). The final assessment controls their classification:
UAR-040 is the new contract defect; UAR-041 is a conditional eligibility
boundary; empty feasibility is a limitation; the terminal claim is carried
over as UAR-030. No old EqTheory-collapse finding is repeated.

The pinned `uc-models.typ` computational edge/designed-only inventory and
`README.md` computational-soundness headline were stale. The authorized
documentation correction now distinguishes the formal `Sym≅ → Iso` map,
the distinct certified `Sym≅ᶜ → ucSetupᴺ` map, and conditional raw-family
soundness. It does not upgrade either map to cryptographic security transfer.
The detailed symbolic plan's §4.2–4.3 and steps 11–13 already state these
boundaries. This documentation correction resolves the stale presentation,
**not UAR-030 or UAR-040**, whose implementation work remains separately
assigned and unverified here.

[symbolic-query-bound]: ../src/CategoricalCrypto/UC/QueryBound.agda
[symbolic-local-negligible]: ../src/CategoricalCrypto/UC/Family/Negligible/Setup.agda
[ar02-text]: kb/sources/papers/abadirogaway2002.txt
[bpw03-text]: kb/sources/papers/backes2003library.txt

[symbolic-runtime]: ../src/CategoricalCrypto/Symbolic/Computational/Run.agda
[symbolic-interpretation-tests]: ../src/CategoricalCrypto/Symbolic/InterpretationTests.agda
[symbolic-deterministic]: ../src/CategoricalCrypto/Symbolic/Soundness/Deterministic.agda

## Completed PM-choice integration and independent review — 2026-10-12

**PM initialization: integrated closure checked.** This supersedes the pending
parent status in the [isolated-leaf disposition](#pm-choice-leaf-disposition).
Main integrated source commits `f07a63a8`, `0595cf6d`, and `e70c33c3`, root
registrations `dafe925d`, and documentation `cf6653e6`: the original five-item
batch is now integrated. After the earlier `Initialization/Example.agda`
check at `-M3G -H1G` (14.63 s), Main reports the full
`CategoricalCrypto.agda` root passing at `-M6G -H1G` in **22.49 s**
(job `bg11`), with one `Checking` line and no warnings. These are attributed
execution observations, not fresh documentation-worker checks or uncontended
performance measurements.

The UAR-023 counterexample and selected-branch `ASTotal` correction are thus
checked through the actual `NDB` boundary and integrated root. The positive/
negative clients and stateful closed observation improve UAR-034 as described
above. No global initialization semantics changed; this does not resolve the
separate UAR-001 or PM-A/model-boundary qualifications.

**Independent source review: no new actionable findings at `d898f3f0`.**
`ReviewFixesResume` recovered the original integrated-fixes review and its four
completed supporting reports, then completed its read-only assessment of that
pinned snapshot. It found the availability/compatibility premises, quantitative
quarter-error composition and all-simulator lower bound, actual SSPᵈ reflection
client, separate W transfer routes, and strengthened symbolic freshness
contract consistent with their stated public boundaries. A shifted source-link
anchor suggestion was classified as a non-blocking documentation nit.
This is source/API inspection, **not execution validation**, and its earlier
snapshot does not independently review the subsequent PM initialization batch.
Known limitations and active follow-ups remain separate; neither this review
nor the green root silently resolves them.

## Checked pure-interface disposition: UAR-037 — 2026-10-12

**Disposition: the stochastic-interface loophole is closed by an enforced
purity contract.** The assigned `PureInterfacesResume` commit `0be796c3` is
integrated as `84b408c8`. The generic `≲[]` relation now requires purity of both
input and output interface legs; `HSim` and static consumers have migrated.
The trace theorem requires explicit purity of every projection it uses.
The static and E₀ theorem statements remain unchanged.

The checked fair-coin example exhibits the formerly admitted commuting
stochastic interface and proves that the strengthened contract excludes it.
Positive consumers still admit genuine nonidentity pure spans, including
projections from a shared random apex: the repair does not restrict relations
to identities or remove probabilistic state. Abstract `PureSub` supplies the
pure-square contract, **not a theorem that an arbitrary base is a probabilistic
coupling category**. The deterministic-subdistribution-pushforward reading is
restricted to `Kl(Dₚ)`.

Main reports `RelationalTests` passing at `-M3G -H1G` before a storage failure
prevented the next launch. After GC freed 7.7 GiB across 577 store paths,
`StaticTests` at `-M3G -H1G` and the integrated root at `-M6G -H1G` passed with
no warnings (job `bg53`, **111.49 s total**, including Nix downloads).
The implementor reports the escape-hatch baseline unchanged at 16.
These are attributed validation observations, **not a performance benchmark**
or new documentation-worker Agda runs. This resolves UAR-037's interface-purity
qualification; it does not resolve the separate channel-construction or
computational-soundness findings.

