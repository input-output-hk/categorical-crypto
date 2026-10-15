# SSP up to distributions: `≈ᵈ`

Built 2026-10-10 on branch `ssp-dist` (`src/CategoricalCrypto/SSP/Dist*`, `--safe --without-K`): `≈ᶜ` compares
coins as syntax, so the one-time pad's deferred sampling is no simulation (landscape §0 finding 8).

## 1. The hom equality (`SSP/Dist.agda`)

`P ≈ᵈ P′` when, for all ancillas `Y Z`, every distinguisher `D` and game `G` read the same verdict
distribution in `Dist⊥ Bool` from one activation of `(D ∘ (id ⊗ P) ⊗ id) ∘ G`: a finite interaction,
the import answered by any game, i.e. any finite stateful rational strategy.  This is
`Standard2/UKernel`'s kernel of `ℰᵖ`, wrapped as a record at level `suc 0ℓ`: the **route is the
kernel one**, and `congᵈ : MonoidalCongruence Protᴹ`, `≈ᵈ-isEquivalence`, `≈ᵖ⇒≈ᵈ` (`≈ᶜ ⇒ ≈ᵈ`, as
`≈ᵖ` is the hom equality built on `≈ᶜ`) and `≈ᵈ⇒≈ᵁ` are its lemmas.  The ancillas let distinguisher
and game share oracles; `UKernel` absorbs a tensor's other factor into one.  Without them the readout
`≈ℰ` is not known to be a `⊗`-congruence.  Reading against oracles (§2) is the proof principle,
`⊑⇒≈ᵈ`; that every `≈ᵈ` has a `⊑` witness is not claimed, and that the oracle-kernel equality of
composite call trees is `≈ᵈ` is [INFERENCE] (games realize finite rational oracles, and a Boolean
threshold test separates two finite joint distributions).

## 2. Call trees as stochastic maps (`SSP/Dist/Kernel.agda`)

- An `Oracle A S` answers `A` from a state; `⟦ t ⟧ O s : Dist⊥ (X × S)` reads a call tree against it,
  and `t ≈ᵏ t′` when they agree against every oracle.  `P · O` serves `P`'s export from an oracle for
  its import; `⟦graft⟧`: grafting is serving.
- A **sampling simulation** `P ⊑ P′` is `ρ : St P → Dist-ℚ (St P′)` with `ρ (init P) ≈ return (init P′)`
  and, against every oracle, sampling then answering = answering then sampling (`Samples`):
  ssprove2023 Thm 2.4's stable invariant with a kernel for the relation, stated open so it composes.
  `sampling` builds one from per-activation squares of call trees, `ρ` a coin tree.
- `⊑-⊗ˡ`, `⊑-⊗ʳ`: tensoring with any protocol (the other factor commutes with `ρ`, `>>=ᴹ-comm⊥`);
  `⊑-run`: closed composites read out alike (`sample-⟦⟧`).  `⊑⇒≈ᵈ` pads by wires and reads out.

### 2.1 Exact finite rational sampling and the native TaskPIOA consumer (2026-10-15)

[`SSP.Dist.Sampling.rationalCoins`](../src/CategoricalCrypto/SSP/Dist/Sampling.agda#L102)
compiles every finite normalized nonnegative rational distribution into a finite coin tree;
[`rationalCoins-correct`](../src/CategoricalCrypto/SSP/Dist/Sampling.agda#L105)
proves equality of the sampled distribution. The primitive `coin` accepts rational Boolean
distributions, not only fair coins, so non-dyadic weights are represented exactly.

The checked [`TaskPIOA.SSPAdapter`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L47)
is a substantive operational consumer of this sampler and the existing `Samples/sample-⟦⟧`
interface. Its actual tick protocol samples the **joint** native next-state/optional-output
law; a disabled task returns successful stutter, not `dead`. `native-samples` and
[`all-calls-agreement`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L150)
give adequacy for every finite reply-adaptive/partial tick call tree.
[`run-agreement`/`reward-agreement`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L183)
cover all finite native words, all initial states and arbitrary rational trace rewards.
[`experiment-agreement`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L262)
uses actual composed SSP resources/consumers, while an independently defined receive-aware
[`Synchronized`](../src/CategoricalCrypto/TaskPIOA/SSPAdapter.agda#L275)
protocol proves native joint-product/schedule compatibility, not ordinary SSP-tensor compatibility.
Computational consumers retain persistent output/state correlation and include acceptance 2/3.

This adapter is **not** a TaskPIOA→full-SSPᵈ `UCSetupMorphism`, U/UC preservation
or reflection. A compiler and target coverage for **that unrestricted endpoint**
are not supplied by individual all-`Calls` adequacy. The distinct scheduled native
setup bridge below has its own actual carrier/test/ancillary justification.
The complete boundary is recorded in
[the native task section](uc-setup-causal-boxes.md#43-other-setups-asynchronous-models).

The later checked
[`TaskPIOA.AdaptiveFinite.padded⇔finite-calls`](../src/CategoricalCrypto/TaskPIOA/AdaptiveFinite.agda#L69)
sharpens the finite test boundary: equality of every **padded** fixed-word law,
retaining silence at each activation, is equivalent to equality of every finite
native Tick `Calls` final-result law. Adaptive task selection, rational coins,
early return and failure are included; private state is projected out, but
outer final-result `nothing` is not dropped or renormalized. Reply-level `nothing`
is instead successful silence. Its generic
[`FiniteTesting`](../src/CategoricalCrypto/SSP/Dist/FiniteTesting.agda#L125)
cylinder proof uses total finitely supported rational kernels, unit queries and
decidable replies, not finite state or a global finite reply enumeration.
The actual `resource` kernels and `runᵖ (D ∘ᵖ resource M)` consumer consequences
are checked. Generic source marker contexts additionally give
[all actual source tests→padded→adaptive/composed consumers](../src/CategoricalCrypto/TaskPIOA/Marker.agda#L196),
for arbitrary signatures including inputs, **not the contextual converse**.
Silence-erased bare-word equality alone is weaker: the
[raw pulse pair](../src/CategoricalCrypto/TaskPIOA/AdaptiveTests.agda#L30)
is separated by a fixed padded test and by an actual source marker context as
well as an adaptive test. This is activation-timestamp information loss, not
an adaptive-power or UC-nonreflection theorem.

The later [`SSP.Dist.SchedulerInformation`](../src/CategoricalCrypto/SSP/Dist/SchedulerInformation.agda#L32)
factors this through a reusable **public-view / shared-codec** API.
`lower` passes only viewed replies to a continuation, never private successor
state; `lower-bind` proves finite substitution compatibility and `lower-observe`
agrees with `viewKernel`. A [`Codec`](../src/CategoricalCrypto/SSP/Dist/SchedulerInformation.agda#L74)
has one block encoder and model-independent decoder, left inverse on valid
encoded words. [`Instrumentation`](../src/CategoricalCrypto/SSP/Dist/SchedulerInformation.agda#L80)
contains actual native contexts/execution and empty/one-extension equations,
not the desired all-adaptive conclusion. `encoded-execution` and `extraction`
derive complete fixed-word recovery; `fixed-information-to-calls` compares
arbitrary initial private states using the **same codec and same finite Calls**.
Coins, arbitrary result sets, early return and `dead`/failure are retained.

TaskPIOA's actual marker product and interleaved schedule instantiate this API:
[`markerCodec`](../src/CategoricalCrypto/TaskPIOA/Marker.agda#L88) is independent
of the automaton, and [`markerInstrumentation`](../src/CategoricalCrypto/TaskPIOA/Marker.agda#L162)
proves its extension law from actual native steps. Nonempty input signatures
are closed by input-forwarding names which the marker automaton never fires.
This strengthens the implementation account, not the source test quantifiers.

Context closure uses an additional **local** premise:
[`sample-result` / `link-samples`](../src/CategoricalCrypto/SSP/Dist/SchedulerInformation.agda#L185)
derive finite-result agreement and preserve the existing receiving/step `Samples`
square under an actual SSP protocol context. Standalone Tick-word equality
alone is not arbitrary input-environment closure. Actual public substitution,
linked Samples and a synchronized masked-sender/input-receiver product are
[checked consumers](../src/CategoricalCrypto/TaskPIOA/MarkerTests.agda#L94);
their finite adaptive/closed composed results agree, with true probability `½`.
No infinite/fair/PPT scheduler or unrestricted SSPdist UC theorem follows.

[`IPDL.SchedulerInformation.instrumentation`](../src/CategoricalCrypto/IPDL/SchedulerInformation.agda#L306)
is an independent **native** instance of that same shared API, with typed
Input/Get/Step commands, port-tagged public replies and actual native Strategy
logger execution. Its `singleton-codec O` is independent of net/private state.
Fixed instrumentation equality derives finite native and actual composed SSP
consumer agreement. Original native `Strategy` embeds failure-free; generic
`dead` becomes a `Maybe` result, so no all-Calls/native-Strategy iff is claimed.
The [privacy/local-linking consumers](../src/CategoricalCrypto/IPDL/SchedulerInformationTests.agda#L147)
include all-native-strategy privacy versus illegal residual peek `0/1`,
successful absence `1`, actual local/protocol-context Samples and genuine
hidden-channel linked/flat correlation `1` and challenge acceptance `½`.
This does not supply an IPDL source UC setup or arbitrary open linking theorem.

### 2.2 A distinct scheduled NativeSSP setup bridge, not full SSPdist transfer

[`TaskPIOA.NativeSSP.Morphism.bridge`](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Morphism.agda#L176)
is a complete setup morphism from the actual TaskPIOA setup to **new**
`TaskPIOA.NativeSSP.Setup.UC.StdSetup`. The target has independent finite
owned `Coins` machines, a proved state/kernel-simulation quotient of native wiring,
and scheduled tests evaluated by actual SSP `Protocol.step`/`Calls` execution.
Constructive source backtranslation covers every native valuation, including
noncanonical coin trees; `ν-epi` and total ancillary representations derive
**E/U/UC preservation**. Actual evaluation on every compiled source valuation
also derives [`ν-mono`](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Morphism.agda#L172).
The universal [`native-context-roundtrip`](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Morphism.agda#L183)
proves `compileContext (sampleContext h) ∼ h` for every target wiring hom in the
native semantic quotient. Its independent
[`simulator-representation`](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Security.agda#L54)
acts at arbitrary target computations and ancillas. Every simulator of this
endpoint is such a hom, so **E/U/UC reflection** and unconditional
[`≈ᵁ-iff` / `≤UC-iff`](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Security.agda#L76)
follow by extracting and backtranslating the target dummy simulator.
These are derived theorems, not fields assuming the desired security conclusion.

The [independent native converter client](../src/CategoricalCrypto/TaskPIOA/NativeSSP/ReflectionTests.agda#L54)
builds a biased native `Coins` installation using actual wire/tensor/composition/
unitor syntax and directly proves its target witness. Native, sampled-source and
recompiled-source receiver rewards are `2/3`, while pulse rewards are `1` on
both sides. Witness-specific and unconditional reflection recover positive source
security; the observations distinguish converters, not UC realizability.

The independently defined
[`Protocol.connector`/`installed`](../src/CategoricalCrypto/TaskPIOA/NativeSSP/Protocol.agda#L48)
uses actual ordinary SSP tensor and composition for sender activation and
prescribed receiver-input calls. `joint-square` covers every paired state and
every boundary-input/left-task/right-task channel; actual composed scheduling,
joint reply/state, and arbitrary closing-consumer implementation congruence follow.
`installed-context` compares those two concrete implementations; it does not extend
the setup's scheduled test class to all SSP consumers.
The [actual Boolean runᵖ regressions](../src/CategoricalCrypto/TaskPIOA/NativeSSP/ProtocolTests.agda#L50)
give `just true`/`just false` by schedule order, with composed broadcast,
persistent correlation and non-dyadic receiver reward `2/3` also checked.
This endpoint is **not `SSP.Dist.Setup.StdSetup`**: no full SSPdist coverage or
reflection, categorical equivalence, quotient-respecting backward functor into
source syntactic equality, full native refinement equivalence, infinite/fair
scheduler or PPT theorem is inferred.

## 3. Laws (`SSP/Dist/Laws.agda`)

| law | statement |
|---|---|
| `coins-comm` | a coin tree commutes with any tree whose result it does not feed; `coin-call`, `coin-comm` are instances |
| `coin-drop` | an unused coin vanishes |
| `coin-flip`, `coin-xor` | `uniform-Bool` relabelled by `not`, by `m xor_` (`uniform-flip`) |
| `≈ᵏ->>=ᶜ` (Kernel) | congruence: the laws rewrite inside a step |
| `stepwise` | a state map with `≈ᵏ`-equal steps gives `≈ᵈ`: tree laws become protocol laws |
| `defer` | **deferred sampling** across activations: `ρ` per state, one square per activation |

Limits: `⊑` ranges over all source states (no reachability invariant), and only the fair coin relabels.

## 4. The setup (`SSP/Dist/Setup.agda`)

`Protᵈ = quotient Protᴹ congᵈ`, `ℰᵈ = descend … ℰᵖ ≈ᵈ⇒≋`, `open StdUC Protᵈ ℰᵈ`, and
`ssp⇒dist : UCSetupMorphism SSP.StdSetup StdSetup` by `StdUCMorphism` from `quotientF` and `descendᵛ`:
the identity on protocols and tests, `ν` mono and epi.  With one spelling of the level neither
`congᵈ` nor `Quotient` needs sealing (no `q` blowup, cf. landscape finding 3).

Security is compared in both directions, not merely preserved by the setup morphism:

- `preserves-≈ᵁ` and `preserves-≤UC` have the `Abstract2.Morphism.Transfer` types for `ssp⇒dist`;
  they compare `Transfer.G ssp⇒dist f`, including its structural identity.  Preservation uses
  `descendᵛ-epi` and `Standard2.Morphism.surjective⇒preserves-≈ᵁ`: every target ancilla is an image,
  so no grade-stability hypothesis is needed.
- `G≈id` removes that structural identity.  For the original protocol representatives,
  `ssp≤⇒dist≤ : f SSP.≤UC g → f ≤UC g` and
  `dist≤⇒ssp≤ : f ≤UC g → f SSP.≤UC g`, where unqualified relations here belong to
  `SSP.Dist.Setup`.
- `dist≈ᵁ⇒ssp≈ᵁ` applies the descended test map's `Mono` comparison at **every prefix context**.
  Objects, ancillas, protocols, `sub`, and the presheaf's tests/action have not changed.  Thus
  reflection does not require the source's unknown `GradeStable`, unlike the generic reflection
  theorem.  `reflects-≤UC` also supplies `Transfer.Reflects-≤UC ssp⇒dist` for the mapped protocols.

There is no inverse functor claimed at hom equality: reflecting security does not say
`≈ᵈ ⇒ ≈ᵖ`.

## 5. The one-time pad (`Examples/SSP/OneTimePad/Dist.agda`)

`otp≈idealᵈ : otp ≈ᵈ (SSP.sub sim SSP.∘ ideal)` follows
`otp ≈ᵖ real ≈ᵈ lazy ≈ᵖ simulated ≈ᵖ sub sim ∘ ideal`; the middle is `defer draw`,
`lazy` the simulated world on its reachable phases, `draw` the real ciphertext and key (`c xor m`).
Nine squares: six by computation, two `xor-cancelˡ`, one `coin-xor` at Alice's send.
The original core has 51 lines against the run-level 53 (`play`–`perfect`): locality, not length.

The namespaces in the example's security statements are explicit:

| export | statement |
|---|---|
| `otp≤idealᵈ` | `otp SSP.≤UC ideal`, in the **source** `SSP.Setup`; retains the distributional-to-U proof |
| `otp≤ideal-dist` | `otp SSPᵈ.≤UC ideal`, in the actual **target** `SSP.Dist.Setup`, by its hom equality and dummy completeness with simulator `sim` |
| `otp≤ideal-image-dist` | `Transfer.G SSPᵈ.ssp⇒dist otp SSPᵈ.≤UC Transfer.G SSPᵈ.ssp⇒dist ideal`, consuming the setup morphism's preservation theorem |
| `otp-simulator-dist` | for every `a : Protocol Eveᴵ X`, the simulator is `a ∘ᵖ sim` and the target U-equivalence compares `sub a ∘ otp` with `sub (a ∘ᵖ sim) ∘ ideal` |
| `otp-observations-dist` | for every such `a`, every ancilla `W`, distinguisher `D : ((W ⊗ᴵ X) ⊗ᴵ Honᴵ) → Ωᴵ` and game `G : unitᴵ → W ⊗ᴵ unitᴵ`, the two target prefix-context composites have the same qualitative verdict distribution |
| `leaky-not-secure-dist` | `¬ (aut SSPᵈ.≤UC ideal)`, reflecting a putative target proof back to the source's probe contradiction |
| `leaky-no-simulator-dist` | for every `s : Protocol (Pollᴵ Bool) Eveᴵ`, `¬ (aut SSPᵈ.≈ᵁ (SSPᵈ.sub s SSPᵈ.∘ ideal))` |

The negative result uses **reflection**, not the contrapositive of source-to-target preservation.
Its source proof shows that the secure channel is blind to complementing the message, whatever
the simulator, whereas the authenticated channel's two probes return masses 1 and 0.

These are one-bit, one-message, pollable-state channels with finite rational call trees; the verdict
relation compares both Boolean masses, including missing mass from abort.  They do not establish
general SSProve expressiveness, asynchronous delivery control, or corruption semantics.

Initial implementation warm checks (2026-10-10, `+RTS -M3G -H1G`, one `Checking` line, warning gate
empty): Kernel 492 lines 16 s, Dist 73 lines 10 s, Laws 76 lines 10 s, Setup 32 lines 12 s,
OneTimePad/Dist 95 lines 10 s.

## 6. Descending the compiler to PM[wb] (`SSP/Dist/Compile.agda`)

`dist⇒PM[wb] : UCSetupMorphism SSPᵈ.StdSetup WB.StdSetup` is a lawful
`StdUCMorphism`, not another compiler or another intermediate setup. Its strong
monoidal functor `Fᵂᵈ` uses the existing `⟦_⟧ᵂ` on protocols and the existing
`Fᵂ` identity, composition, tensor, unit and coherence laws; `νᵂᵈ` uses the
existing `νᵂ` test map and naturality.

The additional congruence `⟦⟧ᵂ-resp-≈ᵈ` evaluates `run≈ᵈ e Y Z` at both
ancillas, applies `Dense.Tests.preserves-≈ℰ`, and uses `compile-pad` to replace
compiled source padding with target padding. `compile-pad` uses the tensor
comparison twice and the compiled-wire comparison on both sides. Rewrapping each
bare-kernel component assembles **target categorical hom equality**. This does
not assume that an arbitrary U-kernel is tensor-congruent.

`preserves-≈ℰ`, `preserves-≈ᵁ` and `preserves-≤UC` retain the exact `Transfer`
types for `dist⇒PM[wb]`, now derived through the reusable structural coverage API.
[`test-coverage`](../src/CategoricalCrypto/SSP/Dist/Compile.agda#L78)
reuses [`SSP.Dense.Tests.test-coverage`](../src/CategoricalCrypto/SSP/Dense/Tests.agda#L476)
on the identical test representatives. That witness is built directly from
`tests-dense` for **arbitrary WB target arrows and input closures**, with the actual
finite truncation/depth/call/positive-rational approximation arguments. It is not
an old preservation theorem packaged as a field, nor an exact `ν.Epi` assertion.

[`ancilla-coverage`](../src/CategoricalCrypto/SSP/Dist/Compile.agda#L82)
represents every target `Iface` by the identical source object and reflexive
isomorphism. Generic `covered-≈ℰ`, `covered-≈ᵁ` and `covered-≤UC` derive the
three preservation statements without target `GradeStable`; the public UC proof
no longer detours through `dist≤⇒ssp≤` and the old direct WB transfer.
[`TestCoverage`](../src/CategoricalCrypto/UCSetup/Coverage.agda#L26) is
target-action density of the existing `ν` image, and
[`ContextRepresentation`](../src/CategoricalCrypto/Standard2/Coverage.agda#L54)
contains an actual source object plus target isomorphism—not a desired U/UC conclusion.

The checked triangle is the actual composite
`ssp-via-dist = composeᵁ dist⇒PM[wb] SSPᵈ.ssp⇒dist` compared with
`Dense.SSP→PM[wb]`. `Triangle.objects`, `homs`, `tests`, `grade-objects`,
`grade-homs`, `κ`, `tensor`, `unit` and `computations` provide coherent pointwise
agreement, not propositional equality of bundled records. The object, hom and
test representatives agree definitionally. The composite κ is
`id ∘ ⟦ wireᵖ ⟧ᵂ`, and the composite tensor/unit comparisons are
`⟦ wireᵖ ⟧ᵂ ∘ id`; their proofs use the respective target identity law and
`wire≈σ`, rather than reflexivity of unrelated comparisons.

`Triangle.return-comparison`, `ext-comparison` and `sub-comparison` also
compare the actual graded-law right-hand sides pointwise. Their proofs pass
through the mapped source operation using both morphisms' checked graded laws
and `computations`; no equality of proof fields or bundled records is assumed.

`Examples/SSP/OneTimePad/WB.agda` consumes the descended congruence in
`lazy≈realᵂ` and `otp≈idealᵂ`, transporting deferred sampling and the OTP
simulator equation as categorical equalities. `otp≤ideal-distᵂ` consumes
`preserves-≤UC` on `Dist.otp≤ideal-dist`; the existing `otp≤idealᵂ` public
statement is retained using that result.

The target remains PM[wb], with legal call/return tests and closures. The raw
compiled wire still aborts on an unsolicited return while ordinary PM copycat
forwards it. Neither ordinary-PM security transfer nor unconditional reflection
of target security is claimed: observation density does not backtranslate every
target simulator to a finite SSP protocol.

Targeted `pagda --useUntracked false check` results (2026-10-14, each file's
own OPTIONS): `SSP/Dist/Compile` passed with `+RTS -M6G -H1G -RTS` after a
3 GiB heap exhaustion; `Examples/SSP/OneTimePad/WB` and `FullTests` passed
with `+RTS -M3G -H1G -RTS`. All three warning gates were empty. These are
typechecking results, not uncontended performance measurements: the client
runs reported Nix fetch/profile-lock contention.

The structural-coverage migration was subsequently checked in its seven changed
modules and genuine ITM/SSP consumers; the whole-source escape baseline did not
grow and the warning gate was empty. At integrated source `f0d6ba39c`, the parent
checked `Examples.ITM.Tests` and this actual `Examples.SSP.OneTimePad.WB` consumer
with paired `-M6G -H1G`, rebuilding all seven changed modules and their affected
dependencies (18 Checking lines), with no warnings. The observed combined 92.90 s
run is attributed integration evidence, not an uncontended performance measurement.
No PM[wb]→SSPdist U/UC reflection or unrestricted target-simulator backtranslation
has been added.
