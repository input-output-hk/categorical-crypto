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

`preserves-≈ℰ`, `preserves-≈ᵁ` and `preserves-≤UC` have the exact `Transfer`
types for `dist⇒PM[wb]`. U-preservation uses identity-on-objects coverage and
bare-kernel preservation; security can also cross `dist≤⇒ssp≤` and the existing
WB transfer, as the implementation does.

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
