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

## 5. The one-time pad (`Examples/SSP/OneTimePad/Dist.agda`)

`otp≤idealᵈ : otp ≤UC ideal` along `otp ≈ᵖ real ≈ᵈ lazy ≈ᵖ simulated ≈ᵖ sub sim ∘ ideal`; the middle is
`defer draw`, `lazy` the simulated world on its reachable phases, `draw` the real ciphertext and key
(`c xor m`).  Nine squares: six by computation, two `xor-cancelˡ`, one `coin-xor` at Alice's send.
Core 51 lines against the run-level 53 (`play`–`perfect`): it buys locality, not length.

Warm checks (`+RTS -M3G -H1G`, one `Checking` line, warning gate empty): Kernel 492 lines 16 s,
Dist 73 lines 10 s, Laws 81 lines 9 s, Setup 32 lines 12 s, OneTimePad/Dist 95 lines 10 s.
