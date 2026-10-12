# The one-time pad in SSP and its distributional quotient

`src/CategoricalCrypto/Examples/SSP/OneTimePad.agda`: maurer2011cc §3.2–3.3's one-time pad in `SSP.Setup`
(`StdUC Protᴹ ℰᵖ`), beside the possibilistic `Examples/RelSetup.agda`.  Interfaces are `oneᴵ`s; a message
travels by pollable state (`docs/uc-setup-ssp.md` §5.2): Alice sends, Bob, Eve and the key fetches poll.

## 1. The source `SSP.Setup`

| name | content |
|---|---|
| `channel leak`; `aut`, `ideal`, `relayEnc` | one message, Eve's poll answered by `leak`; leaking the message, only *that* one was sent, its complement |
| `key`, `enc`, `dec`, `encdec`, `otp` | the key drawn when first fetched (brzuska2018 Def. 9); the converters sharing it; `otp = (wireᵖ ⊗ᵖ encdec) ∘ᵖ ⌜ αᴵ⁻¹ ⌝ ∘ᵖ (aut ⊗ᵖ key) ∘ᵖ ⌜ ∇ ⌝` |
| `sim`; `otp≤ideal` | on Eve's first poll after a send, draw a ciphertext and keep it; `otp ≤UC ideal` |
| `ideal≤aut`, `otp≤aut`, `relay≤aut` | RelSetup's `ideal≤leaky`, `send≤leaky`, `relay≤plain` (simulators relabel Eve's answer) |
| `leaky-not-secure` | `¬ aut ≤UC ideal` |
| `no-tree-simulation` | `∀ s → ¬ otp ≈ᵖ sub s ∘ ideal` |

General lemmas added: `SSP.Reduction.≈ᵍ⇒≈ᵁ` (closed games no distinguisher separates are U-equivalent:
`closed-bridge` after absorbing the trivial closure) and `ProbabilisticLogic.Distribution.Uniform.Flip`
(`uniform-not`, `uniform-flip`: the `Dist-ℚ` face of `Dp.Coin.coin-flip`).

## 2. `otp≤ideal`, and why it is not a few lines

`dummy-complete (sim , …)` along `otp ≈ᵖ real ≈ᵁ simulated ≈ᵖ sub sim ∘ ideal`.

- **Inlining** is the call-tree part: `otp≲real` and `ideal≲simulated` are one simulation each,
  every case `≈ᶜ-refl` once the state is split (brzuska2018's modular game = monolithic game).
- **The middle step is no `≈ᵖ`** (`no-tree-simulation`).  A simulation maps step trees by `mapᶜ`
  up to `≈ᶜ`, which compares coins as syntax, so "Alice's first send draws" is invariant along `≈ᵖ`.
  It holds for `otp` (the key) and fails for `sub s ∘ ideal` whatever `s`: a simulator runs only on
  Eve's polls.  Two distributional facts are needed that `≈ᶜ` cannot see: the draw moves from
  Alice's send to Eve's poll (deferred sampling, as `docs/coin-toss.md` §5 finds for `≈ᴹ`), and
  at the poll `k ↦ m xor k` relabels a fair coin (in `𝔾ᵒ` that is `coin-flip` inside `≈ₚ`).
- **Deferred sampling** is read out at every distinguisher `D` (`perfect : real ≈ᵍ[ 0ℚ ] simulated`):
  one induction on `D`'s step tree per phase, `fresh` (nothing sent), `pending` (the real side
  averaged over the key, `D`'s own coins commuting by `>>=ᴹ-comm`), `revealed` (lockstep), with
  `uniform-flip` at Eve's poll; then `≈ᵍ⇒≈ᵁ`.
- **Distributional proof** (`Examples/SSP/OneTimePad/Dist.agda:otp≤idealᵈ`): the same **source**
  theorem `otp SSP.≤UC ideal`, its core one `defer` of nine per-activation squares.
  `otp≈idealᵈ` is also an actual hom-equation in the quotient, giving the separate target theorem
  `otp≤ideal-dist : otp SSPᵈ.≤UC ideal`; see `docs/uc-setup-ssp-dist.md` §5.

## 3. The negative result

From `aut ≤UC ideal`, `≤UC⇒dummy` and `≈ᵁ⇒≈ℰ` give a simulator `s` under which the probes "send `m`,
report whether Eve saw `true`" agree within ¼ on `aut` and on `sub s ∘ ideal`.  On `aut` they read 1
and 0.  On `sub s ∘ ideal` they read the same: `ideal` absorbs relabelling the message by `not`
(`flip-ideal`), the relabelling turns one probe into the other (`probe-flip`), and it commutes with
the simulator by `sub-commute′` (`Slide.slide`).  Hence `1 ≤ ½`.  `≈ᵁ⇒≈ℰ` suffices (RelSetup's `ℰ-faithful` has no analogue).

In the actual `SSP.Dist.Setup`, `leaky-not-secure-dist : ¬ (aut SSPᵈ.≤UC ideal)` reflects any
purported quotient security proof through `SSPᵈ.dist≤⇒ssp≤` and invokes this source contradiction.
It does **not** follow from one-way preservation.  The stronger consumer
`leaky-no-simulator-dist` rules out target U-equivalence to `sub s ∘ ideal` for every simulator `s`.

## 4. Crossing to other setups

- **SSPᵈ**, crossed: `SSP.Dist.Setup.ssp⇒dist` is the identity on protocol representatives and tests,
  with the latter descended along `quotientF`; its preservation uses the existing `Standard2`
  surjective-ancilla theorem and `Abstract2` transfer.  The example's `otp≤ideal-image-dist`
  consumes that morphism on both endpoints.  Its unwrapped target result `otp≤ideal-dist`
  retains `sim`, and `otp-simulator-dist` gives the explicit simulator `a ∘ᵖ sim` for **every**
  adversary `a`.  `otp-observations-dist` reads this witness through the target presheaf for
  **every** ancilla, distinguisher and game, not just a selected test.  Reflection uses the
  unchanged prefix contexts and the descended test map's `Mono`, without grade stability.
- **PM[wb]** (`docs/uc-setup-ssp.md` §4.2–4.3), crossed: `Examples/SSP/OneTimePad/WB.agda:otp≤idealᵂ`,
  `Fᵂ otp ≤UC Fᵂ ideal`, i.e. `morphism (toProtocol otp) ≤UC morphism (toProtocol ideal)` against
  well-bracketed environments, is `SSP.Dense.Tests.preserves-≤UC otp≤ideal`.  `preserves-≤UC` is
  unconditional: `SSP→PM[wb]` is built over `games-dense` and preserves `≈ℰ` by `tests-dense`
  (`docs/uc-setup-ssp.md` §5.1, §6 C7); no `ν.Epi` is used.
- **Full-test `𝒲[ι*ℰᵒ]` and PM**, for inlining and an explicit simulator construction:
  `Examples/SSP/OneTimePad/FullTests.agda` uses exactly `StdUC.StdSetup 𝒲ᴹ ι*ℰᵒ`,
  not `𝒲ᵂ.StdSetup` or PM[wb]. `otp≈real-full` lifts the nontrivial probabilistic,
  stateful `otp≲real` through `⟦⟧ᵂ-resp` to the full-test U-kernel;
  `otp≤real-full` and `otp≤real-PM` give source security and its inclusion image.
  `ideal-with-sim≤ideal-full` uses the actual compiled, stateful random `sim` as
  dummy simulator, with different real/ideal adversary grades, and
  `ideal-with-sim≤ideal-PM` transports that construction. Its real side is
  `Full.sub compiled-sim ∘ compiled-ideal`, using `𝒲ᴹ`'s tensor: this does not
  assert that compilation preserves the SSP tensor under full tests.
  The bridge `UC/Bracket/InclusionTransfer.ι-preserves-≤UC` needs no PM
  `GradeStable`: singleton-channel wires make `ιᴹ` essentially surjective.
  Neither example asserts full-context OTP confidentiality. `otp≤idealᵂ` lives in
  PM[wb], and the inclusion has no reverse map from that setup into its full-test
  source; the well-bracketed quotient theorem is not an input to this bridge.
- **𝔾ᴿ**: `rewrite⇒RS` starts at PM, not at PM[wb], so the existing OTP confidentiality
  theorem still does not reach random systems through these bridges. Its 𝔾ᴿ statement
  needs the PM statement against all environments first, which needs an adequacy of
  `runᵖ` for compiled closed games that the tree does not have.

These examples cover a one-bit, one-message pollable-state interface with finite rational
call trees, not all SSProve programs or models of asynchronous delivery and corruption.

Checks (warm single-module, `+RTS -M3G -H1G`): `Uniform/Flip` 7 s (30 lines), `SSP/Reduction` 11 s
(121 lines), `Examples/SSP/OneTimePad` 14 s (409 lines), `Examples/SSP/OneTimePad/WB` 15 s (16 lines);
warning gate empty, escape hatches unchanged.
