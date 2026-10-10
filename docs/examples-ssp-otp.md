# The one-time pad in the SSP setup

`src/CategoricalCrypto/Examples/SSP/OneTimePad.agda`: maurer2011cc §3.2–3.3's one-time pad in
`SSP.Setup` (`StdUC Protᴹ ℰᵖ`, `docs/uc-setup-ssp.md`), beside the possibilistic
`Examples/RelSetup.agda`.  Interfaces are `oneᴵ`s; a message travels by pollable state (plan §5.2):
Alice sends, Bob, Eve and the key fetches poll.

## 1. What is proved (all in the SSP setup)

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

## 3. The negative result

From `aut ≤UC ideal`, `≤UC⇒dummy` and `≈ᵁ⇒≈ℰ` give a simulator `s` under which the probes "send `m`,
report whether Eve saw `true`" agree within ¼ on `aut` and on `sub s ∘ ideal`.  On `aut` they read 1
and 0.  On `sub s ∘ ideal` they read the same: `ideal` absorbs relabelling the message by `not`
(`flip-ideal`), the relabelling turns one probe into the other (`probe-flip`), and it commutes with
the simulator by `sub-commute′` (`Slide.slide`).  Hence `1 ≤ ½`.  `≈ᵁ⇒≈ℰ` suffices; RelSetup's
`ℰ-faithful` has no analogue here and is not needed.

## 4. Crossing to other setups: the next step (nothing has crossed yet)

- **PM[wb]** (`docs/uc-setup-ssp.md` §4.2–4.3): `Fᵂ otp ≤UC Fᵂ ideal`, i.e. `morphism (toProtocol otp)
  ≤UC morphism (toProtocol ideal)` against well-bracketed environments, from `otp≤ideal` by the
  corollary of `SSP→PM[wb]` (C4–C6, on branch `ssp-bridge`); a one-line application once it lands.
- **𝔾ᴿ**: `rewrite⇒RS` starts at PM, not at PM[wb], so the bridge does not reach random systems.  The
  𝔾ᴿ statement needs the PM statement against all environments first, which needs an adequacy of
  `runᵖ` for compiled closed games that the tree does not have.

Checks (warm single-module, `+RTS -M3G -H1G`): `Uniform/Flip` 7 s (30 lines), `SSP/Reduction` 11 s
(121 lines), `Examples/SSP/OneTimePad` 14 s (409 lines); warning gate empty, escape hatches unchanged.
