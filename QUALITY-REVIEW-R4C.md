# Quality review R4C (machines, protocols, game playing, interaction, strategies), 2026-10-03

**Scope.** The 41 files in `scope-R4C.txt`. The base is `protocol-rewrite.next5` at `aae4d19e`; the branch is `quality-R4C`.

**Verification.**
- Every commit was checked with the root `src/CategoricalCrypto.agda` at `-M8G -H2G`: rc=0 and the warn grep empty. Several commits also had a per-module check first.
- The tip was checked against the root and against the four non-root leaves the scope reaches: `Examples.ChimericLedger.{Transfer,Serialize}` and `Examples.MerkleDamgard.{Pin,QueryBound}`. All are green.
- The escape-hatch baseline over `src` was 16 lines (all prose) and is unchanged.
- A byte-level NUL check of every committed file is clean.
- The sweep toolkit was not run; the brief assigns it to the sweep agent.

## Committed

| commit | change | ΔLOC |
|---|---|---|
| 686c5bc7 | `Machines.Frame`: deleted the zero-consumer `onR-⊗id` and `⊛-point₂ˡ` (the latter left over from the round-4 `Sim.Lax` deletion) | −13 |
| 0fae473c | `Machines.{Pure,Sandwich}`: `open MC` replaces the second `Core (𝒱ₚ 0ℓ)` application | −2 |
| 661d69e8 | `Machines.Collapse`: the opaque `composeᴳ` and `compose-raw≈ᴳ` only fed `compose-raw≈∘ᴳ` by `refl`, so `compose-raw≈∘ᴳ` is now stated directly | −15 |
| b1e76c4d | `Collapse.collapse≈` is now the one proof of "trace of `kᴳ` ≈ `g 𝒢.∘ f`" (it was `Protocol.Machine.Trace.collapse≈`, and repeated in `morphism-∘`). `morphism-∘` (one consumer) is folded into `morphismCompose`. Docs updated | −13 |
| d5bda499 | Inlined single-consumer wrappers `Observe.hitRun`, `Run.runFrom-sim`, `Protocol.Machine.stateᴹ` and `Structural.pure-iso`. Docs updated | −12 |
| daaa7206 | `Pin`: the depth-8 divergence pins are replaced by `upper-run` (every depth) and `prAgree false`. These are the first pins of both lemmas | +3 |
| 0e4d6394 | Doc and comment fixes: `super` → `badProb⊥-bounded`; `⟦⟧-resp-≈` → `UC.Model.Observation.obs-resp`; Average's pointer moved to `GamePlaying.Defer`; the inventory's `⟦_⟧ᴵ` attribution; the mathematical guide's `_∘ᴹ_` (sequential, not Elgot) | +1 |
| e452c5b4 | `Hop.runWith-join`: the `good` hypothesis is dropped (strictly stronger). `FLGP`'s `_≈_` becomes `_≡_` and its split goes. **Out of scope:** `Hiding.Defer.good-J` is deleted | ±0 (whitespace-insensitive: −29/+29) |
| fdf4179c | `Machines.Iteration`: `iter-cong` is now derived from `iter-transfer` along `id`, no longer an `Elgot` field | +4 |
| 7ab9dc65 | `GamePlaying.Partial.badProb⊥-super` now inducts over the `SuperCert⊥` it used to take field by field | −11 |
| c5186107 | `pure⊗-stateˡ/ʳ` moved from `Machines.Pure` to `Machines.Tensor` (no Kleisli content; the one consumer already opens `Tensor`) | ±0 |
| 2b8b8cb1 | `ϕ`, `step-sim` and `point-sim` moved from `Protocol.Machine.Run` to `Machines.Pointwise` (the simulation→pointwise reading, the converse of `simFn`) | −4 |
| a248361c | `Run{,.Lax}` now use Pointwise's `S`/`KP`/`V` instead of re-applying `Sim`/`KDP`/the monoidal category | −9 |

**Statement and type changes (old → new):**
- `runWith-join : (∀ s s′ → s ≋ s′ → bad s ≡ false) → JoinStep → ∀ d s s′ → s ≋ s′ → …` becomes `runWith-join : JoinStep → ∀ d s s′ → s ≋ s′ → …`.
- `badProb⊥-super`:
  - Old: `(resp bad) (Inv φ) → Preserved⊥ Inv resp → (∀ m s → Inv s → 0ℚ ≤ φ m s) → (∀ m s → Inv s → bad s ≡ true → 1ℚ ≤ φ m s) → (∀ m s q → Inv s → E⊥ … ≤ φ (suc m) s) → ∀ m d s → asks≤ m d → Inv s → badProb⊥ resp bad s d ≤ φ m s`.
  - New: `{resp bad s₀ ε} (c : SuperCert⊥ resp bad s₀ ε) → ∀ m d s → asks≤ m d → Inv s → badProb⊥ resp bad s d ≤ φ m s`, where `Inv` and `φ` are `c`'s fields.
  - `badProb⊥-bounded` keeps its type.
- `Iteration.Elgot` loses its field `iter-cong`. The record now provides it as a derived member of the same type.
- `Pin.machine-dead : cum 8 (runᴹ (morphism stuck) echo) bool→ℚ ≡ 0ℚ` becomes `Upper (runᴹ (morphism stuck) echo) 0ℚ`.
- `Pin.stuck-false : cum 8 (runᴹ (morphism stuck) echo) (indᵇ false) ≡ 0ℚ` becomes `Attains (runᴹ (morphism stuck) echo) (indᵇ false) 0ℚ`.
- **Deleted:** `Frame.onR-⊗id`, `Frame.⊛-point₂ˡ`, `Collapse.composeᴳ`, `Collapse.compose-raw≈ᴳ`, `Compose.morphism-∘`, `Observe.hitRun`, `Run.runFrom-sim`, `Protocol.Machine.stateᴹ`, `Structural.pure-iso`.
- **Moved:**
  - `Protocol.Machine.Trace.collapse≈` → `Machines.Collapse.collapse≈`.
  - `Run.{ϕ,step-sim,point-sim}` → `Machines.Pointwise`.
  - `Pure.pure⊗-state{ˡ,ʳ}` → `Machines.Tensor`.

## Suggestions (ranked by complexity removed)

12. **`Machines/Run/Trace.agda :: dispatch-f, dispatch-g, K∘-enter, exit-out, exit-loop`: restatements with one consumer.** They restate `E⊥-map`/`E⊥-bind`/`E⊥-return` at Trace's parameters, for one consumer, `Realization.Bisim` (8 sites). Inline them there only if the types still infer; they may be type pins like `outF`/`outG`. Unspiked; low confidence. About −20 lines.

## Tried, not worth it

- **`Protocol/Machine.agda :: morphism` retyped to the `_⊎_` spelling** (`MC.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)` instead of `𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]`, for `UC.Machine.Proc`'s heap reason). I measured re-elaborating all 85 `Protocol.Machine` dependents: CPU 80 → 82 s and max RSS 4.68 → 4.77 GB, so it is neutral. Reverted.
- **`UC/Machine.agda :: Proc` moved into `Protocol.Machine`, with `Closed` deleted.** The root check fails at `UC.Machine.Composite`: 26 out-of-scope modules see `Proc` only through `UC.Machine`. Deferred to suggestion 2.
- **`GamePlaying/Partial.agda :: hop-boundᵇ⊥` inlined into `Realization.Bound`.** Kept: it is half of the partial/total hop pair that `fcom-uc.md` §2 presents as one API.
- **`GamePlaying.agda :: SuperCert` as `SuperCert⊥ ∘ embedᵏ`.** Not pursued: it would push `Eⱼ` rewrites onto five or more certificate producers, and `prune-cert` already bridges the two.
- **`Protocol.agda :: wireᵖ` moved into `Pin`.** Kept: it is the relay protocol that `Protocol.Machine`'s header argues with.
- **`Protocol/Machine/Raw.agda :: rawRun` and `Protocol/Machine/Trace.agda :: compose-settles` inlined.** Kept: they are named results that `dp-transport.md` and `rcom-icom-b1.md` cite.

## Not reached

- The `Iteration.Elgot` fields beyond `iter-cong` (e.g. whether `iter-ctx` follows from `iter-transfer`). Unexamined.
