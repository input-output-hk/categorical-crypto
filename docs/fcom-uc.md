# From `F_com`'s game bounds to its machines: settling composites, partial kernels, quantifiers

[`docs/dp-transport.md`](dp-transport.md) moves a closed `Dₚ` run of a raw
machine onto a `Dist⊥` kernel run, given that every activation settles
(`Protocol.Machine.Raw.StepSettles`). Between that and the RO commitment's
UC-level ε-statement stand three generic layers and one example-specific one:
`StepSettles` at a two-factor composite (§1), the game-playing bridges at a
partial kernel (§2), the two-sided bound between the closed machines (§3), and
the quantifiers of the contextual relation (§4). §1, §2 and §4's test and
ancilla quantifiers are theorems; §3 is a theorem on the real leg only.

## 1. The loop settles — the round-trip bound

`Dp.Settle.Settles-bind` is the junction a closed RUN passes. `Dp.Iter.iterₚ`
is the junction a COMPOSITE's step passes, and there no unconditional
statement exists: at an arbitrary body the loop never exits, so `iterₚ u w`
halts at no budget and `Settles n (iterₚ u w) ν` is false for every `n`, `ν`.

### `ProbabilisticLogic.Dp.Settle.Iter`

The junction itself is unconditional:

```agda
Settles-stepᵢ  : (n j : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A)))
                 (ν : Dist⊥ (S × (B ⊎ A))) (κ : S × (B ⊎ A) → Dist⊥ (S × B))
               → Settles n x ν → Supp n x (λ p → Settles (suc j) (contᵢ u p) (κ p))
               → Settles (n + suc j) (stepᵢ u x) (ν >>=⊥ κ)
Settles-stepᵢˢ : …  -- the budgets maxed over the depth-`n` support
Settles-stepᵢ⋆ : …  -- the all-points convenience
```

`stepᵢ u x` is `x >>=ₚ contᵢ u` with the exits taken one step earlier
(`Dp.Iter.tagᵢ` against `Dp.tagₚ`), so the inductions are `Dp.Settle`'s with
`tagᵢ` in place of `tagₚ`. The `suc j` in the hypothesis is not slack: an exit
is a `returnₚ`, whose reading a budget of 0 does not yet see. **No fixpoint
law is spent**: `iterₚ u w` IS `stepᵢ u (u w)` definitionally, so
`Settles-stepᵢ⋆ … (u w) …` is already the one-turn loop lemma and none of
`iterₚ-fix`'s `≈ₚ` appears — which matters, because `Settles` is NOT
`≈ₚ`-stable (below).

The round-trip bound:

```agda
module Loop {S A B : Set} (u : Body S A B) (Ku : S × A → Dist⊥ (S × (B ⊎ A)))
            (bodyS : (w : S × A) → Σ[ i ∈ ℕ ] Settles i (u w) (Ku w)) where

  loopK : ℕ → S × A → Dist⊥ (S × B)
  exitK : ℕ → S × (B ⊎ A) → Dist⊥ (S × B)
  loopK zero    w = return-ℚ nothing
  loopK (suc f) w = Ku w >>=⊥ exitK f
  exitK f (s , inj₁ b) = return⊥ (s , b)
  exitK f (s , inj₂ p) = loopK f (s , p)

  module _ (rank : S × A → ℕ) where
    Drops : ℕ → S × (B ⊎ A) → Set
    Drops r (_ , inj₁ _) = ⊤
    Drops r (s , inj₂ p) = rank (s , p) < r

    Ranked : Set
    Ranked = (w : S × A) (i : ℕ) → Supp i (u w) (Drops (rank w))

    Settles-iter : Ranked → (f : ℕ) (w : S × A) → rank w < f
                 → Σ[ i ∈ ℕ ] Settles i (iterₚ u w) (loopK f w)
```

Three things about this shape are the point.

* **The bound is a rank, not a global clock.** `Ranked` says: at every loop
  point, the body's depth-`i` support carries only re-entries of strictly
  smaller rank. It is read off a step table one clause at a time, at every `i`
  because `Supp` is depth-indexed.
* **It is quantified over the SUPPORT, not over all points.** An unreachable
  re-entry has no bound at all, and demanding one would make `Ranked` false at
  every machine with unreachable configurations — which is all of them. This is
  what `Dp.uniformizeˢ` (with `Supp-map`, `Supp-all`) is for: `Dp.uniformize`
  assumes the per-value budget everywhere.
* **The kernel is the body unrolled `f` rounds, the round past the last read as
  divergence.** That is what makes `loopK` total, and `Settles-iter`'s
  conclusion pins `f` large enough that the divergence is never reached.
  Without the rank the reading is simply wrong, and `Settles-iter` would be
  false rather than unprovable.

### At a traced machine and at a G-composite — `Protocol.Machine.Trace.Compose`

`Machines.Trace.traceStep` is `solve ∘ k ∘ id ⊗₁ i₁`; the two wirings are pure,
so `Settles-ret⋆` takes them one step at a time and the loop is
`Settles-iter`. That is `trace-settles` (with kernel `Ktrace`). A G-composite's
step is `Machines.Collapse.kᴳ`, a dispatch routing each message to one
factor; `Kᴳ` is the two factors' kernels routed the same way, `kᴳ-settles` its
settling, `ranked-from-kᴳ` reduces `Ranked` to a fact about that dispatch, and
`compose-settles` is `trace-settles` at it. At a CLOSED composite,
`compose-StepSettles` is `Raw.StepSettles` for `traceᴳ g f` and `compose-pr` is
the closed run's verdict reading for `g 𝒢.∘ f` itself.

At the RO commitment (`Examples.ROCommitment.Realization.Machine.rankedᴿ`) the
rank of `real 𝒫.∘ resource` is 1 on a resource query and 0 on an answer, at
fuel 2: the receiver never answers the resource with a further query
(`real-up`), and whatever the resource answers is an exit or a rank-0 loop
point, so its own activations never need inspecting.

### Why `Settles` cannot be transported along `≈ₚ`, and what can

`Settles n d ν` carries `Halts n d`, a fact about the TREE modulo semantic
nullity. `_≈ₚ_` is cofinal domination of the `cum` families, i.e. equality of
suprema, and a supremum can be approached without being reached: `d ≈ₚ e` and
`Settles n d ν` do not give `Σ i. Settles i e ν`. So no `Settles` fact moves
along `Dp.Reasoning`'s rearrangements, `Machines.Pointwise`'s calculus or
`_≈ᴹ_`. A `Settles` witness for a composite's step has to be BUILT at the
literal term — which is why `Settles-stepᵢ` is stated at `stepᵢ`, not at
`x >>=ₚ contᵢ u`, and why `𝒢ₚ`'s own `_∘_`, only `S.≈ᴹ`-equal to `traceᴳ g f`
(`collapse≈`), gets no `StepSettles` of its own.

What does cross is the reading of a closed run: monotone `cum` families that
dominate each other cofinally attain the same value, so a `cum` family that has
settled at `v` transports along `≈ₚ` (`Dp.Settle.cum-settled-≈ₚ`). `Settles`
itself would not do, because `Settles-bind` consumes `Halts` of its first
argument and a composite's `Settles` is used as a continuation; the crossing is
therefore made once, at the END, by `compose-pr`.

## 2. The game-playing bridges at a partial kernel

The machines diverge exactly where the game kernels answer `idleR`, so the
transport gives an inequality where a two-sided advantage bound wants an
equality. `Dist⊥` is `Dist-ℚ ∘ Maybe` and the sink scores 0, which only helps
the supermartingale and which the coupling carries through untouched, so the
repair is a `maybeℚ`-relativisation of the toolkit, done once in
`CategoricalCrypto.GamePlaying.Partial`:

| partial | total counterpart |
|---|---|
| `badProb⊥`, `badProb⊥-bad`, `badProb⊥-cong` | `GamePlaying.badProb` |
| `Preserved⊥`, `SuperCert⊥` | `Preserved`, `SuperCert` |
| `badProb⊥-super`, `badProb⊥-bounded` | `badProb-bounded` |
| `Coupling⊥` / `FLGP⊥` | `Coupling` / `Hop.FLGP` |
| `StepBisim⊥` / `runWith⊥-bisim`, `StepBisim⊥ʳ` / `runWith⊥-bisimʳ` | `Hop.StepBisim` / `runWith-bisim` |
| `hop-bound⊥`, `hop-boundᵇ⊥` | `Hop.hop-bound` |

Two structural differences. `Preserved⊥` is genuinely WEAKER than
`Preserved` — an activation the machine refuses to serve reaches no state, so
it preserves any invariant — and the coin junction stays `E`, not `E⊥`, because
`Interaction.runWith⊥`'s `coin` clause binds a TOTAL `Dist-ℚ Bool`.
`runWith⊥-bisimʳ` changes the alphabet (`u : Q → Q′` on asks, a section
`v : R′ → R` on answers), which is what a machine's interface against a game's
`Q`/`R` needs. `hop-boundᵇ⊥` exists because pruning the COUPLING and pruning
its marginal are only `E⊥`-equal (`badProb⊥-cong`).

The total toolkit is the partial one at an embedded kernel:
`embedᵏ : (St → Q → Dist-ℚ (St × R)) → St → Q → Dist⊥ (St × R)`, read back
through `total⇒⊥`; `GamePlaying.badProb` is `badProb⊥ ∘ embedᵏ`. And
`prune dead K` cuts `K` down to the activations a machine serves, with

```agda
prune-cert : (dead : St → Q → Bool)
           → SuperCert K bad s₀ ε → SuperCert⊥ (prune dead K) bad s₀ ε
```

(`dead` constantly `false` is `embedᵏ`): a `SuperCert` proved once about the
total coupling transfers to the pruned kernels for free. `E⊥`'s algebra
(`Eⱼ`, `E⊥-map`, `E⊥-map-bind`, `OnSupport⊥`, `E⊥-mono-on`, `E⊥-abs-diff`)
lives beside `E⊥` in `RationalDist.Expectation`, each the total lemma at
`maybeℚ`.

## 3. `binding-bound`

`Examples.ROCommitment.Honᴵ` is `HonA ⇿ ⊥`, so a strategy at `Honᴵ` alone has
no `ask` and a plugged-adversary statement is vacuous
([`docs/dp-transport.md`](dp-transport.md) §"Route T, and why not Route A"). The non-vacuous
two-sided statement is `runᴹ` at the tensored interface:

```agda
binding-bound : (b : Bool) (m : ℕ)
                (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ))) → asks≤ m d
              → Σ[ n ∈ ℕ ] ((i : ℕ) →
                  ∣ cum (n + i) (runᴹ (subᴵ simulator 𝒫.∘ ideal 𝒫.∘ resource) d) (indᵇ b)
                  -ℚ cum (n + i) (runᴹ (real 𝒫.∘ resource) d) (indᵇ b) ∣ℚ
                  ≤ℚ εᶜ k m)
```

Route: §1 gives `StepSettles` for both closed systems, `Raw.rawPr` turns each
side's `cum` family into a `Pr₁⊥` of a `runWith⊥`, a `StepBisim⊥ʳ` per side
identifies those with the pruned game kernels, and `hop-boundᵇ⊥` at
`Game.cert`-via-`prune-cert` is the bound.

**The real leg is a theorem.** `Examples.ROCommitment.Realization.Bisim`:
`toQ`/`toR` (with section `fromR`) relabel the interface onto the game's
alphabet, `deadR` names the two off-protocol cell activations, and
`bisimᴿ : StepBisim⊥ʳ … respR⊥ …` at `respR⊥ = prune deadR respR`.
`Realization.Bound`: `real-run`, `game-bound⊥`, and `extraction-real`, which
bounds the closed real MACHINE against the pruned ideal GAME by `Game.ε m` at
every `asks≤ m d`.

**The ideal leg is blocked at the machines as they stand**
(`Realization.Bisim` §"Where the ideal leg stops"): the simulator logs every
answer it relays, including one the oracle served from its table, so after a
repeated query `extract` reads `false` (`extract-relog`) where `Game.comI`
reads the committed bit (`extract-table`), and the game's bad event — a
duplicate in the ORACLE's answer log — has not fired. No state relation repairs
it. Either the simulator caches, or `Game.respI` is restated over the relay
log, which makes `Game.cert` false (a repeated query then raises `dup` with
certainty). `binding-bound` is not in `src/`.

## 4. The quantifiers

The game bound quantifies over finite strategies at the concrete resource; the
contextual relation `UC.Quantitative.Family._≈ctx[_]_` (levelwise
`UC.Quantitative.Contextual._≈ᵁᵠ[_]_`) over every certified machine test, at
every ancilla, at every certified closure. Two of the three are not a gap:

```agda
-- UC.Model.Dominated
dominatedᵍᵠ : {P B : Iface} (W : G.Obj)
              (E : W G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ B) G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ W G.⊗₀ 𝟘ᵒ)
              {c c′ : ℕ⁺} → Image forget c E → Image forget c′ m
            → (u v : Proc unitᴵ (P ⊗ᴵ B)) (ε δ : ℚ) → 0ℚ ℚ.< δ
            → ((d : Strat (Neg (P ⊗ᴵ B)) (Pos (P ⊗ᴵ B))) → asks≤ (value (c · c′)) d
               → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
            → Obs ((E G.∘ T₁ᵒ W (gradedᵒ u)) G.∘ m)
              ≈ₚ[ ε ℚ.+ δ ] Obs ((E G.∘ T₁ᵒ W (gradedᵒ v)) G.∘ m)
```

takes agreement at every strategy of the context's budget to agreement at every
certified model test at every seal-object ancilla, at a nontrivial grade. Its
proof is `UC.Machine.Dominated`'s fuel-indexed extraction of a budgeted test
into finite strategies (`UC.Seam.Extract`'s header states the finiteness
obstruction and how the fuel answers it). So:

* **the test** — closed by `dominatedᵍᵠ`. That a strategy embeds as an
  environment only one way is not the obstruction: the converse is not an
  inclusion of contexts but a *domination up to δ*, and that exists.
* **the ancilla** — closed: `W : G.Obj` is arbitrary.
* **the closure** — open at the OPEN resource domain, and not a density
  question. The game fixes the lazily sampled oracle and the one-shot cell, and
  a different closure is a different game with a different `SuperCert`;
  lifting it would mean re-proving `Game.keep-or-sample` and `Game.rare-raise`
  against an abstract query-bounded resource. The resource-installed boundary
  (`Realization.Assembly.Rcom`, at domain `λ _ → 𝟘ᵒ`) leaves no resource for a
  closure to supply, which is why the target theorem moved there
  ([`docs/rcom-icom-b1.md`](rcom-icom-b1.md)).

**The `+ δ`, and why it is absorbable.** `_≈ctx[_]_` demands a fixed schedule,
and `(∀ δ > 0. d ≈ₚ[ ε + δ ] e) → d ≈ₚ[ ε ] e` needs the cofinal supremum to be
attained, which it is not constructively. It need not be: `δ` is chosen per
level, so `δ = 2⁻ⁿ` (`UC.Approximate.Decay.0<inv-pow-2`) — the slack the
corrupted-receiver second hop already spends
(`Examples.CoinToss.Ideal.Receiver.Compose.ηʰ`, `ηʰ-negligible`) — gives the
schedule `εᶜ n q + 2⁻ⁿ = (q+1)²·2⁻ⁿ`, negligible by `GradedBound-+` at
`Asymptotic.εᶜ-negligible` and `negligible-slack`. One additive `2⁻ⁿ` is the
whole price of the test and ancilla quantifiers.
