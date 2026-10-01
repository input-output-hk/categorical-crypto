# State events: the current theorem contract (WP0 inventory)

WP0 of `model-state-events-and-preservation-plan.md` (that plan is untracked at this
baseline; it lives in the `protocol-rewrite` worktree). Baseline: `protocol-rewrite` at
`d505dafe`. This document records what the code states and makes no changes to it.

**Update (monitor-flag landing, `docs/monitor-flag-spike.md`).** Rows 14 and 18-22 and
their signatures state the code after the landing (line numbers dropped there); §2's
derivation and pinned numbers below are the record at the baseline, where the monitor
charged `q + 1`. Since the landing the ideal bound is read at `p′ n` (step 8), `hitsᵘ`'s
premise is at `asks≤ (p′ n) d` (step 10), only the emulation is read at `p′ n + 1` (step 7:
`≈ᶠ-runs` needs a positive cap), and `εᴹ` is gone: `fₚ(n) = εᴸ(n, p(n) + p(n)) + νₚ(n)`.

Conventions.

- Every `file:line` is relative to `src/CategoricalCrypto/` unless it starts with
  `ProbabilisticLogic/`, `Data/` or `Categories/` (those are relative to `src/`). Line
  numbers are at `d505dafe`.
- "Definitionally" means the code uses the identification without a cast. No module was
  re-typechecked for this inventory.
- **UNVERIFIED** marks anything not confirmed by reading the code.
- Plan baseline confirmed at `d505dafe`. There is no `UC/Model/EventBounds.agda`; the
  module is `UC/Machine/EventBounds.agda`. There is no `UC.agda` and no `UC/Model.agda`.
  `IsWatch` does not occur in `src/`, and `watchFrom report` (`Strategy.agda:55`) replaced
  it. `_≤UC[_]_` here is still a record (`UC/Audit.agda:82`); the ledger chain does not use
  it or `UC.Audit` at all.

## 1. The contract table

Columns:

- *Quantifiers*: binding order, with `{…}` for implicit binders and a module telescope in
  `[…]`.
- *Repr.*: **P** is a layer-1 `Protocol` record (call trees). **M** is a machine
  presentation: `Proc A B = 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]` (`UC/Machine.agda:62`), a concrete
  `Machine` whose equality is `_≈ᴹ_`. **G** is a hom of the opaque seal `𝔾ᵒ`. **S** is a
  `Strat` tree. No row uses a quotient type.
- *Resource*: **rate** is `ℕ⁺`. **cap** is `ℕ` and includes 0. **depth** is the `ℕ`
  approximant index.
- *Error*: the error index and how it is read.

The verbatim signatures are in §1.1, keyed by row number.

| # | Definition | Owner | Quantifiers | Repr. | Resource | Error | Adequacy / operational counterpart |
|---|---|---|---|---|---|---|---|
| 1 | `Systems` | `UC/Model/Family/Emulation.agda:49` | `B`, then level `n` | P family | — | — | image `imgᶠ B R n = Gr.closedᵒ (morphism (R n))` (`:61-62`) |
| 2 | `_≈ᶠ[_]_` | `UC/Model/Family/Emulation.agda:68` | `{B}` `R` `ε` `I`; unfolds (`UC/Quantitative/Family.agda:134`, `UC/Quantitative/Contextual.agda:76-80`) to `∀ n W E m {c r′ : ℕ⁺} → Image forget c E → Image forget r′ m → …` | G (images of P) | rates `c r′ : ℕ⁺` on test and closure | `ε : ℕ → ℕ → ℚ`, read at `ε n (value (c · r′))` under `_≈ₚ[_]_` (two-sided, both verdicts; `ProbabilisticLogic/Dp/Advantage.agda:46`, `Dom` = `∀ n ∃ m. cum n ≤ cum m + δ`, `ProbabilisticLogic/Dp.agda:395`, `Data/Rational/LowerReal.agda:31-36`) | `≈ᶠ-runs` (row 4); `≈ctxᴬ⇒≈ℰ[]` (`Emulation.agda:86`) to the packaged `_≈ℰ[_]_` |
| 3 | `_≈ᶠᴺ_` | `UC/Model/Family/Emulation.agda:73` | `Σ ε`, then `NegligibleBound ε × R ≈ᶠ[ ε ] I`: one global schedule, chosen before any allowance | G | as row 2 | `NegligibleBound ε = ∀ p → Poly p → Negligible (λ n → ε n (p n))` (`UC/Approximate.agda:101-102,126`) | none of its own. It is consumed only through its three components (`Transfer.agda:75`); it has no map into `Cᴺ.≤UC` in the tree |
| 4 | `≈ᶠ-runs` | `UC/Model/Family/Emulation.agda:108` | `{B R I}` `ε` `h` `n` `(q : ℕ⁺)` `d` `asks≤ (value q) d` | G → M runs at S | rate `q : ℕ⁺` (no zero), closure at `1⁺` | `ε n (value q)` via `*-identityʳ` | it *is* the adequacy step. It specializes row 2 at ancilla `𝟘ᴳ`, test `auditTest _ d`, closure `auditClose` (`UC/Seam/Audit/Context.agda:52,64`) and certificate `audit-qb` (`:67`), then applies `audit-run` (`:72`: `observe … ≈ₚ runᴹ w e`) |
| 5 | `≤UC[]⇒≤UCᴺ` | `UC/Model/Family/Emulation.agda:100` | `[{A X Y B} s ε neg f g e]` | G | simulator certificate `s : Certified Y X` | fixed `ε`, forgotten into `Cᴺ.≤UC` | not on the ledger chain. Consumers: `Examples/CoinToss/Ideal/Compose.agda:129`, `…/Receiver/Compose.agda:161` |
| 6 | `Strat` | `Strategy.agda:24` | `Q R : Set` | S (`out`/`ask`/`coin` with `Dist-ℚ Bool` coin) | — | — | layer-1 run `runWith⊥` (`Interaction.agda:31`); machine run `runᴹ` (`Protocol/Machine.agda:113`); embedding `strategyEnv` (`UC/Seam.agda:66`), `adequacy : ⟦ strategyEnv B d ∘ u ⟧ᴼ ≈ₚ runᴹ u d` (`UC/Seam/Adequacy.agda:95`); `stratTest` / `stratTest-embeds` (`UC/Machine/Monitor/Agree.agda:78,81`) |
| 7 | `asks≤` | `Strategy.agda:29` | `(n : ℕ)` then `d`; `{Q R}` generalized | S | cap `ℕ`, 0 allowed (`asks≤ zero (ask …) = ⊥`, coins free) | — | `qb-strategyEnv : asks≤ c d → QB c (strategyEnv B d)` (`UC/Seam/Budget.agda:159`); `qb-stratTest` (`UC/Quantitative/EventLift.agda:141`); `audit-qb` (row 4) |
| 8 | `watchFrom` | `Strategy.agda:55` | `report acc d`; `asks≤-watch` (`:61`) keeps the cap | S → S | cap preserved | — | process form `monitorᴹ` (`UC/Machine/Monitor.agda:72`); `agree` (`UC/Machine/Monitor/Agree.agda:505`) |
| 9 | `Pr` (and `Prᵇ`, `runObs`, `runFrom = runWith⊥ kernel`) | `Protocol/Observe.agda:156` (`:141-157`) | `[P]` `d`; `{B}` generalized | P × S | none: total structural recursion on the tree | exact `ℚ` over `Dist⊥`; divergence (`dead`, `evalC dead = return nothing`, `:49`) weighs 0 | `prAgree` (`Protocol/Machine/Agree.agda:101`), `upper-run` (`:119`), `run-upper` (`:130`) |
| 10 | `hitFrom` | `Protocol/Observe.agda:163` | `[P] [Bad]` `acc s d` | P × S | — | — | at `fa45eaf5`: `UC/Machine/StateEvent/Adequacy.agda` reads `PrHit` at the machine through `idleTest` (`:148`), with `hit⇒stateBounded`/`stateBounded⇒hit` (`:203`, `:195`) |
| 11 | `PrHit` (via `hitRun`, `:169`) | `Protocol/Observe.agda:172` | `[P] [Bad]` `d` | P × S | — | exact `ℚ`. This is the COMPLETED-RUN event: `Bad` is sampled at `init P` and after each completed `kernel` step (`:166`), is not updated at `coin`, and is returned only at `out` (`:164`); a `dead` branch contributes 0 | `hit≤badProb⊥` (`Protocol/Safety.agda:50`) to `GamePlaying.Partial.badProb⊥`; ledger-specific `auditWatch-sound`/`-complete` (`Examples/ChimericLedger/Observable.agda:190,196`) |
| 12 | `Bounded` | `Protocol/Observe.agda:179` | `P bad ε`, then `∀ q d → asks≤ q d → Pr P (bad d) ≤ ε q` | P × S | cap `q : ℕ` | `ε : ℕ → ℚ` read at the cap | `upper-run`; lifted to contexts by `ledger-hitsᵘ` (`Examples/ChimericLedger/Property.agda:122`) |
| 13 | `BoundedHit` | `Protocol/Observe.agda:183` | `P Bad ε`, then `∀ q d → asks≤ q d → PrHit P Bad d ≤ ε q` | P × S | cap `q : ℕ` | as row 12 | supplied by `hit-bounded` (`Protocol/Safety.agda:76`) |
| 14 | `Reader` (and `readRun`, `readRun-resp-≈`) | `UC/Machine/EventBounds.agda` | `B B′`, then `∀ Y → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B′) Ωᴵ` | M | — | — | one instance since the monitor-flag landing: `flagReader : Reader B (B ⊗ᴵ Ωᴵ)` (`UC/Machine/Monitor.agda`), which reads `M ▷ P` and the monitored process `μ ∘ f` alike (`compileᴹ` is retired; `docs/monitor-flag-spike.md`); `readRun Y f 𝔠 E m = ctxRun Y (𝔠 Y E) m f`, with `ctxRun Y E m f = ⟦ (E ∘ T₁ᴵ Y f) ∘ m ⟧ᴼ` (`UC/Machine/Bridge.agda`); transported generically over any `Reader` by `UC/Machine/EventBounds/Transport.agda` |
| 15 | `BoundedAt` | `UC/Machine/EventBounds.agda:67` | `{A B}` `q r f 𝔠`, then `∀ Y E m {c c′} → QB c E → QB c′ m → scale c (positive c′) ≤ q → Upper …` | M (arbitrary certified context) | cap `q : ℕ`; certificates `QB c`, `QB c′` (counts `ℕ`); admission `c · (c′ ⊔ 1) ≤ q` (`Data/Nat/Positive.agda:56,63`); depth: `Upper d r = ∀ k → Pr≤ k d ≤ r` (`ProbabilisticLogic/Dp/Advantage.agda:91`) | `r : ℚ`, one-sided | `hits⇒bounded` (row 20) at `compileᴹ` |
| 16 | `Boundedᶠ` | `UC/Machine/EventBounds.agda:78` | `[{A B} f 𝔠]` `ε`, then `∀ n q → BoundedAt q (ε n q) …` | M | as row 15 | `ε : ℕ → ℕ → ℚ`, fixed | `boundedᶠ⇒boundedᴺ` (`:93`) at `ν = 0` |
| 17 | `Boundedᴺ` | `UC/Machine/EventBounds.agda:83` | `[{A B} f 𝔠]` `ε`, then `∀ p → Poly p → Σ ν. Negligible ν × ∀ n → BoundedAt (p n) (ε n (p n) + ν n) …`: `ν` comes after `p`, before `n`, and is uniform over contexts | M | polynomial cap `p n` | `ε` plus a negligible slack `ν : ℕ → ℚ` | as row 16 |
| 18 | `HitsAt` / `Hitsᴺ` | `UC/Quantitative/EventLift.agda` | rows 15/17 at the process `μ ∘ f` and `𝔠 := flagReader B`, `μ : Proc B (B ⊗ᴵ Ωᴵ)` (`Hitsᶠ` is retired: it was row 16 with its arguments reordered) | M | as rows 15, 17 | as rows 15, 17 | `boundedᶠ⇒boundedᴺ` |
| 19 | `hitsᵘ` (the lifting theorem) | `UC/Quantitative/EventLift.agda` | `{B}` `report u q {r}` `h`; `h : ∀ d → asks≤ q d → Upper (runᴹ u (watchFrom report false d)) r` | S premise → M conclusion | premise at the context's cap `q` (was `q + 1` before the monitor-flag landing); the certificate is `stateLift`'s `FlagCert` at `k + 1`, the `+ 1` being the flag ask | `r`, unchanged: no slack is spent | `monitor-flag` (`UC/Machine/Monitor.agda`) under `readRun-resp-≈`, then `stateLift` at `accᴹ report u` (`UC/Machine/StateEvent/Lift.agda`), premise read back by `flag-agree` (`UC/Machine/Monitor/Agree.agda`) |
| 20 | `hits⇒bounded` | `UC/Quantitative/EventLift.agda` | `{B}` `report P q {r}` `h d a` | M premise → P × S conclusion | the same cap `q` (`scale q (positive 0) = q`, `scale-unit`) | `r` | `hits⇒upper` (= `agree` at `Y = unitᴵ`, `E = stratTest B d` (`qb-stratTest`), `m = m₀`, `qb-closed`) + `run-upper`; `agree` is `monitor-flag` + `stateRead-agree` + `flag-agree` |
| 21 | `PreservesValue` | `Examples/ChimericLedger/Property.agda` | `[ser] [a V]` `R`: `Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴸ` | M | as row 17 | `εᴸ` (§2) plus `ν` (`εᴹ = εᴸ ∘ (+ 1)` is retired) | `preservesValue⇒saturated` (row 22) |
| 22 | `preservesValue⇒saturated` | `Examples/ChimericLedger/Property.agda` | `[ser] [a V]` `R {ε} pv`: `Hitsᴺ … ε → Saturated (λ n q r → ∀ d → asks≤ q d → Pr (R n) (auditWatch n d) ≤ r) ε`, at any schedule | M → P × S | cap `p n` | `ε n (p n) + ν n`, the same `ν` | `saturated-map` of `hits⇒bounded` |
| 23 | `TruthfulAudit` | `Examples/ChimericLedger/Transfer.agda:184` | `[ser] [a V]` `R bad`, then `∀ n d → PrHit (R n) (bad n) d ≤ Pr (R n) (auditWatch a V n (withAudits n d))` | P × S | **no cap**: every `d` | exact inequality, no slack | a one-sided detection inequality. Proved for `Ideal` by `ideal-truthful` (`:189`, via `auditWatch-complete`); `liar-not-truthful` (`:314`) refutes it for `Liar` |
| 24 | `preserves-value-transfer` (claim 1) | `Examples/ChimericLedger/Transfer.agda:73` | `[ser]` `a V R si`, then `R ≈ᶠᴺ Ideal a V → PreservesValue a V R` | G premise → M conclusion | see §2 steps 7-11 | `ν n = ε n (p n + 1)` | §2 |
| 25 | `ledger-uc-to-pov-family` (claim 2) | at `fa45eaf5`: `Examples/ChimericLedger/Transfer.agda:185` | `[a V]` `si R badR em truthful`, then `BoundedHitᴺ R badR (λ n q → εᴹ n (q + q))` (`UC/Machine/StateEvent/Adequacy.agda:216`), i.e. `Saturated` (`UC/Machine/EventBounds.agda:93`) at `∀ d → asks≤ q d → PrHit (R n) (badR n) d ≤ r` | G premise → P × S conclusion | cap `p n`, read at `p n + p n` | `εᴹ n (p n + p n) + ν n` | `stateᴺ⇒hitᴺ` (`Adequacy.agda:234`) at `idleTest`, applied to the machine-level `ledger-uc-to-state : … → StateSafe R badR …` (`Transfer.agda:178`; `StateSafe`, `Examples/ChimericLedger/Property.agda:100`) |
| 26 | `ledger-pov-family-negligible` | `Examples/ChimericLedger/Transfer.agda:206` | `[ser] [a V]` `si R badR em truthful p Pp`, then `Σ f. Negligible f × ∀ n d → asks≤ (p n) d → PrHit … ≤ f n` | as row 25 | as row 25 | `f n = εᴹ n (p n + p n) + νₚ n` | row 25 plus `Negligible-+` |
| 27 | `ideal-spends-genesis` (claim 3) | `Examples/ChimericLedger/Transfer.agda:225` | `[ser]` `a V n` | P × S | one fixed strategy | exact `≡ 1ℚ` | `Replay.Genesis` (`Transfer.agda:223`) |
| 28 | `ledger-preserves-value-from-hash` | `Examples/ChimericLedger/Transfer.agda:162` | `[ser]` `a V hash si hp` | G | the premise schedule is rescaled to `εᴴ ε n q = ε n (scale (scale q 1⁺) 1⁺)` (`:121`) | `εᴴ` | `hash-liftⁿ` (`:158`) then row 24 |
| 29 | `State` / `Machine` / `St` | `Machines/Core.agda:40,60,64` | `[𝒱]` `A B` | M | — | — | `State = obj, point : unit ⇒ obj, discard : obj ⇒ unit`, where `point` may be effectful (`:35-39`); `St = obj state` |
| 30 | `_∘ᴹ_` | `Machines/Core.agda:99` (in an `opaque` block, `:98`) | `[𝒱]` `g f` | M | — | — | composite state is `state g ⊛ state f` (`:100`); opaque, so laws opt in with `unfolding` |
| 31 | `_≲_` | `Machines/Sim.agda:45` | `[𝒱 𝒫]` `{A B}` `f g`, fields `θ θ-pure θ-discard θ-point θ-step` | M | — | — | a state simulation, not invertible. At `𝒱ₚ`, `Pure θ = Σ h. θ ≈ᵏ pureᵏ h` (`Categories/Category/Construction/Kleisli/Discrete/Pure.agda:25-26`), so an underlying function exists but only as an existential (`fn`, `:28`) |
| 32 | `_≈ᴹ_` | `Machines/Sim.agda:57` | `[𝒱 𝒫]` `EqClosure _≲_` | M | — | — | `runᴹ-resp-≈ᴹ : f ≈ᴹ g → ∀ d → runᴹ f d ≈ₚ runᴹ g d` (`UC/Machine/Run.agda:133`); `obs-resp` (`UC/Model/Observation.agda:61`). This is the hom equality of `Mealy-Category` (`Machines/Category.agda:81`, `_≈_ = _≲_` closed by `categoryHelperᵉ`) |
| 33 | `Protocol`, `morphism`, `MSt` | `Protocol.agda:59`; `Protocol/Machine.agda:60,85` | `A B`; `St init step` | P → M | — | — | the image state is `MSt = idle (St P) | wait k` (`:60-62`), with pure point `returnₚ (idle (init P))` (`:78-82`); `drive` returns to `idle` only on an answer (`:66-70`); adequacy by `prAgree` |
| 34 | Seal: `𝔾ᵒ`, `sealᵒ`, `procᵒ`/`unprocᵒ`, `≈ᴹ⇒≈ᵒ`/`≈ᵒ⇒≈ᴹ`, `unprocᵒ-∘`/`procᵒ-∘` | `UC/Model/Seal.agda:50,70,81,84,87,91,122,130` | — | G ↔ M | — | — | a seal hom at interface objects *is* a `Proc`, and its equality *is* `𝒢ₚ`'s (`:21-24`); no state is exposed through `𝔾ᵒ`'s interface, and every state read must cross `unprocᵒ` |
| 35 | `Certified` / `QB` | `UC/QueryBound.agda:230,241` | `{A B}` `c M`; `QB c M = Σ N. Certified c N × N ≈ᴹ M` | M | count `c : ℕ`, 0 allowed | — | `Certified` is not `≈ᴹ`-invariant (`:232-238`), so `QB` is its closure; `qb-resp-≈` (`:254`), `qb-closed : QB 0 M` for closed `M` (`:251`) |

Row count: **35**.

### 1.1 Verbatim signatures

Module telescopes are in brackets. `Property` and `Transfer` are parameterised by
`(ser : (n : ℕ) → Ledger.Tx n → List Bool)`; `module _ (a V : ℕ)` is at
`Property.agda:91` and `Transfer.agda:179,247`.

1. `Systems : (ℕ → Iface) → Set₁` · `Systems B = (n : ℕ) → Protocol unitᴵ (B n)`
2. `_≈ᶠ[_]_ : Systems B → (ℕ → ℕ → ℚ) → Systems B → Set₁` · `_≈ᶠ[_]_ {B} R ε I = imgᶠ B R ≈ctxᴬ[ ε ] imgᶠ B I`
   — generalized `B` (`Emulation.agda:52`). Underneath: `f ≈ctxᴬ[ ε ] g = (n : ℕ) → f n ≈ᵁᵠ[ ε n ] g n`; `_≈ᵁᵠ[_]_ {A} {X} {B} f ε g = (W : Obj) (E : W ⊗₀ (X ⊗₀ B) ⇒ Ω) (m : 𝟙 ⇒ W ⊗₀ A) {c r′ : ℕ⁺} → Image forget c E → Image forget r′ m → ⟦ (E ∘ id ⊗₁ f) ∘ m ⟧ A.≈[ ε (value (c · r′)) ] ⟦ (E ∘ id ⊗₁ g) ∘ m ⟧`
3. `_≈ᶠᴺ_ : Systems B → Systems B → Set₁` · `R ≈ᶠᴺ I = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × R ≈ᶠ[ ε ] I`
4. `≈ᶠ-runs : (ε : ℕ → ℕ → ℚ) → R ≈ᶠ[ ε ] I → (n : ℕ) (q : ℕ⁺) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ (value q) d → runᴹ (morphism (R n)) d ≈ₚ[ ε n (value q) ] runᴹ (morphism (I n)) d`
5. `≤UC[]⇒≤UCᴺ : f Cᴺ.≤UC g` in `module _ {A X Y B : Obj^ω} (s : Certified Y X) (ε : ℕ → ℕ → ℚ) (neg : NegligibleBound ε) (f : A ⇒^ω (X ⊛ω B)) (g : A ⇒^ω (Y ⊛ω B)) (e : sim f ≤UC[ s , ε ] sim g)`
6. `data Strat (Q R : Set) : Set where out : Bool → Strat Q R; ask : Q → (R → Strat Q R) → Strat Q R; coin : Dist-ℚ Bool → (Bool → Strat Q R) → Strat Q R`
7. `asks≤ : ℕ → Strat Q R → Set`
8. `watchFrom : (Q → R → Bool) → Bool → Strat Q R → Strat Q R` · `asks≤-watch : (report : Q → R → Bool) {n : ℕ} (acc : Bool) (d : Strat Q R) → asks≤ n d → asks≤ n (watchFrom report acc d)`
9. `Pr : Strat (Neg B) (Pos B) → ℚ` (in `module _ (P : Protocol unitᴵ B)`, `Observe.agda:136`) · `Pr = Prᵇ true`; `Prᵇ b d = Prᵇ⊥ b (runObs d)`; `runObs = runFrom (init P)`; `runFrom = runWith⊥ kernel`; `kernel s q = evalC (step P s q)`
10. `hitFrom : Bool → St P → Strat (Neg B) (Pos B) → Dist⊥ Bool` (in `module _ (Bad : St P → Bool)`, `:161`)
11. `PrHit : Strat (Neg B) (Pos B) → ℚ` · `PrHit d = Pr₁⊥ (hitRun d)`; `hitRun = hitFrom (Bad (init P)) (init P)`
12. `Bounded : (P : Protocol unitᴵ B) → (Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → (ℕ → ℚ) → Set` · `Bounded {B} P bad ε = (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → Pr P (bad d) ≤ℚ ε q`
13. `BoundedHit : (P : Protocol unitᴵ B) → (St P → Bool) → (ℕ → ℚ) → Set` · `BoundedHit {B} P Bad ε = (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → PrHit P Bad d ≤ℚ ε q`
14. `Reader : Iface → Set₁` · `Reader B = (Y : Iface) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B) Ωᴵ` · `readRun : (Y : Iface) → Proc A B → Reader B → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool`
15. `BoundedAt : ℕ → ℚ → Proc A B → Reader B → Set₁` · `BoundedAt {A = A} {B = B} q r f 𝔠 = (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ} → QB c E → QB c′ m → scale c (positive c′) ℕ.≤ q → Upper (readRun Y f 𝔠 E m) r`
16. `Boundedᶠ : (ℕ → ℕ → ℚ) → Set₁` · `Boundedᶠ ε = (n q : ℕ) → BoundedAt q (ε n q) (f n) (𝔠 n)` in `module _ {A B : ℕ → Iface} (f : (n : ℕ) → Proc (A n) (B n)) (𝔠 : (n : ℕ) → Reader (B n))` (`EventBounds.agda:75-76`)
17. `Boundedᴺ : (ℕ → ℕ → ℚ) → Set₁` · `Boundedᴺ ε = (p : ℕ → ℕ) → Poly p → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν × ((n : ℕ) → BoundedAt (p n) (ε n (p n) ℚ.+ ν n) (f n) (𝔠 n))` · `boundedᶠ⇒boundedᴺ : (ε : ℕ → ℕ → ℚ) → Boundedᶠ ε → Boundedᴺ ε`
18. `HitsAt : {A B : Iface} → ℕ → ℚ → Proc A B → Proc B (B ⊗ᴵ Ωᴵ) → Set₁` (`= BoundedAt q r (μ 𝒫.∘ f) (flagReader B)`) · `Hitsᴺ : {A B : ℕ → Iface} → ((n : ℕ) → Proc (A n) (B n)) → ((n : ℕ) → Proc (B n) (B n ⊗ᴵ Ωᴵ)) → (ℕ → ℕ → ℚ) → Set₁` (`= Boundedᴺ (λ n → μ n 𝒫.∘ f n) (λ n → flagReader (B n)) ε`)
19. `hitsᵘ : {B : Iface} (report : Neg B → Pos B → Bool) (u : Proc unitᴵ B) (q : ℕ) {r : ℚ} → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → Upper (runᴹ u (watchFrom report false d)) r) → HitsAt q r u (monitorᴹ report)`
20. `hits⇒bounded : {B : Iface} (report : Neg B → Pos B → Bool) → (P : Protocol unitᴵ B) (q : ℕ) {r : ℚ} → HitsAt q r (morphism P) (monitorᴹ report) → (d : Strat (Neg B) (Pos B)) → asks≤ q d → Pr P (watchFrom report false d) ℚ.≤ r`
21. `PreservesValue : Systems LedgerIf^ω → Set₁` · `PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴸ` · `auditMonitorᶠ n = monitorᴹ (Watched.reportsLoss n t)`
22. `preservesValue⇒saturated : (R : Systems LedgerIf^ω) {ε : ℕ → ℕ → ℚ} → Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ ε → Saturated (λ n q r → (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ q d → Pr (R n) (auditWatch n d) ℚ.≤ r) ε`
23. `TruthfulAudit : (R : Systems LedgerIf^ω) → ((n : ℕ) → St (R n) → Bool) → Set` · `TruthfulAudit R bad = (n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → PrHit (R n) (bad n) d ℚ.≤ Pr (R n) (auditWatch a V n (Watched.withAudits n d))`
24. `preserves-value-transfer : (a V : ℕ) (R : Systems LedgerIf^ω) → SerInj → R ≈ᶠᴺ Ideal a V → PreservesValue a V R`
25. `ledger-uc-to-pov-family : SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool) → R ≈ᶠᴺ Ideal a V → TruthfulAudit R badR → (p : ℕ → ℕ) → Poly p → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ εᴹ n (p n ℕ.+ p n) ℚ.+ ν n)`
26. `ledger-pov-family-negligible : SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool) → R ≈ᶠᴺ Ideal a V → TruthfulAudit R badR → (p : ℕ → ℕ) → Poly p → Σ[ f ∈ (ℕ → ℚ) ] Negligible f × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)`
27. `ideal-spends-genesis : (a V n : ℕ) → Pr (Ideal a V n) (Live.spend a V n) ≡ 1ℚ × ((h : Ledger.Hash n) → Live.moved a V n h ≡ (((h , 0) , (a , V)) ∷ [] , []))`
28. `ledger-preserves-value-from-hash : (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≈ᶠᴺ oracle^ω → PreservesValue a V (Realᴴ hash inputConsuming (genesisAt a V))`
29. `record State : Set (o ⊔ ℓ) where field obj : Obj; point : unit ⇒ obj; discard : obj ⇒ unit` · `record Machine (A B : Obj) : Set (o ⊔ ℓ) where field state : State; step : St ⊗₀ A ⇒ St ⊗₀ B` (`St = obj state`)
30. `_∘ᴹ_ : Machine B P → Machine A B → Machine A P` · `g ∘ᴹ f = mk (state g ⊛ state f) (onL (step g) ∘ onR (step f))`
31. `record _≲_ {A B : Obj} (f g : Machine A B) : Set (ℓ ⊔ e) where field θ : St f ⇒ St g; θ-pure : Pure θ; θ-discard : discard (state g) ∘ θ ≈ discard (state f); θ-point : θ ∘ point (state f) ≈ point (state g); θ-step : θ ⊗₁ id ∘ step f ≈ step g ∘ θ ⊗₁ id`
32. `_≈ᴹ_ : Machine A B → Machine A B → Set (o ⊔ ℓ ⊔ e)` · `_≈ᴹ_ = EqC.EqClosure _≲_`
33. `record Protocol (A B : Iface) : Set₁ where field St : Set; init : St; step : St → Neg B → Calls A (St × Pos B)` · `morphism : Protocol A B → 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]` · `data MSt : Set where idle : St P → MSt; wait : (Pos A → Calls A (St P × Pos B)) → MSt`
34. `𝔾ᵒ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)` (opaque) · `sealᵒ : 𝔾ᵒ ≡ 𝒢ₚᴹ 0ℓ` · `procᵒ : {A B : Iface} → Proc A B → ifaceᵒ A G.⇒ ifaceᵒ B` · `unprocᵒ : {A B : Iface} → ifaceᵒ A G.⇒ ifaceᵒ B → Proc A B` · `≈ᴹ⇒≈ᵒ : {A B : Iface} {f g : Proc A B} → 𝒢ₚ 0ℓ [ f ≈ g ] → procᵒ f G.≈ procᵒ g` · `≈ᵒ⇒≈ᴹ : {A B : Iface} {f g : ifaceᵒ A G.⇒ ifaceᵒ B} → f G.≈ g → 𝒢ₚ 0ℓ [ unprocᵒ f ≈ unprocᵒ g ]` · `unprocᵒ-∘ : {A B C : Iface} (g : Proc B C) (f : Proc A B) → 𝒢ₚ 0ℓ [ unprocᵒ (procᵒ g G.∘ procᵒ f) ≈ M._∘_ g f ]`
35. `Certified : {A B : Iface} → ℕ → Proc A B → Set` · `QB : {A B : Iface} → ℕ → Proc A B → Set₁` · `QB {A} {B} c M = Σ[ N ∈ Proc A B ] Certified c N × (N S.≈ᴹ M)`

### 1.2 Consumers at `d505dafe`

- `Systems`, `_≈ᶠ[_]_`, `_≈ᶠᴺ_`, `≈ᶠ-runs` are used only in `Examples/ChimericLedger/*` (and
  `Systems` in `ReplayFamily`). `≤UC[]⇒≤UCᴺ` is used only in `Examples/CoinToss/Ideal/*`.
- `BoundedAt`, `Boundedᶠ`, `Boundedᴺ` are used only in `UC/Quantitative/EventLift.agda`.
  `Reader` is used only in `UC/Machine/Monitor.agda`. `UC.Machine.EventBounds` has two
  importers (`Monitor`, `EventLift`). `UC.Quantitative.EventLift` has two (`Property`, the
  root `CategoricalCrypto.agda`).
- `Hitsᴺ`, `HitsAt`, `hitsᵘ`, `hits⇒bounded`, `hitsᶠ⇒hitsᴺ` are used only in
  `Examples/ChimericLedger/Property.agda`.
- `PrHit` is used in `Observable`, `Replay` (`genesis-preserves`, `Replay.agda:310`) and
  `Transfer`. `hitFrom` is used in `Observable` and `Protocol/Safety`.
- `PreservesValue` is used in `Property`, `Transfer`, `ReplayFamily`
  (`chimeric-not-preserving`) and `Serialize` (`ideal-preserves-value′`).
  `TruthfulAudit` and the claim-1/2/3 theorems have no consumer outside `Transfer.agda`.
- Import counts: `Machines.Core` 60, `Machines.Sim` 37, `UC.Model.Seal` 27, `Strategy` 55,
  `Protocol.Observe` 15.

## 2. The proof path, ideal birthday bound → `ledger-pov-family-negligible`

`p` is the caller's polynomial. `d₀` is the caller's strategy with `asks≤ (p n) d₀`. `ε` is
the schedule inside the premise `em : R ≈ᶠᴺ Ideal a V`. Each step names the lemma, the
binder it instantiates, and the value it receives.

1. **`birthday`** (`ProbabilisticLogic/Distribution/Uniform/Birthday.agda:70`, module
   parameter `n` = hash width): `∀ q → Γ 1 q ≤ fromℕ (q ℕ.* q ℕ.+ q) * inv-pow-2 n`. Here
   `Γ t j = fromℕ (sumN t j) * inv-pow-2 n` (`:32`) and `sumN 1 q = 1 + 2 + … + q`
   (`:28-30`). The inequality is via `sumN-≤ : sumN t j ≤ j * (t + j)` (`:59`), so the
   stated bound is loose by a factor of about 2 against the potential.
2. **`cert : HitCert Sys₀ Bad εbirthday`** (`Examples/ChimericLedger/Birthday.agda:270`).
   The potential is `φ m st = Φ m (Hs (proj₂ st))` (`:119-120`), with
   `Φ m L = bool→ℚ (dup L) + Γ (length L) m` (`ProbabilisticLogic/Distribution/Uniform/Duplicate.agda:76-77`).
   Here `m` is the REMAINING query budget (`Protocol/Safety.agda` header). At `init`,
   `Hs [] = h₀ ∷ []`, so `φ-init` (`Birthday.agda:285`) is `+-identityˡ` then `birthday m`.
   `εbirthday q = fromℕ (q *ᴺ q +ᴺ q) * inv-pow-2 ℓ` (`:65-66`).
3. **`hit-bounded`** (`Protocol/Safety.agda:76`): `BoundedHit P Bad ε`, via `super` (`:72`)
   and `hit≤badProb⊥` (`:50`). The strategy's cap `m` is the argument of `εbirthday`.
4. **`target`** (`Birthday.agda:343`): `TrajectoryLossBounded inputConsuming (genesis h₀ a₀ V) εbirthday`,
   which is `BoundedHit (Sys vr s₀) (badTotal s₀) εbirthday` (`Observable.agda:72`).
   Premises: `ser-inj` and `h₀` (`Birthday.agda:60`), `a₀ V` (`:96`).
5. **`auditWatch-bounded`** (`Observable.agda:203`): `TrajectoryLossBounded → AuditLossBounded`
   at the same `q`, pointwise in `d` through `auditWatch-sound oracle vr s₀ d`
   (`:190`: `Pr P (auditWatch s₀ d) ≤ PrHit P Bad d`).
6. **`ideal-bounded`** (`Property.agda:142`): `SerInj → (n : ℕ) → Bounded (Ideal n) (auditWatch n) (εᴸ n)`.
   It is `Birthday.target n (ser n) (h₀ n) (si n) a V`, so hash width = security
   parameter, and `εbirthday` at `ℓ = n` is `εᴸ n` with no cast. `SerInj` supplies
   `ser-inj` per level (`Property.agda:48-49`).
7. **`≈ᶠ-runs`** (`Emulation.agda:108`), inside `preserves-value-transfer`
   (`Transfer.agda:79-81`). Level `n`; `q := (p′ n + 1 , m≤n+m 1 (p′ n))`; strategy
   `auditWatch a V n d` with `auditWatch-preserving … (p′ n + 1) d ad` (`Property.agda:103`).
   It yields `≈ₚ[ ε n (p′ n + 1) ]` between the direct runs of `R n` and `Ideal a V n`.
   `p′` is the polynomial that `PreservesValue`'s `Boundedᴺ` receives.
8. **`upper-run`** (`Protocol/Machine/Agree.agda:119`) on
   `ideal-bounded a V si n (p′ n + 1) d ad`, giving
   `Upper (runᴹ (morphism (Ideal a V n)) (auditWatch … d)) (εᴸ n (p′ n + 1))`.
9. **`upper-≈[]`** (`ProbabilisticLogic/Dp/Advantage.agda:100`) gives
   `Upper (runᴹ (morphism (R n)) (auditWatch … d)) (εᴸ n (p′ n + 1) + ε n (p′ n + 1))`.
   This step spends the depth witness `∀ k ∃ m`.
10. **`hitsᴸ a V R n (p′ n)`** (`Property.agda:116`), which is `hitsᵘ` (`EventLift.agda:128`)
    with `q := p′ n`. Steps 7-9 discharge its hypothesis at `asks≤ (p′ n + 1) d`. For an
    arbitrary context `Y E m {c c′} qE qm le` with `le : scale c (positive c′) ≤ p′ n`:
    `c + 1 ≤ p′ n + 1` by `q≤scale` (`EventLift.agda:134`), then `eventDominatedᵘ` at `c`
    with the `QB (c + 1)` certificate of `covCtx`. The result is
    `HitsAt (p′ n) (εᴸ n (p′ n + 1) + ε n (p′ n + 1)) (morphism (R n)) (auditMonitorᶠ n)`.
11. **`preserves-value-transfer`** (`Transfer.agda:73-83`) packages the result:
    `ν n := ε n (p′ n ℕ.+ 1)`, negligible by `neg (λ n → p′ n + 1) (poly-+ Pp (poly-const 1))`
    (`:77`). Since `εᴹ n (p′ n) = εᴸ n (p′ n + 1)` by definition (`Property.agda:77-78`),
    this is `PreservesValue a V R` with no cast.
12. **`preservesValue⇒saturated`** (`Property.agda:133`), called from
    `ledger-uc-to-pov-family` (`Transfer.agda:200-202`) with `p″ := λ n → p n + p n` and
    `poly-+ Pp Pp`; `p″` becomes the `p′` of steps 7-11. For each `n`,
    `hits⇒bounded (reportsLoss …) (R n) (p″ n) (bnd n)` (`EventLift.agda:153`) runs at the
    same cap: `Y = unitᴵ`, `E = stratTest`, `m = m₀`, `c = p″ n`, `c′ = 0`. Nothing is
    spent coming back.
13. **`ledger-uc-to-pov-family`** (`Transfer.agda:193-204`) instantiates step 12's strategy
    as `withAudits n d₀`, admitted by `asks≤-withAudits n (p n) d₀ ad : asks≤ (p n + p n) …`
    (`Observable.agda:81`). It chains with `truthful n d₀`; `TruthfulAudit` has no cap, so
    `d₀` is passed unchanged.
14. **`ledger-pov-family-negligible`** (`Transfer.agda:206-217`):
    `f := λ n → εᴹ n (p n + p n) + νₚ n`, negligible by
    `Negligible-+ (εᴹ-negligible (λ n → p n + p n) (poly-+ Pp Pp)) neg`
    (`UC/Approximate.agda:159`). `εᴹ-negligible` (`Property.agda:80`) is
    `GradedBound-reindex` (`UC/Approximate.agda:180`) of `εᴸ-negligible` (`Property.agda:64`),
    which is `negligibleBound-inv-pow-2` (`UC/Approximate/Decay.agda:70`) with `n ≤ n`.

Quantifier order of the endpoint: `∀ si R badR em truthful → ∀ p → Poly p → ∃ f.
Negligible f × ∀ n → ∀ d → asks≤ (p n) d → …`. This matches the plan's
`∀ p. ∃ ν. ∀ n. ∀ experiment at p(n)`, except that the experiment is a `Strat`. The only
context-uniform statement on the path is `PreservesValue R` (steps 10-11). It is applied
to the REAL system through `hitsᵘ` after the emulation has been read at strategy contexts
(step 7). The emulation is never read at a compiled monitor context.

### Pinned numbers

| Plan | Code | Verdict |
|---|---|---|
| `εᴸ(n,q) = (q² + q)·2⁻ⁿ` | `εᴸ n q = fromℕ (q ℕ.* q ℕ.+ q) ℚ.* inv-pow-2 n` (`Property.agda:61-62`), `inv-pow-2 (suc k) = ½ · inv-pow-2 k` (`ProbabilisticLogic/Distribution/Uniform.agda:95-97`) | confirmed |
| `εᴹ(n,q) = εᴸ(n,q + 1)` | `εᴹ n q = εᴸ n (q ℕ.+ 1)` (`Property.agda:77-78`) | confirmed |
| `fₚ(n) = εᴹ(n,p(n) + p(n)) + νₚ(n)` | `λ n → εᴹ n (p n ℕ.+ p n) ℚ.+ νₚ n` (`Transfer.agda:215`) | confirmed, and `νₚ` is exact: `νₚ n = ε n ((p n ℕ.+ p n) ℕ.+ 1)`, with `ε` the first component of `em` (steps 11-12) |

Fully unfolded: `fₚ(n) = ((2p(n)+1)² + (2p(n)+1))·2⁻ⁿ + ε(n, 2p(n)+1)`, where `2p(n)+1`
is `(p n ℕ.+ p n) ℕ.+ 1`. Both summands are read at the same allowance:

- The doubling is `withAudits`' charge (step 13) and reaches **both** the ideal term and
  the emulation term.
- The `+ 1` is `hitsᵘ`'s monitor charge (step 10), which enters through the ideal read at
  `p′ + 1` (step 8) and the emulation read at `p′ + 1` (step 7).

## 3. Where an environment-based theorem would attach

**Stated over admitted environments (contexts):**

- `_≈ᶠ[_]_` and `_≈ᶠᴺ_` (rows 2-3) range over seal contexts `W E m` with
  `Image forget c E`, `Image forget r′ m` (rates `ℕ⁺`).
- `BoundedAt`, `Boundedᶠ`, `Boundedᴺ`, `HitsAt`, `Hitsᶠ`, `Hitsᴺ`, `PreservesValue`
  (rows 15-18, 21) range over machine contexts `Y E m` with `QB c E`, `QB c′ m`,
  `scale c (positive c′) ≤ q` (counts `ℕ`). This is a different admission notion
  (`QB`, row 35) from the seal's `Image forget`.

**Stated only over `Strat`:** `Bounded`, `BoundedHit`, `_≈adv[_]_`
(`Protocol/Observe.agda:193`), `PrHit`, `hitFrom`, `TruthfulAudit`, `ideal-bounded`,
`Birthday.target`, `auditWatch-sound`/`-complete`/`-bounded`, the conclusions of
`≈ᶠ-runs`, `hits⇒bounded` and `preservesValue⇒saturated`, and both claim-2 endpoints
(rows 25-26). The mixed rows are `hitsᵘ` (premise over `Strat`, conclusion over contexts)
and `hits⇒bounded` (the reverse).

The state event enters only at rows 23, 25 and 26. There, a context-uniform bound on the
audit event (row 21) is read back at embedded strategies (step 12) and compared to
`PrHit` over `Strat` (step 13). No context-level statement mentions a state predicate. At
`d505dafe` no machine-level reading of `PrHit` existed; `UC.Machine.StateEvent.Adequacy`
now supplies it (row 10).

**Candidate A: the plan's instrumented closed network (WP2 `stateRead`).** It would read
the state of the distinguished `f` inside `ctxRun Y E m f = ⟦ (E ∘ T₁ᴵ Y f) ∘ m ⟧ᴼ` and
would touch:

- the run: `ctxRun` (`UC/Machine/Bridge.agda:70`), `readRun`
  (`UC/Machine/EventBounds.agda:59`), `⟦_⟧ᴼ = runᴹ M (ask tt out)`
  (`UC/Machine.agda:93-94`) and `runᴹFrom`/`runᴹ` (`Protocol/Machine.agda:107-114`). No
  state-projecting variant exists.
- the placement of `f`'s state in the composite: `T₁ᴵ Y f = mk (state f) stepT`
  (`UC/Machine.agda:128-129`) keeps `f`'s state object; `_∘ᴹ_` (opaque, `Machines/Core.agda:98-100`)
  pairs states as `state g ⊛ state f`. The composite of `𝒢ₚ` is the G construction over
  the traced `ℳₚ` (`Machines/Base.agda:282-286`, `Machines/G.agda:1-8`, `trace` field
  `:50`). How `traceᴹ` lays out the composite state was not read (**UNVERIFIED**).
- collapse and reassociation along `_≲_`: `collapseˡ`/`collapseʳ` (`Machines/Sim.agda:109-117`),
  `tower`/`watch-collapse` (`UC/Machine/Monitor/Agree.agda:486-503`) and
  `eventRun-closed`/`Kctx` (`EventLift.agda:84`, `UC/Machine/Slide.agda:204`). Each is a
  simulation with a state map `θ`, so predicate compatibility would be owed along each one.
- the seal: rows 2-3 are stated at `𝔾ᵒ`, so reads cross `unprocᵒ`/`unprocᵒ-∘`
  (`Seal.agda:84,122`).
- observation sites for protocol images: `idle` states reached when `drive` returns
  `inj₂` (`Protocol/Machine.agda:66-75`), not `wait` states.

**Candidate B: the flag-wire machine `M ▷ P`** (a `Proc A (B ⊗ᴵ Flagᴵ)` carrying the
accumulated flag, read at completion). The existing pieces have exactly this interface
shape:

- `monitorᴹ : Proc B (B ⊗ᴵ Flagᴵ)` (`Monitor.agda:72`), with state `MonSt B = Bool × Maybe (Neg B)`
  (`:57`). Its accumulator is computed from (query, answer) pairs (`monitorStep`, `:60-68`),
  not from a state.
- `flagReadᴹ : Proc (Ωᴵ ⊗ᴵ Flagᴵ) Ωᴵ` (`:92`) reads the flag after the verdict. A test that
  diverges leaves it in `waitE`, so the flag is not reported (`:11-13`): the same
  completed-run convention as `PrHit`.
- `compileᴹ B μ Y E = flagReadᴹ ∘ (subᴵ E ∘ (a⇐ᴵ ∘ T₁ᴵ Y μ))` (`:99-100`).

From the signatures of `subᴵ` and `a⇐ᴵ` (`UC/Machine.agda:148,166`),
`flagReadᴹ ∘ (subᴵ E ∘ a⇐ᴵ) : Proc (Y ⊗ᴵ (B ⊗ᴵ Flagᴵ)) Ωᴵ`. So
`ctxRun Y (flagReadᴹ ∘ (subᴵ E ∘ a⇐ᴵ)) m (M ▷ P)` has the shape of `readRun` with `μ`
removed and `f := M ▷ P`. The well-typedness is read off the signatures and was not
checked. The construction would touch:

- `Machines.Core.mk` for the new process (state `St M × Bool`).
- for protocol images, a flag-carrying variant of `stepᴹ`/`drive`/`stateᴹ`
  (`Protocol/Machine.agda:66-82`) that updates the flag only when `drive` returns `inj₂`
  and starts at `Bad (init P)`, matching `hitRun`.
- a reader built from `flagReadᴹ` in place of `compileᴹ`, plus an analogue of `agree`
  (`Monitor/Agree.agda:505`) whose right-hand side is `hitRun`/`PrHit`
  (`Protocol/Observe.agda:169-173`) instead of `runᴹ u (watchFrom …)`.
- the lift. `covCtx`'s certificate is built on the collapsed tower whose configuration
  carries the monitor, `WCfg = (FlagSt × St E) × MonSt B` (`Monitor/Agree.agda:260-261`).
  With `M ▷ P` the accumulator is in the process, not the context. Whether `hitsᵘ`/`covCtx`
  apply unchanged, and whether their `+ 1` persists, is **not established**.
- compatibility with `_≲_`: from `σ : M ≲ N` one would need `P = Q ∘ fn(θ-pure σ)`, and `fn`
  is existential at `𝒱ₚ` (row 31).
- a relation from `M ▷ P` back to `M`, discarding the flag port. None was found in the
  modules read (**UNVERIFIED** beyond them; `Flagᴵ` occurs only in `Monitor`, `Monitor/Slide`,
  `Monitor/Agree`, `EventLift`, `Property`).

## 4. Stale citations in what was read

In source comments of the modules read:

| Site | Cites | Status at `d505dafe` |
|---|---|---|
| `UC/Model/Family/Emulation.agda:9` | `UC.Family.Negligible.Setup.rel-agree` | module exists; `rel-agree` occurs nowhere in `src/` (last touched by `git log -S` at `7bff206f`) |
| `UC/Quantitative/EventLift/Cov.agda:284` | `UC.Machine.Monitor.qbᵢ-monitor` | absent from `src/` (last touched by `git log -S` at `1f19f73d`, "delete the zero-consumer UC names"); `docs/event-bounds-in-setup.md:1250,1305` still say "keep as pin" |
| `Protocol/Observe.agda:192` | `docs/kb/frontier/15-probabilistic-uc-model.typ` | not tracked in git; exists only untracked in the main checkout |
| `UC/Audit.agda:28` (cited from `EventBounds.agda:9`) | `UC.Model.EventBounds` | moved to `UC.Machine.EventBounds` |

In docs that the read modules cite:

- `docs/end-to-end.md:173` has `UC.Model.EventBounds.BoundedAt`, which should be
  `UC.Machine.EventBounds`. This is a current-state walkthrough, not a history section.
- `docs/event-bounds-in-setup.md` cites `UC.Model.EventBounds` at
  `:136,530,673,677,799,852,918` (plan and history sections). Its current-state WP3 audit
  table lists the module as `UC/Model/EventBounds` "in place" (`:1231,1240-1245`).
  `IsWatch`/`watchFrom-IsWatch`/`auditWatch-IsWatch` appear at `:462,527,531,647,691,877,1281,1352-1353`.
- `docs/ledger-factoring.md` and `docs/ledger-lift-eps.md` (cited at `Transfer.agda:92,149`)
  name deleted modules: `Examples.ChimericLedger.{Factor,FactorEps,EndToEnd,QueryBound}`,
  `Abstract2.Factor`, `UC.Factor.liftᵖ`, `UC.Seam.Grounded.subBlind`,
  `Protocol.Machine.Total`, `UC.Asymptotic.*`. Both open with a "Route history" banner
  saying the names predate the redesign and are not a map of the tree.
- Mechanical grep, context not read: `docs/quantitative-family.md` has `UC.Model.EventBounds`
  or `UC/Model/EventBounds` at `:438,972,1342,1380,1559,1583,1805` and `IsWatch` at
  `:1427,1452,1466,1478,1489,1535`. `docs/uc-module-inventory.md:42` lists `UC.Model.EventBounds`.

In the plan (`model-state-events-and-preservation-plan.md`, untracked):

- its related-plan links `quantitative-theory-consolidation-review-plan.md` and
  `explicit-error-certificates-plan.md` are not tracked at `d505dafe` (they are untracked
  in the `protocol-rewrite` worktree).
- `UC.Audit.audit-carryᵉ` (`UC/Audit.agda:184`), `UC.Machine.EventBounds` and `AuditEvent`
  (`UC/Audit.agda:94`) resolve.
