# State events: the theorem contract

The definitions the state-event and ledger-safety results are stated over:
their quantifier order, representation, resource, error, and the theorem
connecting each to its operational counterpart (§1). §2 is the proof path from
the ideal birthday bound to `ledger-hit-family-negligible`, with its pinned
numbers. §3 says where state events attach. Module names are relative to
`CategoricalCrypto.` unless they start with `ProbabilisticLogic.`, `Data.` or
`Categories.`. "Definitionally" means the code uses the identification with no
cast.

## 1. The contract table

Columns:

- *Quantifiers*: binding order, with `{…}` for implicit binders and a module
  telescope in `[…]`.
- *Repr.*: **P** is a layer-1 `Protocol` record (call trees). **M** is a
  machine presentation `Proc A B = MC.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)`
  (`UC.Machine`), whose equality is `_≈ᴹ_`. **G** is a hom of the opaque seal
  `𝔾ᵒ`. **S** is a `Strat` tree. No row uses a quotient type.
- *Resource*: **rate** is `ℕ⁺`; **cap** is `ℕ` and includes 0; **depth** is the
  `ℕ` approximant index.
- *Error*: the error index and how it is read.

The verbatim signatures are in §1.1, keyed by row number.

| # | Definition | Owner | Quantifiers | Repr. | Resource | Error | Adequacy / operational counterpart |
|---|---|---|---|---|---|---|---|
| 1 | `Systems` | `UC.Model.Family.Emulation` | `B`, then level `n` | P family | — | — | image `imgᶠ B R n = Gr.stageᵒ (morphism (R n))` |
| 2 | `_≈ᶠ[_]_` | `UC.Model.Family.Emulation` | `{B}` `R` `ε` `I`; unfolds through `_≈ctx[_]_` to `∀ n W E m {c r′ : ℕ⁺} → Image forget c E → Image forget r′ m → …` | G (images of P) | rates `c r′ : ℕ⁺` on test and closure | `ε : ℕ → ℕ → ℚ`, read at `ε n (value (c · r′))` under `≈[_]` (two-sided) | `≈ᶠ-runs` (row 4); `≈ctx⇒≈ℰ[]` to `UC.Family._≈ℰ[_]_` (an implication, not an identification) |
| 3 | `_≈ᶠᴺ_` | `UC.Model.Family.Emulation` | `Σ ε`, then `NegligibleBound ε × R ≈ᶠ[ ε ] I`: one global schedule, chosen before any allowance | G | as row 2 | `NegligibleBound ε = ∀ p → Poly p → Negligible (λ n → ε n (p n))` | consumed only through its components; symmetric and simulator-free, with no map into `_≤UC^ωᵉ_` |
| 4 | `≈ᶠ-runs` | `UC.Model.Family.Emulation` | `{B R I}` `ε` `h` `n` `(q : ℕ⁺)` `d` `asks≤ (value q) d` | G → M runs at S | rate `q : ℕ⁺` (no zero), closure at `1⁺` | `ε n (value q)` via `*-identityʳ` | it *is* the adequacy step: row 2 at ancilla `Gr.𝟘ᴳ`, test `auditTest _ d`, closure `Gr.ιᴳ unitᴵ`, certificate `audit-qb`, then `audit-run` (beside it) |
| 5 | `≤UC[]⇒≤UCᴺ` | `UC.Model.Family.Emulation` | `[{A X Y B} s ε neg f g e]` | G | simulator `s : Y ⇒^ω X` | fixed `ε`, forgotten into `Canonicalᴺ._≤UC_` | not on the ledger chain; consumers `Examples.CoinToss.Ideal.Compose`, `….Receiver.Compose` |
| 6 | `Strat` | `Strategy` | `Q R : Set` | S (`out`/`ask`/`coin`, coin `Dist-ℚ Bool`) | — | — | layer-1 run `runWith⊥`; machine run `runᴹ` (`Machines.Run`); embedding `strategyEnv` (`UC.Seam`) with `adequacy : ⟦ strategyEnv B d 𝒫.∘ u ⟧ᴼ ≈ₚ runᴹ u d` (`UC.Seam.Adequacy`); `stratTest`/`stratTest-embeds` (`UC.Seam.Budget`) |
| 7 | `asks≤` | `Strategy` | `(n : ℕ)` then `d`; `{Q R}` generalized | S | cap `ℕ`, 0 allowed (`asks≤ zero (ask …) = ⊥`, coins free) | — | `qb-stratTest : asks≤ q d → QB q (stratTest B d)`; `audit-qb` (row 4) |
| 8 | `watchFrom` | `Strategy` | `report acc d`; `asks≤-watch` keeps the cap | S → S | cap preserved | — | process form `monitorᴹ` (`UC.Machine.Monitor`); `flag-agree` (`UC.Machine.Monitor`) |
| 9 | `Pr` (and `Prᵇ`, `runObs`, `runFrom = runWith⊥ kernel`) | `Protocol.Observe` | `[P]` `d`; `{B}` generalized | P × S | none: structural recursion on the tree | exact `ℚ` over `Dist⊥`; a `dead` branch weighs 0 | `prAgree`, `upper-run`, `run-upper` (`Protocol.Machine.Agree`) |
| 10 | `hitFrom` | `Protocol.Observe` | `[P] [Bad]` `acc s d` | P × S | — | — | `UC.Machine.StateEvent.Adequacy`: `Interaction.hitWith⊥` at the machine kernel is `hitFrom` on `idle` states (`run-hit`, `stateRead-hit`) |
| 11 | `PrHit` | `Protocol.Observe` | `[P] [Bad]` `d` | P × S | — | exact `ℚ`. **The completed-run event**: `Bad` is sampled at `init P` and after each completed `kernel` step, is not updated at `coin`, and is returned only at `out`; a `dead` branch contributes 0. So a run that hits and then diverges does not count. `GamePlaying.Partial.badProb⊥` is the prefix-reachability event (it stops at the first bad state); the two differ only on runs that hit and then diverge | `hit≤badProb⊥` (`Protocol.Safety`) into `badProb⊥`; `stateBounded⇒hit` / `hit⇒stateBounded` (row 37) at the machine; ledger-specific `auditWatch-sound` / `auditWatch-complete` (`Examples.ChimericLedger.Observable`) |
| 12 | `Bounded` | `Protocol.Observe` | `P bad ε`, then `∀ q d → asks≤ q d → Pr P (bad d) ≤ ε q` | P × S | cap `q : ℕ` | `ε : ℕ → ℚ` read at the cap | `upper-run`; `auditWatch-bounded` (from row 13 at the ledger) |
| 13 | `BoundedHit` | `Protocol.Observe` | `P Bad ε`, then `∀ q d → asks≤ q d → PrHit P Bad d ≤ ε q` | P × S | cap `q : ℕ` | as row 12 | supplied by `hit-bounded` (`Protocol.Safety`); `boundedHit⇒stateᶠ` / `stateᶠ⇒boundedHit` (row 40) |
| 14 | `Reader` (and `readRun`, `readRun-resp-≈`) | `UC.Machine.EventBounds` | `B B′`, then `∀ Y → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B′) Ωᴵ` | M | — | — | instances `flagReader : Reader B (B ⊗ᴵ Ωᴵ)` (`UC.Machine.StateEvent.Read`), which reads both `μ ∘ f` and `M ▷ P`, and `advReader a : Reader B (X ⊗ᴵ B)`; `readRun Y f 𝔠 E m = ctxRun Y (𝔠 Y E) m f` |
| 15 | `BoundedAt` | `UC.Machine.EventBounds` | `{A B}` `q r f 𝔠`, then `∀ Y E m {c c′} → QB c E → QB c′ m → scale c (positive c′) ≤ q → Upper …` | M (arbitrary certified context) | cap `q : ℕ`; certificates `QB c`, `QB c′` (counts `ℕ`); admission `scale c (positive c′) ≤ q`; depth: `Upper d r = ∀ k → Pr≤ k d ≤ r` | `r : ℚ`, one-sided | in: `hitsᵘ` (row 19), `stateLift` (row 38); out: `hits⇒upper`, `stateBounded⇒hit`; simulator absorption `bounded-absorb` |
| 16 | `Boundedᶠ` | `UC.Machine.EventBounds` | `[{A B B′} f 𝔠]` `ε`, then `∀ n q → BoundedAt q (ε n q) …` | M | as row 15 | `ε : ℕ → ℕ → ℚ`, fixed | `boundedᶠ⇒boundedᴺ` at `ν = 0` |
| 17 | `Boundedᴺ` | `UC.Machine.EventBounds` | `[{A B B′} f 𝔠]` `ε` = `Saturated (λ n q r → BoundedAt q r (f n) (𝔠 n)) ε`: `∀ p → Poly p → Σ ν. Negligible ν × ∀ n → …` at `ε n (p n) + ν n`; `ν` comes after `p`, before `n`, and is uniform over contexts | M | polynomial cap `p n` | `ε` plus a negligible slack `ν : ℕ → ℚ` | `saturated-map` carries `ν` unchanged |
| 18 | `HitsAt` / `Hitsᴺ` | `UC.Quantitative.EventLift` | rows 15/17 at the process `μ ∘ f` and `flagReader B`, with `μ : Proc B (B ⊗ᴵ Ωᴵ)` | M | as rows 15, 17 | as rows 15, 17 | completed-run, as row 11 |
| 19 | `hitsᵘ` (the lifting theorem) | `UC.Quantitative.EventLift` | `{B}` `report u q {r}` `h`; `h : ∀ d → asks≤ q d → Upper (runᴹ u (watchFrom report false d)) r` | S premise → M conclusion | premise at the context's own cap `q`; the flag ask is the certificate's one extra unit (`FlagCert` at `k + 1`) | `r`, unchanged: no slack | `monitor-flag` (`monitorᴹ report ∘ u` is the flag wire of `accᴹ report u`) under `readRun-resp-≈`, then `stateLift` at `accᴹ report u`, premise read back by `flag-agree` |
| 20 | `hits⇒bounded` | `UC.Quantitative.EventLift` | `{B}` `report P q {r}` `h d a` | M premise → P × S conclusion | the same cap `q` (`scale-unit`) | `r` | `hits⇒upper` (row 15 at `Y = unitᴵ`, `E = stratTest B d` via `qb-stratTest`, `m = λᴵ⇐` via `qb-closed`), then `run-upper`; `agree` is `monitor-flag` + `stateRead-agree` + `flag-agree` |
| 21 | `PreservesValue` | `Examples.ChimericLedger.Property` | `[ser] [t]` `R`: `Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴸ` | M | as row 17 | `εᴸ` (§2) plus `ν` | `preservesValue⇒saturated` (row 22) |
| 22 | `preservesValue⇒saturated` | `Examples.ChimericLedger.Property` | `[ser] [t]` `R {ε} pv`: `Hitsᴺ … ε → Saturated (λ n q r → ∀ d → asks≤ q d → Pr (R n) (auditWatch n d) ≤ r) ε`, at any schedule | M → P × S | cap `p n` | `ε n (p n) + ν n`, the same `ν` | `saturated-map` of `hits⇒bounded` |
| 23 | `TruthfulAudit` | `Examples.ChimericLedger.Property` | `[ser] [t]` `R bad`, then `∀ n d → PrHit (R n) (bad n) d ≤ Pr (R n) (auditWatch n (withAudits n d))` | P × S | **no cap**: every `d` | exact inequality, no slack | one-sided detection. Proved for `Ideal` by `ideal-truthful` (via `auditWatch-complete`); refuted for `Liar` by `liar-not-truthful` (`Examples.ChimericLedger.Transfer`) |
| 24 | `preserves-value-transfer` (claim 1) | `Examples.ChimericLedger.Transfer` | `[ser]` `a V R si`, then `R ≈ᶠᴺ Ideal a V → PreservesValue (genesisTotal V) R` | G premise → M conclusion | see §2 steps 7-10 | `ν n = ε n (p n + 1)` | §2 |
| 25 | `ledger-uc-to-hit-family` (claim 2) | `Examples.ChimericLedger.Transfer` | `[ser] [a V]` `si R badR em truthful`, then `BoundedHitᴺ R badR (λ n q → εᴸ n (q + q))` | G premise → P × S conclusion | cap `p n`, read at `p n + p n` | `εᴸ n (p n + p n) + ν n` | `stateᴺ⇒hitᴺ` at `idleTest` of `ledger-uc-to-state` (row 39) |
| 26 | `ledger-hit-family-negligible` | `Examples.ChimericLedger.Transfer` | `[ser] [a V]` `si R badR em truthful p Pp`, then `Σ f. Negligible f × ∀ n d → asks≤ (p n) d → PrHit … ≤ f n` | as row 25 | as row 25 | `f n = εᴸ n (p n + p n) + νₚ n` | row 25 plus `Negligible-+` |
| 27 | `ideal-spends-genesis` (claim 3) | `Examples.ChimericLedger.Transfer` | `[ser]` `a V n` | P × S | one fixed strategy | exact `≡ 1ℚ` | `Replay.Genesis` (`genesis-live`, `genesis-moves`) |
| 28 | `ledger-preserves-value-from-hash` | `Examples.ChimericLedger.Transfer` | `[ser]` `a V hash si hp` | G | the premise schedule is rescaled to `εᴴ ε n q = ε n (scale (scale q 1⁺) 1⁺)` | `εᴴ` | `hash-liftⁿ` then row 24 |
| 29 | `State` / `Machine` / `St` | `Machines.Core` | `[𝒱]` `A B` | M | — | — | `State = obj, point : unit ⇒ obj`, where `point` may be effectful (in a Kleisli category `unit` is not initial); `St = obj state`. There is no `discard`: machines are pointed only |
| 30 | `_∘ᴹ_` | `Machines.Core` (in an `opaque` block) | `[𝒱]` `g f` | M | — | — | composite state is `state g ⊛ state f`; opaque, so laws opt in with `unfolding` |
| 31 | `_≲_` | `Machines.Sim` | `[𝒱 𝒫]` `{A B}` `f g`, fields `θ θ-pure θ-point θ-step` | M | — | — | a state simulation, not invertible. `θ` is drawn from the pure subcategory `𝒫`; at the probabilistic model its underlying function is `Machines.Pointwise.ϕ = KP.fn (S.θ-pure sim)` (`fn = proj₁` of `IsPure f = Σ h. f ≈ᵏ pureᵏ h`) |
| 32 | `_≈ᴹ_` | `Machines.Sim` | `[𝒱 𝒫]` `EqClosure _≲_` | M | — | — | `runᴹ-resp-≈ᴹ` (`Machines.Run.Sim`); `obs-resp` (`UC.Model.Observation`); the hom equality of the machine category |
| 33 | `Protocol`, `morphism`, `MSt` | `Protocol`; `Protocol.Machine` | `A B`; `St init step` | P → M | — | — | the image state is `MSt = idle (St P) \| wait k`; `drive` returns to `idle` only on an answer (`ret`); adequacy by `prAgree` |
| 34 | Seal: `𝔾ᵒ`, `sealᵒ`, `procᵒ`/`unprocᵒ`, `≈ᴹ⇒≈ᵒ`/`≈ᵒ⇒≈ᴹ`, `unprocᵒ-∘`/`procᵒ-∘` | `UC.Model.Seal` | — | G ↔ M | — | — | a seal hom at interface objects *is* a `Proc`, and its equality *is* `𝒢ₚ`'s; no state is exposed through `𝔾ᵒ`'s interface, and every state read crosses `unprocᵒ` |
| 35 | `Certified` / `QB` | `UC.QueryBound` | `{A B}` `c M`; `QB c M = Σ N. Certified c N × N ≈ᴹ M` | M | count `c : ℕ`, 0 allowed | — | `Certified` is not `≈ᴹ`-invariant, so `QB` is its closure; `qb-resp-≈`, `qb-closed : QB 0 M` for closed `M` |
| 36 | `StateTest`, `_▷_` | `UC.Machine.StateEvent` | `{A B}` `M`; `P : MC.St M → Bool` | M | — | — | `M ▷ P : Proc A (B ⊗ᴵ Ωᴵ)` samples `P` at the (possibly effectful) initial state and at every completed activation (an answer on `B`), and answers the accumulated flag on one extra `Ωᴵ` port. |
| 37 | `stateRead`, `StateBoundedAt` / `StateBoundedᶠ` / `StateBoundedᴺ` | `UC.Machine.StateEvent.Read` | `Y M P E m`; rows 15-17 at `M ▷ P` and `flagReader B` | M | as rows 15-17 | as rows 15-17 | completed-run, as row 11 (`flagReadᴹ` waits for the verdict). At an embedded strategy the reading is `flagStrat` (`stateRead-agree`); at a protocol image it is `PrHit` past a depth (`stateRead-hit`, `stateBounded⇒hit`, `hit⇒stateBounded` at `idleTest`) |
| 38 | `stateLift` | `UC.Machine.StateEvent.Lift` | `{B}` `M P q {r}` `h`; `h : ∀ d → asks≤ q d → Upper (runᴹ (M ▷ P) (flagStrat d)) r` | S premise → M conclusion | the same cap `q`; certificate `FlagCert` at the test's count plus one, the flag ask | `r`, no slack | every extracted strategy is `FlagShaped` (`B`-asks, at most one flag ask, then only coins and a verdict), and its run is dominated by `flagStrat` of its `B`-part (`shaped-run`) |
| 39 | `StateSafe`, `preservesValue⇒stateSafe`, `ledger-uc-to-state` | `Examples.ChimericLedger.Property`; `….Transfer` | `StateSafe R bad = StateBoundedᴺ (λ n → morphism (R n)) (λ n → idleTest (R n) (bad n))` | M | as row 17 | `ε n (q + q)`: `withAudits` doubles the allowance | `hitᴺ⇒stateᴺ` of (row 22 at `p + p`, then `TruthfulAudit`, then `asks≤-withAudits`) |
| 40 | `BoundedHitᴺ`, `hitᴺ⇒stateᴺ` / `stateᴺ⇒hitᴺ`, `boundedHit⇒stateᶠ` | `UC.Machine.StateEvent.Adequacy` | `[{B} P Bad]`, then `BoundedHitᴺ = Saturated (λ n q r → ∀ d → asks≤ q d → PrHit (P n) (Bad n) d ≤ r)`; the conversions under `[T bd]`, `bd : T n (idle s) ≡ Bad n s` | P × S ↔ M | cap preserved | `ε`, `ν` unchanged in both directions | `saturated-map` of `hit⇒stateBounded` / `stateBounded⇒hit` |

Row count: **40**.

### 1.1 Verbatim signatures

`Property` and `Transfer` are parameterised by
`(ser : (n : ℕ) → Ledger.Tx n → List Bool)`. `PreservesValue`, `TruthfulAudit`,
`preservesValue⇒saturated` and `preservesValue⇒stateSafe` sit in
`Property`'s `module _ (t : ℕ)` (the watched total), and are applied at
`t = genesisTotal V`. The claim theorems sit in `module _ (a V : ℕ)`.

1. `Systems : (ℕ → Iface) → Set₁` · `Systems B = (n : ℕ) → Protocol unitᴵ (B n)`
2. `_≈ᶠ[_]_ : Systems B → (ℕ → ℕ → ℚ) → Systems B → Set₁` · `_≈ᶠ[_]_ {B} R ε I = imgᶠ B R ≈ctx[ ε ] imgᶠ B I`. Underneath (`UC.Quantitative.Family`, `UC.Quantitative.Contextual`): `f ≈ctx[ ε ] g = (n : ℕ) → f n ≈ᵁᵠ[ ε n ] g n`; `_≈ᵁᵠ[_]_ {A} {X} {B} f ε g = (W : Obj) (E : W ⊗₀ (X ⊗₀ B) ⇒ Ω) (m : 𝟙 ⇒ W ⊗₀ A) {c r′ : ℕ⁺} → Image forget c E → Image forget r′ m → ⟦ (E ∘ id ⊗₁ f) ∘ m ⟧ A.≈[ ε (value (c · r′)) ] ⟦ (E ∘ id ⊗₁ g) ∘ m ⟧`
3. `_≈ᶠᴺ_ : Systems B → Systems B → Set₁` · `R ≈ᶠᴺ I = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × R ≈ᶠ[ ε ] I`
4. `≈ᶠ-runs : (ε : ℕ → ℕ → ℚ) → R ≈ᶠ[ ε ] I → (n : ℕ) (q : ℕ⁺) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ (value q) d → runᴹ (morphism (R n)) d ≈ₚ[ ε n (value q) ] runᴹ (morphism (I n)) d`
5. `≤UC[]⇒≤UCᴺ : f Cᴺ.≤UC g` in `module _ {A X Y B : Obj^ω} (s : Y ⇒^ω X) (ε : ℕ → ℕ → ℚ) (neg : NegligibleBound ε) (f : A ⇒^ω (X ⊛ω B)) (g : A ⇒^ω (Y ⊛ω B)) (e : sim f ≤UC[ s , ε ] sim g)`
6. `data Strat (Q R : Set) : Set where out : Bool → Strat Q R; ask : Q → (R → Strat Q R) → Strat Q R; coin : Dist-ℚ Bool → (Bool → Strat Q R) → Strat Q R`
7. `asks≤ : ℕ → Strat Q R → Set`
8. `watchFrom : (Q → R → Bool) → Bool → Strat Q R → Strat Q R` · `asks≤-watch : (report : Q → R → Bool) {n : ℕ} (acc : Bool) (d : Strat Q R) → asks≤ n d → asks≤ n (watchFrom report acc d)`
9. `Pr : Strat (Neg B) (Pos B) → ℚ` (in `module _ (P : Protocol unitᴵ B)`) · `Pr = Prᵇ true`; `Prᵇ b d = Prᵇ⊥ b (runObs d)`; `runObs = runFrom (init P)`; `runFrom = runWith⊥ kernel`; `kernel s q = evalC (step P s q)`
10. `hitFrom : Bool → St P → Strat (Neg B) (Pos B) → Dist⊥ Bool` (in `module _ (Bad : St P → Bool)`) · `hitFrom acc s (out _) = return⊥ acc`; `hitFrom acc s (ask q k) = kernel s q >>=⊥ λ (s′ , r) → hitFrom (acc ∨ Bad s′) s′ (k r)`; `hitFrom acc s (coin μ k) = μ >>=ᴹ λ b → hitFrom acc s (k b)`
11. `PrHit : Strat (Neg B) (Pos B) → ℚ` · `PrHit d = Pr₁⊥ (hitFrom (Bad (init P)) (init P) d)`
12. `Bounded : (P : Protocol unitᴵ B) → (Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → (ℕ → ℚ) → Set` · `Bounded {B} P bad ε = (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → Pr P (bad d) ≤ℚ ε q`
13. `BoundedHit : (P : Protocol unitᴵ B) → (St P → Bool) → (ℕ → ℚ) → Set` · `BoundedHit {B} P Bad ε = (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → PrHit P Bad d ≤ℚ ε q`
14. `Reader : Iface → Iface → Set₁` · `Reader B B′ = (Y : Iface) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ B′) Ωᴵ` · `readRun : (Y : Iface) → Proc A B′ → Reader B B′ → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool`
15. `BoundedAt : ℕ → ℚ → Proc A B′ → Reader B B′ → Set₁` · `BoundedAt {A = A} {B = B} q r f 𝔠 = (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ} → QB c E → QB c′ m → scale c (positive c′) ℕ.≤ q → Upper (readRun Y f 𝔠 E m) r`
16. `Boundedᶠ : (ℕ → ℕ → ℚ) → Set₁` · `Boundedᶠ ε = (n q : ℕ) → BoundedAt q (ε n q) (f n) (𝔠 n)` in `module _ {A B B′ : ℕ → Iface} (f : (n : ℕ) → Proc (A n) (B′ n)) (𝔠 : (n : ℕ) → Reader (B n) (B′ n))`
17. `Boundedᴺ : (ℕ → ℕ → ℚ) → Set₁` · `Boundedᴺ = Saturated λ n q r → BoundedAt q r (f n) (𝔠 n)` · `Saturated X ε = (p : ℕ → ℕ) → Poly p → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν × ((n : ℕ) → X n (p n) (ε n (p n) ℚ.+ ν n))` · `boundedᶠ⇒boundedᴺ : (ε : ℕ → ℕ → ℚ) → Boundedᶠ ε → Boundedᴺ ε`
18. `HitsAt : {A B : Iface} → ℕ → ℚ → Proc A B → Proc B (B ⊗ᴵ Ωᴵ) → Set₁` (`= BoundedAt q r (μ 𝒫.∘ f) (flagReader B)`) · `Hitsᴺ : {A B : ℕ → Iface} → ((n : ℕ) → Proc (A n) (B n)) → ((n : ℕ) → Proc (B n) (B n ⊗ᴵ Ωᴵ)) → (ℕ → ℕ → ℚ) → Set₁` (`= Boundedᴺ (λ n → μ n 𝒫.∘ f n) (λ n → flagReader (B n)) ε`)
19. `hitsᵘ : {B : Iface} (report : Neg B → Pos B → Bool) (u : Proc unitᴵ B) (q : ℕ) {r : ℚ} → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → Upper (runᴹ u (watchFrom report false d)) r) → HitsAt q r u (monitorᴹ report)`
20. `hits⇒bounded : {B : Iface} (report : Neg B → Pos B → Bool) → (P : Protocol unitᴵ B) (q : ℕ) {r : ℚ} → HitsAt q r (morphism P) (monitorᴹ report) → (d : Strat (Neg B) (Pos B)) → asks≤ q d → Pr P (watchFrom report false d) ℚ.≤ r`
21. `PreservesValue : Systems LedgerIf^ω → Set₁` · `PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴸ` · `auditMonitorᶠ n = monitorᴹ (Watched.reportsLoss n t)`
22. `preservesValue⇒saturated : (R : Systems LedgerIf^ω) {ε : ℕ → ℕ → ℚ} → Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ ε → Saturated (λ n q r → (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ q d → Pr (R n) (auditWatch n d) ℚ.≤ r) ε`
23. `TruthfulAudit : (R : Systems LedgerIf^ω) → ((n : ℕ) → St (R n) → Bool) → Set` · `TruthfulAudit R bad = (n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → PrHit (R n) (bad n) d ℚ.≤ Pr (R n) (auditWatch n (Watched.withAudits n d))`
24. `preserves-value-transfer : (a V : ℕ) (R : Systems LedgerIf^ω) → SerInj → R ≈ᶠᴺ Ideal a V → PreservesValue (genesisTotal V) R`
25. `ledger-uc-to-hit-family : SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool) → R ≈ᶠᴺ Ideal a V → TruthfulAudit (genesisTotal V) R badR → BoundedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))`
26. `ledger-hit-family-negligible : SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool) → R ≈ᶠᴺ Ideal a V → TruthfulAudit (genesisTotal V) R badR → (p : ℕ → ℕ) → Poly p → Σ[ f ∈ (ℕ → ℚ) ] Negligible f × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)`
27. `ideal-spends-genesis : (a V n : ℕ) → Pr (Ideal a V n) (Live.spend a V n) ≡ 1ℚ × ((h : Ledger.Hash n) → Live.moved a V n h ≡ (((h , 0) , (a , V)) ∷ [] , []))`
28. `ledger-preserves-value-from-hash : (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≈ᶠᴺ oracle^ω → PreservesValue (genesisTotal V) (Realᴴ hash inputConsuming (genesisAt a V))`
29. `record State : Set (o ⊔ ℓ) where field obj : Obj; point : unit ⇒ obj` · `record Machine (A B : Obj) : Set (o ⊔ ℓ) where field state : State; step : St ⊗₀ A ⇒ St ⊗₀ B` (`St = obj state`)
30. `_∘ᴹ_ : Machine B P → Machine A B → Machine A P` · `g ∘ᴹ f = mk (state g ⊛ state f) (onL (step g) ∘ onR (step f))`
31. `record _≲_ {A B : Obj} (f g : Machine A B) : Set (ℓ ⊔ e) where field θ : St f ⇒ St g; θ-pure : Pure θ; θ-point : θ ∘ point (state f) ≈ point (state g); θ-step : θ ⊗₁ id ∘ step f ≈ step g ∘ θ ⊗₁ id`
32. `_≈ᴹ_ : Machine A B → Machine A B → Set (o ⊔ ℓ ⊔ e)` · `_≈ᴹ_ = EqC.EqClosure _≲_`
33. `record Protocol (A B : Iface) : Set₁ where field St : Set; init : St; step : St → Neg B → Calls A (St × Pos B)` · `morphism : Protocol A B → 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]` · `data MSt : Set where idle : St P → MSt; wait : (Pos A → Calls A (St P × Pos B)) → MSt`
34. `𝔾ᵒ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)` (opaque) · `sealᵒ : 𝔾ᵒ ≡ 𝒢ₚᴹ 0ℓ` · `procᵒ : {A B : Iface} → Proc A B → ifaceᵒ A G.⇒ ifaceᵒ B` · `unprocᵒ : {A B : Iface} → ifaceᵒ A G.⇒ ifaceᵒ B → Proc A B` · `≈ᴹ⇒≈ᵒ : {A B : Iface} {f g : Proc A B} → 𝒢ₚ 0ℓ [ f ≈ g ] → procᵒ f G.≈ procᵒ g` · `≈ᵒ⇒≈ᴹ : {A B : Iface} {f g : ifaceᵒ A G.⇒ ifaceᵒ B} → f G.≈ g → 𝒢ₚ 0ℓ [ unprocᵒ f ≈ unprocᵒ g ]` · `unprocᵒ-∘ : {A B C : Iface} (g : Proc B C) (f : Proc A B) → 𝒢ₚ 0ℓ [ unprocᵒ (procᵒ g G.∘ procᵒ f) ≈ M._∘_ g f ]`
35. `Certified : {A B : Iface} → ℕ → Proc A B → Set` · `QB : {A B : Iface} → ℕ → Proc A B → Set₁` · `QB {A} {B} c M = Σ[ N ∈ Proc A B ] Certified c N × (N S.≈ᴹ M)`
36. `StateTest : Proc A B → Set` · `StateTest M = MC.St M → Bool` · `_▷_ : Proc A (B ⊗ᴵ Ωᴵ)` (in `module _ {A B : Iface} (M : Proc A B) (P : StateTest M)`)
37. `stateRead : {A B : Iface} (Y : Iface) (M : Proc A B) → StateTest M → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool` · `stateRead {B = B} Y M P = readRun Y (M ▷ P) (flagReader B)` · `StateBoundedAt : {A B : Iface} → ℕ → ℚ → (M : Proc A B) → StateTest M → Set₁` · `StateBoundedAt {B = B} q r M P = BoundedAt q r (M ▷ P) (flagReader B)`
38. `stateLift : {B : Iface} (M : Proc unitᴵ B) (P : StateTest M) (q : ℕ) {r : ℚ} → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → Upper (runᴹ (M ▷ P) (flagStrat d)) r) → StateBoundedAt q r M P`
39. `StateSafe : (R : Systems LedgerIf^ω) → ((n : ℕ) → St (R n) → Bool) → (ℕ → ℕ → ℚ) → Set₁` · `preservesValue⇒stateSafe : (R : Systems LedgerIf^ω) (bad : (n : ℕ) → St (R n) → Bool) {ε : ℕ → ℕ → ℚ} → Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ ε → TruthfulAudit R bad → StateSafe R bad (λ n q → ε n (q ℕ.+ q))` · `ledger-uc-to-state : SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool) → R ≈ᶠᴺ Ideal a V → TruthfulAudit (genesisTotal V) R badR → StateSafe R badR (λ n q → εᴸ n (q ℕ.+ q))`
40. `BoundedHitᴺ : (ℕ → ℕ → ℚ) → Set` · `hitᴺ⇒stateᴺ : (ε : ℕ → ℕ → ℚ) → BoundedHitᴺ ε → StateBoundedᴺ (λ n → morphism (P n)) T ε` · `stateᴺ⇒hitᴺ : (ε : ℕ → ℕ → ℚ) → StateBoundedᴺ (λ n → morphism (P n)) T ε → BoundedHitᴺ ε`

## 2. The proof path, ideal birthday bound → `ledger-hit-family-negligible`

`p` is the caller's polynomial and `d₀` the caller's strategy with
`asks≤ (p n) d₀`. `ε` is the schedule inside the premise
`em : R ≈ᶠᴺ Ideal a V`.

1. **`birthday-≤`** (`ProbabilisticLogic.Distribution.Uniform.Birthday`, module
   parameter `n` = hash width): `∀ q → Γ 1 q ≤ birthday-bound q`, with
   `birthday-bound q = fromℕ (q ℕ.* q ℕ.+ q) * inv-pow-2 n`,
   `Γ t j = fromℕ (sumN t j) * ε` and `sumN 1 q = 1 + 2 + … + q`. The
   potential itself is exact, `birthday : Γ 1 q ≡ q(q+1)/2ⁿ⁺¹` (Gauss,
   `sumN-closed`); the published schedule is twice it.
2. **`cert : HitCert Sys₀ Bad birthday-bound`**
   (`Examples.ChimericLedger.Birthday`). The potential is
   `φ m st = Φ m (Hs (proj₂ st))`, with
   `Φ m L = bool→ℚ (dup L) + Γ (length L) m`
   (`ProbabilisticLogic.Distribution.Uniform.Duplicate`). Here `m` is the
   *remaining* query budget.
3. **`hit-bounded`** (`Protocol.Safety`): `BoundedHit P Bad ε`, via `badProb⊥-bounded` and
   `hit≤badProb⊥`. The strategy's cap is the argument of `birthday-bound`.
4. **`target`** (`Birthday`):
   `TrajectoryLossBounded inputConsuming (genesis h₀ a₀ V) birthday-bound`, which
   is `BoundedHit (Sys vr s₀) (badTotal s₀)` (`Observable`).
5. **`auditWatch-bounded`** (`Observable`):
   `TrajectoryLossBounded → AuditLossBounded` at the same `q`, pointwise through
   `auditWatch-sound : Pr P (auditWatch (total s₀) d) ≤ℚ PrHit P Bad d`.
6. **`ideal-bounded`** (`Property`):
   `SerInj → (n : ℕ) → Bounded (Ideal n) (auditWatch (genesisTotal V) n) (εᴸ n)`.
   It is `auditWatch-bounded` of `Birthday.target n (ser n) (h₀ n) (si n) a V`.
   So hash width = security parameter, and `birthday-bound` at width `n` is
   `εᴸ n` with no cast.
7. **`≈ᶠ-runs`**, inside `preserves-value-transfer`, at level `n` with
   `q := (p′ n + 1 , m≤n+m 1 (p′ n))` and strategy `auditWatch … n d`, admitted
   by `asks≤-watch` of `asks≤-mono (m≤m+n (p′ n) 1) d ad`. This yields
   `≈ₚ[ ε n (p′ n + 1) ]` between the direct runs of `R n` and `Ideal a V n`.
   `p′` is the polynomial that `PreservesValue`'s `Boundedᴺ` receives. The
   `+ 1` is there only because `≈ᶠ-runs` takes a positive cap.
8. **`upper-run`** on `ideal-bounded a V si n (p′ n) d ad`:
   `Upper (runᴹ (morphism (Ideal a V n)) (auditWatch … d)) (εᴸ n (p′ n))`. The
   ideal bound is read at the context's own cap.
9. **`upper-≈[]`** (`ProbabilisticLogic.Dp.Advantage`):
   `Upper (runᴹ (morphism (R n)) (auditWatch … d)) (εᴸ n (p′ n) + ε n (p′ n + 1))`.
10. **`hitsᴸ … R n (p′ n)`**, which is `hitsᵘ` with `q := p′ n`. Steps 7-9
    discharge its premise at `asks≤ (p′ n) d`. For an arbitrary context at cap
    `p′ n`, `monitor-flag` rewrites the monitored process to the flag wire of
    `accᴹ`, and `stateLift` lifts at the same cap: the flag ask is paid in the
    extracted strategy's certificate (`FlagCert`, count + 1), not in the cap.
    `preserves-value-transfer` packages the result with
    `ν n := ε n (p′ n ℕ.+ 1)`, negligible by
    `neg (λ n → p′ n + 1) (poly-+ Pp (poly-const 1))`. This is
    `PreservesValue (genesisTotal V) R` with no cast.
11. **`preservesValue⇒stateSafe`** at `ε := εᴸ`, called from
    `ledger-uc-to-state`. It applies `preservesValue⇒saturated` at
    `p″ := λ n → p n + p n` and `poly-+ Pp Pp`; `p″` is the `p′` of steps 7-10.
    `hits⇒bounded` runs at the same cap (`Y = unitᴵ`, `E = stratTest`,
    `m = λᴵ⇐`, `c′ = 0`), so nothing is spent coming back. For each `n` it
    instantiates the strategy as `withAudits n d₀`, admitted by
    `asks≤-withAudits n (p n) d₀ ad : asks≤ (p n + p n) …`, and chains with
    `truthful n d₀`. `TruthfulAudit` has no cap, so `d₀` passes unchanged. The
    strategy-level bound is lifted to `StateSafe` by `hitᴺ⇒stateᴺ` at
    `idleTest`.
12. **`ledger-uc-to-hit-family`** reads it back with `stateᴺ⇒hitᴺ` at
    `idleTest`. Both conversions are `saturated-map`, so `ν` is unchanged:
    `PrHit (R n) (badR n) d₀ ≤ εᴸ n (p n + p n) + ν n`.
13. **`ledger-hit-family-negligible`**:
    `f := λ n → εᴸ n (p n ℕ.+ p n) ℚ.+ νₚ n`, negligible by
    `Negligible-+ (εᴸ-negligible (λ n → p n ℕ.+ p n) (poly-+ Pp Pp)) neg`.
    `εᴸ-negligible` is `negligibleBound-inv-pow-2` (`UC.Approximate.Decay`)
    with width bound `≤-refl`.

Quantifier order of the endpoint:
`∀ si R badR em truthful → ∀ p → Poly p → ∃ f. Negligible f × ∀ n → ∀ d → asks≤ (p n) d → …`,
i.e. `∀ p. ∃ ν. ∀ n. ∀ experiment at p(n)`, with the experiment a `Strat`.
The only context-uniform statements on the path are `PreservesValue R`
(step 10) and `StateSafe` (step 11). The emulation is read only at strategy
contexts (step 7), never at a monitored context.

### Pinned numbers

| Quantity | Code |
|---|---|
| `εᴸ(n,q) = (q² + q)·2⁻ⁿ` | `εᴸ n q = fromℕ (q ℕ.* q ℕ.+ q) ℚ.* inv-pow-2 n` (`Property`) |
| `fₚ(n) = εᴸ(n, p(n) + p(n)) + νₚ(n)` | `λ n → εᴸ n (p n ℕ.+ p n) ℚ.+ νₚ n` (`ledger-hit-family-negligible`) |
| `νₚ(n) = ε(n, (p(n) + p(n)) + 1)` | step 10's `ν` at `p′ = p″`, with `ε` the first component of `em`, carried unchanged by steps 11-12 |

Fully unfolded: `fₚ(n) = ((2p(n))² + 2p(n))·2⁻ⁿ + ε(n, 2p(n) + 1)`.

- The doubling is `withAudits`' charge (step 11), and it reaches **both** the
  ideal term and the emulation term.
- The `+ 1` reaches **only** the emulation term. It is `≈ᶠ-runs`' positive cap
  (step 7). The monitor's flag ask is charged to the extracted strategy's
  certificate, not to the cap (step 10).

## 3. Where state events attach

**Stated over admitted contexts:**

- `_≈ᶠ[_]_` and `_≈ᶠᴺ_` (rows 2-3) range over seal contexts `W E m` with
  `Image forget c E` and `Image forget r′ m` (rates `ℕ⁺`).
- `BoundedAt`, `Boundedᶠ`, `Boundedᴺ`, `HitsAt`, `Hitsᴺ`, `PreservesValue`,
  `StateBoundedAt`/`ᶠ`/`ᴺ` and `StateSafe` (rows 15-18, 21, 37, 39) range over
  machine contexts `Y E m` with `QB c E`, `QB c′ m` and
  `scale c (positive c′) ≤ q` (counts `ℕ`). This admission notion (`QB`,
  row 35) is different from the seal's `Image forget`.

**Stated only over `Strat`:** `Bounded`, `BoundedHit`, `BoundedHitᴺ`,
`_≈adv[_]_` (`Protocol.Observe`), `PrHit`, `hitFrom`, `TruthfulAudit`,
`ideal-bounded`, `Birthday.target`, `auditWatch-sound`/`-complete`/`-bounded`,
the conclusions of `≈ᶠ-runs`, `hits⇒bounded` and `preservesValue⇒saturated`,
and both claim-2 endpoints (rows 25-26). The mixed rows are `hitsᵘ` and
`stateLift` (premise over `Strat`, conclusion over contexts), and
`hits⇒bounded`, `stateBounded⇒hit` (the reverse).

**How a state event is read at a context.** The state predicate is turned into
an interface event by the flag-wire machine `M ▷ P` (row 36), and the context's
test is wrapped by `flagReader`. No state is projected out of a composite, and
no context-level statement reads a state directly: every reading goes through
the extra `Ωᴵ` port. Three consequences:

- *Sampling boundary.* `▷` samples at the initial state and at every completed
  activation (an answer on `B`). At a protocol image, a `B`-answer comes only
  from `drive` returning to `idle`, so a suspended `wait` state is never
  sampled. `idleTest` is the default boundary interpretation, and any test
  agreeing with `Bad` on `idle` gives the same reading (`bd`, row 40).
- *Transport.* A predicate lives on one representative's state type. Machine
  equality does not transport it: an erased state component gives no descent
  (`HitTests.ghost-no-descent`).
- *Event convention.* `flagReadᴹ` waits for the verdict, so the reading is the
  completed-run event of row 11, not prefix reachability. The lift (row 38)
  depends on this. A strategy that read the flag early and then continued would
  not be dominated by `flagStrat` of its `B`-part.
