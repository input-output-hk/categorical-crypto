# Flag-wire spike: `M ▷ P` as the state-event construction (WP2)

This spike is the go/no-go for route B of `docs/state-event-contract.md` §3: a flag-wire
machine instead of instrumenting the closed network. Code:
`src/CategoricalCrypto/UC/Machine/FlagWire.agda` (347 lines, `--safe --without-K
--guardedness`, no postulates or holes, not wired into the root). Base: `protocol-rewrite`
at `28d516a6`. No existing file was edited.

## Definitions (verbatim)

The machine, at the concrete `Dₚ` model (`Proc = 𝒢ₚ`-hom, `MC = Machines.Core (𝒱ₚ 0ℓ)`):

```agda
module _ {A B : Iface} (M : Proc A B) (P : MC.St M → Bool) where

  sample : Bool → MC.St M × (Neg A ⊎ Pos B) → (MC.St M × Bool) × (Neg A ⊎ (Pos B ⊎ Bool))
  sample f (s , inj₁ a) = (s , f) , inj₁ a
  sample f (s , inj₂ b) = (s , f ∨ P s) , inj₂ (inj₁ b)

  ▷step : (MC.St M × Bool) × (Pos A ⊎ (Neg B ⊎ ⊤))
        → Dₚ ((MC.St M × Bool) × (Neg A ⊎ (Pos B ⊎ Bool)))
  ▷step ((s , f) , inj₁ a)        = mapₚ (sample f) (MC.step M (s , inj₁ a))
  ▷step ((s , f) , inj₂ (inj₁ b)) = mapₚ (sample f) (MC.step M (s , inj₂ b))
  ▷step ((s , f) , inj₂ (inj₂ _)) = returnₚ ((s , f) , inj₂ (inj₂ f))

  ▷state : MC.State
  ▷state = record
    { obj     = MC.St M × Bool
    ; point   = λ x → mapₚ (λ s → s , P s) (MC.point (MC.state M) x)
    ; discard = λ p → MC.discard (MC.state M) (proj₁ p)
    }

  infixl 8 _▷_

  _▷_ : Proc A (B ⊗ᴵ Flagᴵ)
  _▷_ = MC.mk ▷state ▷step
```

The flag is sampled only when `M` answers on `B` (a completed activation) and at the
initial state, which may be effectful: `point` maps the test over `M`'s own point. The
flag port is `UC.Machine.Monitor.Flagᴵ = Bool ⇿ ⊤`, the same ticked shape as `Ωᴵ`.
Answering a flag query leaves `M`'s state alone.

Forgetting the port:

```agda
-- A machine that never asks its flag port; a flag answer is off-protocol.
dropF : {S X Y : Set} → S × (X ⊎ (Y ⊎ Bool)) → Dₚ (S × (X ⊎ Y))
dropF (s , inj₁ x)         = returnₚ (s , inj₁ x)
dropF (s , inj₂ (inj₁ y))  = returnₚ (s , inj₂ y)
dropF (s , inj₂ (inj₂ _))  = botₚ

unflag : {A B : Iface} → Proc A (B ⊗ᴵ Flagᴵ) → Proc A B
unflag {A} {B} N = MC.mk (MC.state N) stepU
  where
  stepU : MC.St N × (Pos A ⊎ Neg B) → Dₚ (MC.St N × (Neg A ⊎ Pos B))
  stepU (s , inj₁ a) = MC.step N (s , inj₁ a) >>=ₚ dropF
  stepU (s , inj₂ b) = MC.step N (s , inj₂ (inj₁ b)) >>=ₚ dropF
```

The closing experiment, and the kernel-level completed-run hit:

```agda
flagStrat : {B : Iface} → Strat (Neg B) (Pos B) → Strat (Neg B ⊎ ⊤) (Pos B ⊎ Bool)
flagStrat (out _)    = ask (inj₂ tt) [ (λ _ → out false) , out ]
flagStrat (ask q k)  = ask (inj₁ q) [ flagStrat ∘ k , (λ _ → out false) ]
flagStrat (coin μ k) = coin μ (flagStrat ∘ k)
  hitK : Bool → MC.St M → Strat (Neg B) (Pos B) → Dist⊥ Bool
  hitK acc m (out _)    = return⊥ acc
  hitK acc m (ask q k)  = K m q >>=⊥ λ mr → hitK (acc ∨ P (proj₁ mr)) (proj₁ mr) (k (proj₂ mr))
  hitK acc m (coin μ k) = μ >>=ᴹ λ b → hitK acc m (k b)

  bump : Bool → MC.St M × Pos B → (MC.St M × Bool) × (Pos B ⊎ Bool)
  bump f mr = (proj₁ mr , f ∨ P (proj₁ mr)) , inj₁ (proj₂ mr)

  K▷ : MC.St M × Bool → Neg B ⊎ ⊤ → Dist⊥ ((MC.St M × Bool) × (Pos B ⊎ Bool))
  K▷ (m , f) (inj₁ q) = Dmap⊥ (bump f) (K m q)
  K▷ (m , f) (inj₂ _) = return⊥ ((m , f) , inj₂ f)
```

The context-level reading and bound:

```agda
flagReader : (Y B : Iface) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc (Y ⊗ᴵ (B ⊗ᴵ Flagᴵ)) Ωᴵ
flagReader Y B E = flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ a⇐ᴵ)

stateRead : {A B : Iface} (Y : Iface) (M : Proc A B) → (MC.St M → Bool)
          → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool
stateRead {B = B} Y M P E m = ctxRun Y (flagReader Y B E) m (M ▷ P)

-- `UC.Machine.EventBounds.BoundedAt`'s telescope and admission, verbatim.
StateBoundedAt : {A B : Iface} → ℕ → ℚ → (M : Proc A B) → (MC.St M → Bool) → Set₁
StateBoundedAt {A} {B} q r M P =
    (Y : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A)) {c c′ : ℕ}
  → QB c E → QB c′ m → scale c (positive c′) ℕ.≤ q → Upper (stateRead Y M P E m) r
```

## What was proved

All of the following typecheck green.

- **(a) Forgetting.** `unflag-▷ : unflag (M ▷ P) S.≲ M`, via `Machines.Pointwise.simFn proj₁`.
  So `unflag (M ▷ P) ≈ᴹ M` holds up to simulation, not definitionally: the state objects
  differ (`St M × Bool` against `St M`). `unflag` is a machine-level restriction, not a
  `𝒢ₚ` composite. A `𝒢ₚ` "forget the port" morphism `B ⊗ᴵ Flagᴵ → B` cannot be a
  `wireᴹ`, because the `Bool` answer has no `Pos B` image. It would be a partial,
  stateless machine, and relating it to `unflag` would take one trace collapse (see
  "Owed").
- **(b) Completed-run reading.** This comes in two layers.
  - `flagRun` is generic over any closed `M` with a step kernel `K` and
    `StepSettles M K` (`Protocol.Machine.Raw`). Past a depth, the flag-wire run at
    `flagStrat d` has cumulative mass `E⊥ (σ₀ >>=⊥ λ m → hitK (P m) m d)` at either
    verdict. The proof is `ker▷` (the ▷ machine settles on `K▷`), `rawPr`, and
    `flag-hit`, where `flag-hit` is the kernel identity
    `runWith⊥ K▷ (m , acc) (flagStrat d) = hitK acc m d` read by `E⊥`.
  - `prHit-agree` covers protocol images: for any `P : Protocol unitᴵ B` and any
    `Bad : St P → Bool`,
    `cum (n + i) (runᴹ (morphism P ▷ idleTest) (flagStrat d)) (indᵇ true) ≡ PrHit P Bad d`.
    This is an exact equality past a depth, not a domination. `upper-hit` and
    `hit-upper` turn it into `PrHit ≤ r ⇔ Upper (runᴹ … (flagStrat d)) r`, so
    `BoundedHit P Bad ε` at cap `q` is the flag-wire bound at the flagged strategies,
    and `asks≤-flag` sends cap `q` to cap `q + 1`.
  - The ledger's `badTotal s₀ : LState × S → Bool` is a `St (Sys vr s₀) → Bool`
    (`Observable.agda:68`), so it is an instance of `Bad`. The instance was not
    elaborated separately, to avoid importing `Examples/**`.
  - The boundary interpretation that WP2 asks for is: sampling sites = `B`-outputs,
    and state reading = `idleTest` (`Bad` on `idle s`, `false` on `wait _`). A
    `B`-output of `morphism P` only ever comes from `drive`'s `ret`, which lands in
    `idle`. So `wait` states are never sampled, and the proof never looks at
    `idleTest`'s `wait` clause. Any value there gives the same theorem, which settles
    WP3's "irrelevant internal predicate" case. Every other WP3 distinguishing case
    carries over from `PrHit`, because the result is an equality with it:
    initially-bad (`point` samples `Bad (init P)`), a hit after one activation, a
    deadlock after a bad activation (both sides weigh `dead` as 0), and coins.
- **(c) Compatible simulations lift.** `▷-≲ : (M ▷ P) S.≲ (N ▷ Q)`, from
  `σ : M S.≲ N` and `compat : ∀ s → P s ≡ Q (ϕ σ s)`, where `ϕ = UC.Machine.Run.ϕ`
  is the existential `fn` of `θ-pure`. This is WP1's `EventSimulation` exactly.
  Sampling-boundary compatibility is automatic, because both sides sample at the same
  interface event (a `B`-answer), and a simulation preserves the step's output letter.
  Composition is `S.≲-trans` with `compat` composed. Zigzags lift generator by
  generator, and only along compatible generators.
- **Seal.** `sealed▷ M P = gradedᵒ (M ▷ P) : ifaceᵒ A ⇒ ifaceᵒ B ⊗₀ ifaceᵒ Flagᴵ`
  typechecks with no `unfolding`. This is the smallest interface change (one ticked
  Boolean port, on the right as `compileᴹ` has it), and the existing exported coercion
  `gradedᵒ` already covers it.

## The three UNVERIFIED points of `state-event-contract.md` §3

1. **Can the seal express the flag port without opening `opaque`?** Yes. `B ⊗ᴵ Flagᴵ`
   is an `Iface`, `⊗ᵒ` equates its image with the seal's tensor, and `gradedᵒ` is the
   coercion (`sealed▷`). The state `P` reads stays on the `Proc` side, before `procᵒ`.
   That is the point: under the seal a state is never read, only a port.
2. **How the G-construction lays out the composite state.** I confirmed this by
   reading the code; I did not prove it again.
   - `traceᴹ A B X f = mk (state f) …` (`Machines/Trace.agda:74-75`) keeps the body's
     state.
   - `composeᴳ f g = trace (α ∘ f ⊗₁ g ∘ γ)` (`Categories/GConstruction.agda:55-56`,
     opaque). There `⊗ᵉ` pairs states (`Machines/Tensor.agda:103`), and `α`/`γ` are
     pure structural machines (state `Iˢ`).
   - `Machines.Collapse.collapseᵀ` proves that the body is `≈ᴹ` to
     `mk (state g ⊛ state f) kᴳ`.

   So a component's state survives in a composite, and at the collapsed
   representative it sits at a definite projection. That projection belongs to the
   representative, though. `≈ᴹ` is a zigzag of pure state maps, so a `≈ᴹ`-equal
   composite carries no such component, and every collapse is one more simulation
   along which predicate compatibility would be owed (candidate A's cost). Route B
   never projects: the event leaves on a port, so the `≈ᴹ`-invariance of the
   reading is `runᴹ-resp-≈ᴹ` as it stands.
3. **Does `covCtx`'s `+ 1` survive?** It survives as a *real query* rather than as
   potential slack, but the context-level lift has **not been established**.
   - The `+ 1` is now the flag ask itself. At the strategy level it is exact:
     `asks≤-flag : asks≤ n d → asks≤ (suc n) (flagStrat d)`.
   - In `covCtx` the unit repairs potential: `Cert.pend` pays for a raised
     accumulator that the context holds with no traffic. With `M ▷ P` the
     accumulator is in the process, and the context has to *ask* for it.
   - A plain `Dominated.skeleton` does not give the lift. Its premise ranges over
     every strategy at `B ⊗ᴵ Flagᴵ`, including `out true`, so no event bound can
     discharge it (`UC.Audit`'s header).
   - What is owed is an invariant on `Kctx (flagReader Y B E ∘ T₁ᴵ Y λᴵ⇒) m`. Every
     strategy extracted from its emission tree must be `flagStrat`-shaped, or
     dominated by such a strategy: the flag asked once, last, with the answer as the
     verdict. This invariant takes `CovCtx`'s place, but it has no accumulator
     potential, since the flag is read by a query that the certificate counts.
   - Whether a `qb-∘` certificate of `flagReader` comes out at rate `c + 1` or
     multiplicatively (`flagReadᴹ` issues two downward queries per tick) was not
     established. A hand-built certificate, as `Cert.certᵂ` was, is what would give
     `c + 1`.

## Superseded by the wired modules

The spike module is deleted; its content and the three owed items now live in
`UC/Machine/StateEvent.agda` (`_▷_`, `EventSim`, `unflag-▷`, `▷-≲`), `StateEvent/Read`
(`stateRead`, `StateBoundedAt = BoundedAt q r (M ▷ P) (flagReader B)` after
`Reader B B′`), `StateEvent/Agree` (`stateRead-agree`), `StateEvent/Lift` (`stateLift`:
certificate at `c + 1`, premise at cap `q`, no slack) and `StateEvent/Adequacy`
(`stateRead-hit`, exact past a depth; `hit⇒stateBounded` / `stateBounded⇒hit`). Tests:
`StateEvent/HitTests`.

**A structural caveat for WP4.** The flag event is interface-observable *at `B ⊗ᴵ Flagᴵ`*.
`UC.Audit`'s carry therefore applies to `R ▷ P` versus `I ▷ Q` only given an emulation at
the flagged interface. `R ≤UC I` at `B` does not imply it: the simulator never sees
`R`'s state. The carry is reusable as it stands, but the premise is new mathematics, in
the same place where `TruthfulAudit` sits today.

## Timings (warm, single `Checking` line, `+RTS -M8G -H2G`)

| Module | Warm wall | Note |
|---|---|---|
| `UC.Machine.FlagWire` (347 LOC) | 26.3 s, 27.3 s | budget 60 + 347/4 ≈ 147 s |
| same imports, empty body | 9.1 s | interface loading floor |
| `--profile=definitions` | 26.1 s total | 16.4 s "Miscellaneous" (loading/serialization); largest definitions `ker▷` 1.0 s, `pt` 0.8 s, `hit-upper` 0.5 s |

No existing module was instantiated (only opened), so there is no second baseline. The
first check in the fresh worktree rebuilt 195 dependencies in 225 s.

## Recommendation

**GO for WP1–3 on this route; WP4 conditional.** WP5 is not in the section I was given (it stops at WP4's heading), so its estimate below assumes it is the ledger port. The
construction is local, lives under the seal with no `unfolding`, reads `PrHit` exactly at
protocol images, and lifts compatible simulations with no extra boundary condition.

The LOC estimates below, 1,000–1,400 lines in total, are estimates only:

| Work package | Estimate | Content |
|---|---|---|
| WP1 remainder | ~150 | predicates and reindexing, compat composition, the three acceptance examples including the ghost-bit obstruction |
| WP2 remainder | ~300–400 | context `agree` analogue, `≈ᴹ`-invariance plumbing, optional `Reader` generalization |
| WP3 lift | ~300–450 | the flag-at-end extraction invariant plus a certificate at `c + 1` |
| WP4 | ~50 plumbing | new per-instance theorems for the flagged-interface emulation premise |
| WP5 | ~150–250 | ledger port |

The ~340 lines here are already spent.
