# Monitor-as-flag-wire spike (QUALITY-REVIEW-R2b #1, stage 2 crux)

Verdict: **GO — landed** on branch `stage2` (base `d4b7eb00`): stage 1 at `83169f7e`, the
crux and agreement at `464ce070`, `hitsᵘ` from `stateLift` with the monitor-side
development deleted at `8f59c57f`, the sharpened caps at `6bde8f85`. The spike module is
deleted; what it proved now lives in the library:

| spike name | home |
|---|---|
| `eventRun-flag`, `hits⇒flag`, `flag⇒hits` | gone: `HitsAt q r f μ` is now *defined* as `BoundedAt q r (μ ∘ f) (flagReader B)` (`UC.Quantitative.EventLift`), and `flagReader` sits beside `flagReadᴹ` in `UC.Machine.Monitor`; `compileᴹ`/`eventRun` are retired |
| `settle`, `accᴹ`, `reported`, `monitor-flag` | `UC.Machine.Monitor`, beside `monitorᴹ` |
| `flag-agree` | `UC.Machine.Monitor.Agree` |
| `agree` (the corollary) | `UC.Quantitative.EventLift` — it needs `StateEvent.Agree`, which imports `Monitor.Agree` |
| `hits-flag` | `UC.Quantitative.EventLift.hitsᵘ`, now at premise `asks≤ q` |
| `∨-again` | `Data.Bool.Properties.Ext.∨-idemˡ` |

The rest of this note is the spike's record as written.

Code (deleted): `src/CategoricalCrypto/UC/Machine/StateEvent/Spike/MonitorFlag.agda` (242 lines,
`--safe --without-K --guardedness`, no hatches, unwired, 17–32 s warm). Base `fe5593af`.
No existing file edited.

## 1. Stage 1 (committed in the spike)

```agda
eventRun-flag : eventRun Y f μ E m ≈ₚ readRun Y (μ 𝒫.∘ f) (flagReader B) E m
hits⇒flag     : HitsAt q r f μ → BoundedAt q r (μ 𝒫.∘ f) (flagReader B)
flag⇒hits     : BoundedAt q r (μ 𝒫.∘ f) (flagReader B) → HitsAt q r f μ
```
These use the review's scratch proof as written (two `assoc`s plus `ctxRun-∘`, its first consumer).

## 2. The crux: `monitor-flag`

The simulation belongs on the **process side**. `Watch.watchᴹ` is the wrong place to look:
it collapses reader ∘ test ∘ monitor on the *test* side. Stage 1 moves the monitor next to
the process, and there the composite has two machines, not five. The spike avoids a test on
a 𝒢-composite state by defining the monitored process by hand:

```agda
accᴹ : (report : Neg B → Pos B → Bool) (u : Proc A B) → Proc A B   -- state St u × MonSt B
reported : StateTest (accᴹ report u)                               -- = proj₁ ∘ proj₂
monitor-flag : 𝒫._≈_ (monitorᴹ report 𝒫.∘ u) (accᴹ report u ▷ reported report u)
```
`accᴹ` is `u` followed by `monitorᴹ`'s bookkeeping (`settle`): it records the pending query
and, on a `B`-answer, updates `acc ∨ report q b`. It works at **any** `A`, not just `unitᴵ`.

- **Equivalence needed:** `𝒫._≈_` (= `S.≈ᴹ`), the relation `T₁-resp-≈` and `runᴹ-resp-≈ᴹ`
  accept. The proof is `compose-raw≈∘ᴳ` ⁻¹ ○ `collapseᵀ` ○ `mk-cong col-step` ○ one
  functional simulation `col≲flag`, with ψ (mq , s) = ((s , mq) , proj₁ mq). No zigzag
  and no `EventSim` are used; `▷-≲` / `stateBounded-resp-≈ᵉ` are not needed either.
  About 95 lines including `accᴹ`, under the 60-line target for the collapse proper
  (`upass`/`upump`/`col-step` ≈ 35).
- **Pointwise agreement:** yes, on the image of ψ, which is exactly the set of reachable
  states. ψ sets the flag to the accumulator. At a completed answer `▷` samples
  `f ∨ acc′`, with `f = acc` and `acc′ = acc ∨ report q b`. So the one non-definitional
  step is `a ∨ (a ∨ b) ≡ a ∨ b` (`∨-assoc` + `∨-idem`). Monotonicity is never used
  separately; it is this absorption. `▷` has states outside ψ's image (flag ≠ acc), so the
  match is a simulation into `▷`, not a bijection.
- Both sides update only at a completed `B`-answer. An `A`-message leaves `acc` and the flag
  alone. An answer with no pending query is `botₚ` on both sides, because `settle` mirrors
  `monitorStep`.

## 3. Strategy agreement

```agda
flag-agree : runᴹ (accᴹ report u ▷ reported report u) (flagStrat d)
           ≈ₚ runᴹ u (watchFrom report false d)
```
This is proved directly, by induction on `d` with the invariant `f ≡ a` (20 lines). It does
not go through `Monitor.Agree.agree`. As a result, `agree` itself becomes a 4-line
corollary: `eventRun-flag`, then `monitor-flag` under `runᴹ-resp-≈ᴹ`, then
`StateEvent.Agree.stateRead-agree`, then `flag-agree`.

## 4. Derivation

```agda
hits-flag  : (q : ℕ) {r : ℚ}
           → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → Upper (runᴹ u (watchFrom report false d)) r)
           → HitsAt q r u (monitorᴹ report)
hitsᵘ-flag : -- `hitsᵘ`'s statement verbatim (premise at `asks≤ (q ℕ.+ 1)`)
hitsᵘ-flag q h = hits-flag q λ d a → h d (asks≤-mono (ℕP.m≤m+n q 1) d a)
```
`hits-flag` = `flag⇒hits` ∘ `upper-≈ (monitor-flag under T₁)` ∘ `stateLift accᴹ reported q`
with `flag-agree` rewriting the premise.

**Cap/error shape.** The two developments both charge one extra unit, but for different
reasons. `FlagCert` charges `k + 1` for the flag ask, and the flag ask is also one more ask
of `flagStrat d`. So `stateLift` reads its premise at the context's own cap `q`. `Cert`
charges `c + 1` for the accumulator's potential (`pend`), and this unit has no counterpart
in the watched strategy. So `hitsᵘ` pays it in the premise as `q + 1`. In other words, the
`+1` in `hitsᵘ` comes from how the monitor-side certificate is built, not from the problem.
There is no error-shape difference: both lifts are exact (`Upper … r`, no slack).
`Cert` vs `FlagCert`: `FlagCert` survives.

## 5. Stage 2 as a work package

**Survives:** the state-event side, i.e. `StateEvent/Lift :: FlagCert`, `FlagShaped`,
`shaped-run`, `flagSkeleton`, `flag-slide`, `stateLift`, and `Dominated.Refine`.

**Deleted** (counted at `fe5593af`; consumers checked by grep):

| file :: names | LOC |
|---|---|
| `UC/Quantitative/EventLift/Cov.agda` (whole: `Cert`, `covCtx`, `qb-closedᴹ`) | −303 |
| `UC/Machine/Monitor/Slide.agda` (whole: `relay-slide`, `watch-collapsed`, `watch-resp-≈`, `closedᴹ`, `compiled-slide`; only consumer is Cov) | −184 |
| `UC/Seam/EventTransfer.agda` (whole: watched `Cov`, `runFwdᵂ`; consumers are Dominated + Cov only) | −97 |
| `UC/Machine/Dominated.agda :: CovCtx`, `eventSkeleton` (+ `ET` import) | −51 |
| `UC/Machine/Monitor/Agree.agda :: monStep`, `monᴹ`, `mon-wire`, `Watch`, `WSt`, `Reach`, `Span`, `tower`, `agree` (lines 214–504; `stratTest`, `Read`, `m₀` stay) | −291 |
| `UC/Quantitative/EventLift.agda :: openedᴹ`, `eventRun-closed`, `eventDominatedᶜ/ᵘ`, old `hitsᵘ` body | −61 |
| **total** | **≈ −987** |

**Added:** `accᴹ`/`reported`/`monitor-flag` (≈ 95), `flag-agree` (≈ 25), stage-1 lemmas
(≈ 15), `hitsᵘ` (≈ 10), `agree` (≈ 5), for **≈ +150**. Suggested homes: `accᴹ` and
`monitor-flag` in a new `UC/Machine/Monitor/Flag.agda`; the stage-1 lemmas and `agree` in
`Monitor.Agree`, replacing the deleted block. Net is **≈ −830**, well beyond the review's
−250..−400. The reason is that `Monitor.Agree`'s five-machine `Watch`/`Span` and the whole
`Seam.EventTransfer` go with the monitor certificate.

Further candidate, not measured: once `EventTransfer` is gone, `Seam.Transfer`'s generic
`Covᴵ upd Leaf` has only the identity instance (`runFwd`). Its index parameter could
collapse.

**Statement shape changes** (all strictly stronger or equal):
- `hitsᵘ`: the premise could become `asks≤ q d` (keeping `q ℕ.+ 1` is also free, via
  `hitsᵘ-flag`). If it is sharpened:
  - `EventBounds/Transport :: hitsTransport` gets `Near … q` / `HitsAt q r I`, instead of
    `q ℕ.+ 1`.
  - `hitsTransportᴺ` gets error `εI n q ℚ.+ δ n q`, instead of `εI n (q ℕ.+ 1)`, and drops
    `poly-+ pp (poly-const 1)`.
  - `ChimericLedger/Property :: hitsᴸ` and `ideal-preserves-value` drop `q ℕ.+ 1`.
- With stage 1 (`HitsAt q r f μ = BoundedAt q r (μ 𝒫.∘ f) (flagReader B)`), `hitsTransport`
  is `transport-near` at `accᴹ`, up to `monitor-flag`. That is a candidate for a second
  merge.
- `eventRun`/`compileᴹ` retire or become a one-line abbreviation (stage 1). `agree` keeps
  its statement.

**Risks:** `ChimericLedger` and `Transport` run at `-M8G`; their consumers of the sharpened
cap need re-proof, which is arithmetic only. `Monitor.Agree`'s header and the doc
citations of `Watch`/`compiled-slide` (`docs/event-bounds-in-setup.md`, Cov's header
claims) must be rewritten.

**Estimate:** 1 session to land with the cap kept at `q + 1`, plus about 0.5 session to
sharpen the cap through Transport and ChimericLedger.
