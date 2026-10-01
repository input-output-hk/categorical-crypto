# WP4 spike: transporting a state-event bound along emulation

Code: the package `src/CategoricalCrypto/UC/Machine/EventBounds/Transport.agda` (wired
into the root; `--safe --without-K --guardedness`, no escape hatches). Base `94ed4375`.
The spike module for §1 (c) was deleted; see there.

## Verdict

**GO for a narrowed WP4, estimated at 250–400 lines.** The transport theorem itself is
short, and all of it is proved here. The expensive part is *producing* its premise:
an emulation at `B` never produces it (§2). So WP4 should:

1. make the schema generic over a `Reader` with an adequacy pair (§3) — **done**, the
   package `UC.Machine.EventBounds.Transport` (§4 item 1);
2. build one producer of the flagged premise for systems with a simulator (§4) — not
   approved; open.

The ledger (WP5) must then prove the flagged premise for its own `R`/`I` pair. That is
where `TruthfulAudit` sits today, and no generic theorem removes that obligation.

## 1. The premise, and what the transport gives

With `R I : Proc unitᴵ B` and tests `P`, `Q`:

```agda
FlagNear q ε R P I Q = Near flagStrat q ε (R ▷ P) (I ▷ Q)
  -- = (d : Strat (Neg B) (Pos B)) → asks≤ q d
  --   → Dom (indᵇ true) ε (runᴹ (R ▷ P) (flagStrat d)) (runᴹ (I ▷ Q) (flagStrat d))

transport-near : FlagNear q ε R P I Q → StateBoundedAt q r I Q → StateBoundedAt q (r ℚ.+ ε) R P
```

`Dom (indᵇ true) ε` is the plan's cofinal `near` exactly: for every real depth `k` there
is an ideal depth `l` with `mass(k, real) ≤ mass(l, ideal) + ε`. No exact rational
probability is assumed. The comparison covers only the flag-shaped strategies and only
the `true` mass, which makes it one-sided and much weaker than an emulation at
`B ⊗ᴵ Flagᴵ`.

**Allowance and error transformation.** The cap stays at `q` on both sides, and the error
becomes `r ↦ r + ε`. `transport-near` is proved in three steps:

- the ideal bound is read at each `flagStrat d` (the schema's `unlift`);
- it is carried along `near`;
- it is lifted back to every admitted context (`stateLift`).

The candidates, in the brief's order:

- **(a) Exact, at any `A`.**
  `transportᵉ : EventSim (R , P) (I , Q) → StateBoundedAt q r I Q → StateBoundedAt q r R P`.
  This is one line: `stateBounded-resp-≈ᵉ` along the reversed generator. At closed
  systems it is also the ε = 0 instance of (b): `eventSim⇒near : EventSim … → FlagNear q 0ℚ …`.
- **(b) From the family emulation, at the flagged interface.** `_≈ᶠ[_]_` compares
  protocol images, and `R ▷ P` is not one. The statement therefore takes flagged
  realizations `FR FI : Systems (λ n → B n ⊗ᴵ Flagᴵ)` with
  `morphism (FR n) ≈ᴹ morphism (R n) ▷ P n` (and the same for `I`).
  - `flagged-near : FR ≈ᶠ[ ε ] FI → FlagNear q (ε n (suc q)) …`
  - `flagged-transport : FR ≈ᶠ[ ε ] FI → StateBoundedᶠ I Q εI → StateBoundedᶠ R P (λ n q → εI n q + ε n (suc q))`

  The `suc q` is the flag ask, charged by `asks≤-flag`. Both statements are proved, in
  8 lines together. The premise on `R`, `I` at `B` that would yield `FR ≈ᶠ[ ε ] FI` does
  not exist (§2). The premise on `P`, `Q` is the same one as in (a): the ideal test must
  track the real one along whatever couples the two systems.
- **(c) The `UC.Audit` carry.** Proved, then deleted: `flag-carry` was
  `audit-carry` applied verbatim to `≤UC[]ᵍ qs e` at the flagged graded image
  `flagᴳ R P = a⇒ᴵ ∘ (R ▷ P) : Proc A (X ⊗ᴵ (B ⊗ᴵ Flagᴵ))`. It turns an `AuditBound` of
  the flagged ideal into one of the flagged real, with the allowance going
  `q ↦ scale q r` and a lower-real slack `δ` added — the one route that handles open
  systems with a nontrivial simulator. Its premise is again at the flagged interface (a
  machine equality `R ▷ P ≈ subᴵ s ∘ (I ▷ Q)` up to `a⇒ᴵ`), and its conclusion is an
  `AuditBound` over a `Permitted` class, not a `StateBoundedAt`; linking the two means
  designating the flag-reader contexts (`flagReader B`) as the permitted class and
  proving `Absorbs` for it, which is not built (§4). The two images had to be passed
  explicitly: with `audit-carry _ _ …` the check ran over 10 minutes at 9 GB, against
  10 s explicit. The module, `UC.Machine.StateEvent.Spike.Carry`, is recoverable from
  git at the parent of the commit that deleted it.

## 2. Not derivable from an emulation at `B`

This fails even for exact simulations with no simulator. Take the ghost bit that is
already in `UC.Machine.StateEvent.HitTests`:

- The real system is `ghost`: a `Bool` state that flips on every activation and is never
  output.
- The ideal system is `erased`: state `⊤`.
- `erase : ghost S.≲ erased`. So `ghost ≈ᴹ erased`, and every emulation at `B = Ωᴵ`
  holds at error 0, with the identity simulator.
- Let `P = id` be the bit. After one activation the bit is `true`, so the real reading at
  `ask₁` is 1, and `StateBoundedAt 1 r ghost id` forces `1 ≤ r`.
- Every test `Q` on `⊤` is constant:
  - `Q = false` gives `StateBoundedAt q 0 erased Q` at every cap;
  - `Q = true` is initially bad, so already at cap 0 the ideal bound needs `r ≥ 1`
    (the shape of `HitTests.initially-bad-cap₀`).

So no ideal bound below 1 transports at any error below 1. `ghost-no-descent` is the
machine-level core of this: no `Q` is compatible along `erase`.

The general point is that an emulation relates the traffic at `B`, while the event reads
state that the ideal need not have (and the simulator never sees `R`'s state). This
example is not proved end to end: its two readings would need `stateRead` computations
on `ghost`, which is not a protocol image.

**The extra premise, named precisely:** `FlagNear q ε R P I Q`, which is a one-sided
comparison of the flagged runs at `flagStrat d`, `asks≤ q d`. Sufficient conditions for it:

- `EventSim (R , P) (I , Q)` gives ε = 0;
- `FR ≈ᶠ[ ε ] FI` for flagged realizations gives error `ε n (q + 1)`;
- in the open graded setting, the flagged `Factors` of (c).

Neither `FlagNear` nor `≈ᶠ` at `B` implies the other. `FlagNear` says nothing about the
`B` traffic, and the example above satisfies `≈ᶠ` at `B` but not `FlagNear`.

## 3. Reuse

Used unchanged:

| Piece | Where it is used |
|---|---|
| `Lift.stateLift` | last step of `transport-near` |
| `Agree.stateRead-agree`, `EventLift.qb-stratTest` | `unlift` at the flag wire |
| `Read.stateBounded-resp-≈ᵉ` | (a) |
| `StateEvent.▷-≲` | `eventSim⇒near` |
| `Emulation.≈ᶠ-runs`, `Read.asks≤-flag` | `flagged-near` |
| `UC.Audit.audit-carry` (via `Model.Audit`), `UC.Graded.≤UC[]ᵍ` | (c) |

New statements:

- **`unlift`**, the converse of a lift at a bare machine, proved once for any reader
  from its agreement at `stratTest` (`Agrees`). `Adequacy.stateBounded⇒hit` is stated
  only at protocol images; `EventLift.hits⇒bounded` is `unlift` at the compiled monitor
  followed by `run-upper`, restated there at protocol images.
- **`FlagNear`**, the premise itself.

## 4. What a WP4 package would contain

1. **Generic schema — done**, `UC.Machine.EventBounds.Transport`. A reader `𝔠` with a
   strategy transform `τ` has an adequacy pair: `Lifts 𝔠 τ cap R` (a strategy-level bound
   at `asks≤ (cap q)` gives `BoundedAt q`) and `Agrees 𝔠 τ I` (the reading at
   `stratTest d` is `runᴹ I (τ d)`, whence the converse `unlift`). Then
   `transport : Lifts cap R → Agrees I → Near τ (cap q) ε R I → BoundedAt (cap q) r I 𝔠 → BoundedAt q (r + ε) R 𝔠`,
   with `transportᶠ`/`transportᴺ` for families. The instances:
   - the flag wire (`flagReader`, `flagStrat`, `cap = id`): `transport-near`,
     `flagged-transport` and `eventSim⇒near` are corollaries, `transportᵉ` stays exact;
   - the compiled monitor (`compileᴹ B (monitorᴹ report)`, `watchFrom report false`,
     `cap q = q + 1`, the monitor's accumulator charged by `hitsᵘ`): `hitsTransport` and
     `hitsTransportᴺ`, where the ideal bound is read one cap unit higher.

   `absorb` is the identity at closed systems.
2. **Open systems** (~150–250 lines). `stateLift` is closed-only. For `R : Proc A B` with
   a simulator, the transport must either:
   - close first, which requires `(I ∘ s) ▷ (Q ∘ π) ≈ᴹ (I ▷ Q) ∘ s` for the
     composite-state projection. This needs `Machines.Collapse.collapseᵀ`, whose
     component projection holds only at the collapsed representative, so every collapse
     is one more compatible simulation to prove; or
   - go through (c) and designate flag-reader contexts as a `Permitted` class, proving
     `Absorbs` for `procᵒ s` and an `extractᵍ`-style bridge from `AuditBound` back to
     `StateBoundedAt`.
3. **The consumer.** The ledger supplies `FlagNear` (or the flagged `Factors`) for its
   pair. This is new mathematics per instance. A qualitative `R ≤UC I` at `B` cannot
   stand in for it (§2).
