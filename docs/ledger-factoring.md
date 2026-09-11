# Factoring the ledger as `Ledger ∘ RO` at the UC level

The chimeric ledger is built from two protocols already:

```agda
oracle : Protocol unitᴵ HashIf                      -- ChimericLedger.POV
ledger : Variant → LState → Protocol HashIf LedgerIf
Sysᴴ hash vr s₀ = ledger vr s₀ ∘ᵖ hash
Sys = Sysᴴ oracle
```

What the UC layer saw, before this branch, was only the CLOSED system
`ιᴳ B ∘ procᵒ (morphism (Sysᴴ hash vr s₀))`. `_∘ᵖ_` is a layer-1 operation and
`morphism` is applied to the whole composite, so the hash sits *inside* the hom
and the emulation relation cannot mention it. That is why
`ChimericLedger.Real.ledger-pov` assumes `Real ≤UC^ω Ideal` — emulation at the
whole ledger — which `docs/end-to-end.md`'s corollary section flags as the
premise that ought to come from the hash instead.

This branch exposes the hash as an interface and lifts the premise.

## The port

`UC.Factor` names the two trivially graded homs a closed two-stage system is
built from:

```agda
closedᵒ : {B : Iface} → Proc unitᴵ B → ifaceᵒ unitᴵ ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
closedᵒ {B} w = ιᴳ B ∘ procᵒ w

stageᵒ : {A B : Iface} → Proc A B → ifaceᵒ A ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
stageᵒ {B = B} g = ιᴳ B ∘ procᵒ g
```

`closedᵒ` is exactly the shape `UC.Asymptotic._≤UC^ω_` compares, so no new
relation is introduced anywhere. At the ledger
(`Examples.ChimericLedger.Factor`) the port and its two sides are

```agda
hashPortᵒ : ℕ → Channel
hashPortᵒ n = ifaceᵒ (HashIf^ω n)

hashᵒ : Systems HashIf^ω → (n : ℕ) → ifaceᵒ unitᴵ ⇒ T₀ 𝟘ᴳ (hashPortᵒ n)
hashᵒ hash n = closedᵒ (morphism (hash n))

ledgerᵒ : (n : ℕ) (vr : Variant) (s : Ledger.LState n)
        → hashPortᵒ n ⇒ T₀ 𝟘ᴳ (ifaceᵒ (LedgerIf^ω n))
ledgerᵒ n vr s = stageᵒ (morphism (L.ledger n vr s))
```

The honest typing came out of `procᵒ`: a `Proc A B` is a hom of the seal at
`ifaceᵒ A`/`ifaceᵒ B`, and the trivial grade `𝟘ᴳ` is the graded monad's own
`return` (`CurriedTensor.Properties.return-λ⇐`). A protocol image carries no
adversary interface, so both homs are pure and the port is an *object* boundary,
not a grade — see "What §3 would add" below.

## The factoring

```agda
factorᵖ : {B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol unitᴵ B)
        → closedᵒ (morphism (P₂ ∘ᵖ P₁))
          ≈ sub λ⇒ ∘ (stageᵒ (morphism P₂) ∙ closedᵒ (morphism P₁))
```

and at the ledger

```agda
ledger-factor : (hash : Systems HashIf^ω) (vr : Variant) (n : ℕ) (s : Ledger.LState n)
              → closedᵒ (morphism (L.Sysᴴ n (hash n) vr s))
                ≈ sub λ⇒ ∘ (ledgerᵒ n vr s ∙ hashᵒ hash n)
```

It is in `𝒞._≈_` — machine simulation equivalence, strictly finer than `_≈ᵁ_`,
so the weaker `≈ᵁ` statement the task allowed was not needed — and it is nearly
definitional. Three inputs, none of them new:

| step | source |
|---|---|
| `morphism (P₂ ∘ᵖ P₁) ≈ᴹ morphism P₂ ∘ morphism P₁` | `Protocol.Machine.Total.morphismCompose` (already a theorem) |
| `procᵒ (g ∘ f) ≈ procᵒ g ∘ procᵒ f` | `UC.Model.Seal.procᵒ-∘`, the one addition: `refl` inside the `opaque` block |
| `sub λ⇒ ∘ (h ∙ (return ∘ w)) ≈ h ∘ w` | `Abstract2.Factor.∙-return` = the graded Kleisli triple's `ext-identityʳ` |

`procᵒ-∘` had to be added because the seal exports the mirror fact
`unprocᵒ-∘` only, and outside the `opaque` block neither derives the other:
that would want `procᵒ ∘ unprocᵒ ≈ id`, which is not exported (and cannot be
stated without naming a hom at `ifaceᵒ`-objects on both sides). It is the same
one-line `refl` in the same block, and it is what lets a machine-layer
functoriality theorem cross the seal into a factoring of a sealed hom.

So `procᵒ` of `_∘ᵖ_` splits on the nose. The only content in the factoring is
the *grade*: the Kleisli composite `h ∙ f` is graded at `𝟘ᴳ ⊗₀ 𝟘ᴳ` where the
closed system is graded at `𝟘ᴳ`, and `sub λ⇒` is the regrading.

## The lift, and the premise shape

```agda
liftᵖ : {B C : Iface} (P₂ : Protocol B C) (u v : Protocol unitᴵ B)
      → closedᵒ (morphism u) ≤UC closedᵒ (morphism v)
      → closedᵒ (morphism (P₂ ∘ᵖ u)) ≤UC closedᵒ (morphism (P₂ ∘ᵖ v))
```

The route is `UC-compose`, in the INHERITED order — `Abstract2.UC-compose`,
which `UC.Model.Setup` inherits through `StdUC` and `UC.Model.Bridge`
identifies with the core's. Three moves:

1. `UC-compose p (≤UC-refl (stageᵒ (morphism P₂)))` gives
   `stageᵒ … ∙ closedᵒ (morphism u) ≤UC stageᵒ … ∙ closedᵒ (morphism v)`,
   both graded at `𝟘ᴳ ⊗₀ 𝟘ᴳ`. The upper stage is assumed *nothing*: it enters
   only as `≤UC-refl`.
2. `Abstract2.Factor.≤UC-sub λ⇒ λ⇐ unitorˡ.isoˡ` pushes `sub λ⇒` through the
   order. This needed a small piece of new metatheory (below).
3. `Abstract2.Factor.≤UC-resp-≈` reads both sides back through `factorᵖ`.

**Exact premise shape.** At the ledger the premise is

```agda
hash-lift : (hash : Systems HashIf^ω) (vr : Variant) (s : (n : ℕ) → Ledger.LState n)
          → hash ≤UC^ω oracle^ω → Realᴴ hash vr s ≤UC^ω Realᴴ oracle^ω vr s
```

i.e. it is the *same relation* the system-level premise is stated in —
`UC.Asymptotic._≤UC^ω_`, the inherited `_≤UC_` per level with a simulator per
dummy adversary — read at the hash interface `HashIf^ω n` instead of at
`LedgerIf^ω n`, with `oracle^ω = L.oracle` as the ideal side. Unfolded, per
level:

```agda
(ιᴳ (HashIf^ω n) ∘ procᵒ (morphism (hash n))) ≤UC (ιᴳ (HashIf^ω n) ∘ procᵒ (morphism (L.oracle n)))
```

Nothing weaker suffices and nothing stronger is asked: in particular it is not
a direct run agreement (`Agreeˢ`), and the simulator it carries is what
`UC-compose` composes into the system-level one.

### The one piece of new metatheory: `≤UC-sub`

`sub c ∘ f ≤UC sub c ∘ g` does *not* follow from `f ≤UC g` for arbitrary `c`:
the dummy form gives `f ≈ᵁ sub s₀ ∘ g`, and turning that into
`sub c ∘ f ≈ᵁ sub s′ ∘ (sub c ∘ g)` needs `c ∘ s₀ ≈ s′ ∘ c`, i.e. the simulator
must commute with the regrading. A **retraction** of `c` supplies the missing
conjugation, `s′ = c ∘ s₀ ∘ r`:

```agda
≤UC-sub : (c : X ℐ.⇒ Y) (r : Y ℐ.⇒ X) → r ℐ.∘ c ℐ.≈ ℐ.id
        → {f g : A 𝒞.⇒ T₀ X B} → f ≤UC g → sub c 𝒞.∘ f ≤UC sub c 𝒞.∘ g
```

Here `c = λ⇒ : 𝟘ᴳ ⊗₀ 𝟘ᴳ ⇒ 𝟘ᴳ` and `r = λ⇐`, and `unitorˡ.isoˡ` is the
retraction — the grade the Kleisli composition introduces is a unit, hence
split, hence invisible to the order. `Abstract2.Factor` is stated over an
arbitrary `UCSetup`, so this is available at every model, not just at the
machine one.

## The corollary at the hash premise

`Examples.ChimericLedger.Factor`, beside `Real.ledger-pov` and not touching it:

```agda
ledger-pov-from-hash : SerInj → hash ≤UC^ω oracle^ω → (p : ℕ → ℕ) → Poly p
                     → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
                       × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                          → asks≤ (p n) d
                          → PrHit (Real a V inputConsuming hash nd n)
                                  (badReal a V inputConsuming hash nd n) d ≤ f n)
ledger-pov-from-hash si hp =
  ledger-pov a V inputConsuming hash nd si (hash-lift hash inputConsuming (gen a V) hp)
```

Conclusion, bound and all three discharged real-side hypotheses are
`Real.ledger-pov`'s verbatim; the only change is the premise, which is now
about the hash alone. The family quantification is the per-level `(n : ℕ) →`
used elsewhere, because `_≤UC^ω_` is itself per-level.

This is the slides-literal chain, now formal end to end:

```
H ≤UC RO  ⟹  Ledger ∘ H ≤UC Ledger ∘ RO  ⟹  POV bound on Ledger ∘ H
   hash-lift                                   Real.ledger-pov
```

and it closes `docs/end-to-end.md`'s continuation item 1's remaining clause
("deriving that from a hash-level emulation via family composition is useful
integration work").

## What review §3 would add on top

`docs/protocol-implementation-review.md` §3 asks for a *nontrivial simulator
interface*: process families of the generic `A ⇒ X ⊛ B` shape with simulator
families `Y ⇒ X`, and a simulator that demonstrably spends oracle queries. Its
step 2 says, of a hidden interface, "expose it at the appropriate resource
boundary instead of merely adding a unit grade". The port above is exactly that
boundary — but it is exposed as an **object** boundary, not as a grade:
`hashPortᵒ n` is the domain of `ledgerᵒ` and the codomain of `hashᵒ`, while both
homs stay graded at `𝟘ᴳ`. So §3 is not addressed here, and the honest statement
of what remains is:

* a hash family whose UC image is genuinely graded, `ifaceᵒ unitᴵ ⇒ X ⊛ hashPortᵒ n`
  with `X` the simulator-facing interface (a random oracle with a
  programming/observation port, say — the lazily sampled `POV.oracle` has none);
* a simulator family `Y ⇒ X` at that grade, with an occurrence/count proof for
  its queries rather than an upper bound;
* the budgeted carry (`UC.Asymptotic.Audit.uc-audit-carry`, `simCost`) run at
  that grade instead of at `unit ⇒ unit`.

`liftᵖ` is usable there unchanged in *shape* but not in *proof*: `≤UC-sub`'s
retraction is what makes the unit grade invisible, and at a nontrivial `X` the
grade `X ⊗₀ P` the composition produces is real data that the statement has to
carry rather than discard.

**The ledger cannot supply that example.** The maintainer's reason, recorded
here so it is not re-attempted: the ledger is pure with respect to the graded
monad (its `morphism` image carries no adversary interface) and `POV.oracle`
exposes no adversary interface either, so every simulator in sight is a
`𝟘ᴳ ⇒ 𝟘ᴳ` scalar and is provably blind (`UC.Seam.Grounded.subBlind`). A
nontrivial-simulator example needs a different functionality, and is a separate
project.

## Nothing stopped

No obstruction was hit. `procᵒ` of `_∘ᵖ_` splits without breaking the seal's
opacity (`procᵒ-∘`, one `refl` inside the block), and the grading expresses the
port without difficulty because the port is an object rather than a grade. The
two things worth flagging are recorded above: `procᵒ-∘` is an addition to
`UC.Model.Seal`, and `≤UC-sub` is genuinely new metatheory (with a documented
reason why the unrestricted congruence is false).

## Modules

| module | LOC | what |
|---|---|---|
| `CategoricalCrypto.Abstract2.Factor` | 82 | `∙-return`, `≤UC-resp-≈`, `≤UC-sub`, over an arbitrary `UCSetup` |
| `CategoricalCrypto.UC.Factor` | 104 | `closedᵒ`, `stageᵒ`, `factorᵒ`, `factorᵖ`, `liftᵖ` at the machine model |
| `CategoricalCrypto.Examples.ChimericLedger.Factor` | 116 | the ledger's port, `ledger-factor`, `hash-lift`, `ledger-pov-from-hash` |
| `CategoricalCrypto.UC.Model.Seal` | +8 | `procᵒ-∘` |
