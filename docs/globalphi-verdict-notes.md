# GLOBAL-φ DIRECT — correctly-framed probe notes

> **STATUS (2026-08-25): spike log.** The modules discussed (`DeepProv`, `GlobalPhiDirect.agda`) were probe-only and never entered the tree.

Target: `⟪s⟫ ≅ᴴ ⟪frame⟫` (the deep-rewrite gate #1) where the bijection is the
SPECIFIC one DeepProv builds (seedFromInterfaces + guided fold over provenance
pairs). NOT `⟪decode H⟫ ≅ᴴ H` (that was the prior, misframed run).

Decisive question: is `is-just (findIsoFromCarveᵀ ⟪s⟫ ⟪frame⟫ ⟪lᵗ⟫) ≡ true`
provable in GENERAL (--safe) by BOUNDED structural argument, or does it reduce
to the non-local cumulative-remapP incidence faithfulness (= decoder
completeness, months)?

## Machinery read (facts)

### Verify.verify (Verify.agda:211-264) — the iso decider
Inputs: H, J, and partial bijections φB ψB : PBij. It returns `just (H ≅ᴴ J)` iff
ALL of these decidable checks pass:
  (T1) totalise(forward φB), totalise(backward φB) succeed  — φ is a TOTAL map both ways
  (T2) totalise(forward ψB), totalise(backward ψB) succeed
  (R1) ∀ i. φ⁻¹(φ i) ≡ i ;  ∀ j. φ(φ⁻¹ j) ≡ j     (vertex round-trips)
  (R2) ∀ e. ψ⁻¹(ψ e) ≡ e ;  ∀ k. ψ(ψ⁻¹ k) ≡ k     (edge round-trips)
  (L)  ∀ i. J.vlab(φ i) ≡ H.vlab i                  (vertex label agreement)
  (E1) ∀ e. J.ein (ψ e) ≡ map φ (H.ein  e)          (edge input endpoints)
  (E2) ∀ e. J.eout(ψ e) ≡ map φ (H.eout e)          (edge output endpoints)
  (D)  J.dom ≡ map φ H.dom ;  J.cod ≡ map φ H.cod    (boundary)
  (EL) ∀ e. (transported) J.elab(ψ e) ≡ H.elab e    (edge labels, via flat-match)

So `findIsoFromCarveᵀ … ≡ just _` per-instance is the computational proof. The
GENERAL theorem question = can we show all of T1,T2,R1,R2,L,E1,E2,D,EL hold for
every carve-produced (s,frame,lᵗ) WITHOUT per-instance computation.

### The provenance bijection is BUILT, not searched (DeepProv.agda)
- φ seeded by `seedFromInterfaces H J` = `pairUp` H.dom↔J.dom then H.cod↔J.cod
  into a PBij (forward+backward partial maps), plus a vlab consistency check.
- Then `goEdges` folds `tryEdge H J φ ψ eF e'F` over the provenance ℕ-pairs
  `pairsFor L S` (which walk the carve origin list: complement edges 1:1, hole
  slot expands to ψ-image). `tryEdge` does: shape check (vlab atom-lists of
  ein/eout agree), label flat-match, then `pairUp φ (ein H e)(ein J e')`,
  `pairUp φ' (eout H e)(eout J e')`, then `extend-bij ψ e e'`.
- So φ,ψ are partial maps built by a sequence of `extend`/`extend-bij` whose
  ONLY content is: at the boundary, pair H.dom[k]↔J.dom[k]; per edge pair,
  pair endpoints positionally and edge index.
- CRUCIAL: `extend-bij` REFUSES conflicting bindings (returns nothing). So the
  fold succeeding already encodes a global consistency: every time a vertex is
  pinned twice (e.g. an internal vertex shared by two edges), the two demands
  must AGREE. This is exactly where incidence faithfulness would bite.

## KEY OBSERVATION: the partial-map bindings ARE the incidence constraints

Each `extend p i j` is a no-op-or-conflict on re-binding i: if i already maps to
j' it requires j ≡ j' (PBij.agda:41-43). Therefore:

  goEdges succeeds  ⟺  the family of demands
     { (H.ein e)[k] ↦ (J.ein (φ-pair e))[k] } ∪ { dom/cod pairings } ∪ {eout…}
  is a CONSISTENT partial function (no vertex gets two different images) AND its
  inverse is too, AND every H-vertex gets covered (for totalise to succeed).

This is precisely the statement "the positional endpoint correspondence induced
by the provenance edge-pairing is a well-defined vertex bijection" — i.e. when
two edges of ⟪s⟫ share an internal vertex, their provenance-paired ⟪frame⟫ edges
share the corresponding vertex in the SAME position. THAT is non-local incidence
faithfulness. It is the content of T1/R1 (totalise + round-trip) succeeding.

## Module built: src/GlobalPhiDirect.agda (compiles --safe --without-K, 0 postulates)

- `Factor` names the 9 families of Verify obligations as the EXACT props
  `verify` decides (T totalise, R round-trip, L vlab, E ein/eout, D boundary).
- `Assembly` takes the 4 `Total` witnesses (= residual #1) as parameters and
  `Assembly.Residual2.iso-fields` is a TOTAL --safe function from the residuals
  to ALL vertex/edge/boundary fields of `_≅ᴴ_`.  So the reduction
  "residual#1 + residual#2 ⇒ ⟪s⟫≅ᴴ⟪frame⟫" is MACHINE-CHECKED.
- --safe forbids `postulate`; parameters are a STRICTER factoring than postulates.

## Classification of each residual

### RESIDUAL #1 — totalise (forward/backward φB) — **HARD**
The 4 `Total` parameters. Structurally decisive facts:
- Deep.assemble keeps the CARVED graph H' at nV=S.nV, vlab=S.vlab, dom/cod=S
  (vertices NOT renumbered).  GOOD — but irrelevant, because:
- ⟪frame⟫ ≠ ⟪H'⟫.  tryEmb (Deep.agda:185-199) runs `decode-attempt H'` → a
  TERM `ctx`, then focusAtₙ / retract / glue, and ⟪frame⟫ re-translates the
  resulting term.  ⟪_⟫ RECONSTRUCTS vertices positionally from term wiring.
- Therefore J=⟪frame⟫'s vertex set is the positional reconstruction of the
  decode term.  φB total = that reconstruction is a complete, conflict-free
  bijection onto ⟪s⟫'s vertices that respects incidence.
- That is precisely cumulative-remapP/decode-roundtrip faithfulness: when two
  ⟪s⟫-edges share an internal vertex, the provenance-paired ⟪frame⟫ edges
  share the corresponding vertex in the same position.  NON-LOCAL (depends on
  full kahn order + remapP fusion history). = decoder completeness (months).

### RESIDUAL #2 — round-trips, vlab, per-edge endpoints, boundary, EL
Mostly STRUCTURAL, BUT note the dependency:
- Boundary (D): seedFromInterfaces pairs H.dom↔J.dom, H.cod↔J.cod by
  construction → STRUCTURAL/cheap.
- vlab (L), EL (edge labels): from emb : ⟪lᵗ⟫↪ᴴ⟪s⟫ (verified) for the redex
  block + assemble-keeps-vlab for the complement → STRUCTURAL.
- Per-edge endpoints in `_≅ᴴ_` form `J.ein (ψ e) ≡ map φ (H.ein e)` with the
  ONE global φ:  M1 `decode-preserves-edges` gives `ein ⟪decode⟫ epe ≡ map Φ
  χ-ein` with a PER-EDGE cascade Φ and the LOCAL g-interface χ-ein — NOT the
  global φ, NOT H.ein.  Rewriting `map Φ χ-ein` to `map φ (H.ein e)` for the
  SHARED global φ requires #1 (the cascade-collapse IS the non-conflict).
  So E is NOT independent of #1; it is downstream of it.  Round-trips (R) are
  trivial once the totals exist (totalise gives pointwise evidence; inversion
  is the φB forward/backward sync from extend-bij), but they PRESUPPOSE #1.

## DECISION: NO-GO for bounded proof-carrying Route A

The provenance framing delivers two REAL wins over Route B:
  (i)  it removes the "does an iso EXIST / search for it" problem — the map is
       GIVEN; and
  (ii) it makes residual #2's label/boundary pieces cheap (reuse emb + seed).
It does NOT remove residual #1.  Totalise+round-trip of the SPECIFIC provenance
map is not a free property of an explicitly-constructed map here, because the
map's CODOMAIN (⟪frame⟫ vertices) is itself a decode-term reconstruction, so
"the map is a total bijection" coincides with "the decode reconstruction
faithfully replays ⟪s⟫'s incidence" = the cumulative-remapP incidence
faithfulness = decoder completeness.  This is the same wall (~months), now
appearing as residual #1 instead of as "leg 2".

SINGLE DECISIVE OBLIGATION (named): `tφ⁺ : Total (forward φB)` together with its
backward+round-trip companions — i.e. **the provenance vertex partial-map is a
total bijection between ⟪s⟫'s and ⟪frame⟫'s reconstructed vertex sets**.
Inhabiting it in general = non-local incidence faithfulness.

CAVEAT / where a GO could still hide (honest):  the empirical fact that
`findIsoFromCarveᵀ` PASSES verify on real instances means #1 is TRUE for those
instances and is decided by COMPUTATION (totalise just walks Fin n).  A
PER-INSTANCE proof is free (`refl`-by-computation on a closed graph).  The
NO-GO is specifically about the GENERAL theorem (∀ carve-produced s,frame): the
totalise/round-trip cannot be discharged without the non-local argument.  If the
deep-rewrite engine only ever needs gate #1 on CONCRETE closed terms, a
"compute-and-reflect" tactic (force `findIsoFromCarveᵀ … ≡ just iso`, extract
iso) is bounded and already exists as the current gate — proving it a THEOREM
buys the perf win only if the per-instance computation is the cost, which it is.
=> The perf goal (make the gate a cheap forced proof term) is NOT achieved by a
general theorem; it would need per-instance reflection, which is what the gate
already does.  So Route A's *theorem* form is NO-GO; its *value* (skip the
search) is already captured by DeepProv computing the witness.
