# Tactics for the K reproofs

The deep-dive established *why* Carlier (Lean) and Coq-Combi (Coq) are shorter than
our `PermuteCoherence` K proof: **automation we lack** — Lean's `grind`/`simp`/
`Quotient.lift` + classical `CoxeterSystem`, Coq's SSReflect `gencongr_hom` +
boolean reflection + `tperm` algebra. None of that *code* ports to `--safe
--without-K`, but the corresponding *tactic role* can be supplied in Agda. This
lists the buildable Agda tactics/infrastructure, what each costs, and which reproof
it enables.

Constraint reality: agda-stdlib 2.3 ships real reflection macros
(`Tactic.Cong.cong!`, `Tactic.MonoidSolver`, `Tactic.RingSolver`); `standard-library-meta`
is available. But our own "solver" (`solveMor!`, `SolverReflect`) is a *verified
normalizer function over deep-embedded syntax*, not a goal-quoting macro — that is
the idiom that has worked here. Agda's tactic story is thinner than Lean/Coq; the
high-leverage items are plain parameterized modules + a couple of stdlib macros,
NOT a from-scratch goal-reflecting Coxeter solver.

## T1 — Generic congruence-closure module for `_~ʷ_` (the `gencongr_hom` analogue)

**What.** A parameterized module that, given a base local-rewrite relation `R`
(our `c1`/`c2`/`c3` generators) together with a proof that each base rule is stable
under the framings (`∷`, `++`-right, `liftW`) and sound (`R ⇒ ≈-fb`), DERIVES once
and for all: the equivalence closure (`~refl`/`~sym`/`~trans`), the congruences
(`∷c`, `++c-r`, `lift~`), and the soundness lift `~ʷ⇒≈`. Plain Agda — no reflection.

**Replaces.** The hand-rolled per-constructor recursions `lift~` (Word.agda:280-287),
`++c-r` (290-297), `~ʷ⇒≈` (361-…), `∷-cong`, which must each be re-touched whenever a
generator changes. This is Coq-Combi's `gencongr_hom` ("one local rule +
homogeneity ⇒ full congruence + soundness").

**Enables.** The (A) reproof (clean congruence layer for the new insertion path) and
is itself idea-2 (a standalone modest refactor). Sure win, low risk.

## T2 — stdlib `Tactic.Cong` (`cong!`)

**What.** Import the reflection-based congruence tactic to collapse the multi-step
`∘-fb` / `subst`-transport reassociation chases (the A/B/C/D `∘-fb` chase in
`eval-canonW`, the `subst₂ FinBij` noise in `Map.agda`). Already in stdlib — just use it.

**Enables.** Shrinks the cast/transport boilerplate everywhere; immediate, low effort.

## T3 — FinBij equational solver (`Tactic.MonoidSolver` at `(FinBij, ∘-fb, id-fb)`)

**What.** FinBij under `∘-fb`/`id-fb` is a monoid; instantiate the stdlib monoid
solver (or a small bespoke `∘-fb`-normalizer) to auto-discharge associativity/unit
reshuffles of composition chains. Medium effort (need the `Monoid` instance + check
it plays with `--without-K`).

**Enables.** The `eval-canonW`/`straightenW` `∘-fb` algebra; optional polish.

## T4 — Setoid/`Quotient` equational-reasoning layer for `_≅↭ⁱ_`

**What.** Make `permute` factor through a setoid (or `Quotient`) of `_≅↭ⁱ_`, so the
groupoid/bifunctor generators (`iref`/`isym`/`itrn`, `tr-unit`/`tr-assoc`,
`prep-id`/`prep-tr`) become *definitional* (`Quotient.lift`-style), as in Carlier's
`RecursiveFunctorData`. NOT a goal-reflecting tactic — a structural enabler.

**Enables.** The (B) reproof (collapse the ~280-LOC categorical lift toward ~100-150).
Catch: a `--without-K` setoid quotient *reintroduces* the UIP/`subst` tax (the
`uipX`/`_≅↭ᴴ_` machinery exists precisely because `_↭_` is unquotiented), so budget
~⅓ of the gain reclaimed. High effort, +EV.

## T5 — (Rejected) full goal-reflecting Coxeter/SMC coherence macro

A quote-the-goal macro that decides `_~ʷ_`/`≈Term` by computing `canonW`/normal
forms reflectively. High-risk, large, overlaps the (separately-scoped, circular-ish)
strict coherence solver. Not used for the reproofs.

## Plan

Build **T1** (foundational, enables A). Adopt **T2** opportunistically. Then the two
reproofs:
- **(A)** reprove `insert-thm` Coq-Combi-style (port the `inscode` generator-insertion
  braid-path against our rotation `canonW`) to retire the ~957-LOC exchange subtree
  (`BringToFront*` + `InsertProofMatsumoto` + exchange parts of `ExchangeBase`),
  using T1's clean congruence layer + T2.
- **(B)** the **T4** spike: factor `permute` through a quotient of `_≅↭ⁱ_`.

All work: `--safe --without-K`, postulate-free, K (`faithfulness`/`soundness-full-wired`)
green at every integration; spikes in isolated worktrees, integrated only when green.
