# Quality review

## Resolved (quantitative-family)

Judgment calls made while implementing steps 3 and 4 of
`docs/uc-presheaf-preservation-plan.md`. Everything below is green; each item is a place a
maintainer may want to rule differently.

1. **`simCost`/`q≤simCost` moved out of `UC.Audit` into `UC.Budget`.**
   `UC.Audit`'s private `shuffle` was the same arithmetic as the substitution the new
   quantitative composition theorems perform, so it is now `UC.Budget.ctxBudget-absorb`
   beside `ctxBudget`, with `ctxBudget-simCost` (the `cs ⊔ 1` shape) and
   `ctxBudget-closure≤` (the closure-side bound). `UC.Audit` re-exports `simCost` and
   `q≤simCost` (`UC/Audit.agda:58`), so every name it offered its importers is unchanged
   and `UC.Seam.Audit`/`UC.Asymptotic.Audit`/`Examples` are untouched. Committed on its
   own (`ddf96d40`) at the coordinator's request; the only other change to that file is
   `shuffle`'s body becoming the imported lemma.

2. **`Certified` is a Σ, not a record.** The record form exhausts a 20 GiB heap — a field
   `sim-qb : (n : ℕ) → QB (cost n) (sim n)` over two earlier fields, at the sealed model's
   `QB`, cannot be elaborated. `docs/quantitative-family.md` §1 has the measurement and the
   discriminating probes. If a record is wanted for ergonomics, the way in is a record over
   *parameters* (`Certified′ (sim) (cost) : Set` with one field) or a `no-eta-equality`
   record whose certificate field is a wrapped abstract type; both were untested.

3. **`prefixᵒ` spells `μ ∘ T₁` rather than naming `Abstract2.Action.prefix`.** Measured
   +22 s for the module application of `Abstract2.Action StdSetup`, and every consumed
   lemma is already stated at the `μ ∘ T₁` spelling. If the maintainer prefers the generic
   name in the statement, the change is one import and one definition, at that cost.

4. **`_≤UC^ωᵉ⁺_`'s adversary carries a certificate**, where `Abstract2._≤UC_`'s does not.
   Without it `≤UC^ωᵉ⇒⁺` has no allowance substitution to charge for absorbing the
   adversary into the test. The qualitative order is untouched. An alternative would be to
   quantify uncertified adversaries and conclude at a schedule that is a *bound* (with an
   `Allowance-mono` premise) — strictly weaker, and not built.

5. **`Allowance-mono` is a premise of `≈ctx-pre`/`UC-composeᵉ`, not a field of the
   witness.** Consequence: `UC-composeᵉ` takes its arguments as components rather than as
   two `_≤UC^ωᵉ_` values, because the schedule it needs monotone is existentially bound
   inside one of them. Making `Allowance-mono` a fifth component of `_≤UC^ωᵉ_` buys the
   packaged form and costs `≤UC^ωⁿ⇒≤UC^ωᵉ` a premise that `_≤UC^ωⁿ_` does not carry. A
   proved monotone envelope would remove the choice; its signature is in
   `docs/quantitative-family.md` §10.

6. **The plan's "`≈ctx[0]` from `≈ᵁ`" is not provable at this model**, and the kit says so
   instead: `≈C⇒≈ctx` gives the zero schedule from the ambient hom equality (which
   `obs-resp` observes exactly), and `≈ᵁ⇒≈ctx` takes a positive schedule because `_≈ᵁ_`'s
   observation relation here is closeness at every *positive* error. Same reason
   `uc-≈ᶠ[_]` already took one.

7. **`≈ctxᴬ⇒≈ℰ[]` is a named implication and `_≈ℰ[_]_` was not touched.** The two
   quantifiers genuinely differ (per-level contexts against levelwise families carrying one
   polynomial), so no definitional identification was claimed. `_≈ᶠ[_]_` IS now a
   definitional alias of the canonical relation, which is the identification the plan asks
   for where the domains do coincide.

8. **`UC.Asymptotic.Compose` has no in-repo importer yet.** It is new API; the root wiring
   is listed in `docs/quantitative-family.md` §9 and was deliberately left to the
   maintainer (the root index files are off-limits to this branch).
