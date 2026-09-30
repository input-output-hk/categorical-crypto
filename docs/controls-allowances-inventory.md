# Controls and allowances inventory (WP9, before the change)

Taken at `deeaf867` (`integrate/2-qucsetup.resource`). Lines are `module:line`
at that commit. "Uses" means the field is named, or reached through a lemma
that names it (grep over `src/`).

## Notions and their laws

| Notion (module:line) | Data | Laws | Order it lives over |
|---|---|---|---|
| `Control` (`Approx.Controlled:45`) | `at : Error → Error` | `preserves-ε₀ : at ε₀ ⊑ ε₀`, `preserves-⊕ : at (ε ⊕ δ) ⊑ at ε ⊕ at δ`, `monotone : ε ⊑ δ → at ε ⊑ at δ` | the error preorder `(Error, ≡, ⊑)` of `OrderedErrorAlgebra` (`Approx.Error:42`) |
| `idᶜ`, `_∘ᶜ_` (`Controlled:54`, `:60`) | identity, composite of `at` | composite laws by `⊑-trans` + `monotone` | same |
| `_≐_`, `_≐ᶜ_` (`Controlled:86`, `:89`) | control equality: `at` agree both ways under `⊑` at every error | — | same (not `≡`: schedule errors are functions) |
| `Controlled X Y` (`Controlled:73`) | `map`, `control`, `preserves : x ≈[ ε ] y → map x ≈[ at control ε ] map y` | — | `ApproxSpace` (`Approx.Space:28`) |
| `_≈ᶜ_` (`Controlled:105`) | `≐ᶜ` on controls × maps agree at `ε₀` | equivalence (`:109`) | — |
| `Ctrl` (`Controlled:144`) | category of controlled maps | `composeᶜ-resp` (`:131`) | — |
| `FilteredSpace` (`Approx.Filtered:35`) | `space`, `Admit : Ix → Carrier → Set` | `admit-mono : q ≤ q′ → Admit q x → Admit q′ x` | allowance `Poset I` (module parameter, `Filtered:26`) |
| `Allowance` (`Filtered:46`) | `at : Ix → Ix` | `monotone : q ≤ q′ → at q ≤ at q′` (no `≈`-congruence field) | `Poset I`, only its `_≤_` |
| `idᵃ`, `_∘ᵃ_` (`Filtered:51`, `:56`) | identity, composite | — | same |
| `Filtered X Y` (`Filtered:62`) | `underlying : Controlled`, `allowance : Allowance` | `admits : Admit q x → Admit (at allowance q) (map x)` | — |
| `_≈ᶠ_` (`Filtered:83`) | `≈ᶜ` × `(q : Ix) → at f q ≡ at g q` | equivalence (`:89`), `composeᶠ-resp` (`:112`, uses `cong` of `≡`) | **compares allowance outputs by `≡`, not by `Poset._≈_`** |
| `Filt` (`Filtered:124`) | category of filtered maps | laws by `refl` in the allowance component | — |
| `_≈ᵃ[_]_` (`Filtered:163`) | `admitted : Admit q x → u x ≈[ Ε q ] v x` | `≈ᵃ-refl/-sym/-trans/-mono/-resp₀` (`:174`–`:188`) | schedule `Ε : Ix → Error` |
| `≈ᵃ-pre` (`Filtered:192`) | pullback along `κ` reads `Ε ∘ at (allowance κ)` | — | allowance only |
| `≈ᵃ-post` (`Filtered:201`) | postcomposition reads `at (control k) ∘ Ε` | — | control only |
| `ApproxSpace`, `resp₀`, `zeroSetoid`, `Nonexpansive`, `Approx`, `F₀` (`Approx.Space:28`, `:42`, `:46`, `:55`, `:96`, `:115`) | base spaces | — | error algebra |

## Instances

| Instance (module:line) | Of | Laws |
|---|---|---|
| `Reindexing.reindex ρ` (`Approx.Schedule:65`) | `Control` at `pointwise I V` | all three by `⊑-refl` pointwise: an EXACT control |
| `reindex-cong`, `reindex-∘` (`Schedule:77`, `:83`) | `≐ᶜ` of reindexings, composite by `refl` | — |
| `≤⁺-poset` (`Data.Nat.Positive:37`) | allowance `Poset` of the query model | `On.poset ≤-poset value`: `_≈_` is `value r ≡ value s`, **not** `≡` on `ℕ⁺` |
| `filteredᵠ C` (`UC.Quantitative.Query:134`) | `FilteredSpace` over `Sched`, `≤⁺-poset` | `Admit q E = Image forget q E`, `admit-mono` by `L.sub[_]` |
| `pullᵠ (r , ĥ)` (`Query:177`) | `Filtered` | control `reindex (_· r)`; allowance `at = _· r`, `monotone = *-monoˡ-≤` |
| `Qᵠ` (`Query:191`) | `Presheaf 𝒞ᵇ (Fl.Filt …)` | allowance component of `identity`/`homomorphism`/`F-resp-≈` proved as `≡` on `ℕ⁺` through `value-injective` (`:197`, `:201`, `:204`) |

No other `Control`, `Allowance` or `FilteredSpace` instance exists; `≤⁺-poset`
is the only allowance poset `Filtered` is applied at (`Query:55`), and it is
discrete up to `value-injective`.

## Which law each consumer uses

| Consumer (module:line) | Uses |
|---|---|
| `Controlled._∘ᶜ_` (`:60`) | `monotone`, `preserves-ε₀`, `preserves-⊕` (closure only) |
| `Controlled.composeᶜ-resp` (`:131`) | `monotone`, `preserves-ε₀` |
| `Controlled.F₀ᶜ` (`:180`) | `preserves-ε₀` |
| `Approx.Small.Controlled.SmallPreserving`, `FSmallᶜ` (`:34`, `:48`) | `Control.at` only |
| `Filtered.≈ᵃ-post` (`:201`) | `Control.at`, `Controlled.preserves`; no control law |
| `Filtered._∘ᵃ_` (`:56`) | `Allowance.monotone` (closure only) |
| `Filtered.composeᶠ-resp` (`:112`) | `≡`-`cong` of the outer `Allowance.at` — would be `Poset._≈_`-congruence once outputs are compared by `≈` |
| `Filtered.≈ᵃ-pre` (`:192`) | `Filtered.admits`, `Allowance.at` |
| `Query.pullᵠ`, `Qᵠ` (`:177`, `:191`) | constructs `Allowance`; proves `≈ᶠ` (`reindex-cong`, `value-injective`) |
| `Contextual.absorb-testᵠ` (`UC.Quantitative.Contextual:143`) | `≈ᵃ-pre` along `pullᵠ` (the allowance map `_· r`), `≈ᵃ-mono`, `≈ᵃ-resp₀`, `Query.absorb-test` |
| `Contextual.absorb-closureᵠ` (`:158`) | `≈ᵃ-post` along `pullᵠ` (the control `reindex (_· r)`) after `≈ᵃ-pre` at `1⁺`, `≈ᵃ-mono`, `≈ᵃ-resp₀`, `Query.absorb-closure` |
| `Contextual.ctx-absorb`, `ctx-sub`, `at-trans` (`:174`, `:192`, `:206`) | `absorb-testᵠ` |
| `Contextual.ctx-refl/-sym/-trans/-mono/-resp` (`:110`–`:131`) | `≈ᵃ-refl/-sym/-trans/-mono/-resp₀` |
| `UC.Quantitative.Family.≈ctx⇒agreeᵠ`, `agreeᵠ⇒≈ctx` (`:140`, `:145`) | `agree`, `admitted` |
| `Family.≈ctx-ext` (`:411`) | `ctx-absorb` |
| `Family.≈ctx-pre` (`:428`) | `absorb-closureᵠ` |
| `Family.≈ctx-dom` (`:458`) | `≈ᵃ-post` along `pullᵠ` at `1⁺`, `≈ᵃ-mono`, `≈ᵃ-resp₀` |

Never used by any consumer: `preserves-⊕` and `Allowance.monotone` (each
spent only to close its own notion under composition), `admit-mono` (supplied
by `filteredᵠ`, spent nowhere), and any `≈`-congruence of an allowance map
(the record has none; `composeᶠ-resp` gets it from `≡`).

## Monoidal direction of `Control`

Read the error preorder as a thin category (`ε → δ` iff `ε ⊑ δ`). A lax
monoidal functor has `ε₀ → φ ε₀` and `φ ε ⊕ φ δ → φ (ε ⊕ δ)`; `Control` has
the reverse arrows `φ ε₀ ⊑ ε₀` and `φ (ε ⊕ δ) ⊑ φ ε ⊕ φ δ`, the **oplax**
direction. The error algebra is only a lax-unital preordered magma (no
associativity, one unit bound each side), so neither name applies as a
monoidal-functor claim: `Control` is a monotone, subadditive map that does not
raise zero.

## Allowance vs control

The two data of a `Filtered` map are independent: `≈ᵃ-pre` moves a bound's
allowance by the allowance map alone, `≈ᵃ-post` moves its error by the control
alone, and `pullᵠ`'s pair (`_· r`, `reindex (_· r)`) is not a function of
either component (`Filtered:5`–`:10`).
