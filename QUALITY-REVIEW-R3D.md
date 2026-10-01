# Quality review — protocol-rewrite round 3, part R3D foundations (2026-10-01)

Scope: `scope-R3D.txt` (126 files) at base `27cda67f`. 62 of them are integration-owned, so
they were read for context only (see the last section). The other **63 files** were edited and
reviewed: `Categories/{Category/**,GConstruction*,GradedKleisli/Coherence,Monad/**}`,
`Class/DecEq/Ext`, `Data/{Bits,Bool,List,Rational/LowerReal,Vec}`, `Function/Bundles/Ext`,
`Relation/Binary/**`, `ProbabilisticLogic.agda`, `ProbabilisticLogic/{Distribution/{Possibility*,
RationalDist/*,Uniform/{Birthday,Collision,Duplicate}},Dp*}`. Solver-origin files and the SFunM tree
were not reviewed. Every entry was screened against the earlier ledgers (`QUALITY-REVIEW-{D-foundations,
R2a,R2b,A-examples,B-uc,C-machines}.md`, `QUALITY-REVIEW.md`). An entry that matches one of them says so.

Verification: pagda check run: yes (see *Verification* at the end). Soundness baseline (rule 3 over
`src`): 16 before and 16 after, the same lines, all of them prose mentions of "postulate" in
solver-origin files. Sweep tally (toolkit JSONs in `QUALITY-REVIEW-R3D.d/`):
`using-drop` 16 kept / 88 candidates / 53 skipped; `import-drop` (experimental `import_prune.py`)
**partial**: 21 of 63 files, 7 imports pruned, then stopped (see Suggestion 9); `enum-with` 11 sites,
`enum-where` 162 sites (124 flagged), `enum-comments` 193 blocks, every block dispositioned in
`QUALITY-REVIEW-R3D.d/comment-dispositions.tsv`. `implicit-drop`, `join-lines`, `binder-drop`,
`using-minimize`, and the `with_case`/`where_inline` spikes were not run (Suggestion 9).

## Committed (you can skim these)

- `b28460fb` Comments: cut statement glosses and proof-step narration (9 files, +1/−15). Comment-only.
  Cuts: `β-nat` echo, `trace-slide`'s step narration, `homomorphismᴳ`'s outline and the header's "(see
  there)" to it, `mid`-from-unit label, "Yoneda variant", two duplicate `any`-deprecation notes, `detₚ`
  gloss, `indᵇ-cover` echo. All 193 blocks are dispositioned in `QUALITY-REVIEW-R3D.d/comment-dispositions.tsv`.
- `b51cc9cd` Bare opens where a using list resolves no clash (sweep: using-drop), 8 files, +16/−16. The oracle checked each one green.
- `b6285426` Drop imports nothing uses (sweep: import-drop, 21 of 63 files), 4 files, −7. The oracle checked each one green:
  `Relation.Binary.PropositionalEquality`/`Categories.FreeMonoidal` in the three APROP-coherence modules
  (both reach them through `Categories.APROP`), and `Categories.Category` in `GradedKleisli.Coherence`.
- `3216c17d` Dp.Iter family: the loop-side monotonicity steps are `Tᵗ-mono` (4 files, +5/−14). Five
  private `up` helpers in `Iter`, `Iter/Transfer` (×2), `Iter/Codiagonal` and `Iter/Out` re-derived
  `Iter.Tᵗ-mono` case by case. Each is now one application. Statements unchanged.
- `800b8bd1` Expectation: `Pr₁⊥≤1` next to `Pr₁⊥≥0` (rule 28; pure move, +6/−6).

Net: 21 files, +28/−58.

## Suggestions (need your call), ranked by LOC saved / complexity removed

### 1. Fallout of the SFunM deletion: about −830 LOC across 10 foundation modules with no consumer left
The dependency graph (`import` lines over all of `src`, with `SFunM*`, `SFunPartial` and
`SFunPossibility` removed, iterated until nothing changes) leaves these modules with **no importer**.
Their only consumers today are `SFunM.Test.Possibility`, `SFunPossibility` or each other:
- `src/ProbabilisticLogic/Distribution/RationalDist/Support.agda :: supp` (332): only importer `SFunPossibility`.
- `src/ProbabilisticLogic/Distribution/Possibility.agda :: _≈𝒫_` (123): importers `Support`, `SFunPossibility`.
- `src/ProbabilisticLogic/Distribution/Possibility/Setoids.agda :: 𝒫ˢ` (122): only importer `SFunM.Test.Possibility`.
- `src/Categories/Monad/Setoids/Discrete.agda :: elementwise` (32), `…/Discrete/Morphism.agda :: θ-bind` (45):
  their importers are `Possibility.Setoids`, `Setoids.Maybe` and `SFunM.Test.Possibility`.
- `src/Categories/Monad/Graded/Trivial.agda :: ungraded` (90): only importer `SFunM.Test.Possibility`.
- `src/Data/List/Relation/Binary/BagAndSetEquality/Ext.agda :: ∷-absorb` (21),
  `src/Data/List/Relation/Unary/Any/Properties/Ext.agda :: Any-congˢ` (36),
  `src/Relation/Binary/Bundles/Ext.agda :: _⟨_≈_⟩` (14): each has a single importer
  (`SFunM.Test.Possibility` or `Possibility.Setoids`).
- `src/Function/Bundles/Ext.agda :: discreteFunc` (15): its importers are the two `Setoids.Discrete*`.
  stdlib only has the *dependent* `→-to-⟶`, so this helper has no library replacement.

Two of the stranded modules are KEEP by ruling: `Setoids.Maybe` (the commutative monad) and the
`KleisliTriple⇒ᴹ` part of `Monad/Construction/Kleisli/Ext`. Each then needs a root `import` line,
or it stops being checked at all. `Setoids.Maybe :: Maybe-DiscreteMonad` (and with it the
`Discrete`/`Setoids.Discrete` imports) loses its only consumer, so drop it, −10. Once `Setoids.Discrete`
is gone, `Monad/Discrete :: Elementwise` has a single producer shape (inline `record`s in
`Machines.Base`, `SFunPartial`, `Class.Monad.Ext`). Folding it back into `DiscreteMonad` removes one
record and the `hiding (module Comm)` plumbing (−10). That step touches `Machines.Base` (another part),
so it is a cross-part follow-up.
This is a coordination item for the agent that deletes the SFunM tree. It is not committed here: the
deletion gate (no importer) only holds after that agent's change.

### 2. `src/Data/Rational/LowerReal.agda :: _≲_, _≈_, LowerReal, _≤ℚ_, ≲-≤ℚ, Cut…` — the unused half (≈ −75)
The module's only importer, `Dp.agda`, uses `≼-refl`, `≼-trans`, `≼⇒≼[0]` and `≼[]-mono/-trans/-resp`
(`Dp.agda:404-423`). These have **no consumer** anywhere in `src`: `_≲_`, `≼⇒≲`, `_≈_`, `halves`, `half-pos`,
`≈-trans`, `≈-isEquivalence`, `LowerReal`, `≈⇒≲`, `_≤ℚ_`, `≲-≤ℚ`, and the whole *Cuts* section
(`Cut`, `Cut-down`, `Cut-rounded`, `≲⇒Cut-⊆`, `Cut-⊆⇒≲`, `≲⇔Cut-⊆`, `≈⇒Cut-≐`, `Cut-≐⇒≈`, `≈⇔Cut-≐`).
Under the maintainer's test this is a DELETE. What remains is "domination of ℚ-sequences, with and
without slack". The header's Coquand–Spitters citation then justifies only the name. Either keep the
name with a one-line header ("ℚ-sequence domination, the presentation of lower reals by their
approximants"), or rename to `Data.Rational.Sequence.Domination`. Your call, since you wrote the
module in `b0b1d057`. `docs/lower-real-reading-spike.md` records why `Cofinal`/`Dom` stay as the
inference adapters, and that rationale is unaffected.

### 3. Zero-consumer public lemmas (≈ −30; each `grep -rnF` over `src` hits only its own definition)
- `src/ProbabilisticLogic/Distribution/RationalDist/Setoid.agda :: >>=ᴹ-congʳ`
- `src/ProbabilisticLogic/Distribution/RationalDist/Partial.agda :: >>=⊥-congˡ`
- `src/ProbabilisticLogic/Dp/Settle.agda :: Settles-bot⋆, Settlesᵀ-cum`
- `src/ProbabilisticLogic/Distribution/RationalDist/Advantage.agda :: adv⊥-sym, adv⊥-triangle, adv⊥-≈⇒0`
  (and then `advᵇ⊥-sym/-triangle`, which D-foundations:194 already noted as zero-consumer)
- `src/ProbabilisticLogic/Dp.agda :: cum-*ₗ` (the linearity family keeps `cum-add`/`cum-const`), `:: laterₚ-≈ₚ`
- `src/Categories/Category/Monoidal/Properties/Ext.agda :: αρ-λ` (mirror of the used `ρα-λ`)
- `src/ProbabilisticLogic/Dp/Advantage.agda :: ≼ₚ[]-refl`
Recommendation: delete all of them except `laterₚ-≈ₚ`. "Delays are invisible" is the defining law of
the delay monad's equivalence, and it is the one a downstream user would look for first (rule 32).

### 4. `src/ProbabilisticLogic.agda` (whole module) — a forwarding index with no job (−7, plus one root line)
It imports `RationalDist`, `.Expectation` and `.Setoid` without `public`. The root's
`open import ProbabilisticLogic` (`CategoricalCrypto.agda:108`) is its only importer, and all three
modules are reached from the root without it (closure check with that line removed). Delete the
module and the root line. This is not committed because the root is integration-owned.
D-foundations:210 was about its old `public` re-exports, and the code has changed since.

### 5. `src/Categories/GConstruction{Trace,Loop,Embedding,Monoidal}.agda :: module C` — qualification noise (≈ 0 LOC, ~300 `C.` prefixes)
Each file builds a private `module C` (Category + Traced + Shorthands + selected reasoning) and then
writes every name qualified: `C.trace (C.σ⇒ C.⊗₁ C.id C.∘ …)`. Inside the `WithTrace`/`Embed` bodies no
local name clashes with `C`'s (`α`, `γ`, `mid`, `β` and the `Laws` fields are disjoint from Category,
Traced and Shorthands). A local `open C` would therefore turn most statements into the notation every
other module uses (rule 19). This is family-wide, and `GConstruction.agda` is outside this part, so it
is suggested rather than committed. Not spiked here because of the disk budget (Suggestion 9).
First step: `GConstructionLoop.WithTrace` (12 lines).

### 6. `src/ProbabilisticLogic/Distribution/Uniform/Duplicate.agda :: memb, memb-∈, memb-∉` → stdlib decidable membership (≈ −8)
`memb h hs` is definitionally `does (Any.any? (h ≟_) hs)` (`any?` is a fold of `_⊎-dec_`, whose `does`
is `_∨_`). With that, `memb-∈`/`memb-∉` become `toWitness`/`fromWitnessFalse` over `T (does …)`.
`memb-∈`/`indicator-≤` have no consumer outside the module. `memb` itself is computed with in
`GamePlaying.Test` (closed terms), so any change must keep it reducing there. Not spiked.

### 7. Banner form in `ProbabilisticLogic/**` (≈ +55 lines if applied)
About 55 section banners in the `Dp*`/`RationalDist*` files are two-line (`-----` / `-- Title`) rather
than rule 25's boxed form. The whole tree uses the two-line form consistently, so either the rule or the
tree should change. Applying the boxed form costs a pure-dash line per banner, against the
conciseness rules. Recommendation: amend rule 25 to accept the two-line form.

### 8. `src/Data/Bits/Codec.agda :: list-codec` via `vec-codec` (−13) — written, NOT verified
`list-codec`'s `encs`/`decs`/`encs-law` repeat `vec-codec`'s `enc`/`dec`/`law` at `length xs`. Define
`enc xs = N.encode (length xs) ++ V.encode _ (fromList xs)` and
`dec bs = N.decode bs >>= λ (k , r) → mapᵐ (map₁ toList) (V.decode k r)`, with
`module V (k : ℕ) = Codec (vec-codec C k)`. The law then closes by the same `rewrite` chain plus stdlib
`Data.Vec.Properties.toList∘fromList`, so `list-codec` moves below `vec-codec`. The patch is in the
scratchpad (`R3D/codec-unverified.patch`). It was reverted because there was no time to check `Codec` and
its leaf `Examples.ChimericLedger.Serialize`.

### 9. Unfinished sweep classes: a work item, stopped on disk, not on judgment
On this sandbox each pagda check leaves a source snapshot in the nix store, and `nix-store --gc` is
off-limits in this campaign. The overlay went from 11 GB free to 5.6 GB in the first ~45 min of the
review, with four reviewers running. One cold root check alone took 1.4 GB. The import-drop sweep runs one
check per import line (≈ 600 checks over 63 files), which is incompatible with that. It was stopped
after 21 files (7 prunes kept). Remaining:
`import-drop` 42 files; `implicit-drop`, `join-lines`, `binder-drop`, `using-minimize` 63 files each;
`with_case.py` 11 sites (`Data/List/Run` 3, `RationalDist/Support` 3, `Uniform/Collision` 1,
`Uniform/Duplicate` 4); `where_inline.py` 124 flagged sites (`QUALITY-REVIEW-R3D.d/enum-where.json`).
Every site in the enumeration JSONs is listed, and none is dispositioned by a family verdict. Run these
after a store GC, all classes in one session (`sweeps.sh` in the scratchpad already chains them).

## Tried, not worth it
- `src/Categories/GConstructionMonoidal.agda :: homomorphismᴳ` (where-bindings `Φ₁ Φ₂ Ψ BoxL BoxR residue`)
  — dropped their type signatures (−20). Red: `UnsolvedConstraints`/`UnsolvedMetaVariables`. The level
  and hom-type metas of the `where` RHSs are not determined without the annotations, because the chain
  only mentions them under `C.trace`. The signatures are load-bearing.

## Integration-owned files (noted only)
- `src/CategoricalCrypto.agda` (root): line 108 `open import ProbabilisticLogic` (Suggestion 4); its header
  lists `SFunM.Test.Possibility` among the tests, which goes stale with the SFunM deletion; after
  Suggestion 1 it needs `import Categories.Monad.Setoids.Maybe` and `import Categories.Monad.Construction.Kleisli.Ext`
  to keep the two ruled-KEEP modules checked.

## Out-of-scope edits
None.

## Not reached (hard deadline 15:57)
- Sweep classes: `implicit-drop`, `join-lines`, `binder-drop`, `using-minimize` (63 files each),
  `import-drop` on the remaining 42 files, the `with_case.py` spike (11 `enum-with` sites) and the
  `where_inline.py` spike (124 flagged `enum-where` sites). See Suggestion 9. The enumeration JSONs are committed,
  but **those sites are not dispositioned**.
- Files read only for consumer and comment work, without a full proof-simplification pass:
  `Dp/{Mass,Settle,Settle/Iter,Coin,Commutative,Dominate}`, `RationalDist/Support`, `Possibility/Setoids`,
  `GConstructionHomCoherence`. Most of these were swept in round 1, and `Support`/`Possibility*` are
  Suggestion-1 deletions.
- Not spiked: Suggestions 5 (`C.` qualification), 6 (`memb`), 8 (`list-codec`, written but not checked).
- Statement audit (dimension 1): nothing new found in the files read. It was not done systematically
  for the unread files above.

## Verification
- Soundness baseline: 16 lines before and after, identical. Byte-level NUL check over every changed blob:
  clean. `git diff --check 27cda67f HEAD`: clean.
- Root `src/CategoricalCrypto.agda` (`-M8G -H2G`), run 1 (all committed changes plus the spikes): 202
  modules elaborated, every touched module included (all `Dp.Iter*`, `Expectation`, `Dp`,
  `Dp.Advantage`, `Possibility`, `Support`, `Monad.Discrete`, `GConstruction{Trace,Loop,Embedding,*Coherence}`,
  `Traced.Ext`, `Symmetric.Properties.Ext`, `Kleisli.Discrete.Pure`, `GradedKleisli.Coherence`, `Dp.Elgot`).
  It then went red on the `GConstructionMonoidal` spike (see *Tried*), which was reverted.
- Root run 2 (after the revert): `GConstructionMonoidal`, `Data.Bool.Properties.Ext`, `Machines.Base` and
  174 further importers green, warn-grep empty. The run was **killed at the 30-min background limit** while
  checking `Examples.ROCommitment.Transport`, so the root closure did **not** complete. The non-root leaves
  (`ChimericLedger.{Serialize,Transfer}`, `MerkleDamgard.{Pin,QueryBound}`, `Abstract2.*`,
  `RandomOracle`, `Standard2.Morphism`, `GradedKleisli.Functorial.Category`, `Class.Monad.Ext`) were
  **not checked**. Of those, only `Serialize`, `Pin` and `QueryBound` reach a file this branch changed
  beyond the root cone (`Data.Bits.Codec`, `Data.List.Run`, `Data.Vec.Properties.Ext`), and this branch did
  not change those three files.
- Warn-grep (rule 6) over both root logs: empty.
