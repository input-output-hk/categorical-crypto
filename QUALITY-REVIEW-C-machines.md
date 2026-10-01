# Quality review — protocol-rewrite, part C-machines (2026-09-29)

Scope: the 72 files of `scope-C-machines.txt` at `c71d95fe` — `SFunM/**`, `SFunPartial`,
`SFunPossibility`, `Machines/**`, `GamePlaying*`, `Protocol*`, `Interaction`, `Strategy`,
`OracleCall`, `Iface`. After commit 1 below, 57 files remain.

Verification: tip `0d98eb85`.
- **Commits 1–7 are green together.** One aggregate check covered the root
  `CategoricalCrypto.agda` and every other import-DAG leaf the scope reaches:
  `Examples.ChimericLedger.{ReplayFamily,Serialize,Transfer}` and
  `Examples.MerkleDamgard.{Pin,QueryBound}`. It gave rc=0 with an empty warn grep; 163 modules were
  re-elaborated, taking 447 s at `-M8G -H2G` (a `-M16G` request starved in the gate queue for
  30 min).
- **The cluster commits touch disjoint files**, and the only cross-cluster name change is `βᴹ`,
  which moves inside the Trace commit (`G` mentions it only in a comment). Every other edit is
  proof-internal, private, or comment-only, so each intermediate commit's modules see the same
  interfaces as at the verified tip.
- **Commit 8 (`using-drop`) is green only per file**, by the toolkit oracle. It post-dates the
  aggregate run. It changes only non-`public` opens, so no importer is affected.
- **Soundness baseline** (rule 3, all of `src`): 16 before, 16 after.
- **Stopped again at the disk floor** (1.99 GiB free; the nix store refilled to 17 GiB from other
  worktrees) during the `using-drop` class. The remaining sweep classes are open (see *Sweep work
  item*).

Sweep tally (toolkit JSONs in `QUALITY-REVIEW-C-machines.d/`):

| Class | Status |
|---|---|
| `enum-with` | 21 sites enumerated and dispositioned |
| `enum-where` | 183 sites (122 flagged) enumerated and dispositioned |
| `enum-comments` | 391 blocks enumerated and dispositioned |
| `using-drop` | 43 of 57 files swept, edits kept (commit 8); stopped at `Protocol/Machine/Trace/Compose`, 14 files left; no tally JSON (the tool writes it at the end) |
| `implicit-drop`, `join-lines`, `binder-drop`, `import-drop`, `using-minimize`, `with-case`, `where-inline` | not run |

## Committed (you can skim these)

- `aed1c111` Delete the unreached `SFunM.Spike` tree (15 modules, −3,755 LOC).
  - Nothing outside the tree imports any of it, and the root doesn't either (`grep -rnF 'SFunM.Spike'`).
  - The spike's result is `Machines.Core`, which opens with the same header text.
  - `docs/protocol-rewrite.md:148-149,341` still cite `Spike.*` (out of scope; not edited).
- `485ae895` `SFunM.Kleisli` header: replace the stale "`Spike` certifications run on this one" with
  the remaining consumer. Checked green.
- The five commits below are the review's own edits, one per cluster:
  - `f36c85bb` Machines core (11 files, +41/−90).
  - `bc4a6eb6` Machines.Trace (5 files, +48/−104).
  - `28125833` GamePlaying (5 files, +92/−167).
  - `ff1d692b` Protocol layer (13 files, +102/−180).
  - `ef464f6a` SFunM stack (8 files, +31/−83).

  Contents by cluster:

- **SFunM** (comment-only, plus one eta-wrapper):
  - Kleisli / Kleisli.Monoidal / Kleisli.Properties / Monoidal / Morphism / Properties / SFunPartial /
    SFunPossibility headers and comments: stale sibling narration and design narration cut; rule 24
    duplicates merged into the headers.
  - `SFunM/Kleisli.agda`: drop the overclaim "Composition is associative and unital only up to the
    monad's commutativity". Only `∘ᵉ-resp-≈ᵉ` needs `trace-∘`.
  - `SFunPartial`: three standalone `∎`s joined (rule 13).
  - `SFunPossibility :: supp⊥-cong′` is an eta-wrapper of `supp⊥-cong` with the same telescope:
    inlined (rule 18).
- **Machines.Trace**:
  - Dead `MonoidalUtilities` import/open in `Trace` removed.
  - `βᴹ` moved from `Trace` to `Fubini`, its only consumer (rule 28).
  - `[]-δ⇐` reproved via `tstep-str` (its private `δ⇐-+₁` re-proved that naturality).
  - `cancel-s` / `collapse` / `round` via `Frame.pad-inv`.
  - Seven `merge₂ˡ ○ (refl⟩⊗⟨ e) ○ split₂ˡ` rewritten as upstream `parallel refl e`.
  - `pure-swap = pure-[] pure-i₂ pure-i₁`.
  - Import alias unified to `MCat` (Vanishing, Superposing).
  - Dead `open Equiv` in Congruence removed.
  - Header fixes: `Trace`'s "solve-i₁/i₂/loop are the whole interface to iter" was false;
    `vanishing₁ᴹ`'s "map out of the initial object" was inaccurate.
  - Single-definition banners cut.
- **Machines core**:
  - `Frame`:
    - `swp-natural` / `swp-natural′` become one-line instances of `swp-nat` (−18).
    - `λλ-α` replaced by upstream `coherence-inv₁` + `unitorˡ-commute-to` (−11).
  - `Pure :: swap-copair = []∘+₁`.
  - `Base`: rule-10 import order.
  - Accuracy fixes:
    - `Core :: State`'s "a degenerate discard annihilates every trace": nothing reads `discard`.
    - `Sim`'s "𝒫 is a parameter of this module alone": six modules take it.
    - `Base`'s "eight elementwise laws": eight fields, five laws.
    - `Tensor.Structural` cites `⊗ᵉ-pureˡ/ʳ` as functor laws.
    - `Pure`'s "mirror pair".
    - `Reassoc` cites a nonexistent `lim-hexagon`.
    - `G`'s "Nothing here is a hypothesis": it takes `Elgot`, and its `βᴹ` pointer was stale.
  - `Collapse` / `Iteration` / `G.Lax` narration cut.
- **GamePlaying**:
  - `Partial :: runWith⊥-bisim` becomes two applications of `runWith⊥-bisimʳ` at the identities
    (−14). This refutes the comment "not an instance … only funext identifies it".
  - `Partial`/`Hop` `lhs≡0` replaced by `Data.Rational.Properties.Ext.∣x-x∣≡0`.
  - `Potential :: 0≤scaled` becomes `0≤*`.
  - `∨-cert.bad` hand-rolled `aux` becomes `with … in`.
  - `Average :: endProb-bad` becomes `endProb-frozen` at `Fz = (_≡ true) ∘ bad`.
  - `FLGP⊥`'s unused `in eqbad` dropped.
  - Four `(λ b → bool→ℚ b)` eta-reduced.
  - Headers fixed:
    - `Potential`'s "never lowers": the hypothesis imposes no monotonicity.
    - `Average`'s "rise": `Frozen` forbids any change.
    - `Hop`'s "two instances": there are six.
  - Duplicate comments cut.
- **Protocol**:
  - `Trace.Compose`: `dispatch-f/g = E⊥-map …`; 82× `Col.MC.` becomes a local `module MC = Col.MC`
    (rule 19).
  - `Pin :: half` becomes stdlib `½` (rule 30).
  - `Pin :: agree-∘`'s comment overclaimed: it said the pin breaks if `𝒢`'s trace composition
    disagrees, but `morphism relayed` never runs `𝒢`'s composition.
  - `Agree` header's dangling "(`Protocol.Machine`'s header)" cross-reference removed.
  - `Compose` header condensed; "down from 269 s" dropped.
  - `Raw`/`Total`/`Observe`/`Machine`/`Protocol`/`OracleCall`/`Strategy`/`Interaction`: narration
    and rule-24 duplicates cut.
- `0d98eb85` Sweep `using-drop`, first 43 of 57 files (20 files, bare opens; each kept edit green per the toolkit oracle).

## Suggestions (need your call) — ranked by LOC / complexity removed

### Public API / module layout

1. `src/CategoricalCrypto/SFunM/Kleisli.agda :: SFunᵉ` (whole `SFunM/Kleisli/**`, plus
   `SFunM/{Monoidal,Morphism,Properties}`): **the SFun machine layer is written twice.**
   - **Duplication.** `SFunM.Kleisli*` (891 LOC) is a definition-by-definition copy of
     `SFunM` + `SFunM/*` (957 LOC):
     - `SFunType`, `SFunᵉ`, `trace`, `eval`, `_≈ᵉ_`, `trace-∘` (the same 10-step chain), the
       category laws, `_⊗ᵉ_`, the seven structural morphisms, `⊗ᵉ-homomorphism` (60↔60 verbatim),
       `⊗-split`, and all ten `mapᵉ*`.
     - Often the Kleisli copy is the shorter proof (`σ-conjᵉ`, `statelessᵉ-natural`).
   - **Neither is the machine layer.** `Machines.*`, `UC.*` and `Protocol.Machine.*` run on
     `Categories.Monad.Discrete.DiscreteMonad`. `SFunM` is reached only by `SFunPartial`,
     `SFunPossibility` and `Examples.RandomOracle` (for `SFunType` only); `SFunM.Kleisli` only by
     `Examples.Possibilistic` and its test.
   - **The header's reason doesn't hold.** "Neither parametrisation subsumes the other" is true of
     the two parameter types, but not a reason for two copies: both use only the level-0
     elementwise interface, which is exactly `DiscreteMonad 0ℓ`.
   - **Plan (staged):**
     1. Adapters, about +25: `Setoids.Discrete.toDiscreteMonad`, and `Class` instances →
        `DiscreteMonad 0ℓ`.
     2. Reparametrise the Kleisli stack by `(Mo : DiscreteMonad 0ℓ)`, about ±0.
     3. Port `SFunPartial`/`SFunPossibility` to `Dist⊥ᴰ`/`Listᴰ`, delete the `Class` stack
        (−957), and rename.
     - Net about **−900 LOC** and one monad interface shared with `Machines.*`.
   - **Cruxes to spike:**
     - (a) `Examples.Possibilistic`'s `refl` evals still reduce through `DiscreteMonad` fields.
     - (b) `SFunPartial`'s recorded >120 s record-type comparison: use one named `Dist⊥ᴰ` on
       both sides.
     - (c) Rule-1 care: the `Class` `List` instance is `_≈𝒫_`, coarser than `_∼[set]_`, so
       Possibilistic needs a local set-equality instance to keep its statement.
   - **Constraint:** touches integration-owned `SFunM.agda` and `RandomOracle.agda`.
   - **Longer term:** the SFun layer is a third spelling of `Machines.*`, with the same law
     names and no bridge. A quotient functor `Mealy-Category (Klᴹ M) → SFunᵉ-Category`
     would connect them.
2. `src/CategoricalCrypto/Machines/Collapse.agda :: open import …Pointwise public`: a forwarding
   re-export (rule 19), and the L304 relocation is half-done.
   - `Pointwise` also duplicates `Machines.Pure`:
     - `α+⇒-fn`/`α+⇐-fn`/`+-swap-fn`/`+₁-fn` = `assocʳᵏ`/`assocˡᵏ`/`swapᵏ`/`+₁-pureᵏ`.
     - `⊗-pure h` = `pureᴵ h`.
     - `tstepL/R` = `tstep-inj₁/₂`.
     - The `Pointwise` copies have 0 external uses.
   - Target: one "structural maps are functions" module. Delete the four `-fn`s and route
     `α⇒ᶠ`/`α⇐ᶠ`/`σᶠ`/`⊗ᶠ` through `pureᴹ-cong`, rename `⊗-pure`→`pureᴵ` (10 uses; this also
     removes L304's clash with `KDP.⊗-pure`), then drop the `public` and open `Pointwise` at the
     13 importers.
   - About −40 LOC. Unverified; spike needed.
3. `src/CategoricalCrypto/Protocol/Machine/Total.agda :: totalRun-∘`, `totalRun-resp-≈ᴹ`: zero uses
   anywhere; `TotalRun`'s one consumer is `UC/Seam/Grounded`.
   - Move `TotalRun` next to `runᴹ` in `Protocol.Machine` and delete the module (−55 LOC).
   - Needs a root edit (integration-owned).
   - Related: `Protocol/Observe.agda :: transfer`/`transfer-at` (+ private `≤-shift`, −30) and
     `Protocol/Machine/Raw.agda :: rawKernel` (−16) are also zero-use public. Rule 32 makes all of
     these yours; `Observe`'s header used to advertise `transfer`.
4. `src/CategoricalCrypto/Protocol/Machine.agda :: Closed` (proposed): the closed-machine type
   `MC.Machine (⊥ ⊎ Neg B) (⊥ ⊎ Pos B)` has three spellings:
   - `UC.Machine.Run.Closed`;
   - `UC.Machine.Proc unitᴵ B`;
   - literal at `Protocol/Machine.agda:101`, `Raw:56`, `Total:45,48`.
   - `GamePlaying/Defer/Run` imports `UC.Machine.Run` only for `Closed`.
   - Define it once beside `runᴹ`. This needs an edit to `UC/Machine/Run` (out of scope).
5. `src/CategoricalCrypto/Machines/Base.agda :: 𝒢ₚ`/`Tracedₚ`/`ℳₚ`: `Base` pulls the whole
   G-construction closure (it imports `Machines.G`/`Bundle`), but 38 of its 60 importers use only
   `Dₚ-DiscreteMonad`/`𝒱ₚ`/`distₚ`/`𝒫ₚ`/`Elgotₚ`.
   - Split the instances into a G-side module (22 importers).
   - Perf; measure (rule 31).
6. `src/CategoricalCrypto/GamePlaying.agda :: open … Partial public using (cond; cond-diag)`: a
   rule-19 re-export layer. The underlying `cond` → `if_then_else_` swap is L865 (still open, now in
   `Partial.agda:31-37`).
   - If L865 is declined: delete the re-export and import `Partial using (cond; cond-diag)` in its
     four users (MD/Core, ROCommitment/Game, Hiding/Game, Hiding/Defer); all four are out of scope.
7. `src/CategoricalCrypto/SFunPartial.agda :: unbot`: a public renaming of `Data.Sum.Ext.unitˡ⇒`,
   re-exported again by the root, with 0 outside uses. Its import also sits mid-file (rule 10).
   Drop it and use `unitˡ⇒`.

### Statement audit

8. `src/CategoricalCrypto/Machines/Core.agda :: State.discard` (with `Sim :: _≲_.θ-discard`):
   **no observation reads `discard`.**
   - Every concrete state sets `discard = λ _ → returnₚ tt` (about 15 sites).
   - The only consumers are the `θ-discard` obligations themselves, plus `Frame`'s `⊛-discard*`
     family, `Assoc :: dsc-u`, `Structural :: discard-σ`, `Naturality :: d-ok` and
     `Pointwise :: discard-⊛`.
   - `Sim/Lax`'s own header says "nothing below or downstream spends it".
   - Dropping the field weakens `_≈ᴹ_`, so every `≈ᴹ` statement claims less (rule 1), which is
     why this is yours.
   - It would remove about 90–130 LOC and dissolve most of L323: `_≲_` and `_≲ˡ[ id ]_` would
     then differ only by `identityʳ`.
9. `src/CategoricalCrypto/GamePlaying/Average.agda :: endProb-avg`, `badProb-avg`: the public
   conclusion is stated `≤ℚ Φ m f` with a **private** `Φ`, so the statement names something the
   user can't see. Spell `Φ` out or make it public.
10. `src/CategoricalCrypto/Machines/Trace.agda :: van₁-step`: proved generically in the loop object
    `X`, but `vanishing₁ᴹ` is stated only at `⊥`. A generalisation is available if wanted.

### Simplifications / perf not committed (judgment needed)

11. `src/CategoricalCrypto/Protocol/Machine/Agree.agda :: prAgree`: **two proofs of one
    agreement.**
    - `prAgree` (callAgree/runAgree over `Dp.Stable`) is `Raw.rawPr` at `morphism P`, with
      `Kᴾ (idle s) q = Dmap⊥ (map₁ idle) (kernel P s q)` and a `drive-settles` lemma of about
      20 LOC.
    - Missing piece: generalise `GamePlaying.Partial.runWith⊥-bisim`'s conclusion from `Pr₁⊥` to
      `E⊥ … G` (a strict strengthening).
    - Then `Dp.Stable` loses its only consumer. Move `coin-bind-cum` to `Dp.Coin` and delete
      `Dp.Stable` (90 LOC; out of scope, part D).
    - About −90 LOC and one module.
    - `Stable`/`Settle` are *not* two spellings: `Settles ⇒ Stable` pointwise; see Tried.
12. `src/CategoricalCrypto/Protocol/Safety.agda :: HitCert`, `super`: **the supermartingale
    induction is written a third time.**
    - `HitCert P Bad ε` is field-for-field `GamePlaying.Partial.SuperCert⊥ (kernel P) Bad (init P) ε`.
      This needs `Observe.Reached` to be `Expectation.Mb`, which it literally is, clause for clause.
    - `super` follows from `badProb⊥-super` and a new 15-line `hit≤badProb⊥ : Pr₁⊥ (hitFrom … (Bad s) s d) ≤ badProb⊥ (kernel P) Bad s d`.
      The inequality is strict only where the run diverges after a hit.
    - **Spiked** (`QUALITY-REVIEW-C-machines.d/SafetySpike.agda.txt`): the whole module
      typechecked except one `subst` motive left as `_`, since annotated. The re-check never ran
      (disk).
    - The proof swap alone is −11 LOC. With `HitCert := SuperCert⊥ …` and `Reached := Mb` it is
      about −60 LOC, and `Birthday` stays source-compatible.
    - Matches ledger L1028 by identifier, which is why it is not committed.
13. `src/CategoricalCrypto/GamePlaying.agda :: badProb`: one bad-probability.
    - `badProb resp = badProb⊥ (embedᵏ resp)` deletes `badProb-embed` and `badProb-bad`.
    - `badProb-super` (zero code consumers besides `badProb-bounded`) goes, and
      `badProb-bounded c = badProb⊥-bounded (prune-cert (λ _ _ → false) c)`.
    - About −30 LOC. `Average.badProb≡endProb` and `Hop.runWith-join` each need one `Eⱼ`; MD/Core
      needs re-measuring.
    - Also: `Coupling.FLGP`, `Coupling⊥.FLGP⊥` and `Hop.runWith-join` are three copies of one
      identical-until-bad skeleton. `FLGP` is a `runWith-join` instance (−10..−30).
14. `src/CategoricalCrypto/Machines/Trace/Fubini.agda :: trace-comm`: derivable generically in
    `Traced.Ext` from `vanishing₂` plus conjugation by the symmetry (−60..−100).
    - The literature claim is UNVERIFIED.
    - The crux is whether `Traced.Ext.Laws` accepts a `trace-conj-σ` field, which is a public
      interface change.
15. `src/CategoricalCrypto/Machines/Trace.agda :: iter-onL`: `iter-onL`/`solve-onL`/`onL-pre` are
    the σ-mirror of `iter-ctx`/`solve-onR`/`onR-pre`. One `traceStep-onL` by conjugation through
    `traceStep-sim` removes all three (about −25). Naturality's header records 397 s when merged,
    so measure.
16. `src/CategoricalCrypto/Protocol/Machine/Compose.agda :: trace-pt`: the private
    `loop`/`exit`/`bodyᴹ`/`loop-pt`/`solve-pt`/`trace-pt` block is `UC.Seam.Plug.Loop`.
    - Relocate `Loop` into `Machines.*` (rule 27) and use it from both (−28).
    - Re-measure the 11 s budget.
17. `src/CategoricalCrypto/Strategy.agda :: IsWatch`: fossil generality. Every instance is
    `watchFrom report`, so the `w`/`IsWatch` binders in EventLift, Monitor/Agree and
    ChimericLedger/Property could name `watchFrom` directly (−25).
18. `src/CategoricalCrypto/Machines/Tensor/Structural.agda :: pure-iso`: `pureᴹ` is a functor in
    disguise. Build `pureF : Functor U Mealy-Category`; then `Bundle`'s three iso records are
    upstream `[ pureF ]-resp-≅`, which deletes the seven `λᴹ/ρᴹ/αᴹ-iso*` lemmas (−10..−15).
19. `src/CategoricalCrypto/SFunPartial.agda :: strip⊥`, `trace-mapin`, `trace-mapout`,
    `trace-cong⊥`, `≈ᵉ-trans⊥`, `≡→≈ᵉ⊥`, `strip-eval`, `strip⊥-cong`: 0 uses anywhere.
    - `strip⊥` is left-unitor conjugation, so this is generic material written out at `Dist⊥`.
    - Delete it (−120), or redefine `strip⊥` as `λ⇒ᵉ ∘ᵉ (f ∘ᵉ λ⇐ᵉ)`.
20. `src/CategoricalCrypto/Machines/Frame.agda :: ⊛-discard`, `⊛-point`, `⊛-discardʳ`, `⊛-pointʳ`:
    each is `⊛-discard₂`/`⊛-point₂` at an identity, used once, all in `Trace/Naturality` (−12).
    - `discard-onL`/`dsc`/`dsc-swp` are used only at `d = id`; a direct `onL-collapseʳ` proof is
      −18.
    - All are public, so rule 32 applies.
21. `src/CategoricalCrypto/Machines/Core.agda :: onR`: the same body as `onRᵍ`, written twice.
    `onR = onRᵍ` needs a measurement: 52 files use `onR`.
22. `src/CategoricalCrypto/Machines/Sandwich.agda :: sandwich-∘`, `squeeze`: `sandwich-∘`'s body
    is `map-map`, and `squeeze` mixes two reasoning dialects (−6).
    - `UC/Machine/Slide.agda :: sandwich-id` belongs here too (rule 27; out of scope).
    - Not landed for verification budget only.
23. `src/CategoricalCrypto/Machines/Trace/Superposing.agda :: reconcile` (with
    `Vanishing.vanishing₂.reconcile` and `Fubini.reduce`): the same pure-conjugation proof three
    times. One `pure-conj` lemma in `Machines.Category` (−10).
24. `src/CategoricalCrypto/GamePlaying/Partial.agda :: prune-Dmap` (proposed): "`Dmap⊥` commutes
    past the cut" is written three times (`Coupling.FLGP.ker`, `ROCommitment/Realization/Bound ::
    marginalᴿ`, `bisimᴿᵍ`/`bisimᴵᵍ`). Net about −10.

## Tried, not worth it

- `src/CategoricalCrypto/Interaction.agda :: runWith` (with `runWith⊥`,
  `Protocol.Machine.runᴹFrom`, `Protocol.Observe.hitFrom`): one strategy fold `fold askB coinB ret`
  would make all four `refl` instances.
  - It saves about 6 LOC.
  - It adds a δ-layer to every `refl` pin (MerkleDamgard/Pin, Pin, GamePlaying/Test).
  - The lemmas about the runs still don't unify, because they live in four different relations
    (`≡` on `E⊥`, `≈Mℚ`, `≈ₚ`, `Settles`).
  - So the run function is not spelled twice in any way worth merging; the duplication is in the
    proofs about runs (items 11–13).
- `ProbabilisticLogic/Dp/Stable.agda :: Stable` vs `Dp/Settle.agda :: Settles`: not two spellings
  of one notion. `Settles-cum` is `Settles ⇒ Stable` at each non-negative test, and the converse
  fails because `Stable` has no halting. Item 11 retires `Stable` by making it unused instead.

## Sweep work item (unfinished, per contract)

- **Automatic classes.**
  - `using-drop` finished 43 of 57 files (commit `0d98eb85`). It stopped at
    `Protocol/Machine/Trace/Compose.agda`; that file's in-flight candidate was reverted, and it and
    the 13 files after it are unswept.
  - `implicit-drop`, `join-lines`, `import-drop`, `using-minimize`, `with-case` (21 sites),
    `where-inline` (122 flagged sites) and `binder-drop` were not run: the disk floor was hit first.
  - Measured cost: `using-drop` took about 35 min wall for 43 files under the contended gate.
    Expect roughly 45 min per remaining class, and about 5 h for all seven.
  - Resume: `/tmp/qc-sweeps3.sh`, the driver that ran the classes and committed per class; it
    lives in /tmp, not in the repo. Point it at the 14-file tail for `using-drop` first. Before
    committing `binder-drop`, check the root and the other scope leaves.
- **Enum dispositions.** The read-only finders dispositioned every enum site, with exact
  replacement text (cluster reports, summarised here).
  - `enum-with` (21): all KEEP, with site reasons (goal abstraction or `in`-equation use), except:
    - `badProb`/`badProb⊥`'s four sites, SWAP candidates (spike);
    - `FLGP⊥`'s unused `in eqbad`, dropped (commit `28125833`).
  - `enum-where`: INLINE dispositions for the flagged single-use bindings in:
    - `Pure :: leaves`, `padded`;
    - `Assoc :: dsc-u`/`pt-u`/`step-u`/`brE`/`decompˡ`/`decompʳ`;
    - `Structural :: discard-σ`/`point-σ`;
    - `Trace :: lb`/`sv`/`ent`/`branch₁₂`; `Congruence :: branch₁₂`/`enter`;
    - `Fubini :: shift`/`cancel-s`/`hyp`/`tensor`/`inner`;
    - `Naturality :: d-ok`/`p-ok`/`s-ok`;
    - `Superposing :: loop-relabel`/`branch₁₂`/`step-eq`;
    - `Vanishing :: tstep-ν`/`branch₁`/`nested₁₂`/`branch₂`;
    - `Raw :: branch`/`junction`; `Protocol/Machine/Trace :: value`;
    - `Hop :: bis⊥`/`lhs≡0`; `Partial :: lhs≡0`; `Potential :: aux`;
    - `SFunM/Monoidal :: kern` (×2); `SFunM/Morphism :: kern`.

    The applied subset is committed: `shift`, `cancel-s`, `collapse`, `δ⇐-+₁`, `lhs≡0` ×2,
    `aux`. Every other site is KEEP with a site reason (multi-use, a signature that pins a middle
    term, or a pattern-matching local).
  - `enum-comments` (391 blocks): every block has a CUT/KEEP/REWORD verdict. The CUT and REWORD
    ones are committed.

## Carried forward from `QUALITY-REVIEW.md` (in-scope entries, latest status; channel unchanged)

**Still open:**
- L227 `Sim/Lax :: ≲ˡ-trans`, zero uses.
- L243 `Collapse :: compose≈∘ᴳ`. The finder adds: `Collapse.composeᴳ` is a second opaque
  wrapper around upstream's `GC.composeᴳ`, 0 external uses; `compose-raw≈∘ᴳ` can be
  `ℳ.Equiv.sym (GC.composeᴳ-raw …)` (−13).
- L271 `Safety :: hit-bounded` note.
- L304 remainder (see item 2).
- L323 strict/lax simulation (see item 8).
- L342 `Base :: 𝒢ₚ-Monoidal`, `Frame :: αρ-λ`/`onRᵍ-⊗id`, still zero uses.
- L350 `Collapse :: γ-pure`. The finder reports the premise is wrong: upstream `γ` is right-nested
  and `∘ᴹ` is not definitionally associative. Record it as "declined" if you agree.
- L359 `Frame :: 𝕄` to `Reassoc`; `id⊗id-comm` twice.
- L865 `cond`.
- L879 `Compose` private module block (wider than recorded: `KP` and `𝒢` duplicate too).
- L886 `badProb-bounded` qualifications. The telescope half is STALE: it moved to
  `Partial :: badProb⊥-super`.
- L896 `G/Lax`.
- L985 raw G-composite spelling (`Bd` still zero uses).
- L1028 (superseded in substance by item 12).
- L1108 `Pin` depth constants.
- L1119 no pins for `Machines.*`.

**Resolved:**
- L430/L470: `kernel` now lives in `Observe`; `protoK` is gone.
- L1020: `morphismCompose` is in `Compose`.
- L1074: `agree-false` exists.
- L399 and L411 (Dictionary material now in `Machines.Pure`/`Sandwich`).
- L508 (`Traced.Ext.Laws`).

## Test suites (rule 33)

`GamePlaying/Test`, `Protocol/Machine/Pin` and `SFunM/Test/Possibility` all pin public entry points
only.
- `Pin` freezes internal junction depths (L1108).
- `Pin` redundancy: `agree-∘ = trans machine-∘ (sym layer₁-∘)`, and `agree`/`agree₊₁`/`agree₊₂`
  sample one family. Suggest dropping `machine-∘` and one depth.
- `SFunM/Test/Possibility`'s "Setoids payoffs" section tests `Possibility/Setoids` and
  `Monad.Graded.{Trivial,Uncurried}`, which have no other importer. It is misplaced (rule 27).
- No suite exercises `Machines.*`, `Trace.*`, `Average`, `Hop`, `Partial` or `Defer.Run` directly
  (a coverage gap, not a violation).

## Out-of-scope edits

None.

## Integration-owned files

- `SFunM.agda`: half of item 1. It rebinds telescopes despite its `private variable` block
  (rule 16), `where open R-Setoid ≈ᴹ-setoid` appears 6×, and it carries the same assoc overclaim.
- `Examples/RandomOracle.agda :: Functionality`: 0 uses.
- `CategoricalCrypto.agda`: re-exports `SFunM` and `SFunPartial` publicly. Items 3 and 7 need
  edits there.
