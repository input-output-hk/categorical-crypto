# Quality review — machine-iso (2026-09-17)

Scope: the branch diff `4ad62bdc..HEAD`, 29 `.agda` files totalling about 9260
lines plus `README.md`: `Channel/{Core,Category}`,
`Machine/{Core,Iso,Category,Forwarder,Message,Monoidal,MonoidalCategory,NAry,UC}`,
`Machine/Monoidal/{Coherence,Associator,Unitors,Braiding,Naturality,Interchange,Kleisli}`,
`Machine/Reindex{,/Collapse,/FwdId,/PairAssoc,/Post,/Slide,/Swap,/Unit}`,
`Machine/UC/Kleisli`, `Examples/Channels`, `CategoricalCrypto.agda`, `README.md`.
`Channel/Selection.agda` was pulled in for one item, the debug pragma it shared
with `Machine/Core.agda`.  `src/Categories/**` is out of scope.

Verification: **`pagda` is not on this machine and the contract's
`.claude/sweeps` toolkit does not exist in this repository**, so both were
replaced rather than skipped.  The oracle is `.claude/sweeps/check.sh`,
written and committed here, which requires `agda <file>` to exit 0 **and**
print no line containing `warning`, under each file's own `OPTIONS`; the
closure gate is `agda src/CategoricalCrypto.agda`.  Every commit below was
checked green that way before it landed, and all but two against the whole
closure (the two exceptions are noted where they occur).  In place of the
tree-sitter toolkit I hand-rolled four scripts, all committed:
`sweep.py` enumerates seven style classes and applies any subset,
`enum_comments.py` enumerates every comment block with the contract's noise
flags, `drive.sh` drives a class to a green fixpoint file by file by greedily
bisecting a red batch, and `open_channel.py` performs the one large
qualification rewrite.  No tree-sitter toolkit was built, deliberately.  The
tally below stands in for the contract's toolkit JSONs; it is the oracle's
verdict per site, not an estimate.

Soundness baseline, over the in-scope files.  Before: `postulate` 1, `{!` 2,
and zero for each of `TERMINATING`, `primTrustMe`, `allow-unsolved-metas`,
`type-in-type`, `NO_POSITIVITY_CHECK`, `no-termination-check`, `trustMe`,
`REWRITE`.  Both non-zero counts were textual: the `postulate` hit was the
word "postulated" inside a comment in `Machine/Iso.agda`, and the two `{!`
hits were the commented-out `cup`/`cap` sketch in `Machine/Core.agda`.
After: **every category is zero.**  The two that were non-zero shrank, the
comment having been reworded and the dead sketch removed; nothing grew.  All
29 in-scope files are still `--safe`, and
`--no-require-unique-meta-solutions` is on exactly the four that carried it:
`Channel/{Core,Selection,Category}.agda` and `Machine/Core.agda`.  The final
closure check at HEAD is green.

Sweep tally, per class, over the in-scope files (candidates / kept / skipped):

| class | candidates | kept | skipped, and why |
|---|---|---|---|
| `enum-comments` | 275 blocks | 275 dispositioned | 0 |
| `qual-noise` (`Channel.inType`/`outType`) | 620 | 615 | 5, all in `Machine/Core.agda`, on a real clash |
| `using-drop` | 52 | 52 | 0 |
| `pat-implicit` | 157 | 29 | 128, each rejected by the oracle site by site |
| `enum-where` | 2 | 0 | 2, both dispositioned below |
| `join-lines` | 374 | 0 | not run, a Suggestions work item below |
| `implicit-app` | 440 | 0 | not run, a Suggestions work item below |
| `enum-with` | 196 | 0 | not run, a Suggestions work item below |

`pat-implicit`'s 18% keep rate is the interesting number, and it is per-site
oracle output rather than an opinion: `.claude/sweeps/drive.sh` applied each
file's candidates as a batch, and on red added them back one at a time,
keeping the running green set.  Per file, kept of candidates:
`Examples/Channels` 4/4, `Machine/Reindex` 8/12, `Reindex/Post` 8/27,
`UC/Kleisli` 3/5, `Channel/Core` 2/34, `Forwarder` 2/7, `NAry` 1/4,
`Reindex/Collapse` 1/12, and 0 for each of `Monoidal/Associator` (0/18),
`Monoidal/Unitors` (0/10), `Monoidal/Braiding` (0/8), `Machine/Iso` (0/9),
`Machine/Core` (0/2), `Reindex/Slide` (0/2), `Machine/UC` (0/2),
`Monoidal/Naturality` (0/1).  Two things account for almost all the
rejections: the script cannot tell a constructor pattern (`{In}`, `{Out}`)
from a variable binder, and the three `Monoidal` naturality files pin their
channel implicits on purpose.  So the class is mostly false positives here,
and that is worth knowing before anyone runs `implicit-app`, which is the
same shape.

Measured per-site cost, which is what justifies the unfinished classes: a
single-module recheck against a warm `_build` is 30 to 40 s, the closure check
is 3.5 to 6 minutes once a widely-imported module is touched, and there is a 13
to 18 s interface-deserialization floor before any work happens at all.

Rebase note: this branch was rebased onto `machine-iso` at `d4c7a73d`, which
carries the maintainer's own standard-library swap for `Machine/Message.agda`.
That module is therefore untouched here by agreement.

## Committed (you can skim these)

- `42070779` Drop the leftover `-v allTactics:100` debug pragmas — a reflection
  verbosity flag in `Machine/Core.agda` and `Channel/Selection.agda`, depended
  on by nothing.  Measured: −1.13 GB allocation on those two modules and 37×
  less trace output, but they are 3.7 s of a 353 s build, so this is output
  hygiene and not a speedup.
- `d9be311b` Resync the README with the code it describes — 14 factual
  corrections in sections 1 to 4, every cited module and identifier re-checked
  against the tree.  Prose only.
- `c3a16c6a` Trim the comments in the `Machine.Monoidal` family — 31
  dispositions, five paragraphs consolidated to one copy each, two comments
  corrected.  The diff touches no code line; I verified that mechanically.
- `e12ae33c` Trim the comments in the UC layer, and stop calling `_≅ᴹ_` a
  bisimulation — comment-only again, plus the prose corrections the statement
  audit turned up.  See the first Statement-audit entry for why the naming
  mattered enough to change everywhere at once.
- `e5a83387` Build `machine-monoidal` through `monoidalHelper` — the library
  helper asks for the three forward naturality squares and derives the `-to`
  halves with the same `conjugate-from` calls this module made by hand.  I read
  `Monoidal′` in the dependency source myself: the field types are identical,
  so the assembled record is unchanged.  Costs 4 s on that module, no change in
  peak RSS.
- `f8e8a9bb` Derive `Xfwd-dom`/`Xfwd-cod` in `Reindex.Post`, and drop
  `Reindex.FwdId` — the two exports keep their signatures verbatim, so the
  eight call sites are untouched and only an import line changes in each of
  `Monoidal.{Associator,Braiding,Unitors}`.  Net 37 lines and one module fewer.
- `fe370f4e` Pin that `_≅ᴹ_` is strictly finer than bisimilarity — a `private`
  machine-checked witness, `padded-not-iso`, replacing a prose caveat.
- `27e68cc4` Share one `CompRel` inversion view instead of four copies — three
  byte-identical private `comp-view`s and one named-motive variant become one
  definition in `Machine.Core`, beside the `CompRel` it inverts.  Read the note
  in that message: it adds two names to `Machine.Core`'s exported surface.
- `af461575` Take `Forwarder`'s two congruences from `Machine.Reindex` — 14
  lines of proof become two, via provenance identities `Machine.Reindex`
  already proves by `refl`.  The new import edge is acyclic.
- `e1ea21bf` Open `Channel` locally instead of qualifying `inType` and
  `outType` — 615 of 620 qualifications go, under one `open Channel` per file.
  `Machine/Core.agda` is excluded on a real obstruction, not an oversight: it
  opens `Channel` at an argument in three places, which would leave `inType`
  overloaded.  Scripted, and the script is committed.
- `78c31164` Take the sum and product shuffles from the standard library —
  28 hand-written functions become `Data.Sum.Base`/`Data.Product.Base`
  combinators, bodies only, signatures verbatim, plus six round trips from
  `Data.Sum.Properties`.  Read the message for the finding: no hand-written
  body was load-bearing for definitional reduction, but four use sites needed
  their implicits pinned, because a point-free body no longer mentions the
  channel metas once the conversion checker eta-expands it.
- `c409f8bb` Move `Reindex-id` and the two `Pair-Reindex` specialisations to
  their home — out of `Monoidal.Associator`'s `opaque` block into
  `Machine.Reindex`, beside the `Pair-Reindex` they specialise, which lets
  `Reindex.Collapse` stop writing the same move out by hand twice.
  `Reindex-id` had to move with them or the lift would have been a cycle.
- `27e903aa` Trim the comments in `Machine.Iso` and `Machine.Reindex` — 195
  lines, comment-only.  The bulk is one family: 24 per-clause glosses across
  the six mutual workers of the associativity proof, all restating the
  invariant that the banner above `comp-view` states once.  `Reindex.agda`'s
  header was stale at the top, claiming the module proves `_⊗₁_` is a functor
  for `_∘_`, which is `⊗₁-interchange` in `Monoidal.Interchange`.
- `ecdad383` Trim the comments in `Reindex.Post`, `Forwarder` and
  `Machine.Core` — 204 lines, comment-only.  Six factual corrections, listed
  in the message; the `cup`/`cap` sketch goes, and with it the machine
  layer's last two `{!!}` holes.
- `d7bba386` Trim the comments in the naturality siblings and the `Reindex`
  family — 244 lines, comment-only.  Two families of near-duplicate headers
  reduced to one canonical copy each, and both pointers in the first family
  named the wrong sibling.  `Channel/Core.agda` loses seven type-echo banners
  and gains the reason its `opaque` block exists, which is why every
  downstream proof carries a long `unfolding` list.
- `6aba007c` Remove two dead definitions — `Reindex.Post`'s `relay-core` and
  `Machine.Iso`'s `sizeF`/`sizeG`/`sizeH`, a development-time
  termination-shape check.  Both grep-confirmed at zero references.
- `a58ee712` Add `mapᴹ-invol`, and use it at the five sites that inlined it —
  two of the five were named lemmas whose stated type already was the
  lemma's conclusion, so they become point-free.
- `fb552d50` Drop 52 non-clashing `using` lists in favour of bare opens — the
  whole `using-drop` class, applied as one batch and green.  Measured
  allocation-neutral on the slowest affected module; read the message, my
  first A/B on it was a stale measurement that did not reproduce.

## Suggestions (need your call)

### Statement audit

- `src/CategoricalCrypto/Machine/UC.agda` :: `_≈ℰ_` — the relation compares
  test outcomes at `_≅ᴹ_`, so a test "agreeing" means the two traced composites
  are isomorphic labelled transition systems, hidden state included.  The
  `Bool` the environment emits on `ℰ-Out` is never inspected, and nothing would
  change if `ℰ-Out` were any other channel.  This is sound, so every positive
  result on the branch is honest and in fact stronger than advertised, but it
  means `_≈ᵁ_` is not UC indistinguishability and `_≤UC_` is not UC emulation:
  two machines differing only by unused state are not related, which is the
  case UC exists to handle.  `padded-not-iso`, now committed, is the witness.
  The commits above fix the *prose* everywhere; what needs your judgment is
  whether to fix the *definition*.  `SameTest` is the single place to change:
  make it a verdict-trace equivalence on `Machine _ ℰ-Out`, keep `≅ᴹ ⇒` that
  relation as the soundness lemma, and the abstract layer needs only an
  equivalence plus the two congruences, both of which survive.  Note also that
  the machine layer contains no faithfulness result and no theorem that `≈ℰ` is
  strictly coarser than `≅ᴹ`, so the presheaf machinery is not yet shown to buy
  any coarseness at all.
- `src/CategoricalCrypto/Machine/UC/Kleisli.agda` :: `∘ᴷ-assoc′` — the
  left-hand side is not `F ∘ᴷ (G ∘ᴷ h)`; the grade re-bracketing has been
  folded into `absorb-regroup`, which silently replaces the `∘ᴷ-fwd` that
  `_∘ᴷ_` would use.  So the statement reads as plain associativity while
  asserting associativity modulo a chosen reshuffle, and a reader cannot see
  which regrouping is claimed.  Proposal: state it as
  `(F ∘ᴷ (G ∘ᴷ h)) ≅ᴹ (sub c ∘ ((F ∘ᴷ G) ∘ᴷ h))` with `c` the explicit grade
  associator, or add
  `absorb-regroup ∘ (F ⊗₁ id) ≅ᴹ sub ⊗-assoc ∘ ∘ᴷ-fwd ∘ (F ⊗₁ id)` and derive
  the primed form.  The same shape recurs at `Monoidal/Kleisli.agda`'s
  `∘ᴷ-assoc`.
- `src/CategoricalCrypto/Channel/Selection.agda` :: `⇒-solver-tactic'` — the
  ambiguity guard in the right-hand `_⊗₀_` case is dead code: the body raises
  `error1 "Unique solution required, multiple found."` inside a `catch` whose
  own handler returns the left result, so an ambiguous target silently resolves
  leftmost-first.  Since every structural machine in `Machine.Core` is *defined*
  by a solver term, the meaning of composition rests on that undocumented
  convention rather than on the stated type.  Nothing is wrong today: I checked
  each named reshuffle, and where an atom repeats (`∘σ`'s two `B`s) the
  transposition separates the occurrences at every mode, with injectivity
  proved where needed (`∘σ-inj`) rather than assumed.  Proposal: restructure so
  the ambiguity really errors, and add a port-by-port `refl` test for
  `app ∘σ` and `app ⊗σ` so the wiring is pinned by a checked statement.
  Out of the branch's scope, which is why it is a suggestion rather than a fix.
- `src/CategoricalCrypto/Abstract2.agda` :: `_≤UC_` — the quantifier structure
  is right and worth recording: the simulator is chosen after the adversary but
  before `≈ᵁ`'s environment quantifier, so it is uniform in the environment, as
  UC requires, and `UC-compose`'s composed simulator is built from simulators
  obtained against the dummy.  What the name hides is that this is *perfect*,
  information-theoretic UC with unbounded simulators and no corruption model.
  Worth one qualifying clause in the docs; no code change.
- `src/CategoricalCrypto/Machine/Core.agda` :: `_∣ˡ`, `liftᴷ` — `modifyStepRel`
  translates the *new* machine's output into the old one, so ports outside the
  image are deleted rather than hidden: `M ∣ˡ` keeps only the steps of `M` that
  never touch `B`, and `liftᴷ M` leaves the codomain `E` permanently dead.
  Nothing in scope is unsound, `tr`/`TraceRel` being where traffic is genuinely
  hidden and `idᴷ` only ever using `E = I`, but "restrict" versus "hide" is a
  difference a reader will get wrong.  Relatedly, an internal loop in `tr`
  yields no composite step, so divergence is identified with deadlock; that
  deserves a sentence somewhere.
- `src/CategoricalCrypto/Examples/Channels.agda` :: `secure≤UC-leaky` — the
  direction with content, `¬ (L.Functionality ≤UC S.Functionality)`, is absent;
  `Examples/Basic.agda`'s commented-out `F≤Secure` hole is where the flagship
  claim was meant to live.  The committed header now says the converse is not
  proved, but the gap itself is yours to fill or to declare out of scope.
- `src/CategoricalCrypto/Machine/UC.agda` :: the three `private` sanity checks —
  they pin types, but would typecheck for a vacuous `≤UC`.  Annotating the
  simulator as `∃[ s ∈ Machine Y X ]` would pin its direction, and adding
  `UC-compose` would earn the claim the header used to make about all four
  metatheorems.
- `src/CategoricalCrypto/Machine/UC/Kleisli.agda` :: `sub-⊗ˡ`, `return-ρ⇐` —
  genuine definitional identities stated at `_≅ᴹ_` with `≅ᴹ-refl` rather than at
  `_≡_` with `refl`, which puts "definitional" in the proof term instead of the
  type; the module's own dictionary already writes `=` for them.  Separately,
  `μ-assoc` reuses the name of the graded-monad law for what is an unfolding;
  `μ-is-α` would be honest.

### Public API / module layout

- `src/CategoricalCrypto/Machine/NAry.agda` :: `open Derived public using
  (unit-∘ᴷ; insert-id; ⨂-reshape-env; ⨂-absorb-env)` — all four re-exported
  names are dead outside the file.  `unit-∘ᴷ`'s only reference is intra-module,
  inside `Derived.⨂-unit`, so it resolves without the re-export; `insert-id`,
  `⨂-reshape-env` and `⨂-absorb-env` have no reference anywhere in `src/`.
  `NAry` is re-exported `public` by the root umbrella, so under rule 32 this is
  a narrowing suggestion rather than a commit.  The comment above the line says
  these are "the laws the transfer theorems use", and no transfer theorem in
  this tree uses them; either the theorems are still to come, in which case the
  comment should say so, or the list should go.
- `src/CategoricalCrypto/Machine/Message.agda` :: where the shrunken module
  should live — the repo already has an `X.Ext` convention
  (`src/Data/Maybe/Ext.agda`, `src/Data/List/Properties/Ext.agda`,
  `src/Categories/Morphism/Reasoning/Ext.agda`, `src/Class/Monad/Ext.agda`), and
  what survives in `Message.agda` after your standard-library swap is not
  machine-specific: `inj₁≢inj₂` and the two `Maybe` disjointness lemmas belong
  in `Data.Sum.Properties.Ext` and `Data.Maybe.Properties.Ext`, with
  `Machine.Message` as the machine layer's façade.  Your call, since it moves
  files.
- `src/CategoricalCrypto/Machine/Core.agda` :: `CompView`, `comp-view` — landed
  public by necessity in `27e68cc4`, where the four copies were `private`.  If
  `Machine.Core`'s surface matters, the alternative is a small internal module.
- `src/CategoricalCrypto/Machine/UC/Kleisli.agda` :: the module's place in the
  tree — nothing in it depends on `Machine.UC`, and it is imported only by the
  root umbrella, with a bare `import` that brings nothing into scope.  A `UC.*`
  module that the monoidal core could sensibly depend on is oddly named;
  `Monoidal/KleisliAbstract.agda` would describe it better.  Relevant to the
  `∘ᴷ-assoc` dedup below, which would add exactly that dependency.
- `src/CategoricalCrypto/Machine/Reindex/FwdId.agda` :: `Xfwd-dom`, `Xfwd-cod`
  (now in `Reindex.Post`) — the three functions plus two round-trip laws are
  `Function.Bundles._↔_` spelled out.  Taking an `Inverse` would say what is
  meant, but every call site changes, so it is a design decision.

### Simplifications / perf not committed (judgment needed)

- `src/CategoricalCrypto/Machine/Monoidal/Naturality.agda` :: `⊗ᴷ-fwd-natural`
  and `src/CategoricalCrypto/Machine/UC/Kleisli.agda` :: `⊗ᴷ-∙` — **the single
  largest measured lever on the branch.**  About 38% of a cold build is the
  coherence solver: four `solveMorσ!` call sites cost 97.6 s of a 353.7 s
  build, and the inherited `Categories.Coherence.Monoidal.*` frontend adds
  about 34 s.  Cost is superlinear in generator count, measured: 3 generators
  13.3 s, 4 generators 37.2 s and 47.1 s.  These two definitions are one
  4-generator call each, 47.1 s and 37.2 s, so decomposing them into
  3-generator steps plausibly halves 24% of the build.  It needs real proof
  engineering, finding the intermediate composite and giving it a typed named
  step, so it is staged work rather than a commit.  First stage: crux-spike
  `⊗ᴷ-fwd-natural` alone, because `Monoidal/Coherence.agda` already decomposes
  every participant into α and σ, and if the intermediate is expressible there
  the same shape applies to `⊗ᴷ-∙`.
- build configuration :: the RTS allocation area — **possibly the largest win
  available, and it is one build flag.**  A cold build spends 130 s of 351 s in
  GC across 155,513 gen0 collections, allocating 650 GB against a 3.5 GB
  residency, which is the classic signature of a nursery far too small for the
  allocation rate.  `+RTS -A64M` or `-A256M` carries zero source risk.  Not
  measured: two attempts were lost to contention from this review's own spikes,
  and the honest reading is that GC deltas were inseparable from noise.  Needs
  two cold builds on a quiet box, comparing GC seconds and gen0 counts with
  `bytes allocated` confirming identical work.
- `src/CategoricalCrypto/Machine/Iso.agda` :: the module as a whole, and
  `src/CategoricalCrypto/Machine/UC/Kleisli.agda` likewise — splitting the two
  big modules.  The warm developer loop carries a 13 to 18 s interface-
  deserialization floor before any work happens, almost independent of target,
  and on top of it a real recheck of `Iso`'s body is about 67 s and
  `UC.Kleisli`'s about 105 s.  Splitting cannot reduce the cold build, since
  Agda checks sequentially, but it shrinks what a one-line edit forces Agda to
  redo.  Frame it as a developer-loop improvement only.  `Iso.agda` is
  otherwise certified intrinsic rather than pathological: cost is flat across
  the sixteen mutual workers of the four direction proofs, none above 6.2 s or
  11% of the module, though it does own the library's memory peak at 7.67 GiB
  of 7.95 GiB and 121 GB allocated.
- `src/CategoricalCrypto/Machine/Monoidal/Kleisli.agda` :: `∘ᴷ-assoc` and
  `src/CategoricalCrypto/Machine/NAry.agda` :: `Derived.unit-∘ᴷ` — these are
  **the same propositions** as `UC/Kleisli.agda`'s `∘ᴷ-assoc′` and `unit-∘ᴷ′`,
  character for character after renaming, with disjoint proofs: a hand `Xfwd`
  computation against graded-triple algebra.  The primed pair has zero use
  sites.  A dedup would make `UC.Kleisli` canonical, delete `head₁` and the two
  `∘ᴷ-assoc-L`/`-R` halves (about 70 lines) plus `Derived.unit-∘ᴷ`, and add one
  import edge `Monoidal → Machine.UC.Kleisli`, which is acyclic.  I did not
  commit it for two reasons.  First, `UC/Kleisli.agda`'s header says the
  duplication is deliberate, a demonstration that the abstract layer transfers,
  so removing it destroys the thing the module exists to show; that is your
  call, not mine.  Second, the crux is cost rather than types: instantiating
  the graded-triple-derived law at `NAry.agda`'s `∘ᴷ-assoc (⨂ᴷ f) (⨂ᴷ g) h`
  puts a stuck `⨂` on both sides of an inversion through the opaque `_⊗₀_`,
  next to the `curriedTensor` conversion that `UC/Kleisli.agda` itself records
  as a quarter of an hour if done at the concrete category.  If you want it,
  the spike is: rename in `UC/Kleisli`, add the edge as
  `open import … public using (∘ᴷ-assoc; unit-∘ᴷ)` and **not** as an alias
  definition (an alias re-elaborates the type, which is what has to invert the
  opaque `_⊗₀_`), then profile `NAry.agda` alone from cold.  Minimum outcome if
  you keep the duplication: a cross-reference comment in both places, so a
  future reader does not "fix" it.
- `src/CategoricalCrypto/Machine/Monoidal/Kleisli.agda` :: `head₁`, `head₂` —
  34 and 55 lines of hand collapse between composites of structural forwarders
  only, with no generators, which `solveMorσ!` should reach given that
  `Monoidal/Coherence.agda` already decomposes every participant into α and σ.
  But `head₁` is hexagon-flavoured and the solver provably declines laws
  relating two different crossing decompositions, so expect `nothing` and fall
  back to `rewriteMorσ!` with the hexagon as a rule.  Not spiked: it is one of
  the two 48-GB-shaped levers and the box could not take it during this review.
  If it closes it is a commit.
- `src/CategoricalCrypto/Machine/Monoidal/Unitors.agda` :: the ρ half — about
  180 lines mirroring the λ half line for line.  At the machine level
  `ρ⇒ ≅ᴹ λ⇒ CC.∘ ⊗-symₘ` is a single `Xfwd-bridge` in `Coherence`'s idiom,
  after which `ρ⇒-natural` is roughly eight lines from `λ⇒-natural` and
  `σ-natural`.  The library's `braiding-coherence` is unusable here, since it
  needs `Braided`, which needs the very field being proved, so this is a
  project-level collapse.  Not spiked.
- `src/CategoricalCrypto/Machine/Message.agda` :: `mapᴹ-invol` — the chain
  `trans (mapᴹ-∘ …) (trans (mapᴹ-cong h o) (mapᴹ-id o))` occurs five times, at
  `Reindex.agda:312`, `:559`, `:691`, `Reindex/Swap.agda:88` and
  `Reindex/PairAssoc.agda:129`.  One lemma
  `mapᴹ-invol : (∀ x → f (g x) ≡ x) → ∀ o → mapᴹ f (mapᴹ g o) ≡ o` collapses
  each to a single call, and two of the five sites (`MO-recover`, `o-recover`)
  are named lemmas whose statement already *is* `mapᴹ-invol`'s conclusion, so
  they would disappear rather than shrink.  Left to you only because
  `Message.agda` is yours by agreement this round; it is otherwise a commit.
- `src/CategoricalCrypto/Channel/Core.agda` :: `⊗-combine` — the last member
  of the `Data.Sum.Base` family, declined deliberately rather than for lack of
  time.  Its four identical lambda literals are `⊎.map (p .app) (q .app)`, and
  the correspondence was verified by hand, but this is the definition the
  34 GB `Machine.Iso` incident turned on: the memory came down from 14.6 GB
  live to 4.4 GB by changing the *shape of the argument to* `mk⇒` here.  The
  extension lambda is a generated, copattern-stuck definition; `⊎.map` is a
  `[_,_]′` application that reduces.  Swapping it changes what
  with-abstraction normalises inside every `opaque unfolding _⊗₀_ … ⊗-combine`
  block, which is most of the machine layer.  Verifying it honestly means
  measuring `Iso.agda`'s peak heap, which could not be done during this review
  without risking the maintainer's live editor sessions.  Memory-risky, not
  hard; it wants one serialized run.
- `src/CategoricalCrypto/Machine/Monoidal/Associator.agda` :: `αfₒ⁻` and
  `src/CategoricalCrypto/Machine/Reindex.agda` :: `Pair-resp-≅ᴹ` — two
  stragglers of the same family, both easy.  `αfₒ⁻` is `⊎.assocˡ` (it runs the
  other way from `αfᵢ⁻`, at `outType`); `Pair-resp-≅ᴹ` inlines the pair map by
  hand as `λ (s₁ , s₂) → to φ s₁ , to ψ s₂` and could take
  `Data.Product.Base.map`, as `Machine.Iso` now does.  Neither was attempted,
  so neither is verified.

- `.claude/sweeps/sweep.py` :: the classes `join-lines`, `implicit-app` and
  `enum-with` — dimension 4 left unfinished in three of its seven classes.
  Each is enumerated
  and scripted, and what remains is machine time, at a measured 30 to 40 s per
  module check (65 s for `Machine/Iso.agda`, 105 s for `Machine/UC/Kleisli`).
  `.claude/sweeps/drive.sh <class> <files>` drives a class to a green fixpoint
  file by file, so these are a matter of leaving it running, not of further
  design.
  - `join-lines`: 374 candidates, none applied.  Worth doing by hand rather
    than by driver: the script is blind to deliberate column alignment, so its
    diff needs reading.
  - `implicit-app`: 440 candidates, restricted to sites right of an `=` so a
    signature binder can never be one.  Expect a low keep rate, and that is
    the point of running it: this repository *requires* many of these pins and
    records why, so the survivors are exactly the ones that are noise.  The
    `pat-implicit` run below is the calibration — 26% kept.
  - `enum-with`: 196 sites, of which 132 are flagged single-scrutinee, and
    **none is dispositioned here**.  I am not offering a reason per site,
    because I did not test them; the count and the cost are the honest
    statement.  144 of the 196 are in `Machine/Iso.agda`'s six mutual
    dispatchers, and a per-site spike there costs about 65 s, so that file
    alone is 2.6 hours of machine time.  One fact that helps whoever runs it:
    `case_of_` is already an idiom in this repository (`MachineAxioms`,
    `Categories.FreeMonoidal`, `Categories.Coherence.Monoidal.Compare`), so a
    swap introduces nothing new; but many of these sites chain a second
    `with` onto the first and use the resulting equations under `subst`, so
    the edit is a restructuring of proof text rather than a one-liner.

### Public API / downstream UI, from the interface map

- `src/CategoricalCrypto/Examples/Channels.agda` :: `secure≅sim∘leaky`,
  `secure≤UC-leaky` — rule 33.  **There is no test suite for the in-scope
  code**,
  by design: Agda's typechecker is the verifier and `Examples/` are the
  executable specifications.  Audited in that spirit, `Examples/Channels.agda`
  targets the public entry points correctly: it pins
  `secure≅sim∘leaky : SecureChannel ≅ᴹ ((A ⊗₀ B) ⊗ˡ Sim) ∘ LeakyChannel` and
  `secure≤UC-leaky : S.Functionality UC.≤UC L.Functionality`, both of which are
  the layer's headline statements, reached through `Machine.UC`'s `≈C⇒≈ᵁ` and
  `dummy-complete` rather than through any internal helper.  Nothing in it
  freezes an internal as de-facto interface.  What it lacks is the converse,
  which is the entry above.  The solver suites under
  `src/Categories/Coherence/Monoidal/Test/` are inherited from `main` and out
  of scope.
- `src/CategoricalCrypto/Machine/Monoidal.agda` :: its 13 re-exported names,
  and the eight other `open … public` sites — the interface map, each grepped
  per name.  `Machine.Monoidal` re-exports 13 names through `using` lists, and
  every one of the 13 has at least one use outside the `Machine/Monoidal/`
  subtree, so there is nothing to narrow there.  `CategoricalCrypto.agda`'s 12
  are whole-module re-exports and constitute the layer's front door by
  construction.  `Machine.Core`'s `open Tensor using (_⊗₁_) public`
  is load-bearing everywhere.  `Channel/Core.agda`'s `open _[_]⇒[_]_ public`
  supplies `app`, used throughout.  `Machine.Reindex`'s
  `open import … Machine.Message public` is load-bearing for exactly two
  modules, `Reindex.Unit` and `Reindex.Collapse`, which reach `mapᴹ` only
  through it; the comment claiming every module reaches it that way was false
  and is fixed.  `Machine.UC`'s `open StdUC … public hiding (_⊗₀_; _⊗₁_)` and
  `Machine.UC.Kleisli`'s `open GradedKleisliTriple ℳ public` are the modules'
  whole purpose.  The one narrowing finding is `Machine.NAry`'s, above.

### Companion docs

- `README.md` :: section 4 — the factual errors are fixed and the
  proof-engineering modules are now named, but the proportion problem is
  substantive and yours: section 3 covers 556 lines of Agda in 26 README lines,
  section 4 covers 9979 in about 27.  What does not come through is that the
  layer is `--safe` with zero postulates and zero holes, that the identity laws
  are *derived* rather than assumed, and that the symmetric monoidal structure
  is complete.  The section also still frames the largest and most finished
  part of the development as a legacy loose end ("predating the layers above").
- `README.md` :: section 1, `Monad.Graded` — the heading promises
  `src/Categories/`, but the base record the whole abstract layer is parametric
  over is not in this repository; it is in the upstream `agda-categories` fork.
  Only `Monad.Graded.{Ext,Morphism,Pullback,Uncurried}` are local.  A reader
  following the citation cannot find the definition.  Also unmentioned:
  `Abstract2.Morphism`, `Abstract2.WideSubcategory`, `UCSetup.Morphism`,
  `Standard2.Morphism` (773 lines together, and `WideSubcategory` is the
  machinery behind the OP restriction section 2 spends two sentences on), and
  `Examples.RelSetup`, which is a second *instantiation* of section 2 rather
  than a machine example and is filed nowhere.
- `README.md` :: section headings — sections 1 and 2 carry a path, 3 and 4 do
  not, and section 2's path does not discriminate, since sections 2, 3 and 4 all
  live under `src/CategoricalCrypto/`.  Either drop all four or give all four a
  real one.

## Tried, not worth it

- `src/CategoricalCrypto/Machine/NAry.agda` :: `Derived` reasoning chains —
  spiked, and **reverted on a measured regression that has nothing to do with
  the combinators.**  Adding `open import Categories.Category using (Category)`
  to `NAry.agda`, with no body change at all, takes its typechecking allocation
  from 17.85 GB to 35.54 GB, +99%, and peak residency from 706 MB to 879 MB,
  +24%.  A five-step bisection attributed essentially all of it to that one
  import: `Machine.MonoidalCategory`, `Categories.Morphism.Reasoning`,
  `Categories.Category.Monoidal.Reasoning` and every `open` together add under
  250 MB on top.  Allocation was used rather than wall clock because the same
  file doing byte-identical work measured between 18.6 s and 41.2 s under
  contention, while allocation reproduced to the byte.  The mechanism is
  unexplained; the untested hypothesis is an interaction with the reflection
  machinery `NAry` pulls in through `Tactic.Defaults`.  Worth confirming on a
  quiet box before anyone tries this again, because if it holds, no
  library-combinator conversion of this module can be performance-neutral.
  Salvage: `post-α = pushʳ (⟺ eq)` was confirmed by reading and by
  typechecking, `⨂-post {zero}` and `slide-⊗ᴷ` are `elimˡ ⊗₁-id` (confirmed by
  reading), and `≅ᴹ-sym ∘-assoc-≅ᴹ` / `∘-resp-≅ᴹ e ≅ᴹ-refl` /
  `∘-resp-≅ᴹ ≅ᴹ-refl e` are term-identical to `sym-assoc` / `e ⟩∘⟨refl` /
  `refl⟩∘⟨ e`.  One claim I passed on was **refuted**: `slide-∘ᴷ`/`slide-⊗ᴷ`
  are *not* `merge₁ˡ ○ (eq ⟩⊗⟨refl)`, because `merge₁ˡ` needs the category's
  literal `id` as the second component and these have `CC.id ⊗₁ CC.id`, which
  is only propositionally equal to it; the right form is
  `⟺ ⊗-distrib-over-∘ ○ (elimˡ ⊗₁-id ⟩⊗⟨refl)`.  And note
  `⊗-distrib-over-∘`'s arguments are the project's `⊗₁-interchange`'s in the
  order `{f,g,h,i} ↦ {g,k,f,h}`.
- `Reindex/Post.agda`, `Machine/Iso.agda` :: narrowing the `opaque … unfolding`
  lists, as a *speed* fix — measured dead.  `Post.agda` typechecks with
  `unfolding _⊗₀_` alone in place of six names and `Iso.agda` with three of
  eight across all six blocks, both green, and allocation moves by 0.0012% with
  `.agdai` shrinking a few hundred bytes.  `unfolding` grants permission to
  unfold; it does not force work.  Still worth doing as hygiene and for honest
  signatures, so it stays available as a mechanical commit, but nobody should
  expect a speedup from it.
- `Reindex/Post.agda` :: as a perf target at all — 4.2 s over 1073 lines, 3.9
  ms/line, among the most efficient files in the library.  The two mirror-image
  relay proofs are cheap.  Any perf motivation for touching it is unfounded.
- `Monoidal/Kleisli.agda` :: re-inlining the named `≅ᴹ-trans` chains — the
  48 GB regression is recorded and the fixed form is still in place.  Not
  retested, deliberately.
- `Channel/Core.agda` :: a record expression in place of the `mk⇒` constructor —
  already fixed, the 34 GB incident recorded; 26 `mk⇒` sites remain with one
  `record { app` left.
- `UC/Kleisli.agda` :: ascribing a type to `curriedTensor machines` at the
  concrete category — already correctly avoided, the module building over an
  abstract `M` and instantiating afterwards, now costing 3.5 s.
- `enum-where` :: `NAry.agda:244` and `:246`, both named `eq` — the tool counted
  zero in-scope uses at each, but that is the tool's indentation-based scope
  test failing: each `eq` is used in the body of its parent `⨂-absorb-env`
  clause, above the `where`.  Neither is single-use, so neither is an inlining
  candidate.  These are the only two sites in the class.
- `Machine/UC/Kleisli.agda` :: the `using`-versus-bare-open allocation A/B —
  a measurement of mine that **did not reproduce and was wrong**, recorded so
  nobody chases it.  The first reading said 18.4 GB allocated with bare opens
  against 160.4 GB with the `using` lists, an apparent 8.7× win.  Two further
  rounds of each variant gave 160.56 GB and 160.37 GB, so the two forms are
  allocation-neutral to 0.1% and the outlier was a stale first measurement
  (the module had just been built by a closure check, and the `touch` did not
  force the work I assumed).  The lesson is the one the perf audit already
  states: on this box, A/B by `bytes allocated in the heap`, never by wall
  clock, and never on a single round.
- `MEMORY.md` :: an entry for `git apply -3` being all-or-nothing across files
  (it rolls back files it has already reported as applied cleanly;
  `git apply --exclude=<path>` is the way out).  Real, but it is a git fact
  rather than a fact about this project, so not written.
