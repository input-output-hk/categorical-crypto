# Quality review — review/sfun-monoidal (2026-08-17)

Scope: the branch delta against `categorical-crypto-plan` @ `84009b44` —
`CategoricalCrypto/SFunM.agda`, `SFunM/{Monoidal,Morphism,Properties}.agda`,
`Class/Monad/Ext{,/Setoid}.agda`, `Data/Sum/Ext.agda`,
`Data/Bool/ListAction/Ext.agda`,
`ProbabilisticLogic/Distribution/Possibility.agda`, the `CategoricalCrypto`
index; plus the two files the review added to (`Data/List/Properties/Ext.agda`)
or created (`CategoricalCrypto/SFunM/Test/Possibility.agda`).

Tip: `38df23f3`. Verification: yes — every commit checked green (rc=0 **and** empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing` grep) under each
file's own OPTIONS before landing, and the tree closes over all 17 leaf modules
(the honest closure here: no module is named `*Tests`, so "leaf" = imported by
nothing, computed from the import graph). Soundness baseline: **0 escape hatches
before, 0 after**, every category.

Sweep tally — the committed `.claude/sweeps-tally/tally-*.json`, all seven classes
re-run over all twelve in-scope files at `af583ad6`, i.e. after the earlier rounds
had already consumed their survivors (which is why the counts are smaller than the
work landed):

| class | candidates | oracle-green | committed from this run | skipped |
|---|---|---|---|---|
| `using-drop` | 17 | 7 | 2 | 11 (`open … public`) |
| `implicit-drop` | 125 | 77 | 0 | 0 |
| `binder-drop` | 38 | 2 | 0 | 0 |
| `join-lines` | 10 | 4 | 3 | 0 |
| `enum-with` | 2 sites | — | 0 | — |
| `enum-where` | 15 sites | — | 0 | — |
| `enum-comments` | 32 blocks | — | — | — |

Every `enum-*` site was dispositioned individually; the declines and their
site-specific reasons are under *Tried*. Earlier rounds took 3 more `using-drop`
survivors (`4e58db18`, `9ed3591b`), 4 more `join-lines` (`d8782a40`, `862ea5c4`),
1 `implicit-drop` (`ec98714d`) and 2 `enum-where` inlines (`6d1a3c36`), so those
sites no longer appear as candidates.

Closure matrix (`+RTS -M6G -H1G`, warm):

| leaf | rc | warn | `Checking` | s |
|---|---|---|---|---|
| `CategoricalCrypto` | 0 | 0 | 0 | 6 |
| `CategoricalCrypto.Abstract2.Equivalence` | 0 | 0 | 37 | 69 |
| `CategoricalCrypto.Abstract2.OAPEmulation` | 0 | 0 | 1 | 7 |
| `CategoricalCrypto.Abstract2.WideSubcategory` | 0 | 0 | 5 | 17 |
| `CategoricalCrypto.Examples.RelSetup` | 0 | 0 | 3 | 10 |
| `CategoricalCrypto.RandomOracle` | 0 | 0 | 2 | 9 |
| `CategoricalCrypto.RandomOracle2` | 0 | 0 | 1 | 6 |
| `CategoricalCrypto.SFunM.Test.Possibility` | 0 | 0 | 2 | 6 |
| `CategoricalCrypto.Standard2.Morphism` | 0 | 0 | 2 | 7 |
| `CategoricalCrypto.StandardTV` | 0 | 0 | 6 | 12 |
| `Categories.Coherence.Monoidal.Test.Frontend` | 0 | 0 | 1 | 9 |
| `Categories.Coherence.Monoidal.Test.InterchangeStress` | 0 | 0 | 1 | 8 |
| `Categories.Coherence.Monoidal.Test.Limitations` | 0 | 0 | 1 | 6 |
| `Categories.Coherence.Monoidal.Test.SigmaFrontend` | 0 | 0 | 1 | 7 |
| `Categories.GradedKleisli.Functorial.Category` | 0 | 0 | 2 | 21 |
| `Categories.Monad.Graded.Uncurried` | 0 | 0 | 1 | 9 |
| `LibExt` | 0 | 0 | 1 | 5 |

The `Data/List/Properties/Ext.agda` addition is the one change reaching outside
the delta; that run re-elaborated all seven of its `Categories.*` importers
(`FreeStrictMonoidal`, `Coherence.Monoidal.{Compare,Diagram,MacLane,Normalize,Sigma,WireCoherence}`).

## Committed (you can skim these)

Round 1 (`57863fde..c92e89ef`):

- `4e58db18` Drop the non-clashing `using` lists — rule 11, sweep-verified.
- `d8782a40` Put signatures that fit on one line on one line — rule 14.
- `6b232c91` Cut the comments that restate their own signature — rule 21/22.
- `8833fbad` Take the implicit telescopes from the `variable` block — rule 16, types unchanged.
- `eae36961` Write `idᵉ` out and use the backward reasoning step.
- `efec255c` Take the `∨` and `map` congruences from the stdlib — rule 30.
- `bf1fe7dc` Give the `any` algebra its own module — rule 27.
- `14ed2e83` Order the sections by dependency — rule 28.
- `8c6f7a89` Derive the tensor's identity and right congruence.
- `ae44ddb3` Name the sliding principle the naturality squares share — `statelessᵉ-natural`, −22 lines.
- `c92e89ef` Move `statelessᵉ-inv` next to the rest of the `statelessᵉ` family — rule 28.

Round 2 (`c92e89ef..af583ad6`):

- `f9c51e2e` Trim the comments that restate the code, and fix the ones that misstate it — cuts three narration blocks in `Monoidal` (one of them, "naturality squares are kernel-level identities", was false), two signature paraphrases in `Properties`, `Setoid`'s restatement of its module name, and `Possibility`'s comparison with `Dist-ℚ`/`_≈Mℚ_`, which exist only on `ro-integration`.
- `9ed3591b` Drop the three remaining non-clashing `using` lists — rule 11.
- `ec98714d` Let `σ-conjᵉ` infer `braiding-commuteᵉ`'s factors — the one implicit-drop candidate that is not a pin.
- `ef8d57e7` Put the imports back at the top — rule 10; also drops `Setoid`'s bare `open import Level` (it re-imported `suc`/`zero`/`_⊔_` unrenamed over the Prelude's) and a redundant in-body import.
- `c4caee24` Name the setoid reasoning once instead of at every proof — rule 19, 16 local opens → 3 lines.
- `1f60d1f6` Open the record instead of qualifying its fields — rule 19.
- `6d1a3c36` Inline the two single-use `kern` bindings — rule 18.
- `6ecdf379` Bind the two clause-independent relabellings once — verbatim duplication across `kern` clauses.
- `e5f001c1` Move the last `any` lemma into the `any` algebra — `any-⊗`, rules 26/27.
- `4d4b4312` Derive `<$>ᴹ-∘` from `<$>ᴹ->>=` — the two had the same proof written twice.
- `978edaa6` Derive `statelessᵉ-inv` from the rest of the family — functoriality instead of a kernel computation; adds `module ≈ᵉ` mirroring `module ≈ᴹ`.
- `498ccd7a` Use `HomReasoning`'s composition combinators — `_⟩∘⟨refl`/`refl⟩∘⟨_`; `𝒮.Equiv.refl` now appears nowhere.
- `32e9c0bf` Instantiate the machine layer at a concrete monad — new `SFunM/Test/Possibility.agda`; see the note below.
- `862ea5c4` Put four more signatures and bodies on one line — rule 14, join-lines survivors.
- `84d7b66a` Record `fillˡ`'s length invariant; eta-reduce `any-cong` — rules 21/17.
- `26edbec0` Give `MonadMorphismSetoid` the `_<$>ᴹ_` law it kept re-deriving — `θ-<$>ᴹ`, three sites.
- `be218b26` Prove `concatMap` associative where the list lemmas live — rules 27/30; verified over the whole leaf closure.
- `af583ad6` Name the two kernels the `ᵉ` layer wraps — `idᵏ`/`statelessᵏ`, 9 qualification sites; warm `Monoidal` 10.6 s → 10.4 s on the same basis.
- `38df23f3` Sweep the review's own additions — the `using-drop`/`join-lines` survivors the final re-run found in the code this review wrote.

The test module is the one addition worth a second look: nothing in the tree
forced `SFunᵉ-Monoidal`, `SFunᵉ-Symmetric` or `SFunᵉ-map-monoidal` to elaborate
(every module is abstract over `M`, and `Possibility` had no importer at all), and
`MonadLawsSetoid` admits the trivial model `_≈ᴹ_ = λ _ _ → ⊤`, so a green abstract
build was not evidence of non-vacuity. It pins public entry points only (rule 33):
the four bundles at `M = List`, two `eval` values fixing `trace`'s and `_⊗ᵉ_`'s
observable behaviour, and `SFunᵉ-map`/`SFunᵉ-map-monoidal` along a
`MonadMorphismSetoid Maybe List` — also the first consumer of `FromPropositional`.
Warm cost 5.9 s, so the record-comparison blowup `SFunPartial` documents at
`Dist⊥` does not arise at `List`.

## Suggestions (need your call)

### Public API / module layout

- `src/CategoricalCrypto.agda :: CategoricalCrypto.SFunM.Monoidal` — the index says
  `open import CategoricalCrypto.SFunM public` but plain `open import` for
  `.Monoidal` and `.Morphism`, so `open import CategoricalCrypto` yields `SFunᵉ`,
  `_∘ᵉ_`, `_≈ᵉ_` but not `_⊗ᵉ_`, `statelessᵉ` or any of the bundles — the two
  lines only pull the modules into the docs closure (`pagda.nix`
  `entryModule`). Every other library line in the file is `public`; only
  `Examples.*` is not. Spiked: adding `public` to both is green with an empty warn
  grep (no `ᵉ`-suffixed name clashes with `Channel.*`/`Machine.*`), and
  `SFunM.Properties` comes along transitively. Pick one — three `public`, or drop
  `public` from `SFunM` too. Not committed: it changes what downstream imports.
- `src/CategoricalCrypto/SFunM.agda :: _∘ᵉ'_` — the only kernel-level name not using
  the file's `ᵏ` suffix (`_⊗ᵏ_`, `idᵏ`, `statelessᵏ`, `⊗idᵏ-trace`,
  `statelessᵉ-postᵏ`). Zero uses outside the `SFunM` tree on this branch and on
  `ro-integration`, so `_∘ᵏ_` is a mechanical rename — but `SFunM` is
  downstream-facing, hence yours.
- `src/CategoricalCrypto/SFunM/Monoidal.agda :: ⊗idᵏ-trace` — with `lefts` and
  `fillˡ`, the one genuinely reusable fact in the `private` block ("the trace of
  `f ⊗ᵏ idᵏ` factors through the trace of `f`, refilled along the input pattern").
  Rule 32 leans public; `⊗idᵉ-resp`, `id⊗ᵉ-resp` and `σ-conjᵉ` are correctly private.
- `src/Class/Monad/Ext/Setoid.agda :: <$>ᴹ-congˡ` — zero uses on this branch and on
  `ro-integration`; the two `≈ᴹ.reflexive (cong return …)` sites in
  `SFunM.Properties` are not instances of it. Keep (rule 32) or cut is your call.
- `src/Class/Monad/Ext.agda :: KleisliTriple-M` — with `Monad′-M`, `Kl-M` and
  `module Kl-M`, dead tree-wide (pre-existing, not from this branch). Deleting the
  group removes 27 lines and the five `Categories.*` imports the review just
  hoisted to the top.
- `src/Class/Monad/Ext.agda :: >>=-comm-y` — dead, and step-for-step the
  propositional twin of `>>=-comm-y-≈` in `Ext/Setoid.agda`; `FromPropositional`
  now makes the setoid one derivable at `_≡_`, so one of the two can go.
- `src/CategoricalCrypto/SFunM/Test/Possibility.agda :: fromMaybeᴹ` — if you want
  "any partial machine abstracts to a possibilistic one" as library API rather
  than test scaffolding, its home is `Class/Monad/Ext/Setoid.agda`.
- `src/Data/Bool/ListAction/Ext.agda` — the only `Data/*/Ext.agda` importing
  `categorical-crypto.Prelude`; its two siblings are stdlib-tier leaves with
  explicit `using` lists and `Set ℓ`. Retiering it would remove the
  `hiding (any; or)` dance, at the cost of ~6 import lines.

### Statement audit

- `src/CategoricalCrypto/SFunM.agda :: id-correct` — sits inside the
  `⦃ CommutativeMonadSetoid M ⦄` block but its proof uses only
  `>>=-identityˡ-≈` and `>>=-cong-x`. Moving it into a preceding
  `module _ ⦃ M-Laws ⦄` block is spiked green over the whole closure
  (`mapᵉ-id` in `Morphism` still checks) and strictly strengthens it. Not
  committed because dropping a hypothesis changes what the statement claims.
  Patch: `scratchpad/id-correct-move.patch` — 12 lines, pure block motion.
- `src/CategoricalCrypto/SFunM.agda :: _≈ᵉ_` — batch trace equality: two machines
  are equal iff they agree on every *pre-committed* input list. That is
  may-testing, not bisimulation, and for a nondeterministic `M` it is strictly
  coarser (no adaptive adversary, so no branching structure is observed). Sound
  for everything on the branch, and enough for the monoidal structure, but any
  future operation that copies a machine, shares state between factors, or closes
  a feedback loop is *not* automatically a congruence for it. Worth one header
  line saying so, since `_≈ᵉ_` is what downstream security statements will mean.
- `src/CategoricalCrypto/SFunM/Properties.agda :: ≈ᵉ-sim` — a sufficient condition
  only, not a characterisation, and it demands the square at *every* state of `f`
  including unreachable ones. Fine as used; the name reads like an iff.
- `src/CategoricalCrypto/SFunM/Properties.agda :: statelessᵉ-natural` — nothing
  relates `h` and `k`, so this is a sliding/transport principle (your own commit
  message calls it "the sliding principle"), not naturality of anything.
  `statelessᵉ-slide` would say what it is.
- `src/ProbabilisticLogic/Distribution/Possibility.agda :: _≈𝒫_` — the file proves
  the monad laws but nothing about the quotient itself: no `↭`-invariance and no
  duplication lemma, so "order and multiplicity are invisible" is asserted, not
  established. The converse also fails in general: without decidable equality on
  `A` there need be no separating `Bool`-valued family, so `≈𝒫` is in general
  *coarser* than support equality. Two three-line lemmas
  (`↭ ⇒ ≈𝒫`, `x ∷ x ∷ σ ≈𝒫 x ∷ σ`) would turn the claim into content.
- `src/Class/Monad/Ext/Setoid.agda :: MonadLawsSetoid` — no field mentions
  `Monad`'s own `_<$>_`/`pure`, only `return`/`>>=`, so an instance can satisfy
  every law while `_<$>_` disagrees with `_<$>ᴹ_`. Also the trivial model
  `_≈ᴹ_ = λ _ _ → ⊤` satisfies all three records for any `M`; the new test suite
  is now the in-tree evidence that the bundles are not being read at it.
- `src/CategoricalCrypto/SFunM/Morphism.agda :: SFunᵉ-map-monoidal` — every
  structure map is `idᵉ` and every law reduces to `identityˡ`; the mathematical
  content is `mapᵉ-⊗` alone. The bundle is correct, but "strong monoidal" here
  means "strict", which is worth a word.
- `src/CategoricalCrypto/SFunM/Morphism.agda` — instantiated at `M = N` the module
  has two `MonadSetoid M` instance candidates of the same type; harmless today
  (nothing does it, and the new test uses `Maybe ⇒ List`), a trap later.

### Simplifications / perf not committed (judgment needed)

- `src/ProbabilisticLogic/Distribution/Possibility.agda :: 𝒫` — `𝒫.refl` and
  `𝒫.reflexive refl` leave `UnsolvedConstraints` wherever the setoid's `x` is not
  already fixed by the goal (measured while writing `fromMaybeᴹ`: two of four
  fields failed, the pointwise `λ _ → refl` works). Because `_≈𝒫_` is a
  definition rather than a record, `Setoid.refl` has to unify one meta against
  both sides. Not a defect, but it will bite every instance author; a
  `≈𝒫-refl : σ ≈𝒫 σ` with the argument explicit would fix it.
- `src/CategoricalCrypto/SFunM/Monoidal.agda :: statelessᵉ-⊗` — sits under "The
  structural morphisms" although it is a `_⊗ᵉ_` fact used by the coherence
  proofs; rule 28 would put it under "Functoriality". Pure taste, hence not
  committed.

## Tried, not worth it

- `src/ProbabilisticLogic/Distribution/Possibility.agda :: >>=𝒫-identityˡ` —
  routing the three monad laws through
  `Data.List.Effectful.MonadProperties.{left-identity,right-identity,associative}`.
  Red: upstream fixes `{A B : Set ℓ}` at one level, `MonadLawsSetoid` needs
  `{A : Type ℓ} {B : Type ℓ′}` (`B.ℓ != A.ℓ of type Level`). The two identities
  already call the level-polymorphic primitives (`++-identityʳ`,
  `concatMap-pure`) directly; only associativity had no upstream statement, which
  is what `be218b26` adds.
- `src/Class/Monad/Ext/Setoid.agda :: ≈ᴹ-isEquivalence` — `binder-drop` finds
  `{A : Type ℓ}` droppable here and on `MonadMorphismSetoid.θ`, both green. Not
  taken: 11 of the 13 candidates in that file are red (the binder is load-bearing
  wherever `A` appears only under `{A = A}`), so the two drops would leave the two
  records' field lists half-generalized, and every other field of both records
  binds its telescope explicitly — that is the established convention *in these
  records*, distinct from the proof-level lemmas that do use the block.
- `src/CategoricalCrypto/SFunM/Monoidal.agda` — the `implicit-drop` class as a
  whole: 66 of 113 candidates are oracle-green, 64 of them declined. All are the
  `{M = M}`/`{M = N}` pins; in `Morphism` they are what distinguishes source from
  target (without them `mapᵉ` reads `SFunᵉ A B → SFunᵉ A B`), and in
  `Monoidal` they keep the category argument syntactically identical at every
  `Category`/`Morphism.Reasoning` application. `θ-return`'s `return {A = A}` and
  `MonadSetoid-List`'s hand-over of `σ`/`τ` are documented pins.
- `src/CategoricalCrypto/SFunM/Monoidal.agda :: triangleᵉ` — a named
  "stateless normalisation" principle (any `⊗`/`∘` composite of stateless
  machines is `≈ᵉ` iff the underlying functions are `≗`) to collapse
  `triangleᵉ`/`pentagonᵉ`/`hexagonᵉ`/`⊗ᵉ-identity`. The four sites differ in
  bracketing, so the principle needs the composite passed as data; net +1 line
  over the current `○`-chains. The `statelessᵉ-Functor` route is separately dead
  (a `Functor` record adds no proof power over the lemmas it bundles), and the
  *strong monoidal* statement one level up cannot be used inside the file that
  constructs the monoidal structure.
- `src/CategoricalCrypto/SFunM/Monoidal.agda :: ⊗ᵉ-homomorphism` — deriving it
  from `⊗-split` plus interchange bottoms out in `lefts (fillˡ xs bs) ≡ bs`,
  which is false without a length side condition; and expressing `lefts` via
  `Data.List.Base.partitionSums` loses the lockstep reduction `⊗idᵏ-trace`'s
  induction needs.
- `src/CategoricalCrypto/SFunM/Monoidal.agda :: Λ` — hoisting the duplicated
  relabelling *with* a type ascription: `GeneralizeNotSupportedHere`, because the
  generalized `C`/`C′` are not nameable in a `where` block. Un-annotated works
  and is what `6ecdf379` landed.
- `src/CategoricalCrypto/SFunM/Monoidal.agda :: Λf` — the six `where` bindings
  `enum-where` flags as single-use (`Λf`, `Λg`, `outer`, `cont` in
  `⊗ᵉ-homomorphism`, `K` in `⊗-split`) each have two uses at their own site: the
  argument of a reasoning step and the syntactic endpoint of the chain. The tool
  undercounts by one; the two genuinely single-use ones were inlined in
  `6d1a3c36`. The remaining `kern`s cannot be inlined at all — their clauses carry
  `where` blocks, which a `λ where` clause cannot.
- `src/Data/Sum/Ext.agda :: unitˡ⇒` — `Data.Sum.Algebra.⊎-identityˡ`/`-identityʳ`
  are `↔` bundles *and* live at `Data.Empty.Polymorphic.⊥`, so at `0ℓ` they give
  `Lift 0ℓ ⊥`, not the `⊥` the monoidal unit needs. `84d7b66a` records both
  reasons in the comment.
- `src/CategoricalCrypto/SFunM/Monoidal.agda :: unitorˡ-commuteᵉ` — deriving it
  from `unitorʳ-commuteᵉ` by σ-conjugation: +3 lines, since both are already
  one-liners over `statelessᵉ-natural`.
- `src/Data/Bool/ListAction/Ext.agda :: any-++` — replacing the family with
  `Data.List.Relation.Unary.Any` or a foldr-monoid-homomorphism route: crossing
  `Bool` and `T`/`Any` costs more than the three-line inductions it replaces.
- `src/ProbabilisticLogic/Distribution/Possibility.agda :: >>=𝒫-comm` — no
  `>>=`-commutativity exists upstream, and `≈𝒫` is neither `↭` nor `∼[set]`
  without decidable equality, so `BagAndSetEquality` does not transport.
- `src/CategoricalCrypto/SFunM/Morphism.agda` — switching `open import Data.Sum`
  to `Data.Sum.Base`: both export `map`/`swap`, so the swap does not restore the
  Prelude's deliberate hiding, and rule 11 forbids a non-clashing
  `using (assocʳ)`.
- `src/Class/Monad/Ext.agda :: Extensional-Maybe` — the branch's one `enum-with`
  site in delta code, swapped to `case x of λ where`. Red:
  `MetaCannotDependOn`, because the motive `(x >>= f) ≡ (y >>= g)` mentions the
  scrutinee, so it needs `case_returning_of_` plus a hand-written motive — not the
  clean swap rule 12 asks for.
- `src/Data/List/Properties/Ext.agda :: stripPrefix` — the other `enum-with` site
  (non-dependent, so a real candidate). Red as written: `case_of_` is not in scope
  in that module, which imports narrowly and does not open `Function.Base`. Paying
  an import for a cosmetic swap in pre-existing, out-of-delta code is not worth
  it; likewise its 5 `using-drop`, 1 `join-lines` and 1 `implicit-drop`
  survivors, which are that file's deliberate stdlib-tier style (3 of its 8
  `using` lists are load-bearing, so dropping the rest would leave it half bare).
- `src/CategoricalCrypto/SFunM/Test/Possibility.agda` — `implicit-drop` finds all
  ten `{M = List}`/`{M = Maybe}` ascriptions in the new suite droppable, since
  each monad's instances are the only ones in scope. Declined: those ascriptions
  *are* the assertion — without them the suite reads `_ : Monoidal SFunᵉ-Category`
  and would silently re-target if a second setoid monad ever entered scope.
