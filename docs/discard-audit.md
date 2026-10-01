# WP7: auditing `State.discard`

**2026-09-30: module deleted** (shelved). Recover with `git log --diff-filter=D --oneline -- src/CategoricalCrypto/Machines/Spike/DiscardAudit.agda`, then `git show <commit>^:<path>`.

**2026-09-30: decision taken.** The maintainer accepted §5: machines are pointed, and `discard`/`θ-discard` were removed in `295aef2b`. The spike keeps the old shape locally as the comparison record, so its line numbers below no longer match.

This is the WP7 deliverable of `docs/model-state-events-and-preservation-plan.md`, audited at
`28d516a6`. All paths are relative to `src/CategoricalCrypto/`. "Spike" means
`Machines/Spike/DiscardAudit.agda`. The spike typechecks green (`--safe --without-K
--guardedness`, no escape hatches). It is **not imported by the root `CategoricalCrypto.agda`**,
on purpose. A claim that is argued on paper but not checked is marked UNVERIFIED.

## 1. Consumer inventory

A search for `discard` over `src/CategoricalCrypto` finds the sites below. It also finds four
prose uses of the English word, which are not consumers: `Examples/RelSetup.agda:86-150`,
`Examples/ROCommitment/Game.agda:245`, `UC/Audit/Canonical.agda:11` and
`UC/Machine/Monitor.agda:10`. Each site is classified as:

- **E**: operational execution;
- **A**: a genuine theorem assumption;
- **P**: propagation of a field already present in the record. This includes the coherence lemmas
  that exist only to discharge a propagated `θ-discard`.

| Site | Role | Class |
|---|---|---|
| `Machines/Core.agda:44` | the field `discard : obj ⇒ unit` | definition |
| `Machines/Core.agda:49` | `Iˢ` sets `discard = id` | construction |
| `Machines/Core.agda:57` | `S ⊛ T` sets `discard = λ⇒ ∘ discard S ⊗₁ discard T` | construction (P) |
| `UC/Machine.agda:90` (`initˢ`) | `discard = λ _ → returnₚ tt`; 25 call sites (every Example and UC state) | construction |
| `Protocol/Machine.agda:82` (`stateᴹ`) | `discard = λ _ → returnₚ tt` | construction |
| `Protocol/Machine/Compose.agda:76` | `discard = λ _ → returnₚ tt` | construction |
| `Machines/Sim.agda:49` | field `θ-discard : discard (state g) ∘ θ ≈ discard (state f)` | the obligation |
| `Machines/Sim.agda:63,66,70` | `sim` takes it as an argument; `mk-cong` supplies `identityʳ` | P |
| `Machines/Sim.agda:80` | `≲-trans` composes it | P |
| `Machines/Sim.agda:112,117` | `collapseˡ/ʳ` supply `λ-discard`/`ρ-discard` | P |
| `Machines/Frame.agda:270-273` | `⊛-discard₂` | P (coherence) |
| `Machines/Frame.agda:290-297` | `λ-discard`, `ρ-discard` | P (coherence) |
| `Machines/Frame.agda:302-312` | `⊛-assoc-discard` | P (coherence) |
| `Machines/Category.agda:45` | `assoc-∘ᴹ` | P |
| `Machines/Category.agda:69-70` | `∘ᴹ-resp-≲` | P |
| `Machines/Tensor.agda:110-111` | `⊗ᵉ-resp-≲` | P |
| `Machines/Tensor/Assoc.agda:71-74` | `⊗-split`'s `dsc-u` | P |
| `Machines/Tensor/Structural.agda:180,185-186` | `braiding-commuteᴹ`'s `discard-σ` | P |
| `Machines/Trace/Naturality.agda:74-76,105-107` | two `d-ok` | P |
| `Machines/Trace/Congruence.agda:81` | `trace-resp-≲` passes `θ-discard s` through | P |
| `Machines/Pointwise.agda:96` | `simFn`'s pointwise discard hypothesis | P |
| `Machines/Pointwise.agda:117-124` | `discard-⊛`: a paired state is canonical if both factors are | P |
| `UC/Machine/Monitor/Agree.agda:358-362` | `watch-discard` takes `he : ∀ se → discard (state E) se ≈ₚ returnₚ tt` | **A**, discharged by `λ _ → ≈refl` at `:447` |
| `UC/Machine/Monitor/Agree.agda:447,473`, `UC/QueryBound.agda:395` | callers discharge the obligation with `>>=ₚ-identityˡ` | P |

**Class E is empty.** No run semantics executes `discard`:

- `runᴹFrom` finishes with `returnₚ b` (`Protocol/Machine.agda:107-111`), and
  `runᴹ = point >>= runᴹFrom` (`:113-114`).
- `⟦_⟧ᴼ` is `runᴹ` (`UC/Machine.agda:98-99`).
- `behᵍ` (`UC/QueryBound.agda:180-181`) is `point` followed by `traceᵍ`, and `traceᵍ`
  (`:176-178`) finishes with `returnₚ []`.
- `traceᴹ` keeps the state (`Machines/Trace.agda:74-75`).
- The closed-composite observation `UC/Seam/Plug.agda:71-80` reads only `point` and `step`.
- The run-transfer lemmas `UC/Machine/Run.agda:82-122` use `θ-pure`, `θ-step` and `θ-point`,
  never `θ-discard`.

The only class-A site is also an artefact of generality. `watch-discard` has to assume something
about an arbitrary `E`, and its only caller supplies the definitional `returnₚ tt`. This confirms
`QUALITY-REVIEW-C-machines.md` item 8, with one correction. The review cites a `Sim/Lax` module,
but there is no `Machines/Sim/` directory at this commit.

## 2. Which semantics is intended

The plan names three options.

**(a) A chosen augmentation (an arbitrary, possibly effectful `discard`).** The code states this
intent.

- `Machines/Core.agda:35-39` says `discard` is "real data" and "not canonical" because `unit` is
  not terminal in a Kleisli category. It adds that affineness of `𝒱` "is what would make it so".
- `Machines/Sim.agda:43-44` says `θ` "respects the point, the discard and the step".

No construction ever picks a non-canonical discard, and no semantics spends one (§1).

**(b) Canonical pure erasure at this model.** The code implements this in practice.

- Every leaf state has `discard = λ _ → returnₚ tt`: `UC/Machine.agda:90`,
  `Protocol/Machine.agda:82` and `Protocol/Machine/Compose.agda:76`.
- `Iˢ` has `id`, which is `returnₚ` at `Kl`.
- `⊛` preserves canonicity: `Pointwise.agda:117-124`, and generically Spike `canonical-⊛`
  (`:113`) and `canonical-Iˢ` (`:110`).
- `∘ᴹ` and `⊗ᵉ` pair states with `⊛` (`Core.agda:100`, `Tensor.agda:103`), and `traceᴹ`
  and `pureᴹ`/`idᴹ` use the state they are given or `Iˢ` (`Trace.agda:75`, `Tensor.agda:127`,
  `Core.agda:92`).
- So every machine the codebase builds has a discard `≈` the canonical `!`.

**(c) Pointed machines with no discard.** This is what the observations use. Every observation
listed in §1 is a function of `point` and `step` alone.

At `Kl(Dₚ)` with purity `PureSubᵏ`, options (b) and (c) agree exactly (§3). Only (a) differs, and
only on machines nobody builds.

## 3. What each option does to `_≈ᴹ_`

The spike defines `_≲ᵖ_` / `_≈ᵖ_` (`:57`, `:66`): `_≲_` without `θ-discard`, which is option (c).
Its checked results are listed below.

1. **Keeping `θ-discard` changes the relation.**
   - The scalar `discard ∘ point` is an `≈ᴹ`-invariant: `scalar-≲` and `scalar-≈ᴹ` (`:79`, `:82`),
     via `θ-point` and `θ-discard`.
   - Replacing only the discard never changes `≈ᵖ` (`redisc-≈ᵖ`, `:92`). Under `≈ᴹ` it forces
     the two scalars to agree (`redisc-≈ᴹ`, `:97`).
   - Concrete pair (`Kleisli.separated`, `:155`, at any discrete monad with a scalar
     `bot ≉ return tt`): take state `X`, `point = λ _ → return x₀`, any step `k`, and discards
     `!ᵏ` versus `λ _ → bot`. The two machines are `≈ᵖ` but **not** `≈ᴹ`.
   - At `Dₚ`, `botₚ` is such a scalar (`bot≉return`, `:165`). Instantiating `separated` at `Dₚ`
     only requires plugging in `Machines.Base.Dₚ-DiscreteMonad` (`Machines/Base.agda:63`). That instantiation step is UNVERIFIED in
     Agda: the spike avoids importing `Machines.Base` to keep the check cheap.
2. **For the machines the codebase builds, the relations coincide.** Suppose `unit` is terminal in
   `𝒫`, with a pure `!` that is unique among pure maps into `unit` (`module Canonical`, `:101`).
   - Every pure `θ` then satisfies `! ∘ θ ≈ !` (`!-natural`, `:104`).
   - So `θ-discard` holds automatically between canonical states (`canon-≲`, `:120`).
   - This gives `comparison` (`:127`): for canonical `f` and `g`, `f ≈ᵖ g → f ≈ᴹ g`. The proof
     replaces every intermediate machine of the zig-zag by its canonical copy (`canon-self`, `:123`).
   - The converse `≈ᴹ⇒≈ᵖ` (`:72`) holds unconditionally.
   - The hypotheses hold at every `Kl(M)` with `PureSubᵏ`. `Canonicalᵏ` (`:147`) instantiates
     them with `!ᵏ = pureᵏ (λ _ → tt)` and `!-unique = proj₂`, by η for `⊤`.

   So between machines with canonical discards, `≈ᴹ` (option a) is exactly `≈ᵖ` (option c). The
   answer to the brief's question is yes, on paper and now in Agda: every simulation between the
   current machines satisfies `θ-discard` automatically, because `θ` is pure and every discard is
   `≈ returnₚ tt`.
3. **Option (b) versus (c).** Under (b), `θ-discard` is `!-natural`, a theorem. So (b) is (c) with
   a redundant field.

The categorical reading below is UNVERIFIED as a checked functor; its hom-level content is items
1–2.

- `canon` (spike `:117`) sends pointed machines into the old category.
- It is fully faithful on hom-setoids (`comparison` together with `≈ᴹ⇒≈ᵖ`).
- Its image is the canonical machines, which are closed under `idᴹ`, `∘ᴹ`, `⊗ᵉ`, `pureᴹ` and
  `traceᴹ` by `canonical-Iˢ` and `canonical-⊛`.
- On machines, `canon (g ∘ᴹ f)` and `canon g ∘ᴹ canon f` differ only in their discards (`!`
  against `λ⇒ ∘ ! ⊗₁ !`), and those are `≈` by `!-unique`. So `canon` preserves the structure up
  to identity simulations.
- The old category's extra content is the non-canonical-discard machines. Each is `≈ᵖ` to its
  canonical copy, but in general not `≈ᴹ` to it.

## 4. Affineness

- **No concrete discard diverges.** All three leaf definitions are `λ _ → returnₚ tt` (§2), and
  `Iˢ`/`⊛` preserve that.
- **The type allows divergence, and `Kl(Dₚ)` is not affine.** `botₚ : Dₚ ⊤` is not `≈ₚ`
  `returnₚ tt` (spike `bot≉return`, `:165`). Its `cum` is `0` (`ProbabilisticLogic/Dp.agda:473`),
  while `returnₚ`'s is `1` (`:470`). So `unit` is not terminal, and a state such as
  `rediscˢ S (λ _ → botₚ)` is well-typed.
- **The pure subcategory is affine.** `unit` is terminal among the pure maps (`Canonicalᵏ`), which
  is exactly the hypothesis `comparison` needs.
- **Terminating probabilistic discards.** Informally, the only non-canonical discards at `Dₚ`
  lose mass. A map `S → Dₚ ⊤` that terminates with probability 1 should be `≈ₚ returnₚ tt`,
  because `≈ₚ` sees only `cum`, and at `⊤` that is `P tt` times the mass. This is UNVERIFIED: it
  is not in the spike and there is no lemma for it in `Dp/Mass.agda`.
- **Plan item 5.** For this reason, adding `>>= discard` to `runᴹ` would change verdict
  probabilities whenever a discard loses mass. With the canonical discard it is the identity up to
  `>>=ₚ-identityˡ`. Nothing in the codebase needs it.

## 5. Recommendation

**Remove `discard` from `Machines.Core.State` and `θ-discard` from `_≲_`, making machines pointed
(option c).** This is gated on the maintainer's sign-off, because it changes the hom equality of
`ℳₚ`/`𝒢ₚ` (house rule 1).

- Nothing spends the field (§1, class E is empty).
- The codebase de facto implements option (b), and (b) is provably (c) on every machine it builds
  (§3.2).
- Keeping option (a) buys only the ability to distinguish machines that no construction produces
  and no observation can tell apart (§3.1). Its cost is a coherence family and a proliferating
  hypothesis (`watch-discard`).
- If the maintainer wants to keep an effectful-erasure semantics open, the conservative
  alternative is to leave the code unchanged and fix the header of `Core.agda:35-39`. That header
  should say that every constructed discard is canonical, and that the relation is finer only on
  non-canonical machines, citing this document.

### Migration steps

1. Before any edit, land the spike's comparison as the record of equivalence. It has to be checked
   against the *old* definitions, because afterwards `θ-discard` no longer exists. Move it to
   `docs/` or keep it as an unwired module, as the maintainer prefers.
2. `Core.agda`: drop the field at `:44`, and the `discard` components of `Iˢ` (`:49`) and `⊛`
   (`:57`). Rewrite the header at `:35-39`.
3. `Sim.agda`: drop `θ-discard` (`:49`), `sim`'s argument (`:63`, `:66`) and its uses at `:70`,
   `:80`, `:112` and `:117`.
4. `Frame.agda`: delete `⊛-discard₂`, `λ-discard`, `ρ-discard` and `⊛-assoc-discard`
   (`:270-273`, `:290-297`, `:302-312`), plus the prose at `:5` and `:236`.
5. Remove the propagation sites in these files:
   - `Category.agda:45,69-70`
   - `Tensor.agda:110-111`
   - `Tensor/Assoc.agda:71-74`
   - `Tensor/Structural.agda:185-186`
   - `Trace/Naturality.agda:74-76,105-107`
   - `Trace/Congruence.agda:81`
   - `Pointwise.agda:96,117-124`
   - `UC/Machine/Monitor/Agree.agda:358-362,447,473`
   - `UC/QueryBound.agda:395`
6. Drop the leaf fields at `UC/Machine.agda:90`, `Protocol/Machine.agda:82` and
   `Protocol/Machine/Compose.agda:76`.
7. Run the closure check: the `*Tests` suites and `CategoricalCrypto`.

The estimated saving is about 65–75 LOC across 17 modules, counted from the §1 inventory. This is
UNVERIFIED until the migration is run. `QUALITY-REVIEW-C-machines.md` item 8 estimated 90–130,
but that figure included the `Sim/Lax` module, which is no longer present.

### Statement changes

- **Statements already true under the new relation.** Every `≈ᴹ` statement between machines built
  from canonical states keeps its meaning (§3.2).
- **Coarser conclusions.** Statements quantified over arbitrary machines get coarser conclusions:
  the category laws, `*-resp-≈ᴹ`, and trace naturality, sliding and vanishing. They are strictly
  coarser only at non-canonical discards, which the new type cannot even express.
- **Stronger hypotheses.** Statements that take `≈ᴹ` as a hypothesis get a stronger premise,
  mainly `run-sim` / `⟦⟧-resp-≈` (`UC/Machine/Run.agda:109-118`). They remain provable verbatim,
  since they read only `θ-point` and `θ-step`.
- **One weakened statement.** `watch-discard` loses its hypothesis `he`, and then its statement
  disappears altogether.

### Comparison theorem needed if `discard` is removed

The spike's `Canonical.comparison` together with `≈ᴹ⇒≈ᵖ`, instantiated by `Canonicalᵏ` at
`Kl(Dₚ)`: on machines with canonical discards, the old `≈ᴹ` and the new relation coincide. The
following are recorded rather than proved:

- the closure of the canonical class under `∘ᴹ` and `⊗ᵉ` (`canonical-⊛` / `canonical-Iˢ` suffice);
- the separation result (`separated`), which records that the old relation was genuinely finer
  off that class.
