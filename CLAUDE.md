# House standard — all agents, all tasks

Never touch any git configuration!

Normative rules for writing Agda in this repository. Every agent follows them; the
`agda-quality` reviewer (`.claude/agents/agda-quality.md`) additionally *enforces* them.
Form contract for this file: one numbered imperative per rule (rationale at most an
indented one-liner); when adding a rule, merge or delete any rule it overlaps — this file
is a current-state ledger, not an append-only log.

## Soundness (absolute)

1. Never weaken, generalize away, or delete a theorem/lemma statement to make something
   pass; only a proof may change, and only to another proof of the same statement.
2. Never introduce an escape hatch: `postulate`, `{-# TERMINATING #-}`,
   `{-# NON_TERMINATING #-}`, `primTrustMe`/`trustMe`, `{-# NO_POSITIVITY_CHECK #-}`,
   an unsolved hole (`?`, `{!!}`), or removing `--safe`/`--without-K`/`--cubical` from an
   OPTIONS line.
3. The escape-hatch baseline never grows. Before starting work on a scope, record:
   `grep -rnE 'postulate|TERMINATING|NON_TERMINATING|primTrustMe|trustMe|NO_POSITIVITY|NO_TERMINATION|--no-safe|TRUSTME|\{!|\?\?' <scope>`
   — re-run after, diff; every category ≤ baseline, else revert.
4. An *existing* escape hatch is the maintainer's prior decision: leave it; flag it only
   if genuinely suspicious. Do not fill postulates with proofs uninvited.

## Typechecking (what "green" means)

5. Canonical check: `pagda --useUntracked false check src/<Path>.agda -- +RTS -M3G -H1G -RTS`.
   Always `--useUntracked false` (else pagda dies prompting on empty stdin); always pair
   `-M` with `-H` — a bare `-M` falsely reports `Heap exhausted` on ~1 GiB modules. On
   `Heap exhausted`, first retry with `-H1G` paired and a larger `-M`; never conclude
   "module too big" from a run without `-H`. Wrap every check in `timeout` and never wait a
   slow one out: a **warm single-module** run — its own log has exactly **one** `Checking`
   line — gets a budget of **60 s + LOC/4 s**; on overrun, kill it (only PIDs you spawned)
   and treat the time as a defect per rule 31, unless the module header documents its
   measured cost. Runs rebuilding dependencies (several `Checking` lines) get a 1800 s
   ceiling instead — if a budget kill fires and the partial log shows several `Checking`
   lines, re-run once under the ceiling. One agda run at a time: pagda's memory gate
   serializes, so a hung run silently queues every other check (wall-clock ≠ compute).
   Mechanics, baselines, and how to force a warm measurement: `.claude/agda-toolchain.md`.
6. rc=0 is NOT green. After every check, scan its output with
   `grep -nE 'ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing'`;
   any hit = the check FAILED — fix or revert until rc=0 and that grep is empty.
   Never pass `--warning=error`/`-W error` (it dies on the read-only nix store).
7. Never force `--safe`/`--without-K`/`--cubical` on the CLI: per-file OPTIONS pragmas
   govern the whole closure; CLI flags override them and produce bogus verdicts.
8. After editing a module, also check its in-repo importers — transitively where a name is
   `open … public`-re-exported (a new/renamed name can silently clash in an opener).
   Multi-file work ends with a closure check: the `*Tests` suites + `CategoricalCrypto`.
9. Toolchain reference (memory gate, nix-daemon restart, orphan reaping, profiling):
   `.claude/agda-toolchain.md`.

## Style

10. Imports at the top, sorted by library then alphabetically.
11. Prefer a bare `open M` — write a `using` list only to resolve a real clash, and then
    the smallest subset that checks green. (`open M using () renaming (…)` stays.)
    A non-clashing `using` "documenting the dependency" is noise here, not safety.
12. Prefer `case_of_` / `case_returning_of_` over `with` when it is a clean swap.
13. `∎` never on its own line. Indent 2 spaces, except when aligning matching subterms.
14. Compact layout: if a multi-line construct (signature, field block, short body,
    `where`/`let` binding, case arm) fits the file's prevailing line width on one line,
    put it on one line; a record's first field goes on the `field` line.
15. Drop explicit implicit/instance arguments (`{…}`/`⦃…⦄`) at use sites when the code
    checks without them.
16. Declare a repeated implicit telescope once in a `private variable` block instead of
    re-binding it (`∀ {n m} → …`) in every signature of a lemma family. Keep one merged
    block per scope, and prefer α-renaming a binder to a name the block already declares
    over adding a variable; spare variables are tolerable, fewer is better. Exception:
    keep a paired family (`x y`, `x₁ y₁`, `x₂ y₂`) whose members co-occur when some
    signatures need one pair and others two — don't collapse `x y` into `x₁ y₁`.
17. Prefer the point-free form when it is a clean swap: eta-reduce
    (`λ x → f (g x)` → `f ∘ g`) and use an operator section over a one-use lambda
    (`cong (λ z → a ∷ z)` → `cong (a ∷_)`).
18. Inline single-use `where`/`let`/`private` scaffolding and wrappers that only
    eta-expand another definition.
19. No forwarding-only modules or `open … public` layers whose only job is re-export;
    open the source directly. Replace repeated `R.x` qualification with a local `open R`
    (and repeated local opens of the same module with one `module A = X` + `open A`).
20. Prefer standard categorical / stdlib notation and idioms over ad-hoc symbols.

## Comments

21. A comment survives only if it carries something a competent reader cannot get from
    the code in seconds: a non-obvious *why* (trick, invariant, gotcha) or a citation
    (book §, paper, the library lemma a definition mirrors). Default is cut;
    "it documents X" is not a reason when the code already shows X.
22. Never narrate the *what*: no restating types/OPTIONS/exports/structure, no
    per-step or per-clause paraphrase, no design-alternative essays ("why not X",
    "sibling module Y does…"), no development leftovers ("new/now/added/(was …)",
    done-TODOs, refactor notes-to-self).
23. Module headers are orientation: ≤25 lines freely, ~50 with justification, ~100 with a
    good reason; an essay moves to `docs/` with a one-line pointer — and design-narration
    is cut regardless of length (the ceiling bounds legitimate orientation, it is not a
    keep-quota).
24. One explanation, once, at the most user-facing site in the import graph; the other
    site references it (`see <where>`) or says only what is specific to itself.
25. Section banners keep the project's boxed dash-rule form (rule / `-- Title` / rule,
    matching the file's rule width). A banner earns its place only as a top-level landmark
    grouping more than one definition under a shared theme; a per-lemma divider is noise.
26. **Uniformity is not a keep-reason.** "It's part of a consistent scheme / breaks the
    per-file uniformity" never justifies keeping noise (a divider per definition, an
    unused-implicit telescope repeated across a lemma family, a per-clause gloss pattern)
    — the scheme itself is what is being judged. When a cut applies to one member of a
    uniform family, apply it to the **whole family**: uniformity is preserved by uniform
    application, never by uniform retention.

## Placement & reuse

27. A general-purpose lemma/definition lives in a general-purpose module (a topical
    `…/Properties`, `…/Util`, prelude-style module), never buried in a narrow one; if no
    suitable module exists, add one named for its scope.
28. Within a file, related definitions sit adjacent: a lemma lives next to the
    definition or family it is about — group by relocating within the file rather than
    leaving accretion order.
29. If the natural module name `X` exists upstream (stdlib / agda-categories), do not
    shadow it — extend it as `X.Ext`.
30. Before writing a definition, lemma, or notation, check agda-categories and the stdlib
    (`HomReasoning`, `Commutation`, `Morphism.Reasoning`, Kelly coherence, the solvers);
    reuse or match the ecosystem over reinventing.
31. Fix typecheck performance by restructuring the source (e.g. isolate heavy development
    in its own module), never by RTS flags or option toggles; claim a speedup only from a
    measured before/after on the same warm/cold basis.
32. Be conservative with `private`: this is a foundational library, so absence of a
    current importer is not absence of downstream value. Privatize only the clearly
    bespoke one-off (free exceptions: `variable` blocks, pure plumbing modules); when in
    doubt, keep it public.
33. Test suites exercise the **public entry points** (the API downstream users call), not
    internal helpers — a test pinning an internal helper both under-tests the public API
    and freezes the internal. Target an internal directly only when that internal is
    itself the thing under test (e.g. a negative/`≡ nothing` test of a decision kernel).

## Conduct

34. Never broadly kill processes (`pkill agda`, `pkill -f …`) — other worktrees compile
    concurrently; manage only PIDs you spawned. (Orphan reaping: see the toolchain
    reference.)
35. Never modify `flake.nix` / `pagda.nix` / CI without flagging it; never force-push or
    touch branches/worktrees that are not yours.
