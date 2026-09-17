# Hand-rolled style sweeps

This repository has no tree-sitter sweep toolkit and no `pagda`, so the
dimension-4 and dimension-5 passes of the quality contract are driven by the
two scripts here plus the real typecheck oracle.  Everything is line-oriented;
nothing here parses Agda, so every candidate is a *guess* that the oracle
accepts or rejects.

## The oracle

    ./.claude/sweeps/check.sh <file.agda> ...

Green means `agda <file>` exits 0 **and** prints no line containing `warning`,
under the file's own `OPTIONS`.  Run it from the repository root; Agda picks up
`categorical-crypto.agda-lib` from there.

Two gates, and they cost very different amounts:

- a single module, deps warm: 30 to 40 s;
- the whole closure, `check.sh src/CategoricalCrypto.agda`: 12 s when nothing
  changed, 4 to 5 minutes once a widely-imported module is touched.

So iterate per file, and use the closure check as the gate before a commit.
Keep `_build`; a cold cache makes every number above ten times worse.

## Enumerating candidates

    python3 .claude/sweeps/sweep.py --sweep <class> <file.agda> ...

prints one line per candidate, `id`, `file:start-end`, then class-specific
fields.  `--json` gives the same as JSON.  To apply a subset:

    python3 .claude/sweeps/sweep.py --sweep <class> --apply 3,7,11 <files>

Edits are applied from the highest line number down, so a batch within one
file keeps its offsets.

Classes, and what each is a guess about:

| class | candidate |
|---|---|
| `using-drop` | `open import X using (a; b)` becomes a bare `open import X`.  Skips `using () renaming (…)` and `public`, which the contract exempts. |
| `implicit-app` | an explicit `{A}` argument **to the right of an `=`**, so certainly an application and never a binder.  Many are required pins; expect a low keep rate. |
| `pat-implicit` | a `{x}` pattern on a clause LHS whose name occurs nowhere in the clause. |
| `join-lines` | a continuation line that fits in 80 columns when joined to its predecessor. |
| `enum-with` | a `with` abstraction; reports the scrutinee count, and flags the single-scrutinee ones as `case_of_` candidates.  Enumeration only. |
| `enum-where` | a `where`/`let` binding, with a use count; flags the single-use ones.  Enumeration only. |
| `qual-noise` | a module qualifier used three or more times inside one definition, i.e. a candidate for a local `open`. |

`python3 .claude/sweeps/enum_comments.py <files>` is the dimension-5 pass: it
lists every comment block as header, standalone or inline, with the contract's
noise flags (`leftoverMarker`, `typeEcho`, `headerOverTier`,
`insideDefinition`).

## Procedure

1. Enumerate the class over the in-scope files and record the candidate count.
2. Apply a whole file's candidates, check that file, and on red bisect within
   the file until the surviving subset is green.  A red site is a finding
   about that site, so write down which one and why.
3. Run the closure check once the class is done, then commit the class as one
   mechanical commit.
4. For an enumeration-only class, disposition every site individually.  Where
   the tool flags a site as a likely win, the disposition IS the spike: make
   the edit and let the oracle decide.

## Known limits, stated so nobody trusts these scripts too far

`implicit-app` cannot see a multi-line type signature's telescope, which is
why it refuses everything left of an `=`.  `pat-implicit`'s scope test is
indentation-based and will miss a name used in a sibling clause.  `join-lines`
is blind to deliberate column alignment, so its diff needs reading rather than
skimming.  `qual-noise` counts textually and does not know whether the
qualifier is ambiguous at that point.
