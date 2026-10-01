# Agda toolchain reference

Lookup material for working with this repo's toolchain. The normative rules (canonical
check command, warning gate, importer/closure discipline) are in the repo `CLAUDE.md`;
this file is the troubleshooting/how-it-works detail behind them.

## pagda

`pagda` is the maintainer's Nix-based Agda package manager (`github:WhatisRT/pagda`,
pinned in `flake.lock`). Everything goes through it:

```
pagda --useUntracked false check src/<Path>.agda   # typecheck one file (own OPTIONS)
pagda --useUntracked false check                   # typecheck the whole library
pagda --useUntracked false build                   # full build (= nix build .#default)
pagda doc                                          # browsable HTML docs
pagda gen-ci / pagda regenerate                    # CI workflow / flake.nix from template
```

- Args after `check` are forwarded to agda (add `--` if pagda tries to parse one).
- If `pagda` is missing from PATH: `nix profile add github:WhatisRT/pagda`. True fallback
  (what it wraps):
  `/nix/var/nix/profiles/default/bin/nix --extra-experimental-features 'nix-command flakes' develop --command agda src/<Path>.agda`
- `pagda build` builds into the nix store; `pagda check`'s own `.agdai` live under
  `_build/2.8.0/agda/`. Deleting a module's `.agdai` there forces a cold re-elaboration
  (agda invalidates by content hash — `touch` does nothing).

## Memory model (31 GiB RAM, no swap, 17 cores)

The `~/.local/bin/pagda` wrapper is an flock-based memory-aware admission gate: it admits
a check only while summed in-flight agda RSS fits `PAGDA_BUDGET_MB` (default ~24000),
blocks extras, injects a default `-M${PAGDA_MEM:-3}G -H1G` when the caller passes no
`+RTS`, strips `GHCRTS` (pagda lacks `-rtsopts`), and runs each check under
`timeout ${PAGDA_TIMEOUT:-900}` with a trap that releases the slot on kill.

- If you pass your own `+RTS`, you MUST pair `-M` with `-H` yourself (CLAUDE.md rule 5).
- A lone serial check may use a big heap (`-M16G` is the deep-review serial-retry
  default; up to ~24G fits).
- If checks block forever with no agda running, the slot counter leaked:
  inspect `/tmp/pagda-sem.count`, reset with `echo 0 > /tmp/pagda-sem.count`.
- Real solver modules need ~1–1.5 GiB and check in ~5–7 s warm; treat bigger claims as
  the missing-`-H` artifact until proven otherwise.

## Profiling

Forward `--profile=modules` / `--profile=definitions` to `pagda check` for before/after
numbers, or use the `agda-typecheck-profile` skill for cold per-module/per-definition
timings. `--profile=modules` totals include interface deserialization (~fixed cost), not
just editable content.

## Failure modes

- **`cannot connect to socket … daemon-socket`** — the nix daemon died (not a typecheck
  error). Restart (invoke the symlink directly; it dispatches on argv[0]):
  `sudo sh -c 'setsid /nix/var/nix/profiles/default/bin/nix-daemon --daemon >/tmp/nd.log 2>&1 </dev/null &'`
- **`No space left on device`** — the nix store filled the overlay; report it (a
  `nix-collect-garbage -d` usually frees most of it). Never silently skip verification.
- **`removeLink: permission denied` (rc=42)** — you changed agda's interface fingerprint
  (e.g. `--warning=error`) and it tried to rewrite read-only nix-store interfaces. Drop
  the flag; the warning gate in CLAUDE.md rule 6 is the working substitute.

## Orphaned-process reaping

A finished subagent can leave parentless (PPID 1) toolchain processes spinning (e.g. a
search mis-rooted at `/` pinning many cores). Orphaned = no live owner, so killing them is
safe and is NOT a broad `pkill` (a live compile always has a parent). Match the toolchain
by name so PPID-1 sandbox infra (socat proxy, supervisor `sh`, dockerd, nix-daemon)
survives; run twice (a killed parent reparents its children to PID 1):

```
ps -eo pid=,ppid=,comm=,args= | awk '$2==1 && ($3 ~ /^(agda|ugrep|rg|grep|egrep|find|nix|ghc|cabal|node|git|python3?)$/ || $3 ~ /^[0-9]+[.][0-9]+[.]/ || $0 ~ /ugrep/){print $1}' | xargs -r kill
```

(The `^[0-9]+[.][0-9]+[.]` clause catches the bundled claude tool binary, whose `comm` is
its version string.)

## Typecheck time budgets (rule 5's timeout discipline — measured 2026-07-29)

**The detector is post-hoc and free — never predict cache state.** Agda prints one
`Checking M (path)` line per module it actually re-elaborates and nothing for `.agdai`
interface loads, so the run's own log decides which regime you were in:

- `grep -c 'Checking' log` = 1 → warm single-module. Budget: **60 s + LOC/4 s**.
- count > 1 → dependencies were rebuilding. Ceiling: **1800 s**; no per-LOC budget.
- count = 0, rc=0, seconds-fast → pagda content-hash cache hit (nothing elaborated).
  `touch` does NOT invalidate pagda's cache; to force a genuine warm measurement, append a
  comment line, run, then delete it.

**Baselines (warm, single module, free machine, `+RTS -M10G -H2G`):** 35-LOC module ≈ 8 s,
268-LOC `Abstract2` (the full U-kernel metatheory) ≈ 5 s — startup + interface loading
dominate; real elaboration of a few-hundred-line theory file is seconds. A 258-line file
needing >3 min of compute is a ~50–150× pathology (conversion/meta blowup class — see the
eta-OOM and explicit-implicits notes), to be fixed by restructuring (rule 31), never waited
out. Legitimately heavy modules document their measured warm cost in their header comment;
an undocumented budget overrun is a defect by definition.

**Contention invalidates timings.** pagda's memory gate serializes agda runs: while any
run is alive, new checks QUEUE (0% CPU) and their wall-clock is meaningless. Before timing
anything: `ps -eo pid,etime,pcpu,rss,args | grep agda` and kill YOUR stale runs (specific
PIDs only — other worktrees compile concurrently, rule 34). A budget kill under contention
proves nothing; re-measure on a free gate.
