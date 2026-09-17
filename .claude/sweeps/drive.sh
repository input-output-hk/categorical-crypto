#!/usr/bin/env bash
# Drive one sweep class to a green fixpoint, file by file, bisecting a red
# batch until only accepted sites remain.  Usage: drive.sh <class> <file>...
# Prints one line per file: KEPT/CANDIDATES, and the rejected ids.
set -u
cd "$(dirname "$0")/../.." || exit 99
CLASS=$1; shift
for f in "$@"; do
  ids=$(python3 .claude/sweeps/sweep.py --sweep "$CLASS" "$f" 2>/dev/null | cut -f1 | paste -sd,)
  [ -z "$ids" ] && continue
  n=$(echo "$ids" | tr ',' '\n' | wc -l)
  # try the whole file at once
  accept=""; reject=""
  try () {  # $1 = comma list; returns 0 if green
    git checkout -q -- "$f"
    python3 .claude/sweeps/sweep.py --sweep "$CLASS" --apply "$1" "$f" >/dev/null 2>&1
    out=$(agda "$f" 2>&1); rc=$?
    w=$(printf '%s\n' "$out" | grep -ic warning)
    [ "$rc" -eq 0 ] && [ "$w" -eq 0 ]
  }
  if try "$ids"; then
    accept=$ids
  else
    # greedy: add one id at a time, keeping the running green set
    for id in $(echo "$ids" | tr ',' ' '); do
      cand="${accept:+$accept,}$id"
      if try "$cand"; then accept=$cand; else reject="${reject:+$reject,}$id"; fi
    done
  fi
  git checkout -q -- "$f"
  [ -n "$accept" ] && python3 .claude/sweeps/sweep.py --sweep "$CLASS" --apply "$accept" "$f" >/dev/null 2>&1
  k=0; [ -n "$accept" ] && k=$(echo "$accept" | tr ',' '\n' | wc -l)
  echo "$f  kept=$k/$n  rejected=[${reject:-}]"
done
