#!/usr/bin/env bash
# Green oracle: agda exits 0 AND prints no line containing "warning".
# Usage: check.sh <file.agda> [more files...]
cd "$(dirname "$0")/../.." || exit 99
rc=0
for f in "$@"; do
  out=$(agda "$f" 2>&1); frc=$?
  w=$(printf '%s\n' "$out" | grep -i -c 'warning')
  if [ "$frc" -ne 0 ] || [ "$w" -ne 0 ]; then
    echo "RED $f (rc=$frc warnings=$w)"
    printf '%s\n' "$out" | tail -40
    rc=1
  else
    echo "GREEN $f"
  fi
done
exit $rc
