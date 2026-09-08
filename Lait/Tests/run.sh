#!/usr/bin/env bash
# Run every Lait test file and report which ones are clean.
#
#   ./Lait/Tests/run.sh              # all test files
#   ./Lait/Tests/run.sh TestBasics   # just the named ones
#
# A test file passes when `lake env lean` on it produces no `error:` line.
# `#test` / `#test_error` failures, `#guard_msgs` mismatches and type errors all
# show up that way; `#eval`, `#check` and `print` output is ignored.
#
# NOTE: `lake env lean` loads imported modules from their .olean files and does
# NOT rebuild them.  Run `lake build Lait` first after touching anything under
# Lait/ or you will be testing a stale compiler.

set -uo pipefail
cd "$(dirname "$0")/../.."

if [ "$#" -gt 0 ]; then
  files=()
  for name in "$@"; do files+=("Lait/Tests/${name%.lean}.lean"); done
else
  files=(Lait/Tests/*.lean)
fi

fail=0
for f in "${files[@]}"; do
  [ -e "$f" ] || { printf 'MISSING %s\n' "$f"; fail=1; continue; }
  out=$(lake env lean "$f" 2>&1)
  if printf '%s\n' "$out" | grep -q 'error:'; then
    printf 'FAIL  %s\n' "$f"
    printf '%s\n' "$out" | grep 'error:' | sed 's/^/        /'
    fail=1
  else
    printf 'ok    %s\n' "$f"
  fi
done

exit $fail
