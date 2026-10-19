#!/usr/bin/env bash
# Stage checks on the fully proved part of the library (CONTRIBUTING §9), usable while later
# skeletons still contain `sorry`.
#
# Usage: scripts/stage_check.sh [EXCLUDE_REGEX]
# Builds every module that `scripts/proved_modules.py` lists (minus those matching EXCLUDE_REGEX,
# for files an agent is editing), then runs the axiom audit and the environment linters on exactly
# those modules, the reference check, the named-bound value check (scripts/check_constants.py, on
# the whole library), the naming check (scripts/check_names.py, on an extraction of those modules),
# the rules check (scripts/check_rules.py, by rule id, on the same extraction) and the
# duplicate-statement report (which never fails the script). Logs go to $TMPDIR (default /tmp).
# Run from the repository root; never while another build is running (CONTRIBUTING §10).
set -euo pipefail
tmp="${TMPDIR:-/tmp}/nlalib-stage-check"
mkdir -p "$tmp"
python3 scripts/proved_modules.py | grep -v '^NLAlib$' | grep -Ev "${1:-^$}" > "$tmp/modules.txt"
sed 's/^/import /' "$tmp/modules.txt" > "$tmp/imports.txt"
echo "$(wc -l < "$tmp/modules.txt") proved modules;" \
  "$(python3 scripts/proved_modules.py bad | grep -c . || true) not yet"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake build $(tr '\n' ' ' < "$tmp/modules.txt") \
  > "$tmp/build.log" 2>&1 || { tail -30 "$tmp/build.log"; exit 1; }
echo "build: $(tail -1 "$tmp/build.log"); warnings: $(grep -c 'warning' "$tmp/build.log" || true)"
for check in Audit Lint; do
  { cat "$tmp/imports.txt"; sed '1d' "scripts/$check.lean"; } > "$tmp/$check.lean"
  LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/$check.lean" 2>&1 | tail -4
done
python3 scripts/check_refs.py | tail -1
python3 scripts/check_constants.py > "$tmp/constants.log" || { cat "$tmp/constants.log"; exit 1; }
tail -1 "$tmp/constants.log"
{ cat "$tmp/imports.txt"; sed '1d' scripts/Explore.lean; } > "$tmp/Explore.lean"
EXPLORE_OUT="$tmp/explore-data.json" LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/Explore.lean" \
  > "$tmp/explore.log" 2>&1 || { tail -20 "$tmp/explore.log"; exit 1; }
python3 scripts/check_names.py "$tmp/explore-data.json" --partial > "$tmp/names.log" || \
  { cat "$tmp/names.log"; exit 1; }
grep -v '^check_names:' "$tmp/names.log" || true
tail -1 "$tmp/names.log"
python3 scripts/check_rules.py "$tmp/explore-data.json" --partial --no-names --warn > "$tmp/rules.log"
grep -v '^check_rules:' "$tmp/rules.log" || true
tail -1 "$tmp/rules.log"
{ cat "$tmp/imports.txt"; sed '1d' scripts/Duplicates.lean; } > "$tmp/Duplicates.lean"
LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/Duplicates.lean" > "$tmp/duplicates.log" 2>&1 || true
cat "$tmp/duplicates.log"
