#!/usr/bin/env bash
# Stage checks on the fully proved part of the library (CONTRIBUTING §9), usable while later
# skeletons still contain `sorry`.
#
# Usage: scripts/stage_check.sh [EXCLUDE_REGEX]
# Builds every module that `scripts/proved_modules.py` lists (minus those matching EXCLUDE_REGEX,
# for files an agent is editing) with warnings fatal (`--wfail`, as in CI), then runs the axiom
# audit and the environment linters on exactly those modules, the program checks
# (scripts/Programs.lean, rules E2, E4 and E9, on the whole library as in CI, after a
# `lake build NLAlib` in which `sorry` warnings are allowed), the target lint
# (scripts/Targets.lean, rule E3: the registry docs/targets.toml, its closure hashes and its
# approval), the access-model fixtures (scripts/AccessModelFixtures.lean), the reference check, the named-bound
# value check (scripts/check_constants.py, on the whole library), the freshness of the generated
# rule files (scripts/gen_rules_md.py --check), the rules check
# (scripts/check_rules.py, by rule id, the naming rules N1–N18 included, on an extraction of those
# modules) and the duplicate-statement report (which never fails the script). Logs go to $TMPDIR
# (default /tmp). Run from the repository root; never while another build is running
# (CONTRIBUTING §10).
set -euo pipefail
tmp="${TMPDIR:-/tmp}/nlalib-stage-check"
mkdir -p "$tmp"
python3 scripts/proved_modules.py | grep -v '^NLAlib$' | grep -Ev "${1:-^$}" > "$tmp/modules.txt"
sed 's/^/import /' "$tmp/modules.txt" > "$tmp/imports.txt"
echo "$(wc -l < "$tmp/modules.txt") proved modules;" \
  "$(python3 scripts/proved_modules.py bad | grep -c . || true) not yet"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake build --wfail $(tr '\n' ' ' < "$tmp/modules.txt") \
  > "$tmp/build.log" 2>&1 || { tail -30 "$tmp/build.log"; exit 1; }
echo "build: $(tail -1 "$tmp/build.log"); warnings: $(grep -c 'warning' "$tmp/build.log" || true)"
for check in Audit Lint; do
  { cat "$tmp/imports.txt"; sed '1d' "scripts/$check.lean"; } > "$tmp/$check.lean"
  LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/$check.lean" 2>&1 | tail -4
done
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake build NLAlib > "$tmp/build-all.log" 2>&1 || \
  { tail -30 "$tmp/build-all.log"; exit 1; }
LEAN_NUM_THREADS=1 lake env lean -M 8000 scripts/Programs.lean > "$tmp/programs.log" 2>&1 || \
  { grep -v 'declaration uses .sorry.' "$tmp/programs.log"; exit 1; }
grep '^programs:' "$tmp/programs.log"
LEAN_NUM_THREADS=1 lake env lean -M 8000 scripts/Targets.lean > "$tmp/targets.log" 2>&1 || \
  { grep -v 'declaration uses .sorry.' "$tmp/targets.log"; exit 1; }
grep '^targets:' "$tmp/targets.log"
LEAN_NUM_THREADS=1 lake env lean -M 8000 scripts/AccessModelFixtures.lean > "$tmp/fixtures.log" 2>&1 || \
  { cat "$tmp/fixtures.log"; exit 1; }
echo "access-model fixtures: $(grep -c '^theorem' scripts/AccessModelFixtures.lean) theorems, ok"
python3 scripts/check_refs.py | tail -1
python3 scripts/gen_rules_md.py --check
python3 scripts/check_constants.py > "$tmp/constants.log" || { cat "$tmp/constants.log"; exit 1; }
tail -1 "$tmp/constants.log"
if node --input-type=module -e "await import('katex')" 2>/dev/null; then
  node scripts/check_latex.mjs > "$tmp/latex.log" 2>&1 || { cat "$tmp/latex.log"; exit 1; }
  tail -1 "$tmp/latex.log"
else
  echo "check_latex: skipped, KaTeX not found (npm install --no-save --no-package-lock katex@0.16.22)"
fi
{ cat "$tmp/imports.txt"; sed '1d' scripts/Explore.lean; } > "$tmp/Explore.lean"
EXPLORE_OUT="$tmp/explore-data.json" LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/Explore.lean" \
  > "$tmp/explore.log" 2>&1 || { tail -20 "$tmp/explore.log"; exit 1; }
python3 scripts/check_rules.py "$tmp/explore-data.json" --partial > "$tmp/rules.log" || \
  { cat "$tmp/rules.log"; exit 1; }
grep -v '^check_rules:' "$tmp/rules.log" || true
tail -1 "$tmp/rules.log"
{ cat "$tmp/imports.txt"; sed '1d' scripts/Duplicates.lean; } > "$tmp/Duplicates.lean"
LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/Duplicates.lean" > "$tmp/duplicates.log" 2>&1 || true
cat "$tmp/duplicates.log"
