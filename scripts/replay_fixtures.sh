#!/usr/bin/env bash
# Fixtures of the kernel replay (scripts/Replay.lean; final audits, 2026-10-24). Each module of
# scripts/replay_fixtures/ is compiled into a temporary directory and replayed alone
# (REPLAY_ROOTS); every one must fail for its own reason, and FxF, honest apart from its axiom,
# must pass when not strict:
#   FxA     uses a theorem that its import FxBase added with `addDeclCore … (doCheck := false)`:
#           FxBase is read from outside the dependencies and the toolchain
#   FxBase  that forged theorem itself: the kernel rejects it
#   FxB     the same forgery inside a `module` file
#   FxC     an `unsafe` definition used under `set_option debug.skipKernelTC true`
#   FxD     a hand-named `partial` `helper._unsafe_rec` used by a forged theorem
#   FxE     `native_decide`
#   FxF     an axiom (and private, mutual, nested, match and quotient content, which passes)
# Run from the repository root after `lake build` (the base is the package's dependencies).
set -euo pipefail
src=scripts/replay_fixtures
out="$(mktemp -d "${TMPDIR:-/tmp}/replay-fixtures.XXXXXX")"
trap 'rm -rf "$out"' EXIT
lp="$out:$(lake env printenv LEAN_PATH)"
lean="$(lake env which lean)"
for m in FxBase FxA FxB FxC FxD FxE FxF; do
  LEAN_PATH="$lp" "$lean" --root="$src" -o "$out/$m.olean" "$src/$m.lean" > "$out/$m.build" 2>&1 ||
    { cat "$out/$m.build"; exit 1; }
done
fail=0
expect() {  # module, REPLAY_STRICT or "-" for the default, expected exit, expected message
  local log="$out/$1.$2.log" code=0
  if [ "$2" = - ]; then
    LEAN_PATH="$lp" REPLAY_ROOTS="$1" "$lean" scripts/Replay.lean > "$log" 2>&1 || code=$?
  else
    LEAN_PATH="$lp" REPLAY_ROOTS="$1" REPLAY_STRICT="$2" "$lean" scripts/Replay.lean > "$log" 2>&1 \
      || code=$?
  fi
  if { [ "$3" = 0 ] && [ "$code" = 0 ]; } || { [ "$3" != 0 ] && [ "$code" != 0 ]; }; then
    if grep -q -- "$4" "$log"; then echo "replay fixture $1: ok ($4)"; return; fi
  fi
  echo "replay fixture $1 (strict: $2): exit $code, expected $3 and \"$4\""; cat "$log"; fail=1
}
expect FxA - 1 'FxBase (read from'
expect FxBase - 1 'declaration type mismatch'
expect FxB - 1 'declaration type mismatch'
expect FxC - 1 'is `unsafe` or `partial`'
expect FxD - 1 "unknown constant 'helper._unsafe_rec'"
expect FxE - 1 'is an axiom'
expect FxF - 1 'is an axiom'
expect FxF '' 0 ' 0 violations'
exit $fail
