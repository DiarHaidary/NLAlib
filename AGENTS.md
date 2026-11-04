# Agents working in this repository

`CONTRIBUTING.md` is the contract, for agents as for people: read it in full before writing
library code, and read `docs/rules/DIGEST.md` and the `NLAlib/<Topic>/RULES.md` of each topic you
touch. The rules below are the ones specific to agents.

1. **Do not change the checks.** Never edit `scripts/stage_check.sh`, the check scripts
   (`scripts/check_*.py`, `scripts/check_latex.mjs`, `scripts/*.lean`, their tests and fixtures),
   `docs/rules/rules.toml`, the allowlists `scripts/rules_allow.toml` and
   `scripts/names_allow.toml`, the ratchet `scripts/rules_baseline.json`, `.github/` (CI,
   CODEOWNERS, the PR template) or the build pins (`lakefile.toml`, `lake-manifest.json`,
   `lean-toolchain`), unless that edit is the task you were given. If a check seems wrong, or a
   false positive needs an allowlist entry, say so in your report; do not work around it.
2. **Do not register targets.** Never edit a `*Targets.lean` file, `docs/targets.toml` or
   `docs/targets.approved`; target statements change only with the maintainer's approval
   (CONTRIBUTING §5.5). Prove a registered target as stated; if you cannot, report it.
3. **Do not push**, and do not commit unless you are asked to.
4. **Run the checks before you report.** `python3 scripts/check_rules.py --files <files>` while
   working; `bash scripts/stage_check.sh` (exit 0) before you call the work finished
   (CONTRIBUTING §9). Never run a bare `lake build`; build with `LEAN_NUM_THREADS=2` and a log
   file, one build per checkout at a time (CONTRIBUTING §10).
5. **Stay in scope.** Search Mathlib, then `NLAlib/`, before proving anything. Do not weaken a
   statement to make it provable, and do not add theorems, interfaces or §5.3 rows beyond your
   task; note what you saw in your report instead.
