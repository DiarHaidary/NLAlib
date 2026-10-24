# Agents working in this repository

1. Read `CONTRIBUTING.md` in full. It is the contract; §5.4 (interfaces), §8 (designing a stage),
   §10 (memory) and §11 (agent rules) are not optional.
2. Read the current brief (`docs/PORT_MATRIX.md` for the Matrix layer, finished;
   `docs/PORT_PROBABILITY.md` for the Probability round) and the
   current stage's design note in `docs/design/`. If the note does not exist, the stage has not
   been designed: the orchestrator writes it and stops for approval before any proof is written.
3. Read `docs/port/status.md` to see what is in progress and where the last agent stopped.
4. Design is sequential, one stage at a time; proving is parallel (CONTRIBUTING §11). Do the
   declaration or file you own and nothing else. Search Mathlib, then `NLAlib/`, then the prototype
   files the design note names, before proving anything.
5. Build with `LEAN_NUM_THREADS=2 lake build <your module>` and `lake lean <file> -- -M 8000`, output to a log
   file. Never a bare `lake build`. In a shared checkout, never two builds at once; harness jobs
   each build in their own copy over the shared base, and larger rebuilds go through the build
   queue.
6. Before stopping: update `docs/port/ledger.json` and `docs/port/status.md`, run the §9 checks,
   and leave the read-back for the PR. Do not commit or push unless asked.
7. If you orchestrate: keep your own context small. You make the decisions, write the agent briefs,
   read review verdicts and escalations, and commit. Design notes and skeletons are drafted by Opus
   agents from your brief and reviewed by a `model: "fable"` agent before they go to the maintainer.
   Proofs are dispatched through the workflow harness (https://github.com/NLA-lib/workflow) to
   worker agents, open-weight models first, with Claude as the fallback, and come back to you only
   after the checks and the tier-1 review of CONTRIBUTING §11 (maintainer, 2026-10-24, superseding
   the 2026-10-14 routing). Every `Agent` call passes `model` explicitly; there is no default.
