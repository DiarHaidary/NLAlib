# Publication and NumPy audit fixes (2026-11-04)

This closes findings F09–F11 of the library audit. It changes no mathematical interface,
registered program, cost target, trusted kernel check or build pin.

## Publication

The explorer's rolling release must come from the current `main` commit after that commit's
complete CI workflow succeeds. A manually selected feature branch must never publish it.

`.github/workflows/explore.yml` now follows completion of `CI` on main. Its job accepts only a
successful push run from the same repository, or a manual dispatch on `refs/heads/main`.
Checkout, release creation and the downstream notification all use the source SHA, not the
default-branch SHA attached to a `workflow_run` event. Uploads are serialized with `queue: max`
(up to 100 pending runs), so a stale completion does not replace a pending newer publication.

`scripts/explore_publish.py` verifies the event, the current remote main SHA and the latest
push-CI run for that exact SHA. It runs before extraction and immediately before upload;
manual dispatch uses the same checks. It fails closed on missing CI, an API error, a failed
or still-running rerun, or a main branch which has advanced. This is a live-state gate, not
a claim that main cannot advance between the last API response and the upload.

`scripts/test_explore_publish.py` exercises successful automatic/manual publication and the
rejected branch, tag, pull-request, fork, failed-CI, rerun, stale-SHA and API-error cases.
The existing CI Python test discovery runs it on Linux and Windows. Actionlint 1.7.12 checks
the workflow wiring locally except `concurrency.queue`, which that release does not yet
recognize; `queue: max` is checked against GitHub's current documented syntax below.

Sources: GitHub's [workflow events documentation](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#workflow_run)
and [workflow-run API](https://docs.github.com/en/rest/actions/workflow-runs#list-workflow-runs-for-a-workflow),
and [concurrency queue semantics](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#concurrency).

## Value annotations used by the tightened bounds

The F08 correction exposed a parser defect in `check_constants.py`: two adjacent zero-argument
value markers were read as one marker whose arguments swallowed the second comment. The
documented format explicitly supports several markers on one equation. The parser now stops
at the first terminator. Regression tests verify argument boundaries and that omitting either
registered value from the equation still fails. This repairs the parser without weakening
the value, declaration-body, formatting or registry checks.

## NumPy translation

`NLAlibTools/NumPy.lean` remains an unverified emitter outside the trusted library. Its index
arithmetic follows `Computation.IExp.evalIn`: natural subtraction truncates at zero, and
`a % 0 = a`. A Python lambda evaluates the two remainder operands once and selects the
zero case without invoking Python's failing `% 0`. This needs no NumPy or prelude helper.

`emitProg` inserts `pass` when a program emits no statements. This covers a bare `skip`,
sequences of skips, and empty inlined kernels; the existing loop/branch empty-body handling
is preserved.

`emitterRegressionTest` executes actual generated Python for 54 literal, variable and nested
index cases against Lean's evaluator, ten programs with empty bodies in the two kernel modes,
and a write using remainder-by-zero as both buffer offset and value. These standard-library
tests are mandatory during the tools build; the existing NumPy Hutch++ differential tests
remain. After synchronization with PRs #58 and #59, two additional emitted programs (one per
kernel mode) check the new uniform-draw and kernel-call paths together: deterministic hooks
verify call order, dimensions, input/output offsets and the resulting buffer contents, with
zero-divisor remainders in each index position. No new library theorem, definition, result ID
or Mathlib deviation is introduced.

## Kernel identity follow-up from PR #59

The new black-box call case discarded the kernel identifier and emitted one anonymous
`kernel(...)` call for every identifier. Two distinct kernels with the same block shapes
therefore became indistinguishable. `emitF` takes a total `kname : ι → String` binding to
trusted Python callable expressions. `emitProg` accepts that total binding or a partial
`kernelName : ι → Option String`. Omitting both leaves all kernels unbound. An emitted call
with a missing binding raises `NotImplementedError` when execution reaches it. Callers must
supply implementations matching the bindings. Non-inlined `named` nodes delegate their whole
bodies to external implementations, including any internal kernel calls. Programs without
black-box calls retain their existing use of the emitter, and the translation remains unverified.

The binding is carried through nested statements. Six runtime regressions execute two
distinct kernels inside a loop, or reject absent/partial bindings, in both inline modes.
They check the call sequence and exact buffer contents and install an anonymous callback
that fails if accidentally used. The existing uniform/kernel regressions supply their
single binding explicitly. This exporter correction changes no core interpreter or target.
The separate empty-block interpreter correction and its approval consequence are recorded
in `AuditKernelCalls.md`.
