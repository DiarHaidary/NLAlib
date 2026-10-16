# Regression as a root application topic

Approved by the user, 2026-10-16, following bounded independent review and an import-DAG check.
The requested historical model names are unavailable in this environment; the existing user-authorized
available-agent fallback was used for the mechanical draft and independent review.

Read-back: CONTRIBUTING §§2, 5.3–5.4, 8, 9–11 and PORT_LOWRANK D8 were consulted.
D8 deliberately placed Gaussian/Haar regression in Sketching because GN consumes it before
Solvers. Its stated rework is “file moves only”. The root Regression topic preserves that
ordering and does not depend on LowRank or Solvers.

## Smallest coherent relocation

Moved four whole topic files, retaining every declaration name, statement and proof:

| Former module | Current module | Subject |
| --- | --- | --- |
| Sketching.Properties.LeastSquares | Regression.Embedding | Deterministic sketch-and-solve/preconditioning from embedding and injection hypotheses |
| Sketching.Properties.LeastSquaresOblique | Regression.Oblique | Error split controlled by injection or approximate multiplication |
| Sketching.Properties.Injection | Regression.Oblivious | Regression tails and the shared OSI orthogonality lemma |
| Sketching.Gaussian.LeastSquares | Regression.SketchAndSolve | Exact Gaussian/Haar completion identities, spectral excess moments and unbiasedness |

All paths have the `NLAlib.` prefix and corresponding `.lean` paths. These are root-directory
peers of Sketching and LowRank, not new distribution-law definitions. Keep Gaussian and Haar
law/moment machinery in RandomMatrix, embeddings/JL/OSE/OSI in Sketching, and RSVD/GN/Nyström in
LowRank. Keep generic deterministic `IsLeastSquaresSolution`, `sketchAndSolve`, pseudoinverse and
oblique-projector algebra in Matrix: Matrix already uses those generic objects and must not
import an application layer. Matrix regression foundations can be linked from the explorer
collection without moving them upward.

The mixed Injection file also contains “OSIs respect orthogonality”, useful to LowRank rather
than solely regression. The whole-file move keeps that lemma with its consumers. It is a shared statement in
Regression.Oblivious;
splitting it back into Sketching would be a separate change, not necessary for a clean DAG.

Do not split the mixed Gaussian/Haar file into Gaussian/Haar modules in this pass. Haar proofs
use the private `obliqueProjector_mul_eq_frames` and `pinv_mul_mul_sketchAndSolve` helpers from
the Gaussian portion. Splitting would require publishing/moving shared helpers or duplicating
proof material; a whole topic file avoids all of that. No compatibility aliases or forwarding
modules are needed: declaration names are unchanged and internal import paths are updated.
This is a module-path break for external direct imports; record it explicitly.

## Import consumers and ordering

Direct source import rewrites:

* Regression.Embedding: Regression.Oblique, Regression.Oblivious and
  LowRank.Structural.RangeFinder.
* Regression.Oblique: Regression.Oblivious.
* Regression.Oblivious: LowRank.Oblivious.RangeFinder.
* Regression.SketchAndSolve: LowRank.Gaussian.GeneralizedNystrom,
  LowRank.Gaussian.EarlyTruncation and LowRank.Gaussian.EarlyTruncationHaar.
* NLAlib.lean is regenerated to replace its four old imports.

Dependency direction remains Matrix/Probability/RandomMatrix/Sketching core → Regression →
LowRank → future Solvers. Specifically the current Gaussian LeastSquares file has NO LowRank
imports: its imports are Matrix least squares, Probability matrix integration, Gaussian block
moments/invariance/rank, and Haar blocks. Conversely the three listed LowRank files import it.
No cycle is introduced by the four whole-file moves. Sketching core has no remaining direct
imports of the relocated files: its current only such importer is Injection, also moved.

CONTRIBUTING's layout/dependency contract now includes a layer 3 application sublayer Regression before
LowRank. Root-directory peer does not mean
that LowRank and Regression must be dependency-independent. D8 records the new placement.
Update active design/status/ledger module references and public module-doc links, plus any
source-path metadata. Historical port provenance need not be rewritten indiscriminately.
Do not merge the two deterministic files during relocation: that is unrelated proof/code churn.

## Explorer collection

Add topic Regression, after Sketching and before LowRank. Suggested groups:

* Sketch-and-solve: definition `NLAlib.sketchAndSolve`; results `sketch-and-solve-ls`,
  `sketch-and-solve-error-decomposition`, `sketch-and-solve-expected-error`.
* Sketch-and-precondition: result `sketch-and-precondition`.
* Least-squares foundations: definition `NLAlib.IsLeastSquaresSolution`; results
  `normal-equations`, `least-squares-pseudoinverse`, `minimum-norm-least-squares`,
  `least-squares-perturbation`.
* Shared geometry: definition `NLAlib.obliqueProjector`; results
  `oblique-projection-error-split`, optionally `oblique-projection-norm`.

The Matrix results remain owned by Matrix; cross-topic collection links should preserve their
canonical result and declaration links. `obliqueProjector` is also useful in the LowRank shared
collection; linking it from both is legitimate. The two existing regression algorithm definitions
are in Matrix, so the new topic need not invent a local duplicate definition to populate itself.
Existing result IDs suffice; do not tag OSI orthogonality helpers as a new regression theorem
merely to inflate the topic. The six Gaussian/Haar identities currently share
`sketch-and-solve-expected-error`, so expose their variants rather than splitting identity IDs.

## Rates and validation

The published source snapshot has NO `Asymptotic:` corollaries in regression-related
LeastSquares/Injection modules. Existing embedding rates can support a future regression rate
proof, but they are not regression-rate theorems. Add no Regression Rates entries in this move.
Explicit exact expectation identities remain browsable as results.

The placement amendment was reviewed before implementation as §8 requires. The four files were
relocated sequentially, and import consumers were updated without proof edits. Validation checks
the import DAG, comment-stripped declarations/proof bodies, generated root imports and source
links. Builds and Lean checks run sequentially with capped threads and logs; references, constants,
LaTeX and fresh extraction are checked as well.
The relocation adds no mathematics, interfaces or aliases. Validation results are recorded below;
no commit is made by the implementation agent.

## Implementation report (2026-10-16)

The four whole-file moves and all direct import consumers are updated, and the root module is
regenerated. Live module-doc links point to Regression. `PORT_LOWRANK` D8 and CONTRIBUTING now
record Regression as the layer 3 application sublayer above Sketching and before LowRank.

Read-back from the relocated Lean alone: `Regression.Embedding` proves deterministic residual
and preconditioning estimates under subspace embedding/injection hypotheses;
`Regression.Oblique` bounds the oblique-projector error term;
`Regression.Oblivious` turns injection/isotropy or JL-moment hypotheses into regression tails;
`Regression.SketchAndSolve` proves Gaussian and Haar completion identities, unbiasedness and
Gaussian spectral-excess estimates. Declaration names, statements and proof bodies are unchanged:
a comment/import-stripped source comparison confirms equality for all four moved files.

The module import DAG is acyclic, and no Sketching-core module imports Regression. Existing
Matrix declarations remain in Matrix. Direct-import users must migrate the four old module
paths using the table above; no forwarding modules or aliases are introduced. The ledger uses
declaration names and contains no affected module/path references, so no ledger edit is needed.

Validation logs are in `/tmp/nlalib-regression-checks`: the full two-thread build of NLAlib and
NLAlibScaffold passed (3871 jobs, no warnings); all four moved modules passed sequential
`lake lean ... -- -M 8000` checks; both root import-generation checks passed. The root audit
checked 7204 reachable declarations with zero violations; all lint checks passed; the duplicate
report found zero classes among 4586 library theorems. References, named-bound values and LaTeX
checks passed. The root checks cover the same gates as `stage_check.sh`, so a redundant second
build/audit/lint/duplicates run was omitted after the orchestrator's validation-efficiency review.
Fresh extraction `/tmp/nlalib-regression-explore.json` contains 299 modules and 3455
declarations. All four Regression module paths and source hashes match the checkout; the four
old module paths are absent. No commit was made by the implementation agent.

The Explorer also builds successfully against this fresh extraction with source-body fingerprint
validation enabled. Resolving extraction indices back to declaration names confirms unchanged
public names, all 28 rate mappings, seven shared guarantees and three collections. Source
navigation resolves the four new Regression modules. Independent implementation and report
reviews found no blocking issues.
