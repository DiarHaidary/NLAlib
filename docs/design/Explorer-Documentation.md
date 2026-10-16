# Explorer documentation and presentation

Approved scope, 2026-10-16: documentation and explorer presentation only. No new mathematics,
statements, proofs, or enduring mathematical interfaces. The approved audit distinguishes named
numerical bounds used as implementation support from concepts a reader browses, and pairs
asymptotic readings with their explicit mathematical statements.

## Independent changes

The library metadata wrapper stamps all declaration names registered in `docs/constants.toml`
with optional `explorerRole: "support"`; a registry `explorer_role = "concept"` override
retains headline presentation. It records `sourceHashes`, a map from every listed
module's relative source path to SHA-256 of its extraction-time bytes. Documentation fixes
remain independent of backend and frontend implementation and preserve theorem statements.

The explorer backend emits declaration `role` as `support`, `concept` for remaining definitions,
and `lemma` otherwise. Every declaration remains available for search, source navigation and
raw dependency inspection. Default graph nodes omit support definitions and collapse dependencies
through them; result grouping still takes precedence for a support declaration with a Result id.

`Asymptotic: Full.explicit.name`, with the name on the same or following line, is metadata,
removed from rendered prose. Its target must resolve; cycles fail. An asymptotic declaration
retains its own Result ids and inherits the target's ids, transitively. No declaration is deleted.
Each result supplies `overview` and `explicit` declaration indices and `forms`, containing all
`{overview: asymptoticIndex, explicit: targetIndex}` pairs. A default pair prefers a target matching
the previous primary explicit declaration, then source order. Without a pair both indices use
the original primary. A result's LaTeX override must never replace an asymptotic overview.

The frontend consumes these fields to offer overview and explicit readings, retain access to
all declarations and distinguish support from concepts. This is independently reviewable from
metadata extraction and documentation edits.

Before source body enrichment, the backend validates complete listed-module hash coverage,
relative safe paths, declaration module coverage, and every file's bytes under `--src`. Source
archives work without Git. Hash mismatches fail before slicing; legacy data without hashes
continues with a clear stderr warning and no body enrichment.

## Validation and read-back

Backend unit regressions cover inherited and retained Result ids, multiple pairs and deterministic
default selection, same/next-line metadata removal, unresolved targets and cycles, support graph
collapse with declarations retained, exact source hashes, incomplete coverage, unsafe paths,
mismatched source bytes and legacy fallback. Frontend and library metadata checks are recorded
in the integration report. No Lean build is required for backend-only changes; library docstring
checks remain part of the root integration checks.

## Implementation review

The user approved the audit and requested parallel agents. Backend, frontend and documentation
work were independent; all Lean edits are comments. Available `gpt-6.1-sol` agents substituted
for the unavailable repository model aliases, with explicit model selection. Independent bounded
reviews covered the design/metadata contract, the backend and the frontend. Review caught and
fixed malformed metadata escaping validation, inherited asymptotic titles replacing established
result titles, and paired targets missing from an own-id result's formal-statement section.

Twenty-one library files received targeted documentation edits: standalone result tags, actual
navigation links, explicit independence/moment assumptions, a corrected boundary-integrability
claim, expanded numerical values in conclusions, and removal of development commentary. No new
declaration, mathematical interface, placement deviation or prototype port was introduced; the
port ledger therefore needs no new entries.

Read-back of the representative explorer page: truncated generalized Nyström first states that
absolute positive constants suffice with independent standard Gaussian range and co-range
sketches, positive sufficiently small epsilon, range size at least C k / epsilon and co-range
size at least C l / epsilon, to give expected squared Frobenius error at most (1 + epsilon)
times the optimal squared Frobenius error. Its explicit view states the matching theorem with
range size at least 6 k / epsilon, co-range size at least 8000 l / epsilon, and 0 < epsilon <= 1.
The other error bounds and all formal declarations remain accessible. `truncatedGNFactor` stays
public, directly addressable and searchable, under supporting API rather than a headline.

The explorer reserves scrollbar space so its collapsed catalogue has the main site's reading
column position. Browser measurements with ordinary desktop scrollbars matched the content
bounds at viewport widths 1280, 800 and 390 pixels. The configured column widths were already
equal; no typography or column-width redesign was required.

Deployment must extract both `NLAlib/` and `NLAlib.lean` from the source archive to validate the
complete source manifest. Merge the library changes before deploying the stricter explorer
parser. Uncommitted local previews use extraction-time source bytes; public source links still
point to the recorded Git commit until the changes are committed and extracted again.

Remaining provenance follow-up: the inverse-Wishart probe power moment and matrix mean need
verified citations covering their full statements. HMT Appendix A.8 covers a restricted exponent
range and Appendix A.5 gives a trace formula; neither was presented as an exact source for the
broader statements. This pass does not invent locators.

## Amendment: complete asymptotic result navigation (2026-10-16)

Fresh extraction found eleven asymptotic declarations whose explicit targets carried no Result
ids, so their overview/explicit pairs were absent from result navigation. Add standalone Result
tags to those eleven explicit sample-size theorems in the Gaussian, Haar, Rademacher,
sub-Gaussian, row-sampling, sampling-without-replacement and CountSketch modules. Existing ids
identify the corresponding Gaussian, Rademacher, sub-Gaussian and sparse embedding results.
Three new ids distinguish previously ungrouped results: `jl-haar`, `leverage-sampling-osi` and
`sampling-without-replacement-osi`. Injection results retain their distinction from two-sided
embedding results. All changes are documentation tags; theorem statements and proofs are
unchanged. The backend inherits these ids for each asymptotic overview from its explicit target.

The reference checker requires a Result tag on at least one member of every explicit/asymptotic
pair, so an ungrouped pair fails validation before extraction. Regression coverage checks both
untagged declarations fail and either tagged member suffices.


## Amendment: self-contained SRHT explicit readings (2026-10-16)

Expand the two SRHT-with-replacement sample-size docstrings to state their own hypotheses,
embedding or injection conclusions, current sample thresholds and flattened coherence values.
The injection form assumes nonempty sample and ambient types, and neither form imposes the
without-replacement restriction on the number of sampled rows. Preserve existing citations,
asymptotic links and Result ids. No theorem statements or proofs change.

## Final validation (2026-10-16)

- Both existing checkouts use `feat/explorer-docs`; the user requested separate local commits
  after validation. No new worktree, push or deployment. The unrelated preexisting
  `docs/design/LowRank-S7.md` is untouched. An untracked
  `NLAlib/Sketching/Sparse/CountSketchEmbedding.lean` appeared during concurrent work after
  validation, with a refactor of `CountSketch.lean` and its constant-registry path. That refactor
  is preserved in the working tree, excluded from this commit and not covered by these checks;
  the commit uses the validated CountSketch source and registry path.
- Full `NLAlib NLAlibScaffold` build: 3860 jobs, zero warnings. Every edited Lean file passed
  `lake lean ... -- -M 8000`; final metadata/SRHT amendments were rebuilt and rechecked.
  All 21 edited Lean files have identical code outside comments compared with the branch base.
- Both root-module checks passed. Axiom audit: 6980 declarations, zero violations. Environment
  lint: 14 linters, 4885 declarations plus 2095 generated, zero errors. Duplicate report:
  4490 theorems, zero duplicate classes. Subsequent amendments changed only comments and tags.
- Documentation validation: 55 bibliography keys, 28 asymptotic forms, 24 registered bounds,
  5324 docstrings, 231 value markers on 227 spans, and 16980 mathematical spans; zero problems.
  Eleven library metadata tests and eight explorer backend tests pass; JavaScript syntax and
  both repositories' whitespace checks pass. CI runs the regression suites.
- Fresh extraction: 288 modules, 3373 public declarations. Archive-source validation succeeds,
  including `NLAlib.lean`; 165 definitions receive their source bodies. Generated site:
  287 topic modules, 239 result groups, 21 groups with all 28 asymptotic/explicit pairs and
  24 supporting bounds. Every asymptotic declaration belongs to a result group.
- Chrome checks exercised all 28 pairs in both views, variant selection, formal/source routes,
  exact-name search and direct navigation for `truncatedGNFactor`, absence of supporting bounds
  from headline catalogue/default graph, and mobile controls. No page errors or KaTeX errors
  occurred. Screenshots were inspected at desktop and mobile widths. Mathematical hypotheses
  remain in the selected statement; related Lean links and proof-witness constants stay below
  in the ordinary notes/reference sections.
- Logs and generated data: `/tmp/nlalib-explorer-checks/`, final amendments in its `final/`
  subdirectory; preview `/tmp/nlalib-explorer-preview/`. Width measurements:
  `/tmp/nlalib-width-classic.log`. The port ledger was reviewed and left unchanged: this is a
  documentation/presentation pass, with no new port or changed prototype disposition.
