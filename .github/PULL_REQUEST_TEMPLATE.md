## What this adds

<!-- One topic per PR. Name the file(s) and the headline statements, and the design note if any. -->

## Read-back

<!-- For each headline theorem: what the Lean statement says, written from the Lean alone
     (hypotheses, conclusion, degenerate cases). A reviewer checks this against the source. -->

## Checklist

- [ ] `bash scripts/stage_check.sh` exits 0 (CONTRIBUTING §9)
- [ ] If `scripts/` changed: `python3 -m unittest discover -s scripts -p 'test_*.py'` and
      `node --test scripts/test_check_latex.mjs` pass
- [ ] Every public declaration has a docstring with source and label; new sources are in
      `docs/references.bib`; new named bounds are in `docs/constants.toml`
- [ ] No new allowlist entry or baseline rise, or it is listed here for the maintainer
- [ ] A new program's target is proposed here (only the maintainer registers targets)
