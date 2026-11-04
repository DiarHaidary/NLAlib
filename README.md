# NLAlib

A Lean 4 / Mathlib library of the foundations of numerical linear algebra: matrix analysis and
perturbation theory, polynomial approximation, Krylov methods, probability and random matrices,
sketching, randomized least squares, low-rank approximation, trace estimation and lower bounds.
The aim is reusable statements that other people's proofs can cite, stated once, generally, in
Mathlib's style.

Website: https://nla-lib.org.

## Using

```
lake exe cache get
LEAN_NUM_THREADS=4 lake build NLAlib
```

Pinned: Lean `v4.33.1`, Mathlib `v4.33.1`.

## Contributing

[CONTRIBUTING.md](CONTRIBUTING.md) is the contributor guide: setup, layout and import rules,
names, statement conventions and vocabulary, docstrings and citations, the checks
(`bash scripts/stage_check.sh` before every PR), and how to build without exhausting memory.
AI agents also follow [AGENTS.md](AGENTS.md).

## License

Apache License 2.0, see [LICENSE](LICENSE). Material taken from elsewhere keeps its original
attribution in the file header.
