# NLA-lib

NLA-lib is an open source Lean 4 library covering numerical linear algebra, built on Mathlib.
It aims to serve as a foundation for the formalization of new and existing numerical linear algebra results, including research performed autonomously by agents.
This is a work in progress.

It covers matrix analysis, polynomial approximation, random matrices and concentration, Krylov methods, sketching, least squares, low-rank approximation, trace estimation, and lower bounds.
Everything reachable from `import NLAlib` is sorry-free and uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

- **Website:** [nla-lib.org](https://nla-lib.org)
- **Explorer:** [nla-lib.org/explore](https://nla-lib.org/explore/) lists the definitions and theorems, with their statements and sources.
- **Design:** [nla-lib.org/design](https://nla-lib.org/design/) explains how the library states results, from quantifiers and constants to programs and models of computation.

## Building

```
lake exe cache get
lake build NLAlib
```

Lean and Mathlib are pinned to `v4.33.1` in `lean-toolchain`, and `elan` installs the toolchain.

## Contributing

If you are interested in getting involved, email [tyler.chen@nyu.edu](mailto:tyler.chen@nyu.edu) or open an issue or pull request.
[CONTRIBUTING.md](CONTRIBUTING.md) is the contributor guide: the ground rules and the checks to run before a pull request, with topic guides in [`docs/contributing/`](docs/contributing/) for layout, names, statements, vocabulary, programs, docstrings, proofs and design notes.
AI agents also follow [AGENTS.md](AGENTS.md).

## License

Apache License 2.0, see [LICENSE](LICENSE).
Material taken from elsewhere keeps its original attribution in the file header.
