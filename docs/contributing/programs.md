# Programs

Part of the [contributor guide](../../CONTRIBUTING.md).

Algorithms analysed for their cost are programs over memory buffers (`NLAlib/Computation`,
`docs/design/Computation.md`). A program `<spec>Prog` is written with the builder in its topic
file, next to its specification, and compiled once, at symbolic sizes, into one first-order tree
for all sizes, `<spec>Prog.compiled : Computation.Prog P ι r b` (a registered tree).

A program reaches its matrix only through oracles, and may call black-box kernels
(`Computation.Stmt.kcall`, `docs/design/Computation-DynamicPrograms.md`). A finite-precision
result about a program assumes contracts of what it calls: of the arithmetic
(`Computation.IsRelErrSem`), of an oracle (`Computation.IsMatvecErr`), of a kernel
(`Computation.IsMatMulErr`, `Computation.IsQRErr`). A routine used inside a larger one is
certified once, by a theorem concluding its certificate (`Computation.IsMatvecRoutine`,
`Computation.IsOrthRoutine`, `Computation.ImplementsKernel`), and the larger analysis takes the
certificate as a hypothesis.

Results may be proved autonomously, so the statement of a published cost result is the
library's, not the prover's: it is a **target**.

- A target is a library definition of type `Prop`, written and reviewed by the library, in a
  file of its own, `<Topic>/<Spec>Targets.lean`, and registered in `docs/targets.toml`. It states
  an access model about a registered tree: `Computation.MatrixFree`, `Computation.MatrixFreeProb`
  or `Computation.StoredEntries`, which bind the program before the sizes and quantify over the
  matrix, the tape and the declared inputs afterwards, so the counts and the memory are functions
  of the sizes by the statement itself. Its name is the model, then the specification
  (`MatrixFreeHutchpp`).
- A result is `theorem matrixFreeHutchpp : MatrixFreeHutchpp`: its type is the target constant,
  with no hypothesis, parameter or postcondition of the prover's, and each registered target has
  exactly one such proof. A `Result:` theorem whose statement reaches a run or a budget proves a
  registered target; a lemma about a program family is proof infrastructure and has no result id
  [E3].
- The registry records each target's closure hash (every library constant its statement reaches,
  proofs erased and hygienic names numbered, the registered trees as leaves hashed by their
  constructor normal forms, which the kernel checks are the trees), its printed statement, each
  tree's printed normal form, the toolchain, the Mathlib revision and the SHA-256 of
  `lake-manifest.json` and `lakefile.toml`; `docs/targets.approved` holds the registry's SHA-256. A
  change of a target, of a definition it unfolds to, or of a tree changes a hash and needs a
  maintainer's approval: they review the diff that `TARGETS_UPDATE=1 lake env lean
  scripts/Targets.lean` writes and approve it with `sha256sum docs/targets.toml >
  docs/targets.approved`. A declared input computed from the sizes carries the registry flag
  `precomputed` and a `Precomputed:` docstring sentence [E3].
- Every `<spec>Prog` has a registered tree, named by a registered target, whose definition calls
  it [E4]. This is completeness, not soundness. So a new program lands in `NLAlib` together with
  its registered target, and only a maintainer registers targets: a PR that needs one proposes the
  target statement in its description. `docs/targets.toml` is the list of current targets.
- What the models prove and what they trust is listed in `docs/design/Computation.md`,
  "Guarantees: what is proved and what is trusted". A reader of a target
  still reads its size condition, its declared inputs, its postcondition and its bound: the model
  guarantees that the program meets exactly that statement, not that the statement is the
  interesting one.

The other rules are hygiene: the guarantees do not rest on them.

- Programs, kernels, implementations and compiled trees are computable: not `noncomputable`,
  `partial`, `opaque` or `unsafe`, and they run no code other than their definition (no
  implemented-by attribute) [E2]. It matters for the emitter and the `Float` runner.
- An `alloc` is live for the rest of the enclosing block, so a program that another program calls
  wraps its allocations in `scope` (a kernel is closed by its `named` node) [E9]. An open `alloc`
  is still counted, in the target's `mem`, so the rule is a warning: it keeps the peak the author
  intends.
- Only `NLAlib/Computation` defines a value semantics (`Computation.ScalarSem`) or an
  interpretation (`Computation.Interp`), each with its certificate [E6].
- `Stmt.named`, which the NumPy emitter prints as a call into its prelude, is constructed only in
  the BLAS and implementation files; a theorem may mention it [E8].

A builder need not be generic in its variable sorts: the theorem is about the compiled tree, and
a handle forged from a number does not compile. `scripts/Targets.lean` checks E3 and
`scripts/Programs.lean` checks E2, E4 and E9, each against fixtures of the ways a proof or a
program could cheat (an axiom of a target's type, a vacuous hypothesis, a claim wrapped in a
structure, an edit that must change a hash, a forged handle, a callee with an open `alloc`, …;
each script lists its fixtures). `scripts/AccessModelFixtures.lean` proves that the model forms
of known cheating programs are false. `scripts/check_rules.py` checks E5, E6 and E8. The tools
library `NLAlibTools` ([proofs](proofs.md)) is not part of the library and is not held to its rules.
