# Designing new material

Part of the [contributor guide](../../CONTRIBUTING.md).

New material of any size (a new topic, a new interface, a new layer, or a batch of results that
will be built on) starts with a design note, `docs/design/<Topic>.md`, reviewed before the proofs
are written. It answers, with specifics:

1. **Objects.** Which definitions it introduces, each as a [vocabulary](vocabulary.md) row with its Mathlib bridge, and
   which Mathlib objects it uses directly instead.
2. **Interfaces.** Which hypothesis predicates and structures ([statements](statements.md) §3) it introduces or extends,
   what each bundles, and the raw-condition constructor for each.
3. **Statement shapes.** For each headline result, the exact Lean signature: field, index types,
   interfaces taken, conclusion form, constants handling ([statements](statements.md) §2), and the corollaries it will have.
   Written out, not described.
4. **Consumers.** For each interface and headline statement, which later topic or layer will use
   it and in what form; a statement with no foreseeable consumer is questioned.
5. **Files.** The file split, each file a topic ([ground rules](../../CONTRIBUTING.md#ground-rules) rule 8), with the declarations it will hold
   in order.
   **Placement.** Every new declaration, including each one added to a
   lower layer or to an existing file, goes where a user looking for its topic would find it,
   judged by what the statement is about, never by what its proof imports. The note lists every
   addition outside its own new files with its home and a one-line reason. A declaration placed
   anywhere else (for an import cycle, or a file that cannot yet import it) is flagged in the note
   with its intended home. Reviews check placement explicitly (review list: [P10]).
6. **Material.** Which sources and existing developments were read, what in them is reused (as
   mathematics to cover, as proof material), and what is deliberately not reproduced and why
   (twins, bundles, transport lemmas, local interfaces).
7. **Shared proof machinery** ([ground rules](../../CONTRIBUTING.md#ground-rules) rule 10). Which
   arguments several of the planned proofs will repeat: frame or footprint reasoning for programs,
   index and layout arithmetic, an estimate chain, a transport between two spellings. For each one,
   the note names the existing lemma, rule, tactic or interface that handles it, or plans it as its
   own declarations, proved before the results that use it. If most of a planned proof is such
   steps rather than mathematics, the note says what is missing, instead of planning to write it
   out by hand.
8. **Open questions** for the reviewers, with a recommendation each.

For each bridge and each API lemma that restates a Mathlib fact, the note names the Mathlib lemma
it found, or records "searched, none". An exact overlap ships as an `alias` or a one-line proof
citing the Mathlib lemma, never as an independent proof. A file added or split during the work is
added to the note's file list.

**Deviations from Mathlib are recorded.** Where Mathlib has a notion and the library states things
with another one (a different index type, a total function in place of one that takes a proof, a
named function in place of a scoped instance, a new predicate next to a Mathlib one), the design
note says so, and `docs/design/Mathlib-deviations.md` gets an entry in the same commit: what
Mathlib has, what the library does, why, what it costs, and the bridge lemma; an entry has the
fields Mathlib, NLAlib, Bridge, Why, Cost and Status [G1]. A deviation with no entry is a defect.

The note is reviewed as a design, with the question "will this be the interface people reach for
in five years?". The implementation PRs reference it. A divergence discovered during
implementation is a one-line amendment to the note, approved the same way.
