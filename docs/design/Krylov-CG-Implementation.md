# A concrete square-root-free conjugate gradient implementation

Design and implementation record, 2026-11-04. The existing `CGRun` is a conditional analysis
interface. The approved square-root-free program now has a complete exact execution proof in
`Krylov/LinearSystems/CGProgram.lean`, with its fixed target in `CGTargets.lean`. The earlier
development is preserved in `proposals/krylov/`; the library uses only the canonical library
modules. This note records the algorithm choice and the remaining rounded execution-to-run
construction. See [the integration record](Krylov-Implementation-Integration.md).

## Concrete algorithm and storage

Use the real Hestenes–Stiefel algorithm from zero, with the squared residual scalar cached.
The program performs no square root. Its physical residual vector is stored, and the exact
Euclidean norm in `CGRun.ρ` is an analysis quantity, never a computed instruction.

Declared buffers, all at one tag `p`, are:

| handle | length | initial contents | final role |
| --- | --- | --- | --- |
| 0 | N | right-hand-side words | preserved input |
| 1 | N | uninitialized | x |
| 2 | N | uninitialized | r |
| 3 | N | uninitialized | p |
| 4 | 1 | uninitialized | status |

The read-only data hold the N by N matrix, column-major at index i+N*j. The program loads
these entries into an allocated matrix buffer using `Stmt.rom`, then uses the existing
column-ordered `Computation.gemv`. There is no matrix oracle and no precomputed data hidden
in a matrix-free input. Two further allocations hold a product vector of length N and nine
scalar cells. The program is wrapped in `scope`, so all temporary storage is released.
No full trajectory is physically stored: the proof reconstructs the actual states at the
loop boundaries, and the truncated-budget executions agree with those same boundaries.

The nine scalar cells are old squared residual, next squared residual, curvature, step,
direction coefficient, negative step, zero, positive status word, and negative status word.
The curvature cell is reused as the scalar product scratch during the direction update.

Initialization, in order: load the matrix; create zero and positive status words; negate the
positive word; set status to zero; set x to zero; copy b into r and p; compute dot(r,r) into
the cached scalar; test that scalar for zero and set converged status if zero.

Each of the q loop iterations first tests whether status is zero. An active iteration does:

1. `gemv`: s := A*p, in the existing kernel's fixed column order.
2. `dot`: mu := dot(p,s), accumulated in increasing component order.
3. Test whether mu is strictly positive. If not, set negative status and perform no division.
4. gamma := oldnu/mu, one scalar division.
5. `axpy`: x := gamma*p+x.
6. Negate gamma exactly and `axpy`: r := (-gamma)*s+r.
7. `dot`: nextnu := dot(r,r).
8. delta := nextnu/oldnu, one scalar division before oldnu is overwritten.
9. For each component i in increasing order, perform exactly
   scratch := delta*p[i], followed by p[i] := r[i]+scratch. This is the standard two-operation
   direction update, preserving r; there is no multiplication by a literal one.
10. Copy nextnu into oldnu. Test it for zero and set converged status if zero.

The next residual, direction, and iterate are all written even when nextnu is zero. Thus a
terminal zero residual is represented exactly as permitted by `CGRun`. No subsequent active
step is taken. Under a relative-error contract the positive status literal need not decode
exactly to one; its decoding is positive when u<1. The negative status word is its exact
negation. Status zero therefore means budget exhausted with no stop, positive means zero
residual termination, and negative means nonpositive curvature. Under exact arithmetic these
values are 0, 1 and -1. `exec = none` remains a failed execution; it is never identified with
convergence or a zero residual.

## Numerical bridge and its input-only hypotheses

For N>=1, use the explicit implementation accuracy

```lean
noncomputable irreducible_def cgImplementationRoundoffBound (N : ℕ) (u : ℝ) : ℝ :=
  4 * (N : ℝ) ^ 2 * u
```

The existing numerical-bound vocabulary will gain this scalar bound only when the proposal
is approved for the library; it needs a constants registry entry and positivity/comparison API
then. No registry entry is introduced for an unapproved proposal.

For a constant unit roundoff u at the used tag, set epsilon=4*N^2*u, the proposed bound. The bridge consumes the
existing `IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem` and `AddsZeroExactly dec I.sem`.
The global range predicate is explicit: no overflow or underflow range claim is hidden.
The input matrix and right-hand side are the decodings of the actual ROM/input words.
The spectral and horizon hypotheses are exactly

```lean
(hN : 0 < N) (hq : 0 < q) (ha : 0 < a)
(hA : A.IsHermitian) (hs : spectrum ℝ A ⊆ Set.Icc a a')
(hsmall : (q : ℝ) ^ 2 * Real.sqrt q * (4 * (N : ℝ) ^ 2 * u) *
  (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
```

Nonnegative u follows from the existing contract. The nonempty spectrum gives kappa>=1,
so this window implies epsilon<=10^-5, N*u<1/2 and all local smallness restrictions. There
is no measured direction, residual, error, curvature, convergence, or `CGRun` premise.
Zero unit roundoff is included.

The kernel bounds yield:

* gemv: componentwise error at most gamma_N*abs(A)*abs(p), hence normwise error at most
  gamma_N*sqrt(N)*specNorm(A)*norm(p). Use
  `norm_toLp_map_abs_mulVec_abs_le`; gamma_N<=2*N*u and sqrt(N)<=N give the required epsilon.
* dot(r,r): absolute error at most gamma_N*norm(r)^2. Define theta by division when the
  residual is nonzero and theta=0 for zero residual; the same statement covers terminal zero.
* dot(p,s): absolute error at most gamma_N*norm(p)*norm(s), using Euclidean Cauchy–Schwarz.
  This is exactly `CGRun.μ_eq` and its error bound; the matrix-product error is not counted
  again in the curvature error.
* divisions: the existing scalar contract gives the relative errors e_gamma and e_delta,
  at most u<=epsilon.
* each iterate/residual/direction update: two rounded operations per component give
  gamma_2*(norm(y)+abs(alpha)*norm(x)), with gamma_2<=4*u<=epsilon. Negation is exact.

The original `CGRun` fields are filled with these actual decoded intermediate values and
the resulting defects. There is no separate arithmetic-run structure. Actual loop-boundary
states are retained in the proof, not supplied as desired-local-error hypotheses.

## Successful steps without circular assumptions

The program guard alone distinguishes a nonpositive curvature from a successful division;
the input-only bridge additionally proves this guard never rejects under the window above.
For the first step p=b, so a nonzero b gives a nonzero direction. The existing theorem
`dotProduct_add_pos_of_spectrum_subset_Icc` applies with the normwise product and dot defects
and 3*epsilon*a'<=a. A zero b takes the initial zero-residual branch and no division.

After m>=1 successful steps, construct `C : CGRun N m` from the already executed prefix,
including its terminal p_m and r_m. The existing a priori prefix bounds give
P=2*kappa and K=(21/20)*kappa. Apply `C.norm_r_le_two_mul_norm_p`, whose scalar condition
20*m*epsilon*(1+P+K)<=1 follows from the full q-window. If terminal residual is nonzero,
terminal direction is nonzero, and the same curvature theorem permits the next step.
Thus success is proved by prefix induction. No next-step positivity is used to construct
the previous prefix, and no physical-energy theorem is invoked until the run is constructed.

The conclusion distinguishes m=0, which is the initial zero-right-hand-side termination,
from m>0, which yields the existing run structure. A zero terminal residual is allowed.
The construction gives m<=q, positive/zero final status, and excludes negative status and
`exec = none` under these input-only assumptions. General guarded executions outside the
window may report negative status; no convergence claim is made for them.

## Planned Lean interfaces

The canonical builder and tree, in the proposal's `namespace NLAlib`, have these signatures:

```lean
def cgProg {P ι VB VI : Type} (tag : P) (N q : Computation.IExp VI)
    (b x r p status : VB) : Computation.Builder P ι VB VI Unit

def cgProg.compiled {P ι : Type} (tag : P) : Computation.Prog P ι 1 5
```

The exact guarded step body is inlined in `cgProg`; there is no second step program.
The matrix buffer and workspaces are allocated by this same canonical program.
The compiled tree is `(ProgFamily.compile ...).get rfl`, with N the oracle-dimension size
parameter (unused as an oracle) and q the sole additional size.

A small output-layout predicate may bundle three `HoldsDecoded` facts and the scalar status
read. Its raw constructor is those four facts; it contains no arithmetic equations or bounds.
In the proposal signatures below, writing these four facts directly avoids a new interface:

```lean
-- With C : CGRun N m and st' : Computation.St P K (Computation.OpCount P ι):
Computation.HoldsDecoded st'.store dec tag 1 0 (fun i (_ : Fin 1) => C.x m i)
Computation.HoldsDecoded st'.store dec tag 2 0 (fun i (_ : Fin 1) => C.r m i)
Computation.HoldsDecoded st'.store dec tag 3 0 (fun i (_ : Fin 1) => C.p m i)
```

The high-level theorem quantifies P, K, I, dec, tag, N, q, actual input words and decoded ROM
matrix before its hypotheses. It takes the existing contracts, exact declared-buffer shapes,
ROM/input decoding facts, and precisely the input window above, and concludes

```lean
∃ st' m, (cgProg.compiled tag).exec I N ![q] initial = some st' ∧ m ≤ q ∧
  ((m = 0 ∧ b = 0 ∧
      Computation.HoldsDecoded st'.store dec tag 1 0 (fun _ (_ : Fin 1) => 0) ∧
      Computation.HoldsDecoded st'.store dec tag 2 0 (fun _ (_ : Fin 1) => 0) ∧
      Computation.HoldsDecoded st'.store dec tag 3 0 (fun _ (_ : Fin 1) => 0) ∧
      ∃ w, st'.store.read tag 4 0 = some w ∧ 0 < dec tag w) ∨
   ∃ C : CGRun N m, C.A = A ∧ C.b = b ∧ C.ε = 4 * (N : ℝ) ^ 2 * u ∧
      Computation.HoldsDecoded st'.store dec tag 1 0 (fun i (_ : Fin 1) => C.x m i) ∧
      Computation.HoldsDecoded st'.store dec tag 2 0 (fun i (_ : Fin 1) => C.r m i) ∧
      Computation.HoldsDecoded st'.store dec tag 3 0 (fun i (_ : Fin 1) => C.p m i))
```

The full theorem additionally records the final status and, for each j<=m, the actual
truncated-budget program execution whose output holds `C.x j`, `C.r j` and `C.p j`.
The intended prefix induction must derive these executions rather than assume them. Once
that construction is proved, physical energy, delayed estimator and true-residual corollaries
can apply the existing `CGRun` theorems to the constructed C and rewrite the output-layout
facts. The m=0 output x=0 requires its own branch. These remain planned rounded results,
with their original finite-horizon hypotheses.

## Approved exact target, costs and output

The existing access models are exact-arithmetic models. The target is therefore the exact
execution/cost/output theorem for this same canonical tree; finite-precision bridges are
separate supporting theorems about it, with no `Result:` tags. Its name is
`StoredEntriesConjugateGradient`, with `storedEntriesConjugateGradient` its proof.

For arbitrary real ROM entries and b, the guards make the program succeed, with status in
{0,1,-1}. For SPD decoded ROM matrix A, outputs x,r,p equal `cgState A b 0 q`, including
padded states after exact zero termination. In particular x equals `cgIterate A b 0 q`.
Positive status occurs exactly when the final residual is zero, and negative status is
excluded on SPD input. No SPD assumption is hidden in the size validity predicate.

The target is `StoredEntries (𝕜 := ℝ) tag (cgProg.compiled tag)` with `valid := True`,
`X N _ := Fin N → ℝ`, b as the only initialized declared buffer, output buffers initially
uninitialized with the lengths in the storage table, ROM length N*N, and the postcondition
just described for `A i j := vals (i + N*j)`. It is now registered and proved in
`Krylov/LinearSystems/CGProgram.lean`.

The operation budget, an upper bound including early termination and curvature rejection, is:

| kind | count |
| --- | --- |
| ROM reads | N^2 |
| multiplication | N + q*(N^2+5*N) |
| addition | N + q*(N^2+5*N) |
| conjugation | N + 2*q*N |
| division | 2*q |
| negation | q+1 |
| literal | N+3+q*(N+2) |
| comparison | 1+3*q |
| copy | 2*N+2*q+2 |

All other counts are zero. The cell-memory budget is `2*N^2+5*N+11` at tag, zero at every
other tag. It includes N^2 read-only cells, N^2 loaded matrix cells, the four declared N-vectors,
product workspace N, declared status cell, nine scalar cells and at most one kernel scratch.
These approved formulas are proved unchanged. Any future change to the registered statement
requires a separate review; intermediate accounting may establish stronger inequalities.

## Reuse, files and review

Read `CONTRIBUTING.md` in full, `docs/rules/DIGEST.md`, Computation and Krylov `RULES.md`,
`docs/design/Computation.md`'s program/kernel/access-model material, and
`Krylov-FinitePrecision-Runs.md`. Searched pinned Mathlib for concrete CG or floating-point
execution models: none found. The existing `CGRun`, `CGRunModel`, `CGBackward`, `CGAccuracy`
and `CGEnergyEstimator` are reused; no second convergence analysis is proposed.

Reuse existing `IsRelErrSem.exec_dot_abs_sum_mul_sub_le`,
`IsRelErrSem.exec_dot_eq_sum_mul_one_add`, `IsRelErrSem.exec_axpy`,
`IsRelErrSem.exec_gemv_abs_mulVec_sub_le`, scalar contract success clauses, store frame lemmas,
`exists_exec_loop_eq_some_of_forall`, and the shared matrix norm comparisons. The generic
norm/sqrt work supplies `RelErr.norm_sub_le`; CG itself needs no sqrt wrapper.
Use `isRelErrSem_gridSem` and `addsZeroExactly_gridSem` as a concrete binary round-to-nearest,
unbounded-exponent arithmetic witness, without claiming an executable bit implementation or
IEEE handling of finite exponent range.

Files, after design review:

* `proposals/krylov/ConjugateGradient.lean`: canonical builder/tree, proposed exact target,
  exact execution proof and actual-execution-to-CGRun bridge. Split by topic into further
  proposal files if the 1000-line recommendation requires it; 1500 is a hard ceiling.
* This note: complete statement, proof plan, approval boundary and validation evidence.
* A generic normwise kernel helper needed by both CG and Lanczos is placed once in the
  existing topic for its subject, coordinated with the generic norm/sqrt owner and root;
  it introduces no new program or target.

Open review items: confirm the exact target postcondition/budgets and the output-layout
predicate choice. Recommendation: keep the stored-entries exact target and direct
`HoldsDecoded` conclusions, and prove the finite-precision bridge on the same compiled tree.
Builds are serialized with two Lean threads and logs. No code is written before this design
and its interfaces are reviewed; registration approval is requested only after a checked,
concrete proposal is available.

### Exact target signature submitted for review

The budget function has the proposed table as its `Finsupp.single` body:

```lean
noncomputable def cgCount {P ι : Type} (tag : P) (N q : ℕ) : Computation.OpCount P ι :=
  Finsupp.single (.rom tag) (N ^ 2) +
  Finsupp.single (.bin tag .mul) (N + q * (N ^ 2 + 5 * N)) +
  Finsupp.single (.bin tag .add) (N + q * (N ^ 2 + 5 * N)) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (2 * q) +
  Finsupp.single (.un tag .neg) (q + 1) +
  Finsupp.single (.lit tag) (N + 3 + q * (N + 2)) +
  Finsupp.single (.cmp tag) (1 + 3 * q) +
  Finsupp.single (.copy tag) (2 * N + 2 * q + 2)

def StoredEntriesConjugateGradient : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P),
    Computation.StoredEntries (𝕜 := ℝ) tag (cgProg.compiled (ι := ι) tag)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N _ b => ![(Array.ofFn b).map some, Array.replicate N none,
        Array.replicate N none, Array.replicate N none, Array.replicate 1 none])
      (fun N _ => N ^ 2) (fun N q => cgCount tag N (q 0))
      (fun N _ p => if p = tag then 2 * N ^ 2 + 5 * N + 11 else 0)
      (fun N q b vals _ st =>
        let A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j)
        ∃ status : ℝ, st.store.read tag 4 0 = some status ∧
          (status = 0 ∨ status = 1 ∨ status = -1) ∧
          Computation.Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
          (A.PosDef →
            Computation.Holds st.store tag 1 0
              (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).x i) ∧
            Computation.Holds st.store tag 2 0
              (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).r i) ∧
            Computation.Holds st.store tag 3 0
              (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).p i) ∧
            (status = 1 ↔ (cgState A b 0 (q 0)).r = 0) ∧ status ≠ -1))

theorem storedEntriesConjugateGradient : StoredEntriesConjugateGradient
```

This exact target received maintainer approval on 2026-11-04. Its status and output assertions
are entirely in the postcondition fixed by the target, not a prover-chosen postcondition.

### Generic execution bridge signature submitted for review

The following spells out the planned high-level statement. Here `initial` is a local `let`
abbreviation for the explicit five-buffer `inputState`, not a caller-supplied initial state.
`HoldsDecoded` matrices with a `Fin 1` column index represent the three stored vectors.

```lean
theorem exists_cgRun_exec_cgProg
    {P ι K : Type} [DecidableEq P] (I : Computation.Interp P ι K
      (Computation.OpCount P ι)) (tag : P) (dec : P → K → ℝ) (u : ℝ)
    (hsem : Computation.IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem)
    (hzero : Computation.AddsZeroExactly dec I.sem)
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (words : Fin N → K) (A : Matrix (Fin N) (Fin N) ℝ)
    (hrom : ∀ i j : Fin N, ∃ w,
      I.rom (i + N * j) = some w ∧ dec tag w = A i j)
    {a a' : ℝ} (ha : 0 < a) (hA : A.IsHermitian)
    (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (hsmall : (q : ℝ) ^ 2 * Real.sqrt q * (4 * (N : ℝ) ^ 2 * u) *
      (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    let b : Fin N → ℝ := fun i => dec tag (words i)
    let initial := Computation.inputState tag [(Array.ofFn words).map some,
      Array.replicate N none, Array.replicate N none,
      Array.replicate N none, Array.replicate 1 none]
    ∃ final m, (cgProg.compiled tag).exec I N ![q] initial = some final ∧ m ≤ q ∧
      ((m = 0 ∧ b = 0 ∧
        Computation.HoldsDecoded final.store dec tag 1 0 (fun _ (_ : Fin 1) => 0) ∧
        Computation.HoldsDecoded final.store dec tag 2 0 (fun _ (_ : Fin 1) => 0) ∧
        Computation.HoldsDecoded final.store dec tag 3 0 (fun _ (_ : Fin 1) => 0) ∧
        ∃ w, final.store.read tag 4 0 = some w ∧ 0 < dec tag w) ∨
      ∃ C : CGRun N m, C.A = A ∧ C.b = b ∧ C.ε = 4 * (N : ℝ) ^ 2 * u ∧
        Computation.HoldsDecoded final.store dec tag 1 0 (fun i (_ : Fin 1) => C.x m i) ∧
        Computation.HoldsDecoded final.store dec tag 2 0 (fun i (_ : Fin 1) => C.r m i) ∧
        Computation.HoldsDecoded final.store dec tag 3 0 (fun i (_ : Fin 1) => C.p m i) ∧
        (∀ j ≤ m, ∃ st,
          (cgProg.compiled tag).exec I N ![j] initial = some st ∧
          Computation.HoldsDecoded st.store dec tag 1 0 (fun i (_ : Fin 1) => C.x j i) ∧
          Computation.HoldsDecoded st.store dec tag 2 0 (fun i (_ : Fin 1) => C.r j i) ∧
          Computation.HoldsDecoded st.store dec tag 3 0 (fun i (_ : Fin 1) => C.p j i)))
```

The final checked version must also expose the status dichotomy described above. It may split
this long supporting conclusion into independently useful existence, output and prefix lemmas;
no local arithmetic hypotheses may be added in place of proving them from the actual program.


### Amendment: one canonical registered program

Integration review on 2026-11-04 confirmed that the step is inlined in `cgProg`. The checker
requires direct use of each top-level `...Prog` by a registered tree, so the proposal introduces
only `cgProg` and `cgProg.compiled`, with no separate `cgStepProg` declaration. This removes an
unnecessary second program rather than rename it or bypass its target obligation. The operation
order, storage, target and numerical interfaces above are unchanged. The current interface section contains only the resulting canonical program and tree.

## Exact implementation and remaining rounded work

The maintainer-approved `cgProg`, its symbolic compiled tree and
`StoredEntriesConjugateGradient` now live in the library. The complete proof is
`storedEntriesConjugateGradient` in `Krylov/LinearSystems/CGProgram.lean`. It includes ROM
loading, initialization, all guards, the full loop, scoped allocations and cleanup. For every
real matrix it preserves the input and returns a legal status; under positive definiteness
its x, r and p buffers equal `cgState A b 0 q`, including padding after zero termination.
All approved operation and memory bounds are proved unchanged.

Generic scalar/ROM execution and zero-fill/BLAS frames were extracted into the Computation
topic. CG direction, initialization, body, guard, loop and accounting proofs live beside the
concrete CG program. They use mathematical nonzero-direction and stopping lemmas rather
than assuming the desired execution result. See the
[integration record](Krylov-Implementation-Integration.md) for placement.

The rounded whole-program construction of `CGRun` remains open. The displayed high-level
rounded signature earlier in this design is a goal, not an available theorem. Proposal-only
work derives local phase error bounds from actual operations under the existing scalar
contract; whole rounded initialization, prefix composition and horizon guard guarantees
still require proof. Consequently the exact program theorem alone does not instantiate the
physical finite-precision energy or residual bounds at a whole rounded execution.

## Maintainer approval, 2026-11-04

The user approved the concrete `StoredEntriesConjugateGradient` and `StoredEntriesLanczos`
statements and their identified programs: “Approve both exact target statements.” The exact
CG statement, program, guards and budgets are fixed for the proof; registration is authorized
and the required exact proof is now complete. The rounded execution-to-run
bridge remains work in progress. This supersedes earlier references to awaiting approval of
these exact statements; it does not approve an unstated rounded target.

## Exact stopping and curvature API

To discharge the fixed program's guards, expose the existing nonzero-direction result as
`Matrix.PosDef.cgState_p_ne_zero` in `CGTridiagonal.lean`, reusing its existing proof rather
than reproving line search. Add `cgState_p_eq_zero_of_r_eq_zero` and
`cgState_succ_eq_of_r_eq_zero` in `CGRecurrence.lean`: for every matrix, zero residual implies
zero direction and a fixed whole recurrence state. These follow from the already specified
total step, and require no new arithmetic model or desired program-output assumption. They
justify skipping remaining iterations after the computed exact residual vanishes. No CG
specification definition changes; the target's mathematical output remains fixed.

The real scalarization `cgStep_eq` in `CGRecurrence.lean` rewrites the same specified step
using exact dot products for both squared residual norms and the curvature. Its output is
componentwise multiplication and addition in the program's order, with no assumptions on the
matrix or state and total real division. It uses the existing Euclidean norm-square identity
and real quadratic form, not a second CG recurrence.
