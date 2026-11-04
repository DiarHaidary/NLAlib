# A concrete square-root-free conjugate gradient implementation

Design proposal, 2026-11-04. The existing `CGRun` is an analysis interface. This work connects
one fixed program over the existing Computation DSL and scalar semantics to that interface.
Until the maintainer approves the exact target statement, the canonical program, its compiled
tree, proposed target, and proofs stay outside the library in
`proposals/krylov/ConjugateGradient.lean`. They are genuine DSL programs, not renamed programs
or a second bounded-error arithmetic interface. No target registry, approval, checks, pins or
allowlists change. No cost/output theorem carries a `Result:` id in this proposal.

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
These executions are consequences of the same prefix induction, not premises. Physical
energy, delayed estimator, and true-residual corollaries apply the existing `CGRun` theorems
to this constructed C and rewrite the output-layout facts. At m=0, output x=0 is handled
directly. All statements retain their original finite-horizon hypotheses.

## Proposed exact target, costs and output

The existing access models are exact-arithmetic models. The target is therefore the exact
execution/cost/output theorem for this same canonical tree; finite-precision bridges are
separate supporting theorems about it, with no `Result:` tags. Its proposed name is
`StoredEntriesConjugateGradient`, with `storedEntriesConjugateGradient` its proof.

For arbitrary real ROM entries and b, the guards make the program succeed, with status in
{0,1,-1}. For SPD decoded ROM matrix A, outputs x,r,p equal `cgState A b 0 q`, including
padded states after exact zero termination. In particular x equals `cgIterate A b 0 q`.
Positive status occurs exactly when the final residual is zero, and negative status is
excluded on SPD input. No SPD assumption is hidden in the size validity predicate.

The target is `StoredEntries (𝕜 := ℝ) tag (cgProg.compiled tag)` with `valid := True`,
`X N _ := Fin N → ℝ`, b as the only initialized declared buffer, output buffers initially
uninitialized with the lengths in the storage table, ROM length N*N, and the postcondition
just described for `A i j := vals (i + N*j)`. This is a concrete proposal for maintainer
review, not a registered target.

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
The proof may lower a budget if the exact accounting reaches a stronger bound; changes to
this proposed statement are recorded before approval.

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

This exact target is proposed for later maintainer approval. Its status and output assertions
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

## Implementation status before target registration

The integration review approved this design before implementation. The sole canonical
`cgProg`, its symbolic compiled tree, and the proposed `StoredEntriesConjugateGradient`
statement have been checked by Lean. The scalar lemmas bounding the dot/matvec and
vector-update rounding factors by `cgImplementationRoundoffBound` are proved in the proposal.
The input-buffer preservation assertion was added after independent target review; the
final target statement is rechecked before delivery.

Actual execution support is proved separately: `CGInitialization.lean` loads ROM words with
an exact count/state identity and cell frame; `CGDirectionUpdate.lean` proves execution of the
actual inline two-operation direction update, its count/state identity, cell frame, and
componentwise rounding traces. Generic dot, self-dot, axpy and gemv adapters are proved in
`NLAlib/Matrix/Computation/BLAS.lean`, retaining their actual execution and store witnesses.

The exact whole-program target is **not yet proved**. Initialization composition, the guarded
loop invariant, and the final exact-CG output/count/memory theorem remain. The rounded
whole-program construction of `CGRun` is also **not yet proved**; the displayed high-level
signature is a reviewed goal, not a declaration available for use. Consequently no existing
physical energy or residual theorem has yet been connected to the whole canonical program.
A compiled program definition, a well-typed target statement, and correct kernel bounds do
not establish those missing compositions. This proposal is not counted as completed
implementation coverage, and no target registry or approval file has been changed.

Files added during proof staging on 2026-11-04:

* `proposals/krylov/CGInitialization.lean`: actual ROM-loading execution proof.
* `proposals/krylov/CGDirectionUpdate.lean`: the actual inline direction-update loop proof,
  supplied by integration, with no separate program definition.

Both are supporting proposal files. Generic ROM/literal-loop support is intended for the
Computation execution topic if promoted after review. The direction-update proof belongs
with this concrete CG implementation. No duplicate arithmetic-run structure is introduced.


### Amendment: shared zero initialization

The CG exact initialization will reuse `LanczosImplementation.exec_forRange_zero` from the
shared proposal execution support. The CG-specific uncompiled literal-fill copy was removed;
`CGInitialization.lean` retains the generic ROM-loading execution. The exact specialization
of the shared direction-update execution lives beside the canonical program in
`ConjugateGradient.lean`. A future rounded initializer must derive its word
values from the existing scalar contract, rather than assume exact literals for an arbitrary
carrier.

## Maintainer approval, 2026-11-04

The user approved the concrete `StoredEntriesConjugateGradient` and `StoredEntriesLanczos`
statements and their identified programs: “Approve both exact target statements.” The exact
CG statement, program, guards and budgets are fixed for the proof; registration is authorized
once the required proof is complete. The whole-program proof and the rounded execution-to-run
bridge remain work in progress. This supersedes earlier references to awaiting approval of
these exact statements; it does not approve an unstated rounded target.
