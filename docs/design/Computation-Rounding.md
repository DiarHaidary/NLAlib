# Design note: rounding-error analysis of the BLAS kernels (standard model; bounded range designed)

**Status: implemented, 2026-10-28** (layer 1; layer 2, R6, is designed only). Branch
`design/fp-toolkit`, based on `main` at `c4ff3d9`; review fixes applied (§8). Every statement of
§2 is proved and lives at its `NLAlib/` home (§9); the scaffold is empty again. Decision sheet:
`FP-Toolkit.json`.

## Summary

Two layers of floating-point error analysis for the library's own kernels.

* **Layer 1, the standard model** (this round). Arithmetic has relative error at most $u$ and
  never under- or overflows ([Higham2002, §2.2], model (2.4); the existing contract
  `IsRelErrSem u dec safe sem` with `safe = fun _ _ => True`). We add the algebra of
  $\gamma_n = nu/(1-nu)$ and prove backward and forward error bounds for `dot`, `axpy`,
  `gemv`, `gemm` and a new kernel `trsvLower` (forward substitution), in the order of operations
  the programs actually execute.
* **Layer 2, a bounded exponent range** (designed here, not skeletoned). Overflow is the failure
  mode; gradual underflow adds an absolute error to multiplication and division only.

**Every headline theorem asserts that the run succeeds**, under hypotheses on the inputs alone
(in layer 1: $nu < 1$, the cells hold the data, no overlap, and for `trsvLower` a nonzero
stored diagonal), and bounds the decoded result. No theorem has the form "if the run returns
$z$ then $z$ is accurate".

**The one structural idea.** Each analysis has three parts, and only the last depends on the
error model:

1. a **run lemma**, proved once for *any* error relation: the run succeeds and its decoded
   intermediates form a **trace**, a real sequence in which each operation's result is related to
   the exact result on the previous values; success needs every operation on every *prefix* of a
   trace to be in range;
2. a **trace bound**, pure real analysis with Higham's $\theta_n$ algebra;
3. the **headline**: run lemma + trace bound. In layer 1 the range hypothesis of the run lemma
   is void. In layer 2 it is discharged from an explicit bound on the data, using the trace bound
   on prefixes (this is the induction the success clause forces: the intermediate values are
   computed values, bounded by the error analysis itself).

Layer 2 then reuses the run lemmas unchanged and the layer-1 trace bounds by pushing each
underflow error onto an operand (R6).

---

## 1. Decisions (recommendations; the sheet has the same ids)

### R1. $\gamma_n$: a plain definition, every lemma assumes $nu < 1$

`roundingFactor n u := n * u / (1 - n * u)`. Every lemma and headline carries `n * u < 1`
(a checkable hypothesis on sizes; for IEEE double it is $n < 2^{53}$).
* Alternative (b): a guarded definition (`if n * u < 1 then … else 0`). It hides the
  hypothesis in a junk value and the bound becomes false-looking ("error ≤ 0") outside the range.
* Alternative (c): value in `ℝ≥0∞` with $\top$ for $nu \ge 1$. Makes every bound total but forces
  `ENNReal` arithmetic into the trace proofs.

The name follows N11 (a multiplier in a bound ends in `Factor`); docstrings write $\gamma_n$. It
needs a `docs/constants.toml` entry when it moves into `NLAlib` (B1).

### R2. Placement: all in `NLAlib/Computation`, except the rounding grid

P9 sends general facts to ForMathlib. The $\gamma_n$ lemmas mention `roundingFactor`, an NLAlib
definition that would never join Mathlib, so they are NLAlib vocabulary and stay in
`NLAlib/Computation/Rounding.lean`. The floating-point grid and rounding to nearest of the
witness (R7) mention nothing of NLAlib and are upstream candidates, so they go to
`NLAlib/ForMathlib/Algebra/Order/Round.lean` (next to Mathlib's `round`); the witness semantics
itself goes to `NLAlib/Computation/Grid.lean`. The `trsvLower` kernel must go in `NLAlib/Computation/BLAS.lean` (E8: only
that BLAS file may build `named` nodes).

### R3. Contracts: keep `IsRelErrSem`; add the arithmetic part with an error relation

`IsRelErrSem` stays as it is: it is the readable layer-1 contract that users instantiate (exact
arithmetic, a format semantics) and that headlines quantify over. It is complemented by

```lean
structure IsArithErrSem (err : P → BinOp → ℝ → ℝ → Prop) (dec : P → K → ℝ)
    (safe : P → ℝ → Prop) (sem : ScalarSem P K) : Prop where
  bin_err : … sem.bin p b x y = some z → err p b (b.realOp (dec p x) (dec p y)) (dec p z)
  bin_ok  : … (b = .div → dec p y ≠ 0) → safe p (b.realOp …) → ∃ z, sem.bin p b x y = some z
  lit_zero : ∀ p, ∃ z, sem.lit p 0 = some z ∧ dec p z = 0
  neg, conj : exact and defined
```

with the projection `IsRelErrSem.isArithErrSem : IsRelErrSem u dec safe sem → IsArithErrSem
(fun p _ => RelErr (u p)) dec safe sem`. (`RelErr` is Prop-valued, hence UpperCamelCase, N1;
the review's M2 renamed it from `relErr`.) The run lemmas take `IsArithErrSem`, so the tedious part
(store reasoning through loops) is proved once for every error model. Only the clauses the
kernels use are in it; `sqrt`, comparisons and conversions join when `nrm2` or a branching kernel
is analysed.

Is `IsRelErrSem` right for layer 1? Yes, with two remarks. Its success clause is about the exact
result on *decoded* operands, which is what makes the trace formulation work. And it lacks one
fact the kernels need (R4).

### R4. Adding zero is exact

`dot`, `gemv` and `gemm` accumulate from a literal $0$, so the first addition is $0 + q_0$.
`IsRelErrSem` only says it is $q_0(1+\delta)$, which costs one extra factor: $\gamma_{n+1}$ instead
of Higham's $\gamma_n$. IEEE arithmetic, fixed point and exact arithmetic all have $0 + y = y$
exactly.
* **(a) Recommended**: a predicate `AddsZeroExactly dec sem` (skeleton), folded into
  `IsRelErrSem` as a field when this stage lands (one more line in `isRelErrSem_exactSem`; no
  other user constructs the structure). Constants are Higham's.
* (b) Keep the contract, state $\gamma_{n+1}$.

`AddsZeroExactly` is true of IEEE arithmetic only because every word is representable. It is
**false under flush-to-zero** ($0 + y$ with $y$ subnormal flushes to $0$; FTZ already violates
`bin_err` for addition), and false for any semantics whose words may be off the grid
($\mathrm{fl}(0 + y) = \mathrm{fl}(y) \ne y$). So alternative R6(c) (flush-to-zero) must also
drop `hz`, which costs the `dot` constants there one factor ($\gamma_{n+1}$). The trivial
semantics $x \oplus y = (x + y)(1 + u)$ meets `IsRelErrSem` but not `AddsZeroExactly`; the
witness of R7 meets both.
* (c) Change the kernels to start from the first product. Changes their counts, hence the
  registered targets' hashes (Hutch++ uses `dot`).

### R5. First round: `dot`, `axpy`, `gemv`, `gemm`, `trsvLower`; componentwise statements

* **Kernels.** The four existing ones that the library's programs use, plus a new
  `trsvLower`: $x_i \leftarrow (x_i - \sum_{j<i} t_{ij}x_j)/t_{ii}$ in place, row by row,
  subtracting term by term, which is exactly the order of [Higham2002, Lemma 8.4]. Its exact
  specification is part of the round. Deferred: `trsvUpper` (same proof, reversed indices),
  `scal`, `rscl` (one operation each), `nrm2` (needs `sqrt`).
* **Form.** The headline is the componentwise backward error (Higham's form: $\hat{s} =
  \sum x_iy_i(1+\eta_i)$, $\hat{\mathbf{y}} = (\mathbf{A}+\Delta\mathbf{A})\mathbf{x}$,
  $(\mathbf{T}+\Delta\mathbf{T})\hat{\mathbf{x}} = \mathbf{b}$, all with
  $\lvert\Delta\rvert \le \gamma_n\lvert\cdot\rvert$), plus the componentwise forward bound where it
  is the form users want (`dot`, `gemv`, `gemm`). Normwise corollaries are one-liners for
  later, once a consumer asks.
* **Order of summation.** No assumption: the programs fix it (left to right), and the theorems
  are about those programs. Other orders (pairwise, blocked) would be new kernels.
* **Statements over words.** Inputs are given as words decoding to reals (`HoldsDecoded`, the
  decoded form of `Holds`); the conclusion gives the final store as the input store with the
  output words written (so the frame is part of it) and the error of their decodings. Counts and
  memory are those of the exact specifications, carried over by
  `usage_eq_of_exec_eq_some_of_straightLine` (`NLAlibScaffold/Computation/Exec.lean`, stated now,
  review M3): for a straight-line statement (`Stmt.StraightLine`: no `ite`, no `whileFuel`),
  two successful runs under interpretations with the same charge and widths, over any two
  carriers, from states with the same usage (`St.usage`: tape positions, counts, current and peak
  memory) and store shape end with the same usage. The carriers may differ, so the exact
  specification over $\Bbbk$ gives the counts of a run over any word type; all five kernels are
  straight-line. With it a floating-point headline becomes a `RunsWithin` statement in one step.
* **Result ids.** A theorem that mentions a run is proof infrastructure unless it proves a
  registered target (E3), so the run-level theorems carry citations and no `Result:` id. The
  trace bounds and the $\gamma_n$ lemmas can carry ids. Floating-point targets (an access model
  quantified over every semantics meeting a contract) are a later decision, when a whole algorithm
  is analysed.

### R6. Layer 2: the bounded-range model (recommendation)

**The model.** A second instance of `IsArithErrSem`, one structure for formats with range:

```lean
-- err for the model with gradual underflow ([Higham2002, §2.1, (2.8)]; Demmel's model):
def RelAbsErr (u η : ℝ) (b : BinOp) (a z : ℝ) : Prop :=
  ∃ δ e, |δ| ≤ u ∧ |e| ≤ η ∧ (b = .add ∨ b = .sub → e = 0) ∧ z = a * (1 + δ) + e
structure IsFloatSem (u η Ω : P → ℝ) (dec) (sem) : Prop  -- name open
  -- arithmetic: RelAbsErr; success when |exact| ≤ Ω p (and divisor ≠ 0)
  -- literals, conversions: RelAbsErr (they can underflow); sqrt: relative only
  -- neg, conj, re, comparisons: exact; adding zero exact
```

* **Success means no overflow, invalid operation or division by zero.** The word semantics
  returns `none` exactly where IEEE 754 would raise one of those flags; underflow and inexact are
  not failures. A successful run therefore produces the same words as IEEE arithmetic with default
  (non-stop) exception handling, because no infinity or NaN is ever created. The theorems say
  "no overflow happens", which is stronger and checkable, rather than tracking $\pm\infty$ and
  NaN as values.
* **Underflow costs an absolute term, on multiplication and division only.** With gradual
  underflow an addition or subtraction whose result is subnormal is exact, so $e = 0$ there; a
  product or quotient has $\lvert e\rvert \le \eta$, half the subnormal spacing ($u\lambda$ with
  $\lambda$ the smallest positive normal number; check against (2.8)).
* **Reuse of layer 1.** The run lemmas are the same theorems (they are stated for any `err`).
  The trace bounds are reused by moving each absolute error onto an operand: $x_ky_k(1+\delta) + e
  = (x_ky_k + e')(1+\delta)$ with $\lvert e'\rvert \le \eta/(1-u)$, and additions are layer-1
  operations already. So a layer-2 dot trace of $(x, y)$ is a layer-1 trace of the products
  $x_ky_k + e'_k$, and the layer-1 lemma applies verbatim. Expected layer-2 headlines:
  * `dot`: if $nu < 1$ and $(1+\gamma_n)(\sum\lvert x_i\rvert\lvert y_i\rvert + n\eta) \le \Omega$,
    the run succeeds and
    $\lvert x^{\mathsf{T}}y - \hat{s}\rvert \le \gamma_n\sum\lvert x_i\rvert\lvert y_i\rvert +
    n(1+\gamma_n)\eta$;
  * `gemv`, `gemm`: the same per entry;
  * `trsvLower`: $(\mathbf{T}+\Delta\mathbf{T})\hat{\mathbf{x}} = \mathbf{b} + \Delta\mathbf{b}$
    with $\lvert\Delta\mathbf{T}\rvert \le \gamma_n\lvert\mathbf{T}\rvert$ and
    $\lvert\Delta b_i\rvert$ of order $(i + \lvert t_{ii}\rvert)\eta$; success under an explicit
    bound through the comparison matrix, $(1+\gamma_n)\bigl(\lvert\mathbf{b}\rvert +
    \lvert\mathbf{T}\rvert\,\mathbf{g}\bigr) \le \Omega$ with $\mathbf{g}$ a computable bound on
    $\lvert\hat{\mathbf{x}}\rvert$ from $M(\mathbf{T})^{-1}$ (the exact form to be worked out in the
    layer-2 note).
* **How success is proved.** The run lemma needs every operation on every trace prefix in range.
  The trace bound applies to prefixes too (a prefix is a trace of fewer terms), so it bounds every
  intermediate by the data; the hypothesis above makes that bound at most $\Omega$. This is the
  induction over the computed intermediates, done once inside the run lemma's quantifier.

**Alternatives.**
* (b) Generalise `IsRelErrSem` itself with an absolute term ($\eta = 0$ giving today's contract).
  One structure, but every existing statement changes shape and layer 1 carries an $\eta$ it never
  uses.
* (c) Flush-to-zero arithmetic: $e \ne 0$ for addition too. The same `IsArithErrSem` covers it;
  the reuse trick then needs the additions' errors pushed onto operands as well, which spoils the
  componentwise backward form. Recommended only as a later variant.
* (d) No contract: a specified IEEE format semantics analysed directly (Flocq style). Highest
  fidelity, but every analysis is per format and nothing is reused from layer 1.
* (e) Infinities and NaN as values, success meaning finite outputs. Matches IEEE literally, but an
  infinity can become finite again ($1/\infty = 0$), so error clauses would need exceptions; no
  analysis wants it.

### R7. A witness with $u > 0$: rounding to nearest on a grid (review M1)

Every headline assumes `IsRelErrSem u dec True sem` and `AddsZeroExactly dec sem`; the only
semantics in the repository meeting both had $u = 0$. The witness:

```lean
def Real.floatGrid (t : ℕ) : Set ℝ := {x | ∃ m e : ℤ, |m| < 2 ^ t ∧ x = m * (2 : ℝ) ^ e}
noncomputable def Real.roundNearest (t : ℕ) (x : ℝ) : ℝ :=
  round (x / (2 : ℝ) ^ (Int.log 2 |x| + 1 - t)) * (2 : ℝ) ^ (Int.log 2 |x| + 1 - t)
noncomputable def gridSem (t : P → ℕ) : ScalarSem P ℝ  -- exactSem on decodings, then round
theorem isRelErrSem_gridSem (t : P → ℕ) (ht : ∀ p, 0 < t p) :
    IsRelErrSem (fun p => (2⁻¹ : ℝ) ^ t p) (fun p => Real.roundNearest (t p))
      (fun _ _ => True) (gridSem t)
theorem addsZeroExactly_gridSem (t : P → ℕ) (ht : ∀ p, 0 < t p) :
    AddsZeroExactly (fun p => Real.roundNearest (t p)) (gridSem t)
```

* **Format.** Binary, $t_p$ significant bits at tag $p$, unbounded exponent, round to nearest
  with ties upward (Mathlib's `round`; any tie rule gives the same bound). Unit roundoff
  $u_p = 2^{-t_p}$, Higham's $u = \tfrac12\beta^{1-t}$ at $\beta = 2$ [Higham2002, Theorem 2.2].
  $t_p \ge 1$ is needed: for $t = 0$ the grid is $\{0\}$ and rounding is not idempotent.
* **Carrier and decoding.** `K = ℝ` and `dec p x := roundNearest (t p) x` (the review's
  recommended variant): every word decodes to a grid point, so $0 \oplus y$ decodes to
  $\mathrm{fl}(\mathrm{fl}(y)) = \mathrm{fl}(y)$, the decoding of $y$, with no hypothesis on the
  inputs. Each operation is `exactSem`'s on the decoded operands, rounded at its tag (a
  conversion at the target tag); comparisons exact on decodings. With different `t p` per tag it
  also witnesses mixed precision.
* **Proof.** `isRelErrSem_gridSem` and `addsZeroExactly_gridSem` are proved in the skeleton
  from three `sorry`'d grid facts: the error bound
  $\lvert x - \mathrm{fl}(x)\rvert \le 2^{-t}\lvert x\rvert$ (`Real.abs_sub_roundNearest_le`,
  the only real work, via `Int.zpow_log_le_self`, `Int.lt_zpow_succ_log_self` and
  `abs_sub_round`), `Real.roundNearest_mem_floatGrid` ($t \ge 1$) and
  `Real.roundNearest_eq_self_of_mem_floatGrid`. Mathlib has no rounding-to-grid theory to reuse:
  `Mathlib.Data.FP.Basic` is an experimental, theorem-free implementation; `round` and `Int.log`
  are the building blocks used. A bounded-exponent witness for layer 2 is the same semantics
  failing above $\Omega$.

---

## 2. Declarations (skeleton)

Difficulty: S small (≤ 20 lines), M medium (≤ 80), L large (split into lemmas).

### `NLAlibScaffold/Computation/Rounding.lean` → `NLAlib/Computation/Rounding.lean` (new)

| declaration | statement | source | est. |
|---|---|---|---|
| `roundingFactor n u` | $\gamma_n = nu/(1-nu)$ | [Higham2002, §3.1] | def |
| `RelErr u a z` | $z = a(1+\delta)$, $\lvert\delta\rvert \le u$ | (2.4) | def |
| `roundingFactor_zero`, `roundingFactor_nonneg`, `le_roundingFactor_one` | $\gamma_0 = 0$; $\gamma_n \ge 0$; $u \le \gamma_1$ | §3.1 | S |
| `roundingFactor_le_roundingFactor` | $k \le n \Rightarrow \gamma_k \le \gamma_n$ | §3.1 | S |
| `abs_prod_one_add_zpow_sub_one_le` | $\lvert\prod_{i\in s}(1+\delta_i)^{\pm1} - 1\rvert \le \gamma_{\lvert s\rvert}$ | Lemma 3.1 | M |
| `roundingFactor_add_add_mul_le` | $\gamma_k + \gamma_j + \gamma_k\gamma_j \le \gamma_{k+j}$ | Lemma 3.3 | S |
| `abs_one_add_mul_one_add_sub_one_le` | $(1+\theta_k)(1+\theta_j) = 1 + \theta_{k+j}$ | Lemma 3.3 | S |
| `abs_inv_one_add_sub_one_le` | $(1+\theta_j)^{-1} = 1 + \theta_{2j}$ | Lemma 3.3 (weaker form) | S |
| `mul_roundingFactor_le` | $i\gamma_k \le \gamma_{ik}$ | Lemma 3.3 | S |
| `roundingFactor_add_le` | $\gamma_k + u \le \gamma_{k+1}$ | Lemma 3.3 | S |

### `NLAlibScaffold/Computation/Contract.lean` → `NLAlib/Computation/Contract.lean` (additions)

| declaration | statement | est. |
|---|---|---|
| `IsArithErrSem err dec safe sem` | R3 | structure |
| `AddsZeroExactly dec sem` | $\mathrm{dec}(x) = 0 \Rightarrow \mathrm{dec}(x \oplus y) = \mathrm{dec}(y)$ (R4; becomes a field of `IsRelErrSem` under (a)) | def |
| `HoldsDecoded s dec p b off M` | buffer holds real $\mathbf{M}$ through `dec`; home `Exact.lean`, next to `Holds` | def |
| `IsRelErrSem.isArithErrSem` | the projection (needs `safe p 0`) | S |
| `IsRelErrSem.nonneg` | $0 \le u_p$ (so no headline assumes it) | S |
| `addsZeroExactly_exactSem` | exact arithmetic adds zero exactly | S |

### `NLAlibScaffold/ForMathlib/Algebra/Order/Round.lean` → `NLAlib/ForMathlib/Algebra/Order/Round.lean` (new)

| declaration | statement | source | est. |
|---|---|---|---|
| `Real.floatGrid t` | $\{m2^e : m, e \in \mathbb{Z},\ \lvert m\rvert < 2^t\}$ | | def |
| `Real.roundNearest t x` | round to nearest onto the grid, via `Int.log` and `round` | | def |
| `Real.abs_sub_roundNearest_le` | $\lvert x - \mathrm{fl}(x)\rvert \le 2^{-t}\lvert x\rvert$ | Thm 2.2 | M |
| `Real.roundNearest_mem_floatGrid` | $t \ge 1 \Rightarrow \mathrm{fl}(x) \in$ grid | | M |
| `Real.roundNearest_eq_self_of_mem_floatGrid` | $\mathrm{fl}$ fixes the grid | | S–M |
| `Real.neg_mem_floatGrid` | the grid is symmetric (proved) | | S |

### `NLAlibScaffold/Computation/Grid.lean` → `NLAlib/Computation/Grid.lean` (new)

| declaration | statement | source | est. |
|---|---|---|---|
| `gridSem t` | R7 | | def |
| `relErr_roundNearest` | $\mathrm{fl}(x) = x(1+\delta)$, $\lvert\delta\rvert \le 2^{-t}$ (proved) | Thm 2.2 | S |
| `isRelErrSem_gridSem` | the contract at $u_p = 2^{-t_p}$ (proved from the grid facts) | Thm 2.2, (2.4) | S |
| `addsZeroExactly_gridSem` | adds zero exactly (proved from the grid facts) | | S |

### `NLAlibScaffold/Computation/Exec.lean` → `NLAlib/Computation/Exec.lean` (additions)

| declaration | statement | est. |
|---|---|---|
| `Stmt.StraightLine` | no `ite`, no `whileFuel` | def |
| `St.usage` | `(pos, cnt, cur, peak, curW, peakW)` | def |
| `usage_eq_of_exec_eq_some_of_straightLine` | R5 "Statements over words" | M (induction over `Stmt`, `foldlM` for loops) |

### `NLAlibScaffold/Computation/BLAS.lean` → `NLAlib/Computation/BLAS.lean` (addition)

`trsvLower p n T tOff x xo`: the kernel (R5); a definition, no proof.

### `NLAlibScaffold/Computation/BLAS/Traces.lean` → `NLAlib/Computation/BLAS/Traces.lean` (new)

| declaration | statement | source | est. |
|---|---|---|---|
| `IsDotTrace err x y n s` | $s_0 = 0$; $s_{k+1} \sim s_k + q_k$, $q_k \sim x_ky_k$; $s_{k+1} = q_k$ if $s_k = 0$ | | def |
| `IsSubstRowTrace`, `IsSubstTrace` | forward substitution, row by row | | def |
| `IsDotTrace.exists_eq_sum_mul_one_add` | $s_n = \sum x_ky_k(1+\eta_k)$, $\lvert\eta_k\rvert\le\gamma_n$ | §3.1, (3.4) | M |
| `IsDotTrace.abs_sum_mul_sub_le` | $\lvert\sum x_ky_k - s_n\rvert \le \gamma_n\sum\lvert x_k\rvert\lvert y_k\rvert$ | §3.1, (3.5) | S |
| `exists_eq_mul_one_add_add_mul_one_add_of_relErr` | one `axpy` entry: $ax(1+\theta_2) + y(1+\delta)$ | (2.4) | S |
| `IsSubstTrace.exists_sum_add_mul_eq` | $\sum_{j\le i}(t_{ij}+\Delta t_{ij})\hat{x}_j = b_i$, $\lvert\Delta t_{ij}\rvert \le \gamma_n\lvert t_{ij}\rvert$ | Lemma 8.4, Thm 8.5 | M |

### `NLAlibScaffold/Computation/BLAS/RoundingErrors.lean` → `NLAlib/Computation/BLAS/RoundingErrors.lean` (new)

Run lemmas (any `err`; success under "every prefix in range"): `IsArithErrSem.exec_dot`,
`IsArithErrSem.exec_axpy`, `IsArithErrSem.exec_gemv`, `IsArithErrSem.exec_gemm` (M each; they
follow the loop invariants of `exec_dot`, `exec_axpy`, `exec_gemv`, `exec_gemm`, with words and
decodings in place of field values).

Headlines (standard model, `safe = True`, each asserts success):

| declaration | conclusion besides success and the written store | source |
|---|---|---|
| `IsRelErrSem.exec_dot_eq_sum_mul_one_add` | $\hat{s} = \sum x_iy_i(1+\eta_i)$, $\lvert\eta_i\rvert\le\gamma_n$ | §3.1, (3.4) |
| `IsRelErrSem.exec_dot_abs_sum_mul_sub_le` | $\lvert x^{\mathsf{T}}y - \hat{s}\rvert \le \gamma_n\lvert x\rvert^{\mathsf{T}}\lvert y\rvert$ | (3.5) |
| `IsRelErrSem.exec_axpy` | $\hat{y}_i = ax_i(1+\theta_i) + y_i(1+\delta_i)$, $\lvert\theta_i\rvert\le\gamma_2$, $\lvert\delta_i\rvert\le u$ | (2.4) |
| `IsRelErrSem.exec_gemv_eq_add_mulVec` | $\hat{\mathbf{y}} = (\mathbf{A}+\Delta\mathbf{A})\mathbf{x}$, $\lvert\Delta\mathbf{A}\rvert \le \gamma_n\lvert\mathbf{A}\rvert$ | §3.5, (3.11) |
| `IsRelErrSem.exec_gemv_abs_mulVec_sub_le` | $\lvert\mathbf{A}\mathbf{x} - \hat{\mathbf{y}}\rvert \le \gamma_n\lvert\mathbf{A}\rvert\lvert\mathbf{x}\rvert$ | (3.12) |
| `IsRelErrSem.exec_gemm_abs_mul_sub_le` | $\lvert\mathbf{A}\mathbf{B} - \hat{\mathbf{C}}\rvert \le \gamma_n\lvert\mathbf{A}\rvert\lvert\mathbf{B}\rvert$ | §3.5, (3.13) |

Each is a few lines: the projection R3, the run lemma with its range hypothesis void, the trace
bound (S each).

### `NLAlibScaffold/Computation/BLAS/Triangular.lean` → `NLAlib/Computation/BLAS/Triangular.lean` (new)

| declaration | statement | source | est. |
|---|---|---|---|
| `exec_trsvLower` | exact arithmetic (only the lower triangle of $\mathbf{T}$ need be stored): writes $\mathbf{T}^{-1}\mathbf{b}$, counts $n(n-1)/2$ mul and sub, $n$ div, peak $+1$ | [GolubVanLoan2013, §3.1] | M–L |
| `IsArithErrSem.exec_trsvLower` | run lemma; nonzero diagonal and every prefix in range give success and a trace | Lemma 8.4 | M |
| `IsRelErrSem.exec_trsvLower_add_mulVec_eq` | lower triangle stored; success if the stored diagonal is nonzero; $(\mathbf{T}+\Delta\mathbf{T})\hat{\mathbf{x}} = \mathbf{b}$, $\lvert\Delta\mathbf{T}\rvert\le\gamma_n\lvert\mathbf{T}\rvert$ | Thm 8.5 | S |

Lower triangularity is Mathlib's `M.BlockTriangular OrderDual.toDual`, as in
`Matrix.det_of_lowerTriangular`; nothing new.

**§5.3 rows to add:** `roundingFactor`, `RelErr`, `IsArithErrSem`, `AddsZeroExactly`,
`HoldsDecoded`, `IsDotTrace`, `IsSubstRowTrace`, `IsSubstTrace`, `trsvLower`, `gridSem`,
`Stmt.StraightLine`, `St.usage`, each "none; Mathlib has no floating-point model" (searched:
Mathlib has no rounding model or $\gamma_n$; `Mathlib.Data.FP` is an experimental implementation
without theorems). `Real.floatGrid` and `Real.roundNearest` are ForMathlib upstream candidates.

## 3. Dependency order

1. `Rounding.lean`, the grid facts of `ForMathlib/Algebra/Order/Round.lean`, and the
   `Exec.lean` additions (independent of each other and of the rest; can be dispatched at once).
2. `Contract.lean` additions (independent of 1 except `RelErr`).
3. `Traces.lean` trace bounds (need 1).
4. `trsvLower` into `BLAS.lean`, then `exec_trsvLower` (independent of 1–3).
5. Run lemmas (need 2; independent of 3).
6. Headlines (need 3 and 5).

## 4. Wiring

The skeleton is in `NLAlibScaffold/` under the paths above and is not imported by `NLAlib.lean`
(it has `sorry`). When a declaration is proved it moves to its `NLAlib/` home in the same PR;
`trsvLower` and the `Contract.lean` additions move into the existing files, the three new files
are added to `NLAlib.lean` by `lake exe mk_all` (as are `Grid.lean` and the ForMathlib file). Under R4 (a), `AddsZeroExactly` becomes the field
`add_zero` of `IsRelErrSem` and the `hz` hypotheses disappear from the headlines.

## 5. Deferred

* Layer 2 (R6): its own short note and skeleton once R6 is decided.
* `trsvUpper`, `scal`, `rscl`, `nrm2` (with `sqrt_err`), and normwise corollaries.
* Complex data (Higham's $\tilde{\gamma}_n$ for complex arithmetic, Lemma 3.5): decodings are real
  today; generalising `dec` to $\Bbbk$ is a pending maintainer decision (§8, finding 4).
* Oracles and draws have no finite-precision contract: `IsArithErrSem` and `IsRelErrSem` cover
  scalar operations only. A whole-algorithm analysis needs an accuracy and success clause for the
  matvec oracle (e.g. backward: the decoded $\hat{\mathbf{y}} = (\mathbf{A} + \Delta\mathbf{A})
  \mathbf{x}$, $\lvert\Delta\mathbf{A}\rvert \le \varepsilon\lvert\mathbf{A}\rvert$) and the law
  of the decoded draws; whether headlines then quantify over (semantics, oracle) pairs meeting
  two contracts or over one bundled `Interp` contract is decided with the first such analysis.
* Forward error of triangular solve through condition numbers ([Higham2002, §8.2]).
* Whole-algorithm analyses (Hutch++, Lanczos in floating point) and their targets.
* Mixed precision through `convert`, stochastic rounding.

## 6. Source check (Higham 2002, 2nd ed.)

Confident: model (2.4) and Theorem 2.2 (§2.2); Lemma 3.1; Lemma 3.3 (the rules
$(1+\theta_k)(1+\theta_j) = 1+\theta_{k+j}$, $i\gamma_k \le \gamma_{ik}$, $\gamma_k + u \le
\gamma_{k+1}$, $\gamma_k + \gamma_j + \gamma_k\gamma_j \le \gamma_{k+j}$); Lemma 8.4 and
Theorem 8.5 (substitution, $\lvert\Delta\mathbf{T}\rvert \le \gamma_n\lvert\mathbf{T}\rvert$).
**To check against the book:** the equation numbers (3.4)/(3.5) for the inner product and
(3.11)–(3.13) for matrix-vector and matrix-matrix products; the exact form of the ratio rule in
Lemma 3.3 (stated here only in the weaker form that needs no product structure); the underflow
model (2.8) of §2.1 and its bound on $\eta$ ($\lambda$ or $u\lambda$, and whether $\delta\eta = 0$
is stated); the section of [Demmel1997] with the underflow model.

## 7. Open questions

The decisions R1, R3/R6, R4, R5 and the IEEE success convention are on the sheet, each with a
recommendation. One more, not on the sheet: should the trace bounds and the $\gamma_n$ lemmas get
`Result:` ids now (recommended: only the trace bounds for `dot` and substitution, the two a reader
would look up)?

## 8. Review (Fable checkpoint, 2026-10-28) and dispositions

Verdict: accept with changes (`reports/FP-Rounding-Review.md` in the harness). Each finding and
what was done:

| # | finding | disposition |
|---|---|---|
| 1 (M1) | no semantics with $u > 0$ meets `IsRelErrSem` and `AddsZeroExactly` together | **fixed**: R7, `gridSem` with `dec := roundNearest`, $u_p = 2^{-t_p}$, $t_p \ge 1$; both theorems proved from three grid facts (`sorry`). Grid in ForMathlib (P9), not in `Grid.lean` as the review placed it. FTZ remark added to R4 and to the `AddsZeroExactly` docstring |
| 2 (M2) | `relErr` is Prop-valued | **fixed**: `RelErr`, and `RelAbsErr` in R6; theorem names keep the token `relErr` (`…_of_relErr`), as Mathlib lowers `IsFoo` to `isFoo` in names |
| 3 (M3) | no lemma that straight-line counts do not depend on the semantics | **fixed** (statement; proof `sorry`): `Stmt.StraightLine`, `St.usage`, `usage_eq_of_exec_eq_some_of_straightLine`. Generalised over two carriers and two start states (same usage and store shape), since the exact specifications are over $\Bbbk$ and the floating ones over any `K`; named after its conclusion (N2) rather than the review's `exec_eq_of_straightLine_of_sem`, whose conclusion is not an `exec` equation. Lemmas that each kernel's `run` is straight-line: deferred to the proof of the first `RunsWithin` target |
| 4 (D) | decodings are real-only; complex formats need $\Bbbk$-valued `dec` | **maintainer decision** pending; not done. Statements keep `dec : P → K → ℝ` in one place each, `RelErr` and the traces take the field only through `ℝ`, and `gridSem` would stay the real instance, so the generalisation remains mechanical |
| 5 (W) | oracles and draws have no finite-precision contract | **deferred**; recorded in §5 |
| 6 (W) | `ScalarSem` cannot read the tape, so stochastic rounding is not modelable as `Computation.md` §7.5 says | **deferred** (the §7.5 correction belongs to that note) |
| 7 (W, cheap) | `trsvLower` headlines require the strictly upper part to be stored | **fixed**: `exec_trsvLower` and `IsRelErrSem.exec_trsvLower_add_mulVec_eq` take the lower triangle only, as the run lemma does |
| 8 (W) | equation numbers (3.4)/(3.5), (3.11)–(3.13), (2.8) unverified | **deferred** to before merging; §6 keeps them as "to check"; they must not reach `docs/constants.toml` |
| 9 (W) | `IsDotTrace` asks "adding zero is exact" at every step | **deferred** (kept; harmless now) |
| 10 (W) | `IsArithErrSem` will need `convert`, `sqrt`, other literals | **deferred**; when they join, each family gets its own relation (`errConvert p q`, `errSqrt p`), not `err p b` for a fictitious `BinOp` |
| 11 (W) | layer-2 preview | no action; noted that the grid witness extends to a bounded-exponent one (R7) |
| 12 (W) | conventions (docstrings, constants rows, `exec_axpy` name) | **deferred**; `IsRelErrSem.exec_axpy` may become `exec_axpy_eq_mul_one_add_add_mul_one_add` |

## 9. Integration (2026-10-28)

All of §2 moved to `NLAlib/` as §2 and §4 say: new files `Computation/Rounding.lean`,
`Computation/Grid.lean`, `Computation/BLAS/{Traces,RoundingErrors,Triangular}.lean` and
`ForMathlib/Algebra/Order/Round.lean`; additions to `Contract.lean` (`IsArithErrSem`,
`AddsZeroExactly`, `IsRelErrSem.isArithErrSem`, `IsRelErrSem.nonneg`, `addsZeroExactly_exactSem`),
`Exact.lean` (`HoldsDecoded`), `Exec.lean` (`Stmt.StraightLine`, `St.usage`,
`usage_eq_of_exec_eq_some_of_straightLine`) and `BLAS.lean` (`trsvLower`). Statements are those of
the skeleton. R4 was not changed: `AddsZeroExactly` stays a separate hypothesis (option (b)), so
the `hz` hypotheses remain in the headlines until the maintainer decides R4.

Clean-up while moving: the private copies of `BLAS.lean` helpers in the rounding files were
removed in favour of one public lemma each (`run_dot`, `run_axpy`, the new `run_trsvLower`,
`Store.read_push_size_set!_zero`, `Store.BlockFrame.congr`, and the ForMathlib
`Option.exists_map_eq_some_of_exists`); `Real.roundNearest_roundNearest` (rounding is idempotent)
replaces two local copies in `Grid.lean`; a local `Function.update` lemma is Mathlib's
`Function.comp_update`.

Registered: `NLAlib.Computation.roundingFactor` in `docs/constants.toml` (value $nu/(1 - nu)$;
`scripts/check_constants.py` now finds a constant in a sub-namespace by its last name component);
§5.3 rows. `Result:` ids (§7: the trace bounds a reader looks up, and the grid witness as the
analogue of `isRelErrSem_exactSem`): `inner-product-backward-error`,
`inner-product-forward-error`, `forward-substitution-backward-error`,
`computation-grid-meets-contract`. The kernel headlines (`IsRelErrSem.exec_*`) state runs, so by
E3 they get an id only as proofs of registered targets; none is registered.

**Still unverified against the book** (§6): the equation numbers (3.4), (3.5) (inner product) and
(3.11), (3.12), (3.13) (matrix-vector and matrix-matrix products) cited in the docstrings of
`Traces.lean` and `RoundingErrors.lean`; the form of the ratio rule of Lemma 3.3; the citation
[GolubVanLoan2013, §3.1] for `exec_trsvLower`.
