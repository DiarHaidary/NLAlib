# Design note: the Lanczos program in finite precision, and the port of the stability analysis

2026-10-28. Branch `design/lanczos-fp` (from `design/fp-toolkit` @ 36bab62). Decision sheet:
`state/decisions/Lanczos-FP.json` in the harness (ids L1–L6 below).

## Summary

The maintainer's request: define the Lanczos algorithm fully as a program in the model of
computation, and plug in the analysis of *A simple stability analysis of Lanczos in finite
precision* (T. Chen; Lean at <https://github.com/tchen-research/simple-lanczos-stability>, 6.6k
lines, 0 `sorry`, Lean v4.32.2). That analysis assumes an inexact recurrence (the structure
`LanczosRun`: five local errors and nearly unit vectors, one accuracy parameter ε). This note
closes the gap: a **specific program**, its **exact specification** against `NLAlib.lanczosState`,
and a **bridge theorem**: in the standard model (`IsRelErrSem`, `AddsZeroExactly`) the run
*succeeds* and its outputs *are* a `LanczosRun` with

$$\varepsilon = \max\bigl(\varepsilon_{\mathrm{mv}},\ \gamma_{2N+6}(u)\bigr),\qquad
\varepsilon_{\mathrm{mv}} = \sqrt{N}\,\gamma_N(u)\ \text{(stored matrix, `gemv`)}\ \text{or the oracle's accuracy (matrix-free)},$$

about $N^{3/2}u$ for a stored matrix, $2Nu$ for an oracle accurate to $O(Nu)$. Every hypothesis is
on the data, the sizes and $u$: $\mathbf{H}$ symmetric, $\mathbf{b} \ne \mathbf{0}$, $q \ge 1$,
$(2N+6)u < 1$, $q\varepsilon \le 1/100$. Breakdown is handled inside the program (exact test
$\mathbf{z}^{\mathsf{T}}\mathbf{z} = 0$, never divides by zero); the number of steps covered,
$k$, is read off the outputs (first $j$ with $\beta_j = 0$, else $q$). Every `LanczosRun` field is
derivable; the one assumption the model cannot supply, the accuracy of a matrix-free oracle, is a
named contract (`IsMatvecErr`) discharged for the dense program. The analysis ports as about
5.5k lines (of 6.6k; the rest is replaced by library API), with its constants unchanged.

Skeleton (all typecheck with `lake env lean`; 3 files, 4 definitions + 1 structure, 6 `sorry`):
`NLAlibScaffold/Krylov/Processes/LanczosProgramTree.lean`,
`NLAlibScaffold/Krylov/Processes/LanczosRounding.lean`,
`NLAlibScaffold/Krylov/FinitePrecision/LanczosRun.lean`.

## 1. The program

### 1.1 Variant

Paige's A(1) ordering, the paper's Algorithm 1 and `NLAlib.lanczosStep`'s
(`lanczosAlpha A s = Re⟨q_j, A q_j − β_j q_{j−1}⟩`), so the exact specification needs no
Hermitian hypothesis and the floating run matches `LanczosRun` clause by clause. Step $j$
(1-based; program index $j-1$), all vectors in one slot `nxt` of length $N$:

| line | operation | kernel / instruction | `LanczosRun` clause |
|---|---|---|---|
| 1 | $\mathbf{u} \leftarrow \mathbf{H}\mathbf{v}_j$ | `apply o` (matrix-free) or `gemv` (dense) | `u_eq`, `norm_eu_le` |
| 2 | $t \leftarrow -\beta_{j-1}$ | `un .neg` (exact) | — |
| 3 | $\mathbf{w} \leftarrow t\,\mathbf{v}_{j-1} + \mathbf{u}$ | `axpy` | `w_eq`, `norm_ew_le` |
| 4 | $\alpha_j \leftarrow \mathbf{v}_j^{\mathsf{H}}\mathbf{w}$, `re`, copy out | `dot`, `un .re` (identity on reals) | `α_eq`, `abs_eα_le` |
| 5 | $\mathbf{z} \leftarrow (-\alpha_j)\mathbf{v}_j + \mathbf{w}$ | `un .neg`, `axpy` | `z_eq`, `norm_ez_le` |
| 6 | $s \leftarrow \mathbf{z}^{\mathsf{H}}\mathbf{z}$; $\beta_j \leftarrow \sqrt{s}$, copy out | `dot`, `un .sqrt` | `β_nonneg` |
| 7 | if $s \ne 0$: $\mathbf{v}_{j+1} \leftarrow \mathbf{z}/\beta_j$ | `cmp .eq` against literal 0, `rscl` ($n$ divisions) | `smul_v_eq`, `norm_δ_le`, near unit |

Start (`lanczosInit`): slot 2 $\leftarrow \mathbf{0}$ (literals), slot 0 $\leftarrow \mathbf{b}$
(`copyv`), $s \leftarrow \mathbf{b}^{\mathsf{H}}\mathbf{b}$ (`dot`), if $s \ne 0$:
$c \leftarrow \sqrt{s}$, slot 0 $\leftarrow \mathbf{b}/c$ (`rscl`); $\beta_0 \leftarrow 0$. Slots
rotate: `cur` $= j \bmod 3$, `prev` $= (j+2) \bmod 3$, `nxt` $= (j+1) \bmod 3$. Memory $3N + 4$.

The **2-norm** is `dot` then `sqrt` (no scaling, as `nrm2`; the standard model has no overflow).
**Normalisation is division** (`rscl`: $z_i/\beta$, one rounding), not multiplication by a computed
$1/\beta$ (two roundings): it gives $\lVert\boldsymbol\delta\rVert \le u\lVert\mathbf{z}\rVert$
exactly and keeps the program of `Computation.md` §5 unchanged (decision L4).

### 1.2 Lean shape (`LanczosProgramTree.lean`)

The body is the one designed in `Computation.md` §5 (D15), with two changes: the product is a
parameter `mv : VB → IExp VI → IExp VI → Builder …` so the matrix-free and dense programs share
one body and one proof, and the basis variant writes $q+1$ columns (Paige's theorem and the
backward model use $\mathbf{v}_{k+1}$).

```lean
def lanczosStepWith (mv) (p) (N) (W) (cur prev nxt) (s) (alphaCell betaCell) := do
  mv W cur nxt
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 1⟩);  axpy p ⟨s, 0⟩ W prev W nxt N
  dot p ⟨s, 0⟩ W cur W nxt N;  ins (.un p .re ⟨s, 0⟩ ⟨s, 0⟩);  ins (.copy p alphaCell ⟨s, 0⟩)
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 0⟩);  axpy p ⟨s, 0⟩ W cur W nxt N
  dot p ⟨s, 2⟩ W nxt W nxt N;  ins (.un p .sqrt ⟨s, 1⟩ ⟨s, 2⟩);  ins (.copy p betaCell ⟨s, 1⟩)
  ifThenElse p .eq ⟨s, 2⟩ ⟨s, 3⟩ (pure ()) (rscl p ⟨s, 1⟩ W nxt N)
def lanczosBasisProgWith (mv) (p) (N q) (b alpha beta Q) := …   -- init, q steps, copy v_{q+1}
def lanczosBasisProg (p) (o) := lanczosBasisProgWith (fun W src dst => stmt (.apply o p W dst W src 1)) p
def lanczosBasisDenseProg (p) (N q) (H …) := lanczosBasisProgWith (fun W src dst => gemv p N N H 0 W src W dst) p N q …
```

No `named`, no `noncomputable` (E2, E8); the file is a Krylov file (E5: it states its spec with
`lanczosState`). The name follows `HutchPlusPlusProgramTree.lean`. When the target is registered
(E3/E4) the program gets `lanczosBasisProg.compiled` and the statement becomes a `MatrixFree`
target with the counts of `Computation.md` §6 (plus $N(q+1)$ copies).

### 1.3 Exact specification

`NLAlib.exec_lanczosBasisProg_exactInterp`: under `exactInterp (fun _ => A)`, for every square
$\mathbf{A}$ over $\Bbbk$ and every $\mathbf{b}$, the run succeeds, `alpha[j]` $=$
`lanczosAlpha A (lanczosState A b j)`, `beta[j]` $=$ `(lanczosState A b (j+1)).beta`, `Q` holds
`lanczosMatrix A b (q+1)`. No symmetry or breakdown hypothesis: on breakdown the program leaves
$\mathbf{z} = \mathbf{0}$ in the slot, exactly the junk value $0^{-1}\cdot\mathbf{0}$ of
`lanczosStep`. This is the D15 statement (proof estimate ≈ 700 lines, loop invariant over the
three slots), stated with `exec`; the count/memory part is unchanged from D15.

## 2. The bridge theorem

### 2.1 Statement (`LanczosRounding.lean`)

```lean
theorem IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg (I) (p) (o)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (q) (H : Matrix (Fin N) (Fin N) ℝ) (hH : Hᵀ = H) (hmv : IsMatvecErr I o dec p H εmv)
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0) (hq : 0 < q)
    (hu : ((2 * N + 6 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) εmv ≤ 1 / 100) :
    ∃ st', exec I (lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run (inputState p […]) = some st' ∧
      ∃ α β V, (outputs decode to α, β, V) ∧ (c • V 0 = b + δ₀, 0 < c, ‖δ₀‖ ≤ u‖b‖) ∧
        (∀ j, lanczosSteps β q ≤ j → j < q → α j = 0 ∧ β j = 0) ∧
        ∃ L : LanczosRun N (lanczosSteps β q), L.H = H ∧ L.ε = lanczosRoundingEps N (u p) εmv ∧
          (∀ j < k, L.α (j+1) = α j ∧ L.β (j+1) = β j) ∧ ∀ j ≤ k, L.v (j+1) = V j
```

with `lanczosRoundingEps N u εmv = max εmv γ_{2N+6}(u)` and
`lanczosSteps β q = (first j < q with β j = 0) + 1`, else `q`. The dense twin
`exists_lanczosRun_of_lanczosBasisDenseProg` takes the $N^2$ words of $\mathbf{H}$ as buffer 0
(symmetric after decoding) instead of the oracle, with $\varepsilon_{\mathrm{mv}} = \sqrt{N}\gamma_N$:
all hypotheses are then on data, sizes and $u$. Composed with the analysis, every headline of the
paper becomes "the run succeeds and …" for the program (§3.4).

### 2.2 Clause by clause

Notation: $\gamma_m = mu/(1-mu)$ (`roundingFactor m u`); program step $j$ is `LanczosRun` index
$j+1$; vectors are the decodings of the slot contents (real, `dec`).

| clause | bound obtained | from | status |
|---|---|---|---|
| `u_eq`, `norm_eu_le` | matrix-free: $\varepsilon_{\mathrm{mv}}\lVert\mathbf{H}\rVert\lVert\mathbf{v}\rVert$; dense: $\lvert\mathbf{e}\rvert \le \gamma_N\lvert\mathbf{H}\rvert\lvert\mathbf{v}\rvert$, so $\lVert\mathbf{e}\rVert \le \sqrt{N}\gamma_N\lVert\mathbf{H}\rVert\lVert\mathbf{v}\rVert$ | `IsMatvecErr` (new contract) / `exec_gemv_abs_mulVec_sub_le` + **new** `norm_abs_mulVec_abs_le` (Cauchy–Schwarz by rows, `frobNorm_le_sqrt_rank_mul_specNorm`) | immediate / one new lemma (S) |
| `w_eq`, `norm_ew_le` | $w_i = -\beta v_i(1+\theta_i) + u_i(1+\delta_i)$, so $\lVert\mathbf{e}^w\rVert \le \gamma_2(\lVert\mathbf{u}\rVert + \lvert\beta\rvert\lVert\mathbf{v}_{j-1}\rVert)$ | `IsRelErrSem.exec_axpy` (negation exact) | immediate + normwise step (S) |
| `α_eq`, `abs_eα_le` | $\lvert e^\alpha\rvert \le \gamma_N\sum\lvert v_i\rvert\lvert w_i\rvert \le \gamma_N\lVert\mathbf{v}\rVert\lVert\mathbf{w}\rVert$; `re` exact | `exec_dot_abs_sum_mul_sub_le` + Cauchy–Schwarz | immediate |
| `z_eq`, `norm_ez_le` | $\gamma_2(\lVert\mathbf{w}\rVert + \lvert\alpha\rvert\lVert\mathbf{v}\rVert)$ | `exec_axpy` | immediate |
| `smul_v_eq`, `norm_δ_le` | $s \ne 0$: $\beta v'_i = z_i(1+\delta_i)$, $\lVert\boldsymbol\delta\rVert \le u\lVert\mathbf{z}\rVert$; $s = 0$: $\mathbf{z} = \mathbf{0}$ (below), $\beta = 0$, $\boldsymbol\delta = \mathbf{0}$ | **new** `IsRelErrSem.exec_rscl` | new kernel lemma (S) |
| `abs_norm_v_sq_sub_one_le`, `…_succ_…` | $\lVert\mathbf{v}'\rVert^2 = (1+\phi)/((1+\theta)(1+\sigma)^2)$, $\lvert\phi\rvert \le \gamma_2$, $\lvert\theta\rvert \le \gamma_N$, $\lvert\sigma\rvert \le u$, so $\le \gamma_{2N+6}$ | `exec_dot_eq_sum_mul_one_add`, `sqrt_err`, `exec_rscl`, **new** pure-real `abs_norm_sq_sub_one_le_of_relErr_normalize` (θ-algebra, `abs_inv_one_add_sub_one_le`) | new lemma (M) |
| `β_nonneg` | $\beta = \sqrt{s}(1+\sigma) \ge 0$ | `sqrt_err`, $u < 1$ | immediate |
| `β_pos` | for $j < k$, $\beta_j \ne 0$ by definition of $k$, and $\ge 0$ | `lanczosSteps` | immediate |
| `v_zero`, `β_zero` | literals $0$ decode to $0$ | `lit_err` | immediate |
| `transpose_H` | hypothesis `hH` | input | hypothesis |
| `k_pos` | $q \ge 1$; $k \ge 1$ always | `lanczosSteps` | hypothesis on $q$ |
| `k_mul_ε_le` | $k \le q$ and `hsmall` | — | hypothesis on $q, N, u$ |
| `ε_nonneg` | $\gamma_{2N+6} \ge 0$ | `roundingFactor_nonneg` | immediate |

So $\varepsilon = \max(\varepsilon_{\mathrm{mv}}, u, \gamma_2, \gamma_N, \gamma_{2N+6}) =
\max(\varepsilon_{\mathrm{mv}}, \gamma_{2N+6})$ for $N \ge 1$ ($\mathbf{b} \ne \mathbf{0}$ forces
it). The `γ_{2N+6}` is crude (first order $2Nu$; a sharper count gives $\gamma_{N+4}$); kept for
a short proof (open question Q3).

**Breakdown and success.** The only partial operations are the division in `rscl` and `sqrt` of
a negative. $s = \sum_i z_i^2(1+\eta_i)$ with $\lvert\eta_i\rvert \le \gamma_N < 1$, so $s \ge 0$
(`sqrt` succeeds) and $s = 0 \iff \mathbf{z} = \mathbf{0}$; `cmp_eq` is exact on decodings, so
`rscl` runs only when $s > 0$, and then $\beta = \sqrt{s}(1+\sigma) > 0$. The matvec succeeds by
the contract (oracle) or by `exec_gemv` (dense). Hence **success is unconditional** given the
contract. After breakdown the slot holds a vector decoding to $\mathbf{0}$, the product of
$\mathbf{0}$ is $\mathbf{0}$ (contract bound $\varepsilon\lVert\mathbf{H}\rVert\cdot 0$; `gemv`
by `AddsZeroExactly`), and every later $\alpha$, $\beta$ is $0$: stated as a conjunct.

### 2.3 Options for breakdown (decision L1)

* **(a) Fixed $q$, exact test, $k$ from the outputs** (recommended). The program is the D15
  program (one exact spec, counts unchanged); $k$ = `lanczosSteps β q` is a function of the
  decoded output, so "the steps actually taken" is checkable; later outputs are proved $0$.
* (b) `whileFuel` that stops at breakdown and writes $k$. Same theorem with $k$ an output cell,
  but a second program, an exact spec with a stopping index, and counts depending on $k$.
* (c) Hypothesis "no computed $\beta_j$ is $0$". Rejected: a condition on the run.

### 2.4 Assumptions that the model does not give

1. **Matvec accuracy for an oracle.** `IsRelErrSem` constrains scalar operations only
   (`Computation-Rounding.md` §5, finding 5). Fix: the contract `IsMatvecErr I o dec p H ε`
   (height $N$; on every column succeeds with a decoded result within
   $\varepsilon\lVert\mathbf{H}\rVert\lVert\mathbf{x}\rVert$ of $\mathbf{H}\mathbf{x}$) as a
   hypothesis, the paper's own assumption; discharged for the stored matrix by the dense twin
   (decision L2). A backward-form oracle contract ($\lvert\Delta\mathbf{H}\rvert \le
   \varepsilon\lvert\mathbf{H}\rvert$) implies it with $\sqrt{N}\varepsilon$ by the same lemma.
2. **The start vector.** `LanczosRun` does not relate $\mathbf{v}_1$ to $\mathbf{b}$, but a user
   of the backward model wants $\mathbf{b}$. The bridge adds $c\mathbf{v}_1 = \mathbf{b} +
   \boldsymbol\delta_0$, $c > 0$, $\lVert\boldsymbol\delta_0\rVert \le u\lVert\mathbf{b}\rVert$ (and
   near unit length of $\mathbf{v}_1$ is the $j = 1$ case of the field). No change to the
   interface needed.
3. **Inputs** ($\mathbf{H}$ symmetric after decoding, $\mathbf{b} \ne \mathbf{0}$, $q \ge 1$) and
   **size** ($(2N+6)u < 1$, $q\varepsilon \le 1/100$): hypotheses, all checkable. In double
   precision, dense, $qN^{3/2} \lesssim 9\cdot10^{13}$.
4. **Out of scope** (flag for layer 2): with underflow, $s$ can round to $0$ for
   $\mathbf{z} \ne \mathbf{0}$ and near unit length fails for tiny $\mathbf{z}$; the zero test then
   needs a threshold. Complex data: the program already conjugates (`dot`) and takes `re`; the
   bridge needs $\Bbbk$-valued decodings (pending maintainer decision of the toolkit).

## 3. Porting the stability analysis

### 3.1 Placement and the interface

`NLAlib/Krylov/FinitePrecision/` (topic: finite-precision Krylov processes; Krylov layer, imports
Matrix, never Computation). The interface `NLAlib.LanczosRun n k` (skeleton:
`NLAlibScaffold/Krylov/FinitePrecision/LanczosRun.lean`) is the external structure with:
vectors `Fin n → ℝ`, `vnorm x` → `‖WithLp.toLp 2 x‖`, `vdot` → `⬝ᵥ`, `‖H‖` (L2Operator scope) →
`specNorm H`, `Δ` → `δ`, fields named after their statements (N2): `hHsymm` → `transpose_H`,
`hsmall` → `k_mul_ε_le`, `h_u`/`heu` → `u_eq`/`norm_eu_le`, … , `h_be`/`hΔ` →
`smul_v_eq`/`norm_δ_le`, `hnear`/`hnext` → `abs_norm_v_sq_sub_one_le`/`abs_norm_v_succ_sq_sub_one_le`,
`hβ_internal` → `β_pos`. Error terms stay defined by the paper's equations
(`computed = exact + e`); N10 (`exact − computed`) concerns statements of differences, which the
port writes in that order. The bridge lives in `Krylov/Processes/LanczosRounding.lean` (it imports
Computation; FinitePrecision does not).

### 3.2 What of `Core/` (3.5k lines) the library already has

| external | library | action |
|---|---|---|
| `Matrix.lean`: `Vec`, `Mat`, `vnorm`, `vdot`, `‖X‖ ≤ ‖X‖_F`-type bounds, Schur test, `‖[q_j]‖ ≤ (∑‖q_j‖²)^{1/2}` | `WithLp.toLp 2`, `specNorm`, `Matrix/Norms/Compare.lean` (`specNorm_le_frobNorm`), `HasOrthonormalCols` | replace; Schur test and the column bound to `Matrix/Norms` if absent |
| `Frobenius.lean`: `frobSq`, `frobNorm`, `opNorm_le_frobNorm` | `frobNorm` (squares, no `frobSq`), `specNorm_le_frobNorm` | replace; compression bound $\lVert D\rVert_F \le \sqrt{2k}\lVert D\rVert$ is new → `Matrix/Norms` |
| `SpectralFrobenius.lean`: rank = #nonzero eigenvalues, $\lVert A\rVert_F \le \sqrt{\mathrm{rank}}\lVert A\rVert$ | `frobNorm_le_sqrt_rank_mul_specNorm` | replace (rank lemma: check `Matrix/Spectral`) |
| `Spectral.lean`: `spectralMin/Max/Distance`, Rayleigh bounds | eigenvalue API of `Matrix/Spectral` (Mathlib `IsHermitian.eigenvalues`) | replace by library names; keep only missing lemmas |
| `ExactLanczos.lean`: `exactLanczosState`, identification with an orthonormal recurrence | `NLAlib.lanczosState`, `lanczosTridiagonal`, `IsGradedKrylovBasis.eq_arnoldiMatrix` | **replace**: thm:greenbaum's "exact Lanczos on (Ã, ṽ) returns $T_k$" is restated with `lanczosState` (0-based); the identification lemma (an orthonormal three-term recurrence is the Lanczos recurrence) is new for the library → `LanczosRecurrence.lean` |
| `Measure/`: `AtomicMass`, moments, `atomicWasserstein`, cfc Frobenius Lipschitz | `spectralMeasure` (Measure ℝ), `integral_spectralMeasure`; matrix `cfc` | rem:wasserstein restated on `spectralMeasure` (Q4); cfc Lipschitz in Frobenius → `Matrix/Functions` |
| `Commutator`, `GramCommutator`, `Underline`, `SaadGramCommutator`, `Nilpotent`, `Dilation*`, `BackwardCorrection`, `BlockSpectral` | none | port: Mathlib-only facts (nilpotent augmentation, block algebra) → `ForMathlib/LinearAlgebra/Matrix/…` (rule: general facts without NLAlib vocabulary); the rest (uses `specNorm`) → `Krylov/FinitePrecision/` |

### 3.3 Size, rules, toolchain

* Lines: Core 3.5k → about 0.7k removed (replaced), 0.3k to ForMathlib, 2.5k to
  `Krylov/FinitePrecision`; `Lanczos/` 3.05k ports nearly verbatim (renames). Landing ≈ 5.5–6k
  lines in about 14 files (≤ 1000 lines each, F10). Plus this note's work: exact spec ≈ 700,
  bridge ≈ 900 (three new kernel/real lemmas ≈ 250, invariant over the three slots ≈ 650, shared
  with the exact proof's structure).
* Rules: `module` form, `@[expose] public section`, `namespace NLAlib` (F1–F4); every theorem's
  docstring cites the paper (a new bibliography key, year to confirm) with its labels (`thm:paige`, …);
  `Result:` ids for the headlines; the constants (700, 1200, 3000k³, 4j, `(1+10ε)β + 2‖H‖`, …)
  into `docs/constants.toml` as printed, **unchanged**; names to the grammar (`beta_bound` →
  `LanczosRun.β_le`, `paige_bound` → `LanczosRun.abs_…_le`, `greenbaum_backward_model` →
  `LanczosRun.exists_backwardModel` or kept as a structure-valued theorem).
* Toolchain v4.32.2 → v4.33.1: expect Mathlib renames in `WithLp`/`EuclideanSpace` and the
  L2-operator norm instances, and the `module` conversion (non-exposed definitions break `rfl`
  across files: `@[expose]` as the library does). Mechanical; budget a day of agent time.

### 3.4 Headlines kept, and the composed results

Kept with their constants: `local_errors` (thm:local-errors), `coefficients_paper`
(lem:coefficients), `beta_recurrence_paper`, `paige_bound` (thm:paige) and its dichotomy,
`greenbaum_backward_model` (thm:greenbaum), `stabilized`, `containment` (thm:stabilized,
thm:containment), the Wasserstein remark, and the optional spectral corollaries. Each gets a
program-level corollary in `LanczosRounding.lean`, one line from the bridge: e.g.
"`lanczosBasisDenseProg` succeeds and for every eigenpair $(\theta, \mathbf{y})$ of the computed
$\mathbf{T}_k$, $\lvert\mathbf{y}_k\,\mathbf{x}^{\mathsf{T}}(\beta_k\mathbf{v}_{k+1})\rvert \le
3000k^3\varepsilon\lVert\mathbf{H}\rVert$ with $\varepsilon$ as above". These are the registered
targets (E3), stated on outputs only.

## 4. Toolkit dependencies

Present and used: `IsRelErrSem` (`sqrt_err`, `sqrt_ok`, `cmp_eq`, `re`, `neg`, `lit_err`),
`AddsZeroExactly`, `exec_dot_eq_sum_mul_one_add`, `exec_dot_abs_sum_mul_sub_le`,
`IsRelErrSem.exec_axpy`, `exec_gemv_abs_mulVec_sub_le`, the γ algebra (`roundingFactor_*`,
`abs_inv_one_add_sub_one_le`, `abs_one_add_mul_one_add_sub_one_le`).

Missing (in the skeleton, `sorry`):
* `IsRelErrSem.exec_rscl` (deferred in the toolkit's §5; S).
* `abs_norm_sq_sub_one_le_of_relErr_normalize` (pure real; M).
* `norm_abs_mulVec_abs_le` (normwise from componentwise, $\sqrt{N}$; S; belongs in
  `Matrix/Norms`).
* `IsMatvecErr` (definition: the first oracle contract; L2).
* Run lemmas for `copyv`, `ifThenElse` with an exact comparison, `un` instructions, and the
  `apply` statement under an error contract (S each; the store bookkeeping of the toolkit's
  run lemmas covers them).
* Not needed: `nrm2` (the program inlines dot + sqrt), `scal`, a sqrt *kernel*.

## 5. Open questions (each with a recommendation)

* **Q1 (L6) Basis output.** State the headlines on the `Q` output (the variant with the basis,
  $N(q+1)$ cells) or on the hidden trace of the α/β-only program? Recommended: basis variant for
  the headlines (Paige and Greenbaum are about $\mathbf{V}_{k+1}$); the α/β-only program gets the
  T-only corollaries (Ritz values) by the same proof.
* **Q2 (L3) One ε or five.** Keep the single ε of `LanczosRun` (the paper's constants unchanged)
  or generalise to per-clause $\varepsilon$'s (sharper: $\varepsilon_{\mathrm{mv}}$ appears only in
  `norm_eu_le`)? Recommended: single ε now; per-clause is a later refinement of the analysis.
* **Q3 Constant of near unit length.** $\gamma_{2N+6}$ (short proof) or $\gamma_{N+4}$ (sharp to
  first order)? Recommended: $\gamma_{2N+6}$; it is dominated by $\sqrt{N}\gamma_N$ in the dense
  case for $N \ge 8$.
* **Q4 Spectral measures.** Port `Measure/` (`AtomicMass`, atomic $W_1$) or restate on the
  library's `spectralMeasure`? Recommended: restate on `spectralMeasure`, with $W_1$ defined via
  1-Lipschitz test functions on finite-support measures; keep atomic lemmas private.
* **Q5 (L5) Port or depend.** Port into NLAlib (renames, library API, constants kept) or require
  the external repository as a Lake dependency? Recommended: port (one toolchain, one rule set,
  the explorer); the external repository stays the paper's artefact.
* **Q6 Precision of $\mathbf{b}$ and $\mathbf{H}$.** All at one tag $p$. Mixed precision (matvec
  in higher precision through `convert`) changes only $\varepsilon_{\mathrm{mv}}$. Recommended:
  one tag now.
