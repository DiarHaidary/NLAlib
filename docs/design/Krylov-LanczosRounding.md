# Design note: the Lanczos program in finite precision, and the re-proof of the stability analysis

2026-10-28. Branch `design/lanczos-fp` (from `design/fp-toolkit` @ 36bab62). Decision sheet:
`state/decisions/Lanczos-FP.json` in the harness (ids L1–L7 below).

## Summary

The maintainer's request: define the Lanczos algorithm fully as a program in the model of
computation, and plug in the analysis of *A simple stability analysis of Lanczos in finite
precision* (T. Chen; Lean at <https://github.com/tchen-research/simple-lanczos-stability>, 6.6k
lines, 0 `sorry`, Lean v4.32.2). That analysis assumes an inexact recurrence (the structure
`LanczosRun`: five local errors and nearly unit vectors, one accuracy parameter ε). This note
closes the gap: a **specific program**, its **exact specification** against `NLAlib.lanczosState`,
and a **bridge theorem**: in the standard model (`IsRelErrSem`, `AddsZeroExactly`) the run
*succeeds* and its outputs *are* a `LanczosRun` with

$$\varepsilon = \max\bigl(\varepsilon_{\mathrm{mv}},\ \gamma_{N+4}(u)\bigr),\qquad
\varepsilon_{\mathrm{mv}} = \sqrt{N}\,\gamma_N(u)\ \text{(stored matrix, `gemv`)}\ \text{or the oracle's accuracy (matrix-free)},$$

about $N^{3/2}u$ for a stored matrix, $Nu$ for an oracle accurate to $O(Nu)$. The constant
$\gamma_{N+4}$ is Higham's count (2026-10-28, after review: products of rounding errors,
§2.2), replacing the earlier $\gamma_{2N+6}$. Every hypothesis is on the data, the sizes and
$u$: $\mathbf{H}$ symmetric, $\mathbf{b} \ne \mathbf{0}$, $q \ge 1$, $(N+4)u < 1$,
$q\varepsilon \le 1/100$. Breakdown is handled inside the program (exact test $\beta_j = 0$,
never divides by zero); the number of steps covered, $k$, is read off the outputs (first $j$ with
$\beta_j = 0$, else $q$), and every output after breakdown is $0$, $\mathbf{v}_{k+1}$ included.
Every `LanczosRun` field is derivable; the one assumption the model cannot supply, the accuracy
of a matrix-free oracle, is a named contract (`IsMatvecErr`) discharged for the dense program,
and the matrix-free headline is an instance of an access model, `MatrixFreeRounded` (decision
L7). The analysis is **re-proved** in the library's terms (§3, maintainer 2026-10-28: the
essence, not the text verbatim).

Skeleton (all typecheck; 3 scaffold files, 6 `sorry`: the exact spec, the two bridges, and
none else): `NLAlibScaffold/Krylov/Processes/LanczosProgramTree.lean`,
`NLAlibScaffold/Krylov/Processes/LanczosRounding.lean`,
`NLAlibScaffold/Krylov/FinitePrecision/LanczosRun.lean`. Toolkit additions, all proved, in
`NLAlib/`: `IsRoundingProduct` and its algebra (`Computation/Rounding.lean`), the product form
of `dot` (`BLAS/Traces.lean`, `BLAS/RoundingErrors.lean`), `IsRelErrSem.exec_rscl`
(`BLAS/RoundingErrors.lean`), `IsMatvecErr` and `MatrixFreeRounded` (`Computation/Contract.lean`),
`norm_toLp_map_abs_mulVec_abs_le` (`Matrix/Norms/Compare.lean`).

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
| 7 | if $\beta_j \ne 0$: $\mathbf{v}_{j+1} \leftarrow \mathbf{z}/\beta_j$ | `cmp .eq` of $\beta_j$ against literal 0, `rscl` ($n$ divisions) | `smul_v_eq`, `norm_δ_le`, near unit |

Start (`lanczosInit`): slot 2 $\leftarrow \mathbf{0}$ (literals), slot 0 $\leftarrow \mathbf{b}$
(`copyv`), $s \leftarrow \mathbf{b}^{\mathsf{H}}\mathbf{b}$ (`dot`), $c \leftarrow \sqrt{s}$,
if $c \ne 0$: slot 0 $\leftarrow \mathbf{b}/c$ (`rscl`); $\beta_0 \leftarrow 0$. Slots
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
  ifThenElse p .eq ⟨s, 1⟩ ⟨s, 3⟩ (pure ()) (rscl p ⟨s, 1⟩ W nxt N)   -- test β (review S3)
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
def LanczosOutputs (st) (p) (dec) (alpha beta Q : ℕ) (q) (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ) : Prop
  -- the three output buffers decode to α j, β j (j < q) and V j (j ≤ q)        (review S1)

def HasLanczosRunOutputs (st) (p) (dec) (u ε : ℝ) (alpha beta Q : ℕ) (q) (H) (b : Fin N → ℝ) :=
  ∃ α β V, LanczosOutputs st p dec alpha beta Q q α β V ∧
    (∃ c δ₀, 0 < c ∧ c • V 0 = b + δ₀ ∧ ‖δ₀‖ ≤ u * ‖b‖) ∧
    (∀ j, lanczosSteps β q ≤ j → j < q → α j = 0 ∧ β j = 0) ∧
    (β (lanczosSteps β q - 1) = 0 → ∀ j, lanczosSteps β q ≤ j → j ≤ q → V j = 0) ∧  -- (M2)
    ∃ L : LanczosRun N (lanczosSteps β q), L.H = H ∧ L.ε = ε ∧
      (∀ j < k, L.α (j+1) = α j ∧ L.β (j+1) = β j) ∧ ∀ j ≤ k, L.v (j+1) = V j

theorem IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg (I) (p) (o)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (q) (H : Matrix (Fin N) (Fin N) ℝ) (hH : Hᵀ = H)
    (hmv : IsMatvecErr I o dec p H (εmv * specNorm H))
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0) (hq : 0 < q)
    (hu : ((N + 4 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) εmv ≤ 1 / 100) :
    ∃ st', exec I (lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run (inputState p […]) = some st' ∧
      HasLanczosRunOutputs st' p dec (u p) (lanczosRoundingEps N (u p) εmv) 1 2 3 q H (dec ∘ b)

theorem lanczosBasisProg_matrixFreeRounded (p) (o) (u) (dec) (εmv) :
    MatrixFreeRounded p (fun N n => (lanczosBasisProg p o N (n 0) 0 1 2 3).run) (0 < n 0) …
      (mvBound := εmv * specNorm H) (pre := Hᵀ = H ∧ b ≠ 0 ∧ (N+4)u < 1 ∧ qε ≤ 1/100)
      (post := HasLanczosRunOutputs …)          -- proved: a wrap of the bridge (L7, review M3)
```

with `lanczosRoundingEps N u εmv = max εmv γ_{N+4}(u)` and
`lanczosSteps β q = (first j < q with β j = 0) + 1`, else `q`. The dense twin
`exists_lanczosRun_of_lanczosBasisDenseProg` takes the $N^2$ words of $\mathbf{H}$ as buffer 0
(symmetric after decoding) instead of the oracle, with $\varepsilon_{\mathrm{mv}} = \sqrt{N}\gamma_N$:
all hypotheses are then on data, sizes and $u$. Composed with the analysis, every headline of the
paper becomes "the run succeeds and …" for the program (§3.4). The conjunct (M2) is the paper's
convention $\mathbf{v}_{k+1} = \mathbf{0}$ at a terminal step (`sec:model`): the breakdown slot
keeps $\mathbf{z} = \mathbf{0}$ and every later step computes exact zeros
($\mathrm{fl}(0 \cdot x) = 0$, $\mathrm{fl}(0 + 0) = 0$, $\sqrt{0}(1+\sigma) = 0$, the oracle
bound $\le c \cdot 0$).

`hu` is not implied by `hsmall`: $\gamma_{N+4}$ is negative past $(N+4)u = 1$, so `hsmall`
alone does not bound $u$ (review N2).

### 2.2 Clause by clause

Notation: $\gamma_m = mu/(1-mu)$ (`roundingFactor m u`); $\theta_m$ is a quantity with
`IsRoundingProduct u m θ`: $1 + \theta_m = \prod_{i<m}(1+\delta_i)^{\pm 1}$,
$\lvert\delta_i\rvert \le u$ [Higham2002, Lemma 3.1]; program step $j$ is `LanczosRun` index
$j+1$; vectors are the decodings of the slot contents (real, `dec`).

| clause | bound obtained | from | status |
|---|---|---|---|
| `u_eq`, `norm_eu_le` | matrix-free: $\varepsilon_{\mathrm{mv}}\lVert\mathbf{H}\rVert\lVert\mathbf{v}\rVert$; dense: $\lvert\mathbf{e}\rvert \le \gamma_N\lvert\mathbf{H}\rvert\lvert\mathbf{v}\rvert$, so $\lVert\mathbf{e}\rVert \le \sqrt{N}\gamma_N\lVert\mathbf{H}\rVert\lVert\mathbf{v}\rVert$ | `IsMatvecErr` / `exec_gemv_abs_mulVec_sub_le` + `norm_toLp_map_abs_mulVec_abs_le` | contract / **proved** (`Matrix/Norms/Compare.lean`) |
| `w_eq`, `norm_ew_le` | $w_i = -\beta v_i(1+\theta_i) + u_i(1+\delta_i)$, so $\lVert\mathbf{e}^w\rVert \le \gamma_2(\lVert\mathbf{u}\rVert + \lvert\beta\rvert\lVert\mathbf{v}_{j-1}\rVert)$ | `IsRelErrSem.exec_axpy` (negation exact) | immediate + normwise step (S) |
| `α_eq`, `abs_eα_le` | $\lvert e^\alpha\rvert \le \gamma_N\sum\lvert v_i\rvert\lvert w_i\rvert \le \gamma_N\lVert\mathbf{v}\rVert\lVert\mathbf{w}\rVert$; `re` exact | `exec_dot_abs_sum_mul_sub_le` + Cauchy–Schwarz | immediate |
| `z_eq`, `norm_ez_le` | $\gamma_2(\lVert\mathbf{w}\rVert + \lvert\alpha\rvert\lVert\mathbf{v}\rVert)$ | `exec_axpy` | immediate |
| `smul_v_eq`, `norm_δ_le` | $\beta \ne 0$: $\beta v'_i = z_i(1+\delta_i)$, $\lVert\boldsymbol\delta\rVert \le u\lVert\mathbf{z}\rVert$; $\beta = 0$: $\mathbf{z} = \mathbf{0}$ (below), $\boldsymbol\delta = \mathbf{0}$ | `IsRelErrSem.exec_rscl` | **proved** (`BLAS/RoundingErrors.lean`) |
| `abs_norm_v_sq_sub_one_le`, `…_succ_…` | $\le \gamma_{N+4}$, derivation below | `exec_dot_eq_sum_mul_one_add_isRoundingProduct`, `sqrt_err`, `exec_rscl`, `abs_norm_sq_sub_one_le_of_relErr_normalize` | all **proved** |
| `β_nonneg` | $\beta = \sqrt{s}(1+\sigma) \ge 0$ | `sqrt_err`, $u < 1$ | immediate |
| `β_pos` | for $j < k$, $\beta_j \ne 0$ by definition of $k$, and $\ge 0$ | `lanczosSteps` | immediate |
| `v_zero`, `β_zero` | literals $0$ decode to $0$ | `lit_err` | immediate |
| `transpose_H` | hypothesis `hH` | input | hypothesis |
| `k_pos` | $q \ge 1$; $k \ge 1$ always | `lanczosSteps` | hypothesis on $q$ |
| `k_mul_ε_le` | $k \le q$ and `hsmall` | — | hypothesis on $q, N, u$ |
| `ε_nonneg` | $\gamma_{N+4} \ge 0$ | `roundingFactor_nonneg` | immediate |

**Near unit length, Higham's count.** The computed $s = \mathrm{fl}(\mathbf{z}^{\mathsf{T}}\mathbf{z})
= \sum_i z_i^2(1+\eta_i)$ with each $1+\eta_i$ a product of $N$ rounding factors (the product form
of [Higham2002, (3.4)], `IsDotTrace.exists_eq_sum_mul_one_add_isRoundingProduct`; no hypothesis
$Nu < 1$ is needed for it). The values $1+\theta_m$ fill the interval $[(1-u)^m, (1-u)^{-m}]$
(`isRoundingProduct_iff`), so a weighted mean of $1+\theta_m$'s is a $1+\theta_m$
(`exists_isRoundingProduct_sum_mul_one_add_eq`): $s = \lVert\mathbf{z}\rVert^2(1+\theta_N)$.
Then $\beta = \sqrt{s}(1+\sigma)$, $v_i = (z_i/\beta)(1+\delta_i)$ and
$$\lVert\mathbf{v}\rVert^2 = \frac{\sum_i z_i^2(1+\delta_i)^2}{s(1+\sigma)^2}
= \frac{1+\theta_2}{(1+\theta_N)(1+\sigma)(1+\sigma)} = 1 + \theta_{N+4},$$
the numerator again by the weighted mean ($(1+\delta_i)^2$ is a $1+\theta_2$), the quotient by
Higham's ratio rule $(1+\theta_k)/(1+\theta_j) = 1+\theta_{k+j}$ (`IsRoundingProduct.div`, valid
for products of rounding errors without $j \le k$). Lemma 3.1 (`IsRoundingProduct.abs_le`) then
gives $\lvert\lVert\mathbf{v}\rVert^2 - 1\rvert \le \gamma_{N+4}$ under $(N+4)u < 1$, sharp to
first order ($(N+4)u$). The earlier $\gamma_{2N+6}$ came from bounding $\lvert\theta_N\rvert \le
\gamma_N$ first and inverting with `abs_inv_one_add_sub_one_le` ($\gamma_j \to \gamma_{2j}$),
which loses the product structure; that lemma stays for callers that have only a bound.

So $\varepsilon = \max(\varepsilon_{\mathrm{mv}}, u, \gamma_2, \gamma_N, \gamma_{N+4}) =
\max(\varepsilon_{\mathrm{mv}}, \gamma_{N+4})$ (all under $(N+4)u < 1$). In the oracle case with an
accurate oracle ($\varepsilon_{\mathrm{mv}} \approx Nu$) this is $\approx Nu$, no longer $2Nu$.

**Breakdown and success.** The only partial operations are the division in `rscl` and `sqrt` of
a negative. $s = \lVert\mathbf{z}\rVert^2(1+\theta_N)$ with $1+\theta_N \ge (1-u)^N > 0$, so
$s \ge 0$ (`sqrt` succeeds), $s = 0 \iff \mathbf{z} = \mathbf{0}$, and $\beta = \sqrt{s}(1+\sigma)$
is $0$ exactly when $s$ is ($1+\sigma > 0$). The program tests $\beta$ (review S3, the paper's
`if z_j = 0` in Algorithm 1); `cmp_eq` is exact on decodings, so `rscl` runs only when
$\beta > 0$. The matvec succeeds by the contract (oracle) or by `exec_gemv` (dense). Hence
**success is unconditional** given the contract. After breakdown the slot holds a vector
decoding to $\mathbf{0}$, every later product, update and coefficient is $0$, and so are the
later columns (M2).

### 2.3 Options for breakdown (decision L1)

* **(a) Fixed $q$, exact test, $k$ from the outputs** (recommended). The program is the D15
  program (one exact spec, counts unchanged); $k$ = `lanczosSteps β q` is a function of the
  decoded output, so "the steps actually taken" is checkable; later outputs are proved $0$.
* (b) `whileFuel` that stops at breakdown and writes $k$. Same theorem with $k$ an output cell,
  but a second program, an exact spec with a stopping index, and counts depending on $k$.
* (c) Hypothesis "no computed $\beta_j$ is $0$". Rejected: a condition on the run.

### 2.4 Assumptions that the model does not give

1. **Matvec accuracy for an oracle.** `IsRelErrSem` constrains scalar operations only
   (`Computation-Rounding.md` §5, finding 5). Fix: the contract `IsMatvecErr I o dec p H c`
   in `NLAlib/Computation/Contract.lean` (review S2; height $N$; on every column succeeds with a
   decoded result $\mathbf{y}$, $\lVert\mathbf{H}\mathbf{x} - \mathbf{y}\rVert \le
   c\lVert\mathbf{x}\rVert$), used with $c = \varepsilon_{\mathrm{mv}}\lVert\mathbf{H}\rVert_2$.
   The absolute bound $c$ keeps the Computation layer free of `specNorm` (E5). As a
   hypothesis, the paper's own assumption; discharged for the stored matrix by the dense twin
   (decision L2). A backward-form oracle contract ($\lvert\Delta\mathbf{H}\rvert \le
   \varepsilon\lvert\mathbf{H}\rvert$) implies it with $\sqrt{N}\varepsilon$ by the same lemma.
2. **The start vector.** `LanczosRun` does not relate $\mathbf{v}_1$ to $\mathbf{b}$, but a user
   of the backward model wants $\mathbf{b}$. The bridge adds $c\mathbf{v}_1 = \mathbf{b} +
   \boldsymbol\delta_0$, $c > 0$, $\lVert\boldsymbol\delta_0\rVert \le u\lVert\mathbf{b}\rVert$ (and
   near unit length of $\mathbf{v}_1$ is the $j = 1$ case of the field). No change to the
   interface needed.
3. **Inputs** ($\mathbf{H}$ symmetric after decoding, $\mathbf{b} \ne \mathbf{0}$, $q \ge 1$) and
   **size** ($(N+4)u < 1$, $q\varepsilon \le 1/100$): hypotheses, all checkable. In double
   precision, dense, $qN^{3/2} \lesssim 9\cdot10^{13}$.
4. **Out of scope** (flag for layer 2): with underflow, $s$ can round to $0$ for
   $\mathbf{z} \ne \mathbf{0}$ and near unit length fails for tiny $\mathbf{z}$; the zero test then
   needs a threshold. Complex data: the program already conjugates (`dot`) and takes `re`; the
   bridge needs $\Bbbk$-valued decodings (pending maintainer decision of the toolkit).

### 2.5 The access model (decision L7)

`Computation.md` G52 asks every public result about a program's runs to be an instance of an
access model; the existing models (`MatrixFree`, `StoredEntries`, `MatrixFreeProb`) are exact
arithmetic (`exactInterp`), and `Computation-Rounding.md` §5 deferred the finite-precision form
"to the first such analysis". This is it (review M3).

* **(a) Two contracts** (recommended, applied): `MatrixFreeRounded p prog valid X inputs u dec
  mvBound pre post` in `NLAlib/Computation/Contract.lean`: for all valid sizes, inputs and real
  $\mathbf{H}$ with `pre`, under **every** `I` whose semantics meets `IsRelErrSem u dec ⊤` and
  `AddsZeroExactly` and whose every oracle meets `IsMatvecErr … H (mvBound N n H)`, the run of
  `prog N n` from the inputs succeeds and ends in `post`. No counts (the charge of `I` is
  arbitrary; counts stay with the exact `MatrixFree` target). `prog` is a statement family, so
  a compiled program enters as `Prog.toStmt` once E4 compiles it. The matrix-free bridge is
  wrapped as `lanczosBasisProg_matrixFreeRounded` (proved from the bridge). The dense twin needs
  no oracle; it stays in `exec` form (it is the stronger statement, and an instance of the same
  model with any `mvBound`).
* (b) One bundled contract on `Interp`. Rejected for now: the oracle contract would not be
  separable for the dense twin, and the scalar contracts are reused by every kernel lemma.
* (c) Exempt finite-precision results from G52. Not recommended.

Recorded as L7 in `state/decisions/Lanczos-FP.json` (recommended (a), applied per Fable review;
maintainer to confirm).

### 2.6 Review changes (Fable review 2026-10-28, applied)

M1 import fixed; M2 (above); M3 = L7; S1 `LanczosOutputs`, `HasLanczosRunOutputs`; S2
`IsMatvecErr` → `Computation/Contract.lean`, `IsRelErrSem.exec_rscl` →
`Computation/BLAS/RoundingErrors.lean` (proved; `run_rscl` made public in `BLAS.lean`), the norm
lemma → `Matrix/Norms/Compare.lean` as `norm_toLp_map_abs_mulVec_abs_le` (proved, with
$\sqrt{\lvert n \rvert}$ from `frobNorm_le_sqrt_card_mul_specNorm`, no rank lemma needed); S3
the program tests $\beta$ (step and start, the start now always takes the square root); S4
`LanczosRun.ofLE` (proved). N1 resolved by §2.2 (Higham's count).

## 3. Re-proving the stability analysis

Maintainer, 2026-10-28: "in the end I don't need the results from there verbatim — the
important thing is the essence." So the plan is **not** a line-by-line port of
`simple-lanczos-stability` but a **re-proof of its main results in the library's own terms**,
restructured freely. The earlier advice (here and in the review, N10) to "port the external
definitions first, then restate" is dropped.

### 3.1 What is re-proved

The results of the paper's analysis (external `Lanczos/Bounds.lean`, `Ritz.lean`,
`Greenbaum/Backward.lean`), each restated on `LanczosRun` with library vocabulary:

| result (paper label) | content | library form |
|---|---|---|
| local errors (`thm:local-errors`) | the computed recurrence $\mathbf{H}\mathbf{V}_k = \mathbf{V}_k\mathbf{T}_k + \beta_k\mathbf{v}_{k+1}\mathbf{e}_k^{\mathsf{T}} + \mathbf{F}_k$, $\lVert\mathbf{F}_k\rVert$ bounded | `LanczosRun.…_eq_…`, `specNorm`/`frobNorm` bounds |
| coefficients (`lem:coefficients`), β recurrence | $\lvert\alpha_j\rvert$, $\beta_j \le (1+O(\varepsilon))\lVert\mathbf{H}\rVert$ | `LanczosRun.β_le`, `LanczosRun.abs_α_le` |
| Paige's bound (`thm:paige`) and its dichotomy | loss of orthogonality only towards converged Ritz vectors | `LanczosRun.abs_…_le` on eigenpairs of `lanczosTridiagonal`-shaped $\mathbf{T}_k$ |
| Greenbaum backward model (`thm:greenbaum`) | $\mathbf{T}_k$ is exact Lanczos on a nearby larger problem | exact Lanczos stated with `lanczosState`/`lanczosMatrix`/`lanczosTridiagonal` (0-based), `HasOrthonormalCols` |
| stabilised / containment (`thm:stabilized`, `thm:containment`) | Ritz values in a neighbourhood of the spectrum | eigenvalue API of `Matrix/Spectral` |
| spectral-measure (Wasserstein) remark | the Gauss quadrature measure is $W_1$-close | `spectralMeasure` (Q4) |

The proofs follow the paper's arguments (the essence) but use the library's API from the start:
0-based indexing as in `lanczosState`; `‖WithLp.toLp 2 x‖`, `specNorm`, `frobNorm`,
`frobNorm_le_sqrt_rank_mul_specNorm`, `specNorm_le_frobNorm`, `HasOrthonormalCols`; the
eigenvalue API of `Matrix/Spectral` instead of the external `spectralMin/Max/Distance`;
`spectralMeasure` instead of `AtomicMass`. Mathlib-only facts the proofs need (nilpotent
augmentation, block algebra) go to `ForMathlib`, the rest to `NLAlib/Krylov/FinitePrecision/`.

**Constants may change** if a cleaner route gives them; each change is recorded in
`docs/constants.toml` and in a table here (old value, new value, why). None yet.

### 3.2 The interface may be reshaped

`NLAlib.LanczosRun n k` (skeleton: `NLAlibScaffold/Krylov/FinitePrecision/LanczosRun.lean`) is
currently the external structure renamed (fields after their statements, Naming N2; `vnorm` →
`‖toLp 2 ·‖`, `‖H‖` → `specNorm H`, `Δ` → `δ`), 1-based in $j$ as in the paper ($\mathbf{v}_0 =
\mathbf{0}$, steps $1..k$). It may be **reshaped** when the re-proof or the bridge gives a cleaner
hypothesis set, staying close to the paper's assumptions (`ass:arithmetic`,
`ass:normalization`, `ass:small-eps`); candidates, none applied yet:

* 0-based indexing, matching `lanczosState` and the program's outputs (the bridge's `j + 1`
  shifts disappear);
* the start-vector clause ($c\mathbf{v}_1 = \mathbf{b} + \boldsymbol\delta_0$) and the terminal
  convention $\mathbf{v}_{k+1} = \mathbf{0}$ (M2) as fields, since the backward model and the
  Ritz corollaries use them;
* per-clause accuracies (Q2/L3) only if the re-proof's constants come out cleaner with them.

To keep reshaping cheap: the bridge produces the structure in one place (the `∃ L` of
`HasLanczosRunOutputs`), and `LanczosRun.ofLE` is the only API so far. Any reshaping is noted
here.

### 3.3 Placement, size, rules, toolchain

* `NLAlib/Krylov/FinitePrecision/` (Krylov layer, imports Matrix, never Computation); the
  bridge stays in `Krylov/Processes/LanczosRounding.lean` (it imports Computation).
* Size: the external 6.6k lines are a guide, not a budget; the library replaces most of `Core/`
  (3.5k), and the re-proof of `Lanczos/` (3k) in library terms is expected at about the same
  length, in files of ≤ 1000 lines (F10). Plus this note's work: exact spec ≈ 700, bridge ≈ 900.
* Rules: `module` form, `@[expose] public section`, `namespace NLAlib`; docstrings cite the paper
  (bibliography key to add) with its labels; `Result:` ids for the headlines; names to the
  grammar.
* Toolchain: no port, so the v4.32.2 → v4.33.1 gap is irrelevant (the re-proof is written on the
  library's toolchain).

### 3.4 Headlines and the composed results

Each re-proved headline gets a program-level corollary in `LanczosRounding.lean`, one line from
the bridge: e.g. "`lanczosBasisDenseProg` succeeds and for every eigenpair $(\theta, \mathbf{y})$
of the computed $\mathbf{T}_k$, …" with $\varepsilon$ as above, stated through
`HasLanczosRunOutputs` (S1) and registered as instances of `MatrixFreeRounded` (L7, E3).

### 3.5 Headlines of the re-proof: local errors, Ritz residual, Paige

Scope of this pass (branch `prove/lanczos-analysis`): the external `Lanczos/Bounds.lean`
(coefficients, local errors), `Lanczos/Assembly.lean` + `Ritz.lean` (matrix recurrence, Ritz
residual) and `ComputedCommutator.lean` + `LossOfOrthogonality.lean` (Gram commutator, Paige).
The Greenbaum backward model and its consequences (`thm:greenbaum`, `thm:stabilized`,
`thm:containment`, `rem:wasserstein`) are not in this pass. Files, all in
`NLAlibScaffold/Krylov/FinitePrecision/`: `LocalErrors.lean`, `Recurrence.lean`, `Paige.lean`.
Docstrings say "No printed source" and name the maintainer's draft and its labels; `Paige1976`,
`Paige1980` are added to `references.bib` for the classical forms.

Conventions. `LanczosRun` is unchanged (1-based fields, as the bridges produce it). The derived
objects are 0-based: step $j < k$ is the paper's step $j+1$ (reads $\mathbf{v}_{j+1}$); column $j$
of `L.basis` is $\mathbf{v}_{j+1}$; `L.tridiagonal` is indexed as `lanczosTridiagonal`
($\alpha_{i+1}$ on the diagonal, `L.β i` at $(i, i-1)$); `L.lastIndex : Fin k` is $k-1$, so no proof
term appears in a statement (T9). Norms: `‖WithLp.toLp 2 ·‖`, `specNorm`, `frobNorm`.

| headline (Lean) | paper | paper / external constant | here | why it changed |
|---|---|---|---|---|
| `LanczosRun.β_le` ($j \le k$) | `lem:coefficients` | $\beta_j \le 4j\|\mathbf{A}\|$ | $\tfrac54 j\|\mathbf{H}\|_2$ | recurrence $\beta_{j+1} \le (1+8\varepsilon)(\beta_j + (1+\varepsilon)\|\mathbf{H}\|)$ with $\|\mathbf{v}\| \le 1+\varepsilon/2$, $\|\mathbf{z}\| \le (1+4\varepsilon)\|\mathbf{w}\|$; the paper rounds $1.02\|\mathbf{A}\|$ up to $2\|\mathbf{A}\|$ |
| `norm_u_le` | same, Step 2 | $2\|\mathbf{A}\|$ | $\tfrac{21}{20}\|\mathbf{H}\|_2$ | $(1+\varepsilon)(1+\varepsilon/2) \le 21/20$ |
| `norm_w_le` | same, Step 4 | $5j$ | $\tfrac54(j+1)$ | as for β |
| `abs_α_le` | same | $6j$ | $\tfrac43(j+1)$ | as for β |
| `norm_z_le` | same | $7j$ | $\tfrac43(j+1)$ | as for β |
| `norm_recurrenceError_le` | `thm:local-errors`, $\mathbf{f}_j$ | $\lesssim_k$; ext. $700j\varepsilon\|\mathbf{H}\|$ | $6(j+1)\varepsilon\|\mathbf{H}\|_2$ | the sharper coefficient bounds; the external envelope used $100j$ for every coefficient |
| (field `abs_norm_v_sq_sub_one_le`) | `thm:local-errors`, $g_j$ | $\varepsilon$ | $\varepsilon$ | no theorem: it is an assumption of the interface |
| `abs_adjacentInner_le` | `thm:local-errors`, $p_j$ | $\lesssim_k$; ext. $1200j$ | $7(j+1)\varepsilon\|\mathbf{H}\|_2$ | as above |
| `H_mul_basis` | `eq:governing` | identity | identity | $\mathbf{V}_{k+1}\underline{\mathbf{T}}_k$ written as $\mathbf{V}_k\mathbf{T}_k + \beta_k\mathbf{v}_{k+1}\mathbf{e}_{k-1}^{\mathsf{T}}$ (`vecMulVec`, `Pi.single`); no $\underline{\mathbf{T}}_k$ API needed |
| `frobNorm_residual_le`, `specNorm_residual_le` | proof of `cor:gram-commutator` | $\sqrt{k}\max\|\mathbf{f}_j\|$; ext. $700k^2$ | $6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$ | |
| `H_mulVec_basis_mulVec_sub_smul` | `eq:ritz-residual-identity` | identity | identity | |
| `norm_H_mulVec_basis_mulVec_sub_smul_le` | `eq:ritz-residual-bound` | $\sqrt{1+\varepsilon}\beta_k\lvert y_k\rvert + \|\mathbf{F}_k\|$, divided by $\|\mathbf{x}\|$ | $\sqrt{1+\varepsilon}\beta_k\lvert y_{k-1}\rvert + 6k\sqrt{k}\varepsilon\|\mathbf{H}\|_2$ | the division by $\|\mathbf{x}\|$ is dropped (it is the same inequality) |
| `isUpperTriangular_gramCommutator`, `gramCommutator_sub_transpose` | `lem:gram-commutator`, `eq:generic-commutator` | identity | identity | Mathlib's `Matrix.IsUpperTriangular` |
| `specNorm_gramCommutator_le` | `cor:gram-commutator` | $\lesssim_k$; ext. $3000k^3$ | $30k^2\varepsilon\|\mathbf{H}\|_2$ | the paper bounds every entry and then passes to the Frobenius norm ($2k \cdot \max$); here the strict upper part is bounded by $\|\mathbf{M}-\mathbf{M}^{\mathsf{T}}\|_{\mathsf F}$ as a whole, and $\|\mathbf{V}_k^{\mathsf T}\mathbf{F}_k\|_{\mathsf F} \le \|\mathbf{V}_k\|_{\mathsf F}\|\mathbf{F}_k\|_{\mathsf F}$, saving a factor $k$ |
| `abs_basis_mulVec_dotProduct_mul_abs_le` | `thm:paige` | $\lesssim_k$; ext. $3000k^3$ | $30k^2\varepsilon\|\mathbf{H}\|_2$ | from the commutator bound |

**Status (2026-10-28): all headlines proved**, no `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound` only; 1.2k lines (`LocalErrors` 526, `Recurrence` 248, `Paige`
434) against the external 2.6k of the corresponding files plus their `Core/` support. Supporting
public API: `LanczosRun.ε_le`, `mul_ε_le`, `norm_v_le` ($\|\mathbf{v}_j\| \le 1 + \varepsilon/2$),
`basis_mul_tridiagonal_apply`, `norm_β_smul_v_le`, `normSqDefect`, `gramCommutator_apply_self`,
`abs_gramCommutator_apply_self_le`, `frobNorm_basis_le`,
`frobNorm_transpose_basis_mul_residual_le`,
`frobNorm_tridiagonal_mul_diagonal_sub_diagonal_mul_tridiagonal_le`,
`frobNorm_gramCommutator_sub_transpose_le`. One general fact,
`Matrix.IsUpperTriangular.frobNorm_sub_diagonal_le` (for upper triangular $\mathbf{M}$,
$\|\mathbf{M} - \operatorname{diag}\mathbf{M}\|_{\mathsf F} \le \|\mathbf{M} - \mathbf{M}^{\mathsf T}\|_{\mathsf F}$),
sits in `Paige.lean` and belongs in `NLAlib/Matrix/Norms/Frobenius.lean` when the files move
(not moved now, to avoid rebuilding the library). The duplicate report finds no class involving
the new declarations.

Simplifications against the paper's argument: the Gram-commutator bound does not need
`lem:gram-commutator`'s entrywise bound on the strict upper part (that is where the paper's
$2k\max$ and the external $k^3$ come from): the strict upper part of an upper triangular
matrix is dominated in the Frobenius norm by its skew part, which is
`gramCommutator_sub_transpose` and is bounded by Frobenius norms of products. The paper's
coefficient constants are loose because Step 2 rounds $(1+\varepsilon)^{5/2}\|\mathbf{A}\|$ to
$2\|\mathbf{A}\|$ and then the $\beta$ induction absorbs a $2\|\mathbf{A}\|$ per step; keeping
the factor near $1$ gives $\beta_j \le \tfrac54 j\|\mathbf{H}\|$. Nothing in the paper's
argument was found wrong; one point is implicit there: Step 1b needs
$\|\mathbf{v}_{k+1}\|^2 \ge 1 - \varepsilon$ at the last step, which holds only for $\beta_k \ne 0$
(the field `abs_norm_v_succ_sq_sub_one_le`), the case $\beta_k = 0$ being trivial.

Dropped from the external files as not results: `ritz_residual_bound_div` (the bound divided by
$\|\mathbf{x}\|$), the `CoefficientEnvelope` (every coefficient $\le 100j\|\mathbf{H}\|$), the
`Fmat_bound` corollary ($k^2$ for $k^{3/2}$), `ambient_pos`. The constants are literals in the
statements, as the paper's Step 4 prints its own; whether rule B (§5.2 rule 2) wants them as
named bounds is a reviewer question (recommendation: no, they are the proof's small explicit
values and nothing consumes them by name yet).

## 4. Toolkit dependencies

Present and used: `IsRelErrSem` (`sqrt_err`, `sqrt_ok`, `cmp_eq`, `re`, `neg`, `lit_err`),
`AddsZeroExactly`, `exec_dot_abs_sum_mul_sub_le`, `IsRelErrSem.exec_axpy`,
`exec_gemv_abs_mulVec_sub_le`, the γ algebra (`roundingFactor_*`,
`abs_one_add_mul_one_add_sub_one_le`).

Added with this note (2026-10-28, all **proved**, in `NLAlib/`):
* `IsRoundingProduct` with `isRoundingProduct_zero`, `isRoundingProduct_one_of_abs_le`,
  `IsRoundingProduct.abs_le` (Lemma 3.1), `.mul`, `.inv` (same length), `.div` (ratio rule
  $\theta_{k+j}$), `.mono`, `isRoundingProduct_iff` (the values fill
  $[(1-u)^j, (1-u)^{-j}]$), `exists_isRoundingProduct_sum_mul_one_add_eq` (weighted means)
  — `Computation/Rounding.lean`. The bound-only `abs_inv_one_add_sub_one_le` ($\gamma_{2j}$)
  stays, cross-referenced.
* `IsDotTrace.exists_eq_sum_mul_one_add_isRoundingProduct` (`BLAS/Traces.lean`; the existing
  `exists_eq_sum_mul_one_add` is now derived from it) and
  `IsRelErrSem.exec_dot_eq_sum_mul_one_add_isRoundingProduct` (`BLAS/RoundingErrors.lean`).
* `IsRelErrSem.exec_rscl` (`BLAS/RoundingErrors.lean`; `run_rscl` public in `BLAS.lean`).
* `IsMatvecErr`, `MatrixFreeRounded` (`Computation/Contract.lean`).
* `norm_toLp_map_abs_mulVec_abs_le` (`Matrix/Norms/Compare.lean`).

In the scaffold: `abs_norm_sq_sub_one_le_of_relErr_normalize` (**proved**),
`lanczosBasisProg_matrixFreeRounded` (**proved** from the bridge), `LanczosRun.ofLE` (**proved**).

Still missing (inside the bridge proofs): run lemmas for `copyv`, `ifThenElse` with an exact
comparison, `un` instructions, and the `apply` statement under an error contract (S each; the
store bookkeeping of the toolkit's run lemmas covers them). Not needed: `nrm2`, `scal`, a sqrt
kernel.

## 5. Open questions (each with a recommendation)

* **Q1 (L6) Basis output.** State the headlines on the `Q` output (the variant with the basis,
  $N(q+1)$ cells) or on the hidden trace of the α/β-only program? Recommended: basis variant for
  the headlines (Paige and Greenbaum are about $\mathbf{V}_{k+1}$); the α/β-only program gets the
  T-only corollaries (Ritz values) by the same proof.
* **Q2 (L3) One ε or five.** Keep the single ε of `LanczosRun` (the paper's constants unchanged)
  or generalise to per-clause $\varepsilon$'s (sharper: $\varepsilon_{\mathrm{mv}}$ appears only in
  `norm_eu_le`)? Recommended: single ε now; per-clause is a later refinement of the analysis.
* **Q3 Constant of near unit length.** Resolved (2026-10-28, maintainer's question "why weaker
  than Higham?"): $\gamma_{N+4}$ through products of rounding errors (§2.2), with a proof no longer
  than before; the bound-only route gave $\gamma_{2N+6}$.
* **Q4 Spectral measures.** Port `Measure/` (`AtomicMass`, atomic $W_1$) or restate on the
  library's `spectralMeasure`? Recommended: restate on `spectralMeasure`, with $W_1$ defined via
  1-Lipschitz test functions on finite-support measures; keep atomic lemmas private.
* **Q5 (L5) Port or depend.** Bring into NLAlib or require the external repository as a Lake
  dependency? Decided: into NLAlib, and (maintainer 2026-10-28) as a re-proof of the main results
  in library terms, not a verbatim port (§3); the external repository stays the paper's artefact.
* **Q6 Precision of $\mathbf{b}$ and $\mathbf{H}$.** All at one tag $p$. Mixed precision (matvec
  in higher precision through `convert`) changes only $\varepsilon_{\mathrm{mv}}$. Recommended:
  one tag now.
