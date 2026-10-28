/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Computation.BLAS.RoundingErrors
public import NLAlibScaffold.Krylov.FinitePrecision.LanczosRun
public import NLAlibScaffold.Krylov.Processes.LanczosProgramTree

/-!
# Rounding errors of the Lanczos program

A run of `NLAlib.lanczosBasisProg` (matrix-free) or `NLAlib.lanczosBasisDenseProg` (stored
matrix) in the standard model succeeds, and its outputs are the coefficients and vectors of an
`NLAlib.LanczosRun` with an explicit accuracy parameter: the analysis of
`NLAlib.Krylov.FinitePrecision` (local errors, Paige's theorem, the Greenbaum backward model)
then applies to the computed $\mathbf{T}_k$ and $\mathbf{V}_{k+1}$. The number of steps $k$ is
read off the outputs: the first $j$ with $\beta_j = 0$, or $q$.

The five error clauses of `NLAlib.LanczosRun` come from the kernels: the product from the matvec
contract `NLAlib.Computation.IsMatvecErr` (an assumption on the oracle; for the stored matrix,
from `gemv` and $\lVert\,\lvert\mathbf{H}\rvert\lvert\mathbf{x}\rvert\,\rVert \le \sqrt{N}
\lVert\mathbf{H}\rVert\lVert\mathbf{x}\rVert$), the two updates from `axpy` ($\gamma_2$), the inner
product from `dot` ($\gamma_N$, then Cauchy–Schwarz), the normalisation from `rscl` ($u$); near
unit length from `dot`, `sqrt` and `rscl` together ($\gamma_{2N+6}$). Success is unconditional in
the standard model: the only partial operation is the division by $\beta_j$, which runs only when
$\mathbf{z}_j^{\mathsf{T}}\mathbf{z}_j$ computes to a nonzero value, and then $\beta_j > 0$.

Design: `docs/design/Krylov-LanczosRounding.md` (§2).

## Main definitions

* `NLAlib.Computation.IsMatvecErr`: a normwise accuracy and success contract for an oracle.
* `NLAlib.lanczosSteps`: the number of steps before breakdown, from the computed $\beta$.
* `NLAlib.lanczosRoundingEps`: the accuracy parameter.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_rscl`: the rounding error of `rscl`.
* `NLAlib.abs_norm_sq_sub_one_le_of_relErr_normalize`: a computed normalisation is nearly unit.
* `NLAlib.norm_abs_mulVec_abs_le`: $\lVert\,\lvert\mathbf{H}\rvert\lvert\mathbf{x}\rvert\,\rVert
  \le \sqrt{N}\lVert\mathbf{H}\rVert\lVert\mathbf{x}\rVert$.
* `NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg`: the matrix-free bridge.
* `NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisDenseProg`: the dense bridge.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- **A normwise matvec contract** for oracle `o` of interpretation `I`, at tag `p`, for the
real $N \times N$ matrix $\mathbf{H}$ and accuracy $\varepsilon$: the oracle has height $N$, and on
every single column $\mathbf{x}$ of $N$ words it succeeds with $N$ words decoding to
$\mathbf{H}\mathbf{x} + \mathbf{e}$, $\lVert\mathbf{e}\rVert \le \varepsilon
\lVert\mathbf{H}\rVert\lVert\mathbf{x}\rVert$ ($\mathbf{x}$ read through the decoding). The paper's
assumption on $\mathrm{fl}(\mathbf{A}\mathbf{v})$ [Chen, `ass:arithmetic`]; oracles have no
contract in `NLAlib.Computation.IsRelErrSem` (`docs/design/Computation-Rounding.md` §5). -/
def IsMatvecErr (I : Interp P ι K C) (o : ι) (dec : P → K → ℝ) (p : P) {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ) : Prop :=
  I.height o = N ∧ ∀ X : Array K, (hX : X.size = N) → ∃ Y : Array K, ∃ hY : Y.size = N,
    I.oracle o 1 X = some Y ∧
      ‖WithLp.toLp 2 ((fun i : Fin N => dec p (Y[i.1]'(hY ▸ i.2))) -
          H *ᵥ fun i : Fin N => dec p (X[i.1]'(hX ▸ i.2)))‖ ≤
        ε * specNorm H * ‖WithLp.toLp 2 (fun i : Fin N => dec p (X[i.1]'(hX ▸ i.2)))‖

variable (I : Interp P ι K C) (p : P) {st : St P K C} {u : P → ℝ} {dec : P → K → ℝ}

/-- **Rounding error of `rscl`** in the standard model: under `NLAlib.Computation.IsRelErrSem`
with every value in range, if $a$ decodes to a nonzero $a$ and the cells of $\mathbf{x}$ hold
words decoding to $x_i$ ($i < n$), $a$ not among them, the run of `rscl` succeeds, writes words
$w_i$ into the cells of $\mathbf{x}$ and nothing else, and $w_i$ decodes to
$(x_i / a)(1 + \delta_i)$, $\lvert\delta_i\rvert \le u_p$. From the model (2.4) of
[Higham2002, §2.2]. -/
theorem IsRelErrSem.exec_rscl (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (a : Cell ℕ ℕ)
    (x : ℕ) (xo n : IExp ℕ) (av : ℝ) (xs : ℕ → ℝ) (hav : av ≠ 0)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hax : a.buf = x → ∀ i < n.eval, a.idx.eval ≠ xo.eval + i) :
    ∃ st', ∃ W : ℕ → K, exec I (rscl p a x xo n).run st = some st' ∧
      st.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∀ i < n.eval, ∃ δ : ℝ, |δ| ≤ u p ∧ dec p (W i) = xs i / av * (1 + δ) := by
  sorry

end NLAlib.Computation

namespace NLAlib

open Computation

/-- **A computed normalisation is nearly unit** (pure real): if $\mathbf{z} \ne \mathbf{0}$,
$s = \sum_i z_i^2(1 + \eta_i)$ with $\lvert\eta_i\rvert \le \gamma_n$ (a computed
$\mathbf{z}^{\mathsf{T}}\mathbf{z}$), $\beta = \sqrt{s}\,(1 + \sigma)$ with $\lvert\sigma\rvert \le
u$, and $v_i = (z_i/\beta)(1 + \delta_i)$ with $\lvert\delta_i\rvert \le u$, then $s > 0$,
$\beta > 0$ and $\lvert\lVert\mathbf{v}\rVert^2 - 1\rvert \le \gamma_{2n+6}$. Higham's
$\theta$-algebra [Higham2002, Lemma 3.3]; the constant is not sharp ($\gamma_{n+4}$ to first
order). -/
theorem abs_norm_sq_sub_one_le_of_relErr_normalize {n : ℕ} {u s β : ℝ} {z v : Fin n → ℝ}
    {η δ : Fin n → ℝ} {σ : ℝ} (hu : 0 ≤ u) (hn : ((2 * n + 6 : ℕ) : ℝ) * u < 1) (hz : z ≠ 0)
    (hη : ∀ i, |η i| ≤ roundingFactor n u) (hs : s = ∑ i, z i * z i * (1 + η i))
    (hσ : |σ| ≤ u) (hβ : β = √s * (1 + σ)) (hδ : ∀ i, |δ i| ≤ u)
    (hv : ∀ i, v i = z i / β * (1 + δ i)) :
    0 < s ∧ 0 < β ∧ |‖WithLp.toLp 2 v‖ ^ 2 - 1| ≤ roundingFactor (2 * n + 6) u := by
  sorry

/-- **The entrywise product bound**: $\lVert\,\lvert\mathbf{H}\rvert\lvert\mathbf{x}\rvert\,\rVert
\le \lVert\mathbf{H}\rVert_F\lVert\mathbf{x}\rVert \le \sqrt{N}\lVert\mathbf{H}\rVert
\lVert\mathbf{x}\rVert$ for a real $N \times N$ $\mathbf{H}$, absolute values entrywise; it turns
the componentwise `gemv` bound into the normwise one of `NLAlib.LanczosRun`. Cauchy–Schwarz by
rows, then `NLAlib.frobNorm_le_sqrt_rank_mul_specNorm` [GolubVanLoan2013, (2.3.7)]. -/
theorem norm_abs_mulVec_abs_le {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    ‖WithLp.toLp 2 (H.map abs *ᵥ fun j => |x j|)‖ ≤ √(N : ℝ) * specNorm H * ‖WithLp.toLp 2 x‖ := by
  sorry

/-- **The number of steps before breakdown**, from the computed off-diagonal coefficients
(`β j` $= \beta_{j+1}$, 0-based as the program writes them): $j + 1$ for the first $j < q$ with
$\beta_{j+1} = 0$, else $q$. -/
noncomputable def lanczosSteps (β : ℕ → ℝ) (q : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, j < q ∧ β j = 0 then Nat.find h + 1 else q

/-- **The accuracy parameter of the Lanczos program**:
$\varepsilon = \max(\varepsilon_{\mathrm{mv}}, \gamma_{2N+6}(u))$, the matvec accuracy and the
bound of the other four kernels and of the normalisation. -/
noncomputable def lanczosRoundingEps (N : ℕ) (u εmv : ℝ) : ℝ :=
  max εmv (roundingFactor (2 * N + 6) u)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- **The matrix-free Lanczos program yields a `NLAlib.LanczosRun`** in the standard model:
under `NLAlib.Computation.IsRelErrSem` with every value in range and adding zero exactly, for a
real symmetric $\mathbf{H}$ served by an oracle meeting `NLAlib.Computation.IsMatvecErr` with
accuracy $\varepsilon_{\mathrm{mv}}$, a start vector $\mathbf{b}$ of $N$ words decoding to a
nonzero vector, $q \ge 1$, $(2N+6)u_p < 1$ and $q\varepsilon \le 1/100$ for
$\varepsilon = \max(\varepsilon_{\mathrm{mv}}, \gamma_{2N+6})$, the run of $q$ steps succeeds; its
outputs decode to $\alpha_j$, $\beta_j$ ($j < q$) and $\mathbf{V}$ ($q + 1$ columns), and with
$k$ = `NLAlib.lanczosSteps β q` (the steps before breakdown) there is a run
`L : NLAlib.LanczosRun N k` with matrix $\mathbf{H}$, accuracy parameter $\varepsilon$, the
computed coefficients and Lanczos vectors, and $\mathbf{v}_1$ the computed normalisation of
$\mathbf{b}$ ($c\mathbf{v}_1 = \mathbf{b} + \boldsymbol{\delta}_0$, $c > 0$,
$\lVert\boldsymbol{\delta}_0\rVert \le u_p\lVert\mathbf{b}\rVert$); after breakdown every output is
$0$. Constructed from [Chen, `sec:model`] and [Higham2002, §§2.2, 3.1, 3.5]. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P) (o : ι)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (hH : Hᵀ = H) {εmv : ℝ}
    (hmv : IsMatvecErr I o dec p H εmv) (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0)
    (hq : 0 < q) (hu : ((2 * N + 6 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) εmv ≤ 1 / 100) :
    ∃ st', exec I (lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run
        (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      ∃ (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ),
        (∀ j < q, ∃ w, st'.store.read p 1 j = some w ∧ dec p w = α j) ∧
        (∀ j < q, ∃ w, st'.store.read p 2 j = some w ∧ dec p w = β j) ∧
        (∀ j ≤ q, ∀ i : Fin N, ∃ w, st'.store.read p 3 (i + N * j) = some w ∧ dec p w = V j i) ∧
        (∃ (c : ℝ) (δ₀ : Fin N → ℝ), 0 < c ∧ c • V 0 = (fun i => dec p (b i)) + δ₀ ∧
          ‖WithLp.toLp 2 δ₀‖ ≤ u p * ‖WithLp.toLp 2 (fun i => dec p (b i))‖) ∧
        (∀ j, lanczosSteps β q ≤ j → j < q → α j = 0 ∧ β j = 0) ∧
        ∃ L : LanczosRun N (lanczosSteps β q), L.H = H ∧
          L.ε = lanczosRoundingEps N (u p) εmv ∧
          (∀ j < lanczosSteps β q, L.α (j + 1) = α j ∧ L.β (j + 1) = β j) ∧
          ∀ j ≤ lanczosSteps β q, L.v (j + 1) = V j := by
  sorry

/-- **The dense Lanczos program yields a `NLAlib.LanczosRun`** in the standard model: as
`NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg`, with the product
computed by `gemv` from the $N \times N$ words `Hw` (buffer 0, column-major) decoding to a
symmetric $\mathbf{H}$, so $\varepsilon_{\mathrm{mv}} = \sqrt{N}\gamma_N$ and every hypothesis is
on the data, the sizes and $u_p$. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisDenseProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (Hw : Fin N → Fin N → K)
    (hH : (Matrix.of fun i j => dec p (Hw i j))ᵀ = Matrix.of fun i j => dec p (Hw i j))
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0)
    (hq : 0 < q) (hu : ((2 * N + 6 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) ≤
      1 / 100) :
    ∃ st', exec I (lanczosBasisDenseProg p (.const N) (.const q) 0 1 2 3 4).run
        (inputState p [(List.ofFn fun t : Fin (N * N) =>
            some (Hw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right
              (Nat.zero_lt_of_lt t.2))⟩ ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
          (List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      ∃ (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ),
        (∀ j < q, ∃ w, st'.store.read p 2 j = some w ∧ dec p w = α j) ∧
        (∀ j < q, ∃ w, st'.store.read p 3 j = some w ∧ dec p w = β j) ∧
        (∀ j ≤ q, ∀ i : Fin N, ∃ w, st'.store.read p 4 (i + N * j) = some w ∧ dec p w = V j i) ∧
        (∃ (c : ℝ) (δ₀ : Fin N → ℝ), 0 < c ∧ c • V 0 = (fun i => dec p (b i)) + δ₀ ∧
          ‖WithLp.toLp 2 δ₀‖ ≤ u p * ‖WithLp.toLp 2 (fun i => dec p (b i))‖) ∧
        (∀ j, lanczosSteps β q ≤ j → j < q → α j = 0 ∧ β j = 0) ∧
        ∃ L : LanczosRun N (lanczosSteps β q), L.H = Matrix.of (fun i j => dec p (Hw i j)) ∧
          L.ε = lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) ∧
          (∀ j < lanczosSteps β q, L.α (j + 1) = α j ∧ L.β (j + 1) = β j) ∧
          ∀ j ≤ lanczosSteps β q, L.v (j + 1) = V j := by
  sorry

end NLAlib
