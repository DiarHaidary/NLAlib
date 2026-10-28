/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.Matrix.Norms.Compare
public import NLAlibScaffold.Krylov.FinitePrecision.LanczosRun
public import NLAlibScaffold.Krylov.Processes.LanczosProgramTree

/-!
# Rounding errors of the Lanczos program

A run of `NLAlib.lanczosBasisProg` (matrix-free) or `NLAlib.lanczosBasisDenseProg` (stored
matrix) in the standard model succeeds, and its outputs are the coefficients and vectors of an
`NLAlib.LanczosRun` with an explicit accuracy parameter: the stability analysis of
`NLAlib.Krylov.FinitePrecision` then applies to the computed $\mathbf{T}_k$ and
$\mathbf{V}_{k+1}$. The number of steps $k$ is read off the outputs: the first $j$ with
$\beta_j = 0$, or $q$.

The five error clauses of `NLAlib.LanczosRun` come from the kernels: the product from the matvec
contract `NLAlib.Computation.IsMatvecErr` (an assumption on the oracle; for the stored matrix,
from `gemv` and `NLAlib.norm_toLp_map_abs_mulVec_abs_le`), the two updates from `axpy`
($\gamma_2$), the inner product from `dot` ($\gamma_N$, then Cauchy–Schwarz), the normalisation
from `rscl` ($u$); near unit length from `dot`, `sqrt` and `rscl` together, through products of
rounding errors (`NLAlib.Computation.IsRoundingProduct`): $\gamma_{N+4}$, Higham's count. Success
is unconditional in the standard model: the only partial operations are the square root of the
computed $\mathbf{z}^{\mathsf{T}}\mathbf{z} \ge 0$ and the division by $\beta_j$, which runs only
when $\beta_j$ computes to a nonzero value.

The matrix-free headline is an instance of the access model
`NLAlib.Computation.MatrixFreeRounded` (`NLAlib.lanczosBasisProg_matrixFreeRounded`).
Design: `docs/design/Krylov-LanczosRounding.md` (§2).

## Main definitions

* `NLAlib.lanczosSteps`: the number of steps before breakdown, from the computed $\beta$.
* `NLAlib.lanczosRoundingEps`: the accuracy parameter.
* `NLAlib.LanczosOutputs`: the output buffers decode to $\alpha$, $\beta$, $\mathbf{V}$.
* `NLAlib.HasLanczosRunOutputs`: the outputs of a final state form a `NLAlib.LanczosRun`.

## Main results

* `NLAlib.abs_norm_sq_sub_one_le_of_relErr_normalize`: a computed normalisation is nearly unit.
* `NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg`: the matrix-free bridge.
* `NLAlib.lanczosBasisProg_matrixFreeRounded`: the same as an instance of the access model.
* `NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisDenseProg`: the dense bridge.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib

open Computation

/-- **A computed normalisation is nearly unit** (pure real): if $\mathbf{z} \ne \mathbf{0}$,
$s = \sum_i z_i^2(1 + \eta_i)$ with each $1 + \eta_i$ a product of $n$ factors
$(1 + \delta)^{\pm 1}$, $\lvert \delta \rvert \le u$ (a computed
$\mathbf{z}^{\mathsf{T}}\mathbf{z}$, `NLAlib.Computation.IsRoundingProduct`),
$\beta = \sqrt{s}\,(1 + \sigma)$ with $\lvert\sigma\rvert \le u$,
$v_i = (z_i/\beta)(1 + \delta_i)$ with $\lvert\delta_i\rvert \le u$, $0 \le u$ and
$(n + 4)u < 1$, then $s > 0$, $\beta > 0$ and
$\lvert\lVert\mathbf{v}\rVert^2 - 1\rvert \le \gamma_{n+4}$: $\lVert\mathbf{v}\rVert^2$ is the
ratio of a weighted mean of $(1 + \delta_i)^2$ (two factors) to a weighted mean of
$1 + \eta_i$ ($n$ factors) times $(1 + \sigma)^2$ (two), $n + 4$ factors in all
[Higham2002, Lemmas 3.1 and 3.3]. -/
theorem abs_norm_sq_sub_one_le_of_relErr_normalize {n : ℕ} {u s β : ℝ} {z v : Fin n → ℝ}
    {η δ : Fin n → ℝ} {σ : ℝ} (hu : 0 ≤ u) (hn : ((n + 4 : ℕ) : ℝ) * u < 1) (hz : z ≠ 0)
    (hη : ∀ i, IsRoundingProduct u n (η i)) (hs : s = ∑ i, z i * z i * (1 + η i))
    (hσ : |σ| ≤ u) (hβ : β = √s * (1 + σ)) (hδ : ∀ i, |δ i| ≤ u)
    (hv : ∀ i, v i = z i / β * (1 + δ i)) :
    0 < s ∧ 0 < β ∧ |‖WithLp.toLp 2 v‖ ^ 2 - 1| ≤ roundingFactor (n + 4) u := by
  have hu1 : u < 1 := by
    have : (1 : ℝ) * u ≤ ((n + 4 : ℕ) : ℝ) * u := by gcongr; norm_cast; omega
    linarith
  have hZ : 0 < ∑ i, z i * z i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    exact (mul_self_pos.mpr hi).trans_le
      (single_le_sum (fun j _ => mul_self_nonneg (z j)) (mem_univ i))
  obtain ⟨η', hη', hsη⟩ := exists_isRoundingProduct_sum_mul_one_add_eq hu hu1 univ
    (fun i => z i * z i) η (fun i _ => mul_self_nonneg _) (fun i _ => hη i)
  have h1η : 0 < 1 + η' :=
    (pow_pos (by linarith) n).trans_le ((isRoundingProduct_iff hu hu1).mp hη').1
  have hs' : s = (∑ i, z i * z i) * (1 + η') := hs.trans hsη
  have hspos : 0 < s := by rw [hs']; positivity
  have h1σ : 0 < 1 + σ := by linarith [neg_abs_le σ]
  have hβpos : 0 < β := by rw [hβ]; exact mul_pos (Real.sqrt_pos.mpr hspos) h1σ
  refine ⟨hspos, hβpos, ?_⟩
  have hδ2 := fun i => (isRoundingProduct_one_of_abs_le (hδ i)).mul
    (isRoundingProduct_one_of_abs_le (hδ i))
  obtain ⟨φ, hφ, hφeq⟩ := exists_isRoundingProduct_sum_mul_one_add_eq hu hu1 univ
    (fun i => z i * z i) _ (fun i _ => mul_self_nonneg _) (fun i _ => hδ2 i)
  have hβsq : β ^ 2 = s * (1 + σ) ^ 2 := by rw [hβ, mul_pow, Real.sq_sqrt hspos.le]
  have hsum : ∑ i, v i ^ 2 =
      (∑ i, z i * z i * (1 + ((1 + δ i) * (1 + δ i) - 1))) / β ^ 2 := by
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [hv]
    field_simp
    ring
  have key : ‖WithLp.toLp 2 v‖ ^ 2 = (1 + φ) / ((1 + η') * (1 + σ) * (1 + σ)) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [hsum, hφeq, hβsq, hs', div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hR := hφ.div ((hη'.mul (isRoundingProduct_one_of_abs_le hσ)).mul
    (isRoundingProduct_one_of_abs_le hσ))
  rw [show 2 + (n + 1 + 1) = n + 4 by omega] at hR
  simp only [add_sub_cancel] at hR
  rw [key]
  exact hR.abs_le hn

/-- **The number of steps before breakdown**, from the computed off-diagonal coefficients
(`β j` $= \beta_{j+1}$, 0-based as the program writes them): $j + 1$ for the first $j < q$ with
$\beta_{j+1} = 0$, else $q$. -/
noncomputable def lanczosSteps (β : ℕ → ℝ) (q : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, j < q ∧ β j = 0 then Nat.find h + 1 else q

/-- **The accuracy parameter of the Lanczos program**:
$\varepsilon = \max(\varepsilon_{\mathrm{mv}}, \gamma_{N+4}(u))$, the matvec accuracy and the
bound of the other four kernels ($u$, $\gamma_2$, $\gamma_N \le \gamma_{N+4}$) and of the
normalisation ($\gamma_{N+4}$). -/
noncomputable def lanczosRoundingEps (N : ℕ) (u εmv : ℝ) : ℝ :=
  max εmv (roundingFactor (N + 4) u)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- **The outputs of the Lanczos program**: in state `st`, at tag `p` and decoding `dec`, the
buffers `alpha` and `beta` hold words decoding to $\alpha_j$, $\beta_j$ ($j < q$) and buffer `Q`
holds $q + 1$ columns of $N$ words decoding to $\mathbf{V}_j$ ($j \le q$, column-major). -/
def LanczosOutputs (st : St P K C) (p : P) (dec : P → K → ℝ) (alpha beta Q : ℕ) {N : ℕ}
    (q : ℕ) (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ) : Prop :=
  (∀ j < q, ∃ w, st.store.read p alpha j = some w ∧ dec p w = α j) ∧
  (∀ j < q, ∃ w, st.store.read p beta j = some w ∧ dec p w = β j) ∧
  (∀ j ≤ q, ∀ i : Fin N, ∃ w, st.store.read p Q (i + N * j) = some w ∧ dec p w = V j i)

/-- **The outputs of a Lanczos run form a `NLAlib.LanczosRun`**: the output buffers of `st`
decode to $\alpha$, $\beta$, $\mathbf{V}$ (`NLAlib.LanczosOutputs`); $\mathbf{v}_1$ is a
computed normalisation of $\mathbf{b}$ ($c\mathbf{v}_1 = \mathbf{b} + \boldsymbol{\delta}_0$,
$c > 0$, $\lVert\boldsymbol{\delta}_0\rVert \le u\lVert\mathbf{b}\rVert$); with
$k$ = `NLAlib.lanczosSteps β q`, every later output is $0$ ($\alpha_j = \beta_j = 0$ for
$k \le j < q$, and $\mathbf{V}_j = \mathbf{0}$ for $k \le j \le q$ when the last step is
terminal, the convention $\mathbf{v}_{k+1} = \mathbf{0}$ of [Chen, `sec:model`]); and there is a
run `L : NLAlib.LanczosRun N k` with matrix $\mathbf{H}$, accuracy parameter $\varepsilon$, the
computed coefficients ($L.\alpha_{j+1} = \alpha_j$, $L.\beta_{j+1} = \beta_j$, $j < k$) and the
computed vectors ($L.\mathbf{v}_{j+1} = \mathbf{V}_j$, $j \le k$). -/
def HasLanczosRunOutputs (st : St P K C) (p : P) (dec : P → K → ℝ) (u ε : ℝ)
    (alpha beta Q : ℕ) {N : ℕ} (q : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) : Prop :=
  ∃ (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ), LanczosOutputs st p dec alpha beta Q q α β V ∧
    (∃ (c : ℝ) (δ₀ : Fin N → ℝ), 0 < c ∧ c • V 0 = b + δ₀ ∧
      ‖WithLp.toLp 2 δ₀‖ ≤ u * ‖WithLp.toLp 2 b‖) ∧
    (∀ j, lanczosSteps β q ≤ j → j < q → α j = 0 ∧ β j = 0) ∧
    (β (lanczosSteps β q - 1) = 0 → ∀ j, lanczosSteps β q ≤ j → j ≤ q → V j = 0) ∧
    ∃ L : LanczosRun N (lanczosSteps β q), L.H = H ∧ L.ε = ε ∧
      (∀ j < lanczosSteps β q, L.α (j + 1) = α j ∧ L.β (j + 1) = β j) ∧
      ∀ j ≤ lanczosSteps β q, L.v (j + 1) = V j

/-- **The matrix-free Lanczos program yields a `NLAlib.LanczosRun`** in the standard model:
under `NLAlib.Computation.IsRelErrSem` with every value in range and adding zero exactly, for a
real symmetric $\mathbf{H}$ served by an oracle meeting `NLAlib.Computation.IsMatvecErr` with
bound $\varepsilon_{\mathrm{mv}}\lVert\mathbf{H}\rVert_2$, a start vector $\mathbf{b}$ of $N$
words decoding to a nonzero vector, $q \ge 1$, $(N + 4)u_p < 1$ and $q\varepsilon \le 1/100$ for
$\varepsilon = \max(\varepsilon_{\mathrm{mv}}, \gamma_{N+4})$, the run of $q$ steps succeeds and
its outputs form a run `L : NLAlib.LanczosRun N k` with accuracy parameter $\varepsilon$,
$k$ the steps before breakdown, the computed coefficients and vectors, $\mathbf{v}_1$ the
computed normalisation of $\mathbf{b}$, and every output after breakdown $0$
(`NLAlib.HasLanczosRunOutputs`). The hypothesis $(N + 4)u_p < 1$ is not implied by
$q\varepsilon \le 1/100$: $\gamma_{N+4}$ is negative past $(N + 4)u_p = 1$. Constructed from
[Chen, `sec:model`] and [Higham2002, §§2.2, 3.1, Lemma 3.3]. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P) (o : ι)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (hH : Hᵀ = H) {εmv : ℝ}
    (hmv : IsMatvecErr I o dec p H (εmv * specNorm H)) (b : Fin N → K)
    (hb : (fun i => dec p (b i)) ≠ 0) (hq : 0 < q) (hu : ((N + 4 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) εmv ≤ 1 / 100) :
    ∃ st', exec I (lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run
        (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      HasLanczosRunOutputs st' p dec (u p) (lanczosRoundingEps N (u p) εmv) 1 2 3 q H
        fun i => dec p (b i) := by
  sorry

/-- **The matrix-free Lanczos program in the access model**: the headline
`NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg` as an instance of
`NLAlib.Computation.MatrixFreeRounded` with one size parameter $q \ge 1$, the input
$\mathbf{b}$ (with empty output buffers), matvec bound $\varepsilon_{\mathrm{mv}}
\lVert\mathbf{H}\rVert_2$, precondition $\mathbf{H}^{\mathsf{T}} = \mathbf{H}$,
$\mathbf{b} \ne \mathbf{0}$ (decoded), $(N + 4)u_p < 1$, $q\varepsilon \le 1/100$, and
postcondition `NLAlib.HasLanczosRunOutputs` with $\varepsilon = \max(\varepsilon_{\mathrm{mv}},
\gamma_{N+4})$. [Chen, `sec:model`], [Higham2002, §§2.2, 3.1, Lemma 3.3]. -/
theorem lanczosBasisProg_matrixFreeRounded (p : P) (o : ι) (u : P → ℝ) (dec : P → K → ℝ)
    (εmv : ℝ) :
    MatrixFreeRounded (C := C) (r := 1) (b := 4) p
      (fun N n => (lanczosBasisProg p o (.const N) (.const (n 0)) 0 1 2 3).run)
      (fun _ n => 0 < n 0) (fun N _ => Fin N → K)
      (fun N n b => ![(List.ofFn fun i => some (b i)).toArray, Array.replicate (n 0) none,
        Array.replicate (n 0) none, Array.replicate (N * (n 0 + 1)) none])
      u dec (fun _ _ H => εmv * specNorm H)
      (fun N n b H => Hᵀ = H ∧ (fun i => dec p (b i)) ≠ 0 ∧ ((N + 4 : ℕ) : ℝ) * u p < 1 ∧
        (n 0 : ℝ) * lanczosRoundingEps N (u p) εmv ≤ 1 / 100)
      (fun N n b H st => HasLanczosRunOutputs st p dec (u p) (lanczosRoundingEps N (u p) εmv)
        1 2 3 (n 0) H fun i => dec p (b i)) := by
  intro N n hn b H I h hz hmv ⟨hH, hb, hu, hsmall⟩
  simpa [List.ofFn_succ] using
    IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg I p o h hz (n 0) H hH (hmv o) b hb hn hu
      hsmall

/-- **The dense Lanczos program yields a `NLAlib.LanczosRun`** in the standard model: under
`NLAlib.Computation.IsRelErrSem` with every value in range and adding zero exactly, with the
product computed by `gemv` from the $N \times N$ words `Hw` (buffer 0, column-major) decoding to
a symmetric $\mathbf{H}$, a start vector $\mathbf{b}$ of $N$ words decoding to a nonzero
vector, $q \ge 1$, $(N + 4)u_p < 1$ and $q\varepsilon \le 1/100$ for
$\varepsilon = \max(\sqrt{N}\gamma_N, \gamma_{N+4})$, the run of $q$ steps succeeds and its
outputs form a run `L : NLAlib.LanczosRun N k` as in
`NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg`
(`NLAlib.HasLanczosRunOutputs`); every hypothesis is on the data, the sizes and $u_p$.
[Chen, `sec:model`], [Higham2002, §§2.2, 3.1, 3.5, Lemma 3.3]. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisDenseProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (Hw : Fin N → Fin N → K)
    (hH : (Matrix.of fun i j => dec p (Hw i j))ᵀ = Matrix.of fun i j => dec p (Hw i j))
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0)
    (hq : 0 < q) (hu : ((N + 4 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) ≤
      1 / 100) :
    ∃ st', exec I (lanczosBasisDenseProg p (.const N) (.const q) 0 1 2 3 4).run
        (inputState p [(List.ofFn fun t : Fin (N * N) =>
            some (Hw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right
              (Nat.zero_lt_of_lt t.2))⟩ ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
          (List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      HasLanczosRunOutputs st' p dec (u p)
        (lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p))) 2 3 4 q
        (Matrix.of fun i j => dec p (Hw i j)) fun i => dec p (b i) := by
  sorry

end NLAlib
