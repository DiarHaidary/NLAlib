/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlibScaffold.Computation.Contract
public import NLAlibScaffold.Computation.BLAS.Traces

/-!
# Rounding errors of the BLAS kernels

Error analyses of the library's own `dot`, `axpy`, `gemv` and `gemm` programs, in the order of
operations they execute, against an error contract on the value semantics. Every theorem
asserts that the run **succeeds**, under hypotheses on the inputs alone, and bounds the decoded
result.

Two layers. The **run lemmas** (`NLAlib.Computation.IsArithErrSem.exec_dot`, …) hold for any
error relation `err` and range condition `safe`: the run succeeds and produces a trace
(`NLAlib.Computation.IsDotTrace`), provided every operation on every trace prefix is in range.
The **standard-model theorems** (`NLAlib.Computation.IsRelErrSem.exec_dot_eq_sum_mul_one_add`,
…) take the contract `NLAlib.Computation.IsRelErrSem` with every value in range
($\mathrm{safe} = \mathrm{True}$, underflow and overflow ignored as in [Higham2002, §2.2]), where
the range hypothesis is void, and bound the trace by `NLAlib/Computation/BLAS/Traces.lean`. A
model with underflow and overflow (`docs/design/Computation-Rounding.md`, R6) reuses the run
lemmas and discharges their range hypothesis from explicit bounds on the data.

Decoded values are real: the kernels are analysed over real data. Design:
`docs/design/Computation-Rounding.md` (R3 to R5).

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_dot`, `NLAlib.Computation.IsArithErrSem.exec_axpy`,
  `NLAlib.Computation.IsArithErrSem.exec_gemv`, `NLAlib.Computation.IsArithErrSem.exec_gemm`:
  the run lemmas.
* `NLAlib.Computation.IsRelErrSem.exec_dot_eq_sum_mul_one_add`,
  `NLAlib.Computation.IsRelErrSem.exec_dot_abs_sum_mul_sub_le`: `dot`, [Higham2002, §3.1].
* `NLAlib.Computation.IsRelErrSem.exec_axpy`: `axpy`.
* `NLAlib.Computation.IsRelErrSem.exec_gemv_eq_add_mulVec`,
  `NLAlib.Computation.IsRelErrSem.exec_gemv_abs_mulVec_sub_le`: `gemv`, [Higham2002, §3.5].
* `NLAlib.Computation.IsRelErrSem.exec_gemm_abs_mul_sub_le`: `gemm`, [Higham2002, §3.5].
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P)
  (st : St P K C) {dec : P → K → ℝ}

/-! ### Run lemmas, for any error relation -/

section Runs

variable {err : P → BinOp → ℝ → ℝ → Prop} {safe : P → ℝ → Prop}

/-- **The run of `dot` under an error contract**: if the cells of $\mathbf{x}$ and $\mathbf{y}$
hold words decoding to $x_i$, $y_i$ ($i < n$), $\mathit{dst}$ is a cell of tag $p$ in neither,
adding zero is exact, and on every trace prefix the next product and sum are in range, then the
run succeeds, writes one word $w$ into $\mathit{dst}$ and nothing else, and $w$ decodes to the
last value of a trace of recursive accumulation of $\sum_{i<n} x_i y_i$ under `err`.
[Higham2002, §3.1], for the order of operations of `dot`. -/
theorem IsArithErrSem.exec_dot (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo n : IExp ℕ) (xs ys : ℕ → ℝ)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁)
    (hsafe : ∀ k < n.eval, ∀ s : ℕ → ℝ, IsDotTrace (err p) xs ys k s →
      safe p (xs k * ys k) ∧ ∀ q, err p .mul (xs k * ys k) q → safe p (s k + q)) :
    ∃ st' w, ∃ s : ℕ → ℝ, exec I (dot p dst x xo y yo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      IsDotTrace (err p) xs ys n.eval s ∧ dec p w = s n.eval := by
  sorry

/-- **The run of `axpy` under an error contract**: if $a$ and the cells of $\mathbf{x}$ and
$\mathbf{y}$ hold words decoding to $a$, $x_i$, $y_i$ ($i < n$), $a$ is not in $\mathbf{y}$,
$\mathbf{x}$ and $\mathbf{y}$ are the same vector or do not overlap, and every $a x_i$ and every
$q + y_i$ with $q$ related to $a x_i$ is in range, then the run succeeds, writes words $w_i$ into
the cells of $\mathbf{y}$ and nothing else, and $w_i$ decodes to a value related by `err` to
$q_i + y_i$ for a $q_i$ related to $a x_i$. No printed source. -/
theorem IsArithErrSem.exec_axpy (h : IsArithErrSem err dec safe I.sem) (a : Cell ℕ ℕ) (x : ℕ)
    (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (av : ℝ) (xs ys : ℕ → ℝ)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j)
    (hsafe : ∀ i < n.eval, safe p (av * xs i) ∧ ∀ q, err p .mul (av * xs i) q →
      safe p (q + ys i)) :
    ∃ st', ∃ W : ℕ → K, exec I (axpy p a x xo y yo n).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∀ i < n.eval, ∃ q, err p .mul (av * xs i) q ∧ err p .add (q + ys i) (dec p (W i)) := by
  sorry

/-- **The run of `gemv` under an error contract**: if buffer $A$ holds words decoding to
$a_{ij}$ ($i < m$, $j < n$, column-major from $\mathit{ao}$), the cells of $\mathbf{x}$ words
decoding to $x_j$, the cells of $\mathbf{y}$ are cells of tag $p$ overlapping neither, adding
zero is exact, and on every trace prefix of every row the next product and sum are in range,
then the run succeeds, writes words $w_i$ into the cells of $\mathbf{y}$ and nothing else, and
$w_i$ decodes to the last value of a trace of recursive accumulation of
$\sum_{j<n} a_{ij} x_j$. [Higham2002, §3.5], for the order of operations of `gemv`. -/
theorem IsArithErrSem.exec_gemv (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (av : ℕ → ℕ → ℝ) (xv : ℕ → ℝ)
    (hA : ∀ i < m.eval, ∀ j < n.eval, ∃ w,
      st.store.read p A (ao.eval + i + m.eval * j) = some w ∧ dec p w = av i j)
    (hx : ∀ j < n.eval, ∃ w, st.store.read p x (xo.eval + j) = some w ∧ dec p w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s₁, st.store.write p y (yo.eval + i) v = some s₁)
    (hsafe : ∀ i < m.eval, ∀ k < n.eval, ∀ s : ℕ → ℝ, IsDotTrace (err p) (av i) xv k s →
      safe p (av i k * xv k) ∧ ∀ q, err p .mul (av i k * xv k) q → safe p (s k + q)) :
    ∃ st', ∃ W : ℕ → K, ∃ s : ℕ → ℕ → ℝ, exec I (gemv p m n A ao x xo y yo).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range m.eval).toArray.map W) = some st'.store ∧
      ∀ i < m.eval, IsDotTrace (err p) (av i) xv n.eval (s i) ∧ dec p (W i) = s i n.eval := by
  sorry

/-- **The run of `gemm` under an error contract**: if buffers $A$ and $B$ hold words decoding to
$a_{ik}$ and $b_{kj}$ ($m \times n$ and $n \times l$, column-major from $\mathit{ao}$ and
$\mathit{bo}$), the block of $\mathbf{C}$ is $ml$ cells of tag $p$ overlapping neither, adding
zero is exact, and on every trace prefix of every entry the next product and sum are in range,
then the run succeeds, writes words $w_{i + mj}$ into the block of $\mathbf{C}$ and nothing else,
and $w_{i+mj}$ decodes to the last value of a trace of recursive accumulation of
$\sum_{k<n} a_{ik} b_{kj}$. [Higham2002, §3.5], for the order of operations of `gemm`. -/
theorem IsArithErrSem.exec_gemm (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ)
    (bo : IExp ℕ) (C : ℕ) (co : IExp ℕ) (av bv : ℕ → ℕ → ℝ)
    (hA : ∀ i < m.eval, ∀ k < n.eval, ∃ w,
      st.store.read p A (ao.eval + i + m.eval * k) = some w ∧ dec p w = av i k)
    (hB : ∀ k < n.eval, ∀ j < l.eval, ∃ w,
      st.store.read p B (bo.eval + k + n.eval * j) = some w ∧ dec p w = bv k j)
    (hCA : C = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : C = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hC : ∀ t < m.eval * l.eval, ∃ v s₁, st.store.write p C (co.eval + t) v = some s₁)
    (hsafe : ∀ i < m.eval, ∀ j < l.eval, ∀ k < n.eval, ∀ s : ℕ → ℝ,
      IsDotTrace (err p) (av i) (fun k => bv k j) k s →
      safe p (av i k * bv k j) ∧ ∀ q, err p .mul (av i k * bv k j) q → safe p (s k + q)) :
    ∃ st', ∃ W : ℕ → K, ∃ s : ℕ → ℕ → ℕ → ℝ,
      exec I (gemm p m n l A ao B bo C co).run st = some st' ∧
      st.store.writeBlock p C co.eval ((List.range (m.eval * l.eval)).toArray.map W) =
        some st'.store ∧
      ∀ i < m.eval, ∀ j < l.eval, IsDotTrace (err p) (av i) (fun k => bv k j) n.eval (s i j) ∧
        dec p (W (i + m.eval * j)) = s i j n.eval := by
  sorry

end Runs

/-! ### The standard model -/

section StandardModel

variable {u : P → ℝ}

/-- **Backward error of `dot`** in the standard model [Higham2002, §3.1], (3.4) there: under the
contract `NLAlib.Computation.IsRelErrSem` with every value in range, adding zero exactly, and
$n u_p < 1$, if the cells of $\mathbf{x}$ and $\mathbf{y}$ hold words decoding to $x_i$, $y_i$
($i < n$) and $\mathit{dst}$ is a cell of tag $p$ in neither, the run of `dot` succeeds, writes
one word $w$ into $\mathit{dst}$ and nothing else, and
$$w \text{ decodes to } \sum_{i<n} x_i y_i (1 + \eta_i)\,, \qquad
\lvert \eta_i \rvert \le \gamma_n\,.$$ -/
theorem IsRelErrSem.exec_dot_eq_sum_mul_one_add (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo n : IExp ℕ) (xs ys : ℕ → ℝ) (hn : n.eval * u p < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (dot p dst x xo y yo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      ∃ η : ℕ → ℝ, (∀ i < n.eval, |η i| ≤ roundingFactor n.eval (u p)) ∧
        dec p w = ∑ i ∈ range n.eval, xs i * ys i * (1 + η i) := by
  sorry

/-- **Forward error of `dot`** in the standard model [Higham2002, §3.1], (3.5) there: under the
hypotheses of `NLAlib.Computation.IsRelErrSem.exec_dot_eq_sum_mul_one_add` (the contract with
every value in range, adding zero exactly, $n u_p < 1$, decoded inputs $x_i$, $y_i$, a cell
$\mathit{dst}$ of tag $p$ in neither), the run of `dot` succeeds, writes one word $w$ into
$\mathit{dst}$ and nothing else, and
$$\Bigl\lvert \sum_{i<n} x_i y_i - w \Bigr\rvert \le \gamma_n \sum_{i<n}
\lvert x_i \rvert \lvert y_i \rvert\,,$$ with $w$ read through its decoding. -/
theorem IsRelErrSem.exec_dot_abs_sum_mul_sub_le (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo n : IExp ℕ) (xs ys : ℕ → ℝ) (hn : n.eval * u p < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (dot p dst x xo y yo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      |∑ i ∈ range n.eval, xs i * ys i - dec p w| ≤
        roundingFactor n.eval (u p) * ∑ i ∈ range n.eval, |xs i| * |ys i| := by
  sorry

/-- **Rounding error of `axpy`** in the standard model: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range and $2u_p < 1$, if $a$ and the cells
of $\mathbf{x}$ and $\mathbf{y}$ hold words decoding to $a$, $x_i$, $y_i$ ($i < n$), $a$ is not
in $\mathbf{y}$, and $\mathbf{x}$ and $\mathbf{y}$ are the same vector or do not overlap, the run
of `axpy` succeeds, writes words $w_i$ into the cells of $\mathbf{y}$ and nothing else, and
$$w_i \text{ decodes to } a x_i (1 + \theta_i) + y_i (1 + \delta_i)\,, \qquad
\lvert \theta_i \rvert \le \gamma_2\,,\quad \lvert \delta_i \rvert \le u_p\,.$$ From the model
(2.4) of [Higham2002, §2.2]. -/
theorem IsRelErrSem.exec_axpy (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (a : Cell ℕ ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (av : ℝ) (xs ys : ℕ → ℝ) (hu : 2 * u p < 1)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j) :
    ∃ st', ∃ W : ℕ → K, exec I (axpy p a x xo y yo n).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∀ i < n.eval, ∃ θ δ : ℝ, |θ| ≤ roundingFactor 2 (u p) ∧ |δ| ≤ u p ∧
        dec p (W i) = av * xs i * (1 + θ) + ys i * (1 + δ) := by
  sorry

/-- **Backward error of `gemv`** in the standard model [Higham2002, §3.5], (3.11) there: under
the contract `NLAlib.Computation.IsRelErrSem` with every value in range, adding zero exactly, and
$n u_p < 1$, if buffer $A$ holds the real $m \times n$ matrix $\mathbf{A}$ through the decoding
(column-major from $\mathit{ao}$), the cells of $\mathbf{x}$ hold words decoding to
$\mathbf{x}$, and the cells of $\mathbf{y}$ are cells of tag $p$ overlapping neither, the run of
`gemv` succeeds, writes words $w_i$ into the cells of $\mathbf{y}$ and nothing else, and for some
$\Delta\mathbf{A}$ with $\lvert \Delta a_{ij} \rvert \le \gamma_n \lvert a_{ij} \rvert$,
$$w_i \text{ decodes to } \bigl((\mathbf{A} + \Delta\mathbf{A})\mathbf{x}\bigr)_i\,.$$ -/
theorem IsRelErrSem.exec_gemv_eq_add_mulVec (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (xv : Fin n.eval → ℝ)
    (hn : n.eval * u p < 1) (hA : HoldsDecoded st.store dec p A ao.eval M)
    (hx : ∀ j : Fin n.eval, ∃ w, st.store.read p x (xo.eval + j) = some w ∧ dec p w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s₁, st.store.write p y (yo.eval + i) v = some s₁) :
    ∃ st', ∃ W : ℕ → K, exec I (gemv p m n A ao x xo y yo).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range m.eval).toArray.map W) = some st'.store ∧
      ∃ ΔA : Matrix (Fin m.eval) (Fin n.eval) ℝ,
        (∀ i j, |ΔA i j| ≤ roundingFactor n.eval (u p) * |M i j|) ∧
        ∀ i : Fin m.eval, dec p (W i) = ((M + ΔA) *ᵥ xv) i := by
  sorry

/-- **Forward error of `gemv`** in the standard model [Higham2002, §3.5], (3.12) there: under
the hypotheses of `NLAlib.Computation.IsRelErrSem.exec_gemv_eq_add_mulVec` (the contract with
every value in range, adding zero exactly, $n u_p < 1$, $\mathbf{A}$ and $\mathbf{x}$ stored
through the decoding, $\mathbf{y}$ cells of tag $p$ overlapping neither), the run of `gemv`
succeeds, writes words $w_i$ into the cells of $\mathbf{y}$ and nothing else, and
$$\bigl\lvert (\mathbf{A}\mathbf{x})_i - w_i \bigr\rvert \le
\gamma_n \bigl(\lvert \mathbf{A} \rvert \lvert \mathbf{x} \rvert\bigr)_i\,,$$ with $w_i$ read
through its decoding and absolute values entrywise. -/
theorem IsRelErrSem.exec_gemv_abs_mulVec_sub_le (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (xv : Fin n.eval → ℝ)
    (hn : n.eval * u p < 1) (hA : HoldsDecoded st.store dec p A ao.eval M)
    (hx : ∀ j : Fin n.eval, ∃ w, st.store.read p x (xo.eval + j) = some w ∧ dec p w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s₁, st.store.write p y (yo.eval + i) v = some s₁) :
    ∃ st', ∃ W : ℕ → K, exec I (gemv p m n A ao x xo y yo).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range m.eval).toArray.map W) = some st'.store ∧
      ∀ i : Fin m.eval, |(M *ᵥ xv) i - dec p (W i)| ≤
        roundingFactor n.eval (u p) * ((M.map abs) *ᵥ (fun j => |xv j|)) i := by
  sorry

/-- **Forward error of `gemm`** in the standard model [Higham2002, §3.5], (3.13) there: under
the contract `NLAlib.Computation.IsRelErrSem` with every value in range, adding zero exactly, and
$n u_p < 1$, if buffers $A$ and $B$ hold the real $m \times n$ and $n \times l$ matrices
$\mathbf{A}$, $\mathbf{B}$ through the decoding (column-major from $\mathit{ao}$, $\mathit{bo}$)
and the block of $\mathbf{C}$ is $ml$ cells of tag $p$ overlapping neither, the run of `gemm`
succeeds, writes words $w_{i+mj}$ into the block of $\mathbf{C}$ and nothing else, and
$$\bigl\lvert (\mathbf{A}\mathbf{B})_{ij} - w_{i+mj} \bigr\rvert \le
\gamma_n \bigl(\lvert \mathbf{A} \rvert \lvert \mathbf{B} \rvert\bigr)_{ij}\,,$$ with
$w_{i+mj}$ read through its decoding and absolute values entrywise. -/
theorem IsRelErrSem.exec_gemm_abs_mul_sub_le (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ)
    (bo : IExp ℕ) (C : ℕ) (co : IExp ℕ) (MA : Matrix (Fin m.eval) (Fin n.eval) ℝ)
    (MB : Matrix (Fin n.eval) (Fin l.eval) ℝ) (hn : n.eval * u p < 1)
    (hA : HoldsDecoded st.store dec p A ao.eval MA) (hB : HoldsDecoded st.store dec p B bo.eval MB)
    (hCA : C = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : C = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hC : ∀ t < m.eval * l.eval, ∃ v s₁, st.store.write p C (co.eval + t) v = some s₁) :
    ∃ st', ∃ W : ℕ → K, exec I (gemm p m n l A ao B bo C co).run st = some st' ∧
      st.store.writeBlock p C co.eval ((List.range (m.eval * l.eval)).toArray.map W) =
        some st'.store ∧
      ∀ (i : Fin m.eval) (j : Fin l.eval), |(MA * MB) i j - dec p (W (i + m.eval * j))| ≤
        roundingFactor n.eval (u p) * (MA.map abs * MB.map abs) i j := by
  sorry

end StandardModel

end NLAlib.Computation
