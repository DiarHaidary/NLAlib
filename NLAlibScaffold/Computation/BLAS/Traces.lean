/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Syntax
public import NLAlibScaffold.Computation.Rounding

/-!
# Rounding traces of the BLAS kernels

A run of a kernel under an error contract computes, in decoded values, a **trace**: the sequence
of intermediate values of the kernel's recursion, each operation's result related to the exact
result on the previous values by an error relation `err`. The run lemmas of
`NLAlib/Computation/BLAS/RoundingErrors.lean` and `NLAlib/Computation/BLAS/Triangular.lean`
prove that the run produces a trace; this file bounds traces, with no program in sight. Under the
standard model (`err` the relation `NLAlib.Computation.relErr u` of relative error) the
bounds are those of [Higham2002, Chapters 3 and 8]. A model with underflow reuses them: an
absolute error in a multiplication or division is pushed onto its operands
(`docs/design/Computation-Rounding.md`, R6).

## Main definitions

* `NLAlib.Computation.IsDotTrace`: recursive accumulation of $\sum_k x_k y_k$, as `dot` and
  each row of `gemv` and `gemm` compute it.
* `NLAlib.Computation.IsSubstRowTrace`, `NLAlib.Computation.IsSubstTrace`: forward
  substitution, as `trsvLower` computes it.

## Main results

* `NLAlib.Computation.IsDotTrace.exists_eq_sum_mul_one_add`: backward error of an inner
  product, [Higham2002, §3.1].
* `NLAlib.Computation.IsDotTrace.abs_sum_mul_sub_le`: forward error of an inner product.
* `NLAlib.Computation.exists_eq_mul_one_add_add_mul_one_add_of_relErr`: one `axpy` entry.
* `NLAlib.Computation.IsSubstTrace.exists_sum_add_mul_eq`: backward error of forward
  substitution, [Higham2002, Theorem 8.5].
-/

@[expose] public section

namespace NLAlib.Computation

open Finset

/-- **A trace of recursive accumulation** of $\sum_{k<n} x_k y_k$ under the error relation
`err`: $s_0 = 0$ and, for each $k < n$, a product $q_k$ related by `err` to $x_k y_k$ and
$s_{k+1}$ related by `err` to $s_k + q_k$, equal to $q_k$ when $s_k = 0$ (adding zero is
exact). This is what `dot` computes, and what `gemv` computes in each entry. -/
def IsDotTrace (err : BinOp → ℝ → ℝ → Prop) (x y : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : Prop :=
  s 0 = 0 ∧ ∀ k < n, ∃ q : ℝ, err .mul (x k * y k) q ∧ err .add (s k + q) (s (k + 1)) ∧
    (s k = 0 → s (k + 1) = q)

/-- **A partial trace of one row of forward substitution**: row $i$ of the lower triangular
system with entries $t_{ij}$, right side $b$ and computed solution $x$, after $k$ steps, under
the error relation `err`: $s_0 = b_i$ and, for each $j < k$, a product $q_j$ related to
$t_{ij}x_j$ and $s_{j+1}$ related to $s_j - q_j$. -/
def IsSubstRowTrace (err : BinOp → ℝ → ℝ → Prop) (t : ℕ → ℕ → ℝ) (b x : ℕ → ℝ) (i k : ℕ)
    (s : ℕ → ℝ) : Prop :=
  s 0 = b i ∧ ∀ j < k, ∃ q : ℝ, err .mul (t i j * x j) q ∧ err .sub (s j - q) (s (j + 1))

/-- **A trace of forward substitution** for the lower triangular system with entries $t_{ij}$
and right side $b$, under the error relation `err`: for each row $i < n$, a full row trace $s$
(`NLAlib.Computation.IsSubstRowTrace` after $i$ steps) and $x_i$ related to $s_i/t_{ii}$. This is
what `trsvLower` computes. -/
def IsSubstTrace (err : BinOp → ℝ → ℝ → Prop) (t : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ)
    (x : ℕ → ℝ) : Prop :=
  ∀ i < n, ∃ s : ℕ → ℝ, IsSubstRowTrace err t b x i i s ∧ err .div (s i / t i i) (x i)

variable {u : ℝ} {n : ℕ}

/-- **Backward error of an inner product** [Higham2002, §3.1], (3.4) there: under the standard
model with unit roundoff $0 \le u$, $nu < 1$, the result $s_n$ of a trace of recursive
accumulation is the exact inner product of slightly perturbed data,
$$s_n = \sum_{k<n} x_k y_k (1 + \eta_k)\,, \qquad \lvert \eta_k \rvert \le \gamma_n\,.$$ -/
theorem IsDotTrace.exists_eq_sum_mul_one_add {x y s : ℕ → ℝ}
    (h : IsDotTrace (fun _ => relErr u) x y n s) (hu : 0 ≤ u) (hn : n * u < 1) :
    ∃ η : ℕ → ℝ, (∀ k < n, |η k| ≤ roundingFactor n u) ∧
      s n = ∑ k ∈ range n, x k * y k * (1 + η k) := by
  sorry

/-- **Forward error of an inner product** [Higham2002, §3.1], (3.5) there: under the standard
model with $0 \le u$, $nu < 1$,
$$\Bigl\lvert \sum_{k<n} x_k y_k - s_n \Bigr\rvert \le \gamma_n \sum_{k<n}
\lvert x_k \rvert \lvert y_k \rvert\,.$$ -/
theorem IsDotTrace.abs_sum_mul_sub_le {x y s : ℕ → ℝ}
    (h : IsDotTrace (fun _ => relErr u) x y n s) (hu : 0 ≤ u) (hn : n * u < 1) :
    |∑ k ∈ range n, x k * y k - s n| ≤ roundingFactor n u * ∑ k ∈ range n, |x k| * |y k| := by
  sorry

/-- **One entry of `axpy`** under the standard model: if $q$ is $ax$ with relative error at most
$u$ and $z$ is $q + y$ with relative error at most $u$, $0 \le u$ and $2u < 1$, then
$$z = ax(1 + \theta) + y(1 + \delta)\,, \qquad \lvert \theta \rvert \le \gamma_2\,,\quad
\lvert \delta \rvert \le u\,.$$ From the model (2.4) of [Higham2002, §2.2] and
[Higham2002, Lemma 3.1]. -/
theorem exists_eq_mul_one_add_add_mul_one_add_of_relErr {a x y q z : ℝ} (hq : relErr u (a * x) q)
    (hz : relErr u (q + y) z) (hu : 0 ≤ u) (hu2 : 2 * u < 1) :
    ∃ θ δ : ℝ, |θ| ≤ roundingFactor 2 u ∧ |δ| ≤ u ∧ z = a * x * (1 + θ) + y * (1 + δ) := by
  sorry

/-- **Backward error of forward substitution** [Higham2002, Theorem 8.5], from
[Higham2002, Lemma 8.4]: under the standard model with $0 \le u$ and $nu < 1$, if every
diagonal entry $t_{ii}$ ($i < n$) is nonzero, a trace $\hat{x}$ of forward substitution solves a
nearby system exactly: for some $\Delta t_{ij}$ with
$\lvert \Delta t_{ij} \rvert \le \gamma_n \lvert t_{ij} \rvert$ ($j \le i < n$),
$$\sum_{j \le i} (t_{ij} + \Delta t_{ij})\,\hat{x}_j = b_i \qquad (i < n)\,.$$ -/
theorem IsSubstTrace.exists_sum_add_mul_eq {t : ℕ → ℕ → ℝ} {b x : ℕ → ℝ}
    (h : IsSubstTrace (fun _ => relErr u) t b n x) (hdiag : ∀ i < n, t i i ≠ 0) (hu : 0 ≤ u)
    (hn : n * u < 1) :
    ∃ Δ : ℕ → ℕ → ℝ, (∀ i < n, ∀ j ≤ i, |Δ i j| ≤ roundingFactor n u * |t i j|) ∧
      ∀ i < n, ∑ j ∈ range (i + 1), (t i j + Δ i j) * x j = b i := by
  sorry

end NLAlib.Computation
