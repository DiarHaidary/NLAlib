/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import NLAlibScaffold.Computation.BLAS
public import NLAlibScaffold.Computation.BLAS.RoundingErrors

/-!
# Triangular solve

The kernel `NLAlib.Computation.trsvLower` (forward substitution in place) under exact arithmetic
and under an error contract. Every theorem asserts that the run succeeds under hypotheses on the
inputs alone: the stored diagonal is nonzero. Under the standard model the computed solution
solves a nearby triangular system exactly, with a componentwise relative perturbation of size
$\gamma_n$ [Higham2002, Theorem 8.5]. Design: `docs/design/Computation-Rounding.md` (R5).

## Main results

* `NLAlib.Computation.exec_trsvLower`: under exact arithmetic it computes
  $\mathbf{T}^{-1}\mathbf{b}$.
* `NLAlib.Computation.IsArithErrSem.exec_trsvLower`: the run lemma, for any error relation.
* `NLAlib.Computation.IsRelErrSem.exec_trsvLower_add_mulVec_eq`: backward error,
  [Higham2002, Theorem 8.5].
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib.Computation

/-- **`trsvLower` solves a lower triangular system** under exact arithmetic: if buffer $T$ holds
the lower triangular part of the lower triangular $n \times n$ matrix $\mathbf{T}$ from
$\mathit{tOff}$ (column-major; the cells above the diagonal need not hold anything), with
nonzero diagonal, the cells of $\mathbf{x}$ hold $\mathbf{b}$, and they lie outside the block of
$\mathbf{T}$, the run writes $\mathbf{T}^{-1}\mathbf{b}$ into the cells of $\mathbf{x}$ and
nothing else, keeps the tape and the current memory, raises the peak by one cell, and counts
$n(n-1)/2$ multiplications and subtractions and $n$ divisions. The operation is in
[GolubVanLoan2013, §3.1]. -/
theorem exec_trsvLower {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]
    (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι))
    (n : IExp ℕ) (T : ℕ) (tOff : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) 𝕜) (hM : M.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, M i i ≠ 0) (b : Fin n.eval → 𝕜)
    (hT : ∀ i j : Fin n.eval, j ≤ i →
      st.store.read p T (tOff.eval + i + n.eval * j) = some (M i j))
    (hx : ∀ i : Fin n.eval, st.store.read p x (xo.eval + i) = some (b i))
    (hxT : x = T → xo.eval + n.eval ≤ tOff.eval ∨ tOff.eval + n.eval * n.eval ≤ xo.eval)
    (s₁ : Store P 𝕜) (h₁ : st.store.writeBlock p x xo.eval (Array.ofFn (M⁻¹ *ᵥ b)) = some s₁) :
    ∃ st', exec I (trsvLower p n T tOff x xo).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + ((n.eval * (n.eval - 1) / 2) • (Finsupp.single (.bin p .mul) 1 +
        Finsupp.single (.bin p .sub) 1) + n.eval • Finsupp.single (.bin p .div) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  sorry

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P)
  (st : St P K C) {dec : P → K → ℝ}

/-- **The run of `trsvLower` under an error contract**: if buffer $T$ holds words decoding to
$t_{ij}$ ($i, j < n$, column-major from $\mathit{tOff}$) with $t_{ii} \ne 0$, the cells of
$\mathbf{x}$ hold words decoding to $b_i$ and lie outside the block of $\mathbf{T}$, and on
every trace prefix the next product, difference and quotient are in range, then the run
succeeds, writes words $w_i$ into the cells of $\mathbf{x}$ and nothing else, and the decoded
$w_i$ form a trace of forward substitution under `err`. [Higham2002, Lemma 8.4], for the order
of operations of `trsvLower`. -/
theorem IsArithErrSem.exec_trsvLower {err : P → BinOp → ℝ → ℝ → Prop} {safe : P → ℝ → Prop}
    (h : IsArithErrSem err dec safe I.sem) (n : IExp ℕ) (T : ℕ) (tOff : IExp ℕ) (x : ℕ)
    (xo : IExp ℕ) (tv : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hT : ∀ i < n.eval, ∀ j ≤ i, ∃ w,
      st.store.read p T (tOff.eval + i + n.eval * j) = some w ∧ dec p w = tv i j)
    (hdiag : ∀ i < n.eval, tv i i ≠ 0)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = b i)
    (hxT : x = T → xo.eval + n.eval ≤ tOff.eval ∨ tOff.eval + n.eval * n.eval ≤ xo.eval)
    (hsafe : ∀ i < n.eval, ∀ xv : ℕ → ℝ, IsSubstTrace (err p) tv b i xv →
      (∀ k < i, ∀ s : ℕ → ℝ, IsSubstRowTrace (err p) tv b xv i k s →
        safe p (tv i k * xv k) ∧ ∀ q, err p .mul (tv i k * xv k) q → safe p (s k - q)) ∧
      ∀ s : ℕ → ℝ, IsSubstRowTrace (err p) tv b xv i i s → safe p (s i / tv i i)) :
    ∃ st', ∃ W : ℕ → K, exec I (trsvLower p n T tOff x xo).run st = some st' ∧
      st.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      IsSubstTrace (err p) tv b n.eval (fun i => dec p (W i)) := by
  sorry

/-- **Backward error of triangular solve** in the standard model [Higham2002, Theorem 8.5]:
under the contract `NLAlib.Computation.IsRelErrSem` with every value in range and $n u_p < 1$, if
buffer $T$ holds the lower triangular part of the real lower triangular $n \times n$ matrix
$\mathbf{T}$ through the decoding (column-major from $\mathit{tOff}$; the cells above the
diagonal need not hold anything) with nonzero diagonal, and the cells of $\mathbf{x}$ hold
words decoding to $\mathbf{b}$ and lie outside the block of $\mathbf{T}$, the run of
`trsvLower` succeeds, writes words $w_i$ into the cells of $\mathbf{x}$ and nothing else, and the
decoded $\hat{\mathbf{x}}$ solves a nearby system exactly: for some $\Delta\mathbf{T}$ with
$\lvert \Delta t_{ij} \rvert \le \gamma_n \lvert t_{ij} \rvert$,
$$(\mathbf{T} + \Delta\mathbf{T})\,\hat{\mathbf{x}} = \mathbf{b}\,.$$
Then $\Delta\mathbf{T}$ is lower triangular too. -/
theorem IsRelErrSem.exec_trsvLower_add_mulVec_eq {u : P → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (n : IExp ℕ) (T : ℕ) (tOff : IExp ℕ)
    (x : ℕ) (xo : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : M.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, M i i ≠ 0) (b : Fin n.eval → ℝ)
    (hn : n.eval * u p < 1)
    (hT : ∀ i j : Fin n.eval, j ≤ i → ∃ w,
      st.store.read p T (tOff.eval + i + n.eval * j) = some w ∧ dec p w = M i j)
    (hx : ∀ i : Fin n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = b i)
    (hxT : x = T → xo.eval + n.eval ≤ tOff.eval ∨ tOff.eval + n.eval * n.eval ≤ xo.eval) :
    ∃ st', ∃ W : ℕ → K, exec I (trsvLower p n T tOff x xo).run st = some st' ∧
      st.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∃ ΔT : Matrix (Fin n.eval) (Fin n.eval) ℝ,
        (∀ i j, |ΔT i j| ≤ roundingFactor n.eval (u p) * |M i j|) ∧
        (M + ΔT) *ᵥ (fun i => dec p (W i)) = b := by
  sorry

end NLAlib.Computation
