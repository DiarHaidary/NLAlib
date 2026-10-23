/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Matrix.Factorizations.GramSchmidt

/-!
# Gram–Schmidt as a program

In-place rank-revealing modified Gram–Schmidt on the $k$ columns of an $N \times k$ buffer:
column $j$ is reduced against the earlier columns one at a time (`NLAlib.orthAgainst`,
the sweep `NLAlib.mgsSweep`), then normalised, or left zero when its squared norm is exactly zero.
In exact arithmetic the program computes `NLAlib.gramSchmidtQ` with no rank hypothesis (D6):
modified and classical Gram–Schmidt agree (`NLAlib.mgsSweep_eq_sub_sum`), and a column that
depends on the earlier ones is reduced to zero. The counts `NLAlib.gramSchmidtCount`
are those of a matrix of full column rank; each zero column saves one square root and $N$
divisions, and the realisation is an upper bound. Design: `docs/design/Computation.md` (D6, §5).

## Main definitions

* `NLAlib.orthAgainst`: one modified Gram–Schmidt sweep of a vector.
* `NLAlib.gramSchmidtProg`, `NLAlib.gramSchmidtCount`.

## Main results

* `NLAlib.exec_orthAgainst`: the sweep computes `NLAlib.mgsSweep`.
* `NLAlib.exec_gramSchmidtProg`: the program computes `NLAlib.gramSchmidtQ` from any
  state.
* `NLAlib.runsWithin_gramSchmidtProg`: the realisation from its input.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

section Programs

variable {P ι VB VI : Type}

/-- One modified Gram–Schmidt sweep, $\mathbf{v} \leftarrow \mathbf{v} -
(\mathbf{q}_i^{\mathsf{H}}\mathbf{v})\mathbf{q}_i$ for the columns $\mathbf{q}_0, \dots,
\mathbf{q}_{k-1}$ of the $N$-row buffer $Q$ in turn, each coefficient computed from the partially
reduced vector; the cell $r$ holds the coefficients. -/
def orthAgainst (p : P) (N : IExp VI) (Q : VB) (k : IExp VI) (v : VB) (vo : IExp VI)
    (r : Cell VB VI) : Builder P ι VB VI Unit :=
  forRange k fun i => do
    dot p r Q (N * .var i) v vo N
    ins (.un p .neg r r)
    axpy p r Q (N * .var i) v vo N

/-- **Gram–Schmidt as a program**: in-place rank-revealing modified Gram–Schmidt on the $k$
columns of the $N$-row buffer $Y$. Column $j$ is swept against the earlier columns, its squared
norm is computed, and it is divided by its norm unless the squared norm is exactly zero. Two
scratch cells, freed at the end (`scope`). -/
def gramSchmidtProg (p : P) (N k : IExp VI) (Y : VB) : Builder P ι VB VI Unit := scope do
  let t ← alloc p 2
  forRange k fun j => do
    orthAgainst p N Y (.var j) Y (N * .var j) ⟨t, 0⟩
    dot p ⟨t, 1⟩ Y (N * .var j) Y (N * .var j) N
    ins (.lit p ⟨t, 0⟩ 0)
    ifThenElse p .eq ⟨t, 1⟩ ⟨t, 0⟩ (pure ()) do
      ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩)
      rscl p ⟨t, 1⟩ Y (N * .var j) N

end Programs

/-- The counts of `NLAlib.gramSchmidtProg` on an $N \times k$ matrix of full column
rank, with $J = k(k-1)/2$: $2NJ + Nk$ multiplications and additions, $NJ + Nk$ conjugations,
$J$ negations, $J + 2k$ literals, $k$ comparisons and square roots, and $Nk$ divisions. -/
noncomputable def gramSchmidtCount {P ι : Type} (p : P) (N k : ℕ) : OpCount P ι :=
  Finsupp.single (.bin p .mul) (2 * N * k.choose 2 + N * k) +
  Finsupp.single (.bin p .add) (2 * N * k.choose 2 + N * k) +
  Finsupp.single (.un p .conj) (N * k.choose 2 + N * k) +
  Finsupp.single (.un p .neg) (k.choose 2) + Finsupp.single (.lit p) (k.choose 2 + 2 * k) +
  Finsupp.single (.cmp p) k + Finsupp.single (.un p .sqrt) k +
  Finsupp.single (.bin p .div) (N * k)

section Specs

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- **The sweep computes the modified Gram–Schmidt sweep** under exact arithmetic: if columns
$i < k$ of the buffer $Q$ hold $\mathbf{v}_i$, the cells of $\mathbf{v}$ hold $\mathbf{w}$ and lie
after those columns when in the same buffer, and the cell $r$ is writable and in neither, the run
leaves `mgsSweep V w k` in the cells of $\mathbf{v}$, changes no other cell but $r$ and no buffer's
tag or length, keeps the tape and the current memory, raises the peak by at most one cell, and
counts $k$ times the operations of `dot`, one negation and those of `axpy`.
[GolubVanLoan2013, §5.2.8]. -/
theorem exec_orthAgainst (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι)) {N : ℕ}
    (Q : ℕ) (k : IExp ℕ) (v : ℕ) (vo : IExp ℕ) (r : Cell ℕ ℕ) (V : ℕ → Fin N → 𝕜)
    (w : Fin N → 𝕜) (hQ : ∀ i < k.eval, ∀ a : Fin N, st.store.read p Q (N * i + a) = some (V i a))
    (hv : ∀ a : Fin N, st.store.read p v (vo.eval + a) = some (w a))
    (hvQ : v = Q → N * k.eval ≤ vo.eval) (hrv : r.buf ≠ v) (hrQ : r.buf ≠ Q)
    (hr : ∃ s, st.store.write p r.buf r.idx.eval 0 = some s) :
    ∃ st', exec I (orthAgainst p (.const N) Q k v vo r).run st = some st' ∧
      (∀ a : Fin N, st'.store.read p v (vo.eval + a) = some (mgsSweep V w k.eval a)) ∧
      (∀ q b i, (b = v → i < vo.eval ∨ vo.eval + N ≤ i) → (b = r.buf → i ≠ r.idx.eval) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + k.eval • (N • (Finsupp.single (.un p .conj) 1 +
        Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1) +
        Finsupp.single (.lit p) 1 + Finsupp.single (.un p .neg) 1 +
        N • (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p) := by
  sorry

/-- **Gram–Schmidt as a program computes `gramSchmidtQ`** from any state, under exact arithmetic:
if the buffer $Y$ holds the $N \times k$ matrix $\mathbf{M}$ from offset $0$, the run writes
`gramSchmidtQ M` over it and nothing else, keeps the tape and the current memory, raises the peak
by at most three cells and $3$ cell widths, and counts at most `gramSchmidtCount p N k`.
No rank hypothesis: a column that depends on the earlier ones becomes zero.
[GolubVanLoan2013, §5.2.8]. -/
theorem exec_gramSchmidtProg (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι)) (Y : ℕ)
    {N k : ℕ} (M : Matrix (Fin N) (Fin k) 𝕜) (hM : Holds st.store p Y 0 M) (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p Y 0 (flatten (gramSchmidtQ M)) = some s₁) :
    ∃ st', exec I (gramSchmidtProg p (.const N) (.const k) Y).run st = some st' ∧
      st'.store = s₁ ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt ≤ st.cnt + gramSchmidtCount p N k ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 3)) ∧
      st'.peakW ≤ max st.peakW (st.curW + 3 * I.width p) := by
  sorry

/-- **Gram–Schmidt as a program**: from the input buffer holding the $N \times k$ matrix
$\mathbf{Y}$ column-major, under exact arithmetic, the program runs within the counts
`gramSchmidtCount p N k` and $Nk + 3$ cells, and leaves `gramSchmidtQ Y` in the buffer.
[GolubVanLoan2013, §5.2.8]; here rank-revealing, with no rank hypothesis.
Result: gram-schmidt-program -/
theorem runsWithin_gramSchmidtProg (p : P) {N k : ℕ} (Y : Matrix (Fin N) (Fin k) 𝕜) :
    RunsWithin (exactInterp (P := P) (ι := ι) (fun _ => (0 : Matrix (Fin N) (Fin N) 𝕜))
        fun _ _ => 0)
      ((gramSchmidtProg p (.const N) (.const k) 0).run)
      (inputState p [(flatten Y).map some]) (gramSchmidtCount p N k)
      (fun q => if q = p then N * k + 3 else 0)
      (fun st => Holds st.store p 0 0 (gramSchmidtQ Y)) := by
  sorry

end Specs

end NLAlib
