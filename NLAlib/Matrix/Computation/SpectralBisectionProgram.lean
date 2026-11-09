/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Refinement

/-!
# The spectral bisection program computes `eigh`

The refinement of the program `NLAlib.eighProg` to the shallow `NLAlib.eigh`: (a) under kernels that
are routines on pairs, a semantics that decides flags, exact integer literals up to $n + 4$ and the
exact floor conversion, **every successful run writes exactly `NLAlib.eigh`** on the machine of the
interpretation (`NLAlib.eighTapeMachine`) with the tree of samples at the slots
(`NLAlib.holds_of_exec_eighProg`); (b) under the standard model with every value in range, $u < 1$,
$\ell_0 \ge 1$ and $\varepsilon, R_0 \ge 0$, **every run succeeds** (the sign step has the shallow
step limit, so no run fails for want of steps). Both for the builder and for the registered tree
`NLAlib.eighProg.compiled`; its counts are in
`NLAlib/Matrix/Computation/SpectralBisectionProgram/Count.lean` and `…/Weight.lean`.

## Main results

* `NLAlib.exists_exec_eighProg`: every run succeeds.
* `NLAlib.eighProg.toStmt_compiled`, `NLAlib.eighProg.holds_of_exec_compiled`,
  `NLAlib.eighProg.exists_exec_compiled`: the registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-- The refinement of the spectral bisection program, success: under the standard model at $u$
with every value in range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor
conversion, if the kernels `mm`, `qr` of `I` are routines on interleaved pairs, $\ell_0 \ge 1$,
$R_0$ decodes to a nonnegative value, and the buffers `U`, `dv` at tag `p` have
$2n^2$ and $n$ cells, then every run of `NLAlib.eighProg` succeeds from a state with the tape
positions at $0$, whose buffers `A`, `par`, `U`, `dv` exist, whose block at offset $0$ of
`A` holds the stored $\mathbf{A}$ and whose cells $0$, $1$, $2$ of `par` hold $R_0$,
$\varepsilon$, $\beta$. No printed source. -/
theorem exists_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (hℓ : 1 ≤ ℓ₀) {A par U dv : ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hR₀ : 0 ≤ dec p R₀)
    (hsize : ∀ j ∈ [A, par, U, dv], j < st.store.size)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (hU : ∃ len, st.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, st.store.shape[dv]? = some (p, len) ∧ n ≤ len) :
    ∃ st', exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st' := by
  obtain ⟨lU, hlU, hUle⟩ := hU
  obtain ⟨ldv, hldv, hdvle⟩ := hdv
  obtain ⟨st', hrun, -⟩ := (spec_eighProg hmm hqr .total (safe := fun _ _ => True) p n ℓ₀ F
    ⟨hsem, fun _ _ => trivial, hu⟩ (hsem.decidesFlags (fun q k hk => hlit q k (hk.trans
      (by omega))) p) (hsem.cmp_le p) hlit htn (A₀ := A₀) (R₀ := R₀) (ε := ε) (β := β)
    (b := st.store.size) hsize).spec.exists_exec ⟨rfl, hA, hpar, hpos, hR₀, hℓ,
      fun i hi => ⟨lU, hlU, by omega⟩, fun i hi => ⟨ldv, hldv, by omega⟩⟩
  exact ⟨st', hrun⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The registered tree instantiates to the builder: at the sizes $N$ and $(\ell_0, F)$ the tree
`NLAlib.eighProg.compiled` is `NLAlib.eighProg` on the declared buffers $0$ to $3$. No printed
source. -/
theorem eighProg.toStmt_compiled (p : P) (mm qr : ι) (N : ℕ) (n : Fin 2 → ℕ) :
    (eighProg.compiled p mm qr).toStmt N n =
      ProgFamily.inst (r := 2) (b := 4) (fun _ _ N n h =>
        (eighProg p mm qr N (n 0) (n 1) (h 0) (h 1) (h 2) (h 3)).run) N n := by
  -- the unfolding of the four buffers is deeper than the default recursion limit
  set_option maxRecDepth 10000 in rfl

/-- The registered tree computes `NLAlib.eigh`: let the kernels `mm`, `qr` of `I` be the routines
`mmR`, `qrR` on interleaved pairs, and the semantics decide flags at `p`, with exact integer
literals up to $N + 4$ and the exact floor conversion. A successful run of
`NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$ from the initial state with the
stored $\mathbf{A}$, the stored $R_0$, $\varepsilon$, $\beta$, and $2N^2$ and $N$ empty cells as
declared buffers ends with declared buffers $2$ and $3$ holding `NLAlib.eigh` on the machine of
the interpretation with the tree of samples at the slots.
No printed source. -/
theorem eighProg.holds_of_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (N ℓ₀ F : ℕ) (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (R₀ ε β : K) {st' : St P K C}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some R₀, some ε, some β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M N F R₀ β 0 0 ⟨N, A₀, R₀, ε, ℓ₀⟩)
    pairLayout.Holds st'.store p 2 0 r.1 ∧ ∀ i : Fin N, st'.store.read p 3 i = some (r.2 i) := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled] at h
  set bufs : List (Array (Option K)) := [(pairLayout.toArray A₀).map some,
    #[some R₀, some ε, some β], Array.replicate (2 * (N * N)) none, Array.replicate N none]
    with hbufs
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (bufs := bufs) (k := 0) (Y := A₀)
    rfl
  have h' : exec I (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run
      (inputState p bufs) = some st' := h
  exact holds_of_exec_eighProg hmm hqr p hflag hcmp N ℓ₀ F hlit htn (by simp)
    (by simp [inputState, bufs]) hA (by simp [inputState, bufs, Store.read])
    (by simp [inputState]) h'

/-- The registered tree succeeds: under the standard model at $u$ with every value in range,
$u(p) < 1$, exact integer literals up to $N + 4$ and the exact floor conversion, if the kernels
`mm`, `qr` of `I` are routines on interleaved pairs, $\ell_0 \ge 1$ and $R_0$
decodes to a nonnegative value, then every run of `NLAlib.eighProg.compiled` at the sizes $N$ and
$(\ell_0, F)$ from the initial state with the stored $\mathbf{A}$, the stored $R_0$,
$\varepsilon$, $\beta$, and $2N^2$ and $N$ empty cells as declared buffers succeeds. No printed
source. -/
theorem eighProg.exists_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (N ℓ₀ F : ℕ)
    (hℓ : 1 ≤ ℓ₀) (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (R₀ ε β : K) (hR₀ : 0 ≤ dec p R₀) :
    ∃ st' : St P K C, (eighProg.compiled p mm qr).exec I N ![ℓ₀, F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some R₀, some ε, some β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st' := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled]
  set bufs : List (Array (Option K)) := [(pairLayout.toArray A₀).map some,
    #[some R₀, some ε, some β], Array.replicate (2 * (N * N)) none, Array.replicate N none]
    with hbufs
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (bufs := bufs) (k := 0) (Y := A₀)
    rfl
  exact exists_exec_eighProg hmm hqr hsem p hu N ℓ₀ F hlit htn hℓ (A := 0) (par := 1) (U := 2)
    (dv := 3) (st := inputState p bufs) (A₀ := A₀) (R₀ := R₀) (ε := ε) (β := β) hR₀
    (by simp [inputState, bufs]) hA (by simp [inputState, bufs, Store.read])
    (by simp [inputState]) ⟨2 * (N * N), by simp [inputState, Store.getElem?_shape, bufs], by simp⟩
    ⟨N, by simp [inputState, Store.getElem?_shape, bufs], by simp⟩

end NLAlib
