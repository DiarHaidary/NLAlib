/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PairKernels.HermAvg
public import NLAlib.Matrix.Computation.SpectralBisectionNode.Deflate

/-!
# The compression block of the spectral bisection node step

The compression block of the node step of `NLAlib.eighProg` (`NLAlib.eighCompressBlock`) writes the
compression $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ of the node matrix to the basis a
deflation computed, as the machine of the semantics computes it, and succeeds under the standard
model.

## Main results

* `NLAlib.spec_eighCompressBlock`: the block's specification, for every mode.
* `NLAlib.holds_of_exec_eighCompressBlock`: what a successful run computes.
* `NLAlib.exists_exec_eighCompressBlock`: the compression succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- **The compression block's specification.** If kernel `mm` is a routine on interleaved pairs,
then from a state holding the $k \times r$ basis $\mathbf{Q}$ at `qo` of `Qa`, the node matrix
$\mathbf{A}$ at `mo` of `Ma` and the values $c_2$ and $\sigma$ in the cells `two` and `sg`, the
run of `NLAlib.eighCompressBlock` modifies only its four scratch blocks and the output block at
`co` of `Ma` and keeps the tape positions. If the cells `two` and `sg` lie outside the output
block (a correctness-only hypothesis, so it guards the value clause), that block then holds
`M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ` for the machine `M` of
the semantics. In mode `total` the run also succeeds, given the standard model at $u$ with every
value in range, $c_2$ decoding to a nonzero value and the footprint writable. No printed
source. -/
theorem spec_eighCompressBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem))
    (p : P) (k r : ℕ) {Qa Ma Qh C1 C2 C3 : ℕ} {qo mo co : IExp ℕ} {two sg : Cell ℕ ℕ} (c₂ σ : K)
    (Q : Matrix (Fin k) (Fin r) (K × K)) (A : Matrix (Fin k) (Fin k) (K × K))
    (hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup)
    (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧ sg.buf ∉ [Qh, C1, C2, C3]) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    let fp := [matBlock Qh 0 r k 2, matBlock C1 0 r k 2, matBlock C2 0 r r 2,
      matBlock C3 0 r r 2, matBlock Ma co.eval r r 2]
    RoutineSpec md I (fun st => pairLayout.Holds st.store p Qa qo.eval Q ∧
        pairLayout.Holds st.store p Ma mo.eval A ∧ st.store.read p two.buf two.idx.eval = some c₂ ∧
        st.store.read p sg.buf sg.idx.eval = some σ ∧
        md.Needs (dec p c₂ ≠ 0 ∧ WritableBlocks st.store p fp))
      (eighCompressBlock p mm (.const k) (.const r) Qa qo Ma mo co two sg Qh C1 C2 C3) fp
      fun st st' => (blockDisjoint (Ma, co.eval, 2 * (r * r)) (two.buf, two.idx.eval, 1) = true ∧
          blockDisjoint (Ma, co.eval, 2 * (r * r)) (sg.buf, sg.idx.eval, 1) = true →
          pairLayout.Holds st'.store p Ma co.eval
            (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ)) ∧
        PosKept st st' := by
  intro M fp
  refine ⟨by exec_composable, fun st ⟨hQ, hA, htwo, hσ, hN⟩ => ?_⟩
  have hW := fun s (hs : Store.shape s = st.store.shape) b o l (hx : (b, o, l) ∈ fp) =>
    (Mode.needs_and.mp hN).2.mono fun h => (h _ hx).of_shape_eq hs
  exact (spec_zconjTranspose md hsem p k r (X := Qa) (Y := Qh) (xo := qo) (yo := 0) Q
    (by fp_omega [hbufs])).wp_bind ⟨hQ, hW _ rfl _ _ _ (by simp [fp, matBlock])⟩
    fun st₁ hm₁ h₁ => (RoutineSpec.stmt (hmm.spec_kcall (fun _ => rfl) md p (Qh, 0) (Ma, mo)
      (C1, 0) _ A)).wp_bind ⟨h₁.1, (readsOnly_entryLayoutHolds _ p Ma _ A).of_modifies hA hm₁
      (by fp_omega [hbufs]), by fp_omega [hbufs], by fp_omega [hbufs],
      hW _ hm₁.1 _ _ _ (by simp [fp, matBlock, pairLayout])⟩
    fun st₂ hm₂ h₂ => (RoutineSpec.stmt (hmm.spec_kcall (fun _ => rfl) md p (C1, 0) (Qa, qo)
      (C2, 0) _ Q)).wp_bind ⟨h₂.1, (readsOnly_entryLayoutHolds _ p Qa _ Q).of_modifies hQ
      (hm₁.trans hm₂) (by fp_omega [hbufs]), by fp_omega [hbufs], by fp_omega [hbufs],
      hW _ (hm₁.trans hm₂).1 _ _ _ (by simp [fp, matBlock, pairLayout])⟩
    fun st₃ hm₃ h₃ => (spec_zhermAvg md hsem p r (X := C2) (Y := C3) (xo := 0) (yo := 0)
      (c := two) c₂ _ (by fp_omega [hbufs]) (by fp_omega [hcells])).wp_bind
      ⟨h₃.1, (readsOnly_read _ _ _ _).of_modifies htwo (hm₁.trans hm₂ |>.trans hm₃)
      (by fp_omega [hcells]), (Mode.needs_and.mp hN).1.elim fun h0 =>
      (hW _ (hm₁.trans hm₂ |>.trans hm₃).1 _ _ _ (by simp [fp, matBlock])).mono (⟨h0, ·⟩)⟩
    fun st₄ hm₄ h₄ => (spec_zhermShift md hsem p r (X := C3) (Y := Ma) (xo := 0) (yo := co)
      (c := sg) σ _ (by fp_omega [hbufs])).wp_run ⟨h₄.1, (readsOnly_read _ _ _ _).of_modifies hσ
      (hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄) (by fp_omega [hcells]),
      hW _ (hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄).1 _ _ _ (by simp [fp, matBlock])⟩
    fun st₅ hm₅ h₅ => ⟨(hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄ |>.trans hm₅).mono
      (by simp [fp, matBlock, pairLayout]), fun hg => h₅.1 (by fp_omega [hg.2]),
      h₅.2.trans (h₄.2.trans (h₃.2.2.trans (h₂.2.2.trans h₁.2)))⟩

/-- A compression computes the machine's compression: if kernel `mm` of `I` is the routine `mmR`
on interleaved pairs, a successful run of `NLAlib.eighCompressBlock` for the stored $k \times r$
basis $\mathbf{Q}$ at `qo` of `Qa`, the node matrix $\mathbf{A}$ at `mo` of `Ma`, the cells `two`
and `sg` holding $c_2$ and $\sigma$, writing at `co` of `Ma`, ends
with that block holding `M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ`;
every cell outside it and the scratch buffers is unchanged, the store shape and the tape positions
too. No printed source. -/
theorem holds_of_exec_eighCompressBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (k r : ℕ) {Qa Ma Qh C1 C2 C3 : ℕ} {qo mo co : IExp ℕ} {two sg : Cell ℕ ℕ} {c₂ σ : K}
    {st st' : St P K C} {Q : Matrix (Fin k) (Fin r) (K × K)} {A : Matrix (Fin k) (Fin k) (K × K)}
    (hQ : pairLayout.Holds st.store p Qa qo.eval Q) (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (htwo : st.store.read p two.buf two.idx.eval = some c₂)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup) (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧
      sg.buf ∉ [Qh, C1, C2, C3])
    (hcocells : blockDisjoint (Ma, co.eval, 2 * (r * r)) (two.buf, two.idx.eval, 1) = true ∧
      blockDisjoint (Ma, co.eval, 2 * (r * r)) (sg.buf, sg.idx.eval, 1) = true)
    (h : exec I (eighCompressBlock p mm (.const k) (.const r) Qa qo Ma mo co two sg Qh C1 C2
      C3).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Ma co.eval
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ) ∧
      (∀ q b i, b ∉ [Qh, C1, C2, C3] → blockDisjoint (b, i, 1) (Ma, co.eval, 2 * (r * r)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  exact ((spec_eighCompressBlock (u := fun _ => 0) (dec := fun _ _ => 0) hmm .liberal trivial p k r
    c₂ σ Q A hbufs hcells).spec.holds_of_exec ⟨hQ, hA, htwo, hσ, trivial⟩ h).elim fun hm hv =>
    ⟨hv.1 hcocells, fun q b i hb hbd => hm.2 q b i (by fp_omega [hb, hbd]), hm.1, hv.2⟩

/-- A compression succeeds under the standard model at $u$ with every value in range, the
cell `two` decoding to a nonzero value, if kernel `mm` is a routine on pairs and the scratch buffers
have $2n^2$ cells, $k, r \le n$ (hypotheses on the inputs as
`NLAlib.holds_of_exec_eighCompressBlock`). No printed source. -/
theorem exists_exec_eighCompressBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n k r : ℕ) (hk : k ≤ n) (hr : r ≤ k) {Qa Ma Qh C1 C2 C3 : ℕ} {qo mo co : IExp ℕ}
    {two sg : Cell ℕ ℕ} {c₂ σ : K} {st : St P K C} {Q : Matrix (Fin k) (Fin r) (K × K)}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hQ : pairLayout.Holds st.store p Qa qo.eval Q)
    (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (htwo : st.store.read p two.buf two.idx.eval = some c₂) (htwo0 : dec p c₂ ≠ 0)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup) (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧
      sg.buf ∉ [Qh, C1, C2, C3])
    (hcolen : ∃ len, st.store.shape[Ma]? = some (p, len) ∧ co.eval + 2 * (r * r) ≤ len)
    (hscr : ∀ X ∈ [Qh, C1, C2, C3], ∃ len, st.store.shape[X]? = some (p, len) ∧
      2 * (n * n) ≤ len) :
    ∃ st', exec I (eighCompressBlock p mm (.const k) (.const r) Qa qo Ma mo co two sg Qh C1 C2
      C3).run st = some st' := by
  refine ((spec_eighCompressBlock (toNat := fun _ => 0) (qrR := @fun _ _ X =>
    (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : K) => x) (normal := id) hmm .total hsem p
    k r c₂ σ Q A hbufs hcells).spec.exists_exec ⟨hQ, hA, htwo, hσ, htwo0, fun x hx => ?_⟩).imp
    fun _ h => h.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [matBlock] <;> first
    | exact hcolen.elim fun _ h => writable_of_shape_eq rfl h.1 (by fp_omega [h.2])
    | exact (hscr _ (by simp)).elim fun _ h => writable_of_shape_eq rfl h.1 (by
        fp_omega [h.2, Nat.mul_le_mul (hr.trans hk) hk, Nat.mul_le_mul (hr.trans hk) (hr.trans hk)])

end NLAlib
