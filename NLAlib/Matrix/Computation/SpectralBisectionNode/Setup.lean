/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode.Split

/-!
# The set-up of the spectral bisection node step

The set-up of the node step of `NLAlib.eighProg`, up to the clamp of the split index, as routine
specifications of the program logic (`docs/design/Computation-ProgramLogic.md`): the stored shift
$\sigma$ and $-\sigma$, the sign step, the projectors and the value
$\mathrm{fl}(t + \mathrm{fl}(1/2))$ that the index binder converts; only scratch buffers are
written. Each block is a sequence of calls of specified routines and instructions, the values
carried across calls in bundles of cells (`NLAlib.Computation.CellsHold`). The scratch prefix of
the node step (its seven allocations) is `NLAlib.spec_eighNodeBlock_of_body`.

## Main results

* `NLAlib.spec_eighNodeScalars`, `NLAlib.spec_eighNodeSign`, `NLAlib.spec_eighNodeProjectors`:
  the parts of the set-up.
* `NLAlib.spec_eighNodeSetup`: the set-up.
* `NLAlib.spec_eighNodeBlock_of_body`: the scratch prefix of the node step.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- **A rounded product of nonzero values is nonzero** under the standard model at $u(p) < 1$:
it decodes to $xy(1 + \delta)$ with $\lvert \delta \rvert < 1$. No printed source. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.dec_ne_zero_of_mul_eq_some {u : P → ℝ}
    {dec : P → K → ℝ} {safe : P → ℝ → Prop} {sem : ScalarSem P K}
    (hsem : IsRelErrSem u dec safe sem) {p : P} (hu : u p < 1) {x y v : K} (hx : dec p x ≠ 0)
    (hy : dec p y ≠ 0) (hv : sem.bin p .mul x y = some v) : dec p v ≠ 0 := by
  obtain ⟨δ, hδ, hdec⟩ := hsem.bin_err p .mul x y v trivial hv
  rw [hdec]
  exact mul_ne_zero (mul_ne_zero hx hy) (by linarith [(abs_le.mp hδ).1])

/-- **The scalars of a node step's set-up as a routine specification**: from a state whose cell
$2d$ of `Lv` holds $R$, cell `lo` of `Su` the uniform word $v$ and cell $1$ of `c` the stored
$z_2$, the five instructions write $\sigma = \mathrm{fl}(R/z_2)$, $-\sigma$ and the shift
$\mathrm{fl}(\mathrm{fl}(R/\mathrm{fl}(\ell_0 + d))v)$ in the cells $0$, $1$, $4$ of the scratch
buffer `t` and modify only its cells $0$ to $4$, keeping the tape positions; in mode `total` they
also succeed, given the standard model on the range `safe` holding everywhere, $u(p) < 1$, $z_2$
decoding to a nonzero value, $\ell_0 + d \ge 1$ and the cells writable. No printed source. -/
theorem spec_eighNodeScalars (md : Mode) {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (p : P) (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (ℓ₀ d lo : ℕ) {Lv Su c t : ℕ} (R z₂ v : K) (htLv : t ≠ Lv) (htSu : t ≠ Su) :
    RoutineSpec md I (fun st => st.store.read p Lv (2 * d) = some R ∧
        st.store.read p Su lo = some v ∧ st.store.read p c 1 = some z₂ ∧
        md.Needs (dec p z₂ ≠ 0 ∧ 1 ≤ ℓ₀ + d ∧ Writable st.store p t 0 5))
      (do
        ins (.bin p .div ⟨t, 0⟩ ⟨Lv, 2 * .const d⟩ ⟨c, 1⟩)
        ins (.un p .neg ⟨t, 1⟩ ⟨t, 0⟩)
        ins (.litIdx p ⟨t, 2⟩ (.const ℓ₀ + .const d))
        ins (.bin p .div ⟨t, 3⟩ ⟨Lv, 2 * .const d⟩ ⟨t, 2⟩)
        ins (.bin p .mul ⟨t, 4⟩ ⟨t, 3⟩ ⟨Su, .const lo⟩) : Builder P ι ℕ ℕ Unit) [(t, 0, 5)]
      fun st st' => st'.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div R z₂) ∧
        st'.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
          ((eighTapeMachine I p mmR qrR).div R z₂)) ∧
        st'.store.read p t 4 = some ((eighTapeMachine I p mmR qrR).mul
          ((eighTapeMachine I p mmR qrR).div R
            ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d))) v) ∧ PosKept st st' := by
  refine ⟨by exec_composable, fun st ⟨hR, hSu, hc, hN⟩ => ?_⟩
  have hN' := Mode.needs_and.mpr ⟨hsem, hN⟩
  have hw := fun {fp} {s : Store P K} (i : ℕ) (hi : i < 5) (hm : Modifies fp st.store s) =>
    hN.mono fun h => (h.2.2.of_modifies hm).of_le (off' := i) (n' := 1) (by omega) (by omega)
  have s₁ := RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .div)
    (dst := ⟨t, 0⟩) (x := ⟨Lv, 2 * .const d⟩) (y := ⟨c, 1⟩) (a := R) (b := z₂))
  refine s₁.wp_bind_keep
    (readsOnly_cellsHold [(p, Lv, 2 * d, some R), (p, Su, lo, some v)]) (by fp_omega [htLv, htSu])
    ⟨hR, hc, (Mode.needs_and.mpr ⟨hN'.mono fun ⟨h, h0, _⟩ =>
      h.1.bin_ok p .div R z₂ trivial (fun _ => h0) (h.2.1 _ _), hw 0 (by omega) (.refl [] _)⟩)⟩
    (((cellsHold_nil _).cons hSu).cons hR) fun st₁ hm₁ h₁ hC₁ => ?_
  have s₂ := RoutineSpec.ins (spec_un_getD (m := md) (I := I) (p := p) (op := .neg)
    (dst := ⟨t, 1⟩) (x := ⟨t, 0⟩) (a := (eighTapeMachine I p mmR qrR).div R z₂))
  refine s₂.wp_bind_keep ((readsOnly_cellsHold _).and (readsOnly_cellsHold
        [(p, t, 0, some ((eighTapeMachine I p mmR qrR).div R z₂))]))
    (by fp_omega [htLv, htSu]) ⟨h₁.1, Mode.needs_and.mpr ⟨hsem.mono fun h =>
      (h.1.neg p _).imp fun _ h => h.1, hw 1 (by omega) hm₁⟩⟩ ⟨hC₁, (cellsHold_nil _).cons h₁.1⟩
    fun st₂ hm₂ h₂ ⟨hC₂, hT₂⟩ => ?_
  have s₃ := RoutineSpec.ins (spec_litIdx_getD (m := md) (I := I) (p := p) (dst := ⟨t, 2⟩)
    (e := .const ℓ₀ + .const d))
  refine s₃.wp_bind_keep
    ((readsOnly_cellsHold _).and (readsOnly_cellsHold _)) (by fp_omega [htLv, htSu])
    (Mode.needs_and.mpr ⟨hsem.mono fun h => h.1.lit_ok p _ (h.2.1 _ _),
      hw 2 (by omega) (hm₁.trans hm₂)⟩) ⟨hC₂, hT₂.cons h₂.1⟩ fun st₃ hm₃ h₃ ⟨hC₃, hT₃⟩ => ?_
  have s₄ := RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .div)
    (dst := ⟨t, 3⟩) (x := ⟨Lv, 2 * .const d⟩) (y := ⟨t, 2⟩) (a := R)
    (b := (eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d)))
  refine s₄.wp_bind_keep
    ((readsOnly_cellsHold [(p, Su, lo, some v)]).and (readsOnly_cellsHold _))
    (by fp_omega [htLv, htSu]) ⟨hC₃.read (.head _), h₃.1, Mode.needs_and.mpr ⟨hN'.mono
      fun ⟨h, _, hl, _⟩ => h.1.bin_ok p .div R _ trivial (fun _ => by
        obtain ⟨z, hz⟩ := h.1.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) (h.2.1 _ _)
        change dec p ((I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default) ≠ 0
        rw [hz]
        exact h.1.dec_ne_zero_of_lit_eq_some h.2.2 (by norm_cast; omega) hz) (h.2.1 _ _),
      hw 3 (by omega) (hm₁.trans hm₂ |>.trans hm₃)⟩⟩ ⟨hC₃.sub (by simp), hT₃⟩
    fun st₄ hm₄ h₄ ⟨hC₄, hT₄⟩ => ?_
  have s₅ := RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .mul)
    (dst := ⟨t, 4⟩) (x := ⟨t, 3⟩) (y := ⟨Su, .const lo⟩)
    (a := (eighTapeMachine I p mmR qrR).div R ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d)))
    (b := v))
  refine s₅.wp_run_keep (readsOnly_cellsHold _)
    (by fp_omega) ⟨h₄.1, hC₄.read (.head _), Mode.needs_and.mpr ⟨hsem.mono fun h =>
      h.1.bin_ok p .mul _ v trivial (fun h => nomatch h) (h.2.1 _ _),
      hw 4 (by omega) (hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄)⟩⟩ hT₄ fun st₅ hm₅ h₅ hT₅ => ?_
  exact ⟨(hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄ |>.trans hm₅).of_sub (by simp),
    hT₅.read (.tail _ (.head _)), hT₅.read (.head _), h₅.1,
    h₅.2.trans (h₄.2.trans (h₃.2.trans (h₂.2.trans h₁.2)))⟩

/-- **The sign of a node step's set-up as a routine specification**: from a state of $s_0$
buffers holding the node matrix $\mathbf{A}$ at its block of `Ma`, the shift $c$ in the cell $4$
of `t`, $\beta$ in the cell $2$ of `par`, the stored $z_2$ in the cell $1$ of `c` and $R$ in the
cell $2d$ of `Lv`, the block writes $\mathbf{W} = \mathbf{A} - c\mathbf{I}$ in `W`, $\beta$ and
$\mathrm{fl}(z_2 R)$ in the cells $0$, $1$ of `sp` and the sign of $\mathbf{W}$ (step limit $F$)
in `B` (scratch buffers below $s_0$); it modifies only those blocks and keeps the tape positions;
in mode `total` it also succeeds, given the standard model on the range `safe` holding everywhere,
$u(p) < 1$, $k \ge 1$, $z_2$ and $R$ decoding to nonzero values and the blocks writable. The
semantics decides flags at `p`. No printed source. -/
theorem spec_eighNodeSign {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop} (p : P) (n F d lo k : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1 ∧ 0 < k))
    (hflag : I.sem.DecidesFlags p) {Ma Lv par c t sp W B s₀ : ℕ}
    (A : Matrix (Fin k) (Fin k) (K × K)) (R β z₂ cv : K) (hMaW : Ma ≠ W) (htW : t ≠ W)
    (hparW : par ≠ W) (hcW : c ≠ W) (hLvW : Lv ≠ W) (hcsp : c ≠ sp) (hLvsp : Lv ≠ sp)
    (hspW : sp ≠ W) (hBW : B ≠ W) (hBsp : B ≠ sp) (hBs : B < s₀) (hWs : W < s₀)
    (hsps : sp < s₀) :
    RoutineSpec md I (fun st => st.store.size = s₀ ∧
        pairLayout.Holds st.store p Ma (2 * (n * n) * d + 2 * n * lo) A ∧
        st.store.read p t 4 = some cv ∧ st.store.read p par 2 = some β ∧
        st.store.read p c 1 = some z₂ ∧ st.store.read p Lv (2 * d) = some R ∧
        md.Needs (dec p z₂ ≠ 0 ∧ dec p R ≠ 0 ∧ Writable st.store p W 0 (k * k * 2) ∧
          Writable st.store p sp 0 2 ∧ Writable st.store p B 0 (k * k * 2)))
      (do
        zhermShift p (.const k) Ma (eighBlockOff (.const n) (.const d) (.const lo)) ⟨t, 4⟩ W 0
        ins (.copy p ⟨sp, 0⟩ ⟨par, 2⟩)
        ins (.bin p .mul ⟨sp, 1⟩ ⟨c, 1⟩ ⟨Lv, 2 * .const d⟩)
        eighSignBlock p mm (.const k) (.const F) W 0 sp 0 B 0 : Builder P ι ℕ ℕ Unit)
      [matBlock W 0 k k 2, (sp, 0, 2), matBlock B 0 k k 2]
      fun st st' => pairLayout.Holds st'.store p B 0 (newtonSchulzSign (eighTapeMachine I p mmR qrR)
        β ((eighTapeMachine I p mmR qrR).mul z₂ R) F
        ((eighTapeMachine I p mmR qrR).hermShift A cv)) ∧ PosKept st st' := by
  have hs : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem) :=
    hsem.mono fun h => h.1.mono_safe fun p x _ => h.2.1 p x
  refine ⟨by exec_composable, fun st ⟨hsz, hA, ht4, hβ, hc, hR, hN⟩ => ?_⟩
  have hN' := Mode.needs_and.mpr ⟨hsem, hN⟩
  have s₁ := spec_zhermShift (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR)
    (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md hs p k (X := Ma) (Y := W)
    (xo := eighBlockOff (.const n) (.const d) (.const lo)) (yo := 0) (c := ⟨t, 4⟩) cv A
    (by fp_omega [hMaW])
  refine s₁.wp_bind_keep (readsOnly_cellsHold [(p, par, 2, some β), (p, c, 1, some z₂),
      (p, Lv, 2 * d, some R)]) (by fp_omega [hparW, hcW, hLvW]) ⟨hA, ht4, hN.mono (·.2.2.1)⟩
    (((cellsHold_nil _).cons hR |>.cons hc).cons hβ) fun st₁ hm₁ h₁ hC₁ => ?_
  have s₂ := RoutineSpec.ins (spec_copy (m := md) (I := I) (p := p) (dst := ⟨sp, 0⟩)
    (x := ⟨par, 2⟩) (a := β))
  refine s₂.wp_bind_keep ((readsOnly_cellsHold [(p, c, 1, some z₂), (p, Lv, 2 * d, some R)]).and
      (readsOnly_pairLayoutHolds p W 0 ((eighTapeMachine I p mmR qrR).hermShift A cv)))
    (by fp_omega [hcsp, hLvsp, hspW]) ⟨hC₁.read (.head _), hN.mono fun h =>
      (h.2.2.2.1.of_modifies hm₁).of_le (by simp) (by simp)⟩
    ⟨hC₁.sub (by simp), h₁.1 (by fp_omega [htW])⟩ fun st₂ hm₂ h₂ ⟨hC₂, hW₂⟩ => ?_
  have s₃ := RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .mul)
    (dst := ⟨sp, 1⟩) (x := ⟨c, 1⟩) (y := ⟨Lv, 2 * .const d⟩) (a := z₂) (b := R))
  refine s₃.wp_bind_keep ((readsOnly_pairLayoutHolds p W 0 _).and
      (readsOnly_cellsHold [(p, sp, 0, some β)])) (by fp_omega [hspW])
    ⟨hC₂.read (.head _), hC₂.read (.tail _ (.head _)), Mode.needs_and.mpr ⟨hN'.mono
      fun ⟨h, h0, hR0, _⟩ => h.1.bin_ok p .mul z₂ R trivial (fun h => nomatch h) (h.2.1 _ _),
      hN.mono fun h => (h.2.2.2.1.of_modifies (hm₁.trans hm₂)).of_le (by simp) (by simp)⟩⟩
    ⟨hW₂, (cellsHold_nil _).cons h₂.1⟩ fun st₃ hm₃ h₃ ⟨hW₃, hC₃⟩ => ?_
  have s₄ := spec_eighSignBlock (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm md p k F hsem hflag (A := W) (par := sp) (X := B) (ao := 0) (po := 0) (xo := 0)
    ((eighTapeMachine I p mmR qrR).hermShift A cv) β ((eighTapeMachine I p mmR qrR).mul z₂ R)
    (by fp_omega [hBW]) (by fp_omega [hBsp]) hBs (.inr hWs) hsps
  have hm := hm₁.trans hm₂ |>.trans hm₃
  refine s₄.wp_run ⟨(Store.size_eq_of_shape_eq hm.1).trans hsz, hW₃, hC₃.read (.head _), h₃.1,
    hN'.mono fun ⟨h, h0, hR0, h1⟩ => ⟨by
      obtain ⟨v, hv⟩ := h.1.bin_ok p .mul z₂ R trivial (fun h => nomatch h) (h.2.1 _ _)
      change dec p ((I.sem.bin p .mul z₂ R).getD default) ≠ 0
      rw [hv]
      exact h.1.dec_ne_zero_of_mul_eq_some h.2.2.1 h0 hR0 hv, h1.2.2.of_modifies hm⟩⟩
    fun st₄ hm₄ h₄ => ⟨(hm.trans hm₄).of_sub (by simp [matBlock]), h₄.1,
      h₄.2.trans (h₃.2.trans (h₂.2.2.trans h₁.2))⟩

/-- **The projectors of a node step's set-up as a routine specification**: from a state whose
block at offset $0$ of `B` holds the sign $\mathbf{B}$ and whose cells $0$, $1$, $3$ of `c` hold
$o$, $z_2$ and $m$, the block writes $\mathbf{P}_+ = \mathrm{fl}((\mathbf{B} + m\mathbf{I})/z_2)$ in
`Pp` and $\mathbf{P}_- = \mathrm{fl}(-(\mathbf{B} + o\mathbf{I})/z_2)$ in `Pm`, through the
scratch buffer `T` (the four buffers distinct and `c` none of them); it modifies only the blocks
of `T`, `Pp`, `Pm` and keeps the tape positions; in mode `total` it also succeeds, given the
standard model, $z_2$ decoding to a nonzero value and the blocks writable. No printed source. -/
theorem spec_eighNodeProjectors (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (k : ℕ)
    {c B T Pp Pm : ℕ} (Bm : Matrix (Fin k) (Fin k) (K × K)) (o z₂ m : K) (hBT : B ≠ T)
    (hBPp : B ≠ Pp) (hTPp : T ≠ Pp) (hTPm : T ≠ Pm) (hPpPm : Pp ≠ Pm) (hcT : c ≠ T)
    (hcPp : c ≠ Pp) (hcPm : c ≠ Pm) :
    RoutineSpec md I (fun st => pairLayout.Holds st.store p B 0 Bm ∧
        st.store.read p c 0 = some o ∧ st.store.read p c 1 = some z₂ ∧
        st.store.read p c 3 = some m ∧ md.Needs (dec p z₂ ≠ 0 ∧
          Writable st.store p T 0 (k * k * 2) ∧ Writable st.store p Pp 0 (k * k * 2) ∧
          Writable st.store p Pm 0 (k * k * 2)))
      (do
        zhermShift p (.const k) B 0 ⟨c, 3⟩ T 0
        zhermScale p (.const k) T 0 ⟨c, 1⟩ Pp 0
        zhermShift p (.const k) B 0 ⟨c, 0⟩ T 0
        zneg p (.const k) (.const k) T 0 T 0
        zhermScale p (.const k) T 0 ⟨c, 1⟩ Pm 0 : Builder P ι ℕ ℕ Unit)
      [matBlock T 0 k k 2, matBlock Pp 0 k k 2, matBlock Pm 0 k k 2]
      fun st st' => pairLayout.Holds st'.store p Pp 0 ((eighTapeMachine I p mmR qrR).hermScale
          ((eighTapeMachine I p mmR qrR).hermShift Bm m) z₂) ∧
        pairLayout.Holds st'.store p Pm 0 ((eighTapeMachine I p mmR qrR).hermScale
          ((eighTapeMachine I p mmR qrR).negMat ((eighTapeMachine I p mmR qrR).hermShift Bm o))
          z₂) ∧ PosKept st st' := by
  refine ⟨by exec_composable, fun st ⟨hB, hc0, hc1, hc3, hN⟩ => ?_⟩
  have hw := fun {fp} {s : Store P K} (hm : Modifies fp st.store s) =>
    hN.mono fun h => (⟨h.1, h.2.1.of_modifies hm, h.2.2.1.of_modifies hm,
      h.2.2.2.of_modifies hm⟩ : _ ∧ _ ∧ _ ∧ _)
  have s₁ := spec_zhermShift (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR)
    (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md hsem p k (X := B) (Y := T) (xo := 0)
    (yo := 0) (c := ⟨c, 3⟩) m Bm (by fp_omega [hBT])
  refine s₁.wp_bind_keep ((readsOnly_pairLayoutHolds p B 0 Bm).and
      (readsOnly_cellsHold [(p, c, 0, some o), (p, c, 1, some z₂)])) (by fp_omega [hBT, hcT])
    ⟨hB, hc3, hN.mono (·.2.1)⟩ ⟨hB, ((cellsHold_nil _).cons hc1).cons hc0⟩
    fun st₁ hm₁ h₁ ⟨hB₁, hC₁⟩ => ?_
  have s₂ := spec_zhermScale (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR)
    (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md hsem p k (X := T) (Y := Pp) (xo := 0)
    (yo := 0) (c := ⟨c, 1⟩) z₂ ((eighTapeMachine I p mmR qrR).hermShift Bm m) (by fp_omega [hTPp])
    (by fp_omega [hcPp])
  refine s₂.wp_bind_keep ((readsOnly_pairLayoutHolds p B 0 Bm).and (readsOnly_cellsHold _))
    (by fp_omega [hBPp, hcPp]) ⟨h₁.1 (by fp_omega [hcT]), hC₁.read (.tail _ (.head _)),
      (hw hm₁).mono fun h => ⟨h.1, h.2.2.1⟩⟩ ⟨hB₁, hC₁⟩ fun st₂ hm₂ h₂ ⟨hB₂, hC₂⟩ => ?_
  have s₃ := spec_zhermShift (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR)
    (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md hsem p k (X := B) (Y := T) (xo := 0)
    (yo := 0) (c := ⟨c, 0⟩) o Bm (by fp_omega [hBT])
  refine s₃.wp_bind_keep ((readsOnly_cellsHold [(p, c, 1, some z₂)]).and
      (readsOnly_pairLayoutHolds p Pp 0 _)) (by fp_omega [hcT, hTPp])
    ⟨hB₂, hC₂.read (.head _), (hw (hm₁.trans hm₂)).mono (·.2.1)⟩ ⟨hC₂.sub (by simp), h₂.1⟩
    fun st₃ hm₃ h₃ ⟨hC₃, hP₃⟩ => ?_
  have s₄ := spec_zneg (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR)
    (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md hsem p k k (X := T) (Y := T) (xo := 0)
    (yo := 0) ((eighTapeMachine I p mmR qrR).hermShift Bm o) (.inr ⟨rfl, rfl⟩)
  refine s₄.wp_bind_keep ((readsOnly_cellsHold _).and (readsOnly_pairLayoutHolds p Pp 0 _))
    (by fp_omega [hcT, hTPp]) ⟨h₃.1 (by fp_omega [hcT]),
      (hw (hm₁.trans hm₂ |>.trans hm₃)).mono (·.2.1)⟩ ⟨hC₃, hP₃⟩ fun st₄ hm₄ h₄ ⟨hC₄, hP₄⟩ => ?_
  have s₅ := spec_zhermScale (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR)
    (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md hsem p k (X := T) (Y := Pm) (xo := 0)
    (yo := 0) (c := ⟨c, 1⟩) z₂
    ((eighTapeMachine I p mmR qrR).negMat ((eighTapeMachine I p mmR qrR).hermShift Bm o))
    (by fp_omega [hTPm]) (by fp_omega [hcPm])
  have hm := hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄
  refine s₅.wp_run_keep (readsOnly_pairLayoutHolds p Pp 0 _) (by fp_omega [hPpPm])
    ⟨h₄.1, hC₄.read (.head _), (hw hm).mono fun h => ⟨h.1, h.2.2.2⟩⟩ hP₄
    fun st₅ hm₅ h₅ hP₅ => ⟨(hm.trans hm₅).of_sub (by simp [matBlock]), hP₅, h₅.1,
      h₅.2.trans (h₄.2.trans (h₃.2.trans (h₂.2.trans h₁.2)))⟩

/-- **The set-up of a node step as a routine specification**, up to the clamp: from a state of
$b + 7$ buffers whose top seven are the node step's scratch (shapes as allocated), holding the node
matrix $\mathbf{A}$ at its block of `Ma`, $R$ in the cell $2d$ of `Lv`, $\beta$ in the cell $2$ of
`par`, the uniform word $v$ in the cell `lo` of `Su` and $o$, $z_2$, $h$, $m$ in the cells $0$ to
$3$ of `c` (all below $b$), the run writes $\sigma = \mathrm{fl}(R/z_2)$, $-\sigma$ and
$\mathrm{fl}(\operatorname{tr}\mathbf{P}_+ + h)$ in the cells $0$, $1$, $6$ of the scratch
buffer $b$ and the projectors $\mathbf{P}_\pm$ of the sign $\mathbf{B}$ of
$\mathbf{A} - \mathrm{fl}(\mathrm{fl}(R/\mathrm{fl}(\ell_0 + d))v)\mathbf{I}$ at offset $0$ of
the buffers $b + 5$, $b + 6$; it modifies only the seven scratch buffers and keeps the tape
positions; in mode `total` it also succeeds, given the standard model on the range `safe`
holding everywhere, $u(p) < 1$, $k \ge 1$, $z_2$ and $R$ decoding to nonzero values and
$\ell_0 + d \ge 1$. The semantics decides flags at `p`. No printed source. -/
theorem spec_eighNodeSetup {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d lo k : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1 ∧ 0 < k))
    (hflag : I.sem.DecidesFlags p) (hkn : k ≤ n) {Ma Lv par Su c b : ℕ}
    (hlt : Ma < b ∧ Lv < b ∧ par < b ∧ Su < b ∧ c < b)
    (A Bm Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)) (R β v o z₂ h m : K)
    (hBm : Bm = newtonSchulzSign (eighTapeMachine I p mmR qrR) β
      ((eighTapeMachine I p mmR qrR).mul z₂ R) F ((eighTapeMachine I p mmR qrR).hermShift A
        ((eighTapeMachine I p mmR qrR).mul ((eighTapeMachine I p mmR qrR).div R
          ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d))) v)))
    (hPp : Ppm = (eighTapeMachine I p mmR qrR).hermScale
      ((eighTapeMachine I p mmR qrR).hermShift Bm m) z₂)
    (hPm : Pmm = (eighTapeMachine I p mmR qrR).hermScale ((eighTapeMachine I p mmR qrR).negMat
      ((eighTapeMachine I p mmR qrR).hermShift Bm o)) z₂) :
    RoutineSpec md I (fun st => st.store.size = b + 7 ∧
        pairLayout.Holds st.store p Ma (2 * (n * n) * d + 2 * n * lo) A ∧
        st.store.read p Lv (2 * d) = some R ∧ st.store.read p par 2 = some β ∧
        st.store.read p Su lo = some v ∧ st.store.read p c 0 = some o ∧
        st.store.read p c 1 = some z₂ ∧ st.store.read p c 2 = some h ∧
        st.store.read p c 3 = some m ∧ st.store.shape[b]? = some (p, 7) ∧
        st.store.shape[b + 1]? = some (p, 2) ∧
        (∀ j < 5, st.store.shape[b + 2 + j]? = some (p, 2 * (n * n))) ∧
        md.Needs (dec p z₂ ≠ 0 ∧ dec p R ≠ 0 ∧ 1 ≤ ℓ₀ + d))
      ((do
        ins (.bin p .div ⟨b, 0⟩ ⟨Lv, 2 * .const d⟩ ⟨c, 1⟩)
        ins (.un p .neg ⟨b, 1⟩ ⟨b, 0⟩)
        ins (.litIdx p ⟨b, 2⟩ (.const ℓ₀ + .const d))
        ins (.bin p .div ⟨b, 3⟩ ⟨Lv, 2 * .const d⟩ ⟨b, 2⟩)
        ins (.bin p .mul ⟨b, 4⟩ ⟨b, 3⟩ ⟨Su, .const lo⟩) : Builder P ι ℕ ℕ Unit) >>= fun _ =>
      (do
        zhermShift p (.const k) Ma (eighBlockOff (.const n) (.const d) (.const lo)) ⟨b, 4⟩
          (b + 2) 0
        ins (.copy p ⟨b + 1, 0⟩ ⟨par, 2⟩)
        ins (.bin p .mul ⟨b + 1, 1⟩ ⟨c, 1⟩ ⟨Lv, 2 * .const d⟩)
        eighSignBlock p mm (.const k) (.const F) (b + 2) 0 (b + 1) 0 (b + 3) 0 :
          Builder P ι ℕ ℕ Unit) >>= fun _ =>
      (do
        zhermShift p (.const k) (b + 3) 0 ⟨c, 3⟩ (b + 4) 0
        zhermScale p (.const k) (b + 4) 0 ⟨c, 1⟩ (b + 5) 0
        zhermShift p (.const k) (b + 3) 0 ⟨c, 0⟩ (b + 4) 0
        zneg p (.const k) (.const k) (b + 4) 0 (b + 4) 0
        zhermScale p (.const k) (b + 4) 0 ⟨c, 1⟩ (b + 6) 0 : Builder P ι ℕ ℕ Unit) >>= fun _ => do
        ztraceRe p (.const k) (b + 5) 0 ⟨b, 5⟩
        ins (.bin p .add ⟨b, 6⟩ ⟨b, 5⟩ ⟨c, 2⟩))
      [(b, 0, 7), (b + 1, 0, 2), (b + 2, 0, 2 * (n * n)), (b + 3, 0, 2 * (n * n)),
        (b + 4, 0, 2 * (n * n)), (b + 5, 0, 2 * (n * n)), (b + 6, 0, 2 * (n * n))]
      fun st st' => st'.store.read p b 0 = some ((eighTapeMachine I p mmR qrR).div R z₂) ∧
        st'.store.read p b 1 = some ((eighTapeMachine I p mmR qrR).neg
          ((eighTapeMachine I p mmR qrR).div R z₂)) ∧
        st'.store.read p b 6 = some ((eighTapeMachine I p mmR qrR).add
          ((eighTapeMachine I p mmR qrR).traceRe Ppm) h) ∧
        pairLayout.Holds st'.store p (b + 5) 0 Ppm ∧ pairLayout.Holds st'.store p (b + 6) 0 Pmm ∧
        PosKept st st' := by
  obtain ⟨lMa, lLv, lpar, lSu, lc⟩ := hlt
  have hs : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem) :=
    hsem.mono fun h => h.1.mono_safe fun p x _ => h.2.1 p x
  have hkk : 0 + k * k * 2 ≤ 2 * (n * n) := by nlinarith
  have hkk' : k * k * 2 ≤ 2 * (n * n) := by omega
  refine ⟨by exec_composable, fun st ⟨hsz, hA, hR, hβ, hv, hc0, hc1, hc2, hc3, ht, hsp, hW, hN⟩ =>
    ?_⟩
  have s₁ := spec_eighNodeScalars (mmR := mmR) (qrR := qrR) (I := I) md p
    (hsem.mono fun h => ⟨h.1, h.2.1, h.2.2.1⟩) ℓ₀ d lo (Lv := Lv) (Su := Su) (c := c) (t := b)
    R z₂ v (by omega) (by omega)
  refine s₁.wp_bind_keep ((readsOnly_pairLayoutHolds p Ma _ A).and (readsOnly_cellsHold
      [(p, par, 2, some β), (p, c, 0, some o), (p, c, 1, some z₂), (p, c, 2, some h),
        (p, c, 3, some m), (p, Lv, 2 * d, some R)])) (by fp_omega [lMa, lpar, lc, lLv])
    ⟨hR, hv, hc1, hN.mono fun h => ⟨h.1, h.2.2, writable_of_shape_eq rfl ht (by omega)⟩⟩
    ⟨hA, (((((cellsHold_nil _).cons hR).cons hc3).cons hc2 |>.cons hc1).cons hc0).cons hβ⟩
    fun st₁ hm₁ h₁ ⟨hA₁, hC₁⟩ => ?_
  have s₂ := spec_eighNodeSign (mmR := mmR) (qrR := qrR) hmm md p n F d lo k hsem hflag
    (Ma := Ma) (Lv := Lv) (par := par) (c := c) (t := b) (sp := b + 1) (W := b + 2)
    (B := b + 3) (s₀ := b + 7) A R β z₂ ((eighTapeMachine I p mmR qrR).mul
      ((eighTapeMachine I p mmR qrR).div R ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d))) v)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine s₂.wp_bind_keep ((readsOnly_cellsHold [(p, c, 0, some o), (p, c, 1, some z₂),
      (p, c, 2, some h), (p, c, 3, some m)]).and (readsOnly_cellsHold [(p, b, 0, some
        ((eighTapeMachine I p mmR qrR).div R z₂)), (p, b, 1, some ((eighTapeMachine I p mmR
          qrR).neg ((eighTapeMachine I p mmR qrR).div R z₂)))])) (by fp_omega [lc])
    ⟨(Store.size_eq_of_shape_eq hm₁.1).trans hsz, hA₁, h₁.2.2.1, hC₁.read (.head _),
      hC₁.read (.tail _ (.tail _ (.head _))), hC₁.read (.tail _ (.tail _ (.tail _
        (.tail _ (.tail _ (.head _)))))), hN.mono fun h => ⟨h.1, h.2.1,
        writable_of_shape_eq hm₁.1 (hW 0 (by omega)) hkk,
        writable_of_shape_eq hm₁.1 hsp (by omega), writable_of_shape_eq hm₁.1 (hW 1 (by omega))
          hkk⟩⟩
    ⟨hC₁.sub (by simp), ((cellsHold_nil _).cons h₁.2.1).cons h₁.1⟩ fun st₂ hm₂ h₂ ⟨hC₂, hT₂⟩ => ?_
  have hm := hm₁.trans hm₂
  have s₃ := spec_eighNodeProjectors (mmR := mmR) (qrR := qrR) md hs p k (c := c) (B := b + 3)
    (T := b + 4) (Pp := b + 5) (Pm := b + 6) Bm o z₂ m (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  refine s₃.wp_bind_keep ((readsOnly_cellsHold [(p, c, 2, some h)]).and (readsOnly_cellsHold _))
    (by fp_omega [lc]) ⟨hBm ▸ h₂.1, hC₂.read (.head _), hC₂.read (.tail _ (.head _)),
      hC₂.read (.tail _ (.tail _ (.tail _ (.head _)))), hN.mono fun h => ⟨h.1,
        writable_of_shape_eq hm.1 (hW 2 (by omega)) hkk,
        writable_of_shape_eq hm.1 (hW 3 (by omega)) hkk,
        writable_of_shape_eq hm.1 (hW 4 (by omega)) hkk⟩⟩
    ⟨hC₂.sub (by simp), hT₂⟩ fun st₃ hm₃ h₃ ⟨hC₃, hT₃⟩ => ?_
  have s₄ := spec_ztraceRe (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR)
    (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md hs p k (X := b + 5) (xo := 0)
    (dst := ⟨b, 5⟩) Ppm (show b ≠ b + 5 by omega)
  refine s₄.wp_bind_keep ((readsOnly_cellsHold _).and ((readsOnly_cellsHold _).and
      ((readsOnly_pairLayoutHolds p (b + 5) 0 _).and (readsOnly_pairLayoutHolds p (b + 6) 0 _))))
    (by fp_omega [lc])
    ⟨hPp ▸ h₃.1, Mode.needs_of (writable_of_shape_eq (hm.trans hm₃).1 ht (by simp)) md⟩
    ⟨hC₃, hT₃, hPp ▸ h₃.1, hPm ▸ h₃.2.1⟩ fun st₄ hm₄ h₄ ⟨hC₄, hP₄⟩ => ?_
  have s₅ := RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .add)
    (dst := ⟨b, 6⟩) (x := ⟨b, 5⟩) (y := ⟨c, 2⟩) (b := h)
    (a := (eighTapeMachine I p mmR qrR).traceRe Ppm))
  refine s₅.wp_run_keep ((readsOnly_cellsHold _).and ((readsOnly_pairLayoutHolds p (b + 5) 0
      _).and (readsOnly_pairLayoutHolds p (b + 6) 0 _))) (by fp_omega)
    ⟨h₄.1, hC₄.read (.head _), Mode.needs_and.mpr ⟨hs.mono fun h =>
      h.bin_ok p .add _ _ trivial (fun h => nomatch h) trivial,
      Mode.needs_of (writable_of_shape_eq (hm.trans hm₃ |>.trans hm₄).1 ht (by simp)) md⟩⟩
    hP₄ fun st₅ hm₅ h₅ ⟨hT₅, hP₅⟩ => ?_
  exact ⟨(hm.trans hm₃ |>.trans hm₄ |>.trans hm₅).of_sub (by simp [matBlock, hkk']),
    hT₅.read (.head _), hT₅.read (.tail _ (.head _)), h₅.1, hP₅.1, hP₅.2,
    h₅.2.trans (h₄.2.trans (h₃.2.2.trans (h₂.2.trans h₁.2.2.2)))⟩

omit [Inhabited K] [AddMonoid C] in
/-- After $m$ releases a store has $m$ buffers fewer. -/
private theorem size_iterate_release (st : St P K C) (p : P) (len w : ℕ) :
    ∀ m, ((·.release p len w)^[m] st).store.size = st.store.size - m
  | 0 => rfl
  | m + 1 => by
    have ih := size_iterate_release st p len w m
    rw [Function.iterate_succ_apply']
    change Array.size (Array.pop _) = _
    rw [Array.size_pop, ih]
    omega

omit [Inhabited K] in
/-- **The scratch prefix of a node step.** If the store has $b$ buffers in every state satisfying
`pre`, and the body of `NLAlib.eighNodeBlock` (the set-up, the clamp and the branch) at the
scratch handles $b, \dots, b + 6$ meets a specification from every state that has the seven
scratch buffers on top of a state satisfying `pre` (reads and shapes below $b$ and the tape
positions kept), modifying `fp` and the scratch, then the node block meets the specification
whose footprint is `fp` and whose postcondition is the body's read below $b$ after the seven
releases. No printed source. -/
theorem spec_eighNodeBlock_of_body {m : Mode} (p : P) (mm qr : ι) (n L F d lo k : IExp ℕ)
    (par Lv Su Sg Ma Qa Sz Kd Kp : ℕ) (one two half negone sqh : Cell ℕ ℕ) {b : ℕ}
    {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    {fp : List (ℕ × ℕ × ℕ)} (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st st', pre st → st'.store.size = b + 7 →
      (∀ q x i, x < b → st'.store.read q x i = st.store.read q x i) →
      (∀ x < b, st'.store.shape[x]? = st.store.shape[x]?) → st'.store.shape[b]? = some (p, 7) →
      st'.store.shape[b + 1]? = some (p, 2) →
      (∀ j < 5, st'.store.shape[b + 2 + j]? = some (p, (2 * (n * n) : IExp ℕ).eval)) →
      st'.pos = st.pos → pre' st')
    (h : Spec m I pre' (do
        ins (.bin p .div ⟨b, 0⟩ ⟨Lv, 2 * d⟩ two)
        ins (.un p .neg ⟨b, 1⟩ ⟨b, 0⟩)
        ins (.litIdx p ⟨b, 2⟩ (L + d))
        ins (.bin p .div ⟨b, 3⟩ ⟨Lv, 2 * d⟩ ⟨b, 2⟩)
        ins (.bin p .mul ⟨b, 4⟩ ⟨b, 3⟩ ⟨Su, lo⟩)
        zhermShift p k Ma (eighBlockOff n d lo) ⟨b, 4⟩ (b + 2) 0
        ins (.copy p ⟨b + 1, 0⟩ ⟨par, 2⟩)
        ins (.bin p .mul ⟨b + 1, 1⟩ two ⟨Lv, 2 * d⟩)
        eighSignBlock p mm k F (b + 2) 0 (b + 1) 0 (b + 3) 0
        zhermShift p k (b + 3) 0 negone (b + 4) 0
        zhermScale p k (b + 4) 0 two (b + 5) 0
        zhermShift p k (b + 3) 0 one (b + 4) 0
        zneg p k k (b + 4) 0 (b + 4) 0
        zhermScale p k (b + 4) 0 two (b + 6) 0
        ztraceRe p k (b + 5) 0 ⟨b, 5⟩
        ins (.bin p .add ⟨b, 6⟩ ⟨b, 5⟩ half)
        eighClampBlock p k ⟨b, 6⟩ ⟨b, 2⟩ ⟨b, 3⟩
        Builder.bindIdx p ⟨b, 6⟩ k fun kp => do
          eighWhen (1 - (k - .var kp))
            (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) ⟨b, 0⟩
              ⟨Sz, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 2)
          eighWhen (1 - .var kp)
            (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) ⟨b, 1⟩
              ⟨Sz, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 3)
          eighWhen (.var kp * (k - .var kp))
            (eighSplitBlock p mm qr n d lo k (.var kp) Sg (b + 5) (b + 6) Ma Qa Sz Kd Kp two
              ⟨b, 0⟩ ⟨b, 1⟩ sqh) : Builder P ι ℕ ℕ Unit).run
      (fp ++ [(b, 0, 7), (b + 1, 0, 2), (b + 2, 0, (2 * (n * n) : IExp ℕ).eval),
        (b + 3, 0, (2 * (n * n) : IExp ℕ).eval), (b + 4, 0, (2 * (n * n) : IExp ℕ).eval),
        (b + 5, 0, (2 * (n * n) : IExp ℕ).eval), (b + 6, 0, (2 * (n * n) : IExp ℕ).eval)]) post')
    (hpost : ∀ st s s', pre st → post' s s' → s.pos = st.pos → s'.store.size = b + 7 →
      ∀ s'' : St P K C, (∀ q x i, x < b → s''.store.read q x i = s'.store.read q x i) →
        s''.pos = s'.pos → post st s'') :
    RoutineSpec m I pre (eighNodeBlock p mm qr n L F d lo k par Lv Su Sg Ma Qa Sz Kd Kp one two
      half negone sqh) fp post := by
  have hb₂ : ∀ s, (∃ s₁, (∃ st, pre st ∧ s₁ = st.allocate p (7 : IExp ℕ).eval (I.width p)) ∧
      s = s₁.allocate p (2 : IExp ℕ).eval (I.width p)) → s.store.size = b + 2 := by
    rintro _ ⟨_, ⟨st, hst, rfl⟩, rfl⟩
    simp [St.size_allocate, hb st hst]
  refine RoutineSpec.scope (Spec.allocBind_named (b := b) hb (Spec.allocBind_named (b := b + 1)
    (fun _ ⟨st, hst, e⟩ => by rw [e, St.size_allocate, hb st hst]) ?_))
  let Q : St P K C → St P K C → Prop := fun s₂ s'' => ∀ s₁, (∃ st, pre st ∧
    s₁ = st.allocate p (7 : IExp ℕ).eval (I.width p)) →
    s₂ = s₁.allocate p (2 : IExp ℕ).eval (I.width p) → ∀ st, pre st →
    s₁ = st.allocate p (7 : IExp ℕ).eval (I.width p) →
    post st ((s''.release p (2 : IExp ℕ).eval (I.width p)).release p (7 : IExp ℕ).eval (I.width p))
  let G := fp ++ [(b, 0, (7 : IExp ℕ).eval)] ++ [(b + 1, 0, (2 : IExp ℕ).eval)]
  refine (spec_allocBind_iterate 0 hb₂ (fp := G) (post := Q) ?_).conseq (fun s hs => ⟨s, hs, rfl⟩)
    (fun x hx => by simpa [G] using hx) fun s _ hs hp => hp s hs rfl
  refine spec_allocBind_iterate 1 hb₂ (fp := G) (post := Q) ?_
  refine spec_allocBind_iterate 2 hb₂ (fp := G) (post := Q) ?_
  refine spec_allocBind_iterate 3 hb₂ (fp := G) (post := Q) ?_
  refine spec_allocBind_iterate 4 hb₂ (fp := G) (post := Q) ?_
  refine h.with_modifies.conseq ?_
    (fun x hx => by simpa [G, List.range_succ, Nat.add_assoc, or_assoc] using hx) ?_
  · rintro _ ⟨_, ⟨_, ⟨st, hst, rfl⟩, rfl⟩, rfl⟩
    have hsb := hb st hst
    have h₂ : ∀ x < b, ((st.allocate p (7 : IExp ℕ).eval (I.width p)).allocate p
        (2 : IExp ℕ).eval (I.width p)).store.shape[x]? = st.store.shape[x]? ∧
        ∀ q i, ((st.allocate p (7 : IExp ℕ).eval (I.width p)).allocate p (2 : IExp ℕ).eval
          (I.width p)).store.read q x i = st.store.read q x i := fun x hx => ⟨by
      rw [St.shape_allocate, St.shape_allocate, Array.getElem?_push, Array.getElem?_push,
        if_neg (by simp [Store.size_shape]; omega), if_neg (by simp [Store.size_shape]; omega)],
      fun q i => by rw [St.read_allocate_of_lt _ _ _ _ _ _ _ (by rw [St.size_allocate]; omega),
        St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)]⟩
    obtain ⟨hs5, hr5, hn5, hp5⟩ := iterate_allocate ((st.allocate p (7 : IExp ℕ).eval
      (I.width p)).allocate p (2 : IExp ℕ).eval (I.width p)) p (2 * (n * n) : IExp ℕ).eval
      (I.width p) 5
    have hs2 : ((st.allocate p (7 : IExp ℕ).eval (I.width p)).allocate p (2 : IExp ℕ).eval
        (I.width p)).store.size = b + 2 := by rw [St.size_allocate, St.size_allocate, hsb]
    rw [hs2] at hs5 hn5 hr5
    refine hpre st _ hst hs5 (fun q x i hx => ((hr5 x (by omega)).2 q i).trans ((h₂ x hx).2 q i))
      (fun x hx => (hr5 x (by omega)).1.trans (h₂ x hx).1) ?_ ?_ hn5 hp5
    · rw [(hr5 b (by omega)).1, St.shape_allocate, St.shape_allocate, Array.getElem?_push,
        if_neg (by simp [Store.size_shape]; omega), Array.getElem?_push,
        if_pos (by simp [Store.size_shape]; omega)]
      rfl
    · rw [(hr5 (b + 1) (by omega)).1, St.shape_allocate, St.shape_allocate, Array.getElem?_push,
        if_pos (by simp [Store.size_shape]; omega)]
      rfl
  · rintro _ s'' - ⟨hm, hp⟩ _ - rfl _ - rfl st hst rfl
    obtain ⟨hs5, -, -, hp5⟩ := iterate_allocate ((st.allocate p (7 : IExp ℕ).eval
      (I.width p)).allocate p (2 : IExp ℕ).eval (I.width p)) p (2 * (n * n) : IExp ℕ).eval
      (I.width p) 5
    have hsz : s''.store.size = b + 2 + 5 := by
      rw [Store.size_eq_of_shape_eq hm.1]
      exact hs5.trans (by rw [St.size_allocate, St.size_allocate, hb st hst])
    have h5 := size_iterate_release s'' p (2 * (n * n) : IExp ℕ).eval (I.width p) (4 + 1)
    refine hpost st _ s'' hst hp hp5 (by omega) _ (fun q x i hx => ?_)
      (ReadsOnly.iterate_release (readsOnly_read p 0 0 _) (by simp) p
        (2 * (n * n) : IExp ℕ).eval (I.width p) 5 s'' hsz rfl).2
    rw [St.read_release_of_lt _ _ _ _ _ (by simp [St.release]; omega),
      St.read_release_of_lt _ _ _ _ _ (by omega)]
    exact (ReadsOnly.iterate_release (readsOnly_read q x i _) (fun y hy => by
      simp only [List.mem_singleton] at hy; subst hy; omega) p (2 * (n * n) : IExp ℕ).eval
      (I.width p) 5 s'' hsz rfl).1

end NLAlib
