/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode.SignStep
public import NLAlib.Matrix.Computation.SpectralBisectionNode.SplitSuccess

/-!
# The split block of the spectral bisection node step

A successful run of the split block of the node step of `NLAlib.eighProg` writes the outcome of the
split of `NLAlib.eighStep` on the machine of the semantics: the two children's matrices, sizes and
kinds, and the bases of the deflations; every cell outside the node's window is unchanged.

## Main results

* `NLAlib.holds_of_exec_eighSplitBlock`: what a successful split computes.
* `NLAlib.holds_of_exec_eighSplitBlock_frame`: the same, with the precise frame of the node's
  window.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The node step -/
/-- A packed complex entry lies in its block. -/
private theorem pair_idx_lt_node {l m : ℕ} (i : Fin l) (j : Fin m) (t : Fin 2) :
    2 * ((i : ℕ) + l * j) + t < 2 * (l * m) := by
  have := i.2; have := j.2; have := t.2
  have : l * ((j : ℕ) + 1) ≤ l * m := Nat.mul_le_mul_left l j.2
  nlinarith

/-- A cell is disjoint from a block inside a window it avoids. -/
theorem blockDisjoint_of_window {b i B off len lo' hi' : ℕ} (h : b = B → i < lo' ∨ hi' ≤ i)
    (h1 : lo' ≤ off) (h2 : off + len ≤ hi') : blockDisjoint (b, i, 1) (B, off, len) = true := by
  unfold blockDisjoint
  by_cases hb : b = B
  · rcases h hb with h | h
    · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl (Or.inr (by omega))
    · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr (by omega)
  · simp [hb]

omit [Inhabited K] in
/-- Name the state of a run. -/
theorem name_state_node {X : Stmt P ι ℕ ℕ} {s s' : St P K C} (h : exec I X s = some s')
    {Q : Prop} (k : ∀ σ : St P K C, σ.store = s.store → σ.pos = s.pos → exec I X σ = some s' → Q) :
    Q := k s rfl rfl h

/-- Seven handles, three below `s₀` and four from `s₀` on, are distinct. -/
private theorem nodup_def_node {a b c s₀ G Y Qf Rf : ℕ} (hab : a = b → False) (hac : a = c → False)
    (hbc : b = c → False) (ha : a < s₀) (hb : b < s₀) (hc : c < s₀) (h4 : [G, Y, Qf, Rf].Nodup)
    (hG : s₀ ≤ G) (hY : s₀ ≤ Y) (hQ : s₀ ≤ Qf) (hR : s₀ ≤ Rf) : [a, b, G, Y, Qf, Rf, c].Nodup := by
  have : a ≠ b := hab; have : a ≠ c := hac; have : b ≠ c := hbc
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h4 ⊢
  omega

/-- Six handles, two below `s₀` and four from `s₀` on, are distinct. -/
private theorem nodup_cmp_node {a b s₀ Qh C1 C2 C3 : ℕ} (hab : a = b → False) (ha : a < s₀)
    (hb : b < s₀) (h4 : [Qh, C1, C2, C3].Nodup) (h1 : s₀ ≤ Qh) (h2 : s₀ ≤ C1) (h3 : s₀ ≤ C2)
    (h5 : s₀ ≤ C3) : [a, b, Qh, C1, C2, C3].Nodup := by
  have : a ≠ b := hab
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h4 ⊢
  omega

/-- A handle below `s₀` is not among four from `s₀` on and another. -/
private theorem notmem5_node {x s₀ G Y Qf Rf c : ℕ} (hx : x < s₀) (hG : s₀ ≤ G) (hY : s₀ ≤ Y)
    (hQ : s₀ ≤ Qf) (hR : s₀ ≤ Rf) (hc : x = c → False) : x ∉ [G, Y, Qf, Rf, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨by omega, by omega, by omega, by omega, hc⟩

/-- The index arithmetic of a split inside the window of its node. -/
private theorem split_arith_node {n d lo k kp : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k) :
    2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) * (d + 1) + 2 * n * lo ∧
    2 * (n * n) * (d + 1) + 2 * n * lo + 2 * (kp * kp) ≤
      2 * (n * n) * (d + 1) + 2 * n * (lo + kp) ∧
    2 * (n * n) * (d + 1) + 2 * n * (lo + kp) + 2 * ((k - kp) * (k - kp)) ≤
      2 * (n * n) * (d + 1) + 2 * n * (lo + k) ∧
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) ≤ 2 * (n * n) * d + 2 * n * (lo + k) ∧
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) + 2 * (k * (k - kp)) ≤
      2 * (n * n) * d + 2 * n * (lo + k) ∧
    2 * (n * n) * (d + 1) + 2 * n * lo ≤ 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = kp + r := ⟨k - kp, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : kp * kp ≤ n * kp := Nat.mul_le_mul_right _ (by omega)
  have h2 : r * r ≤ n * r := Nat.mul_le_mul_right _ (by omega)
  have h3 : (kp + r) * (kp + r) ≤ n * (kp + r) := Nat.mul_le_mul_right _ (by omega)
  have h4 : n * lo + n * (kp + r) ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The cells a node step at the slot $lo$ of depth $d$ for a node of size $k$ may write in the
arenas. -/
def EighNodeWindow (H : EighArenas) (n d lo k j b i : ℕ) : Prop :=
  (b = H.Qa ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧ i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
    (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
    (b = H.Sz ∧ (i = n * (d + 1) + lo ∨ i = n * (d + 1) + j)) ∨
    ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo)

omit [Inhabited K] in
/-- A held block is kept if every read of its words is kept. -/
private theorem holds_keep_node {s s' : Store P K} {p : P} {b off l m : ℕ}
    {Y : Matrix (Fin l) (Fin m) (K × K)} (hY : pairLayout.Holds s p b off Y)
    (h : ∀ i, off ≤ i → i < off + 2 * (l * m) → s'.read p b i = s.read p b i) :
    pairLayout.Holds s' p b off Y :=
  hY.of_forall_read_eq fun i h1 h2 => h i h1 (by
    change i < off + m * l * 2 at h2
    linarith [Nat.mul_comm l m])

/-- The distinct handles of a split: two arenas and the buffers `Sg`, `Pp`, `Pm` are distinct
when the handles of the arenas and `Sg`, `Pp`, `Pm` are, and the cells `two`, `sg`, `nsg`, `sq`
lie in none of them (stated as implications to `False`, out of `omega`'s sight). -/
private theorem split_handles_ne {H : EighArenas} {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm]) :
    (Sg = Pp → False) ∧ (Sg = Pm → False) ∧ (Sg = H.Qa → False) ∧ (Pp = H.Qa → False) ∧
      (Pm = H.Qa → False) ∧ (H.Ma = H.Qa → False) ∧ (H.Sz = H.Kd → False) ∧
      (H.Sz = H.Kp → False) ∧ (H.Kd = H.Kp → False) ∧ (H.Qa = H.Sz → False) ∧
      (H.Qa = H.Kd → False) ∧ (H.Qa = H.Kp → False) ∧ (H.Ma = H.Sz → False) ∧
      (H.Ma = H.Kd → False) ∧ (H.Ma = H.Kp → False) ∧ (sq.buf = H.Qa → False) ∧
      (two.buf = H.Qa → False) ∧ (sg.buf = H.Qa → False) ∧ (nsg.buf = H.Qa → False) ∧
      (two.buf = H.Ma → False) ∧ (sg.buf = H.Ma → False) ∧ (nsg.buf = H.Ma → False) := by
  have cc : ∀ c ∈ [two, sg, nsg, sq], ∀ b ∈ H.handles ++ [Sg, Pp, Pm], c.buf = b → False :=
    fun c hc b hb h => hcells c hc (h ▸ hb)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, cc sq (by simp) H.Qa (by simp [EighArenas.handles]),
    cc two (by simp) H.Qa (by simp [EighArenas.handles]),
    cc sg (by simp) H.Qa (by simp [EighArenas.handles]),
    cc nsg (by simp) H.Qa (by simp [EighArenas.handles]),
    cc two (by simp) H.Ma (by simp [EighArenas.handles]),
    cc sg (by simp) H.Ma (by simp [EighArenas.handles]),
    cc nsg (by simp) H.Ma (by simp [EighArenas.handles])⟩ <;>
  simp [EighArenas.handles, h] at hbufs

/-- The two deflations of a split, from a state `σ` whose buffers below `s₀` hold the projectors
$\mathbf{P}_\pm$ at offset $0$ of `Pp`, `Pm`, the level's Gaussian words in `Sg` and the stored
$\sqrt{1/2}$ in `sq`, the scratch buffers `G`, `Y`, `Qf`, `Rf` from `s₀` on: the bases
$\mathbf{Q}_\pm$ of `NLAlib.holds_of_exec_eighSplitBlock` at the node's block of `Qa`, every cell
of a buffer below `s₀` outside that block kept, the shape and the tape positions too. -/
private theorem split_deflations_holds {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp) {Qa Sg Pp Pm G Y Qf Rf : ℕ}
    {sq : Cell ℕ ℕ} {σ σ₃ σ₄ : St P K C} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)} (s₀ : ℕ)
    (nS4 : ∀ b, b < s₀ → b ∉ [G, Y, Qf, Rf]) (lQa : Qa < s₀) (lSg : Sg < s₀) (lPm : Pm < s₀)
    (lsq : sq.buf < s₀) (hnd₁ : [Sg, Pp, G, Y, Qf, Rf, Qa].Nodup)
    (hnd₂ : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (dSgQa : Sg = Qa → False) (dPmQa : Pm = Qa → False) (sqQa : sq.buf = Qa → False)
    (hPp : pairLayout.Holds σ.store p Pp 0 Ppm) (hPm : pairLayout.Holds σ.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), σ.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hsq : σ.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h₃ : exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const kp) (.const lo)
      (if true then 0 else 1) Sg sq Pp G Y Qf Rf Qa
        (eighBlockOff (.const n) (.const d) (.const lo))).run σ = some σ₃)
    (h₄ : exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const (k - kp)) (.const lo)
      (if false then 0 else 1) Sg sq Pm G Y Qf Rf Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe))).run σ₃ =
      some σ₄) :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    pairLayout.Holds σ₄.store p Qa (2 * (n * n) * d + 2 * n * lo)
        (deflate M kp Ppm (leadingBlock k (s.2 true))) ∧
      pairLayout.Holds σ₄.store p Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))
        (deflate M (k - kp) Pmm (leadingBlock k (s.2 false))) ∧
      (∀ q b i, b < s₀ → (b = Qa → i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * (lo + k) ≤ i) →
        σ₄.store.read q b i = σ.store.read q b i) ∧
      σ₄.store.shape = σ.store.shape ∧ σ₄.pos = σ.pos := by
  intro M s
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by
    simp [eighBlockOff]
  obtain ⟨hQp3, hf3, hsh3, hp3⟩ := holds_of_exec_eighDeflateBlock hmm hqr p n k kp d lo hk
    hkpk.le true hPp hsq hSg hnd₁ hsqb h₃
  rw [hbo] at hQp3 hf3
  have hk3 : ∀ q b i, s₀ > b → b ≠ Qa → σ₃.store.read q b i = σ.store.read q b i :=
    fun q b i h1 h2 => hf3 q b i (nS4 _ (by omega)) (by simp [blockDisjoint, h2])
  obtain ⟨hQm4, hf4, hsh4, hp4⟩ := holds_of_exec_eighDeflateBlock hmm hqr p n k (k - kp) d lo hk
    (Nat.sub_le _ _) false (fun i j t => (hk3 _ _ _ lPm dPmQa).trans (hPm i j t))
    ((hk3 _ _ _ lsq sqQa).trans hsq) (fun w hw => (hk3 _ _ _ lSg dSgQa).trans (hSg w hw))
    hnd₂ hsqb h₄
  simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat, hbo, hkpe] at hQm4 hf4
  obtain ⟨-, -, -, F6, F7, -⟩ := split_arith_node (d := d) hk hkpk
  refine ⟨holds_keep_node hQp3 fun i _ hi => hf4 p _ i (nS4 _ lQa) (by
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq]
      left; omega), hQm4, fun q b i hb hbQ => ?_, hsh4.trans hsh3, hp4.trans hp3⟩
  rw [hf4 q b i (nS4 b hb) (blockDisjoint_of_window hbQ (by linarith [Nat.zero_le (k * kp)])
      (by linarith)),
    hf3 q b i (nS4 b hb) (blockDisjoint_of_window hbQ (by linarith) (by linarith))]

/-- The two compressions of a split, from a state `σ` whose buffers below `s₀` hold the node
matrix $\mathbf{A}$, the bases $\mathbf{Q}_\pm$ at the node's block of `Qa` and the cells `two`,
`sg`, `nsg` holding $c_2$, $\sigma$, $-\sigma$, the scratch buffers `Qh`, `C1`, `C2`, `C3` from
`s₀` on: the compressions of `NLAlib.holds_of_exec_eighSplitBlock` at the blocks of the slots $lo$
and $lo + k_+$ of depth $d + 1$ in `Ma`, every cell of a buffer below `s₀` outside the node's
block of depth $d + 1$ kept, the shape and the tape positions too. -/
private theorem split_compressions_holds {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ)
    (hkpe : kpe.eval = kp) {Qa Ma Qh C1 C2 C3 : ℕ} {two sg nsg : Cell ℕ ℕ} {c₂ σ' : K}
    {σ σ₅ σ₆ : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    (s₀ : ℕ) (nC4 : ∀ b, b < s₀ → b ∉ [Qh, C1, C2, C3]) (lQa : Qa < s₀) (lMa : Ma < s₀)
    (ltwo : two.buf < s₀) (lnsg : nsg.buf < s₀) (hnd : [Qa, Ma, Qh, C1, C2, C3].Nodup)
    (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧ sg.buf ∉ [Qh, C1, C2, C3] ∧
      nsg.buf ∉ [Qh, C1, C2, C3])
    (dMaQa : Ma = Qa → False) (twoMa : two.buf = Ma → False) (sgMa : sg.buf = Ma → False)
    (nsgMa : nsg.buf = Ma → False)
    (hA : pairLayout.Holds σ.store p Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hQp : pairLayout.Holds σ.store p Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds σ.store p Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (htwo : σ.store.read p two.buf two.idx.eval = some c₂)
    (hσ : σ.store.read p sg.buf sg.idx.eval = some σ')
    (hnσ : σ.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ'))
    (h₅ : exec I (eighCompressBlock p mm (.const k) (.const kp) Qa
      (eighBlockOff (.const n) (.const d) (.const lo)) Ma
      (eighBlockOff (.const n) (.const d) (.const lo))
      (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3).run σ = some σ₅)
    (h₆ : exec I (eighCompressBlock p mm (.const k) (.const (k - kp)) Qa
      (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) Ma
      (eighBlockOff (.const n) (.const d) (.const lo))
      (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3).run σ₅ =
      some σ₆) :
    let M := eighTapeMachine I p mmR qrR
    pairLayout.Holds σ₆.store p Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) c₂) σ') ∧
      pairLayout.Holds σ₆.store p Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) c₂) (M.neg σ')) ∧
      (∀ q b i, b < s₀ → (b = Ma → i < 2 * (n * n) * (d + 1) + 2 * n * lo ∨
          2 * (n * n) * (d + 1) + 2 * n * (lo + k) ≤ i) →
        σ₆.store.read q b i = σ.store.read q b i) ∧
      σ₆.store.shape = σ.store.shape ∧ σ₆.pos = σ.pos := by
  intro M
  obtain ⟨F1, F3, F4, -, -, F2⟩ := split_arith_node (d := d) hk hkpk
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by simp [eighBlockOff]
  have hbo1 : (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.const lo)).eval =
      2 * (n * n) * (d + 1) + 2 * n * lo := by simp [eighBlockOff]
  have hbo2 : (eighBlockOff (IExp.const n) (IExp.const d + 1)
      (IExp.const lo + kpe)).eval = 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
    simp [eighBlockOff, hkpe]
  have hqo2 : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo) +
      2 * (IExp.const k * kpe)).eval = 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) := by
    simp [eighBlockOff, hkpe]
  obtain ⟨hAp5, hf5, hsh5, hp5⟩ := holds_of_exec_eighCompressBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p k kp (by rw [hbo]; exact hQp) (by rw [hbo]; exact hA) htwo hσ hnd
    ⟨hcells.1, hcells.2.1⟩
    ⟨by simp [blockDisjoint, show Ma ≠ two.buf from fun h => twoMa h.symm],
      by simp [blockDisjoint, show Ma ≠ sg.buf from fun h => sgMa h.symm]⟩ h₅
  rw [hbo1] at hAp5 hf5
  have hk5 : ∀ q b i, s₀ > b → b ≠ Ma → σ₅.store.read q b i = σ.store.read q b i :=
    fun q b i h1 h2 => hf5 q b i (nC4 _ (by omega)) (by simp [blockDisjoint, h2])
  obtain ⟨hAm6, hf6, hsh6, hp6⟩ := holds_of_exec_eighCompressBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p k (k - kp)
    (by rw [hqo2]; exact fun i j t => (hk5 _ _ _ lQa (fun h => dMaQa h.symm)).trans (hQm i j t))
    (by
      rw [hbo]
      exact holds_keep_node hA fun i _ hi => hf5 p _ i (nC4 _ lMa) (by
        simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          decide_eq_true_eq]
        left; linarith))
    ((hk5 _ _ _ ltwo twoMa).trans htwo) ((hk5 _ _ _ lnsg nsgMa).trans hnσ) hnd
    ⟨hcells.1, hcells.2.2⟩
    ⟨by simp [blockDisjoint, show Ma ≠ two.buf from fun h => twoMa h.symm],
      by simp [blockDisjoint, show Ma ≠ nsg.buf from fun h => nsgMa h.symm]⟩ h₆
  rw [hbo2] at hAm6 hf6
  refine ⟨fun i j t => ?_, hAm6, fun q b i hb hbM => ?_, hsh6.trans hsh5, hp6.trans hp5⟩
  · refine (hf6 _ _ _ (nC4 _ lMa) ?_).trans (hAp5 i j t)
    have := pair_idx_lt_node i j t
    simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq]
    left
    change _ + (2 * _ + _) + 1 ≤ _
    linarith
  · rw [hf6 q b i (nC4 b hb) (blockDisjoint_of_window hbM (by linarith) (by linarith)),
      hf5 q b i (nC4 b hb) (blockDisjoint_of_window hbM (by linarith)
        (by linarith [Nat.zero_le ((k - kp) * (k - kp))]))]

omit [Inhabited K] in
/-- The records of a split: the sizes $k_+$ and $k - k_+$ in their cells of `Sz` at depth
$d + 1$, the kind $4$ and $k_+ > 0$ in the node's cells of `Kd` and `Kp` (three distinct
buffers); every other cell is kept, the shape and the tape positions too. -/
private theorem split_records_holds (p : P) (n d lo k kp : ℕ) (hkp : 0 < kp) (kpe : IExp ℕ)
    (hkpe : kpe.eval = kp) (H : EighArenas) (dSzKd : H.Sz = H.Kd → False)
    (dSzKp : H.Sz = H.Kp → False) (dKdKp : H.Kd = H.Kp → False) {σ st' : St P K C}
    (h : exec I (do
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run σ = some st') :
    (st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, (b = H.Sz → ¬i = n * (d + 1) + lo ∧ ¬i = n * (d + 1) + (lo + kp)) →
        (b = H.Kd ∨ b = H.Kp → ¬i = n * d + lo) → st'.store.read q b i = σ.store.read q b i) ∧
      st'.store.shape = σ.store.shape ∧ st'.pos = σ.pos := by
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  rw [hr] at h
  obtain ⟨v7, s7, hv7, hw7, h⟩ := exists_of_exec_seq_litIdx h
  rw [hr] at h
  obtain ⟨v8, s8, hv8, hw8, h⟩ := exists_of_exec_seq_litIdx h
  rw [hr] at h
  obtain ⟨v9, s9, hv9, hw9, h⟩ := exists_of_exec_seq_litIdx h
  change exec I (.seq (.instr _) .skip) _ = some st' at h
  obtain ⟨v10, s10, hv10, hw10, h⟩ := exists_of_exec_seq_litIdx h
  rw [exec_skip, Option.some_inj] at h
  subst h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
    IExp.eval_sub, hkpe] at hv7 hw7 hv8 hw8 hv9 hw9 hv10 hw10
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun q b i hS hK => ?_, ?_, rfl⟩
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dSzKp),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl dSzKd),
      Store.read_of_write_eq_some_of_ne hw8 (Or.inr (by omega)),
      Store.read_of_write_eq_some hw7, hv7]
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dSzKp),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl dSzKd),
      Store.read_of_write_eq_some hw8, hv8]
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dKdKp),
      Store.read_of_write_eq_some hw9, hv9]
  · rw [Store.read_of_write_eq_some hw10, hv10]
  · have hSz : b ≠ H.Sz ∨ ¬i = n * (d + 1) + lo ∧ ¬i = n * (d + 1) + (lo + kp) := by
      by_cases h1 : b = H.Sz
      · exact Or.inr (hS h1)
      · exact Or.inl h1
    rw [Store.read_of_write_eq_some_of_ne hw10 ?_, Store.read_of_write_eq_some_of_ne hw9 ?_,
      Store.read_of_write_eq_some_of_ne hw8 (hSz.imp id fun h => h.2),
      Store.read_of_write_eq_some_of_ne hw7 (hSz.imp id fun h => h.1)]
    · by_cases h1 : b = H.Kd
      · exact Or.inr (hK (Or.inl h1))
      · exact Or.inl h1
    · by_cases h1 : b = H.Kp
      · exact Or.inr (hK (Or.inr h1))
      · exact Or.inl h1
  · rw [Store.shape_of_write_eq_some hw10, Store.shape_of_write_eq_some hw9,
      Store.shape_of_write_eq_some hw8, Store.shape_of_write_eq_some hw7]

/-- The body of a split after its eight allocations: the values of
`NLAlib.holds_of_exec_eighSplitBlock`, and every cell of a buffer below `s₀` outside the cell
`sq` and the node's window is kept. -/
private theorem split_body_holds {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp) (H : EighArenas)
    {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    {σ : K} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)} (s₀ : ℕ)
    (hlt : ∀ b ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf], b < s₀)
    (G Y Qf Rf Qh C1 C2 C3 : ℕ) (hge : ∀ X ∈ [G, Y, Qf, Rf, Qh, C1, C2, C3], s₀ ≤ X)
    (hnd : [G, Y, Qf, Rf, Qh, C1, C2, C3].Nodup)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (do
      eighDeflateBlock p mm qr (.const n) (.const k) (kpe) (.const lo) 0 Sg sq Pp G Y Qf Rf
        H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
      eighDeflateBlock p mm qr (.const n) (.const k) (.const k - kpe) (.const lo) 1 Sg sq Pm
        G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
          2 * (.const k * kpe))
      eighCompressBlock p mm (.const k) (kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ (kpe))
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ (kpe)) :
        Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    (pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, b < s₀ → ¬ EighNodeWindow H n d lo k (lo + kp) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M s Qp Qm
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt hge
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lSg, lPp, lPm, ltwo, lsg, lnsg, lsq⟩ := hlt
  obtain ⟨gG, gY, gQf, gRf, gQh, gC1, gC2, gC3⟩ := hge
  obtain ⟨h4a, h4b, -⟩ :=
    List.nodup_append.mp (show ([G, Y, Qf, Rf] ++ [Qh, C1, C2, C3]).Nodup from hnd)
  obtain ⟨dSgPp, dSgPm, dSgQa, dPpQa, dPmQa, dMaQa, dSzKd, dSzKp, dKdKp, dQaSz, dQaKd, dQaKp,
    dMaSz, dMaKd, dMaKp, sqQa, twoQa, sgQa, nsgQa, twoMa, sgMa, nsgMa⟩ :=
    split_handles_ne hbufs hcells
  have nS4 : ∀ b, b < s₀ → b ∉ [G, Y, Qf, Rf] := fun b hb => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega
  have nC4 : ∀ b, b < s₀ → b ∉ [Qh, C1, C2, C3] := fun b hb => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega
  -- the deflations
  rw [exec_eighDeflateBlock_bind_split, exec_eighDeflateBlock_congr_split, hkpe] at h
  obtain ⟨σ3, h3, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_eighDeflateBlock_bind_split, exec_eighDeflateBlock_congr_split] at h
  simp only [IExp.eval_sub, IExp.eval_const, hkpe] at h
  obtain ⟨σ4, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hQp4, hQm4, hf4, hsh4, hp4⟩ := split_deflations_holds hmm hqr p n d lo k kp hk hkpk
    kpe hkpe s₀ nS4 lQa lSg lPm lsq
    (nodup_def_node dSgPp dSgQa dPpQa lSg lPp lQa h4a gG gY gQf gRf)
    (nodup_def_node dSgPm dSgQa dPmQa lSg lPm lQa h4a gG gY gQf gRf)
    (notmem5_node lsq gG gY gQf gRf sqQa) dSgQa dPmQa sqQa hPp hPm hSg hsq
    (by exact h3) (by exact h4)
  have hk4 : ∀ q b i, b < s₀ → b ≠ H.Qa → σ4.store.read q b i = st.store.read q b i :=
    fun q b i h1 h2 => hf4 q b i h1 fun h => absurd h h2
  -- the compressions
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split, hkpe] at h
  obtain ⟨σ5, h5, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split] at h
  simp only [IExp.eval_sub, IExp.eval_const, hkpe] at h
  obtain ⟨σ6, h6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hAp6, hAm6, hf6, hsh6, hp6⟩ := split_compressions_holds hmm p n d lo k kp hk hkpk kpe
    hkpe s₀ nC4 lQa lMa ltwo lnsg
    (nodup_cmp_node (fun h => dMaQa h.symm) lQa lMa h4b gQh gC1 gC2 gC3)
    ⟨nC4 _ ltwo, nC4 _ lsg, nC4 _ lnsg⟩ dMaQa twoMa sgMa nsgMa
    (fun i j t => (hk4 _ _ _ lMa dMaQa).trans (hA i j t)) hQp4 hQm4
    ((hk4 _ _ _ ltwo twoQa).trans htwo) ((hk4 _ _ _ lsg sgQa).trans hσ)
    ((hk4 _ _ _ lnsg nsgQa).trans hnσ) (by exact h5) (by exact h6)
  have hk6 : ∀ q b i, b < s₀ → b ≠ H.Ma → σ6.store.read q b i = σ4.store.read q b i :=
    fun q b i h1 h2 => hf6 q b i h1 fun h => absurd h h2
  -- the records
  obtain ⟨⟨r1, r2, r3, r4⟩, hfr, hshr, hpr⟩ := split_records_holds p n d lo k kp hkp kpe hkpe H
    dSzKd dSzKp dKdKp h
  have hrec : ∀ q b i, b ≠ H.Sz → b ≠ H.Kd → b ≠ H.Kp →
      st'.store.read q b i = σ6.store.read q b i := fun q b i h1 h2 h3 =>
    hfr q b i (fun h => absurd h h1) fun h => (h.elim h2 h3).elim
  refine ⟨⟨fun i j t => (hrec _ _ _ dQaSz dQaKd dQaKp).trans
      ((hk6 _ _ _ lQa (fun h => dMaQa h.symm)).trans (hQp4 i j t)),
    fun i j t => (hrec _ _ _ dQaSz dQaKd dQaKp).trans
      ((hk6 _ _ _ lQa (fun h => dMaQa h.symm)).trans (hQm4 i j t)),
    fun i j t => (hrec _ _ _ dMaSz dMaKd dMaKp).trans (hAp6 i j t),
    fun i j t => (hrec _ _ _ dMaSz dMaKd dMaKp).trans (hAm6 i j t), r1, r2, r3, r4⟩,
    fun q b i hb hW => ?_, hshr.trans (hsh6.trans hsh4), hpr.trans (hp6.trans hp4)⟩
  simp only [EighNodeWindow, not_or, not_and, not_lt] at hW
  obtain ⟨hWQ, hWM, hWS, hWK⟩ := hW
  refine (hfr q b i hWS hWK).trans ((hf6 q b i hb fun h1 => ?_).trans (hf4 q b i hb fun h1 => ?_))
  · by_contra hc; push Not at hc; exact absurd (hWM h1 hc.1) (by omega)
  · by_contra hc; push Not at hc; exact absurd (hWQ h1 hc.1) (by omega)

omit [AddMonoid C] [Inhabited K] in
/-- Reads of a store below $m$ pops. -/
theorem read_pops_node : ∀ (m : ℕ) {s : Store P K} {q : P} {b i : ℕ}, b + m < s.size →
    Store.read (Array.pop^[m] s) q b i = s.read q b i
  | 0, _, _, _, _, _ => rfl
  | m + 1, s, q, b, i, h => by
    rw [Function.iterate_succ_apply, read_pops_node m (by simp [Array.size_pop]; omega),
      Store.read_pop_of_lt (by omega)]

omit [Inhabited K] in
/-- The run of an allocation, inverted. -/
theorem alloc_inv_node {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.alloc p len body) st = some st') :
    ∃ st₂, exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st₂ ∧
      { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } = st' := by
  rw [exec_alloc] at h
  exact Option.map_eq_some_iff.mp h

omit [Inhabited K] in
/-- The run of a scoped allocation, inverted. -/
theorem alloc_inv_skip_node {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.seq (.alloc p len body) .skip) st = some st') :
    ∃ st₂, exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st₂ ∧
      { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } = st' :=
  alloc_inv_node ((exec_seq_skip I _ st).symm.trans h)

omit [AddMonoid C] [Inhabited K] in
/-- The buffers a split reads exist: the handles of shaped arenas, `Sg`, `Pp`, `Pm` (held) and
the buffers of the cells `two`, `sg`, `nsg`, `sq` (read) are below the size of the store. -/
private theorem split_handles_lt {n lo k kp D : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k)
    {H : EighArenas} {p : P}
    {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {s : Store P K} {w₂ w₃ w₄ w₅ : K} {d : ℕ}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)} (hH : H.Shaped s p n D)
    (hPp : pairLayout.Holds s p Pp 0 Ppm) (hPm : pairLayout.Holds s p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), s.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : s.read p two.buf two.idx.eval = some w₂) (hσ : s.read p sg.buf sg.idx.eval = some w₃)
    (hnσ : s.read p nsg.buf nsg.idx.eval = some w₄) (hsq : s.read p sq.buf sq.idx.eval = some w₅) :
    ∀ b ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf], b < s.size := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, s.shape[b]? = some x → b < s.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have hk0 : 0 < k := by omega
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl)
  exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv,
    Store.lt_size_of_read_eq_some (hSg 0 hn2),
    Store.lt_size_of_read_eq_some (hPp ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩),
    Store.lt_size_of_read_eq_some (hPm ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩),
    Store.lt_size_of_read_eq_some htwo, Store.lt_size_of_read_eq_some hσ,
    Store.lt_size_of_read_eq_some hnσ, Store.lt_size_of_read_eq_some hsq]

/-- A split writes the outcome of `NLAlib.eighStep`'s split, with its precise frame: the values
of `NLAlib.holds_of_exec_eighSplitBlock`, and every cell outside the node's window
(`NLAlib.EighNodeWindow`) unchanged; `NLAlib.holds_of_exec_eighSplitBlock` is its coarse form. -/
theorem holds_of_exec_eighSplitBlock_frame {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp ℕ)
    (hkpe : kpe.eval = kp) (H : EighArenas)
    {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) kpe Sg
      Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    (pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, ¬ EighNodeWindow H n d lo k (lo + kp) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M s Qp Qm
  have hlt := split_handles_lt hk hkpk hH hPp hPm hSg htwo hσ hnσ hsq
  have hl : ∀ {b}, b ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf] →
      b < st.store.size := hlt _
  obtain ⟨s₁, h₁, e₁⟩ := alloc_inv_skip_node h
  obtain ⟨s₂, h₂, e₂⟩ := alloc_inv_node h₁
  obtain ⟨s₃, h₃, e₃⟩ := alloc_inv_node h₂
  obtain ⟨s₄, h₄, e₄⟩ := alloc_inv_node h₃
  obtain ⟨s₅, h₅, e₅⟩ := alloc_inv_node h₄
  obtain ⟨s₆, h₆, e₆⟩ := alloc_inv_node h₅
  obtain ⟨s₇, h₇, e₇⟩ := alloc_inv_node h₆
  obtain ⟨s₈, h₈, e₈⟩ := alloc_inv_node h₇
  clear h h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hst : st'.store = Array.pop^[8] s₈.store ∧ st'.pos = s₈.pos := by
    subst e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈; exact ⟨rfl, rfl⟩
  rw [hst.1, hst.2]
  clear e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ hst
  refine name_state_node h₈ ?_
  clear h₈
  intro σ₈ hσs hσp h₈
  simp only at hσs hσp
  have hrd : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      σ₈.store.read q b i = st.store.read q b i := fun hb => by
    rw [hσs]
    iterate 8 rw [Store.read_push_of_lt (by first | omega | (simp only [Array.size_push]; omega))]
  obtain ⟨⟨v1, v2, v3, v4, v5, v6, v7, v8⟩, hfr, hsh, hps⟩ := split_body_holds hmm hqr p n d lo k
    kp hk hkp hkpk kpe hkpe H st.store.size hlt _ _ _ _ _ _ _ _ (by simp; omega)
    (by simp [List.nodup_cons]; omega) hbufs
    (fun i j t => (hrd (hl (by simp [EighArenas.handles]))).trans (hA i j t))
    (fun i j t => (hrd (hl (by simp))).trans (hPp i j t))
    (fun i j t => (hrd (hl (by simp))).trans (hPm i j t))
    (fun w hw => (hrd (hl (by simp))).trans (hSg w hw)) ((hrd (hl (by simp))).trans htwo)
    ((hrd (hl (by simp))).trans hσ) ((hrd (hl (by simp))).trans hnσ) hcells
    ((hrd (hl (by simp))).trans hsq) (h := h₈)
  clear h₈
  have hsz8 : s₈.store.size = st.store.size + 8 := by
    rw [Store.size_eq_of_shape_eq hsh, hσs]; simp
  have hpop : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      Store.read (Array.pop^[8] s₈.store) q b i = s₈.store.read q b i :=
    fun hb => read_pops_node 8 (by omega)
  have lQa : H.Qa < st.store.size := hl (by simp [EighArenas.handles])
  have lMa : H.Ma < st.store.size := hl (by simp [EighArenas.handles])
  refine ⟨⟨fun i j t => (hpop lQa).trans (v1 i j t), fun i j t => (hpop lQa).trans (v2 i j t),
    fun i j t => (hpop lMa).trans (v3 i j t), fun i j t => (hpop lMa).trans (v4 i j t),
    (hpop (hl (by simp [EighArenas.handles]))).trans v5,
    (hpop (hl (by simp [EighArenas.handles]))).trans v6,
    (hpop (hl (by simp [EighArenas.handles]))).trans v7,
    (hpop (hl (by simp [EighArenas.handles]))).trans v8⟩, fun q b i hW => ?_, ?_,
    hps.trans hσp⟩
  · by_cases hb : b < st.store.size
    · exact (hpop hb).trans ((hfr q b i hb hW).trans (hrd hb))
    · have hsz' : (Array.pop^[8] s₈.store).size = st.store.size := by
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Array.size_pop,
          hsz8]
        omega
      exact (show Store.read (Array.pop^[8] s₈.store) q b i = none from
        Store.read_eq_none_of_size_le (by omega)).trans
          (Store.read_eq_none_of_size_le (by omega)).symm
  · change Store.shape (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop
      (Array.pop (Array.pop s₈.store)))))))) = _
    simp only [Store.shape_pop, hsh, hσs]
    simp [Store.shape]

/-- A split writes the outcome of `NLAlib.eighStep`'s split: if the kernels of `I` are the
routines `mmR`, `qrR` on interleaved pairs, a successful run of `NLAlib.eighSplitBlock` at the slot
$lo$ of depth $d$ for a node of size $k$ (with $lo + k \le n$) whose matrix $\mathbf{A}$ is held at
its block of `Ma`, with $0 < k_+ < k$, the projectors $\mathbf{P}_\pm$ at offset $0$ of `Pp`, `Pm`,
the level's Gaussian words in `Sg`, and the cells `two`, `sg`, `nsg`, `sq` (outside the arenas,
`Sg`, `Pp` and `Pm`) holding the machine's $\mathrm{fl}(2)$, $\sigma$, $-\sigma$ and the stored
$\sqrt{1/2}$ (`NLAlib.Computation.ScalarSem.sqrtHalf`, computed once by `NLAlib.eighProg`), ends
with: $\mathbf{Q}_+ =$
`NLAlib.deflate M kp Pp G₊` and $\mathbf{Q}_-$ packed at the node's block of `Qa`, the compressions
of `NLAlib.eighStep` at the blocks of the slots $lo$ and $lo + k_+$ of depth $d + 1$ in `Ma`, the
sizes $k_+$ and $k - k_+$ in their cells of `Sz`, the kind $4$ and $k_+$ in the node's cells of `Kd`
and `Kp`; every other cell of the arenas, and every cell outside them, is unchanged ($M$ =
`NLAlib.eighTapeMachine I p mmR qrR`, the test matrices those of the node's samples,
`NLAlib.eighTapeSample`). No printed source.
(Design note §8: the hoist of $\sqrt{1/2}$ to `NLAlib.eighProg` made the split read `sq` only,
so the frame has no exemption and needs no distinctness of `sq`.) -/
theorem holds_of_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkp : 0 < kp) (hkpk : kp < k) (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    {σ : K} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp) Sg
      Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      (∀ q b i, ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M s Qp Qm
  have key := holds_of_exec_eighSplitBlock_frame (Sg := Sg) (Pp := Pp) (Pm := Pm)
    (two := two) (sg := sg) (nsg := nsg) (sq := sq) (σ := σ) (st := st) (st' := st') (A := A)
    (Ppm := Ppm) (Pmm := Pmm) hmm hqr p n d lo k kp hk hkp hkpk (.const kp) rfl H hH
    hbufs hA hPp hPm hSg htwo hσ hnσ hcells hsq h
  refine ⟨key.1.1, key.1.2.1, key.1.2.2.1, key.1.2.2.2.1, key.1.2.2.2.2.1, key.1.2.2.2.2.2.1,
    key.1.2.2.2.2.2.2.1, key.1.2.2.2.2.2.2.2, fun q b i h0 h1' => key.2.1 q b i ?_,
    key.2.2.1, key.2.2.2⟩
  intro hw
  have hnk : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have e1 : 2 * (n * n) * d + 2 * n * (lo + k) ≤ 2 * (n * n) * (d + 1) := by nlinarith
  have e2 : 2 * (n * n) * (d + 1) + 2 * n * (lo + k) ≤ 2 * (n * n) * (d + 1 + 1) := by nlinarith
  have e3 : n * (d + 1) + lo + k ≤ n * (d + 1 + 1) := by nlinarith
  have e4 : n * d + lo < n * (d + 1) := by nlinarith
  unfold EighNodeWindow at hw
  unfold EighArenas.LevelCell at h0 h1'
  rcases hw with ⟨rfl, a, b'⟩ | ⟨rfl, a, b'⟩ | ⟨rfl, hi⟩ | ⟨hb, rfl⟩
  · exact h0 (Or.inl ⟨Or.inr (Or.inr rfl), by omega, by omega⟩)
  · exact h1' (Or.inl ⟨Or.inl rfl, by omega, by omega⟩)
  · exact h1' (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by rcases hi with rfl | rfl <;> omega,
      by rcases hi with rfl | rfl <;> omega⟩))
  · refine h0 (Or.inr (Or.inl ⟨?_, by omega, by omega⟩))
    rcases hb with hb | hb
    · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inr hb))

end NLAlib
