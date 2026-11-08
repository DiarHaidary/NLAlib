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

omit [Inhabited K] in
/-- A conjugate transpose keeps the shape of the store and the tape positions. -/
private theorem shape_pos_of_exec_zconjTranspose (p : P) (m n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hins : ∀ {i : Instr P ℕ ℕ} {s s' : St P K C}, (∀ q d x, i ≠ .draw q d x) →
      exec I (.instr i) s = some s' → s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
    intro i s s' hi hs
    rw [exec_instr] at hs
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨Instr.shape_of_run_eq_some hr, ?_⟩
    cases i with
    | draw q d x => exact absurd rfl (hi q d x)
    | _ => simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr; aesop
  change exec I (.seq (.named _ _ (.seq (.loop _ _) .skip)) .skip) st = some st' at h
  rw [exec_seq_skip, exec_named, exec_seq_skip] at h
  refine forall_of_exec_loop_eq_some I
    (fun _ s => s.store.shape = st.store.shape ∧ s.pos = st.pos) ⟨rfl, rfl⟩ ?_ h
  rintro j - s₁ s₂ ⟨hsh, hps⟩ hex
  change exec I (.seq (.loop _ _) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip] at hex
  refine forall_of_exec_loop_eq_some I
    (fun _ s => s.store.shape = st.store.shape ∧ s.pos = st.pos) ⟨hsh, hps⟩ ?_ hex
  rintro i - s₃ s₄ ⟨hsh, hps⟩ hex
  change exec I (.seq (.instr (.copy _ _ _)) (.seq (.instr (.un _ _ _ _)) .skip)) s₃ =
    some s₄ at hex
  rw [exec_seq] at hex
  obtain ⟨s₅, h₅, hex⟩ := Option.bind_eq_some_iff.mp hex
  rw [exec_seq_skip] at hex
  obtain ⟨hsh₅, hps₅⟩ := hins (by intro _ _ _ h; cases h) h₅
  obtain ⟨hsh₄, hps₄⟩ := hins (by intro _ _ _ h; cases h) hex
  exact ⟨hsh₄.trans (hsh₅.trans hsh), hps₄.trans (hps₅.trans hps)⟩

omit [Inhabited K] in
/-- Blocks of distinct buffers are disjoint. -/
theorem blockDisjoint_of_ne {b b' i i' l l' : ℕ} (h : b ≠ b') :
    blockDisjoint (b, i, l) (b', i', l') = true := by
  simp [blockDisjoint, h]

omit [Inhabited K] in
/-- Disjointness of blocks is symmetric. -/
private theorem blockDisjoint_comm {x y : ℕ × ℕ × ℕ} (h : blockDisjoint x y = true) :
    blockDisjoint y x = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  omega

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
  intro M
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hcells
  obtain ⟨⟨hQaMa, hQaQh, hQaC1, hQaC2, hQaC3⟩, ⟨hMaQh, hMaC1, hMaC2, hMaC3⟩, ⟨hQhC1, hQhC2, hQhC3⟩,
    ⟨hC1C2, hC1C3⟩, hC2C3, -⟩ := hbufs
  obtain ⟨⟨htQh, htC1, htC2, htC3⟩, hsQh, hsC1, hsC2, hsC3⟩ := hcells
  have hne := @blockDisjoint_of_ne
  change exec I (.seq (.named _ _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) (.seq (.named _ _ _) .skip))))) st = some st' at h
  rw [exec_seq] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq] at h
  obtain ⟨s₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq] at h
  obtain ⟨s₃, h₃, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq] at h
  obtain ⟨s₄, h₄, h⟩ := Option.bind_eq_some_iff.mp h
  -- the conjugate transpose
  have h₁' := (exec_seq_skip I _ st).trans h₁
  obtain ⟨hQh, hfr₁⟩ := holds_of_exec_zconjTranspose (I := I) (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p k r hQ (hne (Ne.symm hQaQh)) h₁'
  obtain ⟨hsh₁, hps₁⟩ := shape_pos_of_exec_zconjTranspose p k r h₁'
  -- the two products
  rw [exec_kcall] at h₂ h₃
  obtain ⟨c₁, hc₁, hs₂⟩ := Option.map_eq_some_iff.mp h₂
  obtain ⟨c₂', hc₂, hs₃⟩ := Option.map_eq_some_iff.mp h₃
  have e₂ : s₂.store = c₁ := by rw [← hs₂]
  have e₃ : s₃.store = c₂' := by rw [← hs₃]
  have p₂ : s₂.pos = s₁.pos := by rw [← hs₂]
  have p₃ : s₃.pos = s₂.pos := by rw [← hs₃]
  rw [← e₂] at hc₁
  rw [← e₃] at hc₂
  obtain ⟨hC1, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := r) (m := k)
    (n := k) (a := (Qh, 0)) (b := (Ma, mo.eval)) (c := (C1, 0)) hQh
    (hA.of_forall_read_eq fun i _ _ => hfr₁ p Ma i (hne hMaQh)) (hne (Ne.symm hQhC1))
    (hne (Ne.symm hMaC1)) hc₁
  obtain ⟨hC2, hfr₃⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := r) (m := k)
    (n := r) (a := (C1, 0)) (b := (Qa, qo.eval)) (c := (C2, 0)) hC1
    (hQ.of_forall_read_eq fun i _ _ => (hfr₂ p Qa i (hne hQaC1)).trans
      (hfr₁ p Qa i (hne hQaQh))) (hne (Ne.symm hC1C2)) (hne (Ne.symm hQaC2)) hc₂
  -- the cells `two` and `sg` are kept so far
  have hkeep : ∀ c : Cell ℕ ℕ, c.buf ≠ Qh → c.buf ≠ C1 → c.buf ≠ C2 →
      s₃.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval := fun c h1 h2 h3 =>
    (hfr₃ p _ _ (hne h3)).trans ((hfr₂ p _ _ (hne h2)).trans (hfr₁ p _ _ (hne h1)))
  -- the average and the shift
  have h₄' := (exec_seq_skip I _ s₃).trans h₄
  obtain ⟨hC3, hfr₄, hsh₄, hps₄⟩ := holds_of_exec_zhermAvg (I := I) (toNat := toNat)
    (mmR := mmR) (qrR := qrR) (unif := unif) (normal := normal) p r hC2
    ((hkeep two htQh htC1 htC2).trans htwo) (hne (Ne.symm hC2C3)) (hne htC3) h₄'
  rw [exec_seq_skip] at h
  have h' := (exec_seq_skip I _ s₄).trans h
  obtain ⟨hMa, hfr₅, hsh₅, hps₅⟩ := holds_of_exec_zhermShift (I := I) (toNat := toNat)
    (mmR := mmR) (qrR := qrR) (unif := unif) (normal := normal) p r hC3
    ((hfr₄ p _ _ (hne hsC3)).trans ((hkeep sg hsQh hsC1 hsC2).trans hσ)) (hne hMaC3)
    (blockDisjoint_comm hcocells.2) h'
  refine ⟨hMa, fun q b i hb hbd => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    rw [hfr₅ q b i hbd, hfr₄ q b i (hne hb.2.2.2), hfr₃ q b i (hne hb.2.2.1),
      hfr₂ q b i (hne hb.2.1), hfr₁ q b i (hne hb.1)]
  · rw [hsh₅, hsh₄, Interp.shape_of_kcallStore_eq_some hc₂,
      Interp.shape_of_kcallStore_eq_some hc₁, hsh₁]
  · rw [hps₅, hps₄, p₃, p₂, hps₁]

omit [Inhabited K] in
/-- A write in a block of a buffer of a fixed shape: it succeeds, keeps the shape and every cell
outside the block, leaves the value at the written cell and keeps every initialised cell
initialised. -/
private theorem compress_zw {s₀ s : Store P K} {p : P} {Y yo len k N : ℕ}
    (hY : s₀.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len) (hk : k < N)
    (hsh : s.shape = s₀.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s.read q b i = s₀.read q b i)
    (v : K) :
    ∃ s', s.write p Y (yo + k) v = some s' ∧ s'.shape = s₀.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = s₀.read q b i) ∧
      s'.read p Y (yo + k) = some v ∧
      (∀ b i, (∃ w, s.read p b i = some w) → ∃ w, s'.read p b i = some w) := by
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape v (by rw [hsh]; exact hY)
    (show yo + k < len by omega)
  refine ⟨s', hs', (Store.shape_of_write_eq_some hs').trans hsh, fun q b i hb => ?_,
    Store.read_of_write_eq_some hs', fun b i ⟨w, hw⟩ => ?_⟩
  · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans (hfr q b i hb)
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
    by_cases hbY : b = Y
    · exact Or.inr (by omega)
    · exact Or.inl hbY
  · by_cases hbi : b = Y ∧ i = yo + k
    · obtain ⟨rfl, rfl⟩ := hbi
      exact ⟨v, Store.read_of_write_eq_some hs'⟩
    · exact ⟨w, (Store.read_of_write_eq_some_of_ne hs' (not_and_or.mp hbi)).trans hw⟩

omit [Inhabited K] in
/-- A conjugate transpose succeeds under the standard model when the output block fits. -/
private theorem compress_exists_zconjTranspose {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (m n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {st : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * m)) (X, xo.eval, 2 * (m * n)) = true)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * m) ≤ len) :
    ∃ st', exec I (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo).run st =
      some st' := by
  obtain ⟨len, hYsh, hlen⟩ := hY
  let F : Store P K → Prop := fun s => s.shape = st.store.shape ∧
    ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * m)) = true →
      s.read q b i = st.store.read q b i
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) .skip)) .skip) st = some st'
  rw [exec_seq_skip, exec_named, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I (fun _ σ => F σ.store)
    ⟨rfl, fun _ _ _ _ => rfl⟩ fun j hj σ hσ => ?_).imp fun _ h => h.1
  have hj : j < m := hj
  change ∃ st', exec I (.seq (.loop _ _) .skip) σ = some st' ∧ _
  rw [exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall I (fun _ σ => F σ.store) hσ fun i hi σ' hσ' => ?_
  have hi : i < n := hi
  have hY1 : 2 * (i + n * j) + 1 < 2 * (n * m) := by nlinarith
  have hX1 : 2 * (j + m * i) + 1 < 2 * (m * n) := by nlinarith
  have hrX : ∀ t < 2, ∃ a, σ'.store.read p X (xo.eval + (2 * (j + m * i) + t)) = some a := by
    intro t ht
    rw [hσ'.2 _ _ _ ?_]
    · exact ⟨_, hA ⟨j, hj⟩ ⟨i, hi⟩ ⟨t, ht⟩⟩
    · simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXY ⊢
      omega
  obtain ⟨a, ha⟩ := hrX 0 (by norm_num)
  obtain ⟨a', ha'⟩ := hrX 1 (by norm_num)
  obtain ⟨s₁, hs₁, hsh₁, hfr₁, -, -⟩ := compress_zw (k := 2 * (i + n * j)) hYsh hlen
    (by omega) hσ'.1 hσ'.2 a
  obtain ⟨z, hz, -⟩ := hsem.neg p a'
  obtain ⟨s₂, hs₂, hsh₂, hfr₂, -, -⟩ := compress_zw (k := 2 * (i + n * j) + 1) hYsh hlen
    hY1 hsh₁ hfr₁ z
  have ha'₁ : s₁.read p X (xo.eval + (2 * (j + m * i) + 1)) = some a' := by
    rw [hfr₁ _ _ _ ?_, ← hσ'.2 _ _ _ ?_]
    · exact ha'
    all_goals simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hXY ⊢
    all_goals omega
  change ∃ st', exec I (.seq (.instr (.copy _ _ _)) (.seq (.instr (.un _ _ _ _)) .skip)) σ' =
    some st' ∧ _
  rw [exec_seq_instr_copy I (by exact ha) (by exact hs₁),
    exec_seq_instr_un I (by exact ha'₁) hz (by exact hs₂), exec_skip]
  exact ⟨_, rfl, hsh₂, hfr₂⟩

/-- `zmirror` succeeds under the standard model when the output block fits and every word of its
strict upper triangle holds a value. -/
private theorem exists_exec_zmirror_of_upper {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ}
    {σ : St P K C} (hY : ∃ len, σ.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len)
    (hup : ∀ i j, i < j → j < n →
      (∃ v, σ.store.read p Y (yo.eval + 2 * (i + n * j)) = some v) ∧
        ∃ v, σ.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some v) :
    ∃ st', exec I (zmirror (ι := ι) p (.const n) Y yo).run σ = some st' := by
  refine exists_exec_zmirror p n (B := fun i j =>
    ((σ.store.read p Y (yo.eval + 2 * (i + n * j))).getD default,
      (σ.store.read p Y (yo.eval + 2 * (i + n * j) + 1)).getD default))
    (fun i j hij => ?_) hsem hY
  obtain ⟨⟨v, hv⟩, ⟨w, hw'⟩⟩ := hup i j hij j.2
  simp only [hv, hw', Option.getD_some, and_self]

/-- `zhermShift` succeeds under the standard model when the output block fits, wherever the
cell of the shift is (it may lie in the output block). -/
private theorem compress_exists_zhermShift {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {c : Cell ℕ ℕ} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : ∃ cv, st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zhermShift (ι := ι) p (.const n) X xo c Y yo).run st = some st' := by
  obtain ⟨len, hYsh, hlen⟩ := hY
  have hn (i j : ℕ) (hi : i < n) (hj : j < n) : 2 * (i + n * j) + 1 < 2 * (n * n) := by
    nlinarith
  let G : Store P K → (ℕ → ℕ → Prop) → Prop := fun s S => s.shape = st.store.shape ∧
    (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      s.read q b i = st.store.read q b i) ∧
    (∀ b i, (∃ w, st.store.read p b i = some w) → ∃ w, s.read p b i = some w) ∧
    ∀ i j, S i j → (∃ v, s.read p Y (yo.eval + 2 * (i + n * j)) = some v) ∧
      ∃ v, s.read p Y (yo.eval + 2 * (i + n * j) + 1) = some v
  have hXr : ∀ s S, G s S → ∀ i j, i < n → j < n → ∀ t < 2,
      ∃ a, s.read p X (xo.eval + (2 * (i + n * j) + t)) = some a := by
    intro s S hG i j hi hj t ht
    have := hn i j hi hj
    rw [hG.2.1 _ _ _ ?_]
    · exact ⟨_, hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨t, ht⟩⟩
    · simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXY ⊢
      omega
  -- one write in the block keeps `G`
  have hw : ∀ s S, G s S → ∀ k < 2 * (n * n), ∀ v : K, ∃ s', s.write p Y (yo.eval + k) v =
      some s' ∧ G s' S ∧ s'.read p Y (yo.eval + k) = some v ∧
      ∀ b i, (∃ w, s.read p b i = some w) → ∃ w, s'.read p b i = some w := by
    intro s S hG k hk v
    obtain ⟨s', hs', hsh', hfr', hrd', hmo'⟩ := compress_zw hYsh hlen hk hG.1 hG.2.1 v
    exact ⟨s', hs', ⟨hsh', hfr', fun b i h => hmo' b i (hG.2.2.1 b i h), fun i j h =>
      ⟨hmo' _ _ (hG.2.2.2 i j h).1, hmo' _ _ (hG.2.2.2 i j h).2⟩⟩, hrd', hmo'⟩
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) _))) .skip) st =
    some st'
  rw [exec_seq_skip, exec_named, exec_seq]
  -- the strict upper triangle
  refine Option.exists_bind_eq_some_of_exists (fun σ => G σ.store fun i' j' => i' < j' ∧ j' < n)
    ((exists_exec_loop_eq_some_of_forall I
    (fun j σ => G σ.store fun i' j' => i' < j' ∧ j' < j)
      ⟨rfl, fun _ _ _ _ => rfl, fun _ _ h => h, fun _ _ h => absurd h.2 (Nat.not_lt_zero _)⟩
      (fun j hj σ hσ => by
        have hj : j < n := hj
        change ∃ st', exec I (.seq (.loop _ _) .skip) σ = some st' ∧ _
        rw [exec_seq_skip]
        refine (exists_exec_loop_eq_some_of_forall I
          (fun i σ' => G σ'.store fun i' j' => i' < j' ∧ (j' < j ∨ j' = j ∧ i' < i))
          ⟨hσ.1, hσ.2.1, hσ.2.2.1, fun i' j' h => hσ.2.2.2 i' j' ⟨h.1, by omega⟩⟩
          (fun i hi σ' hσ' => by
            have hi : i < j := hi
            have hk := hn i j (by omega) hj
            obtain ⟨a, ha⟩ := hXr _ _ hσ' i j (by omega) hj 0 (by norm_num)
            obtain ⟨s₁, hs₁, hG₁, hr₁, hm₁⟩ := hw _ _ hσ' (2 * (i + n * j)) (by omega) a
            obtain ⟨a'', ha''⟩ := hXr _ _ hG₁ i j (by omega) hj 1 (by norm_num)
            change ∃ st', exec I (.seq (.instr (.copy _ _ _)) (.seq (.instr (.copy _ _ _))
              .skip)) σ' = some st' ∧ _
            rw [exec_seq_instr_copy I (by exact ha) (by exact hs₁)]
            obtain ⟨s₂', hs₂', hG₂', hr₂', hm₂'⟩ := hw _ _ hG₁ (2 * (i + n * j) + 1) hk a''
            rw [exec_seq_instr_copy I (by exact ha'') (by exact hs₂'), exec_skip]
            refine ⟨_, rfl, hG₂'.1, hG₂'.2.1, hG₂'.2.2.1, fun i' j' h => ?_⟩
            by_cases hij : i' = i ∧ j' = j
            · obtain ⟨rfl, rfl⟩ := hij
              exact ⟨hm₂' _ _ ⟨_, hr₁⟩, ⟨_, hr₂'⟩⟩
            · have := hσ'.2.2.2 i' j' ⟨h.1, by omega⟩
              exact ⟨hm₂' _ _ (hm₁ _ _ this.1), hm₂' _ _ (hm₁ _ _ this.2)⟩)).imp
          fun σ' ⟨h', hG'⟩ => ⟨h', hG'.1, hG'.2.1, hG'.2.2.1, fun i' j' h =>
            hG'.2.2.2 i' j' ⟨h.1, by simp only [IExp.eval_var]; omega⟩⟩))) fun σ₁ hσ₁ => ?_
  rw [exec_seq]
  -- the diagonal
  refine Option.exists_bind_eq_some_of_exists (fun σ => G σ.store fun i' j' => i' < j' ∧ j' < n)
    (exists_exec_loop_eq_some_of_forall I
    (fun _ σ => G σ.store fun i' j' => i' < j' ∧ j' < n) hσ₁ (fun i hi σ hσ => by
        have hi : i < n := hi
        have hk := hn i i hi hi
        obtain ⟨a, ha⟩ := hXr _ _ hσ i i hi hi 0 (by norm_num)
        obtain ⟨cv, hcv⟩ := hσ.2.2.1 _ _ hc
        obtain ⟨v, hv⟩ := hsem.bin_ok p .sub a cv trivial nofun trivial
        obtain ⟨s₁, hs₁, hG₁, -, -⟩ := hw _ _ hσ (2 * (i + n * i)) (by omega) v
        obtain ⟨z, hz⟩ := hsem.lit_ok p 0 trivial
        obtain ⟨s₂, hs₂, hG₂, -, -⟩ := hw _ _ hG₁ (2 * (i + n * i) + 1) hk z
        change ∃ st', exec I (.seq (.instr (.bin _ _ _ _ _)) (.seq (.instr (.lit _ _ _))
          .skip)) σ = some st' ∧ _
        rw [exec_seq_instr_bin I (by exact ha) hcv hv (by exact hs₁),
          exec_seq_instr_lit I hz (by exact hs₂), exec_skip]
        exact ⟨_, rfl, hG₂⟩)) fun σ₂ hσ₂ => ?_
  -- the mirror
  exact exists_exec_zmirror_of_upper hsem p n ⟨len, by rw [hσ₂.1]; exact hYsh, hlen⟩
    fun i j hij hj => hσ₂.2.2.2 i j ⟨hij, hj⟩

omit [AddMonoid C] in
/-- A product kernel call on held matrices succeeds when the output block fits, writes the
product and keeps every cell outside the output block. -/
private theorem compress_exists_kcall {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) {l m n : ℕ} {a b c : ℕ × ℕ} {s : Store P K} {A : Matrix (Fin l) (Fin m) (K × K)}
    {B : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds s p a.1 a.2 A)
    (hB : pairLayout.Holds s p b.1 b.2 B)
    (hca : blockDisjoint (c.1, c.2, n * l * 2) (a.1, a.2, m * l * 2) = true)
    (hcb : blockDisjoint (c.1, c.2, n * l * 2) (b.1, b.2, n * m * 2) = true)
    {len : ℕ} (hc : s.shape[c.1]? = some (p, len)) (hlen : c.2 + n * l * 2 ≤ len) :
    ∃ s', I.kcallStore mm p [l, m, n] [a, b] [c] s = some s' ∧
      pairLayout.Holds s' p c.1 c.2 (mmR A B) ∧ ∀ q b' i,
        blockDisjoint (b', i, 1) (c.1, c.2, n * l * 2) = true → s'.read q b' i = s.read q b' i := by
  obtain ⟨s', hs'⟩ : ∃ s', I.kcallStore mm p [l, m, n] [a, b] [c] s = some s' := by
    rw [hmm.kcallStore_eq p ((EntryLayout.holds_iff_readBlock_eq_some pairLayout s p _ _ A).mp hA)
      ((EntryLayout.holds_iff_readBlock_eq_some pairLayout s p _ _ B).mp hB) hca hcb]
    exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi => ⟨len, hc, by
      rw [EntryLayout.size_toArray] at hi
      change i < n * l * 2 at hi
      omega⟩
  exact ⟨s', hs', hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p hA hB hca hcb hs'⟩

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
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hcells
  obtain ⟨⟨hQaMa, hQaQh, hQaC1, hQaC2, hQaC3⟩, ⟨hMaQh, hMaC1, hMaC2, hMaC3⟩, ⟨hQhC1, hQhC2, hQhC3⟩,
    ⟨hC1C2, hC1C3⟩, hC2C3, -⟩ := hbufs
  obtain ⟨⟨htQh, htC1, htC2, htC3⟩, hsQh, hsC1, hsC2, hsC3⟩ := hcells
  have hne := @blockDisjoint_of_ne
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hscr
  obtain ⟨⟨lQh, hQhs, hlQh⟩, ⟨l1, h1s, hl1⟩, ⟨l2, h2s, hl2⟩, ⟨l3, h3s, hl3⟩⟩ := hscr
  obtain ⟨lM, hMs, hlM⟩ := hcolen
  have hrn : r ≤ n := hr.trans hk
  have hrk : r * k ≤ n * n := Nat.mul_le_mul hrn hk
  have hrr : r * r ≤ n * n := Nat.mul_le_mul hrn hrn
  -- the conjugate transpose
  obtain ⟨s₁, h₁⟩ := compress_exists_zconjTranspose (I := I) hsem p k r (X := Qa) (Y := Qh)
    (xo := qo) (yo := 0) hQ (hne (Ne.symm hQaQh))
    ⟨lQh, hQhs, by simp only [IExp.eval_zero]; nlinarith⟩
  obtain ⟨hQh, hfr₁⟩ := holds_of_exec_zconjTranspose (I := I) (toNat := fun _ => 0) (mmR := mmR)
    (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : Unit) => x)
    (normal := fun (_ : Unit) => ((default : K), (default : K))) p k r hQ
    (hne (Ne.symm hQaQh)) h₁
  obtain ⟨hsh₁, -⟩ := shape_pos_of_exec_zconjTranspose p k r h₁
  -- the first product
  obtain ⟨c₁, hc₁, hC1, hfr₂⟩ := compress_exists_kcall (I := I) hmm p (l := r) (m := k) (n := k)
    (a := (Qh, 0)) (b := (Ma, mo.eval)) (c := (C1, 0)) hQh
    (hA.of_forall_read_eq fun i _ _ => hfr₁ p Ma i (hne hMaQh)) (hne (Ne.symm hQhC1))
    (hne (Ne.symm hMaC1)) (by rw [hsh₁]; exact h1s) (by nlinarith)
  have hsh₂ := (Interp.shape_of_kcallStore_eq_some hc₁).trans hsh₁
  -- the second product
  have hQ₂ : pairLayout.Holds c₁ p Qa qo.eval Q := hQ.of_forall_read_eq fun i _ _ =>
    (hfr₂ p Qa i (hne hQaC1)).trans (hfr₁ p Qa i (hne hQaQh))
  obtain ⟨c₂', hc₂, hC2, hfr₃⟩ := compress_exists_kcall (I := I) hmm p (l := r) (m := k)
    (n := r) (a := (C1, 0)) (b := (Qa, qo.eval)) (c := (C2, 0)) hC1 hQ₂ (hne (Ne.symm hC1C2))
    (hne (Ne.symm hQaC2)) (by rw [hsh₂]; exact h2s) (by nlinarith)
  have hsh₃ := (Interp.shape_of_kcallStore_eq_some hc₂).trans hsh₂
  have hkeep : ∀ c : Cell ℕ ℕ, c.buf ≠ Qh → c.buf ≠ C1 → c.buf ≠ C2 →
      c₂'.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval := fun c h1 h2 h3 =>
    (hfr₃ p _ _ (hne h3)).trans ((hfr₂ p _ _ (hne h2)).trans (hfr₁ p _ _ (hne h1)))
  -- the run
  change ∃ st', exec I (.seq (.named _ _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) (.seq (.named _ _ _) .skip))))) st = some st'
  change exec I (.seq (.named _ _ _) .skip) st = some s₁ at h₁
  rw [exec_seq_skip] at h₁
  rw [exec_seq, h₁, Option.bind_some, exec_seq]
  refine Option.exists_bind_eq_some_of_exists (fun σ => σ.store = c₁) ⟨_, by
    rw [exec_kcall]
    simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
    rw [hc₁]; rfl, rfl⟩ ?_
  rintro σ₂ hσ₂
  rw [exec_seq]
  refine Option.exists_bind_eq_some_of_exists (fun σ => σ.store = c₂') ⟨_, by
    rw [exec_kcall]
    simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
    rw [hσ₂, hc₂]; rfl, rfl⟩ ?_
  rintro σ₃ hσ₃
  -- the average
  have htwo₃ : σ₃.store.read p two.buf two.idx.eval = some c₂ := by
    rw [hσ₃, hkeep two htQh htC1 htC2]; exact htwo
  have hC2₃ : pairLayout.Holds σ₃.store p C2 (0 : IExp ℕ).eval
      (mmR (mmR ((I.sem.toFloatMachine p (fun _ => 0) mmR
        (@fun _ _ X => (Matrix.of fun _ _ => default, X)) (fun x (_ : Unit) => x)
        (fun (_ : Unit) => ((default : K), (default : K)))).conjTransposeMat Q) A) Q) := by
    rw [hσ₃]; exact hC2
  obtain ⟨s₄, h₄⟩ := exists_exec_zhermAvg (I := I) p r (st := σ₃) (Y := C3) (yo := 0) hsem htwo0
    hC2₃ htwo₃ (hne (Ne.symm hC2C3)) (hne htC3)
    ⟨l3, by rw [hσ₃, hsh₃]; exact h3s, by simp only [IExp.eval_zero]; nlinarith⟩
  obtain ⟨hC3, hfr₄, hsh₄, -⟩ := holds_of_exec_zhermAvg (I := I) (toNat := fun _ => 0)
    (mmR := mmR) (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X))
    (unif := fun x (_ : Unit) => x) (normal := fun (_ : Unit) => ((default : K), (default : K)))
    p r hC2₃ htwo₃ (hne (Ne.symm hC2C3)) (hne htC3) h₄
  change exec I (.seq (.named _ _ _) .skip) σ₃ = some s₄ at h₄
  rw [exec_seq_skip] at h₄
  rw [exec_seq, h₄, Option.bind_some, exec_seq_skip]
  -- the shift
  obtain ⟨s₅, h₅⟩ := compress_exists_zhermShift (I := I) hsem p r (st := s₄) (X := C3)
    (xo := 0) (Y := Ma) (yo := co) (c := sg) hC3
    ⟨σ, by rw [hfr₄ p _ _ (hne hsC3), hσ₃, hkeep sg hsQh hsC1 hsC2]; exact hσ⟩
    (hne hMaC3) ⟨lM, by rw [hsh₄, hσ₃, hsh₃]; exact hMs, hlM⟩
  change exec I (.seq (.named _ _ _) .skip) s₄ = some s₅ at h₅
  rw [exec_seq_skip] at h₅
  exact ⟨s₅, h₅⟩

end NLAlib
