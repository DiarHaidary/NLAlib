/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.KernelCall
public import NLAlib.Computation.RoutineFrames
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Computation.BLASCongr
public import NLAlib.Matrix.Computation.PairKernels
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownSlot
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels

/-!
# A slot of the upward level of the spectral bisection program

The blocks of one level of the upward pass of `NLAlib.eighProg` (`NLAlib.eighUpLevel`) at constant
sizes, as routine specifications in both modes: a node with one child adds back its shift
(`NLAlib.spec_eighUpShift`), a split multiplies the children's bases by the deflation bases
(`NLAlib.spec_eighUpSplit`), the node dispatches on its stored kind
(`NLAlib.spec_eighUpNodeStep`), and the slot reads its stored size (`NLAlib.spec_eighUpSlot`), as
the machine of the interpretation computes them.

## Main results

* `NLAlib.eighUpShift`, `NLAlib.eighUpSplit`, `NLAlib.eighUpNode`, `NLAlib.eighUpSlot`: the blocks
  of a level at constant sizes.
* `NLAlib.spec_eighUpShift`, `NLAlib.spec_eighUpSplit`: the branches of a node.
* `NLAlib.spec_eighUpNodeStep`: a node writes its output (`NLAlib.eighAux`).
* `NLAlib.spec_eighUpSlot`, `NLAlib.holds_of_exec_eighUpSlot`: what a slot computes
  (`NLAlib.EighArenas.UpSlotsDone`).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! ### The blocks of a level -/

omit [DecidableEq P] in
/-- The one-child branch of the node of size $k$ at slot $lo$ of depth $d$ in
`NLAlib.eighUpLevel` ($n$ slots per level): the child's output block (depth $d + 1$) copied into
the node's, the shift in the cell `tc` added to the child's eigenvalues. -/
def eighUpShift (p : P) (n d lo k : ℕ) (H : EighArenas) (tc : Cell ℕ ℕ) :
    Builder P ι ℕ ℕ Unit := do
  zcopy p (IExp.var k) (IExp.var k) H.Ua (eighBlockOff (IExp.const n) (IExp.const d + 1)
    (IExp.var lo)) H.Ua (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
  forRange (IExp.var k) fun i => ins (.bin p .add
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩ tc)

omit [DecidableEq P] in
/-- The eigenvalue loops of the split branch of the node of size $k$ at slot $lo$ of depth $d$
split at $k_+$ (shift in cell $0$ of buffer `t`): the shift added to the eigenvalues of the positive
child and subtracted from those of the negative one. -/
def eighUpSplitEigs (p : P) (n d lo k kp t : ℕ) (H : EighArenas) : Builder P ι ℕ ℕ Unit := do
  forRange (IExp.var kp) fun j => ins (.bin p .add
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩ ⟨t, 0⟩)
  forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp + IExp.var j⟩
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
      IExp.var j⟩ ⟨t, 0⟩)

omit [DecidableEq P] in
/-- The two products of the split branch of the node of size $k$ at slot $lo$ of depth $d$ split
at $k_+$, then `rest`: the products of the bases of depth $d$ and the children's outputs into the
two column blocks of the node's output. -/
def eighUpProducts (p : P) (mm : ι) (n d lo k kp : ℕ) (H : EighArenas)
    (rest : Builder P ι ℕ ℕ Unit) : Builder P ι ℕ ℕ Unit := do
  let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
  stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
    [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
    [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
  stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp, IExp.var k - IExp.var kp]
    [(H.Qa, qo + 2 * (IExp.var k * IExp.var kp)),
      (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo + IExp.var kp))]
    [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
      2 * (IExp.var k * IExp.var kp))])
  rest

omit [DecidableEq P] in
/-- The split branch of the node of size $k$ at slot $lo$ of depth $d$ in `NLAlib.eighUpLevel`,
split at $k_+$ ($n$ slots per level, shift in cell $0$ of buffer `t`): the products
(`NLAlib.eighUpProducts`), then the eigenvalues (`NLAlib.eighUpSplitEigs`). -/
def eighUpSplit (p : P) (mm : ι) (n d lo k kp t : ℕ) (H : EighArenas) :
    Builder P ι ℕ ℕ Unit :=
  eighUpProducts p mm n d lo k kp H (eighUpSplitEigs (ι := ι) p n d lo k kp t H)

omit [DecidableEq P] in
/-- The node of size $k$ at slot $lo$ of depth $d$ in `NLAlib.eighUpLevel` ($n$ slots per level,
shift $\sigma$ and $-\sigma$ in cells $0$ and $1$ of buffer `t`): the kind binder and its three
branches (`NLAlib.eighUpShift` for kinds $2$ and $3$, `NLAlib.eighUpSplit` for kind $4$). -/
def eighUpNode (p : P) (mm : ι) (n d lo k t : ℕ) (H : EighArenas) : Builder P ι ℕ ℕ Unit :=
  Builder.bindIdx p ⟨H.Kd, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩ 4 fun c => do
    eighWhen (eighEqInd (IExp.var c) 2) (eighUpShift p n d lo k H ⟨t, 0⟩)
    eighWhen (eighEqInd (IExp.var c) 3) (eighUpShift p n d lo k H ⟨t, 1⟩)
    eighWhen (eighEqInd (IExp.var c) 4) <|
      Builder.bindIdx p ⟨H.Kp, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
        (IExp.var k) fun kp => eighUpSplit p mm n d lo k kp t H

omit [DecidableEq P] in
/-- The slot $lo$ of depth $d$ in `NLAlib.eighUpLevel` ($n$ slots per level, shift cells in
buffer `t`): the size binder, and the node (`NLAlib.eighUpNode`) if the size is positive. -/
def eighUpSlot (p : P) (mm : ι) (n d lo t : ℕ) (H : EighArenas) : Builder P ι ℕ ℕ Unit :=
  Builder.bindIdx p ⟨H.Sz, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
    (IExp.const n - IExp.var lo) fun k => eighWhen (IExp.var k) (eighUpNode p mm n d lo k t H)


/-! ### Steps, loops and handles -/

/-- A one-child step adds back the shift $\pm\mathrm{fl}(R/2)$. -/
private theorem eq_of_eighStep_eq_shift {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N fuel k ℓ : ℕ} {R₀ β R ε : F} {A : Matrix (Fin k) (Fin k) (F × F)}
    {s : EighSample Su Sg N} {b : Bool} {A' : Matrix (Fin k) (Fin k) (F × F)} {σ : F}
    (h : eighStep M N fuel R₀ β A R ε ℓ s = .shift b A' σ) :
    σ = if b then M.div R (M.ofNat 2) else M.neg (M.div R (M.ofNat 2)) := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h <;> cases h <;> rfl

/-- A split by `NLAlib.eighStep` (of a node of size $k$ with window $R$, on the sample `s`) at
$k_+$ adds back the shift $\mathrm{fl}(R/2)$ and has $0 < k_+ < k$. -/
theorem eq_div_and_pos_and_lt_of_eighStep_eq_split {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N fuel k ℓ : ℕ} {R₀ β R ε : F} {A : Matrix (Fin k) (Fin k) (F × F)}
    {s : EighSample Su Sg N} {kp : ℕ} {hkp : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (h : eighStep M N fuel R₀ β A R ε ℓ s = .split kp hkp Qp Qm Ap Am σ) :
    σ = M.div R (M.ofNat 2) ∧ 0 < kp ∧ kp < k := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4
  cases h
  exact ⟨rfl, Nat.pos_of_ne_zero h4, lt_of_le_of_ne (min_le_left _ _) h3⟩

omit [Inhabited K] in
/-- The column map of an assembled split: a column below $k_+$ is on the positive side. -/
private theorem finSumFinEquiv_symm_apply_lt {k kp : ℕ} (h : kp ≤ k) (j : Fin k)
    (hj : (j : ℕ) < kp) :
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j = Sum.inl ⟨j, hj⟩ := by
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  ext; simp

omit [Inhabited K] in
/-- The column map of an assembled split: a column from $k_+$ is on the negative side. -/
private theorem finSumFinEquiv_symm_apply_ge {k kp : ℕ} (h : kp ≤ k) (j : Fin k)
    (hj : kp ≤ (j : ℕ)) :
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j =
      Sum.inr ⟨j - kp, by omega⟩ := by
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  ext; simp; omega

omit [AddMonoid C] [Inhabited K] in
/-- Two column blocks stored one after the other hold the matrix of their columns. -/
private theorem holds_fromCols {s : Store P K} {p : P} {b off k kp : ℕ} (h : kp ≤ k)
    {X : Matrix (Fin k) (Fin kp) (K × K)} {Y : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    (hX : pairLayout.Holds s p b off X) (hY : pairLayout.Holds s p b (off + 2 * (k * kp)) Y) :
    pairLayout.Holds s p b off ((Matrix.fromCols X Y).submatrix id
      ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm)) := by
  intro i j t
  by_cases hj : (j : ℕ) < kp
  · simp only [Matrix.submatrix_apply, id, finSumFinEquiv_symm_apply_lt h j hj,
      Matrix.fromCols_apply_inl]
    exact hX i ⟨j, hj⟩ t
  · simp only [Matrix.submatrix_apply, id, finSumFinEquiv_symm_apply_ge h j (by omega),
      Matrix.fromCols_apply_inr]
    rw [← hY i ⟨j - kp, by omega⟩ t]
    congr 1
    simp only [pairLayout]
    have : (j : ℕ) = kp + (j - kp) := by omega
    conv_lhs => rw [this]
    ring

omit [Inhabited K] in
/-- A loop of no trips, then `t`, runs as `t`. -/
theorem exec_seq_loop_of_eval_eq_zero {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} (he : e.eval = 0) : exec I (.seq (.loop e b) t) s = exec I t s := by
  rw [exec_seq, exec_loop, he]
  simp

omit [AddMonoid C] [Inhabited K] in
/-- The distinct handles of the arenas that the upward pass touches, if the eight handles of `H`
are distinct. -/
theorem EighArenas.ua_ne_ea_and_of_nodup {H : EighArenas} (hnd : H.handles.Nodup) :
    H.Ua ≠ H.Ea ∧ H.Ua ≠ H.Qa ∧ H.Kd ≠ H.Ua ∧ H.Kd ≠ H.Ea ∧ H.Kp ≠ H.Ua ∧ H.Kp ≠ H.Ea ∧
      H.Qa ≠ H.Ea ∧ H.Sz ≠ H.Ua ∧ H.Sz ≠ H.Ea ∧ H.Ma ≠ H.Ua ∧ H.Ma ≠ H.Ea ∧ H.Lv ≠ H.Ua ∧
      H.Lv ≠ H.Ea := by
  simp only [EighArenas.handles] at hnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> simp [e] at hnd

omit [AddMonoid C] [Inhabited K] in
/-- A cell of the output arena of `H` (distinct handles) at level $d$ lies in the block of depth
$d$. -/
theorem EighArenas.mul_le_and_lt_of_levelCell_ua {H : EighArenas} {n d i : ℕ}
    (hnd : H.handles.Nodup) (h : H.LevelCell n d H.Ua i) :
    2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1) := by
  obtain ⟨h1, -, h3, -, h5, -, -, h8, -, -, -, h12, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  rcases h with ⟨-, h⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
  · exact h
  · rcases hb with hb | hb | hb | hb
    exacts [absurd hb h1, absurd hb.symm h8, absurd hb.symm h3, absurd hb.symm h5]
  · exact absurd hb.symm h12

omit [AddMonoid C] [Inhabited K] in
/-- A cell of the eigenvalue arena of `H` (distinct handles) at level $d$ lies in the cells of
depth $d$. -/
theorem EighArenas.mul_le_and_lt_of_levelCell_ea {H : EighArenas} {n d i : ℕ}
    (hnd : H.handles.Nodup) (h : H.LevelCell n d H.Ea i) : n * d ≤ i ∧ i < n * (d + 1) := by
  obtain ⟨h1, -, -, -, -, -, h7, -, -, -, h11, -, h13⟩ := H.ua_ne_ea_and_of_nodup hnd
  rcases h with ⟨hb, -⟩ | ⟨-, h⟩ | ⟨hb, -⟩
  · rcases hb with hb | hb | hb
    exacts [absurd hb.symm h11, absurd hb.symm h1, absurd hb.symm h7]
  · exact h
  · exact absurd hb.symm h13

omit [Inhabited K] in
/-- Two nodes at paths of the same length $d$ below the root of size $n \ge 1$, the first at a
slot $lo'$ below the second's $lo$: the first ends before the second starts, and so does its output
block. -/
theorem add_le_and_mul_add_le_of_eighLoc_of_lt {M : FloatMachine K ℕ ℕ} {n F d ℓ₀ : ℕ}
    {R₀ β ε : K} {A : Matrix (Fin n) (Fin n) (K × K)} {a a' : List Bool} {lo lo' : ℕ}
    {y y' : EighNode K} (hn : 1 ≤ n) (ha : a.length = d) (ha' : a'.length = d)
    (hay : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (hay' : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo', y')) (hlt : lo' < lo) :
    lo' + y'.k ≤ lo ∧ 2 * n * lo' + 2 * (y'.k * y'.k) ≤ 2 * n * lo := by
  have hb' := eighLoc_bounds hn hay'
  have hne : a' ≠ a := by
    rintro rfl
    rw [hay] at hay'
    cases hay'
    omega
  have := eighLoc_disjoint (ha'.trans ha.symm) hne hay' hay
  have h1 : lo' + y'.k ≤ lo := by omega
  exact ⟨h1, by nlinarith [Nat.mul_le_mul_right y'.k (show y'.k ≤ n by omega)]⟩

/-- A cell outside level $d$ of the output and eigenvalue arenas lies outside the blocks of the
node of size $k$ at slot $lo$, $lo + k \le n$. -/
private theorem not_mem_blocks_of_not_levelCell {H : EighArenas} {n d lo k b i : ℕ}
    (hk : lo + k ≤ n) (hb' : ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i)) :
    (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
        2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) ∧
      (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) := by
  have hlt : 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) := by
    nlinarith [Nat.mul_le_mul_left n hk]
  refine ⟨?_, ?_⟩
  · by_cases hbU : b = H.Ua
    · subst hbU
      refine Or.inr (by_contra fun hc =>
        hb' ⟨Or.inl rfl, Or.inl ⟨Or.inr (Or.inl rfl), by omega, ?_⟩⟩)
      rw [Nat.mul_succ]
      omega
    · exact Or.inl hbU
  · by_cases hbE : b = H.Ea
    · subst hbE
      refine Or.inr (by_contra fun hc =>
        hb' ⟨Or.inr rfl, Or.inr (Or.inl ⟨Or.inl rfl, by omega, ?_⟩)⟩)
      rw [Nat.mul_succ]
      omega
    · exact Or.inl hbE


/-! ### Guarded blocks -/

section Whens
variable {md : Mode}

omit [Inhabited K] in
/-- A guarded block whose index is $0$ is skipped: the rest of the builder meets its own
specification. No printed source. -/
theorem routineSpec_eighWhen_zero_bind {pre : St P K C → Prop} {e : IExp ℕ}
    {b f : Builder P ι ℕ ℕ Unit} {fp : List (ℕ × ℕ × ℕ)} {post : St P K C → St P K C → Prop}
    (he : e.eval = 0) (h : RoutineSpec md I pre f fp post) :
    RoutineSpec md I pre (eighWhen e b >>= fun _ => f) fp post :=
  h.congr (ExecutionComposable.bind (executionComposable_forRange _ _) h.composable)
    fun st => by
      change exec I (.seq (.loop (1 - (1 - e)) fun _ => b.run) f.run) st = _
      exact exec_seq_loop_of_eval_eq_zero (by simp [he])

omit [Inhabited K] in
/-- A guarded block whose index is $0$ leaves the state unchanged, in every mode. No printed
source. -/
theorem routineSpec_eighWhen_of_eval_eq_zero {pre : St P K C → Prop} {e : IExp ℕ}
    {b : Builder P ι ℕ ℕ Unit} (he : e.eval = 0) :
    RoutineSpec md I pre (eighWhen e b) [] fun st st' => st' = st :=
  (spec_eighWhen (body := b) (pre := pre) (fp := []) (post := fun _ _ => True)
    fun h => absurd h (by omega)).conseq (fun _ h => h) (fun _ h => h) fun _ _ _ h => h.1 he

omit [Inhabited K] in
/-- Two guarded blocks whose indices are $0$ leave the state unchanged, in every mode. No printed
source. -/
theorem routineSpec_eighWhen_bind_eighWhen_of_eval_eq_zero {pre : St P K C → Prop} {e e' : IExp ℕ}
    {b b' : Builder P ι ℕ ℕ Unit} (he : e.eval = 0) (he' : e'.eval = 0) :
    RoutineSpec md I pre (eighWhen e b >>= fun _ => eighWhen e' b') [] fun st st' => st' = st :=
  routineSpec_eighWhen_zero_bind he (routineSpec_eighWhen_of_eval_eq_zero he')


end Whens



/-! ### The branches of a node -/

/-- The one-child branch of a node of the upward pass as a routine specification
(`NLAlib.eighUpShift`, node of size $k$ at slot $lo$, $lo + k \le n$): from the child's output
$\mathbf{U}$ and eigenvalues $e$ at depth $d + 1$ and the shift $\sigma$ in the cell `tc`, the
node's block at depth $d$ holds $\mathbf{U}$ and its eigenvalue cells hold $e_i + \sigma$; only
the node's blocks are modified and the tape positions are kept; in mode `total` it also succeeds,
given the blocks writable and the standard model. No printed source. -/
theorem spec_eighUpShift (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n d lo k : ℕ)
    (H : EighArenas) (tc : Cell ℕ ℕ) (hk : lo + k ≤ n) (hUE : H.Ua ≠ H.Ea)
    (htc : tc.buf ≠ H.Ea) (htcU : tc.buf ≠ H.Ua) (U : Matrix (Fin k) (Fin k) (K × K))
    (e : Fin k → K) (σ : K) :
    RoutineSpec md I (fun st =>
        pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U ∧
        (∀ i : Fin k, st.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i)) ∧
        st.store.read p tc.buf tc.idx.eval = some σ ∧
        md.Needs (Writable st.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ∧
          Writable st.store p H.Ea (n * d + lo) k))
      (eighUpShift (ι := ι) p n d lo k H tc)
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), (H.Ea, n * d + lo, k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
        (∀ i : Fin k, st'.store.read p H.Ea (n * d + lo + i) =
          some ((I.sem.bin p .add (e i) σ).getD default)) ∧ PosKept st st' := by
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have hlk : 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) (show lo + k ≤ n by omega)
    nlinarith
  have e1 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have hz := spec_zcopy (I := I) md p k k (X := H.Ua) (Y := H.Ua)
    (xo := eighBlockOff (.const n) (.const d + 1) (.var lo))
    (yo := eighBlockOff (.const n) (.const d) (.var lo)) U
    (blockDisjoint_of_ne_or_le (Or.inr (Or.inl (by
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
        IExp.eval_ofNat]
      omega))))
  have hz' := hz.congr (r' := zcopy (ι := ι) p (.var k) (.var k) H.Ua
    (eighBlockOff (.const n) (.const d + 1) (.var lo)) H.Ua
    (eighBlockOff (.const n) (.const d) (.var lo))) (by exec_composable)
    fun st => exec_eq_of_normIdx_eq I (by unfold zcopy; rfl) st
  have hE1 : ∀ i, (eighSlotOff (.const n) (.const d + 1) (.var lo) + IExp.var i : IExp ℕ).eval =
      n * (d + 1) + lo + i := fun i => by simp [eighSlotOff]
  have hE0 : ∀ i, (eighSlotOff (.const n) (.const d) (.var lo) + IExp.var i : IExp ℕ).eval =
      n * d + lo + i := fun i => by simp [eighSlotOff]
  have hl := spec_forRange_bin (I := I) (m := md) (p := p) (op := .add) (n := (.var k : IExp ℕ))
    (Y := H.Ea) (off := n * d + lo) (X := H.Ea) (c := tc)
    (didx := fun i => eighSlotOff (.const n) (.const d) (.var lo) + .var i)
    (sidx := fun i => eighSlotOff (.const n) (.const d + 1) (.var lo) + .var i)
    (fun i => if h : i < k then e ⟨i, h⟩ else default) σ hE0
    (fun i hi => blockDisjoint_of_ne_or_le (Or.inr (Or.inr (by
      rw [hE1]; simp only [IExp.eval_var] at hi ⊢; rw [Nat.mul_succ]; omega))))
    (blockDisjoint_of_ne_or_le (Or.inl htc))
  refine (RoutineSpec.bind (hz'.conseq (pre' := fun st =>
    pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U ∧
    (∀ i : Fin k, st.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i)) ∧
    st.store.read p tc.buf tc.idx.eval = some σ ∧
    md.Needs (Writable st.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ∧
      Writable st.store p H.Ea (n * d + lo) k))
    (fun st h => ⟨by simpa [eighBlockOff] using h.1, h.2.2.2.mono (·.1)⟩) (fun x hx => hx)
    (fun _ _ _ h => h))
    (⟨hl.composable, hl.spec.with_modifies⟩ : RoutineSpec md I _ _ _ _) ?_).conseq
    (fun st h => h) ?_ ?_
  · rintro st st₁ ⟨hU, hE, hσ, hN⟩ hm -
    refine ⟨fun i hi => ?_, (readsOnly_read _ _ _ _).of_modifies hσ hm
      (by fp_omega [htcU]), (Mode.needs_and.mpr ⟨hsem, hN⟩).mono
      fun ⟨hs, _, hW⟩ => ⟨fun i _ => hs.bin_ok p .add _ _ trivial (fun h => nomatch h) trivial,
        hW.of_modifies hm⟩⟩
    have hi' : i < k := hi
    rw [hE1, hm.2 p H.Ea _ (by fp_omega [hUE])]
    simp [hi', hE ⟨i, hi'⟩]
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl <;> simp [eighBlockOff]
  · rintro st st' ⟨hU, hE, hσ, hN⟩ ⟨st₁, ⟨hU₁, hp₁⟩, hm₂, hE₂, hp₂⟩
    refine ⟨?_, fun i => ?_, hp₂.trans hp₁⟩
    · simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
        IExp.eval_ofNat] at hU₁
      exact (readsOnly_pairLayoutHolds p H.Ua _ U).of_modifies hU₁ hm₂ (by fp_omega [hUE])
    · have := hE₂ i i.2
      simpa [i.2] using this

/-- The eigenvalue loops of a split as a routine specification (`NLAlib.eighUpSplitEigs`): the shift
$\sigma$ in cell $0$ of `t` is added to the eigenvalues $e_+$ of the positive child and subtracted
from those of the negative child, written into the node's cells; only they are modified. No printed
source. -/
theorem spec_eighUpSplitEigs (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n d lo k kp t : ℕ)
    (H : EighArenas) (hk : lo + k ≤ n) (hkp : kp < k) (htE : t ≠ H.Ea) (ep : Fin kp → K)
    (em : Fin (k - kp) → K) (σ : K) :
    RoutineSpec md I (fun st =>
        (∀ j : Fin kp, st.store.read p H.Ea (n * (d + 1) + lo + j) = some (ep j)) ∧
        (∀ j : Fin (k - kp), st.store.read p H.Ea (n * (d + 1) + (lo + kp) + j) =
          some (em j)) ∧ st.store.read p t 0 = some σ ∧
        md.Needs (Writable st.store p H.Ea (n * d + lo) k))
      (eighUpSplitEigs (ι := ι) p n d lo k kp t H) [(H.Ea, n * d + lo, k)]
      fun st st' => (∀ j : Fin kp, st'.store.read p H.Ea (n * d + lo + j) =
          some ((I.sem.bin p .add (ep j) σ).getD default)) ∧
        (∀ j : Fin (k - kp), st'.store.read p H.Ea (n * d + lo + kp + j) =
          some ((I.sem.bin p .sub (em j) σ).getD default)) ∧ PosKept st st' := by
  have hnlo : n * (d + 1) = n * d + n := by ring
  have hE0 : ∀ i, (eighSlotOff (.const n) (.const d) (.var lo) + IExp.var i : IExp ℕ).eval =
      n * d + lo + i := fun i => by simp [eighSlotOff]
  have hE1 : ∀ i, (eighSlotOff (.const n) (.const d + 1) (.var lo) + IExp.var i : IExp ℕ).eval =
      n * (d + 1) + lo + i := fun i => by simp [eighSlotOff]
  have hE0' : ∀ i, (eighSlotOff (.const n) (.const d) (.var lo) + IExp.var kp + IExp.var i :
      IExp ℕ).eval = n * d + lo + kp + i := fun i => by simp [eighSlotOff]
  have hE1' : ∀ i, (eighSlotOff (.const n) (.const d + 1) (.var lo) + IExp.var kp + IExp.var i :
      IExp ℕ).eval = n * (d + 1) + lo + kp + i := fun i => by simp [eighSlotOff]
  have s3 := spec_forRange_bin (I := I) (m := md) (p := p) (op := .add)
    (n := (.var kp : IExp ℕ)) (Y := H.Ea) (off := n * d + lo) (X := H.Ea) (c := ⟨t, 0⟩)
    (didx := fun i => eighSlotOff (.const n) (.const d) (.var lo) + .var i)
    (sidx := fun i => eighSlotOff (.const n) (.const d + 1) (.var lo) + .var i)
    (fun i => if h : i < kp then ep ⟨i, h⟩ else default) σ hE0
    (fun i hi => blockDisjoint_of_ne_or_le (Or.inr (Or.inr (by
      rw [hE1]; simp only [IExp.eval_var] at hi ⊢; rw [hnlo]; omega))))
    (blockDisjoint_of_ne_or_le (Or.inl htE))
  have s4 := spec_forRange_bin (I := I) (m := md) (p := p) (op := .sub)
    (n := (.var k - .var kp : IExp ℕ)) (Y := H.Ea) (off := n * d + lo + kp) (X := H.Ea)
    (c := ⟨t, 0⟩)
    (didx := fun i => eighSlotOff (.const n) (.const d) (.var lo) + .var kp + .var i)
    (sidx := fun i => eighSlotOff (.const n) (.const d + 1) (.var lo) + .var kp + .var i)
    (fun i => if h : i < k - kp then em ⟨i, h⟩ else default) σ hE0'
    (fun i hi => blockDisjoint_of_ne_or_le (Or.inr (Or.inr (by
      rw [hE1']; simp only [IExp.eval_var, IExp.eval_sub] at hi ⊢; rw [hnlo]; omega))))
    (blockDisjoint_of_ne_or_le (Or.inl htE))
  refine ⟨ExecutionComposable.bind s3.composable s4.composable, fun st ⟨hEp, hEm, hσ, hN⟩ => ?_⟩
  have hN3 := (Mode.needs_and.mpr ⟨hsem, hN⟩).mono fun ⟨hs, hW⟩ =>
    (⟨fun i _ => hs.bin_ok p .add _ _ trivial (fun h => nomatch h) trivial,
      hW.of_le le_rfl (by omega : n * d + lo + kp ≤ n * d + lo + k)⟩ :
      (∀ i < kp, ∃ v, I.sem.bin p .add (if h : i < kp then ep ⟨i, h⟩ else default) σ = some v) ∧
        Writable st.store p H.Ea (n * d + lo) kp)
  refine s3.wp_bind ⟨fun i hi => ?_, hσ, hN3⟩ fun st₃ hm₃ h₃ => ?_
  · have hi' : i < kp := hi
    rw [hE1]
    simpa [hi'] using hEp ⟨i, hi'⟩
  have hN4 := (Mode.needs_and.mpr ⟨hsem, hN⟩).mono fun ⟨hs, hW⟩ =>
    (⟨fun i _ => hs.bin_ok p .sub _ _ trivial (fun h => nomatch h) trivial,
      (hW.of_modifies hm₃).of_le (by omega) (by omega : n * d + lo + kp + (k - kp) ≤
        n * d + lo + k)⟩ :
      (∀ i < k - kp, ∃ v, I.sem.bin p .sub (if h : i < k - kp then em ⟨i, h⟩ else default) σ =
        some v) ∧ Writable st₃.store p H.Ea (n * d + lo + kp) (k - kp))
  refine s4.wp_run ⟨fun i hi => ?_, ?_, hN4⟩ fun st₄ hm₄ h₄ => ?_
  · have hi' : i < k - kp := hi
    rw [hE1', show n * (d + 1) + lo + kp + i = n * (d + 1) + (lo + kp) + i by omega,
      hm₃.2 p H.Ea _ (by simp only [IExp.eval_var]; fp_omega [hnlo])]
    simp [hi', hEm ⟨i, hi'⟩]
  · change st₃.store.read p t 0 = some σ
    rw [hm₃.2 p t 0 (by simp only [IExp.eval_var]; fp_omega [htE])]
    exact hσ
  refine ⟨(hm₃.trans hm₄).of_sub fun x hx => ?_, fun j => ?_, fun j => ?_,
    h₄.2.trans h₃.2⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, IExp.eval_var,
      IExp.eval_sub] at hx
    rcases hx with rfl | rfl
    · exact ⟨(H.Ea, n * d + lo, k), by simp, rfl, le_rfl, by dsimp only; omega⟩
    · exact ⟨(H.Ea, n * d + lo, k), by simp, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · have := h₃.1 j j.2
    rw [hm₄.2 p H.Ea _ (by simp only [IExp.eval_var, IExp.eval_sub]; fp_omega [])]
    simpa [j.2] using this
  · have := h₄.1 j j.2
    simpa [j.2] using this

omit [Inhabited K] in
/-- The products of a split compose with a composable rest. No printed source. -/
theorem executionComposable_eighUpProducts {p : P} {mm : ι} {n d lo k kp : ℕ} {H : EighArenas}
    {rest : Builder P ι ℕ ℕ Unit} (h : ExecutionComposable I rest) :
    ExecutionComposable I (eighUpProducts p mm n d lo k kp H rest) :=
  ExecutionComposable.bind (executionComposable_stmt _)
    (ExecutionComposable.bind (executionComposable_stmt _) h)

/-- The two products of a split in the weakest-precondition form (`NLAlib.eighUpProducts`): from
the stored bases $\mathbf{Q}_\pm$ at depth $d$ and the children's outputs $\mathbf{U}_\pm$ at depth
$d + 1$, the node's output block at depth $d$ holds the two products in its column blocks, and only
it is modified, before the rest. No printed source. -/
theorem wp_eighUpProducts {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    (p : P) (n d lo k kp : ℕ) (H : EighArenas) (hk : lo + k ≤ n) (hkp : kp < k)
    (hUQ : H.Ua ≠ H.Qa) (Qp : Matrix (Fin k) (Fin kp) (K × K))
    (Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)) (Up : Matrix (Fin kp) (Fin kp) (K × K))
    (Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)) {st : St P K C}
    (rest : Builder P ι ℕ ℕ Unit) {Q : St P K C → Prop}
    (hQp : pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (hUp : pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up)
    (hUm : pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um)
    (hN : md.Needs (Writable st.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k))))
    (hrest : ∀ st₂ : St P K C,
      Modifies [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k))] st.store st₂.store →
      pairLayout.Holds st₂.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (mmR Qp Up) →
      pairLayout.Holds st₂.store p H.Ua (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))
        (mmR Qm Um) → PosKept st st₂ → Wp md I rest.run Q st₂) :
    Wp md I (eighUpProducts p mm n d lo k kp H rest).run Q st := by
  have hkk : k * kp ≤ k * k := Nat.mul_le_mul_left k hkp.le
  have hsplit : k * kp + k * (k - kp) = k * k := by rw [← Nat.mul_add, Nat.add_sub_of_le hkp.le]
  have hnk : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have hlk : 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) (show lo + k ≤ n by omega)
    nlinarith
  have e1 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have hnlo : n * (d + 1) = n * d + n := by ring
  have K1 := hmm.spec_kcall pairLayout.get_put md p
    (H.Qa, eighBlockOff (.const n) (.const d) (.var lo))
    (H.Ua, eighBlockOff (.const n) (.const d + 1) (.var lo))
    (H.Ua, eighBlockOff (.const n) (.const d) (.var lo)) Qp Up
  have K1' := (RoutineSpec.stmt K1).congr (r' := Builder.stmt (.kcall mm p
    [IExp.var k, IExp.var kp, IExp.var kp]
    [(H.Qa, eighBlockOff (.const n) (.const d) (.var lo)),
      (H.Ua, eighBlockOff (.const n) (.const d + 1) (.var lo))]
    [(H.Ua, eighBlockOff (.const n) (.const d) (.var lo))])) (by exec_composable)
    fun st => exec_eq_of_normIdx_eq I (by rfl) st
  have K2 := hmm.spec_kcall pairLayout.get_put md p
    (H.Qa, eighBlockOff (.const n) (.const d) (.var lo) + 2 * (IExp.var k * IExp.var kp))
    (H.Ua, eighBlockOff (.const n) (.const d + 1) (.var lo + .var kp))
    (H.Ua, eighBlockOff (.const n) (.const d) (.var lo) + 2 * (IExp.var k * IExp.var kp)) Qm Um
  have K2' := (RoutineSpec.stmt K2).congr (r' := Builder.stmt (.kcall mm p
    [IExp.var k, IExp.var k - IExp.var kp, IExp.var k - IExp.var kp]
    [(H.Qa, eighBlockOff (.const n) (.const d) (.var lo) + 2 * (IExp.var k * IExp.var kp)),
      (H.Ua, eighBlockOff (.const n) (.const d + 1) (.var lo + .var kp))]
    [(H.Ua, eighBlockOff (.const n) (.const d) (.var lo) + 2 * (IExp.var k * IExp.var kp))]))
    (by exec_composable) fun st => exec_eq_of_normIdx_eq I (by rfl) st
  have hq : (eighBlockOff (.const n) (.const d) (.var lo) : IExp ℕ).eval =
      2 * (n * n) * d + 2 * n * lo := by simp [eighBlockOff]
  have hu : (eighBlockOff (.const n) (.const d + 1) (.var lo) : IExp ℕ).eval =
      2 * (n * n) * (d + 1) + 2 * n * lo := by simp [eighBlockOff]
  have hq2 : (eighBlockOff (.const n) (.const d) (.var lo) + 2 * (IExp.var k * IExp.var kp) :
      IExp ℕ).eval = 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) := by simp [eighBlockOff]
  have hu2 : (eighBlockOff (.const n) (.const d + 1) (.var lo + .var kp) : IExp ℕ).eval =
      2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by simp [eighBlockOff]
  unfold eighUpProducts
  refine K1'.wp_bind ⟨by rw [hq]; exact hQp, by rw [hu]; exact hUp, ?_, ?_,
    hN.mono fun h => ?_⟩ fun st₁ hm₁ h₁ => ?_
  · simp only [matBlock, hq, pairLayout]
    fp_omega [hUQ]
  · simp only [matBlock, hq, hu, pairLayout]
    fp_omega [e1, hlk, hkk]
  · simp only [hq, pairLayout]
    exact h.of_le le_rfl (by omega)
  refine K2'.wp_bind ⟨?_, ?_, ?_, ?_, hN.mono fun h => ?_⟩ fun st₂ hm₂ h₂ => ?_
  · rw [hq2]
    exact (readsOnly_pairLayoutHolds p H.Qa _ Qm).of_modifies hQm hm₁ (by
      simp only [pairLayout]; fp_omega [hUQ])
  · rw [hu2]
    exact (readsOnly_pairLayoutHolds p H.Ua _ Um).of_modifies hUm hm₁ (by
      simp only [hq, pairLayout]; fp_omega [e1, hlk, hkk])
  · simp only [matBlock, hq2, pairLayout]
    fp_omega [hUQ]
  · simp only [matBlock, hq2, hu2, pairLayout]
    fp_omega [e1, hlk, hkk, hsplit]
  · simp only [hq, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_ofNat, pairLayout]
    exact (h.of_modifies hm₁).of_le (by omega) (by omega)
  have hX₂ : pairLayout.Holds st₂.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (mmR Qp Up) :=
    (readsOnly_pairLayoutHolds p H.Ua _ _).of_modifies (by rw [hq] at h₁; exact h₁.1) hm₂
      (by simp only [matBlock, pairLayout, hq2]; fp_omega [hkk])
  refine hrest st₂ ((hm₁.trans hm₂).of_sub fun x hx => ?_) hX₂ (by rw [hq2] at h₂; exact h₂.1)
    (h₂.2.2.trans h₁.2.2)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, matBlock, pairLayout,
    hq, hq2] at hx
  rcases hx with rfl | rfl
  · exact ⟨(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), by simp, rfl, le_rfl,
      by dsimp only; omega⟩
  · exact ⟨(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), by simp, rfl, by dsimp only; omega,
      by dsimp only; omega⟩

/-- The split branch of a node of the upward pass as a routine specification
(`NLAlib.eighUpSplit`, node of size $k$ at slot $lo$ split at $0 < k_+ < k$): its block at depth
$d$ holds the assembled products $[\mathbf{Q}_+\mathbf{U}_+\ \mathbf{Q}_-\mathbf{U}_-]$ and its
eigenvalue cells hold $e_+ + \sigma$ then $e_- - \sigma$; only the node's blocks are modified and
the tape positions are kept; in mode `total` it also succeeds, given the standard model and the
blocks writable. No printed source. -/
theorem spec_eighUpSplit {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n d lo k kp t : ℕ)
    (H : EighArenas) (hk : lo + k ≤ n) (hkp : kp < k)
    (hsum : k = kp + (k - kp)) (hUE : H.Ua ≠ H.Ea) (hUQ : H.Ua ≠ H.Qa)
    (htU : t ≠ H.Ua) (htE : t ≠ H.Ea) (Qp : Matrix (Fin k) (Fin kp) (K × K))
    (Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)) (Up : Matrix (Fin kp) (Fin kp) (K × K))
    (Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)) (ep : Fin kp → K)
    (em : Fin (k - kp) → K) (σ : K) :
    RoutineSpec md I (fun st =>
        pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
        pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
        pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up ∧
        pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um ∧
        (∀ j : Fin kp, st.store.read p H.Ea (n * (d + 1) + lo + j) = some (ep j)) ∧
        (∀ j : Fin (k - kp), st.store.read p H.Ea (n * (d + 1) + (lo + kp) + j) =
          some (em j)) ∧ st.store.read p t 0 = some σ ∧
        md.Needs (Writable st.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ∧
          Writable st.store p H.Ea (n * d + lo) k))
      (eighUpSplit (ι := ι) p mm n d lo k kp t H)
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), (H.Ea, n * d + lo, k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          ((Matrix.fromCols (mmR Qp Up) (mmR Qm Um)).submatrix id
            ((finCongr hsum).trans finSumFinEquiv.symm)) ∧
        (∀ j : Fin kp, st'.store.read p H.Ea (n * d + lo + j) =
          some ((I.sem.bin p .add (ep j) σ).getD default)) ∧
        (∀ j : Fin (k - kp), st'.store.read p H.Ea (n * d + lo + kp + j) =
          some ((I.sem.bin p .sub (em j) σ).getD default)) ∧ PosKept st st' := by
  have hEigs := spec_eighUpSplitEigs md hsem p n d lo k kp t H hk hkp htE ep em σ
  refine ⟨executionComposable_eighUpProducts hEigs.composable,
    fun st ⟨hQp, hQm, hUp, hUm, hEp, hEm, hσ, hN⟩ => ?_⟩
  refine wp_eighUpProducts hmm md p n d lo k kp H hk hkp hUQ Qp Qm Up Um _ hQp hQm hUp hUm
    (hN.mono (·.1)) fun st₂ hm₂ hX hY hp₂ => ?_
  refine hEigs.wp_run ⟨fun j => ?_, fun j => ?_, ?_, hN.mono fun h => h.2.of_modifies hm₂⟩
    fun st₃ hm₃ h₃ => ?_
  · rw [hm₂.2 p H.Ea _ (by fp_omega [hUE])]
    exact hEp j
  · rw [hm₂.2 p H.Ea _ (by fp_omega [hUE])]
    exact hEm j
  · rw [hm₂.2 p t 0 (by fp_omega [htU])]
    exact hσ
  refine ⟨(hm₂.trans hm₃).of_sub fun x hx => ?_,
    holds_fromCols hkp.le ((readsOnly_pairLayoutHolds p H.Ua _ _).of_modifies hX hm₃
      (by simp only [matBlock]; fp_omega [hUE]))
      ((readsOnly_pairLayoutHolds p H.Ua _ _).of_modifies hY hm₃
        (by simp only [matBlock]; fp_omega [hUE])), h₃.1, h₃.2.1, h₃.2.2.trans hp₂⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨_, by simp, rfl, le_rfl, le_rfl⟩
  · exact ⟨_, by simp, rfl, le_rfl, le_rfl⟩

/-! ### The node -/

/-- A node of kind $4$ (stored in its kind cell) with $k_+$ in its split cell runs as its split
branch (`NLAlib.spec_eighUpSplit`). No printed source. -/
theorem spec_eighUpNode_four {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n d lo k kp t : ℕ)
    (H : EighArenas) (hk : lo + k ≤ n) (hkp : kp < k)
    (hsum : k = kp + (k - kp)) (hUE : H.Ua ≠ H.Ea) (hUQ : H.Ua ≠ H.Qa)
    (htU : t ≠ H.Ua) (htE : t ≠ H.Ea) (v w : K) (hv : I.sem.toNat p v = some 4)
    (hw : I.sem.toNat p w = some kp) (Qp : Matrix (Fin k) (Fin kp) (K × K))
    (Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)) (Up : Matrix (Fin kp) (Fin kp) (K × K))
    (Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)) (ep : Fin kp → K)
    (em : Fin (k - kp) → K) (σ : K) :
    RoutineSpec md I (fun st => st.store.read p H.Kd (n * d + lo) = some v ∧
        st.store.read p H.Kp (n * d + lo) = some w ∧
        pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
        pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
        pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up ∧
        pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um ∧
        (∀ j : Fin kp, st.store.read p H.Ea (n * (d + 1) + lo + j) = some (ep j)) ∧
        (∀ j : Fin (k - kp), st.store.read p H.Ea (n * (d + 1) + (lo + kp) + j) =
          some (em j)) ∧ st.store.read p t 0 = some σ ∧
        md.Needs (Writable st.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ∧
          Writable st.store p H.Ea (n * d + lo) k))
      (eighUpNode p mm n d lo k t H)
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), (H.Ea, n * d + lo, k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          ((Matrix.fromCols (mmR Qp Up) (mmR Qm Um)).submatrix id
            ((finCongr hsum).trans finSumFinEquiv.symm)) ∧
        (∀ j : Fin kp, st'.store.read p H.Ea (n * d + lo + j) =
          some ((I.sem.bin p .add (ep j) σ).getD default)) ∧
        (∀ j : Fin (k - kp), st'.store.read p H.Ea (n * d + lo + kp + j) =
          some ((I.sem.bin p .sub (em j) σ).getD default)) ∧ PosKept st st' := by
  have hsp := spec_eighUpSplit hmm md hsem p n d lo k kp t H hk hkp hsum hUE hUQ htU htE Qp Qm Up Um
    ep em σ
  have hbk := RoutineSpec.bindIdx_of_read (m := md) (I := I) (p := p)
    (x := ⟨H.Kp, eighSlotOff (.const n) (.const d) (.var lo)⟩) (bound := (.var k : IExp ℕ))
    (body := fun kp => eighUpSplit (ι := ι) p mm n d lo k kp t H) (v := w) (k := kp)
    (pre := fun st => st.store.read p H.Kp (n * d + lo) = some w ∧ _) (fun st h => by
      simpa [eighSlotOff] using h.1) hw (Mode.needs_of (by simpa using hkp.le) md)
    (fun _ => hsp.spec) (fun st h => h.2)
  have hw4 := spec_eighWhen (m := md) (I := I) (e := eighEqInd (.var 4) 4)
    (fun _ => hbk.spec)
  unfold eighUpNode
  refine (RoutineSpec.bindIdx_of_read (m := md) (I := I) (p := p)
    (x := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (bound := 4) (v := v) (k := 4)
    (pre := fun st => st.store.read p H.Kd (n * d + lo) = some v ∧ _) (fun st h => by
      simpa [eighSlotOff] using h.1) hv (Mode.needs_of (by norm_num) md)
    (fun _ => (routineSpec_eighWhen_zero_bind (by simp [eighEqInd])
      (routineSpec_eighWhen_zero_bind (by simp [eighEqInd]) ⟨hw4.composable, hw4.spec⟩)).spec)
    (fun st h => h.2)).conseq (fun st h => h) (fun x hx => hx) ?_
  rintro st st' - ⟨-, h⟩
  exact (h.2 (by simp [eighEqInd])).2

omit [Inhabited K] in
/-- A node of kind $1$ (a leaf) of the upward pass only reads its kind and modifies nothing. No
printed source. -/
theorem spec_eighUpNode_one (md : Mode) (p : P) (n d lo k t : ℕ) (mm : ι) (H : EighArenas)
    (v : K) (hv : I.sem.toNat p v = some 1) :
    RoutineSpec md I (fun st => st.store.read p H.Kd (n * d + lo) = some v)
      (eighUpNode p mm n d lo k t H) [] fun st st' => st'.store = st.store ∧ PosKept st st' := by
  unfold eighUpNode
  refine (RoutineSpec.bindIdx_of_read (m := md) (I := I) (p := p)
    (x := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (bound := 4) (v := v) (k := 1)
    (pre := fun st => st.store.read p H.Kd (n * d + lo) = some v) (pre' := fun _ => True)
    (fun st h => by simpa [eighSlotOff] using h) hv (Mode.needs_of (by norm_num) md)
    (fun _ => (routineSpec_eighWhen_zero_bind (by simp [eighEqInd])
      (routineSpec_eighWhen_bind_eighWhen_of_eval_eq_zero (by simp [eighEqInd])
        (by simp [eighEqInd]))).spec)
    (fun st h => trivial)).conseq (fun st h => h) (fun x hx => hx) ?_
  rintro st st' - ⟨-, h⟩
  subst h
  exact ⟨rfl, rfl⟩

/-- A node of kind $2$ (one child on the positive side) runs as its shift branch with $\sigma$
(cell $0$ of `t`). No printed source. -/
theorem spec_eighUpNode_two (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (mm : ι) (p : P)
    (n d lo k t : ℕ) (H : EighArenas) (hk : lo + k ≤ n) (hUE : H.Ua ≠ H.Ea)
    (htE : t ≠ H.Ea) (htU : t ≠ H.Ua) (v : K) (hv : I.sem.toNat p v = some 2)
    (U : Matrix (Fin k) (Fin k) (K × K)) (e : Fin k → K) (σ : K) :
    RoutineSpec md I (fun st => st.store.read p H.Kd (n * d + lo) = some v ∧
        pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U ∧
        (∀ i : Fin k, st.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i)) ∧
        st.store.read p t 0 = some σ ∧
        md.Needs (Writable st.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ∧
          Writable st.store p H.Ea (n * d + lo) k))
      (eighUpNode p mm n d lo k t H)
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), (H.Ea, n * d + lo, k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
        (∀ i : Fin k, st'.store.read p H.Ea (n * d + lo + i) =
          some ((I.sem.bin p .add (e i) σ).getD default)) ∧ PosKept st st' := by
  have hsh := spec_eighUpShift md hsem p n d lo k H ⟨t, 0⟩ hk hUE htE htU U e σ
  have hw := spec_eighWhen (m := md) (I := I) (e := eighEqInd (.var 2) 2) (fun _ => hsh.spec)
  unfold eighUpNode
  refine (RoutineSpec.bindIdx_of_read (m := md) (I := I) (p := p)
    (x := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (bound := 4) (v := v) (k := 2)
    (pre := fun st => st.store.read p H.Kd (n * d + lo) = some v ∧ _) (fun st h => by
      simpa [eighSlotOff] using h.1) hv (Mode.needs_of (by norm_num) md)
    (fun _ => (RoutineSpec.bind ⟨hw.composable, hw.spec⟩ (pre₂ := fun _ => True)
      (routineSpec_eighWhen_bind_eighWhen_of_eval_eq_zero (by simp [eighEqInd])
        (by simp [eighEqInd]))
      (fun _ _ _ _ _ => trivial)).spec)
    (fun st h => h.2)).conseq (fun st h => h) (fun x hx => by simpa using hx) ?_
  rintro st st' - ⟨-, st₁, h, rfl⟩
  exact (h.2 (by simp [eighEqInd]))

/-- A node of kind $3$ (one child on the negative side) runs as its shift branch with $-\sigma$
(cell $1$ of `t`). No printed source. -/
theorem spec_eighUpNode_three (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (mm : ι) (p : P)
    (n d lo k t : ℕ) (H : EighArenas) (hk : lo + k ≤ n) (hUE : H.Ua ≠ H.Ea)
    (htE : t ≠ H.Ea) (htU : t ≠ H.Ua) (v : K) (hv : I.sem.toNat p v = some 3)
    (U : Matrix (Fin k) (Fin k) (K × K)) (e : Fin k → K) (σ : K) :
    RoutineSpec md I (fun st => st.store.read p H.Kd (n * d + lo) = some v ∧
        pairLayout.Holds st.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U ∧
        (∀ i : Fin k, st.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i)) ∧
        st.store.read p t 1 = some σ ∧
        md.Needs (Writable st.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ∧
          Writable st.store p H.Ea (n * d + lo) k))
      (eighUpNode p mm n d lo k t H)
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), (H.Ea, n * d + lo, k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
        (∀ i : Fin k, st'.store.read p H.Ea (n * d + lo + i) =
          some ((I.sem.bin p .add (e i) σ).getD default)) ∧ PosKept st st' := by
  have hsh := spec_eighUpShift md hsem p n d lo k H ⟨t, 1⟩ hk hUE htE htU U e σ
  have hw := spec_eighWhen (m := md) (I := I) (e := eighEqInd (.var 3) 3) (fun _ => hsh.spec)
  unfold eighUpNode
  refine (RoutineSpec.bindIdx_of_read (m := md) (I := I) (p := p)
    (x := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (bound := 4) (v := v) (k := 3)
    (pre := fun st => st.store.read p H.Kd (n * d + lo) = some v ∧ _) (fun st h => by
      simpa [eighSlotOff] using h.1) hv (Mode.needs_of (by norm_num) md)
    (fun _ => (routineSpec_eighWhen_zero_bind (by simp [eighEqInd])
      (RoutineSpec.bind ⟨hw.composable, hw.spec⟩ (pre₂ := fun _ => True)
        (routineSpec_eighWhen_of_eval_eq_zero (by simp [eighEqInd]))
        (fun _ _ _ _ _ => trivial))).spec)
    (fun st h => h.2)).conseq (fun st h => h) (fun x hx => by simpa using hx) ?_
  rintro st st' - ⟨-, st₁, h, rfl⟩
  exact (h.2 (by simp [eighEqInd]))


/-- A store agrees with `s₀` outside level $d$ of the output and eigenvalue arenas, and on the
blocks of the node of size $k$ at slot $lo$. -/
def UpNodeFrame (H : EighArenas) (n d lo k : ℕ) (s₀ s : Store P K) : Prop :=
  ∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
    ((b = H.Ua → 2 * (n * n) * d + 2 * n * lo ≤ i ∧
        i < 2 * (n * n) * d + 2 * n * lo + 2 * (k * k)) ∧
      (b = H.Ea → n * d + lo ≤ i ∧ i < n * d + lo + k))) → s.read q b i = s₀.read q b i

section Frame
variable {H : EighArenas} {n d lo k : ℕ} {s₀ s : Store P K}

omit [Inhabited K] in
/-- A cell outside the output and eigenvalue arenas reads as in `s₀`. No printed source. -/
theorem UpNodeFrame.read_of_ne (hF : UpNodeFrame H n d lo k s₀ s) {q : P} {b i : ℕ} (hb : b ≠ H.Ua)
    (hb' : b ≠ H.Ea) : s.read q b i = s₀.read q b i :=
  hF q b i (Or.inl fun h => h.1.elim hb hb')

omit [Inhabited K] in
/-- A cell of the output arena at depth $d + 1$ or above reads as in `s₀`. No printed source. -/
theorem UpNodeFrame.read_ua_of_le (hF : UpNodeFrame H n d lo k s₀ s) (hnd : H.handles.Nodup) {q : P}
    {i : ℕ} (hi : 2 * (n * n) * (d + 1) ≤ i) : s.read q H.Ua i = s₀.read q H.Ua i :=
  hF q H.Ua i (Or.inl fun ⟨_, hc⟩ => by
    have := H.mul_le_and_lt_of_levelCell_ua hnd hc
    omega)

omit [Inhabited K] in
/-- A cell of the eigenvalue arena at depth $d + 1$ or above reads as in `s₀`. No printed source. -/
theorem UpNodeFrame.read_ea_of_le (hF : UpNodeFrame H n d lo k s₀ s) (hnd : H.handles.Nodup) {q : P}
    {i : ℕ} (hi : n * (d + 1) ≤ i) : s.read q H.Ea i = s₀.read q H.Ea i :=
  hF q H.Ea i (Or.inl fun ⟨_, hc⟩ => by
    have := H.mul_le_and_lt_of_levelCell_ea hnd hc
    omega)

end Frame

omit [Inhabited K] in
/-- A leaf node leaves its output where it is (`NLAlib.eighUpNode`), from a state that agrees with
`s₀` as in `NLAlib.UpNodeFrame`. No printed source. -/
theorem spec_eighUpNode_leafStep (md : Mode) (mm : ι) (p : P) (n d lo k t : ℕ) (H : EighArenas)
    (hnd : H.handles.Nodup) {s₀ : St P K C} (U : Matrix (Fin k) (Fin k) (K × K)) (e : Fin k → K)
    (hKd : ReadsIdx I.sem s₀.store p H.Kd (n * d + lo) 1)
    (hU : pairLayout.Holds s₀.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U)
    (hE : ∀ i : Fin k, s₀.store.read p H.Ea (n * d + lo + i) = some (e i)) :
    Spec md I (fun st => st.store.shape = s₀.store.shape ∧
        UpNodeFrame H n d lo k s₀.store st.store) (eighUpNode p mm n d lo k t H).run []
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
        (∀ i : Fin k, st'.store.read p H.Ea (n * d + lo + i) = some (e i)) ∧ PosKept st st' := by
  obtain ⟨hUE, -, hKdU, hKdE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hKd
  intro st ⟨hsh, hF⟩
  refine wp_mono ((spec_eighUpNode_one (I := I) md p n d lo k t mm H v hk).spec st
    (by rw [hF.read_of_ne hKdU hKdE]; exact hv)) fun st' ⟨hm, hs, hp⟩ => ⟨hm, ?_, ?_, hp⟩
  · rw [hs]
    exact hU.of_forall_read_eq fun i hi hi' => hF p H.Ua i (Or.inr ⟨fun _ => ⟨hi, by
      simpa [pairLayout, Nat.mul_comm] using hi'⟩, fun h => absurd h hUE⟩)
  · intro i
    rw [hs, hF p H.Ea _ (Or.inr ⟨fun h => absurd h.symm hUE, fun _ => ⟨by omega, by omega⟩⟩)]
    exact hE i

/-- A one-child node (`NLAlib.eighUpNode`, kind $2$ or $3$) copies its child's output and adds the
shift, from a state that agrees with `s₀` as in `NLAlib.UpNodeFrame`, where the arenas hold the
child's output. No printed source. -/
theorem spec_eighUpNode_shiftStep (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (mm : ι) (p : P)
    (n d lo k t : ℕ) (H : EighArenas) (hk : lo + k ≤ n) (hnd : H.handles.Nodup)
    (htH : t ∉ H.handles) (b : Bool) {s₀ : St P K C} (U : Matrix (Fin k) (Fin k) (K × K))
    (e : Fin k → K) (σ : K)
    (hKd : ReadsIdx I.sem s₀.store p H.Kd (n * d + lo) (if b then 2 else 3))
    (hU : pairLayout.Holds s₀.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U)
    (hE : ∀ i : Fin k, s₀.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i))
    (hσ : s₀.store.read p t (if b then 0 else 1) = some σ)
    (hW : md.Needs (Writable s₀.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ∧
      Writable s₀.store p H.Ea (n * d + lo) k)) :
    Spec md I (fun st => st.store.shape = s₀.store.shape ∧
        UpNodeFrame H n d lo k s₀.store st.store) (eighUpNode p mm n d lo k t H).run
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), (H.Ea, n * d + lo, k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
        (∀ i : Fin k, st'.store.read p H.Ea (n * d + lo + i) =
          some ((I.sem.bin p .add (e i) σ).getD default)) ∧ PosKept st st' := by
  have htU : t ≠ H.Ua := fun h => htH (h ▸ by simp [EighArenas.handles])
  have htE : t ≠ H.Ea := fun h => htH (h ▸ by simp [EighArenas.handles])
  obtain ⟨hUE, -, hKdU, hKdE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  obtain ⟨v, hv, hk'⟩ := Option.bind_eq_some_iff.mp hKd
  intro st ⟨hsh, hF⟩
  have hv' : st.store.read p H.Kd (n * d + lo) = some v := by
    rw [hF.read_of_ne hKdU hKdE]; exact hv
  have hU' := hU.of_forall_read_eq (s' := st.store) fun i hi _ =>
    hF.read_ua_of_le hnd (by omega)
  have hE' : ∀ i : Fin k, st.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i) := fun i =>
    (hF.read_ea_of_le hnd (by rw [Nat.mul_succ]; omega)).trans (hE i)
  have hσ' := (hF.read_of_ne htU htE).trans hσ
  cases b
  · exact (spec_eighUpNode_three md hsem mm p n d lo k t H hk hUE htE htU v hk' U e σ).spec st
      ⟨hv', hU', hE', hσ', hW.mono fun ⟨h1, h2⟩ => ⟨h1.of_shape_eq hsh, h2.of_shape_eq hsh⟩⟩
  · exact (spec_eighUpNode_two md hsem mm p n d lo k t H hk hUE htE htU v hk' U e σ).spec st
      ⟨hv', hU', hE', hσ', hW.mono fun ⟨h1, h2⟩ => ⟨h1.of_shape_eq hsh, h2.of_shape_eq hsh⟩⟩

/-- A split node (`NLAlib.eighUpNode`, kind $4$) assembles its output from its children's, from a
state that agrees with `s₀` as in `NLAlib.UpNodeFrame`, where the arenas hold the bases and the
children's outputs. No printed source. -/
theorem spec_eighUpNode_splitStep {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n d lo k kp t : ℕ)
    (H : EighArenas) (hk : lo + k ≤ n) (hkp : kp < k)
    (hsum : k = kp + (k - kp)) (hnd : H.handles.Nodup)
    (htH : t ∉ H.handles) {s₀ : St P K C} (Qp : Matrix (Fin k) (Fin kp) (K × K))
    (Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)) (Up : Matrix (Fin kp) (Fin kp) (K × K))
    (Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)) (ep : Fin kp → K)
    (em : Fin (k - kp) → K) (σ : K)
    (hKd : ReadsIdx I.sem s₀.store p H.Kd (n * d + lo) 4)
    (hKp : ReadsIdx I.sem s₀.store p H.Kp (n * d + lo) kp)
    (hQp : pairLayout.Holds s₀.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s₀.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (hUp : pairLayout.Holds s₀.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up)
    (hUm : pairLayout.Holds s₀.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um)
    (hEp : ∀ j : Fin kp, s₀.store.read p H.Ea (n * (d + 1) + lo + j) = some (ep j))
    (hEm : ∀ j : Fin (k - kp), s₀.store.read p H.Ea (n * (d + 1) + (lo + kp) + j) =
      some (em j))
    (hσ : s₀.store.read p t 0 = some σ)
    (hW : md.Needs (Writable s₀.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ∧
      Writable s₀.store p H.Ea (n * d + lo) k)) :
    Spec md I (fun st => st.store.shape = s₀.store.shape ∧
        UpNodeFrame H n d lo k s₀.store st.store) (eighUpNode p mm n d lo k t H).run
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), (H.Ea, n * d + lo, k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          ((Matrix.fromCols (mmR Qp Up) (mmR Qm Um)).submatrix id
            ((finCongr hsum).trans finSumFinEquiv.symm)) ∧
        (∀ j : Fin kp, st'.store.read p H.Ea (n * d + lo + j) =
          some ((I.sem.bin p .add (ep j) σ).getD default)) ∧
        (∀ j : Fin (k - kp), st'.store.read p H.Ea (n * d + lo + kp + j) =
          some ((I.sem.bin p .sub (em j) σ).getD default)) ∧ PosKept st st' := by
  have htU : t ≠ H.Ua := fun h => htH (h ▸ by simp [EighArenas.handles])
  have htE : t ≠ H.Ea := fun h => htH (h ▸ by simp [EighArenas.handles])
  obtain ⟨hUE, hUQ, hKdU, hKdE, hKpU, hKpE, hQE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  obtain ⟨v, hv, hk'⟩ := Option.bind_eq_some_iff.mp hKd
  obtain ⟨w, hw, hk''⟩ := Option.bind_eq_some_iff.mp hKp
  intro st ⟨hsh, hF⟩
  have hnk : k * kp ≤ k * k := Nat.mul_le_mul_left k hkp.le
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  refine (spec_eighUpNode_four hmm md hsem p n d lo k kp t H hk hkp hsum hUE hUQ htU htE v w hk'
    hk'' Qp Qm Up Um ep em σ).spec st ⟨by rw [hF.read_of_ne hKdU hKdE]; exact hv,
    by rw [hF.read_of_ne hKpU hKpE]; exact hw,
    hQp.of_forall_read_eq fun i _ _ => hF.read_of_ne (Ne.symm hUQ) hQE,
    hQm.of_forall_read_eq fun i _ _ => hF.read_of_ne (Ne.symm hUQ) hQE,
    hUp.of_forall_read_eq fun i hi _ => hF.read_ua_of_le hnd (by omega),
    hUm.of_forall_read_eq fun i hi _ => hF.read_ua_of_le hnd (by nlinarith),
    fun j => (hF.read_ea_of_le hnd (by rw [Nat.mul_succ]; omega)).trans (hEp j),
    fun j => (hF.read_ea_of_le hnd (by rw [Nat.mul_succ]; omega)).trans (hEm j),
    (hF.read_of_ne htU htE).trans hσ,
    hW.mono fun ⟨h1, h2⟩ => ⟨h1.of_shape_eq hsh, h2.of_shape_eq hsh⟩⟩


section NodeStep

variable {mm : ι} (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
  (p : P) (n ℓ₀ F d D : ℕ) (hn : 1 ≤ n) (hd : d < D) (H : EighArenas) (t : ℕ)
  {s₀ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {a : List Bool} {lo : ℕ}
  {y : EighNode K} (ha : a.length = d)
  (hay : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
  (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
  (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
    (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
    ((eighTapeMachine I p mmR qrR).ofNat 2)))
  (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
    ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2))))
  (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
    (d + 1))
  (hW : md.Needs (Writable s₀.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (y.k * y.k)) ∧
    Writable s₀.store p H.Ea (n * d + lo) y.k))

include hn hay hnd htH ht0 ht1 hout ha hW in
/-- The one-child step of a node writes the output of `NLAlib.eighAux`. No printed source. -/
theorem spec_eighUpNodeStep_shift (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem))
    {b : Bool} {A' : Matrix (Fin y.k) (Fin y.k) (K × K)} {σ' : K}
    (hs : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) = .shift b A' σ')
    (hKd : ReadsIdx I.sem s₀.store p H.Kd (n * d + lo) (if b then 2 else 3)) :
    Spec md I (fun st => st.store.shape = s₀.store.shape ∧
        UpNodeFrame H n d lo y.k s₀.store st.store) (eighUpNode p mm n d lo y.k t H).run
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (y.k * y.k)), (H.Ea, n * d + lo, y.k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - (d + 1) + 1) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).1 ∧
        (∀ i : Fin y.k, st'.store.read p H.Ea (n * d + lo + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - (d + 1) + 1) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).2 i)) ∧
        PosKept st st' := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hay
  obtain ⟨hyR, -, -⟩ := eighLoc_params hay
  rw [ha] at hyR
  have hch : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [b]) = some (lo,
      ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
        y.ℓ + 1⟩) := by
    rw [eighLoc_append_singleton, hay]
    simp [eighLoc, ha, hs]
  obtain ⟨hUc, hEc⟩ := hout (a ++ [b]) lo _ (by simp [ha]) hch
  refine (spec_eighUpNode_shiftStep md (u := u) (dec := dec) hsem mm p n d lo y.k t H hkn hnd htH
    b _ _
    (if b then M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2)
      else M.neg (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2))) hKd hUc hEc
    (by cases b; exacts [ht1, ht0]) hW).conseq (fun st h => h) (fun x hx => hx)
    fun st st' _ ⟨hU, hE, hp⟩ => ⟨?_, fun i => (hE i).trans ?_, hp⟩
  · simp only [eighAux, eighSlotTree, hs]
    exact hU
  · simp only [eighAux, eighSlotTree, hs]
    rw [eq_of_eighStep_eq_shift hs, hyR]
    cases b <;> rfl

include hn hay hnd htH ht0 hout ha hW in
/-- The split step of a node writes the output of `NLAlib.eighAux`. No printed source. -/
theorem spec_eighUpNodeStep_split {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) {kp : ℕ} {hkp : kp ≤ y.k}
    {Qp : Matrix (Fin y.k) (Fin kp) (K × K)} {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (K × K)}
    {Ap : Matrix (Fin kp) (Fin kp) (K × K)} {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (K × K)}
    {σ' : K}
    (hs : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) = .split kp hkp Qp Qm Ap Am σ')
    (hKd : ReadsIdx I.sem s₀.store p H.Kd (n * d + lo) 4)
    (hKp : ReadsIdx I.sem s₀.store p H.Kp (n * d + lo) kp)
    (hQp : pairLayout.Holds s₀.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s₀.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (y.k * kp)) Qm) :
    Spec md I (fun st => st.store.shape = s₀.store.shape ∧
        UpNodeFrame H n d lo y.k s₀.store st.store) (eighUpNode p mm n d lo y.k t H).run
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (y.k * y.k)), (H.Ea, n * d + lo, y.k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - (d + 1) + 1) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).1 ∧
        (∀ i : Fin y.k, st'.store.read p H.Ea (n * d + lo + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - (d + 1) + 1) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).2 i)) ∧
        PosKept st st' := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hay
  obtain ⟨hyR, -, -⟩ := eighLoc_params hay
  rw [ha] at hyR
  obtain ⟨hσ', -, hkpk⟩ := eq_div_and_pos_and_lt_of_eighStep_eq_split hs
  have hchp : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [true]) = some (lo,
      ⟨kp, Ap, (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
        y.ℓ + 1⟩) := by
    rw [eighLoc_append_singleton, hay]
    simp [eighLoc, ha, hs]
  have hchm : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [false]) = some (lo + kp,
      ⟨y.k - kp, Am, (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
        y.ℓ + 1⟩) := by
    rw [eighLoc_append_singleton, hay]
    simp [eighLoc, ha, hs]
  obtain ⟨hUp, hEp⟩ := hout (a ++ [true]) lo _ (by simp [ha]) hchp
  obtain ⟨hUm, hEm⟩ := hout (a ++ [false]) (lo + kp) _ (by simp [ha]) hchm
  refine (spec_eighUpNode_splitStep hmm md hsem p n d lo y.k kp t H hkn hkpk
    (Nat.add_sub_of_le hkp).symm hnd htH _ _ _ _ _ _ (M.div y.R (M.ofNat 2)) hKd hKp hQp hQm hUp hUm
    hEp hEm (by rw [hyR]; exact ht0)
    hW).conseq (fun st h => h) (fun x hx => hx)
    fun st st' _ ⟨hU, hE1, hE2, hp⟩ => ⟨?_, fun i => ?_, hp⟩
  · simp only [eighAux, eighSlotTree, hs, ite_true, Bool.false_eq_true, ite_false]
    exact hU
  · simp only [eighAux, eighSlotTree, hs, ite_true, Bool.false_eq_true, ite_false]
    rw [hσ']
    by_cases hi : (i : ℕ) < kp
    · rw [finSumFinEquiv_symm_apply_lt hkp i hi, Sum.elim_inl]
      exact hE1 ⟨i, hi⟩
    · rw [finSumFinEquiv_symm_apply_ge hkp i (by omega), Sum.elim_inr]
      have := hE2 ⟨i - kp, by omega⟩
      rw [show n * d + lo + kp + (i - kp) = n * d + lo + i by omega] at this
      exact this

include hnd in
/-- The leaf step of a node keeps the output of `NLAlib.eighAux` already stored. No printed
source. -/
theorem spec_eighUpNodeStep_leaf {U : Matrix (Fin y.k) (Fin y.k) (K × K)} {e : Fin y.k → K}
    (hs : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) = .leaf U e)
    (hKd : ReadsIdx I.sem s₀.store p H.Kd (n * d + lo) 1)
    (hU : pairLayout.Holds s₀.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U)
    (hE : ∀ i : Fin y.k, s₀.store.read p H.Ea (n * d + lo + i) = some (e i)) :
    Spec md I (fun st => st.store.shape = s₀.store.shape ∧
        UpNodeFrame H n d lo y.k s₀.store st.store) (eighUpNode p mm n d lo y.k t H).run
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (y.k * y.k)), (H.Ea, n * d + lo, y.k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - (d + 1) + 1) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).1 ∧
        (∀ i : Fin y.k, st'.store.read p H.Ea (n * d + lo + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - (d + 1) + 1) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).2 i)) ∧
        PosKept st st' := by
  refine (spec_eighUpNode_leafStep md mm p n d lo y.k t H hnd U e hKd hU hE).conseq
    (fun st h => h) (fun x hx => absurd hx List.not_mem_nil) fun st st' _ h => ?_
  simp only [eighAux, eighSlotTree, hs]
  exact h

include hn hd hay hnd htH ht0 ht1 hout ha hW in
/-- One node of the upward pass (`NLAlib.eighUpNode` at the node $y$ of slot $lo$) as a
specification: it writes its output (`NLAlib.eighAux` at budget $D - d$), modifying only the
node's output block and eigenvalue cells and keeping the tape positions, from a state that agrees
with `s₀` (where the arenas hold the records of depth $d$ and the outputs of depth $d + 1$) as in
`NLAlib.UpNodeFrame`; in mode `total` it also succeeds, given the standard model and the arenas
allocated. No printed source. -/
theorem spec_eighUpNodeStep {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem))
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    Spec md I (fun st => st.store.shape = s₀.store.shape ∧
        UpNodeFrame H n d lo y.k s₀.store st.store) (eighUpNode p mm n d lo y.k t H).run
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (y.k * y.k)), (H.Ea, n * d + lo, y.k)]
      fun st st' => pairLayout.Holds st'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).1 ∧
        (∀ i : Fin y.k, st'.store.read p H.Ea (n * d + lo + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).2 i)) ∧
        PosKept st st' := by
  have hr := hrec a lo y ha hay (eighLoc_bounds hn hay).1
  rw [show D - d = D - (d + 1) + 1 by omega]
  cases hs : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) with
  | leaf U e =>
    rw [hs] at hr
    exact spec_eighUpNodeStep_leaf md p n F d D H t hnd hs hr.1 hr.2.1 hr.2.2
  | shift b A' σ' =>
    rw [hs] at hr
    exact spec_eighUpNodeStep_shift md p n ℓ₀ F d D hn H t ha hay hnd htH ht0 ht1 hout hW hsem hs hr
  | split kp hkp Qp Qm Ap Am σ' =>
    rw [hs] at hr
    exact spec_eighUpNodeStep_split md p n ℓ₀ F d D hn H t ha hay hnd htH ht0 hout hW hmm hsem hs
      hr.1 hr.2.1 hr.2.2.1 hr.2.2.2

end NodeStep



/-! ### The slot -/

omit [Inhabited K] in
/-- A slot reads its stored size $k$ (the index binder) and runs its node if $k \ge 1$ (the
specification of the node is the hypothesis), and nothing for $k = 0$. No printed source. -/
theorem spec_eighUpSlotCore (md : Mode) (mm : ι) (p : P) (n d lo t k : ℕ) (H : EighArenas)
    {v : K} (hv : I.sem.toNat p v = some k) (hk : k ≤ n - lo) {Pr : Store P K → Prop}
    {fp : List (ℕ × ℕ × ℕ)} {post : St P K C → St P K C → Prop}
    (hnode : 0 < k → Spec md I (fun st => Pr st.store) (eighUpNode p mm n d lo k t H).run fp
      post) :
    Spec md I (fun st => st.store.read p H.Sz (n * d + lo) = some v ∧ Pr st.store)
      (eighUpSlot p mm n d lo t H).run fp
      fun st st' => (k = 0 → st'.store = st.store ∧ st'.pos = st.pos) ∧
        (0 < k → post (st.addCnt (I.charge (OpKind.toNat p))) st') := by
  have hw := spec_eighWhen (m := md) (I := I) (e := (IExp.var k : IExp ℕ)) (fun h => hnode h)
  unfold eighUpSlot
  refine (RoutineSpec.bindIdx_of_read (m := md) (I := I) (p := p) (v := v) (k := k)
    (x := ⟨H.Sz, eighSlotOff (.const n) (.const d) (.var lo)⟩) (bound := .const n - .var lo)
    (pre := fun st => st.store.read p H.Sz (n * d + lo) = some v ∧ Pr st.store)
    (pre' := fun st => Pr st.store)
    (body := fun k => eighWhen (.var k) (eighUpNode p mm n d lo k t H))
    (fun st h => by simpa [eighSlotOff] using h.1) hv
    (Mode.needs_of (by simpa using hk) md) (fun _ => hw.spec) (fun st h => h.2)).spec.conseq
    (fun st h => h) (fun x hx => hx) ?_
  rintro st st' - ⟨-, h0, h1⟩
  exact ⟨fun hk0 => by
    have := h0 hk0
    subst this
    exact ⟨rfl, rfl⟩, h1⟩



/-- **The slots below $lo$ of depth $d$ are done** in the state `s` of the upward pass, run from
the state `s₀` (machine `M`, root `root` of size $n$, depth budget $D$): the store shape and the
tape positions are those of `s₀`; every cell outside depth $d$ of the output and eigenvalue arenas,
or outside the blocks of the nodes at the slots below $lo$, reads as in `s₀`; and every such node
has its output (`NLAlib.eighAux` at budget $D - d$) stored. -/
abbrev EighArenas.UpSlotsDone (H : EighArenas) (s s₀ : St P K C) (p : P) (M : FloatMachine K ℕ ℕ)
    (n F D : ℕ) (R₀ β : K) (root : EighNode K) (d lo : ℕ) : Prop :=
  s.store.shape = s₀.store.shape ∧ s.pos = s₀.pos ∧
    (∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
        eighLoc M n F R₀ β 0 0 root a = some (lo', y) → lo' < lo →
        (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
          2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
        (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
      s.store.read q b i = s₀.store.read q b i) ∧
    ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
      eighLoc M n F R₀ β 0 0 root a = some (lo', y) → lo' < lo →
      pairLayout.Holds s.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
          (eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).1 ∧
        ∀ i : Fin y.k, s.store.read p H.Ea (n * d + lo' + i) = some
          ((eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).2 i)

omit [AddMonoid C] in
/-- The state before slot $lo$ agrees with the state `s₀` before the level as `NLAlib.UpNodeFrame`
asks for the node at that slot. No printed source. -/
theorem upNodeFrame_of_upSlotsDone {p : P} {n ℓ₀ F d D lo : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} {H : EighArenas} {s s₀ : St P K C} {a : List Bool} {y : EighNode K}
    (hn : 1 ≤ n) (ha : a.length = d)
    (hay : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (hdone : H.UpSlotsDone s s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d
      lo) :
    UpNodeFrame H n d lo y.k s₀.store s.store := fun q b i hb' => by
  refine hdone.2.2.1 q b i (hb'.imp_right fun ⟨hU', hE'⟩ a' lo' y' ha' hay' hlt => ?_)
  obtain ⟨h1, h2⟩ := add_le_and_mul_add_le_of_eighLoc_of_lt hn ha ha' hay hay' hlt
  refine ⟨?_, ?_⟩
  · by_cases hbU : b = H.Ua
    · exact Or.inr (Or.inr (by have := hU' hbU; omega))
    · exact Or.inl hbU
  · by_cases hbE : b = H.Ea
    · exact Or.inr (Or.inr (by have := hE' hbE; omega))
    · exact Or.inl hbE

omit [AddMonoid C] in
/-- An empty slot (no node) that changes nothing finishes the slots up to it. No printed source. -/
theorem upSlotsDone_succ_of_empty {p : P} {n ℓ₀ F d D lo : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} {H : EighArenas} {s s' s₀ : St P K C}
    (hy : ∀ (a : List Bool) (y : EighNode K), a.length = d →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a ≠ some (lo, y))
    (hdone : H.UpSlotsDone s s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d
      lo) (hst : s'.store = s.store) (hp : s'.pos = s.pos) :
    H.UpSlotsDone s' s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d
      (lo + 1) := by
  obtain ⟨hsh, hps, hfr, hdn⟩ := hdone
  refine ⟨by rw [hst]; exact hsh, hp.trans hps, fun q b i hb => ?_, fun a lo' y ha hay hlt => ?_⟩
  · rw [hst]
    exact hfr q b i (hb.imp_right fun H' a lo' y ha hay hlt => H' a lo' y ha hay (by omega))
  · rw [hst]
    refine hdn a lo' y ha hay (lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) ?_)
    rintro rfl
    exact hy a y ha hay

omit [AddMonoid C] in
/-- A node that writes its output and modifies only its blocks finishes the slots up to it. No
printed source. -/
theorem upSlotsDone_succ_of_node {p : P} {n ℓ₀ F d D lo : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} {H : EighArenas} {s s' s₀ : St P K C} {a : List Bool} {y : EighNode K}
    (hn : 1 ≤ n) (ha : a.length = d) (hnd : H.handles.Nodup)
    (hay : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (hdone : H.UpSlotsDone s s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d
      lo)
    (hm : Modifies [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (y.k * y.k)),
      (H.Ea, n * d + lo, y.k)] s.store s'.store) (hp : s'.pos = s.pos)
    (hU : pairLayout.Holds s'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
      (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
        (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).1)
    (hE : ∀ i : Fin y.k, s'.store.read p H.Ea (n * d + lo + i) = some
      ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
        (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).2 i)) :
    H.UpSlotsDone s' s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d
      (lo + 1) := by
  obtain ⟨hsh, hps, hfr, hdn⟩ := hdone
  obtain ⟨hk1, hb⟩ := eighLoc_bounds hn hay
  obtain ⟨hUE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  refine ⟨hm.1.trans hsh, hp.trans hps, fun q b i hb' => ?_, fun a' lo' y' ha' hay' hlt => ?_⟩
  · have hW := hb'.elim (not_mem_blocks_of_not_levelCell hb) fun hb' =>
      hb' a lo y ha hay (Nat.lt_succ_self lo)
    rw [hm.2 q b i (by fp_omega [hW.1, hW.2])]
    exact hfr q b i (hb'.imp_right fun H' a lo' y ha hay hlt => H' a lo' y ha hay (by omega))
  · by_cases hll : lo' = lo
    · subst hll
      have haa : a' = a := by
        by_contra hne
        have := eighLoc_disjoint (ha'.trans ha.symm) hne hay' hay
        have := (eighLoc_bounds hn hay').1
        omega
      subst haa
      rw [hay] at hay'
      cases hay'
      exact ⟨hU, hE⟩
    · have hlt' : lo' < lo := by omega
      obtain ⟨hU', hE'⟩ := hdn a' lo' y' ha' hay' hlt'
      obtain ⟨h1, h2⟩ := add_le_and_mul_add_le_of_eighLoc_of_lt hn ha ha' hay hay' hlt'
      refine ⟨(readsOnly_pairLayoutHolds p H.Ua _ _).of_modifies hU' hm (by
          simp only [pairLayout] at hU'; fp_omega [hUE, h1, h2]), fun i => ?_⟩
      rw [hm.2 p H.Ea _ (by fp_omega [hUE, h1, h2, i.2])]
      exact hE' i

/-- One slot of the upward pass (`NLAlib.eighUpSlot` at slot $lo < n$ of depth $d < D$) as a
specification: from the slots below $lo$ done (`NLAlib.EighArenas.UpSlotsDone`), the arenas of the
state `s₀` holding the nodes and records of depth $d$ and the outputs of depth $d + 1$, and the
shift cells of `t` holding $\pm\mathrm{fl}(R/2)$, the slots up to $lo$ are done; only the output
and eigenvalue cells of depth $d$ are modified. In mode `total` it also succeeds, given the
standard model and the arenas allocated. No printed source. -/
theorem spec_eighUpSlot {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n ℓ₀ F d D : ℕ)
    (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} {lo : ℕ} (hlo : lo < n) (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
      ((eighTapeMachine I p mmR qrR).div
        (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
        ((eighTapeMachine I p mmR qrR).ofNat 2))))
    (hlev : H.LevelHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hSh : md.Needs (H.Shaped s₀.store p n D)) :
    Spec md I (fun st => H.UpSlotsDone st s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ d lo) (eighUpSlot p mm n d lo t H).run
      [(H.Ua, 2 * (n * n) * d, 2 * (n * n)), (H.Ea, n * d, n)]
      fun _ st' => H.UpSlotsDone st' s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ d (lo + 1) := by
  have hn : 1 ≤ n := by omega
  obtain ⟨hUE, -, -, -, -, -, -, hSzU, hSzE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  intro st hinv
  by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  swap
  · push Not at hy
    obtain ⟨v, hvr0, hv⟩ := Option.bind_eq_some_iff.mp (hlev.2.1 lo hlo fun a y ha => hy a y ha)
    have hSz : st.store.read p H.Sz (n * d + lo) = some v :=
      (hinv.2.2.1 p _ _ (Or.inl fun h => h.1.elim hSzU hSzE)).trans hvr0
    refine wp_mono ((spec_eighUpSlotCore md mm p n d lo t 0 H hv (Nat.zero_le _)
      (Pr := fun _ => True) (fp := []) (post := fun _ _ => True)
      (fun h => absurd h (lt_irrefl 0))) st ⟨hSz, trivial⟩) fun st' ⟨hm, h0, _⟩ => ⟨
        hm.mono fun x hx => absurd hx List.not_mem_nil,
        upSlotsDone_succ_of_empty hy hinv (h0 rfl).1 (h0 rfl).2⟩
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hay
  obtain ⟨v, hvr0, hv⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
  have hSz : st.store.read p H.Sz (n * d + lo) = some v :=
    (hinv.2.2.1 p _ _ (Or.inl fun h => h.1.elim hSzU hSzE)).trans hvr0
  have hlk : 2 * n * lo + 2 * (y.k * y.k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) (show lo + y.k ≤ n by omega)
    nlinarith [Nat.mul_le_mul_right y.k (show y.k ≤ n by omega)]
  have hW : md.Needs (Writable s₀.store p H.Ua (2 * (n * n) * d + 2 * n * lo) (2 * (y.k * y.k)) ∧
      Writable s₀.store p H.Ea (n * d + lo) y.k) :=
    hSh.mono fun ⟨_, _, hUa, _, hEa, _⟩ => ⟨writable_of_shape_eq rfl hUa (by
      have := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ D + 1 by omega)
      nlinarith), writable_of_shape_eq rfl hEa (by
      have := Nat.mul_le_mul_left n (show d + 1 ≤ D + 1 by omega)
      nlinarith)⟩
  refine wp_mono ((spec_eighUpSlotCore md mm p n d lo t y.k H hv (by omega)
    (Pr := fun s => s.shape = s₀.store.shape ∧ UpNodeFrame H n d lo y.k s₀.store s)
    (fun _ => spec_eighUpNodeStep md p n ℓ₀ F d D hn hd H t ha hay hnd htH ht0 ht1 hout hW hmm
      hsem hrec) |> fun h => h) st ⟨hSz, hinv.1, upNodeFrame_of_upSlotsDone hn ha hay hinv⟩)
    fun st' ⟨hm, _, h1⟩ => ?_
  obtain ⟨hU, hE, hp⟩ := h1 (by omega)
  refine ⟨hm.of_sub fun x hx => ?_, upSlotsDone_succ_of_node hn ha hnd hay hinv hm hp hU hE⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨(H.Ua, 2 * (n * n) * d, 2 * (n * n)), by simp, rfl, by dsimp only; omega,
      by dsimp only; omega⟩
  · exact ⟨(H.Ea, n * d, n), by simp, rfl, by dsimp only; omega, by dsimp only; omega⟩


/-- One slot of the upward pass (`NLAlib.eighUpSlot` at slot $lo < n$ of depth $d < D$): the node
at the slot (if any) gets its output; the shape, the tape positions, every cell outside the blocks
of the nodes at the slots up to $lo$, and the outputs of the slots below are kept, when the arenas
in `s₀` hold the nodes and records of depth $d$ and the outputs of depth $d + 1$, the shift cells
of `t` hold $\pm\mathrm{fl}(R/2)$, and `s₁` reads as `s₀` outside the blocks of the slots below
$lo$, which hold their outputs. -/
theorem holds_of_exec_eighUpSlot {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ s₁ s₂ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {lo : ℕ} (hlo : lo < n)
    (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
      ((eighTapeMachine I p mmR qrR).div (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
        ((eighTapeMachine I p mmR qrR).ofNat 2))))
    (hlev : H.LevelHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hdone : H.UpSlotsDone s₁ s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      d lo)
    (h : exec I (eighUpSlot p mm n d lo t H).run s₁ = some s₂) :
    H.UpSlotsDone s₂ s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d
      (lo + 1) :=
  (Triple.holds_of_exec (spec_eighUpSlot hmm .liberal (u := fun _ => 0) (dec := fun _ _ => 0)
    trivial p n ℓ₀ F d D hd H t hlo hnd htH ht0 ht1 hlev hrec hout trivial) hdone h).2

end NLAlib
