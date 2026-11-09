/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode.SignStep
public import NLAlib.Matrix.Computation.SpectralBisectionNode.Compress

/-!
# The split block of the spectral bisection node step

A run of the split block of the node step of `NLAlib.eighProg` writes the outcome of the split of
`NLAlib.eighStep` on the machine of the semantics: the two children's matrices, sizes and kinds,
and the bases of the deflations; every cell outside the node's window is unchanged; under the
standard model it succeeds. Both facts come from one routine specification of the block, proved
with the program logic (`NLAlib/Computation/RoutineSpec.lean`) from those of the deflation and
compression blocks.

## Main definitions

* `NLAlib.EighNodeWindow`, `NLAlib.eighSplitWindow`: the cells a node step may write, and the
  blocks a split writes.

## Main results

* `NLAlib.spec_eighSplitBlock_of_body`: the eight scratch allocations of a split, by named states.
* `NLAlib.spec_eighSplitBody`, `NLAlib.spec_eighSplitBlock`: the split body and block as
  specifications, for every mode.
* `NLAlib.holds_of_exec_eighSplitBlock`: what a successful split computes.
* `NLAlib.holds_of_exec_eighSplitBlock_frame`: the same, with the precise frame of the node's
  window.
* `NLAlib.exists_exec_eighSplitBlock`: a split succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The node step -/
/-- A cell is disjoint from a block inside a window it avoids. -/
theorem blockDisjoint_of_window {b i B off len lo' hi' : ℕ} (h : b = B → i < lo' ∨ hi' ≤ i)
    (h1 : lo' ≤ off) (h2 : off + len ≤ hi') : blockDisjoint (b, i, 1) (B, off, len) = true := by
  apply blockDisjoint_of_ne_or_le
  change b ≠ B ∨ i + 1 ≤ off ∨ off + len ≤ i
  by_cases hb : b = B
  · have := h hb
    omega
  · exact Or.inl hb

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
theorem pairLayout_holds_of_read_eq {s s' : Store P K} {p : P} {b off l m : ℕ}
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

omit [Inhabited K] in
/-- **The scratch prefix of a split.** If the store has $b$ buffers in every state satisfying
`pre`, and the body of `NLAlib.eighSplitBlock` (two deflations, two compressions and four size
literals) at the scratch handles $b, \dots, b + 7$ meets a specification from the state after
the eight allocations of $2n^2$ cells, modifying `fp` and the eight scratch buffers, then the
split block meets the specification whose footprint is `fp` and whose postcondition is the
body's after the eight releases. No printed source. -/
theorem spec_eighSplitBlock_of_body {m : Mode} (p : P) (mm qr : ι) (n d lo k kp : IExp ℕ)
    (Sg Pp Pm Ma Qa Sz Kd Kp : ℕ) (two sg nsg sq : Cell ℕ ℕ) {b : ℕ}
    {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    {fp : List (ℕ × ℕ × ℕ)} (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st, pre st →
      pre' ((fun s => s.allocate p (2 * (n * n) : IExp ℕ).eval (I.width p))^[8] st))
    (h : Spec m I pre' (do
        eighDeflateBlock p mm qr n k kp lo 0 Sg sq Pp b (b + 1) (b + 2) (b + 3) Qa
          (eighBlockOff n d lo)
        eighDeflateBlock p mm qr n k (k - kp) lo 1 Sg sq Pm b (b + 1) (b + 2) (b + 3) Qa
          (eighBlockOff n d lo + 2 * (k * kp))
        eighCompressBlock p mm k kp Qa (eighBlockOff n d lo) Ma (eighBlockOff n d lo)
          (eighBlockOff n (d + 1) lo) two sg (b + 4) (b + 5) (b + 6) (b + 7)
        eighCompressBlock p mm k (k - kp) Qa (eighBlockOff n d lo + 2 * (k * kp)) Ma
          (eighBlockOff n d lo) (eighBlockOff n (d + 1) (lo + kp)) two nsg (b + 4) (b + 5)
          (b + 6) (b + 7)
        ins (.litIdx p ⟨Sz, eighSlotOff n (d + 1) lo⟩ kp)
        ins (.litIdx p ⟨Sz, eighSlotOff n (d + 1) (lo + kp)⟩ (k - kp))
        ins (.litIdx p ⟨Kd, eighSlotOff n d lo⟩ 4)
        ins (.litIdx p ⟨Kp, eighSlotOff n d lo⟩ kp) : Builder P ι ℕ ℕ Unit).run
      (fp ++ (List.range 8).map fun j => (b + j, 0, (2 * (n * n) : IExp ℕ).eval)) post')
    (hpost : ∀ st st', pre st →
      post' ((fun s => s.allocate p (2 * (n * n) : IExp ℕ).eval (I.width p))^[8] st) st' →
      post st ((fun s => s.release p (2 * (n * n) : IExp ℕ).eval (I.width p))^[8] st')) :
    RoutineSpec m I pre (eighSplitBlock p mm qr n d lo k kp Sg Pp Pm Ma Qa Sz Kd Kp two sg nsg sq)
      fp post := by
  refine RoutineSpec.scope ((spec_allocBind_iterate 0 hb ?_).conseq (fun s hs => ⟨s, hs, rfl⟩)
    (fun x hx => by simpa using hx) fun s _ hs hp => hp s hs rfl)
  refine spec_allocBind_iterate 1 hb (spec_allocBind_iterate 2 hb (spec_allocBind_iterate 3 hb
    (spec_allocBind_iterate 4 hb (spec_allocBind_iterate 5 hb (spec_allocBind_iterate 6 hb
    (spec_allocBind_iterate 7 hb ?_))))))
  exact h.conseq (fun _ ⟨st, hst, e⟩ => e ▸ hpre st hst) (fun _ h => h)
    fun _ _ ⟨_, _, _⟩ hp st hst e => hpost st _ hst (e ▸ hp)

omit [AddMonoid C] [Inhabited K] in
/-- The buffers a split reads exist: the handles of shaped arenas, `Sg`, `Pp`, `Pm` (held) and
the buffers of the cells `two`, `sg`, `nsg`, `sq` (read) are below the size of the store. -/
theorem split_handles_lt {n lo k kp D : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k)
    {H : EighArenas} {p : P}
    {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {s : Store P K} {w₂ w₃ w₄ w₅ : K}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)} (hH : H.Shaped s p n D)
    (hPp : pairLayout.Holds s p Pp 0 Ppm) (hPm : pairLayout.Holds s p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), ∃ v, s.read p Sg w = some v)
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
    Store.lt_size_of_read_eq_some (hSg 0 hn2).choose_spec,
    Store.lt_size_of_read_eq_some (hPp ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩),
    Store.lt_size_of_read_eq_some (hPm ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩),
    Store.lt_size_of_read_eq_some htwo, Store.lt_size_of_read_eq_some hσ,
    Store.lt_size_of_read_eq_some hnσ, Store.lt_size_of_read_eq_some hsq]

omit [Inhabited K] in
/-- A deflation block at an index expression for the rank runs as at its value. -/
theorem exec_eighDeflateBlock_congr_split (p : P) (mm qr : ι) (n k r lo : IExp ℕ)
    (side : ℕ) (Sg : ℕ) (sq : Cell ℕ ℕ) (Pm G Y Qf Rf Qa : ℕ) (qo : IExp ℕ) (st : St P K C) :
    exec I (eighDeflateBlock p mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo).run st =
      exec I (eighDeflateBlock p mm qr n k (.const r.eval) lo side Sg sq Pm G Y Qf Rf Qa
        qo).run st :=
  exec_eq_of_normIdx_eq I rfl st

omit [Inhabited K] in
/-- A compression block at an index expression for the rank runs as at its value. -/
theorem exec_eighCompressBlock_congr_split (p : P) (mm : ι) (k r : IExp ℕ) (Qa : ℕ)
    (qo : IExp ℕ) (Ma : ℕ) (mo co : IExp ℕ) (two sg : Cell ℕ ℕ) (Qh C1 C2 C3 : ℕ)
    (st : St P K C) :
    exec I (eighCompressBlock p mm k r Qa qo Ma mo co two sg Qh C1 C2 C3).run st =
      exec I (eighCompressBlock p mm k (.const r.eval) Qa qo Ma mo co two sg Qh C1 C2
        C3).run st :=
  exec_eq_of_normIdx_eq I rfl st

/-- The index arithmetic of a split: the blocks of the bases and of the compressions fit their
arenas, and the compressions lie past the node's block. -/
private theorem eighSplit_bounds_split {n d lo k kp D : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k)
    (hd : d < D) :
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) ≤ 2 * (n * n) * D ∧
      2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) + 2 * (k * (k - kp)) ≤ 2 * (n * n) * D ∧
      2 * (n * n) * (d + 1) + 2 * n * (lo + kp) + 2 * ((k - kp) * (k - kp)) ≤
        2 * (n * n) * (D + 1) ∧
      2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = kp + r := ⟨k - kp, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : r * r ≤ n * r := Nat.mul_le_mul_right _ (by omega)
  have h2 : n * (lo + kp) + n * r ≤ n * n := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have h3 : n * n * (d + 1) ≤ n * n * D := Nat.mul_le_mul_left _ hd
  have h4 : n * lo + (kp + r) * (kp + r) ≤ n * n := by
    have : (kp + r) * (kp + r) ≤ n * (kp + r) := Nat.mul_le_mul_right _ (by omega)
    have : n * lo + n * (kp + r) ≤ n * n := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **The blocks a split writes** in the arenas: the bases $\mathbf{Q}_+$, $\mathbf{Q}_-$ at the
node's block of depth $d$ in `Qa`, the two compressions at the blocks of the slots $lo$ and
$lo + k_+$ of depth $d + 1$ in `Ma`, the two size cells of depth $d + 1$ and the kind and split
cells of the node. -/
def eighSplitWindow (H : EighArenas) (n d lo k kp : ℕ) : List (ℕ × ℕ × ℕ) :=
  [matBlock H.Qa (2 * (n * n) * d + 2 * n * lo) k kp 2,
    matBlock H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) k (k - kp) 2,
    matBlock H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) kp kp 2,
    matBlock H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) (k - kp) (k - kp) 2,
    (H.Sz, n * (d + 1) + lo, 1), (H.Sz, n * (d + 1) + (lo + kp), 1),
    (H.Kd, n * d + lo, 1), (H.Kp, n * d + lo, 1)]

omit [Inhabited K] [AddMonoid C] in
/-- After $m$ allocations at tag `p` the store has $m$ more buffers, the buffers below keep their
shape and cells, and the new ones have the shape of the allocation. -/
theorem iterate_allocate (st : St P K C) (p : P) (len w : ℕ) : ∀ m,
    ((·.allocate p len w)^[m] st).store.size = st.store.size + m ∧
    (∀ x < st.store.size, ((·.allocate p len w)^[m] st).store.shape[x]? = st.store.shape[x]? ∧
      ∀ q i, ((·.allocate p len w)^[m] st).store.read q x i = st.store.read q x i) ∧
    (∀ j < m, ((·.allocate p len w)^[m] st).store.shape[st.store.size + j]? = some (p, len)) ∧
    ((·.allocate p len w)^[m] st).pos = st.pos
  | 0 => ⟨rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩
  | m + 1 => by
    obtain ⟨hs, hr, hn, hp⟩ := iterate_allocate st p len w m
    rw [Function.iterate_succ_apply']
    refine ⟨by rw [St.size_allocate, hs, Nat.add_assoc], fun x hx => ⟨?_, fun q i => ?_⟩,
      fun j hj => ?_, hp⟩
    · rw [St.shape_allocate, Array.getElem?_push, if_neg (by rw [Store.size_shape]; omega),
        (hr x hx).1]
    · rw [St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega), (hr x hx).2]
    · rw [St.shape_allocate, Array.getElem?_push]
      split_ifs with h
      · rfl
      · exact hn j (by rw [Store.size_shape] at h; omega)

omit [Inhabited K] [AddMonoid C] in
/-- A store predicate reading only buffers below $b$ survives $m$ releases of a store of
$b + m$ buffers. -/
theorem ReadsOnly.iterate_release {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {b : ℕ}
    (hF : ReadsOnly F rs) (hrs : ∀ x ∈ rs, x.1 < b) (p : P) (len w : ℕ) :
    ∀ m (s : St P K C), s.store.size = b + m → F s.store →
      F ((·.release p len w)^[m] s).store ∧ ((·.release p len w)^[m] s).pos = s.pos
  | 0, _, _, h => ⟨h, rfl⟩
  | m + 1, s, hs, h => by
    rw [Function.iterate_succ_apply]
    exact ReadsOnly.iterate_release hF hrs p len w m _ (by simp [St.release, hs])
      (hF.pop h fun x hx => by have := hrs x hx; omega)

omit [Inhabited K] in
/-- A compression block composes with what follows. -/
theorem executionComposable_eighCompressBlock (p : P) (mm : ι) (k r : IExp ℕ) (Qa : ℕ)
    (qo : IExp ℕ) (Ma : ℕ) (mo co : IExp ℕ) (two sg : Cell ℕ ℕ) (Qh C1 C2 C3 : ℕ) :
    ExecutionComposable I
      (eighCompressBlock (ι := ι) p mm k r Qa qo Ma mo co two sg Qh C1 C2 C3) := by
  exec_composable

omit [Inhabited K] in
/-- A deflation block composes with what follows. -/
theorem executionComposable_eighDeflateBlock (p : P) (mm qr : ι) (n k r lo : IExp ℕ) (side : ℕ)
    (Sg : ℕ) (sq : Cell ℕ ℕ) (Pm G Y Qf Rf Qa : ℕ) (qo : IExp ℕ) :
    ExecutionComposable I (eighDeflateBlock p mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo) := by
  exec_composable

omit [Inhabited K] in
/-- The records of a split as a routine specification: the sizes $k_+$ and $k - k_+$ in their
cells of `Sz` at depth $d + 1$, the kind $4$ and $k_+$ in the node's cells of `Kd` and `Kp`. -/
theorem spec_eighSplitRecords (md : Mode) (p : P) (n d lo k : ℕ) (kpe : IExp ℕ) (H : EighArenas)
    (hkp : 0 < kpe.eval) (dSzKd : H.Sz ≠ H.Kd) (dSzKp : H.Sz ≠ H.Kp) (dKdKp : H.Kd ≠ H.Kp) :
    let cells := [(H.Sz, n * (d + 1) + lo, 1), (H.Sz, n * (d + 1) + (lo + kpe.eval), 1),
      (H.Kd, n * d + lo, 1), (H.Kp, n * d + lo, 1)]
    RoutineSpec md I (fun st => md.Needs (((∃ z, I.sem.lit p (kpe.eval : ℚ) = some z) ∧
        (∃ z, I.sem.lit p ((k - kpe.eval : ℕ) : ℚ) = some z) ∧
        ∃ z, I.sem.lit p ((4 : ℕ) : ℚ) = some z) ∧ WritableBlocks st.store p cells))
      (do
        ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
        ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
          (.const k - kpe))
        ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
        ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
          Builder P ι ℕ ℕ Unit) cells
      fun st st' => (st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p (kpe.eval : ℚ) ∧
        st'.store.read p H.Sz (n * (d + 1) + (lo + kpe.eval)) =
          I.sem.lit p ((k - kpe.eval : ℕ) : ℚ) ∧
        st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
        st'.store.read p H.Kp (n * d + lo) = I.sem.lit p (kpe.eval : ℚ)) ∧ PosKept st st' := by
  intro cells
  refine ⟨by exec_composable, fun st hN => ?_⟩
  have hW := fun s (hs : Store.shape s = st.store.shape) b o l (hx : (b, o, l) ∈ cells) =>
    (Mode.needs_and.mp hN).2.mono fun h => (h _ hx).of_shape_eq hs
  have hL := (Mode.needs_and.mp hN).1
  exact (RoutineSpec.ins spec_litIdx_read).wp_bind ((Mode.needs_and.mpr ⟨hL.mono (·.1),
    hW _ rfl _ _ _ (by simp [cells])⟩)) fun st₁ hm₁ h₁ =>
    (RoutineSpec.ins spec_litIdx_read).wp_bind ((Mode.needs_and.mpr ⟨hL.mono (·.2.1),
    hW _ hm₁.1 _ _ _ (by simp [cells])⟩)) fun st₂ hm₂ h₂ =>
    (RoutineSpec.ins spec_litIdx_read).wp_bind ((Mode.needs_and.mpr ⟨hL.mono (·.2.2),
    hW _ (hm₁.trans hm₂).1 _ _ _ (by simp [cells])⟩)) fun st₃ hm₃ h₃ =>
    (RoutineSpec.ins spec_litIdx_read).wp_run ((Mode.needs_and.mpr ⟨hL.mono (·.1),
    hW _ (hm₁.trans hm₂ |>.trans hm₃).1 _ _ _ (by simp [cells])⟩)) fun st₄ hm₄ h₄ =>
    ⟨(hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄).mono (by simp [cells, eighSlotOff]),
      ⟨(readsOnly_read _ _ _ _).of_modifies h₁.1 (hm₂.trans hm₃ |>.trans hm₄)
        (by simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
              IExp.eval_ofNat] at *;
            fp_omega [dSzKd, dSzKp, hkp]),
       (readsOnly_read _ _ _ _).of_modifies h₂.1 (hm₃.trans hm₄)
        (by simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
              IExp.eval_ofNat] at *;
            fp_omega [dSzKd, dSzKp]),
       (readsOnly_read _ _ _ _).of_modifies h₃.1 hm₄ (by
        simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
          IExp.eval_ofNat] at *;
          fp_omega [dKdKp]), h₄.1⟩,
      h₄.2.trans (h₃.2.trans (h₂.2.trans h₁.2))⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The scratch blocks of a compression at the handles $b + 4, \dots, b + 7$ lie in the first
$2n^2$ cells of those buffers. -/
theorem modifies_split_scratch {s s' : Store P K} {n k r b co Ma : ℕ} [DecidableEq P]
    (hr : r ≤ k) (hk : k ≤ n) (h : Modifies [matBlock (b + 4) 0 r k 2, matBlock (b + 5) 0 r k 2,
      matBlock (b + 6) 0 r r 2, matBlock (b + 7) 0 r r 2, matBlock Ma co r r 2] s s') :
    Modifies [matBlock Ma co r r 2, (b + 4, 0, 2 * (n * n)), (b + 5, 0, 2 * (n * n)),
      (b + 6, 0, 2 * (n * n)), (b + 7, 0, 2 * (n * n))] s s' := by
  refine h.of_sub fun x hx => ?_
  have := Nat.mul_le_mul (hr.trans hk) hk
  have := Nat.mul_le_mul (hr.trans hk) (hr.trans hk)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [⟨(b + 4, 0, 2 * (n * n)), by simp, rfl, le_rfl, by simp only [matBlock]; omega⟩,
    ⟨(b + 5, 0, 2 * (n * n)), by simp, rfl, le_rfl, by simp only [matBlock]; omega⟩,
    ⟨(b + 6, 0, 2 * (n * n)), by simp, rfl, le_rfl, by simp only [matBlock]; omega⟩,
    ⟨(b + 7, 0, 2 * (n * n)), by simp, rfl, le_rfl, by simp only [matBlock]; omega⟩,
    ⟨_, List.mem_cons_self, rfl, le_rfl, le_rfl⟩]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The footprint of a compression is writable when its scratch buffers at the handles
$b + 4, \dots, b + 7$ have $2n^2$ cells and its output block is writable. -/
theorem writableBlocks_split_compress {s : Store P K} {p : P} {n k r b co Ma : ℕ} (hr : r ≤ k)
    (hk : k ≤ n)
    (hsh : ∀ j < 4, s.shape[b + 4 + j]? = some (p, 2 * (n * n)))
    (hMa : Writable s p Ma co (r * r * 2)) :
    WritableBlocks s p [matBlock (b + 4) 0 r k 2, matBlock (b + 5) 0 r k 2,
      matBlock (b + 6) 0 r r 2, matBlock (b + 7) 0 r r 2, matBlock Ma co r r 2] := by
  have h1 := Nat.mul_le_mul (hr.trans hk) hk
  have h2 := Nat.mul_le_mul (hr.trans hk) (hr.trans hk)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [writable_of_shape_eq rfl (hsh 0 (by omega)) (by simp only [matBlock]; omega),
    writable_of_shape_eq rfl (hsh 1 (by omega)) (by simp only [matBlock]; omega),
    writable_of_shape_eq rfl (hsh 2 (by omega)) (by simp only [matBlock]; omega),
    writable_of_shape_eq rfl (hsh 3 (by omega)) (by simp only [matBlock]; omega), hMa]

/-- The tail of a split, after the two deflations, as a routine specification: the two
compressions at the blocks of the slots $lo$ and $lo + k_+$ of depth $d + 1$ in `Ma` and the
records, with the compressions' scratch at the handles $b + 4, \dots, b + 7$. -/
theorem spec_eighSplitTail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ ∀ p x, safe p x)) (p : P) (n d lo k : ℕ)
    (hk : lo + k ≤ n) (kpe : IExp ℕ) (hkp : 0 < kpe.eval) (hkpk : kpe.eval < k) (H : EighArenas)
    {two sg nsg : Cell ℕ ℕ} (c₂ σ σ' : K) (A : Matrix (Fin k) (Fin k) (K × K))
    (Qp : Matrix (Fin k) (Fin kpe.eval) (K × K)) (Qm : Matrix (Fin k) (Fin (k - kpe.eval)) (K × K))
    (b : ℕ) (dMaQa : H.Ma ≠ H.Qa) (dSzKd : H.Sz ≠ H.Kd) (dSzKp : H.Sz ≠ H.Kp)
    (dKdKp : H.Kd ≠ H.Kp) (dMa : H.Ma ≠ H.Sz ∧ H.Ma ≠ H.Kd ∧ H.Ma ≠ H.Kp)
    (dc : two.buf ≠ H.Ma ∧ sg.buf ≠ H.Ma ∧ nsg.buf ≠ H.Ma)
    (hlt : H.Qa < b ∧ H.Ma < b ∧ two.buf < b ∧ sg.buf < b ∧ nsg.buf < b) :
    RoutineSpec md I (fun st => pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A ∧
        pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
        pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kpe.eval)) Qm ∧
        st.store.read p two.buf two.idx.eval = some c₂ ∧
        st.store.read p sg.buf sg.idx.eval = some σ ∧
        st.store.read p nsg.buf nsg.idx.eval = some σ' ∧
        (∀ j < 4, st.store.shape[b + 4 + j]? = some (p, 2 * (n * n))) ∧
        md.Needs (dec p c₂ ≠ 0 ∧
          WritableBlocks st.store p ((eighSplitWindow H n d lo k kpe.eval).drop 2) ∧
          (∃ z, I.sem.lit p (kpe.eval : ℚ) = some z) ∧
          (∃ z, I.sem.lit p ((k - kpe.eval : ℕ) : ℚ) = some z) ∧
          ∃ z, I.sem.lit p ((4 : ℕ) : ℚ) = some z))
      (do
        eighCompressBlock p mm (.const k) kpe H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
          H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
          (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg (b + 4) (b + 5) (b + 6)
          (b + 7)
        eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
          (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
          (eighBlockOff (.const n) (.const d) (.const lo))
          (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg (b + 4) (b + 5)
          (b + 6) (b + 7)
        ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
        ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
          (.const k - kpe))
        ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
        ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
          Builder P ι ℕ ℕ Unit)
      ((eighSplitWindow H n d lo k kpe.eval).drop 2 ++ [(b + 4, 0, 2 * (n * n)),
        (b + 5, 0, 2 * (n * n)), (b + 6, 0, 2 * (n * n)),
        (b + 7, 0, 2 * (n * n))])
      fun st st' => (pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
          ((eighTapeMachine I p mmR qrR).hermShift ((eighTapeMachine I p mmR qrR).hermAvg
            (mmR (mmR ((eighTapeMachine I p mmR qrR).conjTransposeMat Qp) A) Qp) c₂) σ) ∧
        pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kpe.eval))
          ((eighTapeMachine I p mmR qrR).hermShift ((eighTapeMachine I p mmR qrR).hermAvg
            (mmR (mmR ((eighTapeMachine I p mmR qrR).conjTransposeMat Qm) A) Qm) c₂) σ') ∧
        st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p (kpe.eval : ℚ) ∧
        st'.store.read p H.Sz (n * (d + 1) + (lo + kpe.eval)) =
          I.sem.lit p ((k - kpe.eval : ℕ) : ℚ) ∧
        st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
        st'.store.read p H.Kp (n * d + lo) = I.sem.lit p (kpe.eval : ℚ)) ∧ PosKept st st' := by
  simp only [eighSplitWindow, List.drop_succ_cons, List.drop_zero]
  have hs0 : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem) :=
    hsem.mono fun h => h.1.mono_safe fun p x _ => h.2 p x
  obtain ⟨F1, F3, -⟩ := split_arith_node (d := d) hk hkpk; obtain ⟨lQa, lMa, ltwo, lsg, lnsg⟩ := hlt
  refine ⟨by exec_composable, fun st ⟨hA, hQp, hQm, htwo, hσ, hnσ, hsh, hN⟩ => ?_⟩
  obtain ⟨h0, hWB, hL⟩ := And.imp_right Mode.needs_and.mp (Mode.needs_and.mp hN)
  have hW := fun (s : Store P K) (hs : s.shape = st.store.shape) x
      (hx : x ∈ (eighSplitWindow H n d lo k kpe.eval).drop 2) =>
    hWB.mono fun h => (h x hx).of_shape_eq hs
  have hWC : ∀ s : Store P K, s.shape = st.store.shape → ∀ r ≤ k, ∀ co : ℕ,
      matBlock H.Ma co r r 2 ∈ (eighSplitWindow H n d lo k kpe.eval).drop 2 →
      md.Needs (WritableBlocks s p [matBlock (b + 4) 0 r k 2, matBlock (b + 5) 0 r k 2,
        matBlock (b + 6) 0 r r 2, matBlock (b + 7) 0 r r 2, matBlock H.Ma co r r 2]) :=
    fun s hs r hr co hco => (hW s hs _ hco).mono fun hMa =>
      writableBlocks_split_compress (n := n) hr (by omega) (fun j hj => by rw [hs]; exact hsh j hj)
        hMa
  have hnd : [H.Qa, H.Ma, b + 4, b + 5, b + 6, b + 7].Nodup := by fp_omega [lQa, lMa, dMaQa]
  have hc1 := (spec_eighCompressBlock (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm md hs0 p k kpe.eval (two := two) (sg := sg)
    (qo := eighBlockOff (.const n) (.const d) (.const lo))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo)) c₂ σ Qp A hnd
    (by fp_omega [ltwo, lsg]))
  have hc1' := hc1.congr (r' := eighCompressBlock p mm (.const k) kpe H.Qa
    (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
    (eighBlockOff (.const n) (.const d) (.const lo))
    (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg (b + 4) (b + 5) (b + 6) (b + 7))
    (by exec_composable) fun _ => exec_eighCompressBlock_congr_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine hc1'.wp_bind ⟨hQp, hA, htwo, hσ, ?_⟩ fun st₁ hm₁ h₁ => ?_
  · have := hWC _ rfl kpe.eval hkpk.le (2 * (n * n) * (d + 1) + 2 * n * lo)
      (by simp [eighSplitWindow])
    exact h0.elim fun h0 => this.mono (⟨h0, ·⟩)
  simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hm₁ h₁
  have hnd' : [H.Qa, H.Ma, b + 4, b + 5, b + 6, b + 7].Nodup := hnd
  have heq := fun st => exec_eighCompressBlock_congr_split (I := I) p mm (.const k)
    (.const k - kpe) H.Qa (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe))
    H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
    (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg (b + 4) (b + 5) (b + 6)
    (b + 7) st
  have hc2 := (spec_eighCompressBlock (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm md hs0 p k ((IExp.const k - kpe).eval) (two := two) (sg := nsg)
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) c₂ σ' Qm A hnd'
    (by fp_omega [ltwo, lnsg]))
  replace hc2 := hc2.congr (executionComposable_eighCompressBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) heq
  refine hc2.wp_bind ⟨?_, ?_, ?_, ?_, ?_⟩ fun st₂ hm₂ h₂ => ?_
  · exact (readsOnly_pairLayoutHolds p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kpe.eval))
      Qm).of_modifies hQm hm₁ (by
      fp_omega [lQa, dMaQa])
  · exact (readsOnly_pairLayoutHolds p H.Ma (2 * (n * n) * d + 2 * n * lo) A).of_modifies hA hm₁ (by
      fp_omega [lMa, F1])
  · exact (readsOnly_read _ _ _ _).of_modifies htwo hm₁ (by fp_omega [ltwo, dc.1])
  · exact (readsOnly_read _ _ _ _).of_modifies hnσ hm₁ (by fp_omega [lnsg, dc.2.2])
  · have := hWC _ hm₁.1 (k - kpe.eval) (by omega)
      (2 * (n * n) * (d + 1) + 2 * n * (lo + kpe.eval)) (by simp [eighSplitWindow])
    exact h0.elim fun h0 => this.mono (⟨h0, ·⟩)
  simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hm₂ h₂
  have hR := spec_eighSplitRecords (I := I) md p n d lo k kpe H hkp dSzKd dSzKp dKdKp
  refine hR.wp_run ?_ fun st₃ hm₃ h₃ => ?_
  · refine (Mode.needs_and.mpr ⟨hL, hWB⟩).mono fun ⟨hl, hw⟩ => ⟨hl, fun x hx => ?_⟩
    refine (hw x ?_).of_shape_eq (hm₂.1.trans hm₁.1)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  have hkn : k ≤ n := by omega
  have hm₁' := modifies_split_scratch (n := n) hkpk.le hkn hm₁
  have hm₂' := modifies_split_scratch (n := n) (Nat.sub_le _ _) hkn hm₂
  refine ⟨((hm₁'.trans hm₂').trans hm₃).mono fun x hx => ?_, ⟨?_, ?_, h₃.1⟩,
    h₃.2.trans (h₂.2.trans h₁.2)⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with ((h | h | h | h | h) | h | h | h | h | h) | h | h | h | h <;> subst h <;> simp
  · refine (readsOnly_pairLayoutHolds p H.Ma _ _).of_modifies (h₁.1 ⟨blockDisjoint_of_fst_ne
      (Ne.symm dc.1), blockDisjoint_of_fst_ne (Ne.symm dc.2.1)⟩) (hm₂'.trans hm₃) ?_
    fp_omega [lMa, F3, dMa.1, dMa.2.1, dMa.2.2]
  · refine (readsOnly_pairLayoutHolds p H.Ma _ _).of_modifies (h₂.1 ⟨blockDisjoint_of_fst_ne
      (Ne.symm dc.1), blockDisjoint_of_fst_ne (Ne.symm dc.2.2)⟩) hm₃ ?_
    fp_omega [dMa.1, dMa.2.1, dMa.2.2]

/-- The body of a split after its eight allocations, as a specification: the two deflations at
the scratch handles $b, \dots, b + 3$, then `NLAlib.spec_eighSplitTail`. -/
theorem spec_eighSplitBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ ∀ p x, safe p x))
    (p : P) (n d lo k : ℕ) (hk : lo + k ≤ n) (kpe : IExp ℕ) (hkp : 0 < kpe.eval)
    (hkpk : kpe.eval < k) (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    (c₂ σ σ' : K) (A Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)) (b : ℕ)
    (Qp : Matrix (Fin k) (Fin kpe.eval) (K × K)) (Qm : Matrix (Fin k) (Fin (k - kpe.eval)) (K × K))
    (hQp : Qp = deflate (eighTapeMachine I p mmR qrR) kpe.eval Ppm
      (leadingBlock k ((eighTapeSample n d lo).2 true)))
    (hQm : Qm = deflate (eighTapeMachine I p mmR qrR) (k - kpe.eval) Pmm
      (leadingBlock k ((eighTapeSample n d lo).2 false)))
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hlt : ∀ x ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf], x < b) :
    Spec md I (fun st => pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A ∧
        pairLayout.Holds st.store p Pp 0 Ppm ∧ pairLayout.Holds st.store p Pm 0 Pmm ∧
        (∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v) ∧
        (md = .liberal → ∀ w < 4 * (n * n),
          st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) ∧
        st.store.read p two.buf two.idx.eval = some c₂ ∧
        st.store.read p sg.buf sg.idx.eval = some σ ∧
        st.store.read p nsg.buf nsg.idx.eval = some σ' ∧
        st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p) ∧
        (∀ j < 8, st.store.shape[b + j]? = some (p, 2 * (n * n))) ∧
        md.Needs (dec p c₂ ≠ 0 ∧ WritableBlocks st.store p (eighSplitWindow H n d lo k kpe.eval) ∧
          (∃ z, I.sem.lit p (kpe.eval : ℚ) = some z) ∧
          (∃ z, I.sem.lit p ((k - kpe.eval : ℕ) : ℚ) = some z) ∧
          ∃ z, I.sem.lit p ((4 : ℕ) : ℚ) = some z))
      (do
        eighDeflateBlock p mm qr (.const n) (.const k) kpe (.const lo) 0 Sg sq Pp b (b + 1) (b + 2)
          (b + 3) H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
        eighDeflateBlock p mm qr (.const n) (.const k) (.const k - kpe) (.const lo) 1 Sg sq Pm b
          (b + 1) (b + 2) (b + 3) H.Qa
          (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe))
        eighCompressBlock p mm (.const k) kpe H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
          H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
          (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg (b + 4) (b + 5) (b + 6)
          (b + 7)
        eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
          (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
          (eighBlockOff (.const n) (.const d) (.const lo))
          (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg (b + 4) (b + 5)
          (b + 6) (b + 7)
        ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
        ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
          (.const k - kpe))
        ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
        ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
          Builder P ι ℕ ℕ Unit).run
      (eighSplitWindow H n d lo k kpe.eval ++ [(b, 0, 2 * (n * n)), (b + 1, 0, 2 * (n * n)),
        (b + 2, 0, 2 * (n * n)),
        (b + 3, 0, 2 * (n * n)), (b + 4, 0, 2 * (n * n)), (b + 5, 0, 2 * (n * n)),
        (b + 6, 0, 2 * (n * n)), (b + 7, 0, 2 * (n * n))])
      fun st st' => ((∀ w < 4 * (n * n),
          st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) →
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kpe.eval))
            Qm ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
            ((eighTapeMachine I p mmR qrR).hermShift ((eighTapeMachine I p mmR qrR).hermAvg
              (mmR (mmR ((eighTapeMachine I p mmR qrR).conjTransposeMat Qp) A) Qp) c₂) σ) ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kpe.eval))
            ((eighTapeMachine I p mmR qrR).hermShift ((eighTapeMachine I p mmR qrR).hermAvg
              (mmR (mmR ((eighTapeMachine I p mmR qrR).conjTransposeMat Qm) A) Qm) c₂) σ')) ∧
        (st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p (kpe.eval : ℚ) ∧
          st'.store.read p H.Sz (n * (d + 1) + (lo + kpe.eval)) =
            I.sem.lit p ((k - kpe.eval : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
          st'.store.read p H.Kp (n * d + lo) = I.sem.lit p (kpe.eval : ℚ)) ∧ PosKept st st' := by
  subst hQp hQm
  obtain ⟨dSgPp, dSgPm, dSgQa, dPpQa, dPmQa, dMaQa, dSzKd, dSzKp, dKdKp, dQaSz, dQaKd, dQaKp,
    dMaSz, dMaKd, dMaKp, sqQa, twoQa, sgQa, nsgQa, twoMa, sgMa, nsgMa⟩ :=
    split_handles_ne hbufs hcells
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  obtain ⟨lMa, -, lQa, -, lSz, lKd, lKp, -, lSg, lPp, lPm, ltwo, lsg, lnsg, lsq⟩ := hlt
  intro st ⟨hA, hPp, hPm, hSg, hT, htwo, hσ, hnσ, hsq, hsh, hN⟩
  obtain ⟨h0, hN⟩ := Mode.needs_and.mp hN
  obtain ⟨hWB, hL⟩ := Mode.needs_and.mp hN
  have hscr : ∀ s : Store P K, s.shape = st.store.shape → ∀ X ∈ [b, b + 1, b + 2, b + 3],
      ∃ len, s.shape[X]? = some (p, len) ∧ 2 * (n * n) ≤ len := fun s hs X hX => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rw [hs]
    rcases hX with rfl | rfl | rfl | rfl
    exacts [⟨_, hsh 0 (by omega), le_rfl⟩, ⟨_, hsh 1 (by omega), le_rfl⟩,
      ⟨_, hsh 2 (by omega), le_rfl⟩, ⟨_, hsh 3 (by omega), le_rfl⟩]
  have hD1 := spec_eighDeflateBlock hmm hqr md hsem p n k kpe.eval d lo hk hkpk.le hkp true
    (Sg := Sg) (Pm := Pp) (G := b) (Y := b + 1) (Qf := b + 2) (Rf := b + 3) (Qa := H.Qa) (sq := sq)
    (qo := eighBlockOff (.const n) (.const d) (.const lo)) Ppm
    (by fp_omega [lSg, lPp, lQa, (dSgPp : Sg ≠ Pp),
      (dSgQa : Sg ≠ H.Qa), (dPpQa : Pp ≠ H.Qa)]) (by fp_omega [lsq, (sqQa : sq.buf ≠ H.Qa)])
  replace hD1 := hD1.congr (executionComposable_eighDeflateBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    fun st => exec_eighDeflateBlock_congr_split p mm qr (.const n) (.const k) kpe (.const lo) 0
      Sg sq Pp b (b + 1) (b + 2) (b + 3) H.Qa _ st
  refine hD1.wp_bind ⟨hPp, hsq, hSg, hT, (Mode.needs_and.mpr ⟨Mode.needs_of (hscr _ rfl) md,
    hWB.mono fun h => h _ List.mem_cons_self⟩)⟩ fun st₁ hm₁ h₁ => ?_
  simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hm₁ h₁
  have fr₁ : ∀ x, x < b → x ≠ H.Qa → ∀ q i, st₁.store.read q x i = st.store.read q x i :=
    fun x hx hxQ q i => hm₁.2 q x i (by fp_omega [hx, hxQ])
  have hD2 := spec_eighDeflateBlock hmm hqr md hsem p n k (k - kpe.eval) d lo hk (Nat.sub_le _ _)
    (by omega) false (Sg := Sg) (Pm := Pm) (G := b) (Y := b + 1) (Qf := b + 2) (Rf := b + 3)
    (Qa := H.Qa) (sq := sq)
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) Pmm
    (by fp_omega [lSg, lPm, lQa, dSgPm, dSgQa, dPmQa]) (by fp_omega [lsq, sqQa])
  replace hD2 := hD2.congr (executionComposable_eighDeflateBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    fun st => exec_eighDeflateBlock_congr_split p mm qr (.const n) (.const k) (.const k - kpe)
      (.const lo) 1 Sg sq Pm b (b + 1) (b + 2) (b + 3) H.Qa _ st
  refine hD2.wp_bind ⟨fun i j t => (fr₁ _ lPm dPmQa _ _).trans (hPm i j t),
    (fr₁ _ lsq sqQa _ _).trans hsq, fun w hw => (fr₁ _ lSg dSgQa p w).symm ▸ hSg w hw,
    fun h w hw => (fr₁ _ lSg dSgQa p w).trans (hT h w hw),
    (Mode.needs_and.mpr ⟨Mode.needs_of (hscr _ hm₁.1) md, hWB.mono fun h =>
      (h _ (List.mem_cons_of_mem _ List.mem_cons_self)).of_shape_eq hm₁.1⟩)⟩
    fun st₂ hm₂ h₂ => ?_
  simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hm₂ h₂
  have fr₂ : ∀ x, x < b → x ≠ H.Qa → ∀ q i, st₂.store.read q x i = st.store.read q x i :=
    fun x hx hxQ q i => (hm₂.2 q x i (by fp_omega [hx, hxQ])).trans (fr₁ x hx hxQ q i)
  obtain ⟨⟨Q₁, hQ₁, eQ₁⟩, hp₁⟩ := h₁
  obtain ⟨⟨Q₂, hQ₂, eQ₂⟩, hp₂⟩ := h₂
  have hQ₁' := (readsOnly_pairLayoutHolds p H.Qa (2 * (n * n) * d + 2 * n * lo) Q₁).of_modifies
    hQ₁ hm₂ (by fp_omega [lQa])
  refine (spec_eighSplitTail (qrR := qrR) hmm md hsem p n d lo k hk kpe hkp hkpk H c₂ σ σ' A Q₁ Q₂ b
    (dMaQa : H.Ma ≠ H.Qa) dSzKd dSzKp dKdKp ⟨dMaSz, dMaKd, dMaKp⟩ ⟨twoMa, sgMa, nsgMa⟩
    ⟨lQa, lMa, ltwo, lsg, lnsg⟩).wp_run ⟨fun i j t => (fr₂ _ lMa dMaQa _ _).trans (hA i j t), hQ₁',
      hQ₂, (fr₂ _ ltwo twoQa _ _).trans htwo, (fr₂ _ lsg sgQa _ _).trans hσ,
      (fr₂ _ lnsg nsgQa _ _).trans hnσ, fun j hj => by
        rw [(hm₁.trans hm₂).1, Nat.add_assoc]; exact hsh (4 + j) (by omega),
      ?_⟩ fun st₃ hm₃ h₃ => ?_
  · refine (Mode.needs_and.mpr ⟨h0, Mode.needs_and.mpr ⟨hWB, hL⟩⟩).mono
      fun ⟨h0, hw, hl⟩ => ⟨h0, fun x hx => (hw x (List.mem_of_mem_drop hx)).of_shape_eq
        (hm₁.trans hm₂).1, hl⟩
  simp only [eighSplitWindow, List.drop_succ_cons, List.drop_zero] at hm₃
  refine ⟨((hm₁.trans hm₂).trans hm₃).mono fun x hx => ?_, fun hT' => ?_, h₃.1.2.2,
    h₃.2.trans (hp₂.trans hp₁)⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((h | h | h | h | h) | h | h | h | h | h) | (h | h | h | h | h | h) | h | h | h |
      h
      <;> subst h <;> simp [eighSplitWindow]
  have hT₁ : ∀ w < 4 * (n * n),
      st₁.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)) :=
    fun w hw => (fr₁ _ lSg dSgQa p w).trans (hT' w hw)
  rw [eQ₁ hT'] at hQ₁' h₃
  rw [eQ₂ hT₁] at hQ₂ h₃
  exact ⟨(readsOnly_pairLayoutHolds p H.Qa _ _).of_modifies hQ₁' hm₃
      (by fp_omega [lQa, dMaQa, dQaSz, dQaKd, dQaKp]),
    (readsOnly_pairLayoutHolds p H.Qa _ _).of_modifies hQ₂ hm₃
      (by fp_omega [lQa, dMaQa, dQaSz, dQaKd, dQaKp]), h₃.1.1, h₃.1.2.1⟩
/-- **A split as a routine specification**: if the kernels of `I` are the routines `mmR`, `qrR`
on interleaved pairs, then from a store of $b$ buffers holding the node matrix $\mathbf{A}$ at its
block of `Ma`, the projectors at offset $0$ of `Pp`, `Pm`, initialised Gaussian words in `Sg` and
the values $c_2$, $\sigma$, $\sigma'$ and the stored $\sqrt{1/2}$ in the cells `two`, `sg`, `nsg`,
`sq` (all below $b$, as `NLAlib.holds_of_exec_eighSplitBlock` assumes), the run of
`NLAlib.eighSplitBlock` with $0 < k_+ < k$ modifies only the blocks of
`NLAlib.eighSplitWindow`, writes the sizes, the kind and $k_+$, and keeps the tape positions; if
the Gaussian words are the tape's of depth $d$ (which the liberal mode assumes), it writes the
bases and compressions of `NLAlib.holds_of_exec_eighSplitBlock`. In mode `total` the run also
succeeds, given the standard model on every value, $c_2$ decoding to a nonzero value, the window
writable and the literals of the records defined. No printed source. -/
theorem spec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ ∀ p x, safe p x))
    (p : P) (n d lo k : ℕ) (hk : lo + k ≤ n) (kpe : IExp ℕ) (hkp : 0 < kpe.eval)
    (hkpk : kpe.eval < k) (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    (c₂ σ σ' : K) (A Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)) (b : ℕ)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hlt : ∀ x ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf], x < b) :
    RoutineSpec md I (fun st => st.store.size = b ∧
        pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A ∧
        pairLayout.Holds st.store p Pp 0 Ppm ∧ pairLayout.Holds st.store p Pm 0 Pmm ∧
        (∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v) ∧
        (md = .liberal → ∀ w < 4 * (n * n),
          st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) ∧
        st.store.read p two.buf two.idx.eval = some c₂ ∧
        st.store.read p sg.buf sg.idx.eval = some σ ∧
        st.store.read p nsg.buf nsg.idx.eval = some σ' ∧
        st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p) ∧
        md.Needs (dec p c₂ ≠ 0 ∧ WritableBlocks st.store p (eighSplitWindow H n d lo k kpe.eval) ∧
          (∃ z, I.sem.lit p (kpe.eval : ℚ) = some z) ∧
          (∃ z, I.sem.lit p ((k - kpe.eval : ℕ) : ℚ) = some z) ∧
          ∃ z, I.sem.lit p ((4 : ℕ) : ℚ) = some z))
      (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) kpe Sg Pp Pm H.Ma H.Qa
        H.Sz H.Kd H.Kp two sg nsg sq) (eighSplitWindow H n d lo k kpe.eval)
      fun st st' =>
        let M := eighTapeMachine I p mmR qrR
        let Qp := deflate M kpe.eval Ppm (leadingBlock k ((eighTapeSample n d lo).2 true))
        let Qm := deflate M (k - kpe.eval) Pmm (leadingBlock k ((eighTapeSample n d lo).2 false))
        ((∀ w < 4 * (n * n),
          st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) →
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kpe.eval))
            Qm ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
            (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) c₂) σ) ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kpe.eval))
            (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) c₂) σ')) ∧
        (st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p (kpe.eval : ℚ) ∧
          st'.store.read p H.Sz (n * (d + 1) + (lo + kpe.eval)) =
            I.sem.lit p ((k - kpe.eval : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
          st'.store.read p H.Kp (n * d + lo) = I.sem.lit p (kpe.eval : ℚ)) ∧ PosKept st st' := by
  have hl := hlt
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
  obtain ⟨lMa, -, lQa, -, lSz, lKd, lKp, -, lSg, lPp, lPm, ltwo, lsg, lnsg, lsq⟩ := hl
  refine spec_eighSplitBlock_of_body p mm qr _ _ _ _ kpe Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg
    nsg sq (fun _ h => h.1) (fun st hpre => ?_)
    (Spec.with_modifies (spec_eighSplitBody hmm hqr md hsem p n d lo k hk kpe hkp hkpk H c₂ σ σ' A
      Ppm Pmm b _ _ rfl rfl hbufs hcells hlt)) fun st st' hpre hpost => ?_
  · obtain ⟨hsz, hA, hPp, hPm, hSg, hT, htwo, hσ, hnσ, hsq, hN⟩ := hpre
    obtain ⟨-, hbl, hnew, -⟩ :=
      iterate_allocate st p (2 * (IExp.const n * IExp.const n)).eval (I.width p) 8
    have hrd := fun x (hx : x < b) => (hbl x (hsz ▸ hx)).2 p
    refine ⟨fun i j t => (hrd _ lMa _).trans (hA i j t), fun i j t => (hrd _ lPp _).trans
      (hPp i j t), fun i j t => (hrd _ lPm _).trans (hPm i j t), fun w hw => hrd _ lSg w ▸ hSg w hw,
      fun h w hw => (hrd _ lSg w).trans (hT h w hw), (hrd _ ltwo _).trans htwo,
      (hrd _ lsg _).trans hσ, (hrd _ lnsg _).trans hnσ, (hrd _ lsq _).trans hsq,
      fun j hj => hsz ▸ hnew j hj, hN.mono fun ⟨h0, hw, hl⟩ => ⟨h0, fun x hx => ?_, hl⟩⟩
    have hx1 : x.1 < b := by
      simp only [eighSplitWindow, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    exact (hw x hx).of_getElem?_shape_eq (hbl x.1 (hsz ▸ hx1)).1
  · obtain ⟨hsz, -⟩ := hpre
    obtain ⟨hm, hv, hr, hp⟩ := hpost
    obtain ⟨hs8, hbl, -, hp8⟩ :=
      iterate_allocate st p (2 * (IExp.const n * IExp.const n)).eval (I.width p) 8
    have hsz' : st'.store.size = b + 8 := by
      rw [← Store.size_eq_of_shape_eq hm.1.symm, hs8, hsz]
    have hR := fun {F : Store P K → Prop} {rs} (hF : ReadsOnly F rs) (hrs : ∀ x ∈ rs, x.1 < b) =>
      ReadsOnly.iterate_release hF hrs p (2 * (IExp.const n * IExp.const n)).eval (I.width p) 8
        st' hsz'
    refine ⟨fun hT => ?_, ⟨(hR (readsOnly_read _ _ _ _) (by simpa using lSz) hr.1).1,
      (hR (readsOnly_read _ _ _ _) (by simpa using lSz) hr.2.1).1,
      (hR (readsOnly_read _ _ _ _) (by simpa using lKd) hr.2.2.1).1,
      (hR (readsOnly_read _ _ _ _) (by simpa using lKp) hr.2.2.2).1⟩,
      ((hR (readsOnly_read p H.Kp _ _) (by simpa using lKp) hr.2.2.2).2.trans hp).trans hp8⟩
    obtain ⟨v1, v2, v3, v4⟩ := hv fun w hw => ((hbl Sg (hsz ▸ lSg)).2 p w).trans (hT w hw)
    exact ⟨(hR (readsOnly_pairLayoutHolds _ _ _ _) (by simpa [matBlock] using lQa) v1).1,
      (hR (readsOnly_pairLayoutHolds _ _ _ _) (by simpa [matBlock] using lQa) v2).1,
      (hR (readsOnly_pairLayoutHolds _ _ _ _) (by simpa [matBlock] using lMa) v3).1,
      (hR (readsOnly_pairLayoutHolds _ _ _ _) (by simpa [matBlock] using lMa) v4).1⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The window of a split is writable in arenas of depth $D > d$. -/
theorem writableBlocks_eighSplitWindow {H : EighArenas} {s : Store P K} {p : P}
    {n d lo k kp D : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k) (hd : d < D) (hH : H.Shaped s p n D) :
    WritableBlocks s p (eighSplitWindow H n d lo k kp) := by
  obtain ⟨-, hMa, -, hQa, -, hSz, hKd, hKp, -⟩ := hH
  obtain ⟨B1, B2, B3, -⟩ := eighSplit_bounds_split hk hkpk hd
  obtain ⟨-, F3, -, -, -, -⟩ := split_arith_node (d := d) hk hkpk
  have h1 := Nat.mul_le_mul_left n (show d + 2 ≤ D + 1 by omega)
  have h2 := Nat.mul_le_mul_left n (show d + 1 ≤ D by omega)
  simp only [WritableBlocks, eighSplitWindow, List.forall_mem_cons]
  exact ⟨writable_of_shape_eq rfl hQa (by fp_omega [B1]),
    writable_of_shape_eq rfl hQa (by fp_omega [B2]),
    writable_of_shape_eq rfl hMa (by fp_omega [B3, F3]),
    writable_of_shape_eq rfl hMa (by fp_omega [B3]),
    writable_of_shape_eq rfl hSz (by fp_omega [h1, hk, hkpk]),
    writable_of_shape_eq rfl hSz (by fp_omega [h1, hk, hkpk]),
    writable_of_shape_eq rfl hKd (by fp_omega [h2, hk, hkpk]),
    writable_of_shape_eq rfl hKp (by fp_omega [h2, hk, hkpk]),
    fun x hx => absurd hx List.not_mem_nil⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell outside a split's node window is disjoint from every block of the split's window
(`NLAlib.eighSplitWindow`). -/
theorem blockDisjoint_eighSplitWindow {H : EighArenas} {n d lo k kp b i : ℕ} (hk : lo + k ≤ n)
    (hkpk : kp < k) (hW : ¬ EighNodeWindow H n d lo k (lo + kp) b i) :
    ∀ x ∈ eighSplitWindow H n d lo k kp, blockDisjoint (b, i, 1) x = true := by
  obtain ⟨-, -, -, F6, F7, -⟩ := split_arith_node (d := d) hk hkpk
  obtain ⟨-, F3, F4, -, -, F2⟩ := split_arith_node (d := d) hk hkpk
  have hkn : k * k ≤ n * k := Nat.mul_le_mul_right k (by omega)
  simp only [EighNodeWindow, not_or, not_and, not_lt] at hW
  obtain ⟨hWQ, hWM, hWS, hWK⟩ := hW
  simp only [eighSplitWindow, List.forall_mem_cons, matBlock, blockDisjoint_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => absurd hx List.not_mem_nil⟩
  · by_cases hb : b = H.Qa
    · have := hWQ hb; omega
    · exact Or.inl hb
  · by_cases hb : b = H.Qa
    · have := hWQ hb; omega
    · exact Or.inl hb
  · by_cases hb : b = H.Ma
    · have := hWM hb; omega
    · exact Or.inl hb
  · by_cases hb : b = H.Ma
    · have := hWM hb; omega
    · exact Or.inl hb
  · by_cases hb : b = H.Sz
    · have := hWS hb; omega
    · exact Or.inl hb
  · by_cases hb : b = H.Sz
    · have := hWS hb; omega
    · exact Or.inl hb
  · by_cases hb : b = H.Kd
    · have := hWK (Or.inl hb); omega
    · exact Or.inl hb
  · by_cases hb : b = H.Kp
    · have := hWK (Or.inr hb); omega
    · exact Or.inl hb

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
  subst hkpe
  obtain ⟨hm, hv, hr, hp⟩ := (spec_eighSplitBlock (u := fun _ => 0) (dec := fun _ _ => 0)
    (safe := fun _ _ => True) hmm hqr .liberal trivial p n d lo k hk kpe hkp hkpk H _ σ _ A Ppm Pmm
    st.store.size hbufs hcells
    (split_handles_lt hk hkpk hH hPp hPm (fun w hw => ⟨_, hSg w hw⟩) htwo hσ hnσ
      hsq)).spec.holds_of_exec
      ⟨rfl, hA, hPp, hPm, fun w hw => ⟨_, hSg w hw⟩, fun _ => hSg, htwo, hσ, hnσ, hsq, trivial⟩ h
  exact ⟨⟨(hv hSg).1, (hv hSg).2.1, (hv hSg).2.2.1, (hv hSg).2.2.2, hr⟩,
    fun q b i hW => hm.2 q b i (blockDisjoint_eighSplitWindow hk hkpk hW), hm.1, hp⟩

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

/-- A split succeeds, with the Gaussian words only initialised. -/
theorem exists_exec_eighSplitBlock_ex {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp ℕ)
    (hkpe : kpe.eval = kp)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) kpe
      Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st' := by
  subst hkpe
  obtain ⟨z2, hz2, hdz2⟩ := hlit p 2 le_rfl
  have hlt := split_handles_lt hk hkpk hH hPp hPm hSg (htwo.trans hz2) hσ hnσ hsq
  have hW := writableBlocks_eighSplitWindow (p := p) (s := st.store) hk hkpk hd hH
  exact ((spec_eighSplitBlock (safe := fun _ _ => True) hmm hqr .total ⟨hsem, fun _ _ => trivial⟩
    p n d lo k hk kpe hkp hkpk H z2 σ _ A Ppm Pmm st.store.size hbufs hcells hlt).spec.exists_exec
    ⟨rfl, hA, hPp, hPm, hSg, (by intro h; cases h), htwo.trans hz2, hσ, hnσ, hsq,
      (by rw [hdz2]; norm_num), hW, hsem.lit_ok p _ trivial, hsem.lit_ok p _ trivial,
      hsem.lit_ok p _ trivial⟩).imp fun _ h => h.1

/-- A split succeeds under the standard model at $u$ with every value in range, with an exact
literal $2$, if the kernels are routines on pairs and the arenas are allocated
(hypotheses on the inputs as `NLAlib.holds_of_exec_eighSplitBlock`). No printed source.
(The stored $\sqrt{1/2}$ is read from the cell `sq`, which `NLAlib.eighProg` fills once; design
note §8, the hoist of $\sqrt{1/2}$.) -/
theorem exists_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp)
      Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st' := by
  exact exists_exec_eighSplitBlock_ex hmm hqr hsem hlit p n d lo k kp hk hkp hkpk (.const kp)
      rfl H
    hd hH hbufs
    hA hPp hPm (fun w hw => ⟨_, hSg w hw⟩) htwo hσ hnσ hcells hsq

end NLAlib
