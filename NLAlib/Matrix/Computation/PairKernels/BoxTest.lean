/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PairKernels

/-!
# Complex-pair kernels: the max-modulus test

The rounded specification of `NLAlib.Computation.zboxTest`, the stopping test of the Newton–Schulz
iteration: a successful run writes in the flag cell whether every entry of the block lies in the box
$[lo, hi]$ of the machine, and the run succeeds when its comparisons do.

## Main results

* `NLAlib.Computation.read_of_exec_zboxTest`: what a successful run computes.
* `NLAlib.Computation.exists_exec_zboxTest`: when the run succeeds.
* `NLAlib.Computation.spec_zboxTest`: the test as a routine specification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The max-modulus test -/

private theorem zboxTest_lit {p : P} {f : Cell ℕ ℕ} {s s₂ st : St P K C} {q : ℚ}
    (hsh : s.store.shape = st.store.shape) (hpos : s.pos = st.pos)
    (hfr : ∀ q b i, (b ≠ f.buf ∨ i ≠ f.idx.eval) → s.store.read q b i = st.store.read q b i)
    (hex : exec I (.seq (.instr (.lit p f q)) .skip) s = some s₂) :
    s₂.store.shape = st.store.shape ∧ s₂.pos = st.pos ∧
      (∀ q b i, (b ≠ f.buf ∨ i ≠ f.idx.eval) → s₂.store.read q b i = st.store.read q b i) ∧
      s₂.store.read p f.buf f.idx.eval = some ((I.sem.lit p q).getD default) := by
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  exact ⟨(Store.shape_of_write_eq_some hw').trans hsh, hpos,
    fun q b i hb => (Store.read_of_write_eq_some_of_ne hw' hb).trans (hfr q b i hb),
    by rw [Store.read_of_write_eq_some hw', hv, Option.getD_some]⟩

omit [Inhabited K] in
private theorem zboxTest_forall_iff {p : P} {m n X off : ℕ} {s : Store P K}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds s p X off A) (le : K → K → Bool)
    (ℓ h : K) :
    (∀ k < 2 * (m * n), ∀ x, s.read p X (off + k) = some x → le ℓ x = true ∧ le x h = true) ↔
      ((List.finRange m).all fun i => (List.finRange n).all fun j =>
        le ℓ (A i j).1 && le (A i j).1 h && le ℓ (A i j).2 && le (A i j).2 h) = true := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true]
  constructor
  · intro hT i j
    have hj := Nat.mul_le_mul_left m (show j.1 + 1 ≤ n from j.2)
    rw [Nat.mul_succ] at hj
    have h1 := hT (2 * (i.1 + m * j.1) + 0) (by omega) _ (hA i j ⟨0, Nat.two_pos⟩)
    have h2 := hT (2 * (i.1 + m * j.1) + 1) (by omega) _ (hA i j ⟨1, Nat.one_lt_two⟩)
    exact ⟨⟨⟨h1.1, h1.2⟩, h2.1⟩, h2.2⟩
  · intro hall k hk x hx
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
    set i₀ : Fin m := ⟨k / 2 % m, Nat.mod_lt _ hm⟩
    set j₀ : Fin n := ⟨k / 2 / m, Nat.div_lt_of_lt_mul (by omega)⟩
    have e : 2 * (i₀.1 + m * j₀.1) + k % 2 = k := by
      change 2 * (k / 2 % m + m * (k / 2 / m)) + k % 2 = k
      rw [Nat.mod_add_div]; omega
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hall i₀ j₀
    obtain ⟨t, ht⟩ : ∃ t : Fin pairLayout.width,
        s.read p X (off + k) = some (pairLayout.put (A i₀ j₀) t) :=
      ⟨_, e ▸ hA i₀ j₀ ⟨_, Nat.mod_lt _ two_pos⟩⟩
    rw [hx, Option.some_inj] at ht
    subst ht
    obtain ⟨t, htl⟩ := t
    change t < 2 at htl
    rcases t with _ | _ | t
    exacts [⟨a1, a2⟩, ⟨a3, a4⟩, by omega]

private theorem zboxTest_cell_ne {b i c k len t k' : ℕ}
    (h : blockDisjoint (b, i, 1) (c, k, len) = true) (ht : t < len) (he : k' = k + t) :
    c ≠ b ∨ k' ≠ i := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  by_cases hb : c = b
  · exact Or.inr (by omega)
  · exact Or.inl hb

/-- `zboxTest` computes the machine's test: a successful run of
`NLAlib.Computation.zboxTest` from a state whose block at `X` holds the complex $m \times n$
matrix $\mathbf{A}$ and whose cells `lo`, `hi` hold $\ell$, $h$, with the flag cell outside the
block and distinct from `lo` and `hi`, ends with the flag holding the machine's zero if every
part $t$ of every entry has $\ell \le t$ and $t \le h$ by the machine's comparisons, and the
machine's one otherwise, every other cell unchanged, the same store shape and the same tape
positions. No printed source. -/
theorem read_of_exec_zboxTest (p : P) (m n : ℕ) {X : ℕ} {xo : IExp ℕ} {lo hi f : Cell ℕ ℕ}
    {ℓ h : K} {st st' : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hlo : st.store.read p lo.buf lo.idx.eval = some ℓ)
    (hhi : st.store.read p hi.buf hi.idx.eval = some h)
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (X, xo.eval, 2 * (m * n)) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true)
    (hrun : exec I (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    st'.store.read p f.buf f.idx.eval = some
      (if (List.finRange m).all (fun i => (List.finRange n).all fun j =>
          M.le ℓ (A i j).1 && M.le (A i j).1 h && M.le ℓ (A i j).2 && M.le (A i j).2 h) then
        M.zero else M.one) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (f.buf, f.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M
  classical
  have hprog : (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run = .seq (.named
      "zboxTest" [.idx (.const m), .idx (.const n), .buf X, .idx xo, .cell lo, .cell hi, .cell f]
      (.seq (.instr (.lit p f 0)) (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.ite p .le lo ⟨X, xo + .var w⟩
          (.seq (.ite p .le ⟨X, xo + .var w⟩ hi .skip (.seq (.instr (.lit p f 1)) .skip)) .skip)
          (.seq (.instr (.lit p f 1)) .skip)) .skip) .skip))) .skip := rfl
  rw [hprog, exec_seq_skip, exec_named, exec_seq, ← exec_seq_skip I (.instr _),
    Option.bind_eq_some_iff] at hrun
  obtain ⟨s₀, h₀, hrun⟩ := hrun
  rw [exec_seq_skip] at hrun
  let T : ℕ → Prop := fun w => ∀ k < w, ∀ x, st.store.read p X (xo.eval + k) = some x →
    M.le ℓ x = true ∧ M.le x h = true
  have key := zboxTest_forall_iff (p := p) hA M.le ℓ h
  obtain ⟨sh₀, pos₀, fr₀, fl₀⟩ := zboxTest_lit rfl rfl (fun _ _ _ _ => rfl) h₀
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I
    (fun w s => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ q b i, (b ≠ f.buf ∨ i ≠ f.idx.eval) → s.store.read q b i = st.store.read q b i) ∧
      s.store.read p f.buf f.idx.eval = some (if T w then M.zero else M.one))
    ⟨sh₀, pos₀, fr₀, fl₀.trans (by rw [if_pos (fun k hk => absurd hk (Nat.not_lt_zero _))]; rfl)⟩
    ?_ hrun)
  · obtain ⟨hsh, hpos, hfr, hfl⟩ := hR
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hfl
    exact ⟨hfl.trans (congrArg some (if_congr key rfl rfl)), fun q b i hb => hfr q b i
      ((zboxTest_cell_ne (k' := f.idx.eval) hb Nat.one_pos rfl).imp Ne.symm Ne.symm), hsh, hpos⟩
  rintro w hw s₁ s₂ ⟨hsh, hpos, hfr, hfl⟩ hex
  rw [exec_seq_skip, exec_ite] at hex
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨a, ha, x, hx, r, hr, rfl⟩, hex⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    at hx hw
  have hxst : st.store.read p X (xo.eval + w) = some x :=
    (hfr _ _ _ (zboxTest_cell_ne hfX hw rfl)).symm.trans hx
  rw [hfr _ _ _ (zboxTest_cell_ne (k' := lo.idx.eval) hflo Nat.one_pos rfl), hlo,
    Option.some_inj] at ha
  subst ha
  have hr' : M.le ℓ x = r := by simp only [M, ScalarSem.toFloatMachine, hr, Option.getD_some]
  cases r
  · simp only [Bool.false_eq_true, if_false] at hex
    obtain ⟨sh, ps, fr, fl⟩ := zboxTest_lit (by exact hsh) (by exact hpos) (by exact hfr) hex
    refine ⟨sh, ps, fr, fl.trans ?_⟩
    rw [if_neg fun hT => absurd ((hT w (by omega) x hxst).1.symm.trans hr') (by simp)]
    rfl
  simp only [if_true] at hex
  rw [exec_seq_skip, exec_ite] at hex
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨b, hb, c, hc, r, hr₂, rfl⟩, hex⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var] at hb
  rw [hx, Option.some_inj] at hb
  subst hb
  rw [hfr _ _ _ (zboxTest_cell_ne (k' := hi.idx.eval) hfhi Nat.one_pos rfl), hhi,
    Option.some_inj] at hc
  subst hc
  have hr₂' : M.le x h = r := by simp only [M, ScalarSem.toFloatMachine, hr₂, Option.getD_some]
  cases r
  · simp only [Bool.false_eq_true, if_false] at hex
    obtain ⟨sh, ps, fr, fl⟩ := zboxTest_lit (by exact hsh) (by exact hpos) (by exact hfr) hex
    refine ⟨sh, ps, fr, fl.trans ?_⟩
    rw [if_neg fun hT => absurd ((hT w (by omega) x hxst).2.symm.trans hr₂') (by simp)]
    rfl
  simp only [if_true, exec_skip, Option.some_inj] at hex
  subst hex
  refine ⟨hsh, hpos, hfr, hfl.trans (congrArg some (if_congr ?_ rfl rfl))⟩
  refine ⟨fun hT k hk y hy => ?_, fun hT k hk => hT k (by omega)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
  · exact hT k hk y hy
  · rw [hxst, Option.some_inj] at hy
    subst hy
    exact ⟨hr', hr₂'⟩

/-- `zboxTest` succeeds under the standard model with every value in range, when the flag cell
can be written. No printed source. -/
theorem exists_exec_zboxTest (p : P) (m n : ℕ) {X : ℕ} {xo : IExp ℕ} {lo hi f : Cell ℕ ℕ}
    {ℓ h : K} {st : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hlo : st.store.read p lo.buf lo.idx.eval = some ℓ)
    (hhi : st.store.read p hi.buf hi.idx.eval = some h)
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (X, xo.eval, 2 * (m * n)) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hf : ∃ s, st.store.write p f.buf f.idx.eval default = some s) :
    ∃ st', exec I (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run st = some st' := by
  obtain ⟨s₀, hs₀⟩ := hf
  obtain ⟨z₀, hz₀⟩ := hsem.lit_ok p 0 trivial
  obtain ⟨z₁, hz₁⟩ := hsem.lit_ok p 1 trivial
  have hX : ∀ k < 2 * (m * n), ∃ v, st.store.read p X (xo.eval + k) = some v := by
    intro k hk
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
    have e : 2 * (k / 2 % m + m * (k / 2 / m)) + k % 2 = k := by rw [Nat.mod_add_div]; omega
    exact ⟨_, e ▸ hA ⟨_, Nat.mod_lt _ hm⟩ ⟨_, Nat.div_lt_of_lt_mul (by omega)⟩
      ⟨_, Nat.mod_lt _ two_pos⟩⟩
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hfX hflo hfhi
  let R : St P K C → Prop := fun s => s.store.shape = st.store.shape ∧
    (∀ k < 2 * (m * n), s.store.read p X (xo.eval + k) = st.store.read p X (xo.eval + k)) ∧
    s.store.read p lo.buf lo.idx.eval = some ℓ ∧ s.store.read p hi.buf hi.idx.eval = some h
  have hR : ∀ (s : St P K C) (q : ℚ) (z : K), R s → I.sem.lit p q = some z →
      ∃ s', exec I (.seq (.instr (.lit p f q)) .skip) s = some s' ∧ R s' := by
    rintro s q z ⟨hsh, hsX, hslo, hshi⟩ hz
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_shape_eq hsh hs₀ z
    refine ⟨_, (exec_seq_instr_lit I hz hs').trans (exec_skip I _),
      (Store.shape_of_write_eq_some hs').trans hsh, fun k hk => ?_, ?_, ?_⟩
    · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans (hsX k hk)
      by_cases hb : X = f.buf
      · exact Or.inr (by omega)
      · exact Or.inl hb
    · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans hslo
      by_cases hb : lo.buf = f.buf
      · exact Or.inr (by omega)
      · exact Or.inl hb
    · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans hshi
      by_cases hb : hi.buf = f.buf
      · exact Or.inr (by omega)
      · exact Or.inl hb
  have hrun : (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run = .seq (.named
      "zboxTest" [.idx (.const m), .idx (.const n), .buf X, .idx xo, .cell lo, .cell hi, .cell f]
      (.seq (.instr (.lit p f 0)) (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.ite p .le lo ⟨X, xo + .var w⟩
          (.seq (.ite p .le ⟨X, xo + .var w⟩ hi .skip (.seq (.instr (.lit p f 1)) .skip)) .skip)
          (.seq (.instr (.lit p f 1)) .skip)) .skip) .skip))) .skip := rfl
  obtain ⟨s₁, h₁, hR₁⟩ := hR st 0 z₀ ⟨rfl, fun _ _ => rfl, hlo, hhi⟩ (by exact_mod_cast hz₀)
  rw [hrun, exec_seq_skip, exec_named, exec_seq, ← exec_seq_skip, h₁, Option.bind_some,
    exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I (fun _ s => R s) hR₁ ?_).imp fun _ h => h.1
  rintro w hw s hs
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  obtain ⟨v, hv⟩ := hX w hw
  have hxv : s.store.read p X (xo.eval + w) = some v := (hs.2.1 w hw).trans hv
  rw [exec_seq_skip, exec_ite]
  simp only [cmpStep, hs.2.2.1, IExp.eval_add, IExp.eval_var, hxv, hsem.cmp_le,
    Option.bind_some, Option.map_some]
  split_ifs
  · rw [exec_seq_skip, exec_ite]
    simp only [cmpStep, hs.2.2.2, IExp.eval_add, IExp.eval_var, hxv, hsem.cmp_le,
      Option.bind_some, Option.map_some]
    split_ifs
    · exact ⟨_, exec_skip I _, hs⟩
    · exact hR _ 1 z₁ hs (by exact_mod_cast hz₁)
  · exact hR _ 1 z₁ hs (by exact_mod_cast hz₁)

/-- **The max-modulus test as a routine specification**: from a state holding the $m \times n$
matrix $\mathbf{A}$ at `xo` of `X` and the values $\ell$, $h$ in the cells `lo`, `hi`, with the
flag cell outside the block and distinct from `lo` and `hi`, the run of
`NLAlib.Computation.zboxTest` modifies only the flag cell, which then holds the machine's zero if
every part of every entry lies in $[\ell, h]$ by the machine's comparisons and its one
otherwise, and keeps the tape positions; in mode `total` it also succeeds, given the standard
model and the flag cell writable. No printed source. -/
theorem spec_zboxTest (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (m n : ℕ) {X : ℕ}
    {xo : IExp ℕ} {lo hi f : Cell ℕ ℕ} (ℓ h : K) (A : Matrix (Fin m) (Fin n) (K × K))
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (matBlock X xo.eval m n 2) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    RoutineSpec md I (fun st => pairLayout.Holds st.store p X xo.eval A ∧
        st.store.read p lo.buf lo.idx.eval = some ℓ ∧ st.store.read p hi.buf hi.idx.eval = some h ∧
        md.Needs (Writable st.store p f.buf f.idx.eval 1))
      (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f) [(f.buf, f.idx.eval, 1)]
      fun st st' => st'.store.read p f.buf f.idx.eval = some
          (if (List.finRange m).all (fun i => (List.finRange n).all fun j =>
            M.le ℓ (A i j).1 && M.le (A i j).1 h && M.le ℓ (A i j).2 && M.le (A i j).2 h) then
          M.zero else M.one) ∧ PosKept st st' := by
  intro M
  have e : m * n * 2 = 2 * (m * n) := by ring
  simp only [matBlock, e] at hfX
  refine ⟨executionComposable_named _ _ _, Triple.of_exec (fun st ⟨hA, hl, hh, hW⟩ =>
    (Mode.needs_and.mpr ⟨hsem, hW⟩).mono fun ⟨hsem, hW⟩ => ?_) fun st st' ⟨hA, hl, hh, _⟩ hr => ?_⟩
  · obtain ⟨len, hlen, hi⟩ := hW 0 Nat.one_pos
    exact exists_exec_zboxTest p m n hA hl hh hfX hflo hfhi hsem
      (Store.exists_write_eq_some_of_getElem?_shape default hlen (by omega))
  · obtain ⟨hf, hfr, hsh, hpos⟩ := read_of_exec_zboxTest (toNat := toNat) (mmR := mmR)
      (qrR := qrR) (unif := unif) (normal := normal) p m n hA hl hh hfX hflo hfhi hr
    exact ⟨⟨hsh, fun q b i hb => hfr q b i (hb _ List.mem_cons_self)⟩, hf, hpos⟩

end NLAlib.Computation
