/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.FirstOrder
public import NLAlib.Computation.StaticCost
public import NLAlib.Computation.Grid
public import NLAlib.Computation.BinaryFloatSem
public import NLAlib.Computation.Exact

/-!
# The bounded index binder (scaffold)

Statements for stage COMPDYN S2a (design note `docs/design/Computation-EighProgram.md`, §2): the
run of an index binder on a stored value, the round trip of a size written as an integer literal
and read back by a binder (`NLAlib.Computation.IsExactIntLit` with
`NLAlib.Computation.IsExactToNat`, decisions M1 and M2 of the COMPDYN sheet), the witnesses of the
new contracts for the library's semantics, and the index normal form
(`NLAlib.Computation.Stmt.normIdx`): a statement runs as its normal form, so a kernel lemma stated
at constant sizes applies at sizes bound by a loop or a binder.

## Main results

* `NLAlib.Computation.exec_bindIdx_of_read`, `NLAlib.Computation.exec_bindIdx_eq_none`: the run of
  a binder.
* `NLAlib.Computation.IsExactIntLit.toNat_eq_of_lit_eq_some`: the round trip of a size.
* `NLAlib.Computation.isExactToNat_exactSem`, `NLAlib.Computation.isExactToNat_gridSem`,
  `NLAlib.Computation.isExactToNat_binaryFloatSem`, `NLAlib.Computation.mulShrinks_exactSem`,
  `NLAlib.Computation.mulShrinks_gridSem`: witnesses.
* `NLAlib.Computation.exec_normIdx`: a statement runs as its index normal form.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-! ### The run of a binder -/

/-- **The run of an index binder on a stored value**: if the cell `x` holds $v$ at tag `p` and
the semantics converts $v$ to $k$, the binder runs its body at $\min(k, \mathit{bound})$ after one
charged conversion. No printed source.
Proof: `NLAlib.Computation.exec_bindIdx`, then unfold `NLAlib.Computation.toNatStep` and rewrite
with `hx`, `hk` (`Option.bind_some`, `Option.map_some`). S, 3 lines. -/
theorem exec_bindIdx_of_read [AddMonoid C] (I : Interp P ι K C) {p : P} {x : Cell ℕ ℕ}
    {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} {v : K} {k : ℕ}
    (hx : st.store.read p x.buf x.idx.eval = some v) (hk : I.sem.toNat p v = some k) :
    exec I (.bindIdx p x bound body) st =
      exec I (body (min k bound.eval)) { st with cnt := st.cnt + I.charge (.toNat p) } := by
  simp only [exec_bindIdx, toNatStep, hx, hk, Option.bind_some, Option.map_some]

/-- **An index binder fails when the conversion fails**: if the cell `x` holds $v$ and the
semantics does not convert $v$, the binder fails, whatever its body (the default conversion of a
semantics, so no existing semantics runs a binder). No printed source.
Proof: `NLAlib.Computation.exec_bindIdx`, unfold `NLAlib.Computation.toNatStep`, rewrite with `hx`
and `hk` (`Option.bind_some`, `Option.map_none`, `Option.bind_none`). S, 3 lines. -/
theorem exec_bindIdx_eq_none [AddMonoid C] (I : Interp P ι K C) {p : P} {x : Cell ℕ ℕ}
    {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} {v : K}
    (hx : st.store.read p x.buf x.idx.eval = some v) (hk : I.sem.toNat p v = none) :
    exec I (.bindIdx p x bound body) st = none := by
  simp only [exec_bindIdx, toNatStep, hx, hk, Option.bind_some, Option.map_none, Option.bind_none]

omit [DecidableEq P] in
/-- **The round trip of a size**: under exact integer literals up to $B$ and the exact floor
conversion, the literal of $k \le B$ converts back to $k$. So a size written by `litIdx` and read by
an index binder is the size. No printed source.
Proof: `hlit p k hk` gives a literal $z'$ with decoding $k$; `hz` makes $z = z'$
(`Option.some_injective`); `htn p z` and `Nat.floor_natCast`. S, 5 lines. -/
theorem IsExactIntLit.toNat_eq_of_lit_eq_some {dec : P → K → ℝ} {sem : ScalarSem P K} {B : ℕ}
    (hlit : IsExactIntLit dec sem B) (htn : IsExactToNat dec sem) {p : P} {k : ℕ} (hk : k ≤ B)
    {z : K} (hz : sem.lit p k = some z) : sem.toNat p z = some k := by
  obtain ⟨z', hz', hdec⟩ := hlit p k hk
  have hzz : z = z' := Option.some_injective _ (hz.symm.trans hz')
  subst hzz
  rw [htn p z, hdec, Nat.floor_natCast]

/-! ### Witnesses -/

omit [DecidableEq P] in
/-- **Exact real arithmetic converts exactly**: `NLAlib.Computation.exactSem` over $\mathbb{R}$,
with the identity decoding, meets `NLAlib.Computation.IsExactToNat`. No printed source.
Proof: `intro p x`; unfold `NLAlib.Computation.exactSem`; the imaginary part of a real is $0$
(`RCLike.im_to_real`, `RCLike.re_to_real`), so `if_pos rfl`. S, 3 lines. -/
theorem isExactToNat_exactSem : IsExactToNat (P := P) (fun _ x => x) (exactSem (𝕜 := ℝ)) := by
  intro p x
  simp [exactSem]

omit [DecidableEq P] in
/-- **Floating-point arithmetic on a grid converts exactly**: `NLAlib.Computation.gridSem t`, with
the decoding $x \mapsto \mathrm{fl}_p(x)$ of `NLAlib.Computation.isRelErrSem_gridSem`, meets
`NLAlib.Computation.IsExactToNat`. No printed source.
Proof: `rfl` (the conversion of `NLAlib.Computation.gridSem` is the floor of the decoding). S,
1 line. -/
theorem isExactToNat_gridSem (t : P → ℕ) :
    IsExactToNat (fun p => Real.roundNearest (t p)) (gridSem t) := by
  intro p x
  rfl

omit [DecidableEq P] in
/-- **Bounded binary arithmetic converts exactly**: `NLAlib.Computation.binaryFloatSem`, with the
decoding by the value, meets `NLAlib.Computation.IsExactToNat`. No printed source.
Proof: `rfl`. S, 1 line. -/
theorem isExactToNat_binaryFloatSem (fmt : Float.Model.Format) (he : 2 ≤ fmt.exponentBits)
    (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) :
    IsExactToNat (P := P) (fun _ x => x.val) (binaryFloatSem fmt he r hr) := by
  intro p x
  rfl

omit [DecidableEq P] in
/-- **Exact real multiplication by a factor of modulus at most one does not enlarge**:
`NLAlib.Computation.exactSem` over $\mathbb{R}$, with the identity decoding, meets
`NLAlib.Computation.MulShrinks`. No printed source.
Proof: unfold `NLAlib.Computation.exactSem`; the product is $xy$ (`Option.some.inj`), and
$\lvert xy \rvert = \lvert x \rvert\lvert y \rvert \le \lvert x \rvert$ (`abs_mul`,
`mul_le_of_le_one_right`, `abs_nonneg`). S, 4 lines. -/
theorem mulShrinks_exactSem : MulShrinks (P := P) (fun _ x => x) (exactSem (𝕜 := ℝ)) := by
  intro p x y z h hy
  have hz : x * y = z := Option.some.inj h
  subst hz
  change |x * y| ≤ |x|
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg x) hy

omit [DecidableEq P] in
/-- **Rounding to nearest on a grid does not enlarge a product by a factor of modulus at most
one**: for $t_p \ge 1$, `NLAlib.Computation.gridSem t` with the decoding
$x \mapsto \mathrm{fl}_p(x)$ meets `NLAlib.Computation.MulShrinks`: if $\lvert\mathrm{fl}(y)\rvert
\le 1$ then $\lvert\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(x)\mathrm{fl}(y)))\rvert \le
\lvert\mathrm{fl}(x)\rvert$. No printed source.
Proof: the decoded product is $\mathrm{fl}(a)$ with $a = \mathrm{fl}(x)\mathrm{fl}(y)$,
$\lvert a \rvert \le \lvert b \rvert$ for the grid point $b = \mathrm{fl}(x)$
(`Real.roundNearest_mem_floatGrid`, `Real.roundNearest_roundNearest`); rounding to nearest does not
cross a grid point of larger modulus: if $\lvert a \rvert$ and $\lvert b \rvert$ have the same
binade, $b 2^{-e}$ is an integer of modulus at least $\lvert a 2^{-e}\rvert$ and `round` is
monotone (`Int.le_of_lt_add_one`); if $a$ is in a lower binade,
$\lvert\mathrm{fl}(a)\rvert \le 2^{k + 1} \le \lvert b \rvert$ (`Int.zpow_log_le_self`,
`Int.lt_zpow_succ_log_self`). M, about 70 lines. -/
theorem mulShrinks_gridSem (t : P → ℕ) (ht : ∀ p, 0 < t p) :
    MulShrinks (fun p => Real.roundNearest (t p)) (gridSem t) := by
  -- rounding does not leave the modulus of a grid point `β`
  have key : ∀ {t : ℕ} {a β : ℝ}, β ∈ Real.floatGrid t → |a| ≤ |β| →
      |Real.roundNearest t a| ≤ |β| := by
    intro t a β hβ ha
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [Real.roundNearest]
    have hapos : 0 < |a| := abs_pos.mpr ha0
    have hβpos : 0 < |β| := hapos.trans_le ha
    have hfix : Real.roundNearest t β = β := Real.roundNearest_eq_self_of_mem_floatGrid hβ
    have hσκ : Int.log 2 |a| ≤ Int.log 2 |β| := Int.log_mono_right hapos ha
    have hκle : (2:ℝ) ^ Int.log 2 |β| ≤ |β| := by
      exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two hβpos
    have hσlt : |a| < (2:ℝ) ^ (Int.log 2 |a| + 1) := by
      exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) one_lt_two |a|
    have hmono : ∀ u v : ℝ, u ≤ v → round u ≤ round v := fun u v h => by
      rw [round_eq, round_eq]; exact Int.floor_mono (by linarith)
    rcases eq_or_lt_of_le hσκ with h | h
    · -- same binade as `β`: the rounding step is the one of `β`, which is a multiple of it
      have hfix' := hfix
      rw [Real.roundNearest] at hfix'
      rw [Real.roundNearest, h]
      set e : ℤ := Int.log 2 |β| + 1 - t with he
      have hpos : (0:ℝ) < 2 ^ e := zpow_pos two_pos _
      set N : ℤ := round (β / 2 ^ e) with hN
      have hβN : β = (N:ℝ) * 2 ^ e := hfix'.symm
      have hr : |a / 2 ^ e| ≤ ((|N| : ℤ) : ℝ) := by
        rw [Int.cast_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
        have := ha
        rw [hβN, abs_mul, abs_of_pos hpos] at this
        exact this
      obtain ⟨hl, hu⟩ := abs_le.mp hr
      have h1 := hmono _ _ hl
      have h2 := hmono _ _ hu
      rw [← Int.cast_neg, round_intCast] at h1
      rw [round_intCast] at h2
      have hz : |round (a / 2 ^ e)| ≤ |N| := abs_le.mpr ⟨h1, h2⟩
      have hβabs : |β| = ((|N| : ℤ) : ℝ) * 2 ^ e := by
        rw [hβN, abs_mul, abs_of_pos hpos, Int.cast_abs]
      rw [abs_mul, abs_of_pos hpos, ← Int.cast_abs, hβabs]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hpos.le
    · -- `a` lies in a lower binade: its rounding is at most the top of that binade
      rw [Real.roundNearest]
      set f : ℤ := Int.log 2 |a| + 1 - t with hf
      have hfpos : (0:ℝ) < 2 ^ f := zpow_pos two_pos _
      have hid : (2:ℝ) ^ t * 2 ^ f = 2 ^ (Int.log 2 |a| + 1) := by
        rw [hf, ← zpow_natCast, ← zpow_add₀ two_ne_zero]; congr 1; ring
      have hz : |a / 2 ^ f| ≤ (2:ℝ) ^ t := by
        rw [abs_div, abs_of_pos hfpos, div_le_iff₀ hfpos, hid]; exact hσlt.le
      obtain ⟨hl, hu⟩ := abs_le.mp hz
      have hMr : ((2 ^ t : ℤ) : ℝ) = (2:ℝ) ^ t := by push_cast; rfl
      have h1 := hmono _ _ hl
      have h2 := hmono _ _ hu
      rw [← hMr, ← Int.cast_neg, round_intCast] at h1
      rw [← hMr, round_intCast] at h2
      have hz2 : |round (a / 2 ^ f)| ≤ 2 ^ t := abs_le.mpr ⟨h1, h2⟩
      have hrt : ((|round (a / 2 ^ f)| : ℤ) : ℝ) ≤ (2:ℝ) ^ t := by
        rw [← hMr]; exact_mod_cast hz2
      have hchain : (2:ℝ) ^ (Int.log 2 |a| + 1) ≤ (2:ℝ) ^ Int.log 2 |β| :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      rw [abs_mul, abs_of_pos hfpos, ← Int.cast_abs]
      calc ((|round (a / 2 ^ f)| : ℤ) : ℝ) * 2 ^ f ≤ (2:ℝ) ^ t * 2 ^ f :=
            mul_le_mul_of_nonneg_right hrt hfpos.le
        _ = (2:ℝ) ^ (Int.log 2 |a| + 1) := hid
        _ ≤ (2:ℝ) ^ Int.log 2 |β| := hchain
        _ ≤ |β| := hκle
  intro p x y z h hy
  simp only [gridSem, exactSem, Option.map_some, Option.some.injEq] at h
  subst h
  change |Real.roundNearest (t p) (Real.roundNearest (t p)
      (Real.roundNearest (t p) x * Real.roundNearest (t p) y))| ≤ |Real.roundNearest (t p) x|
  rw [Real.roundNearest_roundNearest (ht p)]
  refine key (Real.roundNearest_mem_floatGrid (ht p) x) ?_
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hy

/-! ### The index normal form -/

/-- **A statement runs as its index normal form**: for every statement at `VB := ℕ`, `VI := ℕ`,
the run of `NLAlib.Computation.Stmt.normIdx s` is the run of `s`, from every state, under every
interpretation. A kernel lemma stated at constant sizes then applies at any index expressions with
the same values: the two statements have the same normal form. No printed source.
Proof: induction on `s` generalizing the state; each case unfolds `NLAlib.Computation.exec`
(`NLAlib.Computation.exec_loop`, `NLAlib.Computation.exec_alloc`,
`NLAlib.Computation.exec_bindIdx`) on both sides: the leaves read their index expressions only
through `NLAlib.Computation.IExp.eval` (`IExp.eval_const`; for an instruction `cases i` and
`NLAlib.Computation.Instr.run`, whose `Instr.kind` does not see indices; for a comparison
`NLAlib.Computation.cmpStep`, for a binder `NLAlib.Computation.toNatStep`, for a kernel call
`List.map_map`), and the binders use the induction hypothesis under `funext` in the folds of
`exec_loop` and `whileFuel`. M, about 80 lines. -/
theorem exec_normIdx [AddMonoid C] (I : Interp P ι K C) :
    ∀ (s : Stmt P ι ℕ ℕ) (st : St P K C), exec I s.normIdx st = exec I s st := by
  intro s
  induction s with
  | skip => intro st; simp only [Stmt.normIdx]
  | seq s t ihs iht =>
    intro st
    have h2 : exec I t.normIdx = exec I t := funext iht
    simp only [Stmt.normIdx, exec_seq, ihs, h2]
  | instr i =>
    intro st
    have hk : Instr.kind (ι := ι) i.normIdx = Instr.kind (ι := ι) i := by cases i <;> rfl
    have hr : ∀ s pos, i.normIdx.run I.sem I.tape s pos = i.run I.sem I.tape s pos := by
      intro s pos; cases i <;> rfl
    simp only [Stmt.normIdx, exec, hk, hr]
  | apply o p dst dOff src sOff cols =>
    intro st
    rfl
  | rom p dst i =>
    intro st
    simp only [Stmt.normIdx, exec, IExp.eval_const, Cell.normIdx]
  | alloc p len body ih =>
    intro st
    simp only [Stmt.normIdx, exec_alloc, IExp.eval_const, ih]
  | loop n body ih =>
    intro st
    have hb : (fun (st : St P K C) (i : ℕ) => exec I (body i).normIdx st) =
        (fun (st : St P K C) (i : ℕ) => exec I (body i) st) :=
      funext fun st => funext fun i => ih i st
    simp only [Stmt.normIdx, exec_loop, IExp.eval_const]
    rw [hb]
  | whileFuel fuel p c x y body ih =>
    intro st
    have hb : exec I body.normIdx = exec I body := funext ih
    have hc : ∀ st, cmpStep I p c x.normIdx y.normIdx st = cmpStep I p c x y st :=
      fun st => rfl
    simp only [Stmt.normIdx, exec, IExp.eval_const, hc, hb]
  | ite p c x y t e iht ihe =>
    intro st
    have ht : exec I t.normIdx = exec I t := funext iht
    have he : exec I e.normIdx = exec I e := funext ihe
    have hc : ∀ st, cmpStep I p c x.normIdx y.normIdx st = cmpStep I p c x y st :=
      fun st => rfl
    simp only [Stmt.normIdx, exec_ite, hc, ht, he]
  | named name args body ih =>
    intro st
    simp only [Stmt.normIdx, exec_named]
    exact ih st
  | kcall o p dims ins outs =>
    intro st
    simp only [Stmt.normIdx, exec, List.map_map, Function.comp_def, IExp.eval_const]
  | bindIdx p x bound body ih =>
    intro st
    have hc : toNatStep I p x.normIdx st = toNatStep I p x st := rfl
    simp only [Stmt.normIdx, exec_bindIdx, IExp.eval_const, hc, ih]

/-- **Statements with the same index normal form run the same.** No printed source.
Proof: `NLAlib.Computation.exec_normIdx` twice. S, 1 line. -/
theorem exec_eq_of_normIdx_eq [AddMonoid C] (I : Interp P ι K C) {s s' : Stmt P ι ℕ ℕ}
    (h : s.normIdx = s'.normIdx) (st : St P K C) : exec I s st = exec I s' st := by
  rw [← exec_normIdx I s st, h, exec_normIdx I s' st]

end NLAlib.Computation
