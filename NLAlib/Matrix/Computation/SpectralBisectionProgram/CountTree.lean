/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.StaticCost
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Matrix.Computation.PairKernels.Hermitian

/-!
# Crude polynomial counts of a first-order tree

Tools for the static count of `NLAlib.eighProg.compiled`: polynomials in $(N, \ell_0, F)$ with
natural coefficients (`NLAlib.CostPoly`) that bound the counts of a first-order tree class by
class (`NLAlib.crudeCount`) and its workspace (`NLAlib.crudeCells`), and the tags of a tree
(`NLAlib.tagsOf`). The functions are defined through the recursor of
`NLAlib.Computation.FStmt`, so that the polynomial checks are decided by the kernel.

## Main results

* `NLAlib.count_staticCost_le_eval_crudeCount`, `NLAlib.cells_staticCost_le_eval_crudeCells`:
  the polynomial bounds of a tree.
* `NLAlib.count_staticCost_le_zero_of_opKindTag_notMem_tagsOf`,
  `NLAlib.cells_staticCost_le_zero_of_notMem_tagsOf`: a tag that is not a tag of the tree is not
  charged.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

variable {P ι : Type}

/-! ### Polynomials -/

/-- Polynomials in $(N, \ell_0, F)$ with natural coefficients, as unnormalized lists of terms
(coefficient, exponents). -/
abbrev CostPoly := List (ℕ × ℕ × ℕ × ℕ)

/-- The value of a polynomial at $(N, \ell_0, F) = (N, L, F)$. -/
def CostPoly.eval (N L F : ℕ) (p : CostPoly) : ℕ :=
  (p.map fun e => e.1 * (N ^ e.2.1 * L ^ e.2.2.1 * F ^ e.2.2.2)).sum

/-- The product of two polynomials. -/
def CostPoly.polyMul (p q : CostPoly) : CostPoly :=
  p.flatMap fun a => q.map fun b => (a.1 * b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

/-- An upper bound of an index expression by a polynomial, the variables bounded by `σ`:
truncated subtraction and the remainder by their first argument. -/
def CostPoly.ofIExp {ni : ℕ} (σ : Fin ni → CostPoly) : IExp (Fin ni) → CostPoly
  | .var v => σ v
  | .const n => [(n, 0, 0, 0)]
  | .add a b => ofIExp σ a ++ ofIExp σ b
  | .sub a _ => ofIExp σ a
  | .mul a b => (ofIExp σ a).polyMul (ofIExp σ b)
  | .mod a _ => ofIExp σ a

/-- The extension of a polynomial environment by a last entry `x`. -/
def CostPoly.snoc {n : ℕ} (σ : Fin n → CostPoly) (x : CostPoly) : Fin (n + 1) → CostPoly :=
  fun i => if h : (i : ℕ) < n then σ ⟨i, h⟩ else x

/-- The constant polynomial $1$ if the classes `c` and `d` agree, $0$ otherwise. -/
def CostPoly.indicator (c d : ℕ) : CostPoly := if d = c then [(1, 0, 0, 0)] else []

private theorem CostPoly.eval_append (N L F : ℕ) (p q : CostPoly) :
    (p ++ q).eval N L F = p.eval N L F + q.eval N L F := by
  simp [CostPoly.eval]

private theorem CostPoly.eval_polyMul (N L F : ℕ) (p q : CostPoly) :
    (p.polyMul q).eval N L F = p.eval N L F * q.eval N L F := by
  induction p with
  | nil => simp [CostPoly.polyMul, CostPoly.eval]
  | cons a p ih =>
    have ih' : CostPoly.eval N L F (p.flatMap fun a => q.map fun b =>
        (a.1 * b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)) =
        CostPoly.eval N L F p * CostPoly.eval N L F q := ih
    simp only [CostPoly.polyMul, List.flatMap_cons, CostPoly.eval_append, ih']
    simp only [CostPoly.eval, List.map_cons, List.sum_cons, List.map_map, add_mul]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp, pow_add]
    ring

private theorem CostPoly.evalIn_le_eval_ofIExp {N L F ni : ℕ} {ρ : Fin ni → ℕ}
    {σ : Fin ni → CostPoly} (h : ∀ v, ρ v ≤ (σ v).eval N L F) :
    ∀ e : IExp (Fin ni), e.evalIn ρ ≤ (CostPoly.ofIExp σ e).eval N L F
  | .var v => h v
  | .const n => by simp [CostPoly.ofIExp, CostPoly.eval, IExp.evalIn]
  | .add a b => by
    simp only [IExp.evalIn, CostPoly.ofIExp, CostPoly.eval_append]
    exact Nat.add_le_add (evalIn_le_eval_ofIExp h a) (evalIn_le_eval_ofIExp h b)
  | .sub a _ => (Nat.sub_le _ _).trans (evalIn_le_eval_ofIExp h a)
  | .mul a b => by
    simp only [IExp.evalIn, CostPoly.ofIExp, CostPoly.eval_polyMul]
    exact Nat.mul_le_mul (evalIn_le_eval_ofIExp h a) (evalIn_le_eval_ofIExp h b)
  | .mod a _ => (Nat.mod_le _ _).trans (evalIn_le_eval_ofIExp h a)

private theorem CostPoly.snoc_le {N L F n : ℕ} {ρ : Fin n → ℕ} {σ : Fin n → CostPoly}
    (h : ∀ v, ρ v ≤ (σ v).eval N L F) {i : ℕ} {x : CostPoly} (hi : i ≤ x.eval N L F) :
    ∀ v, Fin.snoc (α := fun _ => ℕ) ρ i v ≤ (CostPoly.snoc σ x v).eval N L F := by
  intro v
  by_cases hv : (v : ℕ) < n
  · simp only [Fin.snoc, hv, dif_pos, CostPoly.snoc, cast_eq]
    exact h _
  · simp only [Fin.snoc, hv, dif_neg, not_false_eq_true, CostPoly.snoc, cast_eq]
    exact hi

private theorem CostPoly.eval_indicator (N L F c d : ℕ) :
    (CostPoly.indicator c d).eval N L F = if d = c then 1 else 0 := by
  unfold CostPoly.indicator; split_ifs <;> simp [CostPoly.eval]

/-! ### Classes and tags of operation kinds -/

/-- A class of operation kinds, forgetting tags, oracle names and dimensions. -/
def opKindClass : OpKind P ι → ℕ
  | .bin _ b => match b with
    | .add => 10 | .sub => 11 | .mul => 12 | .div => 13 | _ => 14
  | .un _ u => match u with
    | .neg => 20 | .sqrt => 23 | _ => 21
  | .lit _ => 1
  | .cmp _ => 6
  | .copy _ => 2
  | .draw _ d => match d with
    | .gaussian => 30 | .uniform => 32 | _ => 31
  | .convert _ _ => 3
  | .rom _ => 5
  | .load _ _ => 4
  | .matvec _ _ => 8
  | .kcall _ _ _ => 9
  | .toNat _ => 7

/-- The tag of an operation kind. -/
def opKindTag : OpKind P ι → P
  | .bin p _ => p | .un p _ => p | .lit p => p | .cmp p => p | .copy p => p | .draw p _ => p
  | .convert p _ => p | .rom p => p | .load p _ => p | .matvec p _ => p | .kcall p _ _ => p
  | .toNat p => p

/-! ### The crude counts and the tags of a tree -/

/-- The kind of a scalar instruction of a first-order tree, at zero buffers and index values. -/
abbrev instrKind {nb ni : ℕ} (i : Instr P (Fin nb) (Fin ni)) : OpKind P ι :=
  (i.subst (fun _ => 0) (fun _ => .const 0)).kind

/-- **A crude count of the operations of class `c`** of a tree, the index variables bounded by
`σ`: loops by their trip-count bound times the body at the largest index, index binders by the
body at the bound, branches by their sum. -/
noncomputable def crudeCount (c : ℕ) {nb ni : ℕ} (s : FStmt P ι nb ni) :
    (Fin ni → CostPoly) → CostPoly :=
  FStmt.rec (motive := fun _ ni _ => (Fin ni → CostPoly) → CostPoly)
    (skip := fun _ => [])
    (seq := fun _ _ a b σ => a σ ++ b σ)
    (instr := fun i _ => CostPoly.indicator c (opKindClass (instrKind (ι := ι) i)))
    (apply := fun _ _ _ _ _ _ cols σ =>
      CostPoly.indicator c 4 ++ (CostPoly.ofIExp σ cols).polyMul (CostPoly.indicator c 8))
    (rom := fun _ _ _ _ => CostPoly.indicator c 5)
    (alloc := fun _ _ _ b σ => b σ)
    (loop := fun n _ b σ =>
      (CostPoly.ofIExp σ n).polyMul (b (CostPoly.snoc σ (CostPoly.ofIExp σ n))))
    (whileFuel := fun f _ _ _ _ _ b σ =>
      (CostPoly.ofIExp σ f).polyMul (CostPoly.indicator c 6 ++ b σ))
    (ite := fun _ _ _ _ _ _ t e σ => CostPoly.indicator c 6 ++ (t σ ++ e σ))
    (named := fun _ _ _ b σ => b σ)
    (kcall := fun _ _ _ _ _ _ => CostPoly.indicator c 9)
    (bindIdx := fun _ _ bd _ b σ =>
      CostPoly.indicator c 7 ++ b (CostPoly.snoc σ (CostPoly.ofIExp σ bd))) s

/-- A crude bound on the additional live cells of a tree, the index variables bounded by `σ`
(sums for maxima). -/
noncomputable def crudeCells {nb ni : ℕ} (s : FStmt P ι nb ni) :
    (Fin ni → CostPoly) → CostPoly :=
  FStmt.rec (motive := fun _ ni _ => (Fin ni → CostPoly) → CostPoly)
    (skip := fun _ => [])
    (seq := fun _ _ a b σ => a σ ++ b σ)
    (instr := fun _ _ => [])
    (apply := fun _ _ _ _ _ _ _ _ => [])
    (rom := fun _ _ _ _ => [])
    (alloc := fun _ len _ b σ => CostPoly.ofIExp σ len ++ b σ)
    (loop := fun n _ b σ => b (CostPoly.snoc σ (CostPoly.ofIExp σ n)))
    (whileFuel := fun _ _ _ _ _ _ b σ => b σ)
    (ite := fun _ _ _ _ _ _ t e σ => t σ ++ e σ)
    (named := fun _ _ _ b σ => b σ)
    (kcall := fun _ _ _ _ _ _ => [])
    (bindIdx := fun _ _ bd _ b σ => b (CostPoly.snoc σ (CostPoly.ofIExp σ bd))) s

/-- The tags of a tree. -/
noncomputable def tagsOf {nb ni : ℕ} (s : FStmt P ι nb ni) : List P :=
  FStmt.rec (motive := fun _ _ _ => List P)
    (skip := [])
    (seq := fun _ _ a b => a ++ b)
    (instr := fun i => [opKindTag (instrKind (ι := ι) i)])
    (apply := fun _ p _ _ _ _ _ => [p])
    (rom := fun p _ _ => [p])
    (alloc := fun p _ _ b => p :: b)
    (loop := fun _ _ b => b)
    (whileFuel := fun _ p _ _ _ _ b => p :: b)
    (ite := fun p _ _ _ _ _ t e => p :: (t ++ e))
    (named := fun _ _ _ b => b)
    (kcall := fun _ p _ _ _ => [p])
    (bindIdx := fun p _ _ _ b => p :: b) s

/-! ### The bounds -/

private theorem count_supRange_le {f : ℕ → StaticCost P ι} {m B : ℕ} {κ : OpKind P ι}
    (h : ∀ k < m, (f k).count κ ≤ B) : (StaticCost.supRange m f).count κ ≤ B := by
  unfold StaticCost.supRange
  suffices ∀ l : List ℕ, (∀ k ∈ l, k < m) →
      (l.foldr (fun k c => (f k).branch c) StaticCost.zero).count κ ≤ B from
    this _ fun k hk => List.mem_range.mp hk
  intro l hl
  induction l with
  | nil => simp [StaticCost.zero]
  | cons a l ih =>
    simp only [List.foldr_cons, StaticCost.branch, Finsupp.sup_apply]
    exact max_le (h a (hl a List.mem_cons_self)) (ih fun k hk => hl k (List.mem_cons_of_mem a hk))

private theorem cells_supRange_le {f : ℕ → StaticCost P ι} {m B : ℕ} {q : P}
    (h : ∀ k < m, (f k).cells q ≤ B) : (StaticCost.supRange m f).cells q ≤ B := by
  unfold StaticCost.supRange
  suffices ∀ l : List ℕ, (∀ k ∈ l, k < m) →
      (l.foldr (fun k c => (f k).branch c) StaticCost.zero).cells q ≤ B from
    this _ fun k hk => List.mem_range.mp hk
  intro l hl
  induction l with
  | nil => simp [StaticCost.zero]
  | cons a l ih =>
    simp only [List.foldr_cons, StaticCost.branch]
    exact max_le (h a (hl a List.mem_cons_self)) (ih fun k hk => hl k (List.mem_cons_of_mem a hk))

private theorem single_apply_le (k κ : OpKind P ι) :
    (Finsupp.single k 1 : OpCount P ι) κ ≤ if opKindClass k = opKindClass κ then 1 else 0 := by
  classical
  rw [Finsupp.single_apply]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (congrArg opKindClass h1) h2
  · exact zero_le_one
  · exact le_rfl

variable [DecidableEq P]

/-- **The crude count bounds the static count**: under the standard charge, the static count of
the tree `s` at the index values `ρ` of every kind `κ` is at most the crude count of the class of
`κ`, whenever each `ρ v` is at most the value of `σ v` at $(N, L, F)$. -/
theorem count_staticCost_le_eval_crudeCount (w : P → ℕ) (κ : OpKind P ι) (N L F : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ) (σ : Fin ni → CostPoly),
      (∀ v, ρ v ≤ (σ v).eval N L F) →
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ ≤
        (crudeCount (opKindClass κ) s σ).eval N L F := by
  intro nb ni s
  induction s with
  | skip => intro ρ σ _; simp [FStmt.staticCost, StaticCost.zero]
  | seq s t ihs iht =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply, crudeCount,
      CostPoly.eval_append]
    exact Nat.add_le_add (ihs ρ σ h) (iht ρ σ h)
  | instr i =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, crudeCount, CostPoly.eval_indicator]
    exact single_apply_le _ _
  | apply o p d dOff s sOff cols =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.step, crudeCount, CostPoly.eval_append,
      CostPoly.eval_polyMul, CostPoly.eval_indicator, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
    exact Nat.add_le_add (single_apply_le _ _)
      (Nat.mul_le_mul (CostPoly.evalIn_le_eval_ofIExp h cols) (single_apply_le _ _))
  | rom p d i =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, crudeCount, CostPoly.eval_indicator]
    exact single_apply_le _ _
  | alloc p len body ih => exact ih
  | loop n body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply, crudeCount, CostPoly.eval_polyMul]
    have hn := CostPoly.evalIn_le_eval_ofIExp h n
    refine (List.sum_le_card_nsmul _ ((crudeCount (opKindClass κ) body
      (CostPoly.snoc σ (CostPoly.ofIExp σ n))).eval N L F) ?_).trans ?_
    · simp only [List.mem_map, List.mem_range]
      rintro _ ⟨i, hi, rfl⟩
      exact ih _ _ (CostPoly.snoc_le h (hi.le.trans hn))
    · rw [List.length_map, List.length_range, smul_eq_mul]
      exact Nat.mul_le_mul_right _ hn
  | whileFuel fuel p c x y body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, crudeCount, CostPoly.eval_polyMul,
      CostPoly.eval_append, CostPoly.eval_indicator]
    exact Nat.mul_le_mul (CostPoly.evalIn_le_eval_ofIExp h fuel)
      (Nat.add_le_add (single_apply_le _ _) (ih ρ σ h))
  | ite p c x y t e iht ihe =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply, crudeCount, CostPoly.eval_append,
      CostPoly.eval_indicator]
    exact Nat.add_le_add (single_apply_le _ _) (max_le ((iht ρ σ h).trans (Nat.le_add_right _ _))
      ((ihe ρ σ h).trans (Nat.le_add_left _ _)))
  | named name args body ih => exact ih
  | kcall o p dims ins outs =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, crudeCount, CostPoly.eval_indicator]
    exact single_apply_le _ _
  | bindIdx p x bound body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply, crudeCount,
      CostPoly.eval_append, CostPoly.eval_indicator]
    exact Nat.add_le_add (single_apply_le _ _) (count_supRange_le fun k hk => ih _ _
      (CostPoly.snoc_le h ((Nat.lt_succ_iff.mp hk).trans
        (CostPoly.evalIn_le_eval_ofIExp h bound))))

/-- **The crude cell bound bounds the static workspace**: under any charge, the static workspace
of the tree `s` at the index values `ρ` at every tag is at most the value of the crude cell bound,
whenever each `ρ v` is at most the value of `σ v` at $(N, L, F)$. -/
theorem cells_staticCost_le_eval_crudeCells (charge : OpKind P ι → OpCount P ι) (w : P → ℕ)
    (q : P) (N L F : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ) (σ : Fin ni → CostPoly),
      (∀ v, ρ v ≤ (σ v).eval N L F) →
      (s.staticCost charge w ρ).cells q ≤ (crudeCells s σ).eval N L F := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, crudeCells, CostPoly.eval_append]
    exact max_le ((ihs ρ σ h).trans (Nat.le_add_right _ _))
      ((iht ρ σ h).trans (Nat.le_add_left _ _))
  | alloc p len body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.alloc, crudeCells, CostPoly.eval_append]
    refine Nat.add_le_add ?_ (ih ρ σ h)
    split_ifs
    · exact CostPoly.evalIn_le_eval_ofIExp h len
    · exact Nat.zero_le _
  | loop n body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, crudeCells]
    exact StaticCost.sequence_cells_le _ _ _ _ fun i hi => ih _ _ (CostPoly.snoc_le h
      ((List.mem_range.mp hi).le.trans (CostPoly.evalIn_le_eval_ofIExp h n)))
  | whileFuel fuel p c x y body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      crudeCells]
    exact max_le (Nat.zero_le _) (ih ρ σ h)
  | ite p c x y t e iht ihe =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, StaticCost.branch, crudeCells,
      CostPoly.eval_append]
    exact max_le (Nat.zero_le _) (max_le ((iht ρ σ h).trans (Nat.le_add_right _ _))
      ((ihe ρ σ h).trans (Nat.le_add_left _ _)))
  | named name args body ih => exact ih
  | bindIdx p x bound body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, crudeCells]
    exact max_le (Nat.zero_le _) (cells_supRange_le fun k hk => ih _ _
      (CostPoly.snoc_le h ((Nat.lt_succ_iff.mp hk).trans
        (CostPoly.evalIn_le_eval_ofIExp h bound))))
  | _ => intro ρ _; simp [FStmt.staticCost, StaticCost.step, StaticCost.zero]

/-- **A kind whose tag is not a tag of the tree is not counted**: under the standard charge, the
static count of the tree `s` of a kind `κ` whose tag is not in `NLAlib.tagsOf s` is zero. -/
theorem count_staticCost_le_zero_of_opKindTag_notMem_tagsOf (w : P → ℕ) (κ : OpKind P ι) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ), opKindTag κ ∉ tagsOf s →
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ ≤ 0 := by
  classical
  have hs : ∀ k : OpKind P ι, opKindTag κ ≠ opKindTag k →
      (Finsupp.single k 1 : OpCount P ι) κ ≤ 0 := by
    intro k hk
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact hk rfl
  intro nb ni s
  induction s with
  | skip => intro ρ _; simp [FStmt.staticCost, StaticCost.zero]
  | seq s t ihs iht =>
    intro ρ h
    simp only [tagsOf, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply]
    exact Nat.add_le_add (ihs ρ h.1) (iht ρ h.2)
  | apply o p d dOff s sOff cols =>
    intro ρ h
    simp only [tagsOf, List.mem_singleton] at h
    simp only [FStmt.staticCost, StaticCost.step, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rw [Nat.le_zero.mp (hs (.load p o) h), Nat.le_zero.mp (hs (.matvec p o) h)]
    simp
  | alloc p len body ih =>
    intro ρ h
    simp only [tagsOf, List.mem_cons, not_or] at h
    exact ih ρ h.2
  | loop n body ih =>
    intro ρ h
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply]
    refine (List.sum_le_card_nsmul _ 0 ?_).trans (by simp)
    simp only [List.mem_map]
    rintro _ ⟨i, _, rfl⟩
    exact ih _ h
  | whileFuel fuel p c x y body ih =>
    intro ρ h
    simp only [tagsOf, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
    simp [Nat.le_zero.mp (hs (.cmp p) h.1), Nat.le_zero.mp (ih ρ h.2)]
  | ite p c x y t e iht ihe =>
    intro ρ h
    simp only [tagsOf, List.mem_cons, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply]
    have h1 := hs (.cmp p) h.1
    have h2 := iht ρ h.2.1
    have h3 := ihe ρ h.2.2
    omega
  | named name args body ih => exact ih
  | bindIdx p x bound body ih =>
    intro ρ h
    simp only [tagsOf, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply]
    exact Nat.add_le_add (hs (.toNat p) h.1) (count_supRange_le fun k _ => ih _ h.2)
  | _ =>
    intro ρ h
    simp only [tagsOf, List.mem_singleton] at h
    exact hs _ h

/-- **A tag that is not a tag of the tree has no workspace**: under any charge, the static
workspace of the tree `s` at a tag `q` not in `NLAlib.tagsOf s` is zero. -/
theorem cells_staticCost_le_zero_of_notMem_tagsOf (charge : OpKind P ι → OpCount P ι)
    (w : P → ℕ) (q : P) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ), q ∉ tagsOf s →
      (s.staticCost charge w ρ).cells q ≤ 0 := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    intro ρ h
    simp only [tagsOf, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq]
    exact max_le (ihs ρ h.1) (iht ρ h.2)
  | alloc p len body ih =>
    intro ρ h
    simp only [tagsOf, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.alloc, if_neg h.1, zero_add]
    exact ih ρ h.2
  | loop n body ih =>
    intro ρ h
    simp only [FStmt.staticCost]
    exact StaticCost.sequence_cells_le _ _ _ _ fun i _ => ih _ h
  | whileFuel fuel p c x y body ih =>
    intro ρ h
    simp only [tagsOf, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step]
    exact max_le (Nat.zero_le _) (ih ρ h.2)
  | ite p c x y t e iht ihe =>
    intro ρ h
    simp only [tagsOf, List.mem_cons, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, StaticCost.branch]
    exact max_le (Nat.zero_le _) (max_le (iht ρ h.2.1) (ihe ρ h.2.2))
  | named name args body ih => exact ih
  | bindIdx p x bound body ih =>
    intro ρ h
    simp only [tagsOf, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step]
    exact max_le (Nat.zero_le _) (cells_supRange_le fun k _ => ih _ h.2)
  | _ => intro ρ _; simp [FStmt.staticCost, StaticCost.step, StaticCost.zero]

end NLAlib
