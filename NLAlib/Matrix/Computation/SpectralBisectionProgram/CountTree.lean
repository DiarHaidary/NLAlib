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
# The kernel tree of the spectral bisection program

Tools for the static count of `NLAlib.eighProg.compiled`: polynomials in $(N, \ell_0, F)$ with
natural coefficients that bound the counts of a first-order tree class by class, the tree of kernel
calls that a first-order tree prunes to, and the renaming of the registered tree to the tags `Unit`
and oracle names `Bool`, where the polynomial checks are decided.

## Main results

* `NLAlib.ep6_count_le`, `NLAlib.ep6_cells_le`: the polynomial bounds of a tree.
* `NLAlib.ep6_prune_compiled`, `NLAlib.ep6_compiled_map`: the kernel tree of the registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! ### EP6 helpers -/

/-- Polynomials in $(N, \ell_0, F)$ with natural coefficients, as unnormalized lists of terms
(coefficient, exponents). -/
abbrev ep6_Poly := List (ℕ × ℕ × ℕ × ℕ)

/-- The value of a polynomial. -/
def ep6_ev (N L F : ℕ) (p : ep6_Poly) : ℕ :=
  (p.map fun e => e.1 * (N ^ e.2.1 * L ^ e.2.2.1 * F ^ e.2.2.2)).sum

/-- The product of two polynomials. -/
def ep6_pmul (p q : ep6_Poly) : ep6_Poly :=
  p.flatMap fun a => q.map fun b => (a.1 * b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

private theorem ep6_ev_append (N L F : ℕ) (p q : ep6_Poly) :
    ep6_ev N L F (p ++ q) = ep6_ev N L F p + ep6_ev N L F q := by
  simp [ep6_ev]

private theorem ep6_ev_pmul (N L F : ℕ) (p q : ep6_Poly) :
    ep6_ev N L F (ep6_pmul p q) = ep6_ev N L F p * ep6_ev N L F q := by
  induction p with
  | nil => simp [ep6_pmul, ep6_ev]
  | cons a p ih =>
    have ih' : ep6_ev N L F (p.flatMap fun a => q.map fun b =>
        (a.1 * b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)) =
        ep6_ev N L F p * ep6_ev N L F q := ih
    simp only [ep6_pmul, List.flatMap_cons, ep6_ev_append, ih']
    simp only [ep6_ev, List.map_cons, List.sum_cons, List.map_map, add_mul]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro b _
    simp only [Function.comp, pow_add]
    ring

/-- An upper bound of an index expression by a polynomial: truncated subtraction and the
remainder by their first argument. -/
def ep6_up {ni : ℕ} (σ : Fin ni → ep6_Poly) : IExp (Fin ni) → ep6_Poly
  | .var v => σ v
  | .const n => [(n, 0, 0, 0)]
  | .add a b => ep6_up σ a ++ ep6_up σ b
  | .sub a _ => ep6_up σ a
  | .mul a b => ep6_pmul (ep6_up σ a) (ep6_up σ b)
  | .mod a _ => ep6_up σ a

private theorem ep6_evalIn_le_up {N L F ni : ℕ} {ρ : Fin ni → ℕ} {σ : Fin ni → ep6_Poly}
    (h : ∀ v, ρ v ≤ ep6_ev N L F (σ v)) :
    ∀ e : IExp (Fin ni), e.evalIn ρ ≤ ep6_ev N L F (ep6_up σ e)
  | .var v => h v
  | .const n => by simp [ep6_up, ep6_ev, IExp.evalIn]
  | .add a b => by
    simp only [IExp.evalIn, ep6_up, ep6_ev_append]
    exact Nat.add_le_add (ep6_evalIn_le_up h a) (ep6_evalIn_le_up h b)
  | .sub a _ => (Nat.sub_le _ _).trans (ep6_evalIn_le_up h a)
  | .mul a b => by
    simp only [IExp.evalIn, ep6_up, ep6_ev_pmul]
    exact Nat.mul_le_mul (ep6_evalIn_le_up h a) (ep6_evalIn_le_up h b)
  | .mod a _ => (Nat.mod_le _ _).trans (ep6_evalIn_le_up h a)

/-- Extension of a polynomial environment by a last entry. -/
def ep6_snoc {n : ℕ} (σ : Fin n → ep6_Poly) (x : ep6_Poly) : Fin (n + 1) → ep6_Poly :=
  fun i => if h : (i : ℕ) < n then σ ⟨i, h⟩ else x

private theorem ep6_snoc_le {N L F n : ℕ} {ρ : Fin n → ℕ} {σ : Fin n → ep6_Poly}
    (h : ∀ v, ρ v ≤ ep6_ev N L F (σ v)) {i : ℕ} {x : ep6_Poly} (hi : i ≤ ep6_ev N L F x) :
    ∀ v, Fin.snoc (α := fun _ => ℕ) ρ i v ≤ ep6_ev N L F (ep6_snoc σ x v) := by
  intro v
  by_cases hv : (v : ℕ) < n
  · simp only [Fin.snoc, hv, dif_pos, ep6_snoc, cast_eq]
    exact h _
  · simp only [Fin.snoc, hv, dif_neg, not_false_eq_true, ep6_snoc, cast_eq]
    exact hi

/-- A class of operation kinds, forgetting tags, oracle names and dimensions. -/
def ep6_cls {P ι : Type} : OpKind P ι → ℕ
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
def ep6_ktag {P ι : Type} : OpKind P ι → P
  | .bin p _ => p | .un p _ => p | .lit p => p | .cmp p => p | .copy p => p | .draw p _ => p
  | .convert p _ => p | .rom p => p | .load p _ => p | .matvec p _ => p | .kcall p _ _ => p
  | .toNat p => p

/-- The constant polynomial $1$ if the classes agree, $0$ otherwise. -/
def ep6_ind (c d : ℕ) : ep6_Poly := if d = c then [(1, 0, 0, 0)] else []

private theorem ep6_ev_ind (N L F c d : ℕ) :
    ep6_ev N L F (ep6_ind c d) = if d = c then 1 else 0 := by
  unfold ep6_ind; split_ifs <;> simp [ep6_ev]

/-- **A crude count of the operations of class `c`**: loops by their trip-count bound times the
body at the largest index, index binders by the body at the bound, branches by their sum. -/
def ep6_C {P ι : Type} (c : ℕ) :
    {nb ni : ℕ} → FStmt P ι nb ni → (Fin ni → ep6_Poly) → ep6_Poly
  | _, _, .skip, _ => []
  | _, _, .seq s t, σ => ep6_C c s σ ++ ep6_C c t σ
  | _, _, .instr i, _ =>
      ep6_ind c (ep6_cls ((i.subst (fun _ => 0) (fun _ => .const 0)).kind (ι := ι)))
  | _, _, .apply _ _ _ _ _ _ cols, σ => ep6_ind c 4 ++ ep6_pmul (ep6_up σ cols) (ep6_ind c 8)
  | _, _, .rom _ _ _, _ => ep6_ind c 5
  | _, _, .alloc _ _ b, σ => ep6_C c b σ
  | _, _, .loop n b, σ => ep6_pmul (ep6_up σ n) (ep6_C c b (ep6_snoc σ (ep6_up σ n)))
  | _, _, .whileFuel f _ _ _ _ b, σ => ep6_pmul (ep6_up σ f) (ep6_ind c 6 ++ ep6_C c b σ)
  | _, _, .ite _ _ _ _ t e, σ => ep6_ind c 6 ++ (ep6_C c t σ ++ ep6_C c e σ)
  | _, _, .named _ _ b, σ => ep6_C c b σ
  | _, _, .kcall _ _ _ _ _, _ => ep6_ind c 9
  | _, _, .bindIdx _ _ bd b, σ => ep6_ind c 7 ++ ep6_C c b (ep6_snoc σ (ep6_up σ bd))

/-- A crude bound on the additional live cells (sums for maxima). -/
def ep6_Cc {P ι : Type} : {nb ni : ℕ} → FStmt P ι nb ni → (Fin ni → ep6_Poly) → ep6_Poly
  | _, _, .seq s t, σ => ep6_Cc s σ ++ ep6_Cc t σ
  | _, _, .alloc _ len b, σ => ep6_up σ len ++ ep6_Cc b σ
  | _, _, .loop n b, σ => ep6_Cc b (ep6_snoc σ (ep6_up σ n))
  | _, _, .whileFuel _ _ _ _ _ b, σ => ep6_Cc b σ
  | _, _, .ite _ _ _ _ t e, σ => ep6_Cc t σ ++ ep6_Cc e σ
  | _, _, .named _ _ b, σ => ep6_Cc b σ
  | _, _, .bindIdx _ _ bd b, σ => ep6_Cc b (ep6_snoc σ (ep6_up σ bd))
  | _, _, _, _ => []

/-- The tags of a tree. -/
def ep6_tags {P ι : Type} : {nb ni : ℕ} → FStmt P ι nb ni → List P
  | _, _, .skip => []
  | _, _, .seq s t => ep6_tags s ++ ep6_tags t
  | _, _, .instr i => [ep6_ktag ((i.subst (fun _ => 0) (fun _ => .const 0)).kind (ι := ι))]
  | _, _, .apply _ p _ _ _ _ _ => [p]
  | _, _, .rom p _ _ => [p]
  | _, _, .alloc p _ b => p :: ep6_tags b
  | _, _, .loop _ b => ep6_tags b
  | _, _, .whileFuel _ p _ _ _ b => p :: ep6_tags b
  | _, _, .ite p _ _ _ t e => p :: (ep6_tags t ++ ep6_tags e)
  | _, _, .named _ _ b => ep6_tags b
  | _, _, .kcall _ p _ _ _ => [p]
  | _, _, .bindIdx p _ _ b => p :: ep6_tags b

theorem ep6_sum_le {α : Type} [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (l : List ℕ) (f : ℕ → α) (B : α) (h : ∀ i ∈ l, f i ≤ B) :
    (l.map f).sum ≤ l.length • B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, succ_nsmul']
    exact add_le_add (h a List.mem_cons_self) (ih fun i hi => h i (List.mem_cons_of_mem a hi))

omit [DecidableEq P] in
private theorem ep6_supRange_count_le {f : ℕ → StaticCost P ι} {m B : ℕ} {κ : OpKind P ι}
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

omit [DecidableEq P] in
private theorem ep6_supRange_cells_le {f : ℕ → StaticCost P ι} {m B : ℕ} {q : P}
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

omit [DecidableEq P] in
private theorem ep6_single_le (k κ : OpKind P ι) :
    (Finsupp.single k 1 : OpCount P ι) κ ≤ if ep6_cls k = ep6_cls κ then 1 else 0 := by
  classical
  rw [Finsupp.single_apply]
  split_ifs with h1 h2 <;> simp_all

/-- The crude count bounds the static count of every kind by its class. -/
theorem ep6_count_le (w : P → ℕ) (κ : OpKind P ι) (N L F : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ) (σ : Fin ni → ep6_Poly),
      (∀ v, ρ v ≤ ep6_ev N L F (σ v)) →
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ ≤
        ep6_ev N L F (ep6_C (ep6_cls κ) s σ) := by
  intro nb ni s
  induction s with
  | skip => intro ρ σ _; simp [FStmt.staticCost, StaticCost.zero]
  | seq s t ihs iht =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply, ep6_C, ep6_ev_append]
    exact Nat.add_le_add (ihs ρ σ h) (iht ρ σ h)
  | instr i =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, ep6_C, ep6_ev_ind]
    exact ep6_single_le _ _
  | apply o p d dOff s sOff cols =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.step, ep6_C, ep6_ev_append, ep6_ev_pmul, ep6_ev_ind,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Nat.add_le_add (ep6_single_le _ _)
      (Nat.mul_le_mul (ep6_evalIn_le_up h cols) (ep6_single_le _ _))
  | rom p d i =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, ep6_C, ep6_ev_ind]
    exact ep6_single_le _ _
  | alloc p len body ih =>
    intro ρ σ h
    exact ih ρ σ h
  | loop n body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply, ep6_C, ep6_ev_pmul]
    have hn := ep6_evalIn_le_up h n
    refine (ep6_sum_le _ _ (ep6_ev N L F (ep6_C (ep6_cls κ) body
      (ep6_snoc σ (ep6_up σ n)))) ?_).trans ?_
    · intro i hi
      exact ih _ _ (ep6_snoc_le h ((List.mem_range.mp hi).le.trans hn))
    · rw [List.length_range, smul_eq_mul]
      exact Nat.mul_le_mul_right _ hn
  | whileFuel fuel p c x y body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, ep6_C, ep6_ev_pmul, ep6_ev_append,
      ep6_ev_ind]
    exact Nat.mul_le_mul (ep6_evalIn_le_up h fuel) (Nat.add_le_add (ep6_single_le _ _) (ih ρ σ h))
  | ite p c x y t e iht ihe =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply, ep6_C, ep6_ev_append, ep6_ev_ind]
    exact Nat.add_le_add (ep6_single_le _ _) (max_le ((iht ρ σ h).trans (Nat.le_add_right _ _))
      ((ihe ρ σ h).trans (Nat.le_add_left _ _)))
  | named name args body ih =>
    intro ρ σ h
    exact ih ρ σ h
  | kcall o p dims ins outs =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, ep6_C, ep6_ev_ind]
    exact ep6_single_le _ _
  | bindIdx p x bound body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply, ep6_C,
      ep6_ev_append, ep6_ev_ind]
    exact Nat.add_le_add (ep6_single_le _ _) (ep6_supRange_count_le fun k hk => ih _ _
      (ep6_snoc_le h ((Nat.lt_succ_iff.mp hk).trans (ep6_evalIn_le_up h bound))))

/-- The crude cell bound bounds the static workspace. -/
theorem ep6_cells_le (charge : OpKind P ι → OpCount P ι) (w : P → ℕ) (q : P)
    (N L F : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ) (σ : Fin ni → ep6_Poly),
      (∀ v, ρ v ≤ ep6_ev N L F (σ v)) →
      (s.staticCost charge w ρ).cells q ≤ ep6_ev N L F (ep6_Cc s σ) := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, ep6_Cc, ep6_ev_append]
    exact max_le ((ihs ρ σ h).trans (Nat.le_add_right _ _))
      ((iht ρ σ h).trans (Nat.le_add_left _ _))
  | alloc p len body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.alloc, ep6_Cc, ep6_ev_append]
    refine Nat.add_le_add ?_ (ih ρ σ h)
    split_ifs
    · exact ep6_evalIn_le_up h len
    · exact Nat.zero_le _
  | loop n body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, ep6_Cc]
    exact StaticCost.sequence_cells_le _ _ _ _ fun i hi => ih _ _ (ep6_snoc_le h
      ((List.mem_range.mp hi).le.trans (ep6_evalIn_le_up h n)))
  | whileFuel fuel p c x y body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step, ep6_Cc]
    exact max_le (Nat.zero_le _) (ih ρ σ h)
  | ite p c x y t e iht ihe =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, StaticCost.branch, ep6_Cc,
      ep6_ev_append]
    exact max_le (Nat.zero_le _) (max_le ((iht ρ σ h).trans (Nat.le_add_right _ _))
      ((ihe ρ σ h).trans (Nat.le_add_left _ _)))
  | named name args body ih =>
    intro ρ σ h
    exact ih ρ σ h
  | bindIdx p x bound body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, ep6_Cc]
    exact max_le (Nat.zero_le _) (ep6_supRange_cells_le fun k hk => ih _ _
      (ep6_snoc_le h ((Nat.lt_succ_iff.mp hk).trans (ep6_evalIn_le_up h bound))))
  | _ => intro ρ σ _; simp [FStmt.staticCost, StaticCost.step, StaticCost.zero]

/-- A kind whose tag is not a tag of the tree is not counted. -/
theorem ep6_count_tag (w : P → ℕ) (κ : OpKind P ι) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ), ep6_ktag κ ∉ ep6_tags s →
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ ≤ 0 := by
  classical
  have hs : ∀ k : OpKind P ι, ep6_ktag κ ≠ ep6_ktag k →
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
    simp only [ep6_tags, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply]
    exact Nat.add_le_add (ihs ρ h.1) (iht ρ h.2)
  | instr i =>
    intro ρ h
    simp only [ep6_tags, List.mem_singleton] at h
    exact hs _ h
  | apply o p d dOff s sOff cols =>
    intro ρ h
    simp only [ep6_tags, List.mem_singleton] at h
    simp only [FStmt.staticCost, StaticCost.step, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rw [Nat.le_zero.mp (hs (.load p o) h), Nat.le_zero.mp (hs (.matvec p o) h)]
    simp
  | rom p d i =>
    intro ρ h
    simp only [ep6_tags, List.mem_singleton] at h
    exact hs _ h
  | alloc p len body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    exact ih ρ h.2
  | loop n body ih =>
    intro ρ h
    simp only [ep6_tags] at h
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply]
    refine (ep6_sum_le _ _ 0 fun i _ => ih _ h).trans ?_
    simp
  | whileFuel fuel p c x y body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
    have h1 := hs (.cmp p) h.1
    have h2 := ih ρ h.2
    simp_all
  | ite p c x y t e iht ihe =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply]
    have h1 := hs (.cmp p) h.1
    have h2 := iht ρ h.2.1
    have h3 := ihe ρ h.2.2
    omega
  | named name args body ih =>
    intro ρ h
    exact ih ρ h
  | kcall o p dims ins outs =>
    intro ρ h
    simp only [ep6_tags, List.mem_singleton] at h
    exact hs _ h
  | bindIdx p x bound body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply]
    exact Nat.add_le_add (hs (.toNat p) h.1) (ep6_supRange_count_le fun k _ => ih _ h.2)

/-- A tag that is not a tag of the tree has no workspace. -/
theorem ep6_cells_tag (charge : OpKind P ι → OpCount P ι) (w : P → ℕ) (q : P) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ), q ∉ ep6_tags s →
      (s.staticCost charge w ρ).cells q ≤ 0 := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    intro ρ h
    simp only [ep6_tags, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq]
    exact max_le (ihs ρ h.1) (iht ρ h.2)
  | alloc p len body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.alloc, if_neg h.1, zero_add]
    exact ih ρ h.2
  | loop n body ih =>
    intro ρ h
    simp only [ep6_tags] at h
    simp only [FStmt.staticCost]
    exact StaticCost.sequence_cells_le _ _ _ _ fun i _ => ih _ h
  | whileFuel fuel p c x y body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step]
    exact max_le (Nat.zero_le _) (ih ρ h.2)
  | ite p c x y t e iht ihe =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, StaticCost.branch]
    exact max_le (Nat.zero_le _) (max_le (iht ρ h.2.1) (ihe ρ h.2.2))
  | named name args body ih =>
    intro ρ h
    exact ih ρ h
  | bindIdx p x bound body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step]
    exact max_le (Nat.zero_le _) (ep6_supRange_cells_le fun k _ => ih _ h.2)
  | _ => intro ρ _; simp [FStmt.staticCost, StaticCost.step, StaticCost.zero]

/-- The polynomial environment of the sizes $(N, \ell_0, F)$. -/
def ep6_σ0 : Fin 3 → ep6_Poly :=
  fun v =>
    if v.val = 0 then [(1, 1, 0, 0)] else if v.val = 1 then [(1, 0, 1, 0)] else [(1, 0, 0, 1)]

/-- The check of a scalar class: degrees at most $(3, 1, 1)$ and coefficients summing to at most
$1024$. -/
def ep6_okS (p : ep6_Poly) : Bool :=
  p.all (fun e => e.2.1 ≤ 3 && e.2.2.1 ≤ 1 && e.2.2.2 ≤ 1) && decide ((p.map (·.1)).sum ≤ 1024)

/-- The check of the workspace: degrees at most $(2, 1, 0)$, coefficients of the terms without
$\ell_0$ summing to at most $192$, with $\ell_0$ to at most $64$. -/
def ep6_okC (p : ep6_Poly) : Bool :=
  p.all (fun e => e.2.1 ≤ 2 && e.2.2.1 ≤ 1 && e.2.2.2 = 0) &&
    decide ((p.map fun e => if e.2.2.1 = 0 then e.1 else 0).sum ≤ 192) &&
    decide ((p.map fun e => if e.2.2.1 = 0 then 0 else e.1).sum ≤ 64)

def ep6_mI {P P' VB VI : Type} (f : P → P') : Instr P VB VI → Instr P' VB VI
  | .lit p d q => .lit (f p) d q
  | .litIdx p d e => .litIdx (f p) d e
  | .bin p b d x y => .bin (f p) b d x y
  | .un p u d x => .un (f p) u d x
  | .copy p d s => .copy (f p) d s
  | .draw p dist d => .draw (f p) dist d
  | .convert p q d s => .convert (f p) (f q) d s

/-- A tree with its tags and oracle names renamed. -/
def ep6_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    {nb ni : ℕ} → FStmt P ι nb ni → FStmt P' ι' nb ni
  | _, _, .skip => .skip
  | _, _, .seq s t => .seq (ep6_map f g s) (ep6_map f g t)
  | _, _, .instr i => .instr (ep6_mI f i)
  | _, _, .apply o p d dOff s sOff cols => .apply (g o) (f p) d dOff s sOff cols
  | _, _, .rom p d i => .rom (f p) d i
  | _, _, .alloc p len b => .alloc (f p) len (ep6_map f g b)
  | _, _, .loop n b => .loop n (ep6_map f g b)
  | _, _, .whileFuel fu p c x y b => .whileFuel fu (f p) c x y (ep6_map f g b)
  | _, _, .ite p c x y t e => .ite (f p) c x y (ep6_map f g t) (ep6_map f g e)
  | _, _, .named n a b => .named n a (ep6_map f g b)
  | _, _, .kcall o p d i o' => .kcall (g o) (f p) d i o'
  | _, _, .bindIdx p x bd b => .bindIdx (f p) x bd (ep6_map f g b)

omit [DecidableEq P] in
set_option maxRecDepth 100000 in
/-- The registered tree is the tree at the tags `Unit` and oracle names `Bool`, renamed. -/
theorem ep6_compiled_map (p : P) (mm qr : ι) : eighProg.compiled p mm qr =
    ep6_map (fun _ => p) (fun b => bif b then mm else qr) (eighProg.compiled () true false) := rfl

/-- A tree of kernel calls: the skeleton of a first-order tree that carries its kernel counts. -/
inductive ep6_KT (P ι : Type) : ℕ → Type
  | skip {ni : ℕ} : ep6_KT P ι ni
  | seq {ni : ℕ} (a b : ep6_KT P ι ni) : ep6_KT P ι ni
  | loop {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι (ni + 1)) : ep6_KT P ι ni
  | rep {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι ni) : ep6_KT P ι ni
  | br {ni : ℕ} (a b : ep6_KT P ι ni) : ep6_KT P ι ni
  | bind {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι (ni + 1)) : ep6_KT P ι ni
  | call {ni : ℕ} (o : ι) (p : P) (d : List (IExp (Fin ni))) : ep6_KT P ι ni

def ep6_sseq {P ι : Type} {ni : ℕ} : ep6_KT P ι ni → ep6_KT P ι ni → ep6_KT P ι ni
  | .skip, b => b
  | a, .skip => a
  | a, b => .seq a b

def ep6_sloop {P ι : Type} {ni : ℕ} (n : IExp (Fin ni)) :
    ep6_KT P ι (ni + 1) → ep6_KT P ι ni
  | .skip => .skip
  | b => .loop n b

def ep6_srep {P ι : Type} {ni : ℕ} (n : IExp (Fin ni)) : ep6_KT P ι ni → ep6_KT P ι ni
  | .skip => .skip
  | b => .rep n b

def ep6_sbr {P ι : Type} {ni : ℕ} : ep6_KT P ι ni → ep6_KT P ι ni → ep6_KT P ι ni
  | .skip, b => b
  | a, .skip => a
  | a, b => .br a b

def ep6_sbind {P ι : Type} {ni : ℕ} (n : IExp (Fin ni)) :
    ep6_KT P ι (ni + 1) → ep6_KT P ι ni
  | .skip => .skip
  | b => .bind n b

/-- The kernel calls of a tree. -/
def ep6_prune {P ι : Type} : {nb ni : ℕ} → FStmt P ι nb ni → ep6_KT P ι ni
  | _, _, .seq s t => ep6_sseq (ep6_prune s) (ep6_prune t)
  | _, _, .alloc _ _ b => ep6_prune b
  | _, _, .loop n b => ep6_sloop n (ep6_prune b)
  | _, _, .whileFuel f _ _ _ _ b => ep6_srep f (ep6_prune b)
  | _, _, .ite _ _ _ _ t e => ep6_sbr (ep6_prune t) (ep6_prune e)
  | _, _, .named _ _ b => ep6_prune b
  | _, _, .kcall o p d _ _ => .call o p d
  | _, _, .bindIdx _ _ bd b => ep6_sbind bd (ep6_prune b)
  | _, _, _ => .skip

def ep6_v {ni : ℕ} (i : ℕ) (h : i < ni := by decide) : IExp (Fin ni) := .var ⟨i, h⟩

/-- The split of a node (depth $10$ variables). -/
def ep6_Dsplit {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 10 :=
  .seq (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5]) (.seq (.call qr p [ep6_v 5, ep6_v 5])
    (.seq (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5]) (.seq (.call qr p [ep6_v 5, ep6_v 5])
    (.seq (.call mm p [ep6_v 8, ep6_v 5, ep6_v 5]) (.seq (.call mm p [ep6_v 8, ep6_v 5, ep6_v 8])
    (.seq (.call mm p [.sub (ep6_v 5) (ep6_v 8), ep6_v 5, ep6_v 5])
      (.call mm p [.sub (ep6_v 5) (ep6_v 8), ep6_v 5, .sub (ep6_v 5) (ep6_v 8)])))))))

def ep6_D9 {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 9 :=
  .loop (.sub (.const 1) (.sub (.const 1) (.mul (ep6_v 8) (.sub (ep6_v 5) (ep6_v 8)))))
    (ep6_Dsplit p mm qr)

def ep6_D8 {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 8 :=
  .seq (.seq (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5])
      (.loop (ep6_v 2) (.seq (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5])
        (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5]))))
    (.bind (ep6_v 5) (ep6_D9 p mm qr))

def ep6_D6 {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 6 :=
  .loop (.sub (.const 1) (.sub (.const 1) (ep6_v 5)))
    (.loop (.sub (.const 1) (.sub (.const 1) (.sub (ep6_v 5) (.const 1)))) (ep6_D8 p mm qr))

def ep6_U10 {P ι : Type} (p : P) (mm : ι) : ep6_KT P ι 10 :=
  .seq (.call mm p [ep6_v 5, ep6_v 9, ep6_v 9])
    (.call mm p [ep6_v 5, .sub (ep6_v 5) (ep6_v 9), .sub (ep6_v 5) (ep6_v 9)])

def ep6_U9 {P ι : Type} (p : P) (mm : ι) : ep6_KT P ι 9 :=
  .bind (ep6_v 5) (ep6_U10 p mm)

def ep6_U8 {P ι : Type} (p : P) (mm : ι) : ep6_KT P ι 8 :=
  .loop (.sub (.const 1) (.sub (.const 1)
    (.mul (.sub (.const 1) (.sub (ep6_v 7) (.const 4)))
      (.sub (.const 1) (.sub (.const 4) (ep6_v 7))))))
    (ep6_U9 p mm)

def ep6_U6 {P ι : Type} (p : P) (mm : ι) : ep6_KT P ι 6 :=
  .loop (.sub (.const 1) (.sub (.const 1) (ep6_v 5))) (.bind (.const 4) (ep6_U8 p mm))

/-- The kernel calls of `NLAlib.eighProg.compiled`. -/
def ep6_T {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 3 :=
  .seq (.loop (.add (ep6_v 1) (.const 1)) (.loop (ep6_v 0) (.bind (.sub (ep6_v 0) (ep6_v 4))
      (ep6_D6 p mm qr))))
    (.loop (.add (ep6_v 1) (.const 1)) (.loop (ep6_v 0) (.bind (.sub (ep6_v 0) (ep6_v 4))
      (ep6_U6 p mm))))

set_option maxRecDepth 100000 in
private theorem ep6_prune_compiled0 :
    ep6_prune (eighProg.compiled () true false) = ep6_T () true false := rfl

theorem ep6_okC_compiled0 :
    ep6_okC (ep6_Cc (eighProg.compiled () true false) ep6_σ0) = true := by decide +kernel

theorem ep6_okS_compiled0 : ∀ c ∈ [1, 2, 6, 7, 10, 11, 12, 13, 20, 23, 30, 32],
    ep6_okS (ep6_C c (eighProg.compiled () true false) ep6_σ0) = true := by decide +kernel

theorem ep6_zero_compiled0 : ∀ c ∈ [3, 4, 5, 8, 14, 21, 31],
    ep6_C c (eighProg.compiled () true false) ep6_σ0 = [] := by decide +kernel

/-! #### Renaming -/

theorem ep6_C_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') (c : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (σ : Fin ni → ep6_Poly),
      ep6_C c (ep6_map f g s) σ = ep6_C c s σ := by
  intro nb ni s
  induction s with
  | instr i => intro σ; cases i <;> rfl
  | _ => intro σ; simp only [ep6_map, ep6_C, *]

theorem ep6_Cc_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (σ : Fin ni → ep6_Poly),
      ep6_Cc (ep6_map f g s) σ = ep6_Cc s σ := by
  intro nb ni s
  induction s with
  | _ => intro σ; simp only [ep6_map, ep6_Cc, *]

theorem ep6_tags_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni), ep6_tags (ep6_map f g s) = (ep6_tags s).map f := by
  intro nb ni s
  induction s with
  | instr i => cases i <;> rfl
  | _ => simp only [ep6_map, ep6_tags, List.map_append, List.map_cons, List.map_nil, *]

/-- Renaming a tree of kernel calls. -/
private def ep6_KTmap {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    {ni : ℕ} → ep6_KT P ι ni → ep6_KT P' ι' ni
  | _, .skip => .skip
  | _, .seq a b => .seq (ep6_KTmap f g a) (ep6_KTmap f g b)
  | _, .loop n b => .loop n (ep6_KTmap f g b)
  | _, .rep n b => .rep n (ep6_KTmap f g b)
  | _, .br a b => .br (ep6_KTmap f g a) (ep6_KTmap f g b)
  | _, .bind n b => .bind n (ep6_KTmap f g b)
  | _, .call o p d => .call (g o) (f p) d

private theorem ep6_prune_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni),
      ep6_prune (ep6_map f g s) = ep6_KTmap f g (ep6_prune s) := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    simp only [ep6_map, ep6_prune, ihs, iht]
    cases ep6_prune s <;> cases ep6_prune t <;> rfl
  | loop n b ih =>
    simp only [ep6_map, ep6_prune, ih]
    cases ep6_prune b <;> rfl
  | whileFuel fu p c x y b ih =>
    simp only [ep6_map, ep6_prune, ih]
    cases ep6_prune b <;> rfl
  | ite p c x y t e iht ihe =>
    simp only [ep6_map, ep6_prune, iht, ihe]
    cases ep6_prune t <;> cases ep6_prune e <;> rfl
  | bindIdx p x bd b ih =>
    simp only [ep6_map, ep6_prune, ih]
    cases ep6_prune b <;> rfl
  | alloc p len b ih => simp only [ep6_map, ep6_prune, ih]
  | named n a b ih => simp only [ep6_map, ep6_prune, ih]
  | _ => rfl

omit [DecidableEq P] in
theorem ep6_prune_compiled (p : P) (mm qr : ι) :
    ep6_prune (eighProg.compiled p mm qr) = ep6_T p mm qr := by
  rw [ep6_compiled_map, ep6_prune_map, ep6_prune_compiled0]
  rfl

end NLAlib
