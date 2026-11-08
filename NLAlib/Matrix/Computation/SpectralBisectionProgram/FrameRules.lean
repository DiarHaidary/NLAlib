/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Computation.StaticCost
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Computation.Loops

/-!
# A Hoare logic for the weighted kernel count of the spectral bisection program

The weighted kernel count of a run of `NLAlib.eighProg`, by an invariant of the run: `NLAlib.ep7_HT`
is a Hoare triple for the cost and for the cells of one tracked buffer (the size arena), and
`NLAlib.ep7_BW` is the same for a builder that keeps the tracked buffer, through any continuation.
Frame rules for every block that does not write the tracked buffer; no semantic contract, the
kernels are arbitrary.

## Main results

* `NLAlib.ep7_ht_seq`, `NLAlib.ep7_ht_run`, `NLAlib.ep7_sf_run`: the rules.
* `NLAlib.ep7_ht_slot`: a slot of the downward pass.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! ### EP7 helpers

The weighted kernel count of a run, by an invariant of the run: `ep7_HT` is a Hoare triple
for the cost and for the cells of one tracked buffer (the size arena `Sz`); `ep7_BW` is the
same for a builder that keeps the tracked buffer, through any continuation. -/

section EP7

omit [AddMonoid C] [Inhabited K]

/-- The weight of an operation kind: `T` of the largest dimension of a kernel call. -/
def ep7_wt (T : ℕ → ℕ) : OpKind P ι → ℕ
  | .kcall _ _ ds => T (ds.foldr max 0)
  | _ => 0

/-- The cells of buffer `b` at tag `p`. -/
def ep7_V (s : Store P K) (p : P) (b : ℕ) : ℕ → Option K := fun i => s.read p b i

/-- Every successful run of `s` from a state whose buffer `b` reads `V₀` adds at most `c T(m)` to
the weighted count and ends with buffer `b` satisfying `Q`. -/
def ep7_HT (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (V₀ : ℕ → Option K) (s : Stmt P ι ℕ ℕ) (c : ℕ) (Q : (ℕ → Option K) → Prop) : Prop :=
  Monotone T → (∀ κ, I.charge κ = Finsupp.single κ 1) → ∀ st st' : St P K (OpCount P ι),
    b < st.store.size → ep7_V st.store p b = V₀ → exec I s st = some st' →
    Finsupp.weight (ep7_wt T) st'.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt + c * T m ∧
      Q (ep7_V st'.store p b)

/-- A statement that keeps buffer `b` and costs at most `c T(m)`. -/
def ep7_SF (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (s : Stmt P ι ℕ ℕ) (c : ℕ) : Prop :=
  ∀ V₀, ep7_HT I T p b m V₀ s c (· = V₀)

/-- The run of a builder with a continuation. -/
def ep7_run (x : Builder P ι ℕ ℕ Unit) (k : Unit → Stmt P ι ℕ ℕ) : Stmt P ι ℕ ℕ :=
  @ContT.run (Stmt P ι ℕ ℕ) Id Unit x k

/-- A builder that keeps buffer `b` and costs at most `c T(m)`, through every continuation. -/
def ep7_BW (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (x : Builder P ι ℕ ℕ Unit) (c : ℕ) : Prop :=
  ∀ (k : Unit → Stmt P ι ℕ ℕ) (c' : ℕ) V₀ Q, ep7_HT I T p b m V₀ (k ()) c' Q →
    ep7_HT I T p b m V₀ (ep7_run x k) (c + c') Q

/-- The buffer an instruction writes. -/
def ep7_dst : Instr P ℕ ℕ → ℕ
  | .lit _ d _ => d.buf
  | .litIdx _ d _ => d.buf
  | .bin _ _ d _ _ => d.buf
  | .un _ _ d _ => d.buf
  | .copy _ d _ => d.buf
  | .draw _ _ d => d.buf
  | .convert _ _ d _ => d.buf

variable {I : Interp P ι K (OpCount P ι)} {T : ℕ → ℕ} {p : P} {b m : ℕ}

omit [DecidableEq P] in
private theorem ep7_wt_add (T : ℕ → ℕ) (c : OpCount P ι) (κ : OpKind P ι) :
    Finsupp.weight (ep7_wt T) (c + Finsupp.single κ 1) =
      Finsupp.weight (ep7_wt T) c + ep7_wt T κ := by
  rw [map_add, Finsupp.weight_single, one_smul]

theorem ep7_size {s : Stmt P ι ℕ ℕ} {st st' : St P K (OpCount P ι)}
    (h : exec I s st = some st') : st'.store.size = st.store.size :=
  Store.size_eq_of_shape_eq (shape_eq_of_exec_eq_some h)

theorem ep7_ht_mono {V₀ : ℕ → Option K} {s : Stmt P ι ℕ ℕ} {c c' m' : ℕ}
    {Q Q' : (ℕ → Option K) → Prop} (h : ep7_HT I T p b m V₀ s c Q) (hc : c ≤ c')
    (hm : m ≤ m') (hQ : ∀ V, Q V → Q' V) : ep7_HT I T p b m' V₀ s c' Q' := by
  intro hT hch st st' hb hV hex
  obtain ⟨h1, h2⟩ := h hT hch st st' hb hV hex
  exact ⟨h1.trans (Nat.add_le_add_left (Nat.mul_le_mul hc (hT hm)) _), hQ _ h2⟩

theorem ep7_ht_skip {V₀ : ℕ → Option K} {Q : (ℕ → Option K) → Prop} (hQ : Q V₀) :
    ep7_HT I T p b m V₀ .skip 0 Q := by
  intro _ _ st st' _ hV hex
  rw [exec_skip] at hex
  cases hex
  exact ⟨by omega, hV ▸ hQ⟩

theorem ep7_ht_seq {V₀ : ℕ → Option K} {s t : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ}
    {Q₁ Q : (ℕ → Option K) → Prop} (h₁ : ep7_HT I T p b m V₀ s c₁ Q₁)
    (h₂ : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ t c₂ Q) :
    ep7_HT I T p b m V₀ (.seq s t) (c₁ + c₂) Q := by
  intro hT hch st st' hb hV hex
  rw [exec_seq] at hex
  obtain ⟨st₁, hs, ht⟩ := Option.bind_eq_some_iff.mp hex
  obtain ⟨a1, a2⟩ := h₁ hT hch st st₁ hb hV hs
  obtain ⟨b1, b2⟩ := h₂ _ a2 hT hch st₁ st' (by rw [ep7_size hs]; exact hb) rfl ht
  refine ⟨?_, b2⟩
  rw [add_mul]
  omega

private theorem ep7_ht_alloc {V₀ : ℕ → Option K} {q : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {c : ℕ} {Q : (ℕ → Option K) → Prop} (h : ∀ h, b < h → ep7_HT I T p b m V₀ (body h) c Q) :
    ep7_HT I T p b m V₀ (.alloc q len body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  have hs₂ := ep7_size h₂
  simp only [Array.size_push] at hs₂
  obtain ⟨a1, a2⟩ := h st.store.size hb hT hch _ st₂ (by simp; omega)
    (by rw [← hV]; funext i; exact Store.read_push_of_lt hb) h₂
  refine ⟨a1, ?_⟩
  have : ep7_V (Array.pop st₂.store) p b = ep7_V st₂.store p b := by
    funext i; exact Store.read_pop_of_lt (by omega)
  simpa [this] using a2

private theorem ep7_ht_named {V₀ : ℕ → Option K} {nm : String} {args : List (Arg ℕ ℕ)}
    {body : Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ep7_HT I T p b m V₀ body c Q) : ep7_HT I T p b m V₀ (.named nm args body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_named] at hex
  exact h hT hch st st' hb hV hex

private theorem ep7_ht_ite {V₀ : ℕ → Option K} {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ}
    {t e : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ} {Q : (ℕ → Option K) → Prop}
    (ht : ep7_HT I T p b m V₀ t c₁ Q) (he : ep7_HT I T p b m V₀ e c₂ Q) :
    ep7_HT I T p b m V₀ (.ite q cmp x y t e) (c₁ + c₂) Q := by
  intro hT hch st st' hb hV hex
  rw [exec_ite] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold cmpStep at hr
  obtain ⟨a, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨a', -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp hr
  have hw : Finsupp.weight (ep7_wt T) (st.cnt + I.charge (.cmp q)) =
      Finsupp.weight (ep7_wt T) st.cnt := by
    rw [hch, ep7_wt_add]; rfl
  split_ifs at hex
  · obtain ⟨a1, a2⟩ := ht hT hch { st with cnt := st.cnt + I.charge (.cmp q) } st' hb hV hex
    refine ⟨?_, a2⟩
    rw [hw] at a1; rw [add_mul]; omega
  · obtain ⟨a1, a2⟩ := he hT hch { st with cnt := st.cnt + I.charge (.cmp q) } st' hb hV hex
    refine ⟨?_, a2⟩
    rw [hw] at a1; rw [add_mul]; omega

private theorem ep7_ht_bindIdx {V₀ : ℕ → Option K} {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ∀ v ≤ bound.eval, ep7_HT I T p b m V₀ (body v) c Q) :
    ep7_HT I T p b m V₀ (.bindIdx q x bound body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_bindIdx] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold toNatStep at hr
  obtain ⟨a, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp hr
  dsimp only at hex
  split_ifs at hex with hle
  obtain ⟨a1, a2⟩ := h _ hle hT hch { st with cnt := st.cnt + I.charge (.toNat q) } st' hb hV hex
  refine ⟨?_, a2⟩
  rw [hch, ep7_wt_add] at a1
  exact a1

/-- the value a binder reads from cell `i` of the tracked buffer -/
def ep7_f (I : Interp P ι K (OpCount P ι)) (p : P) (V : ℕ → Option K) (i : ℕ) : ℕ :=
  ((V i).bind (I.sem.toNat p)).getD 0

private theorem ep7_ht_bindIdx_read {V₀ : ℕ → Option K} {e : IExp ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ep7_HT I T p b m V₀ (body (min (ep7_f I p V₀ e.eval) bound.eval)) c Q) :
    ep7_HT I T p b m V₀ (.bindIdx p ⟨b, e⟩ bound body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_bindIdx] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold toNatStep at hr
  obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hr
  have hf : ep7_f I p V₀ e.eval = r' := by
    rw [← hV]; simp only [ep7_f, ep7_V]; rw [ha]; simp [hr']
  dsimp only at hex
  split_ifs at hex with hle
  rw [← min_eq_left hle, ← hf] at hex
  obtain ⟨a1, a2⟩ := h hT hch { st with cnt := st.cnt + I.charge (.toNat p) } st' hb hV hex
  refine ⟨?_, a2⟩
  rw [hch, ep7_wt_add] at a1
  exact a1

private theorem ep7_ht_loop0 {V₀ : ℕ → Option K} {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {Q : (ℕ → Option K) → Prop} (hn : n.eval = 0) (hQ : Q V₀) :
    ep7_HT I T p b m V₀ (.loop n body) 0 Q := by
  intro _ _ st st' _ hV hex
  rw [exec_loop, hn] at hex
  simp only [List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at hex
  subst hex
  exact ⟨by omega, hV ▸ hQ⟩

private theorem ep7_ht_loop1 {V₀ : ℕ → Option K} {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ}
    {Q : (ℕ → Option K) → Prop} (hn : n.eval = 1) (h : ep7_HT I T p b m V₀ (body 0) c Q) :
    ep7_HT I T p b m V₀ (.loop n body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_loop, hn] at hex
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil] at hex
  obtain ⟨s, hs, hex⟩ := Option.bind_eq_some_iff.mp hex
  simp only [Option.pure_def, Option.some.injEq] at hex
  subst hex
  exact h hT hch st s hb hV hs

theorem ep7_ht_litIdx {V₀ : ℕ → Option K} {e m' : IExp ℕ} :
    ep7_HT I T p b m V₀ (.instr (.litIdx p ⟨b, e⟩ m')) 0
      (· = Function.update V₀ e.eval (I.sem.lit p (m'.eval : ℚ))) := by
  intro _ hch st st' _ hV hex
  rw [exec_instr] at hex
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hex
  simp only [Instr.run] at hr
  obtain ⟨v, hv, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp hr
  refine ⟨?_, ?_⟩
  · rw [hch, ep7_wt_add]; simp [ep7_wt, Instr.kind]
  · rw [← hV, hv]
    funext i
    simp only [ep7_V]
    by_cases hi : i = e.eval
    · subst hi; rw [Function.update_self]; exact Store.read_of_write_eq_some hw
    · rw [Function.update_of_ne hi]; exact Store.read_of_write_eq_some_of_ne hw (Or.inr hi)

private theorem ep7_run_write {sem : ScalarSem P K} {tape : Dist → ℕ → K} {s : Store P K}
    {pos : Dist → ℕ} {r : Store P K × (Dist → ℕ)} (i : Instr P ℕ ℕ)
    (h : i.run sem tape s pos = some r) :
    ∃ q j v, s.write q (ep7_dst i) j v = some r.1 := by
  cases i with
  | lit p' d q' =>
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | litIdx p' d e =>
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | bin p' o d x y =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a', -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | un p' o d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | copy p' d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | draw p' dd d =>
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | convert p' q' d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩

omit [DecidableEq P] in
private theorem ep7_wt_kind (i : Instr P ℕ ℕ) : ep7_wt (ι := ι) T i.kind = 0 := by
  cases i <;> rfl

private theorem ep7_sf_instr {i : Instr P ℕ ℕ} (hi : ep7_dst i ≠ b) :
    ep7_SF I T p b m (.instr i) 0 := by
  intro V₀ _ hch st st' hb hV hex
  rw [exec_instr] at hex
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hex
  obtain ⟨q, j, v, hw⟩ := ep7_run_write i hr
  refine ⟨?_, ?_⟩
  · rw [hch, ep7_wt_add, ep7_wt_kind]; omega
  · rw [← hV]; funext i'
    exact Store.read_of_write_eq_some_of_ne hw (Or.inl (Ne.symm hi))

private theorem ep7_foldr_max_le {l : List ℕ} (h : ∀ x ∈ l, x ≤ m) : l.foldr max 0 ≤ m := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

private theorem ep7_mem_kcallBlocks {outs : List (ℕ × ℕ)} {lens : List ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ kcallBlocks outs lens) : ∃ y ∈ outs, x.1 = y.1 := by
  induction outs generalizing lens with
  | nil => simp [kcallBlocks] at hx
  | cons y outs ih =>
    cases lens with
    | nil => simp [kcallBlocks] at hx
    | cons l lens =>
      simp only [kcallBlocks, List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨y, by simp, rfl⟩
      · obtain ⟨y', hy', h⟩ := ih hx
        exact ⟨y', by simp [hy'], h⟩

private theorem ep7_sf_kcall {o : ι} {q : P} {dims : List (IExp ℕ)} {ins outs : List (ℕ × IExp ℕ)}
    (ho : ∀ x ∈ outs, x.1 ≠ b) (hd : ∀ d ∈ dims, d.eval ≤ m) :
    ep7_SF I T p b m (.kcall o q dims ins outs) 1 := by
  intro V₀ hT hch st st' hb hV hex
  simp only [exec] at hex
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hex
  unfold Interp.kcallStore at hs
  split_ifs at hs with hcond
  obtain ⟨xs, -, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨ys, -, hs⟩ := Option.bind_eq_some_iff.mp hs
  refine ⟨?_, ?_⟩
  · rw [hch, ep7_wt_add]
    simp only [ep7_wt, one_mul]
    refine Nat.add_le_add_left (hT (ep7_foldr_max_le ?_)) _
    intro x hx
    obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hx
    exact hd d hdm
  · rw [← hV]; funext i'
    refine Store.read_of_writeBlocks_eq_some_of_forall hs fun x hx => Or.inl ?_
    obtain ⟨y, hy, hxy⟩ := ep7_mem_kcallBlocks hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    rw [hxy]; exact Ne.symm (ho z hz)

private theorem ep7_sf_loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ}
    (h : ∀ i, ep7_SF I T p b m (body i) c) : ep7_SF I T p b m (.loop n body) (n.eval * c) := by
  intro V₀ hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun i s => b < s.store.size ∧ ep7_V s.store p b = V₀ ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt + i * c * T m)
    ⟨hb, hV, by simp⟩ (fun i _ s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      obtain ⟨a1, a2⟩ := h i V₀ hT hch s₁ s₂ h1 h2 hs
      refine ⟨by rw [ep7_size hs]; exact h1, a2, ?_⟩
      rw [add_mul, add_mul, one_mul]; omega) hex
  obtain ⟨-, h2, h3⟩ := this
  exact ⟨h3, h2⟩

private theorem ep7_sf_skip : ep7_SF I T p b m .skip 0 := fun _ => ep7_ht_skip rfl

/-! Builder rules -/

theorem ep7_bw_mono {x : Builder P ι ℕ ℕ Unit} {c c' : ℕ} (h : ep7_BW I T p b m x c)
    (hc : c ≤ c') : ep7_BW I T p b m x c' :=
  fun k c'' V₀ Q hk => ep7_ht_mono (h k c'' V₀ Q hk) (by omega) le_rfl fun _ h => h

theorem ep7_bw_pure : ep7_BW I T p b m (pure () : Builder P ι ℕ ℕ Unit) 0 :=
  fun _ _ _ _ hk => ep7_ht_mono hk (by omega) le_rfl fun _ h => h

theorem ep7_bw_bind {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    (hx : ep7_BW I T p b m x c₁) (hf : ep7_BW I T p b m (f ()) c₂) :
    ep7_BW I T p b m (x >>= f) (c₁ + c₂) := fun k c' V₀ Q hk =>
  ep7_ht_mono (hx (fun a => ep7_run (f a) k) (c₂ + c') V₀ Q (hf k c' V₀ Q hk)) (by omega)
    le_rfl fun _ h => h

private theorem ep7_ht_seq_sf {V₀ : ℕ → Option K} {s t : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ}
    {Q : (ℕ → Option K) → Prop} (h₁ : ep7_SF I T p b m s c₁) (h₂ : ep7_HT I T p b m V₀ t c₂ Q) :
    ep7_HT I T p b m V₀ (.seq s t) (c₁ + c₂) Q :=
  ep7_ht_seq (h₁ V₀) fun _ h => by subst h; exact h₂

private theorem ep7_bw_stmt {s : Stmt P ι ℕ ℕ} {c : ℕ} (h : ep7_SF I T p b m s c) :
    ep7_BW I T p b m (stmt s) c := fun _ _ _ _ hk => ep7_ht_seq_sf h hk

theorem ep7_bw_ins {i : Instr P ℕ ℕ} (hi : ep7_dst i ≠ b) : ep7_BW I T p b m (ins i) 0 :=
  ep7_bw_stmt (ep7_sf_instr hi)

theorem ep7_bw_kcall {o : ι} {q : P} {dims : List (IExp ℕ)} {ins outs : List (ℕ × IExp ℕ)}
    (ho : ∀ x ∈ outs, x.1 ≠ b) (hd : ∀ d ∈ dims, d.eval ≤ m) :
    ep7_BW I T p b m (stmt (.kcall o q dims ins outs)) 1 :=
  ep7_bw_stmt (ep7_sf_kcall ho hd)

theorem ep7_sf_run {x : Builder P ι ℕ ℕ Unit} {c : ℕ} (h : ep7_BW I T p b m x c) :
    ep7_SF I T p b m x.run c := fun V₀ =>
  ep7_ht_mono (h (fun _ => .skip) 0 V₀ _ (ep7_ht_skip (Q := (· = V₀)) rfl)) (by omega) le_rfl
    fun _ h => h

theorem ep7_bw_allocBind {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ h, b < h → ep7_BW I T p b m (f h) c) :
    ep7_BW I T p b m (alloc q len >>= f) c := fun k c' V₀ Q hk =>
  ep7_ht_alloc fun h' hh => h h' hh k c' V₀ Q hk

theorem ep7_bw_forRange {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ i, ep7_BW I T p b m (body i) c) : ep7_BW I T p b m (forRange n body) (n.eval * c) :=
  fun _ _ _ _ hk => ep7_ht_seq_sf (ep7_sf_loop fun i => ep7_sf_run (h i)) hk

theorem ep7_bw_scope {x : Builder P ι ℕ ℕ Unit} {c : ℕ} (h : ep7_BW I T p b m x c) :
    ep7_BW I T p b m (scope x) c := fun _ _ _ _ hk => ep7_ht_seq_sf (ep7_sf_run h) hk

theorem ep7_bw_named {nm : String} {args : List (Arg ℕ ℕ)} {x : Builder P ι ℕ ℕ Unit}
    {c : ℕ}
    (h : ep7_BW I T p b m x c) : ep7_BW I T p b m (named nm args x) c :=
  fun _ _ _ _ hk => ep7_ht_seq_sf (fun V₀ => ep7_ht_named (ep7_sf_run h V₀)) hk

theorem ep7_bw_ite {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ} {t e : Builder P ι ℕ ℕ Unit}
    {c₁ c₂ : ℕ} (ht : ep7_BW I T p b m t c₁) (he : ep7_BW I T p b m e c₂) :
    ep7_BW I T p b m (ifThenElse q cmp x y t e) (c₁ + c₂) := fun _ _ _ _ hk =>
  ep7_ht_seq_sf (fun V₀ => ep7_ht_ite (ep7_sf_run ht V₀) (ep7_sf_run he V₀)) hk

theorem ep7_bw_bindIdx {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ v ≤ bound.eval, ep7_BW I T p b m (body v) c) :
    ep7_BW I T p b m (bindIdx q x bound body) c := fun _ _ _ _ hk =>
  ep7_ht_seq_sf (fun V₀ => ep7_ht_bindIdx fun v hv => ep7_sf_run (h v hv) V₀) hk

theorem ep7_bw_when {e : IExp ℕ} {body : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ep7_BW I T p b m body c) : ep7_BW I T p b m (eighWhen e body) c := by
  unfold eighWhen
  refine ep7_bw_mono (ep7_bw_forRange fun _ => h) ?_
  simp only [IExp.eval_sub, IExp.eval_ofNat]
  exact (Nat.mul_le_mul_right c (show 1 - (1 - e.eval) ≤ 1 by omega)).trans (by simp)

theorem ep7_bw_bind0 {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    (hx : ep7_BW I T p b m x 0) (hf : ep7_BW I T p b m (f ()) 0) :
    ep7_BW I T p b m (x >>= f) 0 := ep7_bw_bind hx hf

theorem ep7_bw_forRange0 {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit}
    (h : ∀ i, ep7_BW I T p b m (body i) 0) : ep7_BW I T p b m (forRange n body) 0 :=
  ep7_bw_mono (ep7_bw_forRange h) (by simp)

theorem ep7_bw_ite0 {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ} {t e : Builder P ι ℕ ℕ Unit}
    (ht : ep7_BW I T p b m t 0) (he : ep7_BW I T p b m e 0) :
    ep7_BW I T p b m (ifThenElse q cmp x y t e) 0 := ep7_bw_ite ht he

local macro "ep7_side" : tactic => `(tactic| (simp only [ep7_dst, List.mem_cons, List.mem_singleton,
  forall_eq_or_imp, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
  IExp.eval_var, IExp.eval_add, IExp.eval_sub, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
  ne_eq, false_or, or_false, false_implies, forall_const, true_and] at * <;> omega))

local macro "ep7_z" : tactic => `(tactic| repeat (first
  | exact ep7_bw_pure
  | (apply ep7_bw_ins; ep7_side)
  | (apply ep7_bw_forRange0; intro _)
  | apply ep7_bw_scope
  | apply ep7_bw_named
  | apply ep7_bw_ite0
  | (apply ep7_bw_bindIdx; intro _ _)
  | apply ep7_bw_when
  | (apply ep7_bw_allocBind; intro _ _)
  | apply ep7_bw_bind0))

private theorem ep7_bw_zmirror {q : P} {n : IExp ℕ} {Y : ℕ} {yo : IExp ℕ} (hY : Y ≠ b) :
    ep7_BW I T p b m (zmirror q n Y yo) 0 := by
  unfold zmirror; ep7_z

theorem ep7_bw_zhermShift {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zhermShift q n X xo c Y yo) 0 := by
  unfold zhermShift; ep7_z

theorem ep7_bw_zhermScale {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zhermScale q n X xo c Y yo) 0 := by
  unfold zhermScale; ep7_z

theorem ep7_bw_zhermAvg {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zhermAvg q n X xo c Y yo) 0 := by
  unfold zhermAvg; ep7_z

theorem ep7_bw_zcopy {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zcopy q n n' X xo Y yo) 0 := by
  unfold zcopy; ep7_z

theorem ep7_bw_zneg {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zneg q n n' X xo Y yo) 0 := by
  unfold zneg; ep7_z

theorem ep7_bw_zconjTranspose {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zconjTranspose q n n' X xo Y yo) 0 := by
  unfold zconjTranspose; ep7_z

theorem ep7_bw_zidentity {q : P} {n : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zidentity q n Y yo) 0 := by
  unfold zidentity; ep7_z

theorem ep7_bw_ztraceRe {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {d : Cell ℕ ℕ}
    (hd : d.buf ≠ b) : ep7_BW I T p b m (ztraceRe q n X xo d) 0 := by
  unfold ztraceRe; ep7_z

theorem ep7_bw_zboxTest {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {lo hi fl : Cell ℕ ℕ}
    (hd : fl.buf ≠ b) : ep7_BW I T p b m (zboxTest q n n' X xo lo hi fl) 0 := by
  unfold zboxTest; ep7_z

local macro "ep7_k" : tactic => `(tactic| first
  | (with_reducible apply ep7_bw_zhermShift); ep7_side
  | (with_reducible apply ep7_bw_zhermScale); ep7_side
  | (with_reducible apply ep7_bw_zhermAvg); ep7_side
  | (with_reducible apply ep7_bw_zcopy); ep7_side
  | (with_reducible apply ep7_bw_zneg); ep7_side
  | (with_reducible apply ep7_bw_zconjTranspose); ep7_side
  | (with_reducible apply ep7_bw_zidentity); ep7_side
  | (with_reducible apply ep7_bw_ztraceRe); ep7_side
  | (with_reducible apply ep7_bw_zboxTest); ep7_side)

local macro "ep7_bw_tac" : tactic => `(tactic| repeat (first
  | (with_reducible exact ep7_bw_pure)
  | (with_reducible apply ep7_bw_ins); ep7_side
  | (with_reducible apply ep7_bw_kcall) <;> ep7_side
  | ep7_k
  | (with_reducible apply ep7_bw_forRange0); intro _; ep7_z; done
  | (with_reducible apply ep7_bw_forRange); intro _
  | (with_reducible apply ep7_bw_scope)
  | (with_reducible apply ep7_bw_named)
  | (with_reducible apply ep7_bw_ite)
  | (with_reducible apply ep7_bw_bindIdx); intro _ _
  | (with_reducible apply ep7_bw_when)
  | (with_reducible apply ep7_bw_allocBind); intro _ _
  | (with_reducible apply ep7_bw_bind)))

private theorem ep7_bw_nsTest {q : P} {mm : ι} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {W V : ℕ}
    {one lo hi fl : Cell ℕ ℕ} (hW : W ≠ b) (hV : V ≠ b) (hfl : fl.buf ≠ b) (hn : n.eval ≤ m) :
    ep7_BW I T p b m (newtonSchulzTestBlock q mm n X xo W V one lo hi fl) 1 := by
  unfold newtonSchulzTestBlock
  apply ep7_bw_mono
  · ep7_bw_tac
  · simp

private theorem ep7_bw_nsStep {q : P} {mm : ι} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {W V : ℕ}
    {c : Cell ℕ ℕ} (hX : X ≠ b) (hW : W ≠ b) (hV : V ≠ b) (hc : c.buf ≠ b) (hn : n.eval ≤ m) :
    ep7_BW I T p b m (newtonSchulzStepBlock q mm n X xo W V c) 1 := by
  unfold newtonSchulzStepBlock
  apply ep7_bw_mono
  · ep7_bw_tac
  · simp

theorem ep7_bw_sign {q : P} {mm : ι} {n F : IExp ℕ} {A : ℕ} {ao : IExp ℕ} {par : ℕ}
    {po : IExp ℕ} {X : ℕ} {xo : IExp ℕ} (hX : X ≠ b) (hn : n.eval ≤ m) :
    ep7_BW I T p b m (eighSignBlock q mm n F A ao par po X xo) (2 * F.eval + 1) := by
  unfold eighSignBlock
  apply ep7_bw_mono
  · repeat (first
      | (with_reducible apply ep7_bw_nsTest) <;> ep7_side
      | (with_reducible apply ep7_bw_nsStep) <;> ep7_side
      | (with_reducible exact ep7_bw_pure)
      | (with_reducible apply ep7_bw_ins); ep7_side
      | ep7_k
      | (with_reducible apply ep7_bw_forRange); intro _
      | (with_reducible apply ep7_bw_scope)
      | (with_reducible apply ep7_bw_ite)
      | (with_reducible apply ep7_bw_allocBind); intro _ _
      | (with_reducible apply ep7_bw_bind))
  · simp; omega

theorem ep7_bw_deflate {q : P} {mm qr : ι} {n k r lo : IExp ℕ} {side : ℕ} {Sg : ℕ}
    {sq : Cell ℕ ℕ} {Pm G Y Qf Rf Qa : ℕ} {qo : IExp ℕ} (hG : G ≠ b) (hY : Y ≠ b) (hQf : Qf ≠ b)
    (hRf : Rf ≠ b) (hQa : Qa ≠ b) (hk : k.eval ≤ m) :
    ep7_BW I T p b m (eighDeflateBlock q mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo) 2 := by
  unfold eighDeflateBlock
  apply ep7_bw_mono
  · ep7_bw_tac
  · simp

theorem ep7_bw_compress {q : P} {mm : ι} {k r : IExp ℕ} {Qa : ℕ} {qo : IExp ℕ} {Ma : ℕ}
    {mo co : IExp ℕ} {two sg : Cell ℕ ℕ} {Qh C1 C2 C3 : ℕ} (hMa : Ma ≠ b) (hQh : Qh ≠ b)
    (hC1 : C1 ≠ b) (hC2 : C2 ≠ b) (hC3 : C3 ≠ b) (hk : k.eval ≤ m) (hr : r.eval ≤ m) :
    ep7_BW I T p b m (eighCompressBlock q mm k r Qa qo Ma mo co two sg Qh C1 C2 C3) 2 := by
  unfold eighCompressBlock
  apply ep7_bw_mono
  · ep7_bw_tac
  · simp

theorem ep7_bw_leaf {q : P} {diag : Bool} {k : IExp ℕ} {Ma : ℕ} {mo : IExp ℕ} {Ua : ℕ}
    {uo : IExp ℕ} {Ea : ℕ} {eo : IExp ℕ} {kd : Cell ℕ ℕ} (hUa : Ua ≠ b) (hEa : Ea ≠ b)
    (hkd : kd.buf ≠ b) : ep7_BW I T p b m (eighLeafBlock q diag k Ma mo Ua uo Ea eo kd) 0 := by
  unfold eighLeafBlock
  cases diag <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ep7_z

theorem ep7_bw_clamp {q : P} {k : IExp ℕ} {x z kc : Cell ℕ ℕ} (hx : x.buf ≠ b)
    (hz : z.buf ≠ b) (hkc : kc.buf ≠ b) : ep7_BW I T p b m (eighClampBlock q k x z kc) 0 := by
  unfold eighClampBlock; ep7_z

/-! HT rules with continuations -/

section K

variable {V₀ : ℕ → Option K} {k : Unit → Stmt P ι ℕ ℕ} {Q : (ℕ → Option K) → Prop}

theorem ep7_ht_bwBindK {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    {c₁ c₂ : ℕ}
    (hx : ep7_BW I T p b m x c₁) (hf : ep7_HT I T p b m V₀ (ep7_run (f ()) k) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (x >>= f) k) (c₁ + c₂) Q :=
  hx (fun a => ep7_run (f a) k) c₂ V₀ Q hf

theorem ep7_ht_bwK {x : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    (hx : ep7_BW I T p b m x c₁) (hk : ep7_HT I T p b m V₀ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run x k) (c₁ + c₂) Q :=
  hx k c₂ V₀ Q hk

theorem ep7_ht_bindK {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ep7_HT I T p b m V₀ (ep7_run x (fun a => ep7_run (f a) k)) c Q) :
    ep7_HT I T p b m V₀ (ep7_run (x >>= f) k) c Q := h

theorem ep7_ht_allocK {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ h, b < h → ep7_HT I T p b m V₀ (ep7_run (f h) k) c Q) :
    ep7_HT I T p b m V₀ (ep7_run (alloc q len >>= f) k) c Q :=
  ep7_ht_alloc h

theorem ep7_ht_litK {e m' : IExp ℕ} {c : ℕ}
    (h : ep7_HT I T p b m (Function.update V₀ e.eval (I.sem.lit p (m'.eval : ℚ))) (k ()) c Q) :
    ep7_HT I T p b m V₀ (ep7_run (ins (.litIdx p ⟨b, e⟩ m')) k) c Q := by
  change ep7_HT I T p b m V₀ (.seq (.instr (.litIdx p ⟨b, e⟩ m')) (k ())) c Q
  exact ep7_ht_mono (ep7_ht_seq ep7_ht_litIdx fun _ h' => by subst h'; exact h) (by omega) le_rfl
    fun _ h => h

private theorem ep7_ht_whenK0 {e : IExp ℕ} {B : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (he : 1 - (1 - e.eval) = 0) (h : ep7_HT I T p b m V₀ (k ()) c Q) :
    ep7_HT I T p b m V₀ (ep7_run (eighWhen e B) k) c Q := by
  change ep7_HT I T p b m V₀ (.seq (.loop (1 - (1 - e)) fun _ => B.run) (k ())) c Q
  exact ep7_ht_mono (ep7_ht_seq (c₂ := c) (ep7_ht_loop0 (Q := (· = V₀)) (by simpa using he) rfl)
    fun _ h' => by rw [h']; exact h) (by omega) le_rfl fun _ h => h

private theorem ep7_ht_whenK1 {e : IExp ℕ} {B : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    {Q₁ : (ℕ → Option K) → Prop} (he : 1 - (1 - e.eval) = 1)
    (hB : ep7_HT I T p b m V₀ B.run c₁ Q₁) (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (eighWhen e B) k) (c₁ + c₂) Q :=
  ep7_ht_seq (ep7_ht_loop1 (n := 1 - (1 - e)) (body := fun _ => B.run) (by simpa using he) hB) h

theorem ep7_ht_scopeK {x : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hx : ep7_HT I T p b m V₀ x.run c₁ Q₁) (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (scope x) k) (c₁ + c₂) Q :=
  ep7_ht_seq hx h

private theorem ep7_ht_iteK {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ} {t e : Builder P ι ℕ ℕ Unit}
    {c₁ c₂ c₃ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (ht : ep7_HT I T p b m V₀ t.run c₁ Q₁) (he : ep7_HT I T p b m V₀ e.run c₂ Q₁)
    (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₃ Q) :
    ep7_HT I T p b m V₀ (ep7_run (ifThenElse q cmp x y t e) k) (c₁ + c₂ + c₃) Q :=
  ep7_ht_seq (ep7_ht_ite ht he) h

private theorem ep7_ht_bindIdxK {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hb : ∀ v ≤ bound.eval, ep7_HT I T p b m V₀ (body v).run c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (bindIdx q x bound body) k) (c₁ + c₂) Q :=
  ep7_ht_seq (ep7_ht_bindIdx hb) h

theorem ep7_ht_bindIdxReadK {e : IExp ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hb : ep7_HT I T p b m V₀ (body (min (ep7_f I p V₀ e.eval) bound.eval)).run c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (bindIdx p ⟨b, e⟩ bound body) k) (c₁ + c₂) Q :=
  ep7_ht_seq (ep7_ht_bindIdx_read hb) h

theorem ep7_ht_run {x : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ep7_HT I T p b m V₀ (ep7_run x fun _ => .skip) c Q) :
    ep7_HT I T p b m V₀ x.run c Q := h

theorem ep7_ht_forRangeK {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    {Q₁ : (ℕ → Option K) → Prop}
    (hl : ep7_HT I T p b m V₀ (.loop n fun i => (body i).run) c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (forRange n body) k) (c₁ + c₂) Q :=
  ep7_ht_seq hl h

theorem ep7_ht_skipK (hQ : Q V₀) : ep7_HT I T p b m V₀ ((fun _ => Stmt.skip) ()) 0 Q :=
  ep7_ht_skip hQ

end K

/-- the child block -/
private theorem ep7_ht_child {k : IExp ℕ} {Ma : ℕ} {mo mo' : IExp ℕ} {sg kd : Cell ℕ ℕ} {e : IExp ℕ}
    {code : ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hkd : kd.buf ≠ b) :
    ep7_HT I T p b m V₀ (eighChildBlock p k Ma mo mo' sg ⟨b, e⟩ kd code).run 0
      (· = Function.update V₀ e.eval (I.sem.lit p (k.eval : ℚ))) := by
  unfold eighChildBlock
  apply ep7_ht_mono (c := 0 + (0 + 0)) _ (by omega) le_rfl fun _ h => h
  apply ep7_ht_bwBindK (ep7_bw_zhermShift hMa)
  apply ep7_ht_bindK
  apply ep7_ht_litK
  apply ep7_ht_bwK (ep7_bw_ins ?_)
  · exact ep7_ht_skipK rfl
  · exact hkd

local macro "ep7_bwx" : tactic => `(tactic| first
  | (with_reducible apply ep7_bw_deflate) <;> ep7_side
  | (with_reducible apply ep7_bw_compress) <;> ep7_side
  | (with_reducible apply ep7_bw_sign) <;> ep7_side
  | (with_reducible apply ep7_bw_leaf) <;> ep7_side
  | (with_reducible apply ep7_bw_clamp) <;> ep7_side
  | (with_reducible apply ep7_bw_ins); ep7_side
  | (with_reducible apply ep7_bw_kcall) <;> ep7_side
  | ep7_k
  | ep7_bw_tac)

local macro "ep7_ht_tac" : tactic => `(tactic| repeat (first
  | (with_reducible apply ep7_ht_allocK); intro _ _
  | (with_reducible apply ep7_ht_bindK); (with_reducible apply ep7_ht_litK)
  | (with_reducible apply ep7_ht_litK)
  | (with_reducible apply ep7_ht_bwBindK); on_goal 1 => (ep7_bwx; done)
  | (with_reducible apply ep7_ht_bwK); on_goal 1 => (ep7_bwx; done)
  | exact ep7_ht_skipK rfl))

private theorem ep7_ht_split {mm qr : ι} {n d lo k kp : IExp ℕ} {Sg Pp Pm Ma Qa Kd Kp : ℕ}
    {two sg nsg sq : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk : k.eval ≤ m) (hkp : kp.eval ≤ k.eval) :
    ep7_HT I T p b m V₀
      (eighSplitBlock p mm qr n d lo k kp Sg Pp Pm Ma Qa b Kd Kp two sg nsg sq).run 8
      (· = Function.update (Function.update V₀ (eighSlotOff n (d + 1) lo).eval
        (I.sem.lit p (kp.eval : ℚ))) (eighSlotOff n (d + 1) (lo + kp)).eval
        (I.sem.lit p ((k - kp).eval : ℚ))) := by
  unfold eighSplitBlock
  apply ep7_ht_run
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply ep7_ht_scopeK
    · apply ep7_ht_run
      dsimp only
      ep7_ht_tac
    · intro V h; exact ep7_ht_skipK h.symm
  · norm_num

/-- the effect of a node step on the size cells -/
def ep7_RN (I : Interp P ι K (OpCount P ι)) (p : P) (V₀ : ℕ → Option K) (i₀ k : ℕ)
    (V : ℕ → Option K) : Prop :=
  ∃ kp ≤ k, ((kp = 0 ∨ kp = k) ∧ V = Function.update V₀ i₀ (I.sem.lit p (k : ℚ))) ∨
    (0 < kp ∧ kp < k ∧ V = Function.update (Function.update V₀ i₀ (I.sem.lit p (kp : ℚ)))
      (i₀ + kp) (I.sem.lit p ((k - kp : ℕ) : ℚ)))

private theorem ep7_ht_tail {mm qr : ι} {n d lo k : IExp ℕ} {Sg Pp Pm Ma Qa Kd Kp : ℕ}
    {two sg nsg sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk2 : 2 ≤ k.eval) (hkm : k.eval ≤ m) (v : ℕ)
    (hv : v ≤ k.eval) :
    ep7_HT I T p b m V₀ (do
        eighWhen (1 - (k - IExp.var v))
          (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) sg
            ⟨b, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 2)
        eighWhen (1 - IExp.var v)
          (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) nsg
            ⟨b, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 3)
        eighWhen (IExp.var v * (k - IExp.var v))
          (eighSplitBlock p mm qr n d lo k (IExp.var v) Sg Pp Pm Ma Qa b Kd Kp two sg nsg sqh)
        : Builder P ι ℕ ℕ Unit).run 8
      (ep7_RN I p V₀ (eighSlotOff n (d + 1) lo).eval k.eval) := by
  apply ep7_ht_run
  apply ep7_ht_bindK
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · -- the negative child
    apply ep7_ht_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_bindK
    apply ep7_ht_whenK1 (by simp) (ep7_ht_child hMa (by simpa using hKd))
    intro V₁ h₁
    apply ep7_ht_whenK0 (by simp)
    apply ep7_ht_skipK
    exact ⟨0, by omega, Or.inl ⟨Or.inl rfl, h₁⟩⟩
  rcases Nat.lt_or_ge v k.eval with hvk | hvk
  · -- a split
    apply ep7_ht_mono (c := 8 + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_bindK
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_whenK1 (by simp; have := Nat.mul_pos hv0 (Nat.sub_pos_of_lt hvk); omega)
      (ep7_ht_split hMa hQa hKd hKp hkm (by simp; omega))
    intro V₁ h₁
    apply ep7_ht_skipK
    refine ⟨v, by omega, Or.inr ⟨hv0, hvk, ?_⟩⟩
    rw [h₁]
    simp [eighSlotOff, Nat.add_assoc]
  · -- the positive child
    have hvk' : v = k.eval := by omega
    subst hvk'
    apply ep7_ht_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK1 (by simp) (ep7_ht_child hMa (by simpa using hKd))
    intro V₁ h₁
    apply ep7_ht_bindK
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_whenK0 (by simp)
    apply ep7_ht_skipK
    exact ⟨k.eval, le_rfl, Or.inl ⟨Or.inr rfl, h₁⟩⟩

private theorem ep7_ht_node {mm qr : ι} {n L F d lo k : IExp ℕ} {par Lv Su Sg Ma Qa Kd Kp : ℕ}
    {one two half negone sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk2 : 2 ≤ k.eval) (hkm : k.eval ≤ m) :
    ep7_HT I T p b m V₀ (eighNodeBlock p mm qr n L F d lo k par Lv Su Sg Ma Qa b Kd Kp one two
      half negone sqh).run (2 * F.eval + 9)
      (ep7_RN I p V₀ (eighSlotOff n (d + 1) lo).eval k.eval) := by
  unfold eighNodeBlock
  apply ep7_ht_run
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply ep7_ht_scopeK
    · apply ep7_ht_run
      dsimp only
      ep7_ht_tac
      exact ep7_ht_bindIdxK (fun v hv => ep7_ht_tail hMa hQa hKd hKp hk2 hkm v hv)
        fun V h => ep7_ht_skipK h
    · intro V h; exact ep7_ht_skipK h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega

/-- the body of a slot of a downward level, at the size `k` it reads -/
def ep7_downSlot (p : P) (mm qr : ι) (n L F d : IExp ℕ)
    (par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp t : ℕ)
    (one two half negone sqh : Cell ℕ ℕ) (lo k : ℕ) : Builder P ι ℕ ℕ Unit :=
  eighWhen (IExp.var k) do
    eighWhen (1 - (IExp.var k - 1))
      (eighLeafBlock p true (IExp.var k) Ma (eighBlockOff n d (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo)) Ea (eighSlotOff n d (IExp.var lo))
        ⟨Kd, eighSlotOff n d (IExp.var lo)⟩)
    eighWhen (IExp.var k - 1) do
      ins (.bin p .mul ⟨t, 4⟩ ⟨Lv, 2 * d + 1⟩ ⟨par, 0⟩)
      ifThenElse p .le ⟨Lv, 2 * d⟩ ⟨t, 4⟩
        (eighLeafBlock p false (IExp.var k) Ma (eighBlockOff n d (IExp.var lo)) Ua
          (eighBlockOff n d (IExp.var lo)) Ea (eighSlotOff n d (IExp.var lo))
          ⟨Kd, eighSlotOff n d (IExp.var lo)⟩)
        (eighNodeBlock p mm qr n L F d (IExp.var lo) (IExp.var k) par Lv Su Sg Ma Qa Sz Kd Kp one
          two half negone sqh)

theorem ep7_ht_slot {mm qr : ι} {n L F d : IExp ℕ} {par Lv Su Sg Ma Ua Qa Ea Kd Kp t : ℕ}
    {one two half negone sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hUa : Ua ≠ b)
    (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b) (ht : t ≠ b) (lo k : ℕ)
    (hkm : k ≤ m) :
    ep7_HT I T p b m V₀ (ep7_downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp t one two
      half negone sqh lo k).run (2 * F.eval + 9)
      (fun V => V = V₀ ∨
        (2 ≤ k ∧ ep7_RN I p V₀ (eighSlotOff n (d + 1) (IExp.var lo)).eval k V)) := by
  unfold ep7_downSlot
  apply ep7_ht_run
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · apply ep7_ht_mono (c := 0) _ (by omega) le_rfl fun _ h => h
      exact ep7_ht_whenK0 (by simp) (ep7_ht_skipK (Or.inl rfl))
    · have hk1 : k = 1 := by omega
      subst hk1
      apply ep7_ht_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
      apply ep7_ht_whenK1 (by simp) _ fun V h => ep7_ht_skipK h
      apply ep7_ht_run
      apply ep7_ht_bindK
      apply ep7_ht_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
      apply ep7_ht_whenK1 (by simp) (ep7_sf_run (ep7_bw_leaf hUa hEa (by simpa using hKd)) V₀)
      intro V₁ h₁
      apply ep7_ht_whenK0 (by simp)
      exact ep7_ht_skipK (Or.inl h₁)
  · apply ep7_ht_mono (c := (2 * F.eval + 9) + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK1 (by simp; omega) _ fun V h => ep7_ht_skipK h
    apply ep7_ht_run
    apply ep7_ht_bindK
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_mono (c := (2 * F.eval + 9) + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK1 (by simp; omega) _ fun V h => ep7_ht_skipK h
    apply ep7_ht_run
    apply ep7_ht_mono (c := 0 + (0 + (2 * F.eval + 9) + 0)) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_bwBindK (ep7_bw_ins (by simpa [ep7_dst] using ht))
    apply ep7_ht_iteK (Q₁ := fun V => V = V₀ ∨ (2 ≤ k ∧
      ep7_RN I p V₀ (eighSlotOff n (d + 1) (IExp.var lo)).eval k V))
    · exact ep7_ht_mono (ep7_sf_run (ep7_bw_leaf hUa hEa (by simpa using hKd)) V₀) le_rfl le_rfl
        fun V h => Or.inl h
    · exact ep7_ht_mono (ep7_ht_node hMa hQa hKd hKp (by simpa using hk) (by simpa using hkm))
        le_rfl le_rfl fun V h => Or.inr ⟨hk, by simpa using h⟩
    · intro V h; exact ep7_ht_skipK h

end EP7

end NLAlib
