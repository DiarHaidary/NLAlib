/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Matrix.Computation.SpectralBisectionTape
public import NLAlib.Matrix.Computation.NewtonSchulzSignProgram

/-!
# The sign step of the spectral bisection program

The sign block of the node step of `NLAlib.eighProg` (`NLAlib.eighSignBlock`) runs the Newton–Schulz
iteration with the shallow step limit, a bounded loop that stops at the first iterate that passes
the test: under kernels that are routines on pairs and a semantics that decides flags, a successful
run writes the sign `NLAlib.newtonSchulzSign` of the machine of the semantics, and under the
standard model it always succeeds (unlike the `whileFuel` loop of `NLAlib.newtonSchulzSignProg`, it
does not fail when no iterate passes the test).

## Main results

* `NLAlib.holds_of_exec_eighSignLoop`, `NLAlib.holds_of_exec_eighSignBlock`: what a successful run
  computes.
* `NLAlib.exists_exec_eighSignBlock`: the sign step succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The sign iteration as routine specifications -/

/-- One step of the bounded Newton–Schulz loop on matrices: keep $\mathbf{B}$ if it passes the
test at threshold $\eta$, else take the rounded step. -/
def eighSignIter {Su Sg : Type} (M : FloatMachine K Su Sg) (η : K) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) (K × K)) : Matrix (Fin n) (Fin n) (K × K) :=
  if newtonSchulzTest M η B then B else newtonSchulzRounded M B

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- **The bounded Newton–Schulz loop is the iterate of its step**: a matrix that passes the test
is a fixed point. No printed source. -/
theorem newtonSchulzLoop_eq_iterate {Su Sg : Type} (M : FloatMachine K Su Sg) (η : K) {n : ℕ}
    (N : ℕ) (A : Matrix (Fin n) (Fin n) (K × K)) :
    newtonSchulzLoop M η N A = (eighSignIter M η)^[N] A := by
  induction N generalizing A with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, newtonSchulzLoop]
    by_cases ht : newtonSchulzTest M η A
    · rw [if_pos ht, show eighSignIter M η A = A from if_pos ht]
      exact (Function.iterate_fixed (show eighSignIter M η A = A from if_pos ht) N).symm
    · rw [if_neg ht, ih, show eighSignIter M η A = newtonSchulzRounded M A from if_neg ht]

/-- The state the bounded Newton–Schulz loop keeps between iterations: the iterate
$\mathbf{B}$ at `xo` of `X`, $\mathrm{mm}(\mathbf{B}, \mathbf{B})$ at offset $0$ of `W`, the
threshold $\eta$, the machine's one and $-\eta$ in the cells $0$, $3$, $4$ of `t`, and in the
cell $1$ the flag of the test of $\mathbf{B}$. -/
def EighSignState {Su Sg : Type} (M : FloatMachine K Su Sg) (p : P) {n : ℕ} (X xo W t : ℕ) (η : K)
    (B : Matrix (Fin n) (Fin n) (K × K)) (s : Store P K) : Prop :=
  pairLayout.Holds s p X xo B ∧ pairLayout.Holds s p W 0 (M.mm B B) ∧ s.read p t 0 = some η ∧
    s.read p t 3 = some M.one ∧ s.read p t 4 = some (M.neg η) ∧
    s.read p t 1 = some (if newtonSchulzTest M η B then M.zero else M.one)

/-- **One iteration of the bounded Newton–Schulz loop as a routine specification**: from the loop
state at $\mathbf{B}$, the conditional step modifies only the cells of `t`, the scratch blocks
of `V`, `W` and the block at `X`, and ends in the loop state at `NLAlib.eighSignIter M η B`,
keeping the tape positions; in mode `total` it also succeeds, given the standard model at
$u(p) < 1$ and the blocks writable. The semantics decides flags at `p`. No printed source. -/
theorem spec_eighSignIter {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} (p : P)
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p) (n : ℕ) {X W V t : ℕ} {xo : IExp ℕ} (η : K)
    (B : Matrix (Fin n) (Fin n) (K × K)) (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V)
    (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V) :
    RoutineSpec md I (fun st => EighSignState (I.sem.toFloatMachine p toNat mmR qrR unif normal)
        p X xo.eval W t η B st.store ∧ md.Needs (Writable st.store p t 0 5 ∧
          Writable st.store p V 0 (n * n * 2) ∧ Writable st.store p W 0 (n * n * 2) ∧
          Writable st.store p X xo.eval (n * n * 2)))
      (ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩ (do
          newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (pure ()))
      [(t, 0, 5), matBlock V 0 n n 2, matBlock W 0 n n 2, matBlock X xo.eval n n 2]
      fun st st' => EighSignState (I.sem.toFloatMachine p toNat mmR qrR unif normal) p X xo.eval
        W t η (eighSignIter (I.sem.toFloatMachine p toNat mmR qrR unif normal) η B) st'.store ∧
        PosKept st st' := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  obtain ⟨z, o, hz, ho, hzo, hoo⟩ := hflag
  have hM0 : M.zero = z := by simp [M, ScalarSem.toFloatMachine, hz]
  have hM1 : M.one = o := by simp [M, ScalarSem.toFloatMachine, ho]
  have hcell : ∀ i j : ℕ, i ≠ j → blockDisjoint (t, i, 1) (t, j, 1) = true := fun i j h => by
    simp [blockDisjoint]; omega
  -- the step and the test, by the call rule
  have hT : RoutineSpec md I (fun st => EighSignState M p X xo.eval W t η B st.store ∧
        md.Needs (Writable st.store p t 0 5 ∧ Writable st.store p V 0 (n * n * 2) ∧
          Writable st.store p W 0 (n * n * 2) ∧ Writable st.store p X xo.eval (n * n * 2)))
      (do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      [(t, 0, 5), matBlock V 0 n n 2, matBlock W 0 n n 2, matBlock X xo.eval n n 2]
      fun st st' => EighSignState M p X xo.eval W t η (newtonSchulzRounded M B) st'.store ∧
        PosKept st st' := by
    refine ⟨(executionComposable_newtonSchulzStepBlock _ _ _ _ _ _ _ _).bind
      (executionComposable_newtonSchulzTestBlock _ _ _ _ _ _ _ _ _ _ _),
      fun st ⟨⟨hX, hW, h0, h3, h4, _⟩, hN⟩ => ?_⟩
    have hw := fun {fp} {s : Store P K} (hm : Modifies fp st.store s) => hN.mono fun h =>
      (⟨h.1.of_modifies hm, h.2.1.of_modifies hm, h.2.2.1.of_modifies hm,
        h.2.2.2.of_modifies hm⟩ : _ ∧ _ ∧ _ ∧ _)
    exact (spec_newtonSchulzStepBlock (toNat := toNat) (qrR := qrR) (unif := unif)
        (normal := normal) hmm md p hsem n (c := ⟨t, 2⟩) B hWX hVX hWV htW htV
        (blockDisjoint_of_fst_ne htX)).wp_bind_keep
        (f := fun _ => newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (readsOnly_cellsHold _) (by fp_omega [htW, htV, htX])
        ⟨hX, hW, hN.mono fun h => ⟨h.1.of_le (by simp) (by simp), h.2⟩⟩
        (((cellsHold_nil _).cons h0).cons h4 |>.cons h3)
      fun st₁ hm₁ h₁ hC₁ => (spec_newtonSchulzTestBlock (toNat := toNat) (qrR := qrR) (unif := unif)
        (normal := normal) hmm md (hsem.mono (·.1)) p n (X := X) (W := W) (V := V) (xo := xo)
        (one := ⟨t, 3⟩) (lo := ⟨t, 4⟩) (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) η _ hWX hWV
        (by simp [htW, htV]) (hcell 1 4 (by omega)) (hcell 1 0 (by omega))).wp_run_keep
        ((readsOnly_cellsHold _).and (readsOnly_pairLayoutHolds p X xo.eval _))
        (by fp_omega [htW, htV, hWX, hVX, htX])
        ⟨h₁.1, hC₁.read (.head _), hC₁.read (.tail _ (.head _)),
          hC₁.read (.tail _ (.tail _ (.head _))),
          (hw hm₁).mono fun h => ⟨h.2.2.1, h.2.1, h.1.of_le (by simp) (by simp)⟩⟩ ⟨hC₁, h₁.1⟩
      fun st₂ hm₂ h₂ ⟨hC₂, hX₂⟩ => ⟨(hm₁.trans hm₂).of_sub (by simp [matBlock]), ⟨hX₂, h₂.1,
        hC₂.read (.tail _ (.tail _ (.head _))), hC₂.read (.head _), hC₂.read (.tail _ (.head _)),
        h₂.2.2.1⟩, h₂.2.2.2.trans h₁.2⟩
  refine (RoutineSpec.ifThenElse (r := !newtonSchulzTest M η B) hT
    (routineSpec_pure (pre := fun _ => True))
    (fun st ⟨⟨_, _, _, h3, _, h1⟩, _⟩ => ⟨_, _, h1, h3, ?_⟩) (fun st hst _ => hst)
    (fun _ _ _ => trivial)).conseq (fun _ h => h) (fun _ h => h) fun st st' hst ⟨hTr, hEf⟩ => ?_
  · by_cases ht : newtonSchulzTest M η B
    · obtain rfl := hEf (by simp [ht])
      rw [show eighSignIter M η B = B from if_pos ht]
      exact ⟨hst.1, rfl⟩
    · rw [show eighSignIter M η B = newtonSchulzRounded M B from if_neg ht]
      exact (hTr (by simp [ht])).imp id fun h => h
  · cases newtonSchulzTest M η B
    · simpa [hM1] using hoo
    · simpa [hM0, hM1] using hzo

/-- **The bounded Newton–Schulz loop as a routine specification**: from the loop state at
$\mathbf{A}$, the loop of $F$ conditional steps modifies only the cells of `t`, the scratch
blocks of `V`, `W` and the block at `X`, and ends in the loop state at
`NLAlib.newtonSchulzLoop M η F A`, keeping the tape positions; in mode `total` it also
succeeds, given the standard model at $u(p) < 1$ and the blocks writable. The semantics decides
flags at `p`. No printed source. -/
theorem spec_eighSignLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} (p : P)
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {X W V t : ℕ} {xo : IExp ℕ} (η : K)
    (A : Matrix (Fin n) (Fin n) (K × K)) (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V)
    (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V) :
    RoutineSpec md I (fun st => EighSignState (I.sem.toFloatMachine p toNat mmR qrR unif normal)
        p X xo.eval W t η A st.store ∧ md.Needs (Writable st.store p t 0 5 ∧
          Writable st.store p V 0 (n * n * 2) ∧ Writable st.store p W 0 (n * n * 2) ∧
          Writable st.store p X xo.eval (n * n * 2)))
      (forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩ (do
          newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (pure ()))
      [(t, 0, 5), matBlock V 0 n n 2, matBlock W 0 n n 2, matBlock X xo.eval n n 2]
      fun st st' => EighSignState (I.sem.toFloatMachine p toNat mmR qrR unif normal) p X xo.eval
        W t η (newtonSchulzLoop (I.sem.toFloatMachine p toNat mmR qrR unif normal) η F A)
          st'.store ∧ PosKept st st' := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  refine (RoutineSpec.forRange (fun _ => [(t, 0, 5), matBlock V 0 n n 2, matBlock W 0 n n 2,
      matBlock X xo.eval n n 2]) (fun st₀ k st => EighSignState M p X xo.eval W t η
        ((eighSignIter M η)^[k] A) st.store ∧ md.Needs (Writable st.store p t 0 5 ∧
          Writable st.store p V 0 (n * n * 2) ∧ Writable st.store p W 0 (n * n * 2) ∧
          Writable st.store p X xo.eval (n * n * 2)) ∧ PosKept st₀ st)
      (fun _ h => ⟨h.1, h.2, rfl⟩) fun st₀ _ k _ => ?_).conseq (fun _ h => h)
      (fun x hx => by obtain ⟨_, -, hx⟩ := List.mem_flatMap.mp hx; exact hx)
      fun _ _ _ h => ⟨by rw [newtonSchulzLoop_eq_iterate]; exact h.1, h.2.2⟩
  exact ((spec_eighSignIter hmm md p hsem hflag n (xo := xo) η _ hWX hVX hWV htX htW htV).spec
    |>.with_modifies).conseq (fun _ h => ⟨h.1, h.2.1⟩) (fun _ h => h)
    fun _ _ h ⟨hm, hS, hp⟩ => ⟨by rw [Function.iterate_succ_apply']; exact hS,
      h.2.1.mono fun w => ⟨w.1.of_modifies hm, w.2.1.of_modifies hm, w.2.2.1.of_modifies hm,
        w.2.2.2.of_modifies hm⟩, hp.trans h.2.2⟩

/-- **The body of the sign step as a routine specification**, at its scratch handles `t`
(five cells), `W`, `V`: from a state holding $\mathbf{A}$ at `ao` of `A` and $\varepsilon$, $b$
in the cells `po`, `po + 1` of `par`, with the output block at `xo` of `X` disjoint from both,
the run computes $\eta = \mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$, the scaled
$\mathbf{A}/b$ at `X`, its test and the bounded loop; it modifies only the scratch and the output
block, which then holds `NLAlib.newtonSchulzSign M ε b F A`, and keeps the tape positions; in mode
`total` it also succeeds, given the standard model on the range `safe` holding everywhere, at
$u(p) < 1$, with $n \ge 1$, $b$ decoding to a nonzero value and the blocks writable. The
semantics decides flags at `p`. No printed source. -/
theorem spec_eighSignBody {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop} (p : P) (n F : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1 ∧ 0 < n))
    (hflag : I.sem.DecidesFlags p) {A par X t W V : ℕ} {ao po xo : IExp ℕ}
    (A₀ : Matrix (Fin n) (Fin n) (K × K)) (ε b : K)
    (hXA : blockDisjoint (matBlock X xo.eval n n 2) (matBlock A ao.eval n n 2) = true)
    (hXp : blockDisjoint (matBlock X xo.eval n n 2) (par, po.eval, 2) = true)
    (htA : n = 0 ∨ t ≠ A) (htp : t ≠ par)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V) :
    RoutineSpec md I (fun st => pairLayout.Holds st.store p A ao.eval A₀ ∧
        st.store.read p par po.eval = some ε ∧ st.store.read p par (po.eval + 1) = some b ∧
        md.Needs (dec p b ≠ 0 ∧ Writable st.store p t 0 5 ∧ Writable st.store p V 0 (n * n * 2) ∧
          Writable st.store p W 0 (n * n * 2) ∧ Writable st.store p X xo.eval (n * n * 2)))
      (do
        ins (.litIdx p ⟨t, 2⟩ (4 * .const n))
        ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
        ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
        ins (.lit p ⟨t, 3⟩ 1)
        zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
        forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
          (do
            newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
            newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
          (pure ()) : Builder P ι ℕ ℕ Unit)
      [(t, 0, 5), matBlock V 0 n n 2, matBlock W 0 n n 2, matBlock X xo.eval n n 2]
      fun st st' => pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
        PosKept st st' := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  have hs : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem) :=
    hsem.mono fun h => h.1.mono_safe fun p x _ => h.2.1 p x
  have hsu : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem ∧ u p < 1) :=
    hsem.mono fun h => ⟨h.1.mono_safe fun p x _ => h.2.1 p x, h.2.2.1⟩
  have hAt : BlocksDisjoint [matBlock A ao.eval n n 2] [(t, 0, 5)] := by
    rcases htA with rfl | h
    · exact fun x hx y _ => by rw [List.mem_singleton.mp hx]; simp [matBlock, blockDisjoint]
    · exact blocksDisjoint_singleton_of_fst_ne (by simpa [matBlock] using Ne.symm h)
  refine ⟨by exec_composable, fun st ⟨hA, hε, hb, hN⟩ => ?_⟩
  have hw := fun {fp} {s : Store P K} (hm : Modifies fp st.store s) => hN.mono fun h =>
    (⟨h.2.1.of_modifies hm, h.2.2.1.of_modifies hm, h.2.2.2.1.of_modifies hm,
      h.2.2.2.2.of_modifies hm⟩ : _ ∧ _ ∧ _ ∧ _)
  have ht : ∀ {fp} {s : Store P K} (i : ℕ), i < 5 → Modifies fp st.store s →
      md.Needs (Writable s p t i 1) := fun i hi hm =>
    (hw hm).mono fun h => h.1.of_le (by omega) (by omega)
  -- the scalar prologue; the cells later steps read are kept in one bundle
  refine (RoutineSpec.ins (spec_litIdx_getD (p := p) (dst := ⟨t, 2⟩)
      (e := 4 * .const n))).wp_bind_keep
    (readsOnly_cellsHold [(p, par, po.eval, some ε), (p, par, po.eval + 1, some b)])
    (by fp_omega [htp]) (hsem.elim fun h => (ht 2 (by omega) (.refl [] _)).mono fun w =>
      ⟨h.1.lit_ok p _ (h.2.1 _ _), w⟩) (((cellsHold_nil _).cons hb).cons hε)
    fun st₁ hm₁ h₁ hC₁ => ?_
  refine (RoutineSpec.ins (spec_bin_getD (p := p) (op := .div) (dst := ⟨t, 0⟩)
      (x := ⟨par, po⟩) (y := ⟨t, 2⟩) (a := ε))).wp_bind_keep
    (readsOnly_cellsHold [(p, par, po.eval + 1, some b)]) (by fp_omega [htp])
    ⟨hC₁.read (by simp), h₁.1, hsem.elim fun h => (ht 0 (by omega) hm₁).mono fun w => ⟨by
      obtain ⟨v, hv⟩ := h.1.lit_ok p (((4 * IExp.const n).eval : ℕ) : ℚ) (h.2.1 _ _)
      refine h.1.bin_ok p .div ε _ trivial (fun _ => ?_) (h.2.1 _ _)
      rw [hv]
      exact h.1.dec_ne_zero_of_lit_eq_some h.2.2.1 (by simp; omega) hv, w⟩⟩
    (hC₁.sub (by simp)) fun st₂ hm₂ h₂ hC₂ => ?_
  refine (RoutineSpec.ins (spec_un_getD (p := p) (op := .neg) (dst := ⟨t, 4⟩)
      (x := ⟨t, 0⟩))).wp_bind_keep ((readsOnly_cellsHold _).and (readsOnly_cellsHold _))
    (by fp_omega [htp]) ⟨h₂.1, hsem.elim fun h => (ht 4 (by omega) (hm₁.trans hm₂)).mono fun w =>
      ⟨(h.1.neg p _).imp fun _ h => h.1, w⟩⟩ ⟨hC₂, (cellsHold_nil _).cons h₂.1⟩
    fun st₃ hm₃ h₃ ⟨hC₃, hT₃⟩ => ?_
  refine (RoutineSpec.ins (spec_lit_getD (p := p) (dst := ⟨t, 3⟩) (q := 1))).wp_bind_keep
    ((readsOnly_cellsHold _).and (readsOnly_cellsHold _)) (by fp_omega [htp])
    (hsem.elim fun h => (ht 3 (by omega) (hm₁.trans hm₂ |>.trans hm₃)).mono fun w =>
      ⟨h.1.lit_ok p 1 (h.2.1 _ _), w⟩) ⟨hC₃, hT₃.cons h₃.1⟩ fun st₄ hm₄ h₄ ⟨hC₄, hT₄⟩ => ?_
  have hm := ((hm₁.trans hm₂ |>.trans hm₃).trans hm₄).of_sub (fp' := [(t, 0, 5)]) (by simp)
  -- the scaled matrix, its test and the loop, the bundle kept across each call
  refine (spec_zhermScale (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
    (normal := normal) md hs p n (X := A) (Y := X) (xo := ao) (yo := xo) (c := ⟨par, po + 1⟩) b A₀
    hXA (by
      have := hXp; simp only [blockDisjoint_iff, matBlock, IExp.eval_add, IExp.eval_ofNat] at this ⊢
      omega)).wp_bind_keep (readsOnly_cellsHold _) (by fp_omega [htX])
    ⟨(readsOnly_pairLayoutHolds p A ao.eval A₀).of_modifies hA hm hAt, hC₄.read (by simp),
      hN.mono fun w => ⟨w.1, w.2.2.2.2.of_modifies hm⟩⟩ (hT₄.cons h₄.1) fun st₅ hm₅ h₅ hC₅ => ?_
  refine (spec_newtonSchulzTestBlock (toNat := toNat) (qrR := qrR) (unif := unif)
    (normal := normal) hmm md hs p n (X := X) (W := W) (V := V) (xo := xo) (one := ⟨t, 3⟩)
    (lo := ⟨t, 4⟩) (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) (M.div ε (M.ofNat (4 * n))) _ hWX hWV
    (by simp [htW, htV]) (by simp [blockDisjoint]) (by simp [blockDisjoint])).wp_bind_keep
    ((readsOnly_cellsHold _).and (readsOnly_pairLayoutHolds p X xo.eval _))
    (by fp_omega [htW, htV, hWX, hVX, htX])
    ⟨h₅.1, hC₅.read (.head _), hC₅.read (.tail _ (.head _)),
      hC₅.read (.tail _ (.tail _ (.head _))),
      (hw (hm.trans hm₅)).mono fun w => ⟨w.2.2.1, w.2.1, w.1.of_le (by simp) (by simp)⟩⟩
    ⟨hC₅, h₅.1⟩ fun st₆ hm₆ h₆ ⟨hC₆, hX₆⟩ => ?_
  refine (spec_eighSignLoop hmm md p hsu hflag n F (xo := xo) (M.div ε (M.ofNat (4 * n))) _
    hWX hVX hWV htX htW htV).wp_run ⟨⟨hX₆, h₆.1, hC₆.read (.tail _ (.tail _ (.head _))),
      hC₆.read (.head _), hC₆.read (.tail _ (.head _)), h₆.2.2.1⟩, hw (hm.trans hm₅ |>.trans hm₆)⟩
    fun st₇ hm₇ h₇ => ?_
  exact ⟨(hm.trans hm₅ |>.trans hm₆ |>.trans hm₇).of_sub (by simp [matBlock]), h₇.1.1,
    h₇.2.trans (h₆.2.2.2.trans (h₅.2.trans (h₄.2.trans (h₃.2.trans (h₂.2.trans h₁.2)))))⟩

/-- **The sign step as a routine specification**: from a state of $s_0$ buffers holding the
$n \times n$ matrix $\mathbf{A}$ at `ao` of `A` and $\varepsilon$, $b$ in the cells `po`,
`po + 1` of `par`, with the output block at `xo` of the buffer `X` ($X < s_0$) disjoint from
both, the run of `NLAlib.eighSignBlock` modifies only the output block, which then holds
`NLAlib.newtonSchulzSign M ε b F A` ($M$ the machine of the semantics at `p` with product `mmR`),
and keeps the tape positions; in mode `total` it also succeeds, given the standard model on the
range `safe` holding everywhere, at $u(p) < 1$, with $n \ge 1$, $b$ decoding to a nonzero value and
the output block writable. The semantics decides flags at `p`. No printed source. -/
theorem spec_eighSignBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop} (p : P) (n F : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1 ∧ 0 < n))
    (hflag : I.sem.DecidesFlags p) {A par X : ℕ} {ao po xo : IExp ℕ}
    (A₀ : Matrix (Fin n) (Fin n) (K × K)) (ε b : K)
    (hXA : blockDisjoint (matBlock X xo.eval n n 2) (matBlock A ao.eval n n 2) = true)
    (hXp : blockDisjoint (matBlock X xo.eval n n 2) (par, po.eval, 2) = true) {s₀ : ℕ}
    (hXs : X < s₀) (hAs : n = 0 ∨ A < s₀) (hps : par < s₀) :
    RoutineSpec md I (fun st => st.store.size = s₀ ∧ pairLayout.Holds st.store p A ao.eval A₀ ∧
        st.store.read p par po.eval = some ε ∧ st.store.read p par (po.eval + 1) = some b ∧
        md.Needs (dec p b ≠ 0 ∧ Writable st.store p X xo.eval (n * n * 2)))
      (eighSignBlock p mm (.const n) (.const F) A ao par po X xo) [matBlock X xo.eval n n 2]
      fun st st' => pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
        PosKept st st' := by
  refine RoutineSpec.scope (Spec.allocBind_named (b := s₀) (fun _ h => h.1)
    (Spec.allocBind_named (b := s₀ + 1) ?_ (Spec.allocBind_named (b := s₀ + 2) ?_ ?_)))
  · rintro _ ⟨st, h, rfl⟩
    rw [St.size_allocate, h.1]
  · rintro _ ⟨_, ⟨st, h, rfl⟩, rfl⟩
    rw [St.size_allocate, St.size_allocate, h.1]
  refine ((spec_eighSignBody (toNat := toNat) (qrR := qrR) (unif := unif) (normal := normal)
    hmm md p n F hsem hflag (t := s₀) (W := s₀ + 1) (V := s₀ + 2)
    (X := X) A₀ ε b hXA hXp (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)).spec.with_modifies.sub ?_).conseq ?_ (fun _ h => h) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
      List.nil_append, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left, matBlock,
      IExp.eval_ofNat, IExp.eval_mul, IExp.eval_const]
    have e : 0 + n * n * 2 ≤ 0 + 2 * (n * n) := Nat.le_of_eq (by ring)
    exact ⟨.inr (.inl ⟨trivial, le_rfl, le_rfl⟩), .inr (.inr (.inr ⟨trivial, le_rfl, e⟩)),
      .inr (.inr (.inl ⟨trivial, le_rfl, e⟩)), .inl ⟨trivial, le_rfl, le_rfl⟩⟩
  · rintro _ ⟨_, ⟨_, ⟨st, ⟨hs, hA, hε, hb, hN⟩, rfl⟩, rfl⟩, rfl⟩
    have h1 := St.size_allocate st p (IExp.eval 5) (I.width p)
    have h2 := St.size_allocate (st.allocate p (IExp.eval 5) (I.width p)) p
      (2 * (IExp.const n * IExp.const n)).eval (I.width p)
    have hr : ∀ {i : ℕ} {v : Option K}, st.store.read p par i = v → Store.read
        (((st.allocate p (IExp.eval 5) (I.width p)).allocate p
          (2 * (IExp.const n * IExp.const n)).eval (I.width p)).allocate p
          (2 * (IExp.const n * IExp.const n)).eval (I.width p)).store p par i = v := fun h => by
      rw [St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega), St.read_allocate_of_lt _ _ _ _ _ _ _
        (by omega), St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega), h]
    have wt := St.writable_allocate st p (IExp.eval 5) (I.width p)
    have wW := St.writable_allocate (st.allocate p (IExp.eval 5) (I.width p)) p
      (2 * (IExp.const n * IExp.const n)).eval (I.width p)
    have wV := St.writable_allocate ((st.allocate p (IExp.eval 5) (I.width p)).allocate p
      (2 * (IExp.const n * IExp.const n)).eval (I.width p)) p
      (2 * (IExp.const n * IExp.const n)).eval (I.width p)
    rw [hs] at wt
    rw [h1, hs] at wW
    rw [h2, h1, hs] at wV
    have hl : 0 + n * n * 2 ≤ 0 + (2 * (IExp.const n * IExp.const n)).eval :=
      Nat.le_of_eq (by simp; ring)
    refine ⟨?_, hr hε, hr hb, hN.mono fun ⟨hb0, hX⟩ => ⟨hb0, (wt.push _).push _,
      wV.of_le le_rfl hl, (wW.of_le le_rfl hl).push _, ((hX.push _).push _).push _⟩⟩
    rcases hAs with h0 | hA'
    · subst h0
      exact fun i => i.elim0
    · have hR := show ReadsOnly _ [matBlock A ao.eval n n 2] from
        readsOnly_entryLayoutHolds pairLayout p A ao.eval A₀
      exact hR.push (hR.push (hR.push hA (by simp [matBlock]; omega) _)
        (by simp [matBlock]; omega) _) (by simp [matBlock]; omega) _
  · intro s s' _ ⟨hm, hX, hp⟩ s₂ _ e₂ s₁ _ e₁ st hst e₀
    subst e₂ e₁ e₀
    have hsz := Store.size_eq_of_shape_eq hm.1
    simp only [St.size_allocate] at hsz
    have hR := show ReadsOnly _ [matBlock X xo.eval n n 2] from
      readsOnly_entryLayoutHolds (pairLayout (K := K)) p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀)
    have h₁ := hR.pop hX (by simp [matBlock]; omega)
    have h₂ := hR.pop h₁ (by simp [matBlock, Array.size_pop]; omega)
    exact ⟨hR.pop h₂ (by simp [matBlock, St.release, Array.size_pop]; omega), hp⟩

/-! ### The sign step's refinement and success lemmas -/

/-- The bounded Newton–Schulz loop computes `NLAlib.newtonSchulzLoop`: if kernel `mm` of `I`
is the routine `mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run
of the loop of `NLAlib.eighSignBlock` with $F$ iterations, from a state whose block at `X` holds
$\mathbf{A}$, whose scratch buffer `W` holds $\mathrm{mm}(\mathbf{A}, \mathbf{A})$, whose cells
$0$, $3$, $4$ of the scratch buffer `t` hold $\eta$, the machine's one and $-\eta$, and whose cell
$1$ holds the flag of the test of $\mathbf{A}$, ends with the block at `X` holding
`NLAlib.newtonSchulzLoop M η F A` ($M$ the machine of the semantics at `p` with product `mmR`);
every cell outside the block at `X` and the buffers `t`, `W`, `V` is unchanged, the store shape and
the tape positions too. No printed source. -/
theorem holds_of_exec_eighSignLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n F : ℕ) {X W V t : ℕ} {xo : IExp ℕ} {η : K}
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A))
    (hη : st.store.read p t 0 = some η)
    (hone : st.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hf : st.store.read p t 1 = some (if newtonSchulzTest
      (I.sem.toFloatMachine p toNat mmR qrR unif normal) η A then
        (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero else
        (I.sem.toFloatMachine p toNat mmR qrR unif normal).one))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (forRange (ι := ι) (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
      (do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      (pure ())).run st = some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzLoop (I.sem.toFloatMachine p toNat mmR qrR unif normal) η F A) ∧
      (∀ q b i, b ≠ t → b ≠ W → b ≠ V →
        blockDisjoint (b, i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  obtain ⟨hm, ⟨hX, -⟩, hp⟩ := (spec_eighSignLoop (u := fun _ => 0) (dec := fun _ _ => 0) hmm
    .liberal p trivial hflag n F (xo := xo) η A hWX hVX hWV htX htW htV).spec.holds_of_exec
    ⟨⟨hA, hW, hη, hone, hlo, hf⟩, trivial⟩ h
  exact ⟨hX, fun q b i hbt hbW hbV hbX => hm.2 q b i (by fp_omega [hbt, hbW, hbV, hbX]), hm.1,
    hp⟩

/-- The sign step computes `NLAlib.newtonSchulzSign`: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run of
`NLAlib.eighSignBlock` at size $n$ and step limit $F$, from a state whose block at `A` holds the
stored $\mathbf{A}$ and whose cells `po`, `po + 1` of `par` hold $\varepsilon$ and $b$, with the
output block at `X` disjoint from both and in an existing buffer at tag `p` of at least $2n^2$
cells from `xo` (so not one of the block's scratch buffers, which are popped at the end), ends
with the output block holding `NLAlib.newtonSchulzSign M ε b F A` (the machine of the semantics at
`p` with product `mmR`, for every choice of its other black boxes); every cell outside the output
block is unchanged, the store shape and the tape positions too. No printed source. -/
theorem holds_of_exec_eighSignBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X : ℕ} {ao po xo : IExp ℕ}
    {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {ε b : K}
    (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (h : exec I (eighSignBlock p mm (.const n) (.const F) A ao par po X xo).run st = some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
      (∀ q b' i, blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hps := Store.lt_size_of_read_eq_some hε
  obtain ⟨hm, hX', hp⟩ := (spec_eighSignBlock (u := fun _ => 0) (dec := fun _ _ => 0)
    (safe := fun _ _ => True) (toNat := toNat) (qrR := qrR) (unif := unif) (normal := normal) hmm
    .liberal p n F trivial hflag A₀ ε b (by fp_omega [hXA]) (by fp_omega [hXp])
    (hX.elim fun _ h => Store.size_shape st.store ▸ (Array.getElem?_eq_some_iff.mp h.1).1)
    (by rcases Nat.eq_zero_or_pos n with h0 | hn
        · exact .inl h0
        · exact .inr (Store.lt_size_of_read_eq_some (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩)))
    hps).spec.holds_of_exec ⟨rfl, hA, hε, hb, trivial⟩ h
  exact ⟨hX', fun q b' i hb' => hm.2 q b' i (by fp_omega [hb']), hm.1, hp⟩

/-- The sign step always succeeds under the standard model at $u$ with every value in range,
$u(p) < 1$ and an exact literal $1$, if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, $n \ge 1$, $b$ decodes to a nonzero value and the output block at `X` (tag `p`) has $2n^2$
cells (hypotheses on the inputs as `NLAlib.holds_of_exec_eighSignBlock`): unlike the pilot's
`whileFuel` loop, the bounded loop does not fail when no iterate passes the test. No printed
source. -/
theorem exists_exec_eighSignBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 1) (p : P) (hu : u p < 1) (n F : ℕ) (hn : 0 < n)
    {A par X : ℕ} {ao po xo : IExp ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {ε b : K} (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (eighSignBlock p mm (.const n) (.const F) A ao par po X xo).run st =
      some st' := by
  have hps := Store.lt_size_of_read_eq_some hε
  obtain ⟨len, hXsh, hlen⟩ := hX
  refine ((spec_eighSignBlock (safe := fun _ _ => True) (toNat := fun _ => 0) (unif := fun x
    (_ : K) => x) (normal := id) (qrR := fun A => (fun _ _ => default, A)) hmm .total p n F
    ⟨hsem, fun _ _ => trivial, hu, hn⟩ (hsem.decidesFlags hlit p) A₀ ε b (by fp_omega [hXA])
    (by fp_omega [hXp]) (Store.size_shape st.store ▸ (Array.getElem?_eq_some_iff.mp hXsh).1)
    (.inr (Store.lt_size_of_read_eq_some (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩))) hps).spec
    |>.exists_exec ⟨rfl, hA, hε, hb, hb0, writable_of_shape_eq rfl hXsh (by fp_omega [hlen])⟩).imp
    fun _ h => h.1

end NLAlib
