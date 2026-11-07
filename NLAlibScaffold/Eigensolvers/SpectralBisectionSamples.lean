/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionTape
public import NLAlib.RandomMatrix.Tape
public import NLAlib.Eigensolvers.SpectralBisection
public import NLAlibScaffold.Matrix.Computation.InterpMachine
public import NLAlibScaffold.Matrix.Computation.SpectralBisectionProgram
public import NLAlibScaffold.RandomMatrix.Computation.ComplexTape

/-!
# The samples a spectral bisection run reads (scaffold)

Statements for a new file `NLAlib/Eigensolvers/SpectralBisectionSamples.lean` (stage
COMPDYN S2b, design note `docs/design/Computation-EighProgram.md`, §6): from the program's tape to
the ideal sample tree of `NLAlib.eigh`.

* **Samples by position and by value.** `NLAlib.eigh` on a machine of a semantics uses its samples
  only through the samplers, and only at the nodes it reaches (the seed and the leading block of
  each test matrix). So the output on the tape machine with the tree of sample positions at the
  slots (`NLAlib.eighTapeMachine`, `NLAlib.eighSlotTree`) is the output on the ideal machine with
  the tree of ideal samples (`NLAlib.eighIdealTree`), for a rounding of the tape that does not
  depend on the position.
* **Lazy sampling.** On the ideal tape of law `NLAlib.Computation.tapeLaw`, the tree of ideal
  samples is independent with law `NLAlib.eighSampleLaw` at every path: the positions a node reads
  are decided by earlier samples and are disjoint from every other node's.
* **The ideal machine.** The machine of the semantics with the samplers of the tape rounding meets
  `NLAlib.FloatMachine.IsAccurate`, and its samplers have countable ranges and measurable fibres.

## Main results

* `NLAlib.eigh_toFloatMachine_map_samples`, `NLAlib.eigh_congr_samples`,
  `NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`: from positions to ideal samples.
* `NLAlib.iIndepFun_eighIdealTree`: lazy sampling.
* `NLAlib.Computation.isUnifSampler_uniformUnif`, `NLAlib.Computation.isAccurate_eighIdealMachine`,
  `NLAlib.Computation.countable_range_uniformUnif`,
  `NLAlib.Computation.countable_range_gaussianNormal`: the ideal machine.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

open Computation

/-! ### From positions to ideal samples -/

/-- The Newton–Schulz loop on two machines of one semantics that differ only in their samplers
(private helper of `NLAlib.eigh_toFloatMachine_map_samples`). -/
private theorem newtonSchulzSign_toFloatMachine_samplers {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) {k : ℕ}
    (b x : K) (N : ℕ) (B : Matrix (Fin k) (Fin k) (K × K)) :
    newtonSchulzSign (sem.toFloatMachine p toNat mm qr unif normal) b x N B =
      newtonSchulzSign (sem.toFloatMachine p toNat mm qr unif' normal') b x N B := by
  suffices h : ∀ η N (B' : Matrix (Fin k) (Fin k) (K × K)),
      newtonSchulzLoop (sem.toFloatMachine p toNat mm qr unif normal) η N B' =
        newtonSchulzLoop (sem.toFloatMachine p toNat mm qr unif' normal') η N B' from h _ N _
  intro η N
  induction N with
  | zero => intro B'; rfl
  | succ N ih => intro B'; simp only [newtonSchulzLoop, ih]; rfl

/-- The deflation of a leading block on two machines of one semantics whose normal samplers agree
along $g$ (private helper of `NLAlib.eigh_toFloatMachine_map_samples`). -/
private theorem deflate_leadingBlock_toFloatMachine_map {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} [Inhabited Sg] [Inhabited Sg'] (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) (g : Sg → Sg')
    (hn : ∀ z, normal z = normal' (g z)) {n k : ℕ} (hk : k ≤ n) (r : ℕ)
    (Pm : Matrix (Fin k) (Fin k) (K × K)) (G : Matrix (Fin n) (Fin n) Sg) :
    deflate (sem.toFloatMachine p toNat mm qr unif normal) r Pm (leadingBlock k G) =
      deflate (sem.toFloatMachine p toNat mm qr unif' normal') r Pm
        (leadingBlock k (G.map g)) := by
  have hG : (leadingBlock k G).map normal = (leadingBlock k (G.map g)).map normal' := by
    refine Matrix.ext fun i j => ?_
    have hi : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨i.2.trans_le hk, j.2.trans_le hk⟩
    simp only [leadingBlock, Matrix.map_apply, Matrix.of_apply, dif_pos hi, hn]
  simp only [deflate]
  exact congrArg _ (by rw [show (leadingBlock k G).map
    (sem.toFloatMachine p toNat mm qr unif normal).normal = _ from hG]; rfl)

/-- One step on two machines of one semantics whose samplers agree along $f$ and $g$ (private
helper of `NLAlib.eigh_toFloatMachine_map_samples`). -/
private theorem eighStep_toFloatMachine_map {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} [Inhabited Sg] [Inhabited Sg'] (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) (f : Su → Su')
    (g : Sg → Sg') (hu : ∀ c v, unif c v = unif' c (f v)) (hn : ∀ z, normal z = normal' (g z))
    (n signFuel : ℕ) (R₀ β : K) {k : ℕ} (hk : k ≤ n) (A : Matrix (Fin k) (Fin k) (K × K))
    (R ε : K) (ℓ : ℕ) (s : EighSample Su Sg n) :
    eighStep (sem.toFloatMachine p toNat mm qr unif normal) n signFuel R₀ β A R ε ℓ s =
      eighStep (sem.toFloatMachine p toNat mm qr unif' normal') n signFuel R₀ β A R ε ℓ
        (f s.1, fun b => (s.2 b).map g) := by
  obtain rfl : unif = fun c v => unif' c (f v) := funext fun c => funext (hu c)
  obtain rfl : normal = fun z => normal' (g z) := funext hn
  by_cases hk1 : k ≤ 1
  · simp only [eighStep, if_pos hk1]; rfl
  simp only [eighStep, if_neg hk1]
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [newtonSchulzSign_toFloatMachine_samplers sem p toNat mm qr _ _ unif' normal']
  intro h₁ h₂
  simp only [deflate_leadingBlock_toFloatMachine_map sem p toNat mm qr _ _ unif' normal' g hn hk]
  rfl

/-- **`NLAlib.eigh` sees its samples only through the samplers**: on two machines of the same
semantics, conversion and black boxes whose samplers agree along maps $f$ of seeds and $g$ of
Gaussian samples ($\mathrm{unif}(c, v) = \mathrm{unif}'(c, f(v))$,
$\mathrm{normal}(z) = \mathrm{normal}'(g(z))$), the output on a tree of samples is the output on the
tree mapped by $f$ and $g$. No printed source.
Proof: generalize to `NLAlib.eighAux` with a node of size $k \le n$ and induction on the budget;
`NLAlib.eighStep` uses the seed through `NLAlib.FloatMachine.unif` and the test matrices through
`NLAlib.deflate` of `NLAlib.leadingBlock`, whose map by $g$ is the leading block of the mapped
matrix ($k \le n$, `Matrix.map_apply`, `Matrix.of_apply`), and `NLAlib.deflate` maps them by the
normal sampler (`Matrix.map_map`); every other operation is the same on both machines
(`NLAlib.Computation.ScalarSem.toFloatMachine`). The children have sizes at most $k$. M, about 60
lines. -/
theorem eigh_toFloatMachine_map_samples {P K : Type} [Inhabited K] {Su Sg Su' Sg' : Type}
    [Inhabited Sg] [Inhabited Sg'] (sem : ScalarSem P K) (p : P) (toNat : K → ℕ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Su' → K) (normal' : Sg' → K × K) (f : Su → Su') (g : Sg → Sg')
    (hu : ∀ c v, unif c v = unif' c (f v)) (hn : ∀ z, normal z = normal' (g z)) (signFuel ℓ : ℕ)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K)) (R₀ ε β : K)
    (s : List Bool → EighSample Su Sg n) :
    eigh (sem.toFloatMachine p toNat mm qr unif normal) signFuel ℓ A R₀ ε β s =
      eigh (sem.toFloatMachine p toNat mm qr unif' normal') signFuel ℓ A R₀ ε β
        (fun a => (f (s a).1, fun b => ((s a).2 b).map g)) := by
  suffices h : ∀ (fuel k : ℕ) (A : Matrix (Fin k) (Fin k) (K × K)) (R ε : K) (ℓ : ℕ)
      (s : List Bool → EighSample Su Sg n), k ≤ n →
      eighAux (sem.toFloatMachine p toNat mm qr unif normal) n signFuel R₀ β fuel A R ε ℓ s =
        eighAux (sem.toFloatMachine p toNat mm qr unif' normal') n signFuel R₀ β fuel A R ε ℓ
          (fun a => (f (s a).1, fun b => ((s a).2 b).map g)) from h _ n A R₀ ε ℓ s le_rfl
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro k A R ε ℓ s hk
    simp only [eighAux]
    rw [eighStep_toFloatMachine_map sem p toNat mm qr unif normal unif' normal' f g hu hn n signFuel
      R₀ β hk]
    generalize eighStep (sem.toFloatMachine p toNat mm qr unif' normal') n signFuel R₀ β A R ε ℓ
      (f (s []).1, fun b => ((s []).2 b).map g) = st
    cases st with
    | leaf U d => rfl
    | shift b A' σ => dsimp only; rw [ih _ A' _ _ _ _ hk]; rfl
    | split kp h Qp Qm Ap Am σ =>
      dsimp only
      rw [ih _ Ap _ _ _ _ (h.trans hk), ih _ Am _ _ _ _ ((Nat.sub_le _ _).trans hk)]
      rfl

/-- A step of `NLAlib.eighStep` reads its sample only through the seed and the leading blocks of
the test matrices of its size. -/
private lemma eighStep_congr_sample {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (N signFuel : ℕ) (R₀ β : F) {k : ℕ} (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ)
    {t t' : EighSample Su Sg N} (h1 : t.1 = t'.1)
    (h2 : ∀ b, leadingBlock k (t.2 b) = leadingBlock k (t'.2 b)) :
    eighStep M N signFuel R₀ β A R ε ℓ t = eighStep M N signFuel R₀ β A R ε ℓ t' := by
  obtain ⟨v, G⟩ := t
  obtain ⟨v', G'⟩ := t'
  simp only at h1 h2
  subst h1
  unfold eighStep
  simp only [h2]

/-- The sample of a child is the sample below its side: the node at `b :: a` is the node at `a`
below the child on side `b`. -/
private lemma eighNodeAt_cons_of_eighChild {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) (x c : EighNode F) (b : Bool)
    (a : List Bool) (s : List Bool → EighSample Su Sg N)
    (hc : eighChild M N signFuel R₀ β x (s []) b = some c) :
    eighNodeAt M N signFuel R₀ β (b :: a) x s =
      eighNodeAt M N signFuel R₀ β a c (fun a' => s (b :: a')) := by
  simp [eighNodeAt, hc]

/-- The budget-$f$ recursion `NLAlib.eighAux` from a node reads its samples only at the paths of
length below $f$ that the node reaches. Induction on the budget. -/
private lemma eighAux_congr_samples {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (signFuel : ℕ) {n : ℕ} (R₀ β : F) (f : ℕ) :
    ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ)
      {s s' : List Bool → EighSample Su Sg n},
      (∀ (a : List Bool) (y : EighNode F), a.length < f →
        eighNodeAt M n signFuel R₀ β a ⟨k, A, R, ε, ℓ⟩ s = some y →
          (s a).1 = (s' a).1 ∧ ∀ b, leadingBlock y.k ((s a).2 b) = leadingBlock y.k ((s' a).2 b)) →
      eighAux M n signFuel R₀ β f A R ε ℓ s = eighAux M n signFuel R₀ β f A R ε ℓ s' := by
  induction f with
  | zero => intro k A R ε ℓ s s' _; rfl
  | succ f ih =>
    intro k A R ε ℓ s s' H
    have H0 := H [] ⟨k, A, R, ε, ℓ⟩ (by simp) rfl
    have hstep := eighStep_congr_sample M n signFuel R₀ β A R ε ℓ (t := s []) (t' := s' [])
      H0.1 (fun b => H0.2 b)
    have hchild : ∀ (b : Bool) (c : EighNode F),
        eighChild M n signFuel R₀ β ⟨k, A, R, ε, ℓ⟩ (s []) b = some c →
        ∀ (a : List Bool) (y : EighNode F), a.length < f →
          eighNodeAt M n signFuel R₀ β a c (fun a' => s (b :: a')) = some y →
            (s (b :: a)).1 = (s' (b :: a)).1 ∧
              ∀ d, leadingBlock y.k ((s (b :: a)).2 d) = leadingBlock y.k ((s' (b :: a)).2 d) := by
      intro b c hc a y hl hy
      exact H (b :: a) y (by simp only [List.length_cons]; omega)
        ((eighNodeAt_cons_of_eighChild M n signFuel R₀ β _ c b a s hc).trans hy)
    simp only [eighAux]
    rw [hstep]
    cases hT : eighStep M n signFuel R₀ β A R ε ℓ (s' []) with
    | leaf U d => rfl
    | shift b A' σ =>
      have hc : eighChild M n signFuel R₀ β ⟨k, A, R, ε, ℓ⟩ (s []) b =
          some ⟨k, A', (eighNextParams M R ε ℓ).1, (eighNextParams M R ε ℓ).2, ℓ + 1⟩ := by
        simp [eighChild, hstep.trans hT]
      dsimp only
      rw [ih A' _ _ (ℓ + 1) (hchild b _ hc)]
    | split kp h Qp Qm Ap Am σ =>
      have hcT : eighChild M n signFuel R₀ β ⟨k, A, R, ε, ℓ⟩ (s []) true =
          some ⟨kp, Ap, (eighNextParams M R ε ℓ).1, (eighNextParams M R ε ℓ).2, ℓ + 1⟩ := by
        simp [eighChild, hstep.trans hT]
      have hcF : eighChild M n signFuel R₀ β ⟨k, A, R, ε, ℓ⟩ (s []) false =
          some ⟨k - kp, Am, (eighNextParams M R ε ℓ).1, (eighNextParams M R ε ℓ).2, ℓ + 1⟩ := by
        simp [eighChild, hstep.trans hT]
      dsimp only
      rw [ih Ap _ _ (ℓ + 1) (hchild true _ hcT), ih Am _ _ (ℓ + 1) (hchild false _ hcF)]

/-- **`NLAlib.eigh` reads only the samples of the nodes it reaches**: two trees of samples that
agree, at every path of length at most $\ell$ (the nodes with a positive budget) that
`NLAlib.eighNodeAt` follows, on the seed and on the leading $k \times k$ blocks of the test matrices
($k$ the node's size), give the same output. No printed source.
Proof: generalize to `NLAlib.eighAux` at budget $f$ from a node, with agreement at the paths of
length below $f$; induction on $f$: at budget $f + 1$, `NLAlib.eighStep` at the node depends on the
sample at the empty path only through the seed and the leading blocks (unfold `NLAlib.eighStep`,
`congr`), so the step, its children and the children's subtrees of samples (agreeing below, by the
hypothesis at $b :: a$, `NLAlib.eighNodeAt`) agree. M, about 50 lines. -/
theorem eigh_congr_samples {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (signFuel ℓ : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (F × F)) (R₀ ε β : F)
    {s s' : List Bool → EighSample Su Sg n}
    (h : ∀ (a : List Bool) (y : EighNode F), a.length ≤ ℓ →
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y →
        (s a).1 = (s' a).1 ∧ ∀ b, leadingBlock y.k ((s a).2 b) = leadingBlock y.k ((s' a).2 b)) :
    eigh M signFuel ℓ A R₀ ε β s = eigh M signFuel ℓ A R₀ ε β s' := by
  exact eighAux_congr_samples M signFuel R₀ β (ℓ + 1) A R₀ ε ℓ
    (fun a y hl hy => h a y (Nat.lt_succ_iff.mp hl) hy)


/-- The Newton–Schulz loop on two machines of one semantics that differ only in their samplers
(private helper of `NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`). -/
private theorem newtonSchulzSign_toFloatMachine_tape {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) {k : ℕ}
    (b x : K) (N : ℕ) (B : Matrix (Fin k) (Fin k) (K × K)) :
    newtonSchulzSign (sem.toFloatMachine p toNat mm qr unif normal) b x N B =
      newtonSchulzSign (sem.toFloatMachine p toNat mm qr unif' normal') b x N B := by
  suffices h : ∀ η N (B' : Matrix (Fin k) (Fin k) (K × K)),
      newtonSchulzLoop (sem.toFloatMachine p toNat mm qr unif normal) η N B' =
        newtonSchulzLoop (sem.toFloatMachine p toNat mm qr unif' normal') η N B' from h _ N _
  intro η N
  induction N with
  | zero => intro B'; rfl
  | succ N ih => intro B'; simp only [newtonSchulzLoop, ih]; rfl

/-- The deflation of a leading block on two machines of one semantics whose normal samplers agree
along $g$ (private helper of `NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`). -/
private theorem deflate_leadingBlock_toFloatMachine_tape {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} [Inhabited Sg] [Inhabited Sg'] (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) (g : Sg → Sg')
    (hn : ∀ z, normal z = normal' (g z)) {n k : ℕ} (hk : k ≤ n) (r : ℕ)
    (Pm : Matrix (Fin k) (Fin k) (K × K)) (G : Matrix (Fin n) (Fin n) Sg) :
    deflate (sem.toFloatMachine p toNat mm qr unif normal) r Pm (leadingBlock k G) =
      deflate (sem.toFloatMachine p toNat mm qr unif' normal') r Pm
        (leadingBlock k (G.map g)) := by
  have hG : (leadingBlock k G).map normal = (leadingBlock k (G.map g)).map normal' := by
    refine Matrix.ext fun i j => ?_
    have hi : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨i.2.trans_le hk, j.2.trans_le hk⟩
    simp only [leadingBlock, Matrix.map_apply, Matrix.of_apply, dif_pos hi, hn]
  simp only [deflate]
  exact congrArg _ (by rw [show (leadingBlock k G).map
    (sem.toFloatMachine p toNat mm qr unif normal).normal = _ from hG]; rfl)

/-- One step on two machines of one semantics whose samplers agree along $f$ and $g$ (private
helper of `NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`). -/
private theorem eighStep_toFloatMachine_tape {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} [Inhabited Sg] [Inhabited Sg'] (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) (f : Su → Su')
    (g : Sg → Sg') (hu : ∀ c v, unif c v = unif' c (f v)) (hn : ∀ z, normal z = normal' (g z))
    (n signFuel : ℕ) (R₀ β : K) {k : ℕ} (hk : k ≤ n) (A : Matrix (Fin k) (Fin k) (K × K))
    (R ε : K) (ℓ : ℕ) (s : EighSample Su Sg n) :
    eighStep (sem.toFloatMachine p toNat mm qr unif normal) n signFuel R₀ β A R ε ℓ s =
      eighStep (sem.toFloatMachine p toNat mm qr unif' normal') n signFuel R₀ β A R ε ℓ
        (f s.1, fun b => (s.2 b).map g) := by
  obtain rfl : unif = fun c v => unif' c (f v) := funext fun c => funext (hu c)
  obtain rfl : normal = fun z => normal' (g z) := funext hn
  by_cases hk1 : k ≤ 1
  · simp only [eighStep, if_pos hk1]; rfl
  simp only [eighStep, if_neg hk1]
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [newtonSchulzSign_toFloatMachine_tape sem p toNat mm qr _ _ unif' normal']
  intro h₁ h₂
  simp only [deflate_leadingBlock_toFloatMachine_tape sem p toNat mm qr _ _ unif' normal' g hn hk]
  rfl

/-- One step reads its sample only through the seed and the leading blocks of its size (private
helper of `NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`). -/
private theorem eighStep_congr_leadingBlock {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ) {s s' : EighSample Su Sg N}
    (h₁ : s.1 = s'.1) (h₂ : ∀ b, leadingBlock k (s.2 b) = leadingBlock k (s'.2 b)) :
    eighStep M N signFuel R₀ β A R ε ℓ s = eighStep M N signFuel R₀ β A R ε ℓ s' := by
  obtain ⟨v, G⟩ := s
  obtain ⟨v', G'⟩ := s'
  obtain rfl : v = v' := h₁
  simp only [eighStep, h₂]

/-- The ideal sample of a node below the depth budget has the seed and the leading blocks of the
slot's positions read on the ideal tape (private helper of
`NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`). -/
private theorem eighIdealSample_eq_eighTapeSample (ξ : Dist → ℕ → ℝ) {N D d : ℕ} (hd : d < D)
    (lo k : ℕ) (pre : List Bool) :
    ξ .uniform (eighTapeSample N d lo).1 = (eighIdealSample ξ N D d lo (some k) pre).1 ∧
      ∀ b, leadingBlock k (((eighTapeSample N d lo).2 b).map (eighIdealComplex ξ)) =
        leadingBlock k ((eighIdealSample ξ N D d lo (some k) pre).2 b) := by
  refine ⟨by simp only [eighTapeSample, eighIdealSample, if_pos hd], fun b => ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [leadingBlock, eighTapeSample, eighIdealSample, if_pos hd, Matrix.of_apply,
    Matrix.map_apply, i.2, j.2, and_self, if_true]

/-- Along every path below the budget, the slot tree mapped to ideal samples and the tree of ideal
samples agree on the seed and the leading blocks of the node reached (private helper of
`NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`). -/
private theorem eighSlotTree_map_agree_eighIdealTree {P K : Type} [Inhabited K]
    (sem : ScalarSem P K) (p : P) (toN : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → ℕ → K) (normal : ℕ → K × K) (unif' : K → ℝ → K) (normal' : ℂ → K × K)
    (ξ : Dist → ℕ → ℝ) (hu : ∀ c i, unif c i = unif' c (ξ .uniform i))
    (hn : ∀ z, normal z = normal' (eighIdealComplex ξ z)) (n signFuel D : ℕ) (R₀ β : K) :
    ∀ (a : List Bool) (d lo : ℕ) (x : EighNode K) (pre : List Bool) (y : EighNode K), x.k ≤ n →
      d + a.length < D →
      eighNodeAt (sem.toFloatMachine p toN mm qr unif' normal') n signFuel R₀ β a x
          (fun a => (ξ .uniform
            (eighSlotTree (sem.toFloatMachine p toN mm qr unif normal) n signFuel R₀ β d lo x a).1,
            fun b => ((eighSlotTree (sem.toFloatMachine p toN mm qr unif normal) n signFuel R₀ β d
              lo x a).2 b).map (eighIdealComplex ξ))) = some y →
        ξ .uniform
            (eighSlotTree (sem.toFloatMachine p toN mm qr unif normal) n signFuel R₀ β d lo x a).1 =
          (eighIdealTree (sem.toFloatMachine p toN mm qr unif' normal') n signFuel D R₀ β ξ d lo
            (some x) pre a).1 ∧
        ∀ b, leadingBlock y.k (((eighSlotTree (sem.toFloatMachine p toN mm qr unif normal) n
            signFuel R₀ β d lo x a).2 b).map (eighIdealComplex ξ)) =
          leadingBlock y.k ((eighIdealTree (sem.toFloatMachine p toN mm qr unif' normal') n
            signFuel D R₀ β ξ d lo (some x) pre a).2 b) := by
  intro a
  induction a with
  | nil =>
    intro d lo x pre y _ hd h
    obtain rfl : x = y := Option.some.inj h
    exact eighIdealSample_eq_eighTapeSample ξ (by simpa using hd) lo x.k pre
  | cons b a ih =>
    intro d lo x pre y hx hd h
    have hst := eighStep_toFloatMachine_tape sem p toN mm qr unif normal unif' normal' (ξ .uniform)
      (eighIdealComplex ξ) hu hn n signFuel R₀ β hx x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    have h0 := eighIdealSample_eq_eighTapeSample ξ (d := d) (D := D) (N := n) (by simp at hd; omega)
      lo x.k pre
    have hJ := eighStep_congr_leadingBlock (sem.toFloatMachine p toN mm qr unif' normal') n signFuel
      R₀ β x.A x.R x.ε x.ℓ (s := (ξ .uniform (eighTapeSample n d lo).1,
        fun b => ((eighTapeSample n d lo).2 b).map (eighIdealComplex ξ)))
      (s' := eighIdealSample ξ n D d lo (some x.k) pre) h0.1 h0.2
    have hd' : d + 1 + a.length < D := by simp only [List.length_cons] at hd; omega
    simp only [eighNodeAt, eighChild, eighSlotTree.eq_1, eighSlotTree.eq_2] at h
    rw [eighSlotTree.eq_2, eighIdealTree.eq_3, ← hJ, ← hst]
    rw [← hst] at h
    generalize eighStep (sem.toFloatMachine p toN mm qr unif normal) n signFuel R₀ β x.A x.R x.ε x.ℓ
      (eighTapeSample n d lo) = st at h ⊢
    cases st with
    | leaf U e => simp only [Option.bind_none, reduceCtorEq] at h
    | shift b' A' σ =>
      by_cases hb : b = b'
      · simp only [hb, if_true, Option.bind_some] at h ⊢
        exact ih (d + 1) lo _ (pre ++ [b']) y hx hd' h
      · simp only [hb, if_false, Option.bind_none, reduceCtorEq] at h
    | split kp hkp Qp Qm Ap Am σ =>
      cases b
      · simp only [Bool.false_eq_true, if_false, Option.bind_some] at h ⊢
        exact ih (d + 1) (lo + kp) _ (pre ++ [false]) y ((Nat.sub_le _ _).trans hx) hd' h
      · simp only [if_true, Option.bind_some] at h ⊢
        exact ih (d + 1) lo _ (pre ++ [true]) y (hkp.trans hx) hd' h

/-- **The run's output on positions is the output on ideal samples**: for an interpretation whose
tape is a rounding $\rho \circ \xi$ of an ideal tape $\xi$, with $\rho$ independent of the position,
`NLAlib.eigh` on the tape machine (`NLAlib.eighTapeMachine`) with the tree of sample positions at
the slots (`NLAlib.eighSlotTree`) is `NLAlib.eigh` on the ideal machine (the machine of the
semantics with the samplers `NLAlib.Computation.ScalarSem.uniformUnif` and
`NLAlib.Computation.ScalarSem.gaussianNormal` of $\rho$) with the tree of ideal samples
(`NLAlib.eighIdealTree`, budget $\ell + 1$). No printed source.
Proof: `NLAlib.eigh_toFloatMachine_map_samples` with $f(i) = \xi_{\mathrm{uniform}}(i)$ and
$g(z) = $ `NLAlib.eighIdealComplex` $\xi\ z$: the shift is the same rounded product
(`NLAlib.Computation.ScalarSem.tapeUnif`, `hρ`), and the stored Gaussian pair is the same
(`NLAlib.Computation.ScalarSem.tapeNormal`, $\sqrt2\,(\xi_{2z}/\sqrt2) = \xi_{2z}$,
`Real.mul_self_sqrt`, `field_simp`). Then `NLAlib.eigh_congr_samples`: by induction on the path, the
node at a path of length $d \le \ell$ is the same in both recursions (the steps agree by the
previous point), `NLAlib.eighNodeAt_eighSlotTree` gives its slot $lo$, and `NLAlib.eighIdealSample`
at $d < \ell + 1$ reads the static positions of `NLAlib.eighTapeSample` on the seed and the leading
block. L, about 120 lines. -/
theorem eigh_eighTapeMachine_eq_eigh_eighIdealTree {P ι K C : Type} [Inhabited K]
    (I : Interp P ι K C) (p : P) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (ρ : Dist → ℕ → ℝ → K) (hρ : ∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y)
    (ξ : Dist → ℕ → ℝ) (signFuel ℓ : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K))
    (R₀ ε β : K) :
    let I' : Interp P ι K C := { I with tape := fun d i => ρ d i (ξ d i) }
    let M := eighTapeMachine I' p mmR qrR
    let M' := I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
      (I.sem.uniformUnif p (ρ .uniform 0)) (I.sem.gaussianNormal p (ρ .gaussian 0))
    eigh M signFuel ℓ A R₀ ε β (eighSlotTree M n signFuel R₀ β 0 0 ⟨n, A, R₀, ε, ℓ⟩) =
      eigh M' signFuel ℓ A R₀ ε β
        (fun a => eighIdealTree M' n signFuel (ℓ + 1) R₀ β ξ 0 0 (some ⟨n, A, R₀, ε, ℓ⟩) [] a) := by
  intro I' M M'
  have hu : ∀ c i, I.sem.tapeUnif p (fun i => ρ .uniform i (ξ .uniform i)) c i =
      I.sem.uniformUnif p (ρ .uniform 0) c (ξ .uniform i) := fun c i => by
    simp only [ScalarSem.tapeUnif, ScalarSem.uniformUnif, hρ .uniform i 0]
  have hn : ∀ z, I.sem.tapeNormal p (fun i => ρ .gaussian i (ξ .gaussian i)) z =
      I.sem.gaussianNormal p (ρ .gaussian 0) (eighIdealComplex ξ z) := fun z => by
    have h2 : √2 ≠ 0 := by positivity
    simp only [ScalarSem.tapeNormal, ScalarSem.gaussianNormal, eighIdealComplex,
      mul_div_cancel₀ _ h2, hρ .gaussian _ 0]
  refine (eigh_toFloatMachine_map_samples I.sem p (fun x => (I.sem.toNat p x).getD 0) mmR qrR _ _
    _ _ (ξ .uniform) (eighIdealComplex ξ) hu hn signFuel ℓ A R₀ ε β _).trans ?_
  refine eigh_congr_samples M' signFuel ℓ A R₀ ε β fun a y ha h => ?_
  exact eighSlotTree_map_agree_eighIdealTree I.sem p _ mmR qrR _ _ _ _ ξ hu hn n signFuel (ℓ + 1)
    R₀ β a 0 0 _ [] y le_rfl (by omega) h

/-- The σ-algebra of the tape coordinates in `Q`. -/
private noncomputable abbrev tapeSigma (Q : Set (Dist × ℕ)) : MeasurableSpace (Dist → ℕ → ℝ) :=
  ⨆ p ∈ Q, MeasurableSpace.comap (fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2) inferInstance

private lemma measurable_tape_apply (p : Dist × ℕ) :
    Measurable fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2 :=
  (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

private lemma tapeSigma_le (Q : Set (Dist × ℕ)) :
    tapeSigma Q ≤ (inferInstance : MeasurableSpace (Dist → ℕ → ℝ)) :=
  iSup₂_le fun p _ => (measurable_tape_apply p).comap_le

private lemma tapeSigma_mono {Q Q' : Set (Dist × ℕ)} (h : Q ⊆ Q') : tapeSigma Q ≤ tapeSigma Q' :=
  biSup_mono h

private lemma measurable_tapeSigma_apply {Q : Set (Dist × ℕ)} {p : Dist × ℕ} (hp : p ∈ Q) :
    Measurable[tapeSigma Q] fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2 :=
  Measurable.of_comap_le (le_iSup₂ (f := fun p (_ : p ∈ Q) => MeasurableSpace.comap
    (fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2) inferInstance) p hp)

private lemma indep_tapeSigma {Q Q' : Set (Dist × ℕ)} (h : Disjoint Q Q') :
    Indep (tapeSigma Q) (tapeSigma Q') tapeLaw := by
  have hind : iIndepFun (fun (p : Dist × ℕ) (ξ : Dist → ℕ → ℝ) => ξ p.1 p.2) tapeLaw := by
    have h := iIndepFun_uncurry_infinitePi' (Ω := fun (_ : Dist) (_ : ℕ) => ℝ)
      (fun d (_ : ℕ) => d.law) (X := fun (_ : Dist) (_ : ℕ) (x : ℝ) => x)
      (fun _ _ => measurable_id)
    exact h
  rw [iIndepFun_iff_iIndep] at hind
  exact indep_iSup_of_disjoint (fun p => (measurable_tape_apply p).comap_le) hind h


/-- The ideal sample read at the uniform position `u` and the complex Gaussian positions `z`. -/
private noncomputable def eighReadSample (N u : ℕ) (z : Bool → Fin N → Fin N → ℕ)
    (ξ : Dist → ℕ → ℝ) : EighSample ℝ ℂ N :=
  (ξ .uniform u, fun b => Matrix.of fun i j => eighIdealComplex ξ (z b i j))

private lemma map_pi_fin_two_eq_complexGaussian :
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map
      (fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ)) = complexGaussian := by
  have hA : Measurable (Complex.measurableEquivRealProd.symm ∘ Prod.map (· / √2) (· / √2)) :=
    Complex.measurableEquivRealProd.symm.measurable.comp (by fun_prop)
  have hfun : (fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ)) =
      (Complex.measurableEquivRealProd.symm ∘ Prod.map (· / √2) (· / √2)) ∘
        MeasurableEquiv.finTwoArrow := rfl
  have hd : (gaussianReal 0 1).map (· / √2) = gaussianReal 0 2⁻¹ := by
    have hfn : (fun x : ℝ => x / √2) = fun x => (√2)⁻¹ * x :=
      funext fun x => div_eq_inv_mul _ _
    rw [hfn, gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.eq
      simp [mul_comm]
  rw [hfun, ← Measure.map_map hA MeasurableEquiv.finTwoArrow.measurable,
    (measurePreserving_finTwoArrow _).map_eq,
    ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), hd]
  rfl

private lemma measurable_complexPair :
    Measurable fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ) :=
  Complex.measurableEquivRealProd.symm.measurable.comp (f := fun v : Fin 2 → ℝ =>
    (v 0 / √2, v 1 / √2)) (((measurable_pi_apply 0).div_const _).prodMk
      ((measurable_pi_apply 1).div_const _))

private lemma measurable_complex_mk {α : Type*} {mα : MeasurableSpace α} {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => (⟨f x, g x⟩ : ℂ) :=
  Complex.measurableEquivRealProd.symm.measurable.comp (hf.prodMk hg)

/-- Pairs of independent standard Gaussians scaled by $1/\sqrt2$, arranged as a matrix, form a
standard complex Gaussian matrix. -/
private lemma map_pi_gaussianReal_eq_complexGaussianMatrix (n : ℕ) :
    Measure.map
      (fun y : (Fin n × Fin n) × Fin 2 → ℝ =>
        (Matrix.of fun i j => (⟨y ((i, j), 0) / √2, y ((i, j), 1) / √2⟩ : ℂ) :
          Matrix (Fin n) (Fin n) ℂ))
      (Measure.pi fun _ : (Fin n × Fin n) × Fin 2 => gaussianReal 0 1) =
        complexGaussianMatrix (Fin n) (Fin n) := by
  have hG := measurePreserving_curry_pi (m := Fin n × Fin n) (n := Fin 2)
    (ν := fun _ _ => gaussianReal 0 1)
  have hH := measurePreserving_curry_pi (m := Fin n) (n := Fin n) (α := Fin 2 → ℝ)
    (ν := fun _ _ => Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
  have hHG := hH.comp hG
  have hPmap : Measure.map
      (fun x : Fin n → Fin n → Fin 2 → ℝ =>
        (Matrix.of fun i j => (⟨x i j 0 / √2, x i j 1 / √2⟩ : ℂ) : Matrix (Fin n) (Fin n) ℂ))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
        Measure.pi fun _ : Fin 2 => gaussianReal 0 1) = complexGaussianMatrix (Fin n) (Fin n) := by
    refine (Measure.pi_map_pi (f := fun _ (r : Fin n → Fin 2 → ℝ) j =>
        (⟨r j 0 / √2, r j 1 / √2⟩ : ℂ))
      (fun _ => (measurable_pi_lambda _ fun j =>
        measurable_complexPair.comp (measurable_pi_apply j)).aemeasurable)).trans ?_
    refine congrArg Measure.pi (funext fun i => ?_)
    refine (Measure.pi_map_pi (f := fun _ (v : Fin 2 → ℝ) => (⟨v 0 / √2, v 1 / √2⟩ : ℂ))
      (fun _ => measurable_complexPair.aemeasurable)).trans ?_
    exact congrArg Measure.pi (funext fun _ => map_pi_fin_two_eq_complexGaussian)
  have hPm : Measurable fun x : Fin n → Fin n → Fin 2 → ℝ =>
      (Matrix.of fun i j => (⟨x i j 0 / √2, x i j 1 / √2⟩ : ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      measurable_complexPair.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))
  rw [← hPmap, ← hHG.map_eq, Measure.map_map hPm hHG.measurable]
  rfl

/-- **The law of a sample read at distinct positions**: under the law of the tape, the ideal sample
read at one uniform position and at pairwise distinct complex Gaussian positions has the law
`NLAlib.eighSampleLaw`. -/
private lemma hasLaw_eighReadSample (N u : ℕ) (z : Bool → Fin N → Fin N → ℕ)
    (hz : Function.Injective fun p : Bool × Fin N × Fin N => z p.1 p.2.1 p.2.2) :
    HasLaw (eighReadSample N u z) (eighSampleLaw N) tapeLaw := by
  have hid : HasLaw (fun ξ : Dist → ℕ → ℝ => ξ) tapeLaw tapeLaw := ⟨aemeasurable_id, Measure.map_id⟩
  -- the uniform seed
  have hU : HasLaw (fun ξ : Dist → ℕ → ℝ => ξ .uniform u) Dist.uniform.law tapeLaw :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => Dist.uniform.law) u).fun_comp_hasLaw
      (hasLaw_apply_of_hasLaw_tapeLaw hid .uniform)
  -- the Gaussian draws at the positions
  have hf : Function.Injective fun p : Bool × ((Fin N × Fin N) × Fin 2) =>
      2 * z p.1 p.2.1.1 p.2.1.2 + p.2.2.1 := by
    rintro ⟨b, ⟨i, j⟩, t⟩ ⟨b', ⟨i', j'⟩, t'⟩ h
    have ht : t.1 = t'.1 := by simp only at h; omega
    have hz' : z b i j = z b' i' j' := by simp only at h; omega
    have := hz (a₁ := (b, i, j)) (a₂ := (b', i', j')) hz'
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl, rfl⟩ := this
    rw [Fin.ext ht]
  have hY : HasLaw (fun (ξ : Dist → ℕ → ℝ) (p : Bool × ((Fin N × Fin N) × Fin 2)) =>
      ξ .gaussian (2 * z p.1 p.2.1.1 p.2.1.2 + p.2.2.1))
      (Measure.pi fun _ : Bool × ((Fin N × Fin N) × Fin 2) => gaussianReal 0 1) tapeLaw :=
    (hasLaw_apply_of_hasLaw_tapeLaw hid .gaussian).comp_of_injective hf
  have hC := measurePreserving_curry_pi (m := Bool) (n := (Fin N × Fin N) × Fin 2)
    (ν := fun _ _ => gaussianReal 0 1)
  have hMm : ∀ _ : Bool, Measurable fun y : (Fin N × Fin N) × Fin 2 → ℝ =>
      (Matrix.of fun i j => (⟨y ((i, j), 0) / √2, y ((i, j), 1) / √2⟩ : ℂ) :
        Matrix (Fin N) (Fin N) ℂ) := fun _ =>
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      measurable_complexPair.comp (measurable_pi_lambda
        (fun (c : (Fin N × Fin N) × Fin 2 → ℝ) (t : Fin 2) => c ((i, j), t))
        fun _ => measurable_pi_apply _)
  have hmap : Measure.map
      (fun y : Bool → (Fin N × Fin N) × Fin 2 → ℝ => fun b =>
        (Matrix.of fun i j => (⟨y b ((i, j), 0) / √2, y b ((i, j), 1) / √2⟩ : ℂ) :
          Matrix (Fin N) (Fin N) ℂ))
      (Measure.pi fun _ : Bool => Measure.pi fun _ : (Fin N × Fin N) × Fin 2 => gaussianReal 0 1)
      = Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N) := by
    refine (Measure.pi_map_pi (fun b => (hMm b).aemeasurable)).trans ?_
    exact congrArg Measure.pi (funext fun _ => map_pi_gaussianReal_eq_complexGaussianMatrix N)
  have hGm : Measurable fun y : Bool → (Fin N × Fin N) × Fin 2 → ℝ => fun b =>
      (Matrix.of fun i j => (⟨y b ((i, j), 0) / √2, y b ((i, j), 1) / √2⟩ : ℂ) :
        Matrix (Fin N) (Fin N) ℂ) :=
    measurable_pi_lambda _ fun b => (hMm b).comp (measurable_pi_apply b)
  have hG : HasLaw (fun ξ : Dist → ℕ → ℝ => fun b =>
      (Matrix.of fun i j => eighIdealComplex ξ (z b i j) : Matrix (Fin N) (Fin N) ℂ))
      (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)) tapeLaw := by
    have := (HasLaw.mk (hGm.comp hC.measurable).aemeasurable
      (by rw [← Measure.map_map hGm hC.measurable, hC.map_eq, hmap])).comp hY
    convert this using 1
    funext ξ b
    ext i j
    simp [eighIdealComplex, MeasurableEquiv.curry, Function.curry]
  -- the seed and the matrices are independent
  have hind : iIndepFun (fun (d : Dist) (ξ : Dist → ℕ → ℝ) => ξ d) tapeLaw :=
    iIndepFun_infinitePi (P := fun d : Dist => iidSequence d.law)
      (X := fun (_ : Dist) (x : ℕ → ℝ) => x) fun _ => measurable_id
  have hUG : IndepFun (fun ξ : Dist → ℕ → ℝ => ξ .uniform u) (fun ξ : Dist → ℕ → ℝ => fun b =>
      (Matrix.of fun i j => eighIdealComplex ξ (z b i j) : Matrix (Fin N) (Fin N) ℂ)) tapeLaw := by
    have h2 := hind.indepFun (i := .uniform) (j := .gaussian) (by simp)
    refine h2.comp (φ := fun x : ℕ → ℝ => x u) (ψ := fun (x : ℕ → ℝ) (b : Bool) =>
      (Matrix.of fun i j => (⟨x (2 * z b i j) / √2, x (2 * z b i j + 1) / √2⟩ : ℂ) :
        Matrix (Fin N) (Fin N) ℂ)) (measurable_pi_apply u) ?_
    exact measurable_pi_lambda _ fun b => measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun j => measurable_complex_mk
        ((measurable_pi_apply _).div_const _) ((measurable_pi_apply _).div_const _)
  exact hUG.hasLaw_prod hU hG

/-! ### The shape of a step -/

/-- The sizes of a step: a one-child node has size at least $2$, and a split is proper. -/
private lemma eighStep_shape {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (N signFuel : ℕ) (R₀ β : F) {k : ℕ} (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ)
    (s : EighSample Su Sg N) :
    match eighStep M N signFuel R₀ β A R ε ℓ s with
    | .leaf _ _ => True
    | .shift _ _ _ => 2 ≤ k
    | .split kp _ _ _ _ _ _ => 0 < kp ∧ kp < k := by
  unfold eighStep
  dsimp only
  split_ifs with h1 h2 h3 h4
  · trivial
  · trivial
  · omega
  · omega
  · exact ⟨Nat.pos_of_ne_zero h4, lt_of_le_of_ne (min_le_left _ _) h3⟩

/-- The two children of a node: none, one child of the same size (at least $2$), or a proper
split. -/
private lemma eighChild_cases {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (N signFuel : ℕ) (R₀ β : F) (x : EighNode F) (s : EighSample Su Sg N) :
    (eighChild M N signFuel R₀ β x s true = none ∧ eighChild M N signFuel R₀ β x s false = none) ∨
    (∃ y, eighChild M N signFuel R₀ β x s true = some y ∧
      eighChild M N signFuel R₀ β x s false = none ∧ y.k = x.k ∧ 2 ≤ x.k) ∨
    (∃ y, eighChild M N signFuel R₀ β x s true = none ∧
      eighChild M N signFuel R₀ β x s false = some y ∧ y.k = x.k ∧ 2 ≤ x.k) ∨
    (∃ y y', eighChild M N signFuel R₀ β x s true = some y ∧
      eighChild M N signFuel R₀ β x s false = some y' ∧ 1 ≤ y.k ∧ 1 ≤ y'.k ∧
        y.k + y'.k = x.k) := by
  have h := eighStep_shape M N signFuel R₀ β x.A x.R x.ε x.ℓ s
  unfold eighChild
  generalize eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s = st at h ⊢
  cases st with
  | leaf U e => simp
  | shift b' A' σ => cases b' <;> simp [h]
  | split kp hkp Qp Qm Ap Am σ =>
    simp only [Bool.false_eq_true, if_false, if_true]
    right; right; right
    exact ⟨_, _, rfl, rfl, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩

/-! ### The tree of ideal samples, one level at a time -/

section Tree

variable {F : Type*} (M : FloatMachine F ℝ ℂ) (N signFuel D : ℕ) (R₀ β : F)

/-- The children of a possible node under a sample. -/
private def eighKids (xo : Option (EighNode F)) (s : EighSample ℝ ℂ N) :
    Option (EighNode F) × Option (EighNode F) :=
  (xo.bind fun x => eighChild M N signFuel R₀ β x s true,
    xo.bind fun x => eighChild M N signFuel R₀ β x s false)

/-- The slot of the child on side `b`, for the children `c` of a node at slot `lo`. -/
private def eighKidSlot (lo : ℕ) (c : Option (EighNode F) × Option (EighNode F)) (b : Bool) : ℕ :=
  if b then lo else lo + (c.1.map EighNode.k).getD 0

/-- The child on side `b`. -/
private def eighKid (c : Option (EighNode F) × Option (EighNode F)) (b : Bool) :
    Option (EighNode F) :=
  if b then c.1 else c.2

/-- Below no node the tree does not depend on the slot. -/
private lemma eighIdealTree_none_slot (ξ : Dist → ℕ → ℝ) (a : List Bool) :
    ∀ (d lo lo' : ℕ) (pre : List Bool),
      eighIdealTree M N signFuel D R₀ β ξ d lo none pre a =
        eighIdealTree M N signFuel D R₀ β ξ d lo' none pre a := by
  induction a with
  | nil => intro d lo lo' pre; simp only [eighIdealTree, Option.map_none, eighIdealSample]
  | cons b a ih => intro d lo lo' pre; simp only [eighIdealTree]; exact ih _ _ _ _

/-- **The tree one level down**: the subtree on side `b` is the tree of the child on side `b` at
its slot. -/
private lemma eighIdealTree_cons (ξ : Dist → ℕ → ℝ) (d lo : ℕ) (xo : Option (EighNode F))
    (pre : List Bool) (b : Bool) (a : List Bool) :
    eighIdealTree M N signFuel D R₀ β ξ d lo xo pre (b :: a) =
      eighIdealTree M N signFuel D R₀ β ξ (d + 1)
        (eighKidSlot lo (eighKids M N signFuel R₀ β xo
          (eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)) b)
        (eighKid (eighKids M N signFuel R₀ β xo
          (eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)) b) (pre ++ [b]) a := by
  cases xo with
  | none => cases b <;> simp [eighIdealTree, eighKids, eighKidSlot, eighKid]
  | some x =>
    simp only [eighIdealTree, eighKids, eighKidSlot, eighKid, Option.bind_some, Option.map_some]
    unfold eighChild
    generalize eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ
      (eighIdealSample ξ N D d lo (some x.k) pre) = st
    cases st with
    | leaf U e => cases b <;> simp
    | shift b' A' σ =>
      cases b <;> cases b' <;> simp only [Bool.false_eq_true, if_false, if_true, Option.map_some,
        Option.getD_some, Option.map_none, Option.getD_none, add_zero, reduceCtorEq]
      exact eighIdealTree_none_slot M N signFuel D R₀ β ξ a _ _ _ _
    | split kp hkp Qp Qm Ap Am σ => cases b <;> simp

end Tree

/-! ### The positions a node reads -/

section Positions

/-- The uniform position of the seed of a node of size `ko` at slot `lo` of depth `d`, reached by
the path `pre`: its static position below the depth budget, and a fresh one otherwise. -/
private def eighRootU (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : ℕ :=
  match ko with
  | some _ => if d < D then N * d + lo else N * D + Encodable.encode pre
  | none => N * D + Encodable.encode pre

/-- The complex Gaussian position of entry $(i, j)$ of the test matrix on side `b` of a node. -/
private def eighRootZ (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) (b : Bool)
    (i j : Fin N) : ℕ :=
  match ko with
  | some k =>
    if d < D ∧ (i : ℕ) < k ∧ (j : ℕ) < k then
      2 * (N * N) * d + N * (2 * (lo + j) + if b then 0 else 1) + i
    else 2 * (N * N) * D + Encodable.encode (pre, b, (i : ℕ), (j : ℕ))
  | none => 2 * (N * N) * D + Encodable.encode (pre, b, (i : ℕ), (j : ℕ))

private lemma eighIdealSample_eq_eighReadSample (ξ : Dist → ℕ → ℝ) (N D d lo : ℕ)
    (ko : Option ℕ) (pre : List Bool) :
    eighIdealSample ξ N D d lo ko pre =
      eighReadSample N (eighRootU N D d lo ko pre) (eighRootZ N D d lo ko pre) ξ := by
  cases ko with
  | none => rfl
  | some k =>
    unfold eighIdealSample eighReadSample eighRootU eighRootZ
    by_cases hd : d < D
    · simp only [hd, if_true, true_and]
      congr 1
      funext b
      ext i j
      simp only [Matrix.of_apply]
      split_ifs <;> rfl
    · simp only [hd, if_false, false_and]

/-- The fresh uniform positions of the paths through `pre`. -/
private def eighFreshU (N D : ℕ) (pre : List Bool) : Set ℕ :=
  {r | ∃ a, pre <+: a ∧ r = N * D + Encodable.encode a}

/-- The fresh complex Gaussian positions of the paths through `pre`. -/
private def eighFreshZ (N D : ℕ) (pre : List Bool) : Set ℕ :=
  {z | ∃ (a : List Bool) (b : Bool) (i j : ℕ), pre <+: a ∧
    z = 2 * (N * N) * D + Encodable.encode (a, b, i, j)}

/-- The uniform positions the subtree of a node of size `ko` at slot `lo` of depth `d` may read:
its own seed, the static seeds of its range at the depths below, and the fresh positions of the
paths through `pre`. -/
private def eighRegionU (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : Set ℕ :=
  {r | ∃ k, ko = some k ∧ ∃ d' j, d ≤ d' ∧ d' < D ∧ ((d' = d ∧ j = lo) ∨ (lo ≤ j ∧ j < lo + k)) ∧
    r = N * d' + j} ∪ eighFreshU N D pre

/-- The complex Gaussian positions the subtree of a node may read. -/
private def eighRegionZ (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : Set ℕ :=
  {z | ∃ k, ko = some k ∧ ∃ d' j s i, d ≤ d' ∧ d' < D ∧ lo ≤ j ∧ j < lo + k ∧ s < 2 ∧ i < N ∧
    z = 2 * (N * N) * d' + N * (2 * j + s) + i} ∪ eighFreshZ N D pre

/-- A node of size `ko` at slot `lo` lies inside the root range. -/
private def EighInv (N lo : ℕ) (ko : Option ℕ) : Prop := ∀ k, ko = some k → lo + k ≤ N

/-- A child of size `ko'` at slot `lo'` fits in the range of its parent of size `ko` at slot `lo`,
and is not empty. -/
private def EighFits (lo : ℕ) (ko : Option ℕ) (lo' : ℕ) (ko' : Option ℕ) : Prop :=
  ∀ k', ko' = some k' → 1 ≤ k' ∧ ∃ k, ko = some k ∧ lo ≤ lo' ∧ lo' + k' ≤ lo + k

private lemma eq_of_mul_add_eq_of_lt {N d₁ d₂ j₁ j₂ : ℕ} (h₁ : j₁ < N) (h₂ : j₂ < N)
    (h : N * d₁ + j₁ = N * d₂ + j₂) : d₁ = d₂ ∧ j₁ = j₂ := by
  have := (Nat.add_mul_eq_add_mul_iff_of_lt (j := d₁) (j' := d₂) h₁ h₂).mp (by omega)
  exact ⟨this.2, this.1⟩

private lemma mul_add_lt_mul_of_lt {N d D j : ℕ} (hj : j < N) (hd : d < D) : N * d + j < N * D :=
  calc N * d + j < N * (d + 1) := by rw [mul_add, mul_one]; omega
    _ ≤ N * D := Nat.mul_le_mul_left _ hd

private lemma mul_add_le_mul_of_le {N d D j : ℕ} (hj : j ≤ N) (hd : d < D) : N * d + j ≤ N * D :=
  calc N * d + j ≤ N * (d + 1) := by rw [mul_add, mul_one]; omega
    _ ≤ N * D := Nat.mul_le_mul_left _ hd

private lemma gaussPos_eq (N d j s i : ℕ) :
    2 * (N * N) * d + N * (2 * j + s) + i = 2 * N * (N * d + j) + (N * s + i) := by ring

private lemma gaussPos_inj {N d₁ d₂ j₁ j₂ s₁ s₂ i₁ i₂ : ℕ} (hj₁ : j₁ < N) (hj₂ : j₂ < N)
    (hs₁ : s₁ < 2) (hs₂ : s₂ < 2) (hi₁ : i₁ < N) (hi₂ : i₂ < N)
    (h : 2 * (N * N) * d₁ + N * (2 * j₁ + s₁) + i₁ = 2 * (N * N) * d₂ + N * (2 * j₂ + s₂) + i₂) :
    d₁ = d₂ ∧ j₁ = j₂ ∧ s₁ = s₂ ∧ i₁ = i₂ := by
  rw [gaussPos_eq, gaussPos_eq] at h
  have hl₁ : N * s₁ + i₁ < 2 * N := by interval_cases s₁ <;> omega
  have hl₂ : N * s₂ + i₂ < 2 * N := by interval_cases s₂ <;> omega
  obtain ⟨hc, hr⟩ := eq_of_mul_add_eq_of_lt hl₁ hl₂ h
  obtain ⟨hd, hj⟩ := eq_of_mul_add_eq_of_lt hj₁ hj₂ hc
  obtain ⟨hs, hi⟩ := eq_of_mul_add_eq_of_lt hi₁ hi₂ hr
  exact ⟨hd, hj, hs, hi⟩

private lemma gaussPos_lt {N d D j s i : ℕ} (hj : j < N) (hd : d < D) (hs : s < 2) (hi : i < N) :
    2 * (N * N) * d + N * (2 * j + s) + i < 2 * (N * N) * D := by
  rw [gaussPos_eq]
  have h1 := mul_add_lt_mul_of_lt hj hd
  have hl : N * s + i < 2 * N := by interval_cases s <;> omega
  calc 2 * N * (N * d + j) + (N * s + i) < 2 * N * (N * d + j) + 2 * N := by omega
    _ = 2 * N * (N * d + j + 1) := by ring
    _ ≤ 2 * N * (N * D) := Nat.mul_le_mul_left _ h1
    _ = 2 * (N * N) * D := by ring

private lemma encode_ne_zero_of_ne_nil {a : List Bool} (h : a ≠ []) : Encodable.encode a ≠ 0 := by
  cases a with
  | nil => exact absurd rfl h
  | cons b a => simp [Encodable.encode_list_cons]

private lemma encode_fst_eq {a a' : List Bool} {b b' : Bool} {i j i' j' : ℕ}
    (h : Encodable.encode (a, b, i, j) = Encodable.encode (a', b', i', j')) : a = a' :=
  (Prod.ext_iff.mp (Encodable.encode_injective h)).1

private lemma prefix_of_append_prefix {pre a : List Bool} {b : Bool} (h : pre ++ [b] <+: a) :
    pre <+: a :=
  (List.prefix_append pre [b]).trans h

private lemma length_lt_of_append_prefix {pre a : List Bool} {b : Bool} (h : pre ++ [b] <+: a) :
    pre.length < a.length := by
  have := h.length_le
  simp only [List.length_append, List.length_singleton] at this
  omega

private lemma not_append_prefix_both {pre a : List Bool} (h₁ : pre ++ [true] <+: a)
    (h₂ : pre ++ [false] <+: a) : False := by
  have h := (List.prefix_of_prefix_length_le h₁ h₂ (by simp)).eq_of_length (by simp)
  simp at h

variable {N D d lo lo' : ℕ} {ko ko' : Option ℕ} {pre : List Bool} {b : Bool}

private lemma side_lt_two (b : Bool) : (if b then 0 else 1 : ℕ) < 2 := by cases b <;> simp

private lemma eighRootU_mem : eighRootU N D d lo ko pre ∈ eighRegionU N D d lo ko pre := by
  cases ko with
  | none => exact Or.inr ⟨pre, List.prefix_refl _, rfl⟩
  | some k =>
    simp only [eighRootU]
    split_ifs with hd
    · exact Or.inl ⟨k, rfl, d, lo, le_rfl, hd, Or.inl ⟨rfl, rfl⟩, rfl⟩
    · exact Or.inr ⟨pre, List.prefix_refl _, rfl⟩

private lemma eighRootZ_mem (b : Bool) (i j : Fin N) :
    eighRootZ N D d lo ko pre b i j ∈ eighRegionZ N D d lo ko pre := by
  cases ko with
  | none => exact Or.inr ⟨pre, b, i, j, List.prefix_refl _, rfl⟩
  | some k =>
    simp only [eighRootZ]
    by_cases h : d < D ∧ (i : ℕ) < k ∧ (j : ℕ) < k
    · rw [if_pos h]
      exact Or.inl ⟨k, rfl, d, lo + j, _, i, le_rfl, h.1, by omega, by omega,
        side_lt_two b, i.2, rfl⟩
    · rw [if_neg h]
      exact Or.inr ⟨pre, b, i, j, List.prefix_refl _, rfl⟩

private lemma eighRegionU_subset (hF : EighFits lo ko lo' ko') :
    eighRegionU N D (d + 1) lo' ko' (pre ++ [b]) ⊆ eighRegionU N D d lo ko pre := by
  rintro r (⟨k', hk', d', j, hd1, hd2, hj, rfl⟩ | ⟨a, ha, rfl⟩)
  · obtain ⟨h1, k, hk, hlo, hhi⟩ := hF k' hk'
    exact Or.inl ⟨k, hk, d', j, by omega, hd2, Or.inr (by omega), rfl⟩
  · exact Or.inr ⟨a, prefix_of_append_prefix ha, rfl⟩

private lemma eighRegionZ_subset (hF : EighFits lo ko lo' ko') :
    eighRegionZ N D (d + 1) lo' ko' (pre ++ [b]) ⊆ eighRegionZ N D d lo ko pre := by
  rintro z (⟨k', hk', d', j, s, i, hd1, hd2, hj1, hj2, hs, hi, rfl⟩ | ⟨a, b', i, j, ha, rfl⟩)
  · obtain ⟨h1, k, hk, hlo, hhi⟩ := hF k' hk'
    exact Or.inl ⟨k, hk, d', j, s, i, by omega, hd2, by omega, by omega, hs, hi, rfl⟩
  · exact Or.inr ⟨a, b', i, j, prefix_of_append_prefix ha, rfl⟩

private lemma eighRootU_not_mem (hI : EighInv N lo ko) (hF : EighFits lo ko lo' ko') :
    eighRootU N D d lo ko pre ∉ eighRegionU N D (d + 1) lo' ko' (pre ++ [b]) := by
  rintro (⟨k', hk', d', j, hd1, hd2, hj, h⟩ | ⟨a, ha, h⟩)
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF k' hk'
    have hk := hI k rfl
    have hjN : j < N := by omega
    simp only [eighRootU] at h
    split_ifs at h with hd
    · have := (eq_of_mul_add_eq_of_lt (by omega) hjN h).1
      omega
    · have := mul_add_lt_mul_of_lt hjN hd2
      omega
  · have hne : a ≠ [] := by
      intro h'
      have := length_lt_of_append_prefix ha
      simp [h'] at this
    have he := encode_ne_zero_of_ne_nil hne
    cases ko with
    | none =>
      simp only [eighRootU, add_right_inj] at h
      have := length_lt_of_append_prefix ha
      rw [Encodable.encode_injective h] at this
      omega
    | some k =>
      simp only [eighRootU] at h
      split_ifs at h with hd
      · have := mul_add_le_mul_of_le (N := N) (j := lo) (by have := hI k rfl; omega) hd
        omega
      · simp only [add_right_inj] at h
        have := length_lt_of_append_prefix ha
        rw [Encodable.encode_injective h] at this
        omega

private lemma eighRootZ_not_mem (hI : EighInv N lo ko) (hF : EighFits lo ko lo' ko') (b' : Bool)
    (i j : Fin N) :
    eighRootZ N D d lo ko pre b' i j ∉ eighRegionZ N D (d + 1) lo' ko' (pre ++ [b]) := by
  rintro (⟨k', hk', d', j', s, i', hd1, hd2, hj1, hj2, hs, hi, h⟩ | ⟨a, b'', i', j', ha, h⟩)
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF k' hk'
    have hk := hI k rfl
    simp only [eighRootZ] at h
    by_cases hc : d < D ∧ (i : ℕ) < k ∧ (j : ℕ) < k
    · rw [if_pos hc] at h
      have := (gaussPos_inj (by omega) (by omega) (side_lt_two b') hs i.2 hi h).1
      omega
    · rw [if_neg hc] at h
      have := gaussPos_lt (N := N) (j := j') (by omega) hd2 hs hi
      omega
  · cases ko with
    | none =>
      simp only [eighRootZ, add_right_inj] at h
      have := length_lt_of_append_prefix ha
      rw [encode_fst_eq h] at this
      omega
    | some k =>
      have hk := hI k rfl
      simp only [eighRootZ] at h
      by_cases hc : d < D ∧ (i : ℕ) < k ∧ (j : ℕ) < k
      · rw [if_pos hc] at h
        have := gaussPos_lt (N := N) (j := lo + j) (by omega) hc.1 (side_lt_two b') i.2
        omega
      · rw [if_neg hc] at h
        simp only [add_right_inj] at h
        have := length_lt_of_append_prefix ha
        rw [encode_fst_eq h] at this
        omega

private lemma disjoint_eighRegionU {lo₁ lo₂ : ℕ} {ko₁ ko₂ : Option ℕ} (hI : EighInv N lo ko)
    (hF₁ : EighFits lo ko lo₁ ko₁) (hF₂ : EighFits lo ko lo₂ ko₂)
    (hS : ∀ k₁ k₂, ko₁ = some k₁ → ko₂ = some k₂ → lo₁ + k₁ ≤ lo₂) :
    Disjoint (eighRegionU N D (d + 1) lo₁ ko₁ (pre ++ [true]))
      (eighRegionU N D (d + 1) lo₂ ko₂ (pre ++ [false])) := by
  rw [Set.disjoint_left]
  rintro r (⟨k₁, hk₁, d₁, j₁, -, hd₁, hj₁, rfl⟩ | ⟨a₁, ha₁, rfl⟩)
    (⟨k₂, hk₂, d₂, j₂, -, hd₂, hj₂, h⟩ | ⟨a₂, ha₂, h⟩)
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₁ k₁ hk₁
    obtain ⟨h1', k', hk', hlo', hhi'⟩ := hF₂ k₂ hk₂
    cases hk'
    have hk := hI k rfl
    have := hS k₁ k₂ hk₁ hk₂
    have := (eq_of_mul_add_eq_of_lt (by omega) (by omega) h).2
    omega
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₁ k₁ hk₁
    have := mul_add_lt_mul_of_lt (N := N) (j := j₁) (by have := hI k rfl; omega) hd₁
    omega
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₂ k₂ hk₂
    have := mul_add_lt_mul_of_lt (N := N) (j := j₂) (by have := hI k rfl; omega) hd₂
    omega
  · simp only [add_right_inj] at h
    rw [Encodable.encode_injective h] at ha₁
    exact not_append_prefix_both ha₁ ha₂

private lemma disjoint_eighRegionZ {lo₁ lo₂ : ℕ} {ko₁ ko₂ : Option ℕ} (hI : EighInv N lo ko)
    (hF₁ : EighFits lo ko lo₁ ko₁) (hF₂ : EighFits lo ko lo₂ ko₂)
    (hS : ∀ k₁ k₂, ko₁ = some k₁ → ko₂ = some k₂ → lo₁ + k₁ ≤ lo₂) :
    Disjoint (eighRegionZ N D (d + 1) lo₁ ko₁ (pre ++ [true]))
      (eighRegionZ N D (d + 1) lo₂ ko₂ (pre ++ [false])) := by
  rw [Set.disjoint_left]
  rintro z (⟨k₁, hk₁, d₁, j₁, s₁, i₁, -, hd₁, hj₁, hj₁', hs₁, hi₁, rfl⟩ |
      ⟨a₁, b₁, i₁, j₁, ha₁, rfl⟩)
    (⟨k₂, hk₂, d₂, j₂, s₂, i₂, -, hd₂, hj₂, hj₂', hs₂, hi₂, h⟩ | ⟨a₂, b₂, i₂, j₂, ha₂, h⟩)
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₁ k₁ hk₁
    obtain ⟨h1', k', hk', hlo', hhi'⟩ := hF₂ k₂ hk₂
    cases hk'
    have hk := hI k rfl
    have := hS k₁ k₂ hk₁ hk₂
    have := (gaussPos_inj (by omega) (by omega) hs₁ hs₂ hi₁ hi₂ h).2.1
    omega
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₁ k₁ hk₁
    have := gaussPos_lt (N := N) (j := j₁) (by have := hI k rfl; omega) hd₁ hs₁ hi₁
    omega
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₂ k₂ hk₂
    have := gaussPos_lt (N := N) (j := j₂) (by have := hI k rfl; omega) hd₂ hs₂ hi₂
    omega
  · simp only [add_right_inj] at h
    rw [encode_fst_eq h] at ha₁
    exact not_append_prefix_both ha₁ ha₂

private lemma injective_eighRootZ (hI : EighInv N lo ko) :
    Function.Injective fun p : Bool × Fin N × Fin N =>
      eighRootZ N D d lo ko pre p.1 p.2.1 p.2.2 := by
  rintro ⟨b₁, i₁, j₁⟩ ⟨b₂, i₂, j₂⟩ h
  dsimp only at h
  have hfresh : ∀ {b₁ b₂ : Bool} {i₁ j₁ i₂ j₂ : Fin N},
      2 * (N * N) * D + Encodable.encode (pre, b₁, (i₁ : ℕ), (j₁ : ℕ)) =
        2 * (N * N) * D + Encodable.encode (pre, b₂, (i₂ : ℕ), (j₂ : ℕ)) →
      (b₁, i₁, j₁) = (b₂, i₂, j₂) := by
    intro b₁ b₂ i₁ j₁ i₂ j₂ h
    simp only [add_right_inj] at h
    have := Encodable.encode_injective h
    simp only [Prod.mk.injEq] at this ⊢
    exact ⟨this.2.1, Fin.ext this.2.2.1, Fin.ext this.2.2.2⟩
  cases ko with
  | none => exact hfresh h
  | some k =>
    have hk := hI k rfl
    simp only [eighRootZ] at h
    by_cases hc₁ : d < D ∧ (i₁ : ℕ) < k ∧ (j₁ : ℕ) < k
    · rw [if_pos hc₁] at h
      by_cases hc₂ : d < D ∧ (i₂ : ℕ) < k ∧ (j₂ : ℕ) < k
      · rw [if_pos hc₂] at h
        obtain ⟨-, hj, hs, hi⟩ := gaussPos_inj (by omega) (by omega) (side_lt_two b₁)
          (side_lt_two b₂) i₁.2 i₂.2 h
        have hb : b₁ = b₂ := by cases b₁ <;> cases b₂ <;> first | rfl | simp at hs
        rw [hb, Fin.ext hi, Fin.ext (by omega : (j₁ : ℕ) = j₂)]
      · rw [if_neg hc₂] at h
        have := gaussPos_lt (N := N) (j := lo + j₁) (by omega) hc₁.1 (side_lt_two b₁) i₁.2
        omega
    · rw [if_neg hc₁] at h
      by_cases hc₂ : d < D ∧ (i₂ : ℕ) < k ∧ (j₂ : ℕ) < k
      · rw [if_pos hc₂] at h
        have := gaussPos_lt (N := N) (j := lo + j₂) (by omega) hc₂.1 (side_lt_two b₂) i₂.2
        omega
      · rw [if_neg hc₂] at h
        exact hfresh h

end Positions

/-! ### The σ-algebras of the positions -/

/-- The tape coordinates at the uniform positions `U` and at the Gaussian words of the complex
positions `Z`. -/
private def tapeLift (U Z : Set ℕ) : Set (Dist × ℕ) :=
  {p | (p.1 = .uniform ∧ p.2 ∈ U) ∨ (p.1 = .gaussian ∧ p.2 / 2 ∈ Z)}

private lemma tapeLift_mono {U U' Z Z' : Set ℕ} (hU : U ⊆ U') (hZ : Z ⊆ Z') :
    tapeLift U Z ⊆ tapeLift U' Z' := by
  rintro p (⟨h1, h2⟩ | ⟨h1, h2⟩)
  exacts [Or.inl ⟨h1, hU h2⟩, Or.inr ⟨h1, hZ h2⟩]

private lemma disjoint_tapeLift {U U' Z Z' : Set ℕ} (hU : Disjoint U U') (hZ : Disjoint Z Z') :
    Disjoint (tapeLift U Z) (tapeLift U' Z') := by
  rw [Set.disjoint_left]
  rintro p (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
  · exact Set.disjoint_left.mp hU h2 h2'
  · rw [h1] at h1'; cases h1'
  · rw [h1] at h1'; cases h1'
  · exact Set.disjoint_left.mp hZ h2 h2'

/-- A sample read at positions inside `U` and `Z` is measurable for the coordinates there. -/
private lemma measurable_eighReadSample {N u : ℕ} {z : Bool → Fin N → Fin N → ℕ} {U Z : Set ℕ}
    (hu : u ∈ U) (hz : ∀ b i j, z b i j ∈ Z) :
    Measurable[tapeSigma (tapeLift U Z)] (eighReadSample N u z) := by
  have hc : ∀ p ∈ tapeLift U Z,
      Measurable[tapeSigma (tapeLift U Z)] fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2 :=
    fun p hp => measurable_tapeSigma_apply hp
  have hpi : ∀ {δ : Type} {X : δ → Type} [∀ a, MeasurableSpace (X a)]
      (f : (Dist → ℕ → ℝ) → ∀ a, X a), (∀ a, Measurable[tapeSigma (tapeLift U Z)] fun c => f c a) →
      Measurable[tapeSigma (tapeLift U Z)] f :=
    fun f hf => @measurable_pi_lambda _ _ _ (tapeSigma (tapeLift U Z)) _ f hf
  refine Measurable.prodMk (hc (.uniform, u) (Or.inl ⟨rfl, hu⟩)) ?_
  refine hpi _ fun b => hpi _ fun i => hpi _ fun j => ?_
  refine measurable_complex_mk ((hc (.gaussian, 2 * z b i j) (Or.inr ⟨rfl, ?_⟩)).div_const _)
    ((hc (.gaussian, 2 * z b i j + 1) (Or.inr ⟨rfl, ?_⟩)).div_const _)
  · rw [show 2 * z b i j / 2 = z b i j by omega]; exact hz b i j
  · rw [show (2 * z b i j + 1) / 2 = z b i j by omega]; exact hz b i j

section Regions

variable {N D d lo : ℕ} {ko : Option ℕ} {pre : List Bool}

/-- The coordinates the subtree of a node may read. -/
private def eighRegion (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : Set (Dist × ℕ) :=
  tapeLift (eighRegionU N D d lo ko pre) (eighRegionZ N D d lo ko pre)

/-- The coordinates the sample of a node reads. -/
private def eighRootPos (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : Set (Dist × ℕ) :=
  tapeLift {eighRootU N D d lo ko pre}
    (Set.range fun p : Bool × Fin N × Fin N => eighRootZ N D d lo ko pre p.1 p.2.1 p.2.2)

private lemma measurable_eighIdealSample :
    Measurable[tapeSigma (eighRootPos N D d lo ko pre)]
      fun ξ => eighIdealSample ξ N D d lo ko pre := by
  simp only [eighIdealSample_eq_eighReadSample]
  exact measurable_eighReadSample (U := {eighRootU N D d lo ko pre})
    (Z := Set.range fun p : Bool × Fin N × Fin N => eighRootZ N D d lo ko pre p.1 p.2.1 p.2.2)
    (Set.mem_singleton _) fun b i j => ⟨(b, i, j), rfl⟩

private lemma eighRootPos_subset : eighRootPos N D d lo ko pre ⊆ eighRegion N D d lo ko pre :=
  tapeLift_mono (Set.singleton_subset_iff.mpr eighRootU_mem)
    (Set.range_subset_iff.mpr fun p => eighRootZ_mem p.1 p.2.1 p.2.2)

private lemma disjoint_eighRootPos {lo' : ℕ} {ko' : Option ℕ} {b : Bool} (hI : EighInv N lo ko)
    (hF : EighFits lo ko lo' ko') :
    Disjoint (eighRootPos N D d lo ko pre) (eighRegion N D (d + 1) lo' ko' (pre ++ [b])) := by
  refine disjoint_tapeLift (Set.disjoint_singleton_left.mpr (eighRootU_not_mem hI hF)) ?_
  rw [Set.disjoint_left]
  rintro _ ⟨p, rfl⟩
  exact eighRootZ_not_mem hI hF p.1 p.2.1 p.2.2

private lemma eighRegion_subset {lo' : ℕ} {ko' : Option ℕ} {b : Bool}
    (hF : EighFits lo ko lo' ko') :
    eighRegion N D (d + 1) lo' ko' (pre ++ [b]) ⊆ eighRegion N D d lo ko pre :=
  tapeLift_mono (eighRegionU_subset hF) (eighRegionZ_subset hF)

private lemma disjoint_eighRegion {lo₁ lo₂ : ℕ} {ko₁ ko₂ : Option ℕ} (hI : EighInv N lo ko)
    (hF₁ : EighFits lo ko lo₁ ko₁) (hF₂ : EighFits lo ko lo₂ ko₂)
    (hS : ∀ k₁ k₂, ko₁ = some k₁ → ko₂ = some k₂ → lo₁ + k₁ ≤ lo₂) :
    Disjoint (eighRegion N D (d + 1) lo₁ ko₁ (pre ++ [true]))
      (eighRegion N D (d + 1) lo₂ ko₂ (pre ++ [false])) :=
  disjoint_tapeLift (disjoint_eighRegionU hI hF₁ hF₂ hS) (disjoint_eighRegionZ hI hF₁ hF₂ hS)

end Regions

section Kids

variable {F : Type*} (M : FloatMachine F ℝ ℂ) (N signFuel : ℕ) (R₀ β : F)

/-- The children of a node fit in its range, are inside the root range, and the positive child
lies left of the negative one. -/
private lemma eighKids_spec {lo : ℕ} {xo : Option (EighNode F)}
    (hI : EighInv N lo (xo.map EighNode.k)) (s : EighSample ℝ ℂ N) :
    (∀ b, EighFits lo (xo.map EighNode.k)
        (eighKidSlot lo (eighKids M N signFuel R₀ β xo s) b)
        ((eighKid (eighKids M N signFuel R₀ β xo s) b).map EighNode.k) ∧
      EighInv N (eighKidSlot lo (eighKids M N signFuel R₀ β xo s) b)
        ((eighKid (eighKids M N signFuel R₀ β xo s) b).map EighNode.k)) ∧
    ∀ k₁ k₂, (eighKid (eighKids M N signFuel R₀ β xo s) true).map EighNode.k = some k₁ →
      (eighKid (eighKids M N signFuel R₀ β xo s) false).map EighNode.k = some k₂ →
      eighKidSlot lo (eighKids M N signFuel R₀ β xo s) true + k₁ ≤
        eighKidSlot lo (eighKids M N signFuel R₀ β xo s) false := by
  cases xo with
  | none =>
    simp [eighKids, eighKid, eighKidSlot, EighFits, EighInv]
  | some x =>
    have hx := hI x.k rfl
    rcases eighChild_cases M N signFuel R₀ β x s with
      ⟨h1, h2⟩ | ⟨y, h1, h2, hy, hk⟩ | ⟨y, h1, h2, hy, hk⟩ | ⟨y, y', h1, h2, hy, hy', hk⟩ <;>
    · refine ⟨fun b => ?_, ?_⟩
      · cases b <;> simp [eighKids, eighKid, eighKidSlot, h1, h2, EighFits, EighInv] <;> omega
      · simp [eighKids, eighKid, eighKidSlot, h1, h2]

private lemma eighNodeAt_singleton (x : EighNode F) (b : Bool) (s : EighSample ℝ ℂ N) :
    eighNodeAt M N signFuel R₀ β [b] x (fun _ => s) = eighChild M N signFuel R₀ β x s b := by
  simp [eighNodeAt]

private lemma countable_range_eighKids (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalc : (Set.range M.normal).Countable) (xo : Option (EighNode F)) :
    (Set.range (eighKids M N signFuel R₀ β xo)).Countable := by
  cases xo with
  | none =>
    refine (Set.countable_singleton (none, none)).mono ?_
    rintro _ ⟨s, rfl⟩
    rfl
  | some x =>
    have h : ∀ b, (Set.range fun s : EighSample ℝ ℂ N =>
        eighChild M N signFuel R₀ β x s b).Countable :=
      fun b => (countable_range_eighNodeAt hunifc hnormalc N signFuel R₀ β [b] x).mono (by
        rintro _ ⟨s, rfl⟩
        exact ⟨fun _ => s, eighNodeAt_singleton M N signFuel R₀ β x b s⟩)
    refine ((h true).prod (h false)).mono ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨⟨s, rfl⟩, ⟨s, rfl⟩⟩

private lemma measurableSet_eighKids_preimage (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (xo : Option (EighNode F)) (c : Option (EighNode F) × Option (EighNode F)) :
    MeasurableSet (eighKids M N signFuel R₀ β xo ⁻¹' {c}) := by
  cases xo with
  | none => exact MeasurableSet.const ((none, none) = c)
  | some x =>
    have h : ∀ b y, MeasurableSet {s : EighSample ℝ ℂ N | eighChild M N signFuel R₀ β x s b = y} :=
      fun b y => by
        have := measurableSet_eighNodeAt_eq hunifm hunifc hnormalm hnormalc (N := N)
          (signFuel := signFuel) (R₀ := R₀) (β := β) (ζ := fun _ s => s)
          (fun _ => measurable_id) [b] x y
        simpa only [eighNodeAt_singleton] using this
    have : eighKids M N signFuel R₀ β (some x) ⁻¹' {c} =
        {s | eighChild M N signFuel R₀ β x s true = c.1} ∩
          {s | eighChild M N signFuel R₀ β x s false = c.2} := by
      ext s
      simp [eighKids, Prod.ext_iff]
    rw [this]
    exact (h true c.1).inter (h false c.2)

end Kids

/-! ### Lazy sampling -/

/-- A map that is chosen among countably many measurable maps by a function with measurable fibres
is measurable. -/
private lemma measurable_of_countable_cases {α β γ : Type*} {m : MeasurableSpace α}
    [MeasurableSpace γ] {κ : α → β} {g : β → α → γ} (hc : (Set.range κ).Countable)
    (hκ : ∀ c, MeasurableSet[m] (κ ⁻¹' {c})) (hg : ∀ c ∈ Set.range κ, Measurable[m] (g c)) :
    Measurable[m] fun x => g (κ x) x := by
  intro B hB
  have : (fun x => g (κ x) x) ⁻¹' B = ⋃ c ∈ Set.range κ, κ ⁻¹' {c} ∩ g c ⁻¹' B := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff,
      Set.mem_range, exists_prop]
    exact ⟨fun h => ⟨κ x, ⟨x, rfl⟩, rfl, h⟩, fun ⟨c, _, hc, h⟩ => hc ▸ h⟩
  rw [this]
  exact MeasurableSet.biUnion hc fun c hc' => (hκ c).inter (hg c hc' hB)

/-- A product over a finite set of paths: the empty path, then the paths through each side. -/
private lemma prod_eq_mul_prod_preimage_cons {β : Type*} [CommMonoid β] (S : Finset (List Bool))
    (g : List Bool → β) :
    ∏ a ∈ S, g a = (if [] ∈ S then g [] else 1) *
      ((∏ a ∈ S.preimage (List.cons true) List.cons_injective.injOn, g (true :: a)) *
        ∏ a ∈ S.preimage (List.cons false) List.cons_injective.injOn, g (false :: a)) := by
  have hside : ∀ b : Bool, ∏ a ∈ S.preimage (List.cons b) List.cons_injective.injOn, g (b :: a) =
      ∏ a ∈ S, if a.head? = some b then g a else 1 := by
    intro b
    rw [← Finset.prod_preimage (List.cons b) S List.cons_injective.injOn]
    · simp
    · intro x _ hx
      rw [if_neg]
      rintro h
      cases x with
      | nil => simp at h
      | cons c l =>
        simp only [List.head?_cons, Option.some.injEq] at h
        exact hx ⟨l, by rw [h]⟩
  have hnil : (if [] ∈ S then g [] else 1) = ∏ a ∈ S, if a = [] then g a else 1 := by
    rw [Finset.prod_ite_eq']
  rw [hside, hside, hnil, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rcases a with _ | ⟨_ | _, l⟩ <;> simp

/-- Splitting an event by the countably many values of a function with measurable fibres. -/
private lemma tsum_measure_preimage_inter_fibre {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace γ] (μ : Measure α) {f : α → γ} (hf : Measurable f) {κ : γ → β}
    (hc : (Set.range κ).Countable) (hκ : ∀ c, MeasurableSet (κ ⁻¹' {c})) {B : Set γ}
    (hB : MeasurableSet B) :
    ∑' c : Set.range κ, μ (f ⁻¹' (κ ⁻¹' {c.1} ∩ B)) = μ (f ⁻¹' B) := by
  rw [← measure_biUnion hc (fun c₁ _ c₂ _ hne => Set.disjoint_left.mpr fun x h₁ h₂ =>
      hne (h₁.1.symm.trans h₂.1)) fun c _ => hf ((hκ c).inter hB)]
  congr 1
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff,
    Set.mem_range, exists_prop]
  exact ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨_, ⟨_, rfl⟩, rfl, h⟩⟩

section Lazy

variable {F : Type*} (M : FloatMachine F ℝ ℂ) (N signFuel D : ℕ) (R₀ β : F)
  (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
  (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
  (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)

include hunifm hunifc hnormalm hnormalc in
/-- The subtree of a node is measurable for the coordinates it may read. -/
private lemma measurable_eighIdealTree (a : List Bool) :
    ∀ (d lo : ℕ) (xo : Option (EighNode F)) (pre : List Bool),
      EighInv N lo (xo.map EighNode.k) →
      Measurable[tapeSigma (eighRegion N D d lo (xo.map EighNode.k) pre)]
        fun ξ => eighIdealTree M N signFuel D R₀ β ξ d lo xo pre a := by
  induction a with
  | nil =>
    intro d lo xo pre _
    simp only [eighIdealTree, eighIdealSample_eq_eighReadSample]
    exact measurable_eighReadSample eighRootU_mem fun b i j => eighRootZ_mem b i j
  | cons b a ih =>
    intro d lo xo pre hI
    simp only [eighIdealTree_cons]
    have hs₀ : Measurable[tapeSigma (eighRegion N D d lo (xo.map EighNode.k) pre)]
        fun ξ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre := by
      exact measurable_eighIdealSample.mono (tapeSigma_mono eighRootPos_subset) le_rfl
    refine measurable_of_countable_cases
      (κ := fun ξ => eighKids M N signFuel R₀ β xo
        (eighIdealSample ξ N D d lo (xo.map EighNode.k) pre))
      (g := fun c ξ => eighIdealTree M N signFuel D R₀ β ξ (d + 1) (eighKidSlot lo c b)
        (eighKid c b) (pre ++ [b]) a) ?_ ?_ ?_
    · exact (countable_range_eighKids M N signFuel R₀ β hunifc hnormalc xo).mono
        (Set.range_comp_subset_range
          (fun ξ : Dist → ℕ → ℝ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)
          (eighKids M N signFuel R₀ β xo))
    · exact fun c => hs₀ (measurableSet_eighKids_preimage M N signFuel R₀ β hunifm hunifc hnormalm
        hnormalc xo c)
    · rintro _ ⟨ξ, rfl⟩
      obtain ⟨hk, -⟩ := eighKids_spec M N signFuel R₀ β hI
        (eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)
      exact (ih _ _ _ _ (hk b).2).mono (tapeSigma_mono (eighRegion_subset (hk b).1)) le_rfl

/-- The event that the sample of a node lies in `B` and gives the children `c`. -/
private def eighRootEvent (d lo : ℕ) (xo : Option (EighNode F)) (pre : List Bool)
    (B : Set (EighSample ℝ ℂ N)) (c : Option (EighNode F) × Option (EighNode F)) :
    Set (Dist → ℕ → ℝ) :=
  (fun ξ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre) ⁻¹'
    (eighKids M N signFuel R₀ β xo ⁻¹' {c} ∩ B)

/-- The event that the samples of the subtree of the child on side `b`, of the children `c`, lie
in the sets `A` at the paths through `b` of `S`. -/
private def eighKidEvent (d lo : ℕ) (pre : List Bool) (S : Finset (List Bool))
    (A : List Bool → Set (EighSample ℝ ℂ N)) (c : Option (EighNode F) × Option (EighNode F))
    (b : Bool) : Set (Dist → ℕ → ℝ) :=
  ⋂ a ∈ S.preimage (List.cons b) List.cons_injective.injOn,
    (fun ξ => eighIdealTree M N signFuel D R₀ β ξ (d + 1) (eighKidSlot lo c b) (eighKid c b)
      (pre ++ [b]) a) ⁻¹' A (b :: a)

/-- The event of the samples of a tree at the paths of `S`, split by the children of its node. -/
private lemma inter_iInter_eighIdealTree_eq (d lo : ℕ) (xo : Option (EighNode F))
    (pre : List Bool) (S : Finset (List Bool)) (A : List Bool → Set (EighSample ℝ ℂ N))
    (G : Set (Dist → ℕ → ℝ)) :
    G ∩ ⋂ a ∈ S, (fun ξ => eighIdealTree M N signFuel D R₀ β ξ d lo xo pre a) ⁻¹' A a =
      ⋃ c ∈ Set.range (eighKids M N signFuel R₀ β xo),
        ((G ∩ eighRootEvent M N signFuel D R₀ β d lo xo pre
            (if [] ∈ S then A [] else Set.univ) c) ∩
          eighKidEvent M N signFuel D R₀ β d lo pre S A c false) ∩
        eighKidEvent M N signFuel D R₀ β d lo pre S A c true := by
  ext ξ
  simp only [eighRootEvent, eighKidEvent, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    Set.mem_iUnion, Set.mem_range, exists_prop, Set.mem_singleton_iff, Finset.mem_preimage]
  constructor
  · rintro ⟨hGξ, hall⟩
    refine ⟨_, ⟨_, rfl⟩, ⟨⟨hGξ, rfl, ?_⟩, fun a ha => ?_⟩, fun a ha => ?_⟩
    · split_ifs with h
      · exact hall [] h
      · trivial
    · have := hall _ ha
      rwa [eighIdealTree_cons] at this
    · have := hall _ ha
      rwa [eighIdealTree_cons] at this
  · rintro ⟨c, -, ⟨⟨hGξ, hc, hB⟩, hf⟩, ht⟩
    refine ⟨hGξ, fun a ha => ?_⟩
    rcases a with _ | ⟨b, a⟩
    · rw [if_pos ha] at hB
      exact hB
    · rw [eighIdealTree_cons, hc]
      cases b
      · exact hf a ha
      · exact ht a ha

include hunifm hunifc hnormalm hnormalc in
/-- **One piece of the event**: given the product formula for the two children (the induction
hypothesis), the probability that `G`, the sample of the node in `B₀` with children `c`, and the
events of the two subtrees all hold is the product. -/
private lemma measure_eighRootEvent_inter_eighKidEvent {d lo : ℕ} {xo : Option (EighNode F)}
    {pre : List Bool} (hI : EighInv N lo (xo.map EighNode.k)) (s : EighSample ℝ ℂ N)
    {S : Finset (List Bool)} {A : List Bool → Set (EighSample ℝ ℂ N)}
    (hA : ∀ a, MeasurableSet (A a)) {G : Set (Dist → ℕ → ℝ)}
    (hG : MeasurableSet[tapeSigma (eighRegion N D d lo (xo.map EighNode.k) pre)ᶜ] G)
    {B₀ : Set (EighSample ℝ ℂ N)} (hB₀ : MeasurableSet B₀)
    (hkid : ∀ b G', MeasurableSet[tapeSigma (eighRegion N D (d + 1)
          (eighKidSlot lo (eighKids M N signFuel R₀ β xo s) b)
          ((eighKid (eighKids M N signFuel R₀ β xo s) b).map EighNode.k) (pre ++ [b]))ᶜ] G' →
        tapeLaw (G' ∩ eighKidEvent M N signFuel D R₀ β d lo pre S A
          (eighKids M N signFuel R₀ β xo s) b) =
        tapeLaw G' * ∏ a ∈ S.preimage (List.cons b) List.cons_injective.injOn,
          eighSampleLaw N (A (b :: a))) :
    tapeLaw (((G ∩ eighRootEvent M N signFuel D R₀ β d lo xo pre B₀
        (eighKids M N signFuel R₀ β xo s)) ∩
        eighKidEvent M N signFuel D R₀ β d lo pre S A (eighKids M N signFuel R₀ β xo s) false) ∩
        eighKidEvent M N signFuel D R₀ β d lo pre S A (eighKids M N signFuel R₀ β xo s) true) =
      tapeLaw G * tapeLaw (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀
          (eighKids M N signFuel R₀ β xo s)) *
        ((∏ a ∈ S.preimage (List.cons true) List.cons_injective.injOn,
            eighSampleLaw N (A (true :: a))) *
          ∏ a ∈ S.preimage (List.cons false) List.cons_injective.injOn,
            eighSampleLaw N (A (false :: a))) := by
  obtain ⟨hk, hslot⟩ := eighKids_spec M N signFuel R₀ β hI s
  have hKm : MeasurableSet[tapeSigma (eighRootPos N D d lo (xo.map EighNode.k) pre)]
      (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ (eighKids M N signFuel R₀ β xo s)) :=
    measurable_eighIdealSample ((measurableSet_eighKids_preimage M N signFuel R₀ β hunifm hunifc
      hnormalm hnormalc xo _).inter hB₀)
  have hEm : MeasurableSet[tapeSigma (eighRegion N D (d + 1)
      (eighKidSlot lo (eighKids M N signFuel R₀ β xo s) false)
      ((eighKid (eighKids M N signFuel R₀ β xo s) false).map EighNode.k) (pre ++ [false]))]
      (eighKidEvent M N signFuel D R₀ β d lo pre S A (eighKids M N signFuel R₀ β xo s) false) :=
    Finset.measurableSet_biInter _ fun a _ =>
      measurable_eighIdealTree M N signFuel D R₀ β hunifm hunifc hnormalm hnormalc a _ _ _ _
        (hk false).2 (hA _)
  have hdisj := disjoint_eighRegion (D := D) (d := d) (pre := pre) hI (hk true).1 (hk false).1
    hslot
  have hGt := tapeSigma_mono (Set.compl_subset_compl.mpr (eighRegion_subset (D := D) (d := d)
    (pre := pre) (b := true) (hk true).1)) _ hG
  have hGf := tapeSigma_mono (Set.compl_subset_compl.mpr (eighRegion_subset (D := D) (d := d)
    (pre := pre) (b := false) (hk false).1)) _ hG
  have hKt := tapeSigma_mono (disjoint_eighRootPos (D := D) (d := d) (pre := pre) (b := true)
    hI (hk true).1).subset_compl_right _ hKm
  have hKf := tapeSigma_mono (disjoint_eighRootPos (D := D) (d := d) (pre := pre) (b := false)
    hI (hk false).1).subset_compl_right _ hKm
  rw [hkid true _ ((hGt.inter hKt).inter (tapeSigma_mono hdisj.subset_compl_left _ hEm)),
    hkid false _ (hGf.inter hKf),
    (Indep_iff _ _ _).mp (indep_tapeSigma (Set.disjoint_compl_left_iff_subset.mpr
      eighRootPos_subset)) _ _ hG hKm]
  ring

include hunifm hunifc hnormalm hnormalc in
/-- **Lazy sampling, the induction**: for a node inside the root range, an event `G` of the
coordinates outside the region of its subtree, and finitely many paths of length below `L`, the
probability that `G` holds and the subtree's samples at the paths lie in measurable sets is the
probability of `G` times the product of their `NLAlib.eighSampleLaw` masses. -/
private lemma measure_inter_iInter_eighIdealTree (L : ℕ) :
    ∀ (d lo : ℕ) (xo : Option (EighNode F)) (pre : List Bool),
      EighInv N lo (xo.map EighNode.k) →
      ∀ (S : Finset (List Bool)), (∀ a ∈ S, a.length < L) →
      ∀ (A : List Bool → Set (EighSample ℝ ℂ N)), (∀ a, MeasurableSet (A a)) →
      ∀ G, MeasurableSet[tapeSigma (eighRegion N D d lo (xo.map EighNode.k) pre)ᶜ] G →
        tapeLaw (G ∩ ⋂ a ∈ S,
            (fun ξ => eighIdealTree M N signFuel D R₀ β ξ d lo xo pre a) ⁻¹' A a) =
          tapeLaw G * ∏ a ∈ S, eighSampleLaw N (A a) := by
  induction L with
  | zero =>
    intro d lo xo pre _ S hS A _ G _
    have : S = ∅ := Finset.eq_empty_of_forall_notMem fun a ha => by have := hS a ha; omega
    subst this
    simp
  | succ L ih =>
    intro d lo xo pre hI S hS A hA G hG
    -- the sample of the node, its law, and the children it gives
    have hs₀m := measurable_eighIdealSample (N := N) (D := D) (d := d) (lo := lo)
      (ko := xo.map EighNode.k) (pre := pre)
    have hs₀law : HasLaw (fun ξ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)
        (eighSampleLaw N) tapeLaw := by
      simp only [eighIdealSample_eq_eighReadSample]
      exact hasLaw_eighReadSample N _ _ (injective_eighRootZ hI)
    have hC := countable_range_eighKids M N signFuel R₀ β hunifc hnormalc xo
    have hκm := measurableSet_eighKids_preimage M N signFuel R₀ β hunifm hunifc hnormalm hnormalc
      xo
    set B₀ : Set (EighSample ℝ ℂ N) := if [] ∈ S then A [] else Set.univ with hB₀def
    have hB₀ : MeasurableSet B₀ := by
      rw [hB₀def]; split_ifs; exacts [hA [], MeasurableSet.univ]
    have hKm : ∀ c, MeasurableSet[tapeSigma (eighRootPos N D d lo (xo.map EighNode.k) pre)]
        (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c) :=
      fun c => hs₀m ((hκm c).inter hB₀)
    -- each piece: independence of the node's sample from `G`, then the two children
    have hpiece : ∀ c ∈ Set.range (eighKids M N signFuel R₀ β xo),
        tapeLaw (((G ∩ eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c) ∩
            eighKidEvent M N signFuel D R₀ β d lo pre S A c false) ∩
            eighKidEvent M N signFuel D R₀ β d lo pre S A c true) =
          tapeLaw G * tapeLaw (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c) *
            ((∏ a ∈ S.preimage (List.cons true) List.cons_injective.injOn,
                eighSampleLaw N (A (true :: a))) *
              ∏ a ∈ S.preimage (List.cons false) List.cons_injective.injOn,
                eighSampleLaw N (A (false :: a))) := by
      rintro _ ⟨s, rfl⟩
      refine measure_eighRootEvent_inter_eighKidEvent M N signFuel D R₀ β hunifm hunifc hnormalm
        hnormalc hI s hA hG hB₀ fun b G' hG' => ih _ _ _ _ ((eighKids_spec M N signFuel R₀ β hI
          s).1 b).2 _ (fun a ha => ?_) (fun a => A (b :: a)) (fun a => hA _) G' hG'
      have := hS _ (Finset.mem_preimage.mp ha)
      simp only [List.length_cons] at this
      omega
    -- the sum over the children
    have hs₀m' := hs₀m.mono (tapeSigma_le _) le_rfl
    have hKsum : ∑' c : Set.range (eighKids M N signFuel R₀ β xo),
        tapeLaw (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c) =
          if [] ∈ S then eighSampleLaw N (A []) else 1 := by
      rw [show (fun c : Set.range (eighKids M N signFuel R₀ β xo) =>
          tapeLaw (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c)) =
          fun c => tapeLaw ((fun ξ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre) ⁻¹'
            (eighKids M N signFuel R₀ β xo ⁻¹' {c.1} ∩ B₀)) from rfl,
        tsum_measure_preimage_inter_fibre tapeLaw hs₀m' hC hκm hB₀,
        ← Measure.map_apply hs₀m' hB₀, hs₀law.map_eq, hB₀def]
      split_ifs
      · rfl
      · rw [← hs₀law.map_eq, Measure.map_apply hs₀m' MeasurableSet.univ, Set.preimage_univ,
          measure_univ]
    rw [inter_iInter_eighIdealTree_eq, measure_biUnion hC ?_ ?_,
      tsum_congr fun (c : Set.range (eighKids M N signFuel R₀ β xo)) => hpiece c.1 c.2,
      ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hKsum,
      prod_eq_mul_prod_preimage_cons S, mul_assoc]
    · intro c₁ _ c₂ _ hne
      refine Set.disjoint_left.mpr fun ξ h₁ h₂ => hne ?_
      exact h₁.1.1.2.1.symm.trans h₂.1.1.2.1
    · rintro _ ⟨s, rfl⟩
      obtain ⟨hk, -⟩ := eighKids_spec M N signFuel R₀ β hI s
      refine (((tapeSigma_le _ _ hG).inter (tapeSigma_le _ _ (hKm _))).inter ?_).inter ?_ <;>
      exact Finset.measurableSet_biInter _ fun a _ => (measurable_eighIdealTree M N signFuel D R₀ β
        hunifm hunifc hnormalm hnormalc a _ _ _ _ (hk _).2).mono (tapeSigma_le _) le_rfl (hA _)

end Lazy

/-- **Lazy sampling**: on an ideal tape $\xi$ of law `NLAlib.Computation.tapeLaw`, for a machine
over ideal samples whose samplers have measurable fibres and countable ranges, the tree of ideal
samples of `NLAlib.eighIdealTree` from a node of size at most $N$ at slot $0$ of depth $0$ is
independent, with law `NLAlib.eighSampleLaw` $N$ at every path. The positions a node reads are a
function of the samples of the nodes above it, and they are disjoint from the positions of every
other node (static positions of distinct slots of one depth, of distinct depths, and positions
beyond the program's draws indexed by the path). Nothing in Mathlib is a precedent. No printed
source.
Proof: it suffices to show that for every finite set $S$ of paths the joint law of the samples at
$S$ is the product (through `MeasureTheory.Measure.pi`); induction on the largest length in $S$:
condition on the σ-algebra of the samples at the shorter paths (`MeasureTheory.condExp`, or the
kernel form `ProbabilityTheory.Kernel`); the node at each path of the largest length is a
countably-valued measurable function of those samples (as `NLAlib.countable_range_eighNodeAt` and
`NLAlib.measurableSet_eighNodeAt_eq` show for the shallow tree), and on each of its values the
samples at the paths of the largest length are the tape at fixed, pairwise disjoint sets of
positions, independent of the shorter paths' positions (`ProbabilityTheory.iIndepFun.comp`, the
product structure of `NLAlib.Computation.tapeLaw`, `MeasureTheory.Measure.infinitePi`), so their
conditional law is the product of `NLAlib.eighSampleLaw` (the uniform seed
`NLAlib.Computation.Dist.law_uniform_Icc`, the complex Gaussian entries as the pilot's
`NLAlib.Computation.hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw`). H, about 600+ lines (a general
lemma "adaptively chosen disjoint blocks of an i.i.d. sequence are i.i.d." first, then this
instance). -/
theorem iIndepFun_eighIdealTree {F : Type*} (M : FloatMachine F ℝ ℂ)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (N signFuel D : ℕ) (R₀ β : F) (x : EighNode F) (hx : x.k ≤ N) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) :
    iIndepFun (fun a ω => eighIdealTree M N signFuel D R₀ β (ξ ω) 0 0 (some x) [] a) μ ∧
      ∀ a, HasLaw (fun ω => eighIdealTree M N signFuel D R₀ β (ξ ω) 0 0 (some x) [] a)
        (eighSampleLaw N) μ := by
  have hI : EighInv N 0 ((some x).map EighNode.k) := fun k hk => by
    simp only [Option.map_some, Option.some.injEq] at hk
    omega
  have hTm : ∀ a, Measurable fun θ => eighIdealTree M N signFuel D R₀ β θ 0 0 (some x) [] a :=
    fun a => (measurable_eighIdealTree M N signFuel D R₀ β hunifm hunifc hnormalm hnormalc a 0 0
      (some x) [] hI).mono (tapeSigma_le _) le_rfl
  -- the product formula on the canonical space
  have key : ∀ (S : Finset (List Bool)) (A : List Bool → Set (EighSample ℝ ℂ N)),
      (∀ a, MeasurableSet (A a)) →
      tapeLaw (⋂ a ∈ S, (fun θ => eighIdealTree M N signFuel D R₀ β θ 0 0 (some x) [] a) ⁻¹' A a) =
        ∏ a ∈ S, eighSampleLaw N (A a) := by
    intro S A hA
    have := measure_inter_iInter_eighIdealTree M N signFuel D R₀ β hunifm hunifc hnormalm hnormalc
      (S.sup List.length + 1) 0 0 (some x) [] hI S
      (fun a ha => Nat.lt_succ_of_le (Finset.le_sup (f := List.length) ha)) A hA Set.univ
      MeasurableSet.univ
    simpa only [Set.univ_inter, measure_univ, one_mul] using this
  have hlaw : ∀ a, HasLaw (fun ω => eighIdealTree M N signFuel D R₀ β (ξ ω) 0 0 (some x) [] a)
      (eighSampleLaw N) μ := by
    intro a
    refine (HasLaw.mk (hTm a).aemeasurable ?_).comp hξ
    ext B hB
    rw [Measure.map_apply (hTm a) hB]
    simpa using key {a} (fun _ => B) fun _ => hB
  refine ⟨?_, hlaw⟩
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  classical
  set A : List Bool → Set (EighSample ℝ ℂ N) := fun a => if a ∈ S then sets a else Set.univ
    with hAdef
  have hA : ∀ a, MeasurableSet (A a) := fun a => by
    rw [hAdef]; dsimp only; split_ifs with h; exacts [hsets a h, MeasurableSet.univ]
  have hAS : ∀ a ∈ S, A a = sets a := fun a ha => by rw [hAdef]; dsimp only; rw [if_pos ha]
  have hpre : ∀ B, MeasurableSet B → μ (ξ ⁻¹' B) = tapeLaw B := fun B hB => by
    rw [← hξ.map_eq, Measure.map_apply_of_aemeasurable hξ.aemeasurable hB]
  calc μ (⋂ a ∈ S, (fun ω => eighIdealTree M N signFuel D R₀ β (ξ ω) 0 0 (some x) [] a) ⁻¹'
          sets a)
      = μ (ξ ⁻¹' ⋂ a ∈ S,
          (fun θ => eighIdealTree M N signFuel D R₀ β θ 0 0 (some x) [] a) ⁻¹' A a) := by
        congr 1
        ext ω
        simp only [Set.mem_iInter, Set.mem_preimage]
        exact forall₂_congr fun a ha => by rw [hAS a ha]
    _ = ∏ a ∈ S, eighSampleLaw N (A a) := by
        rw [hpre _ (Finset.measurableSet_biInter _ fun a _ => hTm a (hA a)), key S A hA]
    _ = _ := by
        refine Finset.prod_congr rfl fun a ha => ?_
        rw [hAS a ha, ← (hlaw a).map_eq,
          Measure.map_apply_of_aemeasurable (hlaw a).aemeasurable (hsets a ha)]

end NLAlib

namespace NLAlib.Computation

variable {P K : Type} [Inhabited K]

/-! ### The ideal machine -/

/-- **The uniform shift of a tape rounding meets the uniform-sampler contract**: if `sem` meets the
standard model at $u \ge 0$ with every value in range and `NLAlib.Computation.MulShrinks`, and the
rounding $\rho$ of a seed $v \in [-1, 1]$ errs by at most $c\,u\lvert v \rvert$ and stays in
$[-1, 1]$, then `NLAlib.Computation.ScalarSem.uniformUnif` of $\rho$ meets `NLAlib.IsUnifSampler`
at unit roundoff $(c + 1)u$ and floor $0$. No printed source.
Proof: the product succeeds (`bin_ok`, `trivial`); its modulus is at most $\bar s$ by `hmul` (the
factor $\overline{\rho(v)} \in [-1, 1]$); its error is
$\lvert \bar s v - \bar z \rvert \le \bar s\lvert v - \overline{\rho(v)}\rvert +
\lvert \bar s\overline{\rho(v)} - \bar z \rvert \le \bar s c u + u\bar s$ (`bin_err`,
`abs_sub_le`, `abs_mul`). M, about 40 lines. -/
theorem isUnifSampler_uniformUnif {sem : ScalarSem P K} {dec : P → K → ℝ} {u c : ℝ}
    (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem) (hmul : MulShrinks dec sem)
    (p : P) {ρ : ℝ → K} (hρ : ∀ v : ℝ, |v| ≤ 1 → |dec p (ρ v) - v| ≤ c * u * |v|)
    (hρI : ∀ v ∈ Set.Icc (-1 : ℝ) 1, dec p (ρ v) ∈ Set.Icc (-1 : ℝ) 1) (hu : 0 ≤ u) (hc : 0 ≤ c) :
    IsUnifSampler (dec p) ((c + 1) * u) 0 (sem.uniformUnif p ρ) := by
  intro s v hs hv
  have hrI : |dec p (ρ v)| ≤ 1 := abs_le.mpr (hρI v hv)
  have hvabs : |v| ≤ 1 := abs_le.mpr hv
  obtain ⟨z', hz'⟩ := hsem.bin_ok p .mul s (ρ v) trivial (fun h => by cases h) trivial
  obtain ⟨δ, hδ, hzd⟩ := hsem.bin_err p .mul s (ρ v) z' trivial hz'
  have hmz := hmul p s (ρ v) z' hz' hrI
  have hzeq : sem.uniformUnif p ρ s v = z' := by
    change (sem.bin p .mul s (ρ v)).getD default = z'
    rw [hz']; rfl
  rw [hzeq, max_eq_left hs]
  rw [abs_of_nonneg hs] at hmz
  simp only [BinOp.realOp] at hzd
  refine ⟨hmz, ?_⟩
  rw [hzd]
  have key : dec p s * v - dec p s * dec p (ρ v) * (1 + δ) =
      dec p s * (v - dec p (ρ v)) - dec p s * dec p (ρ v) * δ := by ring
  have hvr : |v - dec p (ρ v)| ≤ c * u * |v| := by
    rw [abs_sub_comm]; exact hρ v hvabs
  have hrδ : |dec p (ρ v)| * |δ| ≤ u := by
    calc |dec p (ρ v)| * |δ| ≤ 1 * u := mul_le_mul hrI hδ (abs_nonneg _) zero_le_one
      _ = u := one_mul u
  rw [key]
  calc |dec p s * (v - dec p (ρ v)) - dec p s * dec p (ρ v) * δ|
      ≤ |dec p s * (v - dec p (ρ v))| + |dec p s * dec p (ρ v) * δ| := abs_sub _ _
    _ = dec p s * |v - dec p (ρ v)| + dec p s * (|dec p (ρ v)| * |δ|) := by
        simp only [abs_mul, abs_of_nonneg hs, mul_assoc]
    _ ≤ dec p s * (c * u * |v|) + dec p s * u :=
        add_le_add (mul_le_mul_of_nonneg_left hvr hs) (mul_le_mul_of_nonneg_left hrδ hs)
    _ ≤ (c + 1) * u * dec p s := by
        nlinarith [mul_le_mul_of_nonneg_left hvabs (mul_nonneg (mul_nonneg hs hc) hu)]

/-- **The ideal machine is accurate**: if `sem` meets the standard model at $u \ge 0$ with every
value in range, exact literals up to $2$, the exact floor conversion and
`NLAlib.Computation.MulShrinks`, the routines meet `NLAlib.IsMatMulErr` and `NLAlib.IsQRErr` at $u$,
floor $0$, range $\Omega$, and the tape rounding $\rho$ meets `NLAlib.Computation.IsTapeRounding` at
$u$, floor $0$, range $2\Omega$, constants $c(d) \ge 0$, with $(c(\mathrm{gaussian}) + 3)u \le 1/10$
and the tape range covering the seeds ($1 \le 2\Omega$; without it the tape contract does not
constrain the rounding of a seed), then the machine of the semantics with the conversion of the
semantics, the routines and the samplers of $\rho$ at position $0$ meets
`NLAlib.FloatMachine.IsAccurate` at the unit roundoff $u_{\mathrm M} = (c(\mathrm{uniform}) + 1)u$,
floor $0$, range $\Omega$ and normal-sampler constant $2(c(\mathrm{gaussian}) + 3)$. No printed
source.
Proof: the conversion is the floor of the decoding (`funext`, `htn`, `Option.getD_some`); the
pilot's `NLAlib.Computation.isAccurate_toFloatMachine` (scaffold) at $u_{\mathrm M} \ge u$
(`NLAlib.Computation.IsRelErrSem.mono`; the kernel contracts at $u_{\mathrm M}$, monotone in $u$ by
their definitions), with the uniform sampler by `NLAlib.Computation.isUnifSampler_uniformUnif` (its
error hypothesis from the first clause of `hρ` at $\lvert v \rvert \le 1 \le 2\Omega$, `hΩ`,
`max_eq_left`) and the normal sampler by the pilot's
`NLAlib.Computation.isNormalSampler_gaussianNormal` (scaffold), raised from $u$ to $u_{\mathrm M}$
(`mul_le_mul_of_nonneg_left`). M, about 60 lines. -/
theorem isAccurate_eighIdealMachine {sem : ScalarSem P K} {dec : P → K → ℝ} {u Ω : ℝ}
    {μM μQ : ℕ → ℝ} {c : Dist → ℝ} (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem)
    (hlit : IsExactIntLit dec sem 2) (htn : IsExactToNat dec sem) (hmul : MulShrinks dec sem)
    (p : P) {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
    (hmm : IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mm)
    (hqr : IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qr) {ρ : Dist → ℕ → ℝ → K}
    (hρ : IsTapeRounding dec p u 0 (2 * Ω) c ρ) (hΩ : 1 ≤ 2 * Ω) (hu : 0 ≤ u) (hcu : 0 ≤ c .uniform)
    (hcg : 0 ≤ c .gaussian) (hcgu : (c .gaussian + 3) * u ≤ 1 / 10) (hμM : ∀ d, 0 ≤ μM d)
    (hμQ : ∀ d, 0 ≤ μQ d) :
    (sem.toFloatMachine p (fun x => (sem.toNat p x).getD 0) mm qr
      (sem.uniformUnif p (ρ .uniform 0)) (sem.gaussianNormal p (ρ .gaussian 0))).IsAccurate
        (dec p) ((c .uniform + 1) * u) 0 Ω μM μQ (2 * (c .gaussian + 3)) := by
  have huM : u ≤ (c .uniform + 1) * u := by nlinarith [mul_nonneg hcu hu]
  have hu' : 0 ≤ (c .uniform + 1) * u := mul_nonneg (by linarith) hu
  have hconv : (fun x => (sem.toNat p x).getD 0) = fun x => ⌊dec p x⌋₊ :=
    funext fun x => by
      rw [htn p x]
      split_ifs with h0
      · rfl
      · exact (Nat.floor_eq_zero.mpr (by linarith [not_le.mp h0])).symm
  have hsem' : IsRelErrSem (fun _ => (c .uniform + 1) * u) dec (fun _ _ => True) sem :=
    hsem.mono fun _ => huM
  have hlit' : IsExactIntLit dec sem 1 := fun p k hk => hlit p k (hk.trans (by norm_num))
  have hmm' : IsMatMulErr (decodeComplex (dec p)) ((c .uniform + 1) * u) 0 Ω μM mm :=
    { specNorm_mul_sub_le := fun A B hAB =>
        (hmm.specNorm_mul_sub_le A B hAB).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huM (hμM _))
            (le_max_right _ _))
      isHermitian_of_map_eq_conjTranspose := hmm.isHermitian_of_map_eq_conjTranspose }
  have hqr' : IsQRErr (decodeComplex (dec p)) ((c .uniform + 1) * u) 0 Ω μQ qr := fun A hA =>
    let h := hqr A hA
    ⟨h.1, h.2.choose, h.2.choose_spec.1,
      h.2.choose_spec.2.1.trans (mul_le_mul_of_nonneg_left huM (hμQ _)),
      h.2.choose_spec.2.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left huM (hμQ _)) (le_max_right _ _))⟩
  have hρU : ∀ v : ℝ, |v| ≤ 1 → |dec p (ρ .uniform 0 v) - v| ≤ c .uniform * u * |v| := by
    intro v hv
    have h := hρ.1 .uniform 0 v (hv.trans hΩ)
    rwa [max_eq_left (abs_nonneg v)] at h
  have hunif : IsUnifSampler (dec p) ((c .uniform + 1) * u) 0 (sem.uniformUnif p (ρ .uniform 0)) :=
    isUnifSampler_uniformUnif hsem hmul p hρU (fun v hv => hρ.2 0 v hv) hu hcu
  have hρG : ∀ x : ℝ, |x| ≤ 2 * Ω → |dec p (ρ .gaussian 0 x) - x| ≤ c .gaussian * u * |x| := by
    intro x hx
    have h := hρ.1 .gaussian 0 x hx
    rwa [max_eq_left (abs_nonneg x)] at h
  have hnorm : IsNormalSampler (decodeComplex (dec p)) u (2 * (c .gaussian + 3)) 0 Ω
      (sem.gaussianNormal p (ρ .gaussian 0)) :=
    isNormalSampler_gaussianNormal hsem hlit p hρG hcg hu hcgu
  have hnorm' : IsNormalSampler (decodeComplex (dec p)) ((c .uniform + 1) * u)
      (2 * (c .gaussian + 3)) 0 Ω (sem.gaussianNormal p (ρ .gaussian 0)) := fun z hz =>
    (hnorm z hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left huM (by linarith)) (le_max_right _ _))
  rw [hconv]
  exact isAccurate_toFloatMachine Ω hsem' hlit' hu' p hmm' hqr' hunif hnorm'

set_option linter.style.longLine false in
/-- **The uniform shift of a rounding with countable range has countable ranges and measurable
fibres**, as
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw`
asks of a machine's uniform sampler. No printed source.
Proof: the range at scale $s$ is the image of the range of $\rho$ (`Set.range_comp_subset_range`,
`Set.Countable.mono`, `Set.Countable.image`); a fibre is the preimage under $\rho$ of a subset of
that countable range, a countable union of the fibres of $\rho$ (`MeasurableSet.biUnion`). S, about
15 lines. -/
theorem countable_range_uniformUnif (sem : ScalarSem P K) (p : P) {ρ : ℝ → K}
    (hc : (Set.range ρ).Countable) (hm : ∀ z, MeasurableSet (ρ ⁻¹' {z})) :
    (∀ s, (Set.range (sem.uniformUnif p ρ s)).Countable) ∧
      ∀ s z, MeasurableSet (sem.uniformUnif p ρ s ⁻¹' {z}) := by
  refine ⟨fun s => ?_, fun s z => ?_⟩
  · have hrange : Set.range (sem.uniformUnif p ρ s) =
        (fun w => (sem.bin p .mul s w).getD default) '' Set.range ρ := by
      rw [← Set.range_comp]; rfl
    rw [hrange]
    exact hc.image _
  · have hT : {w | w ∈ Set.range ρ ∧ (sem.bin p .mul s w).getD default = z}.Countable :=
      hc.mono fun w hw => hw.1
    have hset : sem.uniformUnif p ρ s ⁻¹' {z} =
        ⋃ w ∈ {w | w ∈ Set.range ρ ∧ (sem.bin p .mul s w).getD default = z}, ρ ⁻¹' {w} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
        exists_prop]
      constructor
      · intro h
        exact ⟨ρ v, ⟨⟨v, rfl⟩, h⟩, rfl⟩
      · rintro ⟨w, ⟨_, hw⟩, hv⟩
        rw [← hv] at hw
        exact hw
    rw [hset]
    exact MeasurableSet.biUnion hT fun w _ => hm w

/-- **The normal sampler of a rounding with countable range has a countable range and measurable
fibres**. No printed source.
Proof: as `NLAlib.Computation.countable_range_uniformUnif`; a fibre is the set of $z$ whose parts
$\sqrt2\operatorname{Re} z$, $\sqrt2\operatorname{Im} z$ have their roundings in two countable sets,
measurable by `Complex.measurable_re`, `Complex.measurable_im` and countable unions. S, about 20
lines. -/
theorem countable_range_gaussianNormal (sem : ScalarSem P K) (p : P) {ρ : ℝ → K}
    (hc : (Set.range ρ).Countable) (hm : ∀ z, MeasurableSet (ρ ⁻¹' {z})) :
    (Set.range (sem.gaussianNormal p ρ)).Countable ∧
      ∀ z, MeasurableSet (sem.gaussianNormal p ρ ⁻¹' {z}) := by
  have hF : ∀ a : K, MeasurableSet
      {x : ℝ | (sem.bin p .mul (ρ x) (sem.sqrtHalf p)).getD default = a} := by
    intro a
    have hT : {w | w ∈ Set.range ρ ∧
        (sem.bin p .mul w (sem.sqrtHalf p)).getD default = a}.Countable :=
      hc.mono fun w hw => hw.1
    have hset : {x : ℝ | (sem.bin p .mul (ρ x) (sem.sqrtHalf p)).getD default = a} =
        ⋃ w ∈ {w | w ∈ Set.range ρ ∧
          (sem.bin p .mul w (sem.sqrtHalf p)).getD default = a}, ρ ⁻¹' {w} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · intro h
        exact ⟨ρ x, ⟨⟨x, rfl⟩, h⟩, rfl⟩
      · rintro ⟨w, ⟨_, hw⟩, hx⟩
        rw [← hx] at hw
        exact hw
    rw [hset]
    exact MeasurableSet.biUnion hT fun w _ => hm w
  have hsub : Set.range (sem.gaussianNormal p ρ) ⊆
      (fun q : K × K => ((sem.bin p .mul q.1 (sem.sqrtHalf p)).getD default,
        (sem.bin p .mul q.2 (sem.sqrtHalf p)).getD default)) ''
        (Set.range ρ ×ˢ Set.range ρ) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(ρ (√2 * z.re), ρ (√2 * z.im)), ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩
  refine ⟨((hc.prod hc).image _).mono hsub, fun z => ?_⟩
  have hset : sem.gaussianNormal p ρ ⁻¹' {z} =
      (fun x : ℂ => √2 * x.re) ⁻¹' {x : ℝ | (sem.bin p .mul (ρ x) (sem.sqrtHalf p)).getD default
          = z.1} ∩
        (fun x : ℂ => √2 * x.im) ⁻¹' {x : ℝ | (sem.bin p .mul (ρ x) (sem.sqrtHalf p)).getD default
          = z.2} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      ScalarSem.gaussianNormal, Prod.ext_iff]
  rw [hset]
  exact ((hF z.1).preimage (measurable_const.mul Complex.measurable_re)).inter
    ((hF z.2).preimage (measurable_const.mul Complex.measurable_im))

end NLAlib.Computation
