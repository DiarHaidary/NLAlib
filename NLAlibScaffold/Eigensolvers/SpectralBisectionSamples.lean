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
  sorry

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
  sorry

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
    funext fun x => by rw [htn p x]; rfl
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
