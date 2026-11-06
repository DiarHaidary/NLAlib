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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end NLAlib.Computation
