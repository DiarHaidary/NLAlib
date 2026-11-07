/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.Computation.Model
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.RandomMatrix.Gaussian.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# Test matrices drawn from a random tape

A program draws its random numbers from a tape, one i.i.d. sequence per distribution
(`docs/design/Computation.md`, D12), and stores an $N \times k$ test matrix column-major:
`NLAlib.Computation.tapeMatrix x off N k` has entry $(i, j)$ equal to tape value
$\mathit{off} + i + Nj$. With a standard Gaussian tape the matrix drawn is a standard Gaussian
matrix, and two matrices drawn from disjoint stretches of the tape are independent. These are the
laws the probabilistic theorems about programs need, so that a program that draws its own test
matrices inherits the tail bounds of its specification with no new probability.

The law of the tape is fixed once, here: `NLAlib.Computation.tapeLaw` makes the tapes of the
distributions independent, the tape of `d` an i.i.d. sequence with law `d.law` (a standard Gaussian,
a Rademacher sign, a uniform draw on $[-1, 1]$). The probabilistic companion of the matrix-free
model, `NLAlib.Computation.MatrixFreeProb`, bounds the probability that a program fails to run
within its counts and memory and to satisfy its postcondition, when the tape has this law; the law
is part of the definition, never a hypothesis of a theorem, so it cannot depend on the matrix.

## Main definitions

* `NLAlib.Computation.Dist.law`, `NLAlib.Computation.tapeLaw`: the law of the tape.
* `NLAlib.Computation.MatrixFreeProb`: the probabilistic matrix-free model, on a first-order
  program; `NLAlib.Computation.ProgFamily.MatrixFreeProb`, the same model on a program family
  (proof infrastructure).
* `NLAlib.Computation.MatrixFreeRoundedProb`: the rounded probabilistic model, quantified over
  the index-exact interpretations meeting contracts and the roundings of the tape, with counts
  and memory.

## Main results

* `NLAlib.hasLaw_tapeMatrix_of_hasLaw_iidSequence`: a Gaussian tape draws a Gaussian matrix.
* `NLAlib.indepFun_tapeMatrix_of_hasLaw_iidSequence`: consecutive draws are independent.
* `NLAlib.Computation.hasLaw_apply_of_hasLaw_tapeLaw`: the tape of one distribution under the
  law of the tape.
* `NLAlib.Computation.ProgFamily.MatrixFreeProb.prog`: a result for a family is a result for a
  program that instantiates to it.
* `NLAlib.Computation.Dist.law_uniform_Icc`: the uniform law gives $[-1, 1]$ mass one.
* `NLAlib.Computation.Dist.real_law_uniform_Icc`: the mass of a subinterval.
* `NLAlib.Computation.ae_forall_mem_Icc_of_hasLaw_tapeLaw`: ideal uniform draws lie in
  $[-1, 1]$.
* `NLAlib.Computation.IsTapeRounding.ae_forall_mem_Icc_of_hasLaw_tapeLaw`: so do stored ones.
* `NLAlib.Computation.MatrixFreeRoundedProb.mono`: a larger bound.
* `NLAlib.Computation.MatrixFreeRoundedProb.of_exec`: the model from success, correctness and a
  count bound of every successful run.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

open Computation

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The tape positions of an $N \times k$ draw from position `off` are distinct. -/
private theorem injective_tapePos (off N k : ℕ) :
    Function.Injective fun p : Fin N × Fin k => off + p.1.1 + N * p.2.1 := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h' : i.1 + N * j.1 = i'.1 + N * j'.1 := by simp only at h; omega
  obtain ⟨h1, h2⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i.2 i'.2).mp h'
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- **A Gaussian tape draws a Gaussian matrix**: if the tape $x$ is an i.i.d. sequence of standard
Gaussians, the $N \times k$ matrix drawn from it from position $\mathit{off}$, column-major, is a
standard Gaussian matrix. No printed source.
Result: tape-gaussian-matrix -/
theorem hasLaw_tapeMatrix_of_hasLaw_iidSequence {x : Ω → ℕ → ℝ}
    (hx : HasLaw x (iidSequence (gaussianReal 0 1)) μ) (off N k : ℕ) :
    HasLaw (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) off N k) (gaussianMatrix (Fin N) (Fin k)) μ := by
  refine hasLaw_gaussianMatrix_of_hasLaw_uncurry ?_
  have h := hx.comp_of_injective (injective_tapePos off N k)
  convert h using 2 with ω
  funext ⟨i, j⟩
  simp only [tapeMatrix]
  rfl

/-- **Consecutive draws are independent**: if the tape $x$ is an i.i.d. sequence with a
probability law $\nu$, the $N \times k$ matrix drawn from position $0$ and the $N \times \ell$
matrix drawn after it, from position $Nk$, are independent. No printed source.
Result: tape-independent-draws -/
theorem indepFun_tapeMatrix_of_hasLaw_iidSequence {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {x : Ω → ℕ → ℝ} (hx : HasLaw x (iidSequence ν) μ) (N k ℓ : ℕ) :
    IndepFun (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) 0 N k)
      (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) (N * k) N ℓ) μ := by
  have : IsProbabilityMeasure μ := hx.isProbabilityMeasure_iff.mpr inferInstance
  have hind := ((hasLaw_infinitePi_iff (ν := fun _ : ℕ => ν)).mp hx).1
  have hST : Disjoint (Finset.range (N * k)) (Finset.Ico (N * k) (N * k + N * ℓ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
    omega
  have h := hind.indepFun_finset₀ _ _ hST fun n => (hx.aemeasurable.eval n)
  have hS : ∀ (i : Fin N) (j : Fin k), i.1 + N * j.1 ∈ Finset.range (N * k) := by
    intro i j
    simp only [Finset.mem_range]
    nlinarith [i.2, j.2]
  have hT : ∀ (i : Fin N) (j : Fin ℓ), N * k + i.1 + N * j.1 ∈
      Finset.Ico (N * k) (N * k + N * ℓ) := by
    intro i j
    simp only [Finset.mem_Ico]
    constructor
    · omega
    · nlinarith [i.2, j.2]
  have := h.comp (φ := fun v : Finset.range (N * k) → ℝ =>
      (Matrix.of fun (i : Fin N) (j : Fin k) => v ⟨_, hS i j⟩ : Matrix (Fin N) (Fin k) ℝ))
    (ψ := fun v : Finset.Ico (N * k) (N * k + N * ℓ) → ℝ =>
      (Matrix.of fun (i : Fin N) (j : Fin ℓ) => v ⟨_, hT i j⟩ : Matrix (Fin N) (Fin ℓ) ℝ))
    (by fun_prop) (by fun_prop)
  convert this using 1 <;> funext ω <;> ext i j <;> simp [tapeMatrix]

namespace Computation

/-- The law of one draw from each distribution: the standard Gaussian, the Rademacher law
(a random sign), and the uniform law on $[-1, 1]$ (Lebesgue measure conditioned on the
interval). -/
noncomputable def Dist.law : Dist → Measure ℝ
  | .gaussian => gaussianReal 0 1
  | .rademacher => rademacherMeasure
  | .uniform => volume[|Set.Icc (-1) 1]

/-- The law of a draw is a probability measure. -/
instance isProbabilityMeasure_law (d : Dist) : IsProbabilityMeasure d.law := by
  cases d
  · exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  · exact inferInstanceAs (IsProbabilityMeasure rademacherMeasure)
  · exact cond_isProbabilityMeasure_of_finite (by simp) (by simp)

/-- **The law of the tape**: the tapes of the distributions are independent, and the tape of `d`
is an i.i.d. sequence with law `d.law`. -/
noncomputable def tapeLaw : Measure (Dist → ℕ → ℝ) :=
  Measure.infinitePi fun d : Dist => iidSequence d.law

/-- The law of the tape is a probability measure. -/
instance isProbabilityMeasure_tapeLaw : IsProbabilityMeasure tapeLaw :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun d : Dist => iidSequence d.law))

/-- Under the law of the tape, the tape of one distribution is an i.i.d. sequence with its law. -/
theorem hasLaw_apply_of_hasLaw_tapeLaw {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ)
    (d : Dist) : HasLaw (fun ω => ξ ω d) (iidSequence d.law) μ :=
  (measurePreserving_eval_infinitePi (fun d : Dist => iidSequence d.law) d).fun_comp_hasLaw hξ

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- **The probabilistic matrix-free model.** For all sizes $N$, $n$ satisfying `valid`, every
declared input $x$ and every $N \times N$ matrix $\mathbf{A}$, and every tape $\xi$ on any
probability space whose law is the law of the tape `tapeLaw` (fixed by this definition: the tapes
independent, the tape of `d` i.i.d. with law `d.law`), the probability that the program `prog`,
run under exact arithmetic with every oracle name meaning $\mathbf{A}$ and the tape $\xi(\omega)$
from the initial state that holds the declared buffers `inputs N n x` at tag `p` and nothing
else, fails to run within the counts `cost N n` and the memory `mem N n` in a state satisfying
`good N n x A` is at most `bound N n x A`.

The program, one first-order tree for all sizes, is bound before the sizes, the matrix, the
declared inputs and the tape, and the law of the tape is part of the definition: neither the
program nor the law can depend on the data. -/
def MatrixFreeProb {r b : ℕ} (p : P) (prog : Prog P ι r b)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option 𝕜))
    (cost : ℕ → (Fin r → ℕ) → OpCount P ι) (mem : ℕ → (Fin r → ℕ) → P → ℕ)
    (good : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 →
      St P 𝕜 (OpCount P ι) → Prop)
    (bound : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 → ℝ) : Prop :=
  ∀ N n, valid N n → ∀ (x : X N n) (A : Matrix (Fin N) (Fin N) 𝕜) (Ω : Type)
    (_ : MeasurableSpace Ω) (μ : Measure Ω) (ξ : Ω → Dist → ℕ → ℝ), HasLaw ξ tapeLaw μ →
    μ.real {ω | ¬ prog.RunsWithin (exactInterp (fun _ => A) (ξ ω)) N n
      (inputState p (List.ofFn (inputs N n x))) (cost N n) (mem N n) (good N n x A)} ≤
      bound N n x A

/-- **The probabilistic matrix-free model on a program family**, proof infrastructure for
`NLAlib.Computation.MatrixFreeProb`. For all sizes $N$, $n$ satisfying `valid`, every declared
input $x$ and every $N \times N$ matrix $\mathbf{A}$, and every tape $\xi$ on any probability
space whose law is the law of the tape `tapeLaw` (fixed by this definition: the tapes
independent, the tape of `d` i.i.d. with law `d.law`), the probability that the program family
`prog`, run under exact arithmetic with every oracle name meaning $\mathbf{A}$ and the tape
$\xi(\omega)$ from the initial state that holds the declared buffers `inputs N n x` at tag `p`
and nothing else, fails to run within the counts `cost N n` and the memory `mem N n` in a state
satisfying `good N n x A` is at most `bound N n x A`.

The program is bound before the matrix, the declared inputs and the tape, and the law of the tape
is part of the definition: neither the program nor the law can depend on the data. -/
def ProgFamily.MatrixFreeProb {r b : ℕ} (p : P) (prog : ProgFamily P ι r b)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option 𝕜))
    (cost : ℕ → (Fin r → ℕ) → OpCount P ι) (mem : ℕ → (Fin r → ℕ) → P → ℕ)
    (good : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 →
      St P 𝕜 (OpCount P ι) → Prop)
    (bound : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 → ℝ) : Prop :=
  ∀ N n, valid N n → ∀ (x : X N n) (A : Matrix (Fin N) (Fin N) 𝕜) (Ω : Type)
    (_ : MeasurableSpace Ω) (μ : Measure Ω) (ξ : Ω → Dist → ℕ → ℝ), HasLaw ξ tapeLaw μ →
    μ.real {ω | ¬ RunsWithin (exactInterp (fun _ => A) (ξ ω)) (prog.inst N n)
      (inputState p (List.ofFn (inputs N n x))) (cost N n) (mem N n) (good N n x A)} ≤
      bound N n x A

/-- From a family to a program, probabilistic: a result for the program family $F$ in the
probabilistic matrix-free model is a result, with the same size condition, declared inputs,
counts, memory, event and bound, for every first-order program $c$ that instantiates at every
size to the statement of $F$ there. No printed source. -/
theorem ProgFamily.MatrixFreeProb.prog {r b : ℕ} {p : P} {F : ProgFamily P ι r b}
    {valid : ℕ → (Fin r → ℕ) → Prop} {X : ℕ → (Fin r → ℕ) → Type}
    {inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option 𝕜)}
    {cost : ℕ → (Fin r → ℕ) → OpCount P ι} {mem : ℕ → (Fin r → ℕ) → P → ℕ}
    {good : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 →
      St P 𝕜 (OpCount P ι) → Prop}
    {bound : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 → ℝ}
    (h : ProgFamily.MatrixFreeProb p F valid X inputs cost mem good bound) (c : Prog P ι r b)
    (hc : ∀ N n, c.toStmt N n = F.inst N n) :
    Computation.MatrixFreeProb p c valid X inputs cost mem good bound := by
  intro N n hv x A Ω _ μ ξ hξ
  refine (le_of_eq (congrArg μ.real (Set.ext fun ω => not_congr ?_))).trans
    (h N n hv x A Ω _ μ ξ hξ)
  rw [Prog.runsWithin_iff (hsize := by simp), hc]

/-- **The rounded probabilistic model.** For all sizes $N$, $n$ satisfying `valid` and every
declared input $x$ satisfying `pre N n x`, under **every** interpretation $I$ whose semantics is
index exact at the decoding `dec` up to `B N n` (`NLAlib.Computation.IsIndexExactSem`: exact
integer literals up to the bound and the exact floor conversion, failing below zero) and that
meets the contracts `Contracts N n` (on its value semantics, literals and kernels), every rounding
$\rho$ of the tape meeting `ρOK` (a tape-rounding contract such as
`NLAlib.Computation.IsTapeRounding`), and every ideal tape $\xi$ on any probability space whose
law is the law of the tape `tapeLaw` (fixed by this definition: the tapes independent, the tape
of `d` i.i.d. with law `d.law`), the probability that the program `prog`, run under $I$ with the
stored tape $\rho(d, i, \xi(\omega)(d, i))$ and the standard charge (one count per operation of
each kind) from the initial state that holds the declared buffers `inputs N n x` at tag `p` and
nothing else, fails, or exceeds the counts `cost N n` or the workspace `mem N n` (the peak memory
per tag, declared buffers included, the read-only data of $I$ counted on top), or ends in a state
not satisfying `good N n x`, is at most `bound N n x`.

The program, one first-order tree for all sizes, is bound before the sizes, the inputs, the
interpretation, the rounding and the tape. The arithmetic, the kernels and the rounding of the
draws are quantified over everything meeting the contracts, and the law of the ideal tape is part
of the definition, so it cannot depend on the data. The index exactness is part of the model, at
the decoding `dec` of the target, so a target cannot drop it or state it at another decoding. The
counts are those of the run itself, so the cost bound holds on the same event as the
postcondition. -/
def MatrixFreeRoundedProb {K : Type} {r b : ℕ} (p : P) (prog : Prog P ι r b)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option K))
    (dec : P → K → ℝ) (B : ℕ → (Fin r → ℕ) → ℕ) (cost : ℕ → (Fin r → ℕ) → OpCount P ι)
    (mem : ℕ → (Fin r → ℕ) → P → ℕ)
    (Contracts : ℕ → (Fin r → ℕ) → Interp P ι K (OpCount P ι) → Prop)
    (ρOK : (Dist → ℕ → ℝ → K) → Prop) (pre : (N : ℕ) → (n : Fin r → ℕ) → X N n → Prop)
    (good : (N : ℕ) → (n : Fin r → ℕ) → X N n → St P K (OpCount P ι) → Prop)
    (bound : (N : ℕ) → (n : Fin r → ℕ) → X N n → ℝ) : Prop :=
  ∀ N n, valid N n → ∀ x : X N n, pre N n x → ∀ (I : Interp P ι K (OpCount P ι))
    (ρ : Dist → ℕ → ℝ → K), IsIndexExactSem dec (B N n) I.sem → Contracts N n I → ρOK ρ →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (ξ : Ω → Dist → ℕ → ℝ),
    HasLaw ξ tapeLaw μ →
    μ.real {ω | ¬ prog.RunsWithin
        { I with tape := fun d i => ρ d i (ξ ω d i), charge := fun k => Finsupp.single k 1 } N n
        (inputState p (List.ofFn (inputs N n x))) (cost N n) (fun q => mem N n q + I.romSize q)
        (good N n x)} ≤ bound N n x

/-- **A rounded probabilistic result from success, correctness and a count bound**: if, under
every interpretation with the standard charge meeting the index exactness and the contracts,
the probability that the run fails or ends outside `good` is at most `bound`, and every successful
run under the standard charge from the declared inputs stays within `cost` and `mem`, then the
model holds, provided the contracts do not depend on the charge. No printed source. -/
theorem MatrixFreeRoundedProb.of_exec {K : Type} {r b : ℕ} {p : P} {prog : Prog P ι r b}
    {valid : ℕ → (Fin r → ℕ) → Prop} {X : ℕ → (Fin r → ℕ) → Type}
    {inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option K)}
    {dec : P → K → ℝ} {B : ℕ → (Fin r → ℕ) → ℕ} {cost : ℕ → (Fin r → ℕ) → OpCount P ι}
    {mem : ℕ → (Fin r → ℕ) → P → ℕ}
    {Contracts : ℕ → (Fin r → ℕ) → Interp P ι K (OpCount P ι) → Prop}
    {ρOK : (Dist → ℕ → ℝ → K) → Prop} {pre : (N : ℕ) → (n : Fin r → ℕ) → X N n → Prop}
    {good : (N : ℕ) → (n : Fin r → ℕ) → X N n → St P K (OpCount P ι) → Prop}
    {bound : (N : ℕ) → (n : Fin r → ℕ) → X N n → ℝ}
    (hC : ∀ N n I, Contracts N n I →
      Contracts N n { I with charge := fun k => Finsupp.single k 1 })
    (hcost : ∀ N n (x : X N n) (I : Interp P ι K (OpCount P ι)) (st : St P K (OpCount P ι)),
      I.charge = (fun k => Finsupp.single k 1) →
      prog.exec I N n (inputState p (List.ofFn (inputs N n x))) = some st →
      st.cnt ≤ cost N n ∧ ∀ q, st.peak q ≤ mem N n q)
    (h : ∀ N n, valid N n → ∀ x : X N n, pre N n x → ∀ (I : Interp P ι K (OpCount P ι))
      (ρ : Dist → ℕ → ℝ → K), IsIndexExactSem dec (B N n) I.sem → Contracts N n I → ρOK ρ →
      I.charge = (fun k => Finsupp.single k 1) →
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (ξ : Ω → Dist → ℕ → ℝ),
      HasLaw ξ tapeLaw μ →
      μ.real {ω | ¬ ∃ st', prog.exec { I with tape := fun d i => ρ d i (ξ ω d i) } N n
          (inputState p (List.ofFn (inputs N n x))) = some st' ∧ good N n x st'} ≤
        bound N n x) :
    MatrixFreeRoundedProb p prog valid X inputs dec B cost mem Contracts ρOK pre good bound := by
  intro N n hv x hpre I ρ hidx hCI hρ Ω _ μ ξ hξ
  have := hξ.isProbabilityMeasure
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top μ _)) (h N n hv x hpre
    { I with charge := fun k => Finsupp.single k 1 } ρ hidx (hC N n I hCI) hρ rfl Ω _ μ ξ hξ)
  rintro ⟨st, hex, hg⟩
  obtain ⟨hc, hm⟩ := hcost N n x _ st rfl hex
  exact hω ⟨by simp, st, hex, by simpa [inputState] using hc,
    fun q => Nat.add_le_add_right (hm q) _, hg⟩

/-! ### Uniform draws and the rounded model -/

section Uniform

/-- The uniform law lives on $[-1, 1]$: the law of a uniform draw gives the interval
$[-1, 1]$ mass one. No printed source. -/
theorem Dist.law_uniform_Icc : Dist.uniform.law (Set.Icc (-1) 1) = 1 :=
  cond_apply_self (by norm_num [Real.volume_Icc]) measure_Icc_lt_top.ne

/-- The uniform law of a subinterval: for $-1 \le a \le b \le 1$, a uniform draw lies in
$[a, b]$ with probability
$$\frac{b - a}{2}.$$
No printed source. -/
theorem Dist.real_law_uniform_Icc {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Dist.uniform.law.real (Set.Icc a b) = (b - a) / 2 := by
  have hab' : 0 ≤ b - a := by linarith
  have h2 : 0 ≤ 1 - (-1 : ℝ) := by norm_num
  change ((volume[|Set.Icc (-1 : ℝ) 1]) (Set.Icc a b)).toReal = _
  rw [cond_apply measurableSet_Icc, Set.Icc_inter_Icc, max_eq_right ha, min_eq_right hb,
    ENNReal.toReal_mul, ENNReal.toReal_inv, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_ofReal hab', ENNReal.toReal_ofReal h2]
  ring

/-- Ideal uniform draws lie in $[-1, 1]$: if the tape $\xi$ has the law of the tape
`NLAlib.Computation.tapeLaw` under $\mu$, then $\mu$-almost surely every uniform draw
$\xi(\omega)(d, i)$, $d$ = `NLAlib.Computation.Dist.uniform`, $i \in \mathbb{N}$, lies in
$[-1, 1]$. No printed source. -/
theorem ae_forall_mem_Icc_of_hasLaw_tapeLaw {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) :
    ∀ᵐ ω ∂μ, ∀ i, ξ ω .uniform i ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have hlaw : HasLaw (fun ω => ξ ω .uniform i) Dist.uniform.law μ :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => Dist.uniform.law) i).fun_comp_hasLaw
      (hasLaw_apply_of_hasLaw_tapeLaw hξ .uniform)
  have hae : ∀ᵐ x ∂(μ.map fun ω => ξ ω .uniform i), x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hlaw.map_eq]
    exact ae_cond_mem measurableSet_Icc
  exact (ae_map_iff hlaw.aemeasurable measurableSet_Icc).mp hae

/-- Stored uniform draws lie in $[-1, 1]$: under the tape-rounding contract
`NLAlib.Computation.IsTapeRounding` for $\rho$, at tag `p`, and an ideal tape $\xi$ with the law of
the tape under $\mu$, $\mu$-almost surely every stored uniform draw
$\rho(d, i, \xi(\omega)(d, i))$, $d$ = `NLAlib.Computation.Dist.uniform`, decodes into
$[-1, 1]$. No printed source. -/
theorem IsTapeRounding.ae_forall_mem_Icc_of_hasLaw_tapeLaw {P K : Type} {dec : P → K → ℝ}
    {p : P} {u τ Ω : ℝ} {c : Dist → ℝ} {ρ : Dist → ℕ → ℝ → K}
    (h : IsTapeRounding dec p u τ Ω c ρ)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ}
    (hξ : HasLaw ξ tapeLaw μ) :
    ∀ᵐ ω ∂μ, ∀ i, dec p (ρ .uniform i (ξ ω .uniform i)) ∈ Set.Icc (-1 : ℝ) 1 :=
  (NLAlib.Computation.ae_forall_mem_Icc_of_hasLaw_tapeLaw hξ).mono fun _ hω i => h.2 i _ (hω i)

/-- A larger bound: a result in the rounded probabilistic model with the bound `bound` holds
with every pointwise larger bound `bound'`. No printed source. -/
theorem MatrixFreeRoundedProb.mono {P ι K : Type} [DecidableEq P] {r b : ℕ} {p : P}
    {prog : Prog P ι r b} {valid : ℕ → (Fin r → ℕ) → Prop} {X : ℕ → (Fin r → ℕ) → Type}
    {inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option K)}
    {dec : P → K → ℝ} {B : ℕ → (Fin r → ℕ) → ℕ} {cost : ℕ → (Fin r → ℕ) → OpCount P ι}
    {mem : ℕ → (Fin r → ℕ) → P → ℕ}
    {Contracts : ℕ → (Fin r → ℕ) → Interp P ι K (OpCount P ι) → Prop}
    {ρOK : (Dist → ℕ → ℝ → K) → Prop} {pre : (N : ℕ) → (n : Fin r → ℕ) → X N n → Prop}
    {good : (N : ℕ) → (n : Fin r → ℕ) → X N n → St P K (OpCount P ι) → Prop}
    {bound bound' : (N : ℕ) → (n : Fin r → ℕ) → X N n → ℝ}
    (h : MatrixFreeRoundedProb p prog valid X inputs dec B cost mem Contracts ρOK pre good bound)
    (hb : ∀ N n x, bound N n x ≤ bound' N n x) :
    MatrixFreeRoundedProb p prog valid X inputs dec B cost mem Contracts ρOK pre good bound' :=
  fun N n hv x hpre I ρ hidx hI hρ Ω _ μ ξ hξ =>
    (h N n hv x hpre I ρ hidx hI hρ Ω _ μ ξ hξ).trans (hb N n x)

end Uniform

end Computation

end NLAlib
