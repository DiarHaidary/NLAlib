/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Mul
public import NLAlib.ForMathlib.Analysis.Convex.SupportingLine
public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.Matrix.Norms.Block
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Trace functions

For a function $f$ from $\mathbb{R}$ to $\mathbb{R}$, the trace function
$\mathbf{A} \mapsto \operatorname{tr} f(\mathbf{A}) = \sum_i f(\lambda_i(\mathbf{A}))$ on Hermitian
matrices (in Lean the real part of the trace) inherits monotonicity and convexity from $f$. With
$f = \exp$ this gives the monotonicity and convexity of the trace exponential. Quadratic forms
satisfy Jensen's inequality
$\varphi(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \le \mathbf{x}^{\mathsf{H}}
\varphi(\mathbf{A}) \mathbf{x}$
for convex $\varphi$ and unit $\mathbf{x}$.

The intrinsic dimension
$\operatorname{intdim}(\mathbf{A}) = \operatorname{tr} \mathbf{A} / \|\mathbf{A}\|_2$
(`NLAlib.intrinsicDimension`) of a positive semidefinite matrix replaces the ambient dimension in
trace bounds.

## Main definitions

* `NLAlib.intrinsicDimension`: the ratio of the trace to the spectral norm.

## Main results

* `NLAlib.re_trace_cfc_le_re_trace_cfc_of_le`: monotone $f$ gives a monotone trace function.
* `NLAlib.convexOn_re_trace_cfc`: convex $f$ gives a convex trace function.
* `NLAlib.re_trace_mul_cfc_le_re_trace_cfc_sub`: Klein's inequality.
* `NLAlib.apply_re_quadForm_le_re_quadForm_cfc`: Jensen for quadratic forms.
* `NLAlib.apply_re_quadForm_le_re_quadForm_cfc_of_hasSupportingLineOn`,
  `NLAlib.apply_specNorm_mul_sq_le_specNorm_mul_sq_of_hasSupportingLineOn`: Jensen for a function
  with a supporting line, for quadratic forms and for the norm of a projected matrix.
* `NLAlib.re_quadForm_mem_of_spectrum_subset`: the quadratic form at a unit vector lies in every
  convex set containing the spectrum.
* `NLAlib.sum_apply_re_quadForm_le_re_trace_cfc`: Peierls' inequality.
* `NLAlib.re_trace_cfc_conjTranspose_mul_mul_le`: trace Jensen for compressions.
* `NLAlib.re_trace_exp_le_re_trace_exp_of_le`, `NLAlib.convexOn_re_trace_exp`.
* `Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul`: the intrinsic dimension lemma.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-! ### Jensen for quadratic forms along an orthonormal frame -/

/-- The quadratic form of $f(\mathbf{A})$ at a unit vector is an average of $f$ over the
eigenvalues: there are weights $w_i \ge 0$ summing to $1$ with
$\operatorname{Re}(\mathbf{x}^{\mathsf{H}} f(\mathbf{A}) \mathbf{x})
= \sum_i w_i f(\lambda_i(\mathbf{A}))$ for every $f$. -/
private theorem exists_weights_re_quadForm_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    ∃ w : Fin (Fintype.card n) → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ f : ℝ → ℝ, RCLike.re (quadForm (cfc f A) x) = ∑ i, w i • f (eigenvalue A i) := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  refine ⟨fun i => ‖(Uᴴ *ᵥ x) i‖ ^ 2, fun i => by positivity, ?_, fun f => ?_⟩
  · have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (Uᴴ *ᵥ x))
    rw [(hU.conjTranspose_of_card_eq hr.symm).norm_toLp_mulVec x, hx, one_pow] at h
    exact h.symm
  · rw [re_quadForm_cfc_eq_sum hU hr hAU f x]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]

/-- **Jensen's inequality for a quadratic form.** For $\varphi$ convex on a set containing the
spectrum of the Hermitian matrix $\mathbf{A}$ and a unit vector $\mathbf{x}$,
$\varphi(\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}))
\le \operatorname{Re}(\mathbf{x}^{\mathsf{H}} \varphi(\mathbf{A}) \mathbf{x})$.
[HalkoMartinssonTropp2011, Proposition 8.6 context]. -/
theorem apply_re_quadForm_le_re_quadForm_cfc {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConvexOn ℝ s φ)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) :
    φ (RCLike.re (quadForm A x)) ≤ RCLike.re (quadForm (cfc φ A) x) := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_weights_re_quadForm_cfc hA hx
  have hsa : IsSelfAdjoint A := hA
  have hid := hw fun x => x
  rw [cfc_id' ℝ A hsa] at hid
  rw [hid, hw φ]
  exact hφ.map_sum_le (fun i _ => hw0 i) hw1 fun i _ => hAs (hA.eigenvalue_mem_spectrum i.isLt)

/-- The quadratic form of a Hermitian matrix at a unit vector lies in every convex set containing
the spectrum: $\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \in s$ for
$\|\mathbf{x}\| = 1$, since it is a convex combination of the eigenvalues. -/
theorem re_quadForm_mem_of_spectrum_subset {s : Set ℝ} (hs : Convex ℝ s) {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    RCLike.re (quadForm A x) ∈ s := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_weights_re_quadForm_cfc hA hx
  have hsa : IsSelfAdjoint A := hA
  have hid := hw fun x => x
  rw [cfc_id' ℝ A hsa] at hid
  rw [hid]
  exact hs.sum_mem (fun i _ => hw0 i) hw1 fun i _ => hAs (hA.eigenvalue_mem_spectrum i.isLt)

/-- The quadratic form at a coordinate vector is the diagonal entry:
$\mathbf{e}_i^{\mathsf{H}}\mathbf{N}\mathbf{e}_i = \mathbf{N}_{i,i}$. -/
private theorem quadForm_single_one (N : Matrix n n 𝕜) (i : n) :
    quadForm N (Pi.single i 1) = N i i := by
  rw [quadForm_def, Matrix.mulVec_single_one, ← Pi.single_star, star_one, single_one_dotProduct]
  rfl

omit [DecidableEq n] in
/-- The columns of a matrix with orthonormal columns are unit vectors. -/
private theorem norm_toLp_mulVec_single {U : Matrix n p 𝕜} (hU : HasOrthonormalCols U) (i : p) :
    ‖WithLp.toLp 2 (U *ᵥ Pi.single i 1)‖ = 1 := by
  rw [hU.norm_toLp_mulVec]
  exact (PiLp.norm_single 2 (fun _ : p => 𝕜) i (1 : 𝕜)).trans norm_one

/-- **Peierls' inequality.** For $\varphi$ convex on a set containing the spectrum of the
Hermitian matrix $\mathbf{A}$ and $\mathbf{U}$ with orthonormal columns
$\mathbf{u}_i = \mathbf{U}\mathbf{e}_i$,
$$\sum_i \varphi(\operatorname{Re}(\mathbf{u}_i^{\mathsf{H}}\mathbf{A}\mathbf{u}_i))
  \le \operatorname{Re} \operatorname{tr}(\mathbf{U}^{\mathsf{H}} \varphi(\mathbf{A}) \mathbf{U})
  \,;$$
for a unitary $\mathbf{U}$ the right side is $\operatorname{tr} \varphi(\mathbf{A})$.
[Carlen2010, Theorem 2.9]; stated there for an orthonormal basis, here for any orthonormal family.
Result: peierls-inequality -/
theorem sum_apply_re_quadForm_le_re_trace_cfc {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConvexOn ℝ s φ)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) :
    ∑ i, φ (RCLike.re (quadForm A (U *ᵥ Pi.single i 1))) ≤
      RCLike.re (Uᴴ * cfc φ A * U).trace := by
  rw [Matrix.trace, map_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hd : (Uᴴ * cfc φ A * U) i i = quadForm (cfc φ A) (U *ᵥ Pi.single i 1) := by
    rw [← quadForm_conjTranspose_mul_mul, quadForm_single_one]
  rw [Matrix.diag_apply, hd]
  exact apply_re_quadForm_le_re_quadForm_cfc hφ hA hAs (norm_toLp_mulVec_single hU i)

/-- A Hermitian matrix has a unitary frame along which its quadratic form takes the sorted
eigenvalues: $\operatorname{Re}(\mathbf{u}_i^{\mathsf{H}}\mathbf{C}\mathbf{u}_i) =
\lambda_i(\mathbf{C})$
for the columns $\mathbf{u}_i$ of a unitary $\mathbf{U}$. -/
private theorem exists_frame_re_quadForm_eq_eigenvalue {C : Matrix n n 𝕜} (hC : C.IsHermitian) :
    ∃ U : Matrix n (Fin (Fintype.card n)) 𝕜, HasOrthonormalCols U ∧ U * Uᴴ = 1 ∧
      ∀ i, RCLike.re (quadForm C (U *ᵥ Pi.single i 1)) = eigenvalue C i := by
  obtain ⟨U, hU, hCU⟩ := hC.exists_mul_eq_mul_diagonal
  refine ⟨U, hU, hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm, fun i => ?_⟩
  rw [← quadForm_conjTranspose_mul_mul, Matrix.mul_assoc, hCU, ← Matrix.mul_assoc,
    hU.conjTranspose_mul_self, Matrix.one_mul, quadForm_single_one, Matrix.diagonal_apply_eq,
    RCLike.ofReal_re]

omit [DecidableEq n] in
/-- The quadratic form of a real combination of two matrices:
$\operatorname{Re}(\mathbf{x}^{\mathsf{H}}(a\mathbf{A} + b\mathbf{B})\mathbf{x})
= a \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) +
b \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{B}\mathbf{x})$. -/
private theorem re_quadForm_smul_add_smul (a b : ℝ) (A B : Matrix n n 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm (a • A + b • B) x) =
      a * RCLike.re (quadForm A x) + b * RCLike.re (quadForm B x) := by
  rw [quadForm_add_left, RCLike.real_smul_eq_coe_smul (K := 𝕜) a,
    RCLike.real_smul_eq_coe_smul (K := 𝕜) b, quadForm_smul_left, quadForm_smul_left, map_add,
    RCLike.re_ofReal_mul, RCLike.re_ofReal_mul]

/-- The three parts of the convexity of a trace function along one convex combination. -/
private theorem re_trace_cfc_smul_add_smul_le {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) (hB : B.IsHermitian)
    (hBs : spectrum ℝ B ⊆ s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A + b • B).IsHermitian ∧ spectrum ℝ (a • A + b • B) ⊆ s ∧
      RCLike.re (cfc f (a • A + b • B)).trace ≤
        a * RCLike.re (cfc f A).trace + b * RCLike.re (cfc f B).trace := by
  have hC : (a • A + b • B).IsHermitian :=
    (hA.smul (IsSelfAdjoint.all a)).add (hB.smul (IsSelfAdjoint.all b))
  obtain ⟨U, hU, hUU, hq⟩ := exists_frame_re_quadForm_eq_eigenvalue hC
  have hu := fun i => norm_toLp_mulVec_single hU i
  have hqC : ∀ i : Fin (Fintype.card n), eigenvalue (a • A + b • B) i =
      a * RCLike.re (quadForm A (U *ᵥ Pi.single i 1)) +
        b * RCLike.re (quadForm B (U *ᵥ Pi.single i 1)) := fun i => by
    rw [← hq i, re_quadForm_smul_add_smul]
  have hmA := fun i => re_quadForm_mem_of_spectrum_subset hf.1 hA hAs (hu i)
  have hmB := fun i => re_quadForm_mem_of_spectrum_subset hf.1 hB hBs (hu i)
  refine ⟨hC, ?_, ?_⟩
  · rw [hC.spectrum_subset_iff]
    intro i hi
    rw [hqC ⟨i, hi⟩]
    exact hf.1 (hmA _) (hmB _) ha hb hab
  · rw [hC.re_trace_cfc, ← Fin.sum_univ_eq_sum_range (fun i => f (eigenvalue (a • A + b • B) i))]
    calc ∑ i : Fin (Fintype.card n), f (eigenvalue (a • A + b • B) i)
        ≤ ∑ i : Fin (Fintype.card n),
            (a * f (RCLike.re (quadForm A (U *ᵥ Pi.single i 1))) +
              b * f (RCLike.re (quadForm B (U *ᵥ Pi.single i 1)))) :=
          Finset.sum_le_sum fun i _ => by
            rw [hqC i]
            exact hf.2 (hmA i) (hmB i) ha hb hab
      _ = a * ∑ i : Fin (Fintype.card n), f (RCLike.re (quadForm A (U *ᵥ Pi.single i 1))) +
            b * ∑ i : Fin (Fintype.card n), f (RCLike.re (quadForm B (U *ᵥ Pi.single i 1))) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ a * RCLike.re (Uᴴ * cfc f A * U).trace + b * RCLike.re (Uᴴ * cfc f B * U).trace :=
          add_le_add
            (mul_le_mul_of_nonneg_left (sum_apply_re_quadForm_le_re_trace_cfc hf hA hAs hU) ha)
            (mul_le_mul_of_nonneg_left (sum_apply_re_quadForm_le_re_trace_cfc hf hB hBs hU) hb)
      _ = a * RCLike.re (cfc f A).trace + b * RCLike.re (cfc f B).trace := by
          rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_mul_cycle Uᴴ, hUU,
            Matrix.one_mul]

omit [DecidableEq n] in
/-- **The overlap formula** for two unitary diagonalisations:
$$\operatorname{Re}
\operatorname{tr}\bigl(\mathbf{U}\operatorname{diag}(\mathbf{a})\mathbf{U}^{\mathsf{H}}
  \mathbf{V}\operatorname{diag}(\mathbf{b})\mathbf{V}^{\mathsf{H}}\bigr)
  = \sum_{j, k} \mathbf{a}_j \mathbf{b}_k \, \lvert (\mathbf{U}^{\mathsf{H}}\mathbf{V})_{j,k}
  \rvert^2 \,.$$ -/
private theorem re_trace_mul_diagonal_mul (U V : Matrix n p 𝕜) (a b : p → ℝ) :
    RCLike.re ((U * Matrix.diagonal (fun j => ((a j : ℝ) : 𝕜)) * Uᴴ) *
      (V * Matrix.diagonal (fun k => ((b k : ℝ) : 𝕜)) * Vᴴ)).trace =
      ∑ j, ∑ k, a j * b k * ‖(Uᴴ * V) j k‖ ^ 2 := by
  have hw : Vᴴ * U = (Uᴴ * V)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h1 : (U * Matrix.diagonal (fun j => ((a j : ℝ) : 𝕜)) * Uᴴ *
      (V * Matrix.diagonal (fun k => ((b k : ℝ) : 𝕜)) * Vᴴ)).trace =
      (Matrix.diagonal (fun j => ((a j : ℝ) : 𝕜)) * (Uᴴ * V) *
        Matrix.diagonal (fun k => ((b k : ℝ) : 𝕜)) * (Uᴴ * V)ᴴ).trace := by
    rw [← hw, Matrix.mul_assoc U, Matrix.mul_assoc U, Matrix.trace_mul_comm U]
    simp only [Matrix.mul_assoc]
  rw [h1]
  generalize Uᴴ * V = W
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, ite_mul,
    mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.conjTranspose_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [show ((a j : ℝ) : 𝕜) * W j k * ((b k : ℝ) : 𝕜) * star (W j k) =
      ((a j * b k : ℝ) : 𝕜) * (W j k * star (W j k)) by push_cast; ring,
    RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

/-! ### Monotonicity and convexity -/

/-- **A monotone function gives a monotone trace function**: if $\mathbf{A}$ is Hermitian,
$\mathbf{A} \preceq \mathbf{B}$, both have spectrum in $s$ and $f$ is non-decreasing on $s$, then
$\operatorname{Re} \operatorname{tr} f(\mathbf{A}) \le \operatorname{Re} \operatorname{tr}
f(\mathbf{B})$.
[Tropp2015, §2.1 and §8.3]; [Carlen2010, Theorem 2.10].
Port of `NLAlib.traceExp_le_traceExp`, there for the exponential over $\mathbb{C}$.
Result: trace-monotonicity -/
theorem re_trace_cfc_le_re_trace_cfc_of_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (h : A ≤ B)
    {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s) (hAs : spectrum ℝ A ⊆ s)
    (hBs : spectrum ℝ B ⊆ s) : RCLike.re (cfc f A).trace ≤ RCLike.re (cfc f B).trace := by
  have hB : B.IsHermitian := by
    have h' := hA.add (Matrix.le_iff.mp h).isHermitian
    rwa [add_sub_cancel] at h'
  rw [hA.re_trace_cfc, hB.re_trace_cfc]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  exact hf (hAs (hA.eigenvalue_mem_spectrum hi')) (hBs (hB.eigenvalue_mem_spectrum hi'))
    (eigenvalue_le_eigenvalue_of_le h hA i)

/-- **A convex function gives a convex trace function**: for $f$ convex on $s$, the function
$\mathbf{A} \mapsto \operatorname{Re} \operatorname{tr} f(\mathbf{A})$ is convex on the Hermitian
matrices with spectrum in $s$.
[Carlen2010, Theorem 2.10]; [Bhatia1997, Problem IX.8.14 context].
Port of `NLAlib.convexOn_traceExp_isHermitian` and `NLAlib.convexOn_traceEvenPower`, there for
the exponential and for even powers.
Result: trace-convexity -/
theorem convexOn_re_trace_cfc {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) :
    ConvexOn ℝ {A : Matrix n n 𝕜 | A.IsHermitian ∧ spectrum ℝ A ⊆ s}
      fun A => RCLike.re (cfc f A).trace := by
  refine ⟨fun A hA B hB a b ha hb hab => ?_, fun A hA B hB a b ha hb hab => ?_⟩
  · have h := re_trace_cfc_smul_add_smul_le hf hA.1 hA.2 hB.1 hB.2 ha hb hab
    exact ⟨h.1, h.2.1⟩
  · exact (re_trace_cfc_smul_add_smul_le hf hA.1 hA.2 hB.1 hB.2 ha hb hab).2.2

/-- **The generalized Klein inequality.** For finitely many functions $f_i$, $g_i$, if
$\sum_i f_i(a) g_i(h) \ge 0$ for all $a, h \in s$, then
$\sum_i \operatorname{Re} \operatorname{tr}(f_i(\mathbf{A}) g_i(\mathbf{H})) \ge 0$ for Hermitian
$\mathbf{A}$, $\mathbf{H}$ with spectrum in $s$.
[Tropp2015, Proposition 8.3.5]. Port of `NLAlib.generalized_klein`. -/
theorem sum_re_trace_cfc_mul_cfc_nonneg {ι : Type*} [Fintype ι] {f g : ι → ℝ → ℝ} {s : Set ℝ}
    (hfg : ∀ a ∈ s, ∀ h ∈ s, 0 ≤ ∑ i, f i a * g i h) {A H : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hH : H.IsHermitian) (hAs : spectrum ℝ A ⊆ s) (hHs : spectrum ℝ H ⊆ s) :
    0 ≤ ∑ i, RCLike.re (cfc (f i) A * cfc (g i) H).trace := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  obtain ⟨V, hV, hHV⟩ := hH.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  have heq : ∀ i, RCLike.re (cfc (f i) A * cfc (g i) H).trace =
      ∑ j : Fin (Fintype.card n), ∑ k : Fin (Fintype.card n),
        f i (eigenvalue A j) * g i (eigenvalue H k) * ‖(Uᴴ * V) j k‖ ^ 2 := fun i => by
    rw [cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAU,
      cfc_eq_mul_diagonal_mul_conjTranspose hV hr hHV]
    exact re_trace_mul_diagonal_mul U V _ _
  simp only [heq]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [← Finset.sum_mul]
  exact mul_nonneg (hfg _ (hAs (hA.eigenvalue_mem_spectrum j.isLt)) _
    (hHs (hH.eigenvalue_mem_spectrum k.isLt))) (by positivity)

/-- **Klein's inequality.** For $f$ convex on $s$ with derivative $f'$ within $s$ at every point
of $s$, and Hermitian $\mathbf{A}$, $\mathbf{B}$ with spectrum in $s$,
$$\operatorname{Re} \operatorname{tr}((\mathbf{A} - \mathbf{B}) f'(\mathbf{B}))
  \le \operatorname{Re} \operatorname{tr} f(\mathbf{A}) - \operatorname{Re} \operatorname{tr}
  f(\mathbf{B}) \,.$$
[Carlen2010, Theorem 2.11]; [Tropp2015, §8.3].
Port of `NLAlib.generalized_klein`, in its classical form.
Result: klein-inequality -/
theorem re_trace_mul_cfc_le_re_trace_cfc_sub {f f' : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAs : spectrum ℝ A ⊆ s) (hBs : spectrum ℝ B ⊆ s) :
    RCLike.re ((A - B) * cfc f' B).trace ≤
      RCLike.re (cfc f A).trace - RCLike.re (cfc f B).trace := by
  have hscalar : ∀ a ∈ s, ∀ b ∈ s, (a - b) * f' b ≤ f a - f b := by
    intro a ha b hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · have h := hf.slope_le_of_hasDerivWithinAt ha hb hab (hf' b hb)
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hab)] at h
      linarith
    · rw [sub_self, sub_self, zero_mul]
    · have h := hf.le_slope_of_hasDerivWithinAt hb ha hab (hf' b hb)
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hab)] at h
      linarith
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ B) := fun g =>
    B.finite_real_spectrum.continuousOn g
  have h := sum_re_trace_cfc_mul_cfc_nonneg (ι := Fin 4)
    (f := ![f, fun _ => 1, fun x => x, fun _ => 1])
    (g := ![fun _ => 1, fun x => -f x, fun x => -f' x, fun x => x * f' x]) (s := s)
    (fun a ha b hb => by
      simp only [Fin.sum_univ_four, Matrix.cons_val]
      linarith [hscalar a ha b hb]) hA hB hAs hBs
  simp only [Fin.sum_univ_four, Matrix.cons_val] at h
  have hsA : IsSelfAdjoint A := hA
  have hsB : IsSelfAdjoint B := hB
  rw [cfc_const_one ℝ A hsA, cfc_const_one ℝ B hsB, cfc_neg, cfc_neg, cfc_id' ℝ A hsA,
    cfc_mul (fun x => x) f' B (hcont _) (hcont _), cfc_id' ℝ B hsB, Matrix.mul_one, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_neg, map_neg, map_neg] at h
  rw [Matrix.sub_mul, Matrix.trace_sub, map_sub]
  linarith

/-! ### Compressions -/

/-- **The power scheme bound.** For positive semidefinite $\mathbf{B}$ and $\mathbf{Q}$ with
orthonormal columns,
$\|\mathbf{Q}^{\mathsf{H}}\mathbf{B}\mathbf{Q}\|_2^{q+1}
\le \|\mathbf{Q}^{\mathsf{H}}\mathbf{B}^{q+1}\mathbf{Q}\|_2$. This is why power iteration improves
the randomized range finder. [HalkoMartinssonTropp2011, Proposition 8.6]. -/
theorem specNorm_conjTranspose_mul_mul_pow_le {B : Matrix n n 𝕜} (hB : B.PosSemidef)
    {Q : Matrix n p 𝕜} (hQ : HasOrthonormalCols Q) (q : ℕ) :
    specNorm (Qᴴ * B * Q) ^ (q + 1) ≤ specNorm (Qᴴ * B ^ (q + 1) * Q) := by
  rcases isEmpty_or_nonempty p with hp | hp
  · have h0 : Qᴴ * B * Q = 0 := Subsingleton.elim _ _
    rw [h0, specNorm_zero, zero_pow (Nat.succ_ne_zero q)]
    exact specNorm_nonneg _
  · have hM : (Qᴴ * B * Q).PosSemidef := hB.conjTranspose_mul_mul_same Q
    obtain ⟨u, hu, hMu⟩ := hM.exists_norm_eq_one_and_mulVec_eq_specNorm_smul
    have hx : ‖WithLp.toLp 2 (Q *ᵥ u)‖ = 1 := by rw [hQ.norm_toLp_mulVec, hu]
    have h1 : specNorm (Qᴴ * B * Q) = RCLike.re (quadForm B (Q *ᵥ u)) := by
      rw [← quadForm_conjTranspose_mul_mul, re_quadForm_of_mulVec_eq_smul hu hMu]
    have h2 := apply_re_quadForm_le_re_quadForm_cfc (convexOn_pow (q + 1)) hB.isHermitian
      hB.spectrum_subset_Ici hx
    have hsa : IsSelfAdjoint B := hB.isHermitian
    rw [cfc_pow_id B (q + 1) hsa] at h2
    have h3 := abs_re_quadForm_le (Qᴴ * B ^ (q + 1) * Q) u
    rw [quadForm_conjTranspose_mul_mul, hu, one_pow, mul_one] at h3
    rw [h1]
    exact h2.trans ((le_abs_self _).trans h3)

/-- **Trace Jensen for compressions** (Berezin's inequality). For $f$ convex on a set containing
the spectrum of the Hermitian $\mathbf{A}$ and $\mathbf{Q}$ with orthonormal columns,
$\operatorname{Re} \operatorname{tr} f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})
\le \operatorname{Re} \operatorname{tr}(\mathbf{Q}^{\mathsf{H}} f(\mathbf{A}) \mathbf{Q})$.
[Carlen2010, Theorem 2.12 context]; [Bhatia1997, Problem IX.8.14]. -/
theorem re_trace_cfc_conjTranspose_mul_mul_le {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) :
    RCLike.re (cfc f (Qᴴ * A * Q)).trace ≤ RCLike.re (Qᴴ * cfc f A * Q).trace := by
  have hM : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  obtain ⟨W, hW, hWW, hq⟩ := exists_frame_re_quadForm_eq_eigenvalue hM
  rw [hM.re_trace_cfc, ← Fin.sum_univ_eq_sum_range (fun i => f (eigenvalue (Qᴴ * A * Q) i))]
  have h := sum_apply_re_quadForm_le_re_trace_cfc hf hA hAs (hQ.mul hW)
  have htr : (Q * W)ᴴ * cfc f A * (Q * W) = Wᴴ * (Qᴴ * cfc f A * Q) * W := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [htr, Matrix.trace_mul_cycle, hWW, Matrix.one_mul] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) h
  rw [← hq i, quadForm_conjTranspose_mul_mul, Matrix.mulVec_mulVec]

/-! ### The trace exponential -/

/-- **The trace exponential is monotone** in the Loewner order: for Hermitian $\mathbf{A}$ and
$\mathbf{A} \preceq \mathbf{B}$,
$\operatorname{Re} \operatorname{tr} \exp(\mathbf{A}) \le \operatorname{Re} \operatorname{tr}
\exp(\mathbf{B})$.
[Tropp2015, §2.1]. Port of `NLAlib.traceExp_le_traceExp`, there over $\mathbb{C}$. -/
theorem re_trace_exp_le_re_trace_exp_of_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : A ≤ B) : RCLike.re (exp A).trace ≤ RCLike.re (exp B).trace := by
  have hB : B.IsHermitian := by
    have h' := hA.add (Matrix.le_iff.mp h).isHermitian
    rwa [add_sub_cancel] at h'
  rw [hA.exp_eq_cfc, hB.exp_eq_cfc]
  exact re_trace_cfc_le_re_trace_cfc_of_le hA h (Real.exp_monotone.monotoneOn Set.univ)
    (Set.subset_univ _) (Set.subset_univ _)

/-- **The trace exponential is convex** on the Hermitian matrices:
$\mathbf{A} \mapsto \operatorname{Re} \operatorname{tr} \exp(\mathbf{A})$ is convex there.
[Tropp2015, §8.3]. Port of `NLAlib.convexOn_traceExp_isHermitian`, there over $\mathbb{C}$. -/
theorem convexOn_re_trace_exp :
    ConvexOn ℝ {A : Matrix n n 𝕜 | A.IsHermitian} fun A => RCLike.re (exp A).trace := by
  have h := convexOn_re_trace_cfc (𝕜 := 𝕜) (n := n) convexOn_exp
  have hS : {A : Matrix n n 𝕜 | A.IsHermitian ∧ spectrum ℝ A ⊆ Set.univ} =
      {A : Matrix n n 𝕜 | A.IsHermitian} := by
    ext A
    exact and_iff_left (Set.subset_univ _)
  rw [hS] at h
  refine h.congr fun A hA => ?_
  change RCLike.re (cfc Real.exp A).trace = RCLike.re (exp A).trace
  rw [Matrix.IsHermitian.exp_eq_cfc hA]

/-- The trace exponential is stable under perturbation:
$\operatorname{Re} \operatorname{tr} \exp(\mathbf{A})
\le e^{\|\mathbf{A} - \mathbf{B}\|_2} \operatorname{Re} \operatorname{tr} \exp(\mathbf{B})$ for
Hermitian $\mathbf{A}$, $\mathbf{B}$.
Port of `NLAlib.traceExp_le_exp_mul_traceExp_of_norm_sub_le`. -/
theorem re_trace_exp_le_exp_specNorm_sub_mul {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    RCLike.re (exp A).trace ≤ Real.exp (specNorm (A - B)) * RCLike.re (exp B).trace := by
  have h1 : A ≤ B + specNorm (A - B) • (1 : Matrix n n 𝕜) :=
    sub_le_iff_le_add'.mp (hA.sub hB).le_specNorm_smul_one
  rw [← re_trace_exp_add_real_smul_one]
  exact re_trace_exp_le_re_trace_exp_of_le hA h1

/-! ### Intrinsic dimension -/

/-- The **intrinsic dimension** of a matrix: the ratio of its trace to its spectral norm,
$\operatorname{intdim}(\mathbf{A}) = \operatorname{Re} \operatorname{tr} \mathbf{A} /
\|\mathbf{A}\|_2$
(Lean's division by zero gives $0$ for $\mathbf{A} = \mathbf{0}$). For a nonzero positive
semidefinite matrix it lies between $1$ and the rank.
[Tropp2015, Definition 7.1.1]. Port of `NLAlib.intrinsicDimension`, there over $\mathbb{C}$. -/
noncomputable def intrinsicDimension (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re A.trace / specNorm A

omit [DecidableEq n] in
/-- The intrinsic dimension of a nonzero positive semidefinite matrix is at least one:
$1 \le \operatorname{intdim}(\mathbf{A})$. -/
theorem _root_.Matrix.PosSemidef.one_le_intrinsicDimension {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≠ 0) : 1 ≤ intrinsicDimension A := by
  have hpos : 0 < specNorm A :=
    lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp h))
  rw [intrinsicDimension, one_le_div hpos]
  exact hA.specNorm_le_re_trace

omit [DecidableEq n] in
/-- The intrinsic dimension of a positive semidefinite matrix is at most its rank:
$\operatorname{intdim}(\mathbf{A}) \le \operatorname{rank} \mathbf{A}$. -/
theorem _root_.Matrix.PosSemidef.intrinsicDimension_le_rank {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : intrinsicDimension A ≤ A.rank := by
  rcases eq_or_ne A 0 with rfl | h
  · rw [intrinsicDimension, specNorm_zero, div_zero]
    exact Nat.cast_nonneg _
  have hpos : 0 < specNorm A :=
    lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp h))
  rw [intrinsicDimension, div_le_iff₀ hpos, hA.isHermitian.re_trace_eq_sum_range_eigenvalue,
    hA.isHermitian.rank_eq_card_eigenvalue_ne_zero, hA.specNorm_eq_eigenvalue_zero,
    ← Finset.sum_filter_ne_zero]
  have hle := Finset.sum_le_card_nsmul
    ((Finset.range (Fintype.card n)).filter fun k => eigenvalue A k ≠ 0)
    (fun k => eigenvalue A k) (eigenvalue A 0) fun k _ => hA.eigenvalue_antitone (Nat.zero_le k)
  rwa [nsmul_eq_mul] at hle

omit [DecidableEq n] in
/-- Enlarging the denominator does not increase the ratio defining the intrinsic dimension: if
$\|\mathbf{A}\|_2 \le c$ then
$\operatorname{Re} \operatorname{tr} \mathbf{A} / c \le \operatorname{intdim}(\mathbf{A})$. -/
private theorem re_trace_div_le_intrinsicDimension {A : Matrix n n 𝕜} (hA : A.PosSemidef) {c : ℝ}
    (hc : specNorm A ≤ c) : RCLike.re A.trace / c ≤ intrinsicDimension A := by
  rcases eq_or_ne A 0 with rfl | h
  · rw [intrinsicDimension, Matrix.trace_zero, map_zero, zero_div, zero_div]
  · have hpos : 0 < specNorm A :=
      lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp h))
    exact div_le_div_of_nonneg_left ((specNorm_nonneg A).trans hA.specNorm_le_re_trace) hpos hc

omit [DecidableEq m] [DecidableEq n] in
/-- The intrinsic dimension of a block diagonal positive semidefinite matrix is at most the sum
of the intrinsic dimensions of the blocks $\mathbf{A}$, $\mathbf{B}$.
[Tropp2015, §7.3]. Port of `NLAlib.intrinsicDimension_fromBlocks`. -/
theorem intrinsicDimension_fromBlocks_le {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    intrinsicDimension (Matrix.fromBlocks A 0 0 B) ≤
      intrinsicDimension A + intrinsicDimension B := by
  rw [intrinsicDimension, Matrix.trace_fromBlocks, map_add, specNorm_fromBlocks_zero₁₂_zero₂₁,
    add_div]
  exact add_le_add (re_trace_div_le_intrinsicDimension hA (le_max_left _ _))
    (re_trace_div_le_intrinsicDimension hB (le_max_right _ _))

omit [DecidableEq m] [DecidableEq n] in
/-- The intrinsic dimension of a block diagonal positive semidefinite matrix is at least the
smaller of the intrinsic dimensions of the blocks $\mathbf{A}$, $\mathbf{B}$.
Port of `NLAlib.intrinsicDimension_fromBlocks`. -/
theorem min_intrinsicDimension_le_intrinsicDimension_fromBlocks {A : Matrix m m 𝕜}
    {B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    min (intrinsicDimension A) (intrinsicDimension B) ≤
      intrinsicDimension (Matrix.fromBlocks A 0 0 B) := by
  have htA : 0 ≤ RCLike.re A.trace := (specNorm_nonneg A).trans hA.specNorm_le_re_trace
  have htB : 0 ≤ RCLike.re B.trace := (specNorm_nonneg B).trans hB.specNorm_le_re_trace
  rw [intrinsicDimension, intrinsicDimension, intrinsicDimension, Matrix.trace_fromBlocks, map_add,
    specNorm_fromBlocks_zero₁₂_zero₂₁]
  rcases le_total (specNorm A) (specNorm B) with hAB | hAB
  · rw [max_eq_right hAB]
    exact (min_le_right _ _).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_left htA) (specNorm_nonneg B))
  · rw [max_eq_left hAB]
    exact (min_le_left _ _).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right htB) (specNorm_nonneg A))

/-- **The intrinsic dimension lemma.** For $\varphi$ convex on $[0, \infty)$ with
$\varphi(0) = 0$ and positive semidefinite $\mathbf{A}$,
$$\operatorname{Re} \operatorname{tr} \varphi(\mathbf{A})
  \le \operatorname{intdim}(\mathbf{A}) \, \varphi(\|\mathbf{A}\|_2) \,.$$
[Tropp2015, Lemma 7.5.1].
Port of `NLAlib.traceFunction_le_intrinsicDimension_mul`, there over $\mathbb{C}$.
Result: intrinsic-dimension -/
theorem _root_.Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Ici 0) φ) (hφ0 : φ 0 = 0) :
    RCLike.re (cfc φ A).trace ≤ intrinsicDimension A * φ (specNorm A) := by
  rcases eq_or_ne A 0 with rfl | h
  · rw [intrinsicDimension, specNorm_zero, div_zero, zero_mul,
      (Matrix.isHermitian_zero (α := 𝕜) (n := n)).re_trace_cfc]
    simp only [eigenvalue_zero, hφ0, Finset.sum_const_zero, le_refl]
  have hpos : 0 < specNorm A :=
    lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp h))
  rw [hA.isHermitian.re_trace_cfc, intrinsicDimension,
    hA.isHermitian.re_trace_eq_sum_range_eigenvalue, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi0 := hA.eigenvalue_nonneg i
  have hiL : eigenvalue A i ≤ specNorm A :=
    (le_abs_self _).trans (hA.isHermitian.abs_eigenvalue_le_specNorm i)
  have hc := hφ.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hpos.le)
    (sub_nonneg.mpr ((div_le_one hpos).mpr hiL)) (div_nonneg hi0 hpos.le)
    (sub_add_cancel 1 (eigenvalue A i / specNorm A))
  rw [hφ0, smul_zero, zero_add, zero_add, smul_eq_mul, smul_eq_mul,
    div_mul_cancel₀ _ hpos.ne'] at hc
  exact hc

/-! ### Jensen from a supporting line -/

-- Stage B1b

omit [DecidableEq m] [DecidableEq p] in
/-- **Jensen's inequality for a quadratic form, from a supporting line**: for Hermitian
$\mathbf{A}$ with spectrum in $s$, a unit vector $\mathbf{x}$ and $\varphi$ with a supporting line
on $s$ at $\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$,
$$\varphi(\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})) \le
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\varphi(\mathbf{A})\mathbf{x})\,,$$
with no convexity assumed. Generalises `NLAlib.apply_re_quadForm_le_re_quadForm_cfc` (a convex
$\varphi$ differentiable at the point has a supporting line there, `ConvexOn.hasSupportingLineOn`).
[TroppWebber2023, Lemma 9.4 (proof)]. -/
theorem apply_re_quadForm_le_re_quadForm_cfc_of_hasSupportingLineOn {φ : ℝ → ℝ} {s : Set ℝ}
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) (hφ : HasSupportingLineOn φ s (RCLike.re (quadForm A x))) :
    φ (RCLike.re (quadForm A x)) ≤ RCLike.re (quadForm (cfc φ A) x) := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_weights_re_quadForm_cfc hA hx
  obtain ⟨c, hc⟩ := hφ
  have hsa : IsSelfAdjoint A := hA
  have hid := hw fun x => x
  rw [cfc_id' ℝ A hsa] at hid
  set a := RCLike.re (quadForm A x)
  have hsum : ∑ i, w i • (φ a + c * (eigenvalue A i - a)) =
      φ a * ∑ i, w i + c * (∑ i, w i • eigenvalue A i - a * ∑ i, w i) := by
    simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hw1, ← hid, mul_one, mul_one, sub_self, mul_zero, add_zero] at hsum
  rw [hw φ, ← hsum]
  exact Finset.sum_le_sum fun i _ => smul_le_smul_of_nonneg_left
    (hc _ (hAs (hA.eigenvalue_mem_spectrum i.isLt))) (hw0 i)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
/-- The top eigenvector of $\mathbf{P}\mathbf{A}\mathbf{A}^{\mathsf{H}}\mathbf{P}$ lies in the
range of the orthogonal projector $\mathbf{P}$ when $\|\mathbf{P}\mathbf{A}\|_2 > 0$: there is a
unit $\mathbf{u}$ with $\mathbf{P}\mathbf{u} = \mathbf{u}$ and
$\operatorname{Re}(\mathbf{u}^{\mathsf{H}}\mathbf{A}\mathbf{A}^{\mathsf{H}}\mathbf{u}) =
\|\mathbf{P}\mathbf{A}\|_2^2$. -/
private theorem exists_mulVec_eq_self_and_re_quadForm_eq_specNorm_sq {A : Matrix m n 𝕜}
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) (h₀ : 0 < specNorm (P * A)) :
    ∃ u : m → 𝕜, ‖WithLp.toLp 2 u‖ = 1 ∧ P *ᵥ u = u ∧
      RCLike.re (quadForm (A * Aᴴ) u) = specNorm (P * A) ^ 2 := by
  have hne : Nonempty m := by
    by_contra h
    have : P * A = 0 := by
      have := not_nonempty_iff.mp h
      exact Subsingleton.elim _ _
    rw [this, specNorm_zero] at h₀
    exact lt_irrefl _ h₀
  have hM : (P * A * (P * A)ᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  obtain ⟨u, hu, hMu⟩ := hM.exists_norm_eq_one_and_mulVec_eq_specNorm_smul
  rw [specNorm_mul_conjTranspose_self] at hMu
  have hMe : P * A * (P * A)ᴴ = Pᴴ * (A * Aᴴ) * P := by
    rw [Matrix.conjTranspose_mul, hP.conjTranspose_eq]
    simp only [Matrix.mul_assoc]
  have hPM : P * (P * A * (P * A)ᴴ) = P * A * (P * A)ᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.mul_self]
  have hc : (specNorm (P * A) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h₀.ne'
  have hPu : P *ᵥ u = u := by
    have h := congrArg (fun M => M *ᵥ u) hPM
    simp only [← Matrix.mulVec_mulVec, hMu, Matrix.mulVec_smul] at h
    exact smul_right_injective _ hc h
  refine ⟨u, hu, hPu, ?_⟩
  rw [← re_quadForm_of_mulVec_eq_smul hu hMu, hMe, quadForm_conjTranspose_mul_mul, hPu]

omit [DecidableEq n] [DecidableEq p] in
/-- **The projection half of the almost-convex Jensen inequality**: for an orthogonal projector
$\mathbf{P}$ with $\mathbf{P}\mathbf{A} \ne \mathbf{0}$, a matrix $\mathbf{B}$ with
$\mathbf{B}\mathbf{B}^{\mathsf{H}} = \varphi(\mathbf{A}\mathbf{A}^{\mathsf{H}})$, and $\varphi$
with a supporting line on $[0, \infty)$ at $\|\mathbf{P}\mathbf{A}\|_2^2$,
$$\varphi(\|\mathbf{P}\mathbf{A}\|_2^2) \le \|\mathbf{P}\mathbf{B}\|_2^2\,.$$
The top eigenvector of $\mathbf{P}\mathbf{A}\mathbf{A}^{\mathsf{H}}\mathbf{P}$ lies in the range of
$\mathbf{P}$, and the quadratic-form half applies there. The hypothesis
$\|\mathbf{P}\mathbf{A}\|_2 > 0$ is needed: at $\mathbf{P} = \mathbf{0}$ the conclusion is
$\varphi(0) \le 0$. [TroppWebber2023, Lemma 9.4, (9.4)]. -/
theorem apply_specNorm_mul_sq_le_specNorm_mul_sq_of_hasSupportingLineOn {φ : ℝ → ℝ}
    {A : Matrix m n 𝕜} {B : Matrix m p 𝕜} (hB : B * Bᴴ = cfc φ (A * Aᴴ)) {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (h₀ : 0 < specNorm (P * A))
    (hφ : HasSupportingLineOn φ (Set.Ici 0) (specNorm (P * A) ^ 2)) :
    φ (specNorm (P * A) ^ 2) ≤ specNorm (P * B) ^ 2 := by
  obtain ⟨u, hu, hPu, hq⟩ := exists_mulVec_eq_self_and_re_quadForm_eq_specNorm_sq hP h₀
  have hH : (A * Aᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have h1 := apply_re_quadForm_le_re_quadForm_cfc_of_hasSupportingLineOn hH.isHermitian
    hH.spectrum_subset_Ici hu (hq ▸ hφ)
  rw [hq, ← hB] at h1
  have hBe : quadForm (B * Bᴴ) u = quadForm (P * B * (P * B)ᴴ) u := by
    rw [Matrix.conjTranspose_mul, hP.conjTranspose_eq, ← hPu, ← quadForm_conjTranspose_mul_mul,
      hP.conjTranspose_eq, hPu]
    simp only [Matrix.mul_assoc]
  have h2 := abs_re_quadForm_le (P * B * (P * B)ᴴ) u
  rw [← hBe, hu, one_pow, mul_one, specNorm_mul_conjTranspose_self] at h2
  exact h1.trans ((le_abs_self _).trans h2)

end NLAlib
