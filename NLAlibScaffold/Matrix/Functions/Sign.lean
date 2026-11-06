/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Matrix.Perturbation.DavisKahanGap
public import NLAlib.Matrix.Spectral.Inertia
public import NLAlib.Matrix.Spectral.Weyl
public import NLAlibScaffold.Polynomial.Approximation.NewtonSchulz
public import Mathlib.Data.Real.Sign

/-!
# The sign of a Hermitian matrix (scaffold)

Statements for a new file `NLAlib/Matrix/Functions/Sign.lean` (stage HDIAG, wave W1, design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` §3.2). The sign of a Hermitian matrix is
Mathlib's `cfc Real.sign A`; no new definition. The headline is a dimension-free perturbation
bound, $\|\operatorname{sign}(\mathbf{A}) - \operatorname{sign}(\mathbf{B})\|_2 \le
2\|\mathbf{A} - \mathbf{B}\|_2/a$ when every eigenvalue of $\mathbf{A}$ has modulus at least $a$,
proved by the Davis–Kahan theorem; it replaces the contour-integral Lemma 2.2 of [Shah2024]
($n\|\mathbf{A} - \mathbf{B}\|_2/(a - \|\mathbf{A} - \mathbf{B}\|_2)$, for any matrices).

## Main results

* `Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le`: the perturbation bound.
* `Matrix.IsHermitian.cfc_newtonSchulz`, `Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz`.
* `Matrix.IsHermitian.specNorm_sub_cfc_sign_le`.
* `Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq`: frames of the spectral
  projectors $\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c\mathbf{I}))$.
* `Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign`: the trace of the projector is the inertia.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The Newton–Schulz map of a Hermitian matrix is the polynomial
$g(\mathbf{A}) = \tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$.
Proof: `cfc_mul`, `cfc_sub`, `cfc_const`, `cfc_id`, `cfc_pow` (Mathlib's unital continuous
functional calculus) after rewriting
`NLAlib.newtonSchulz` as `fun x => (2⁻¹ : ℝ) * (x * (3 - x * x))`; or
`Matrix.IsHermitian.cfc_eq` and a diagonal computation. M, about 12 lines. -/
theorem _root_.Matrix.IsHermitian.cfc_newtonSchulz {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    cfc newtonSchulz A = (2⁻¹ : ℝ) • (A * ((3 : ℝ) • (1 : Matrix n n 𝕜) - A * A)) := by
  have hf : newtonSchulz = fun x : ℝ => (2⁻¹ : ℝ) * (x * ((3 : ℝ) - x * x)) :=
    funext fun x => by simp only [newtonSchulz]; ring
  have hA' : IsSelfAdjoint A := hA.isSelfAdjoint
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A
  have hsq : cfc (fun x : ℝ => x * x) A = A * A := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A, hid]
  have h3 : cfc (fun _ : ℝ => (3 : ℝ)) A = (3 : ℝ) • (1 : Matrix n n 𝕜) := by
    rw [cfc_const (3 : ℝ) A, Algebra.algebraMap_eq_smul_one]
  rw [hf, cfc_const_mul (2⁻¹ : ℝ) (fun x : ℝ => x * ((3 : ℝ) - x * x)) A,
    cfc_mul (fun x : ℝ => x) (fun x : ℝ => (3 : ℝ) - x * x) A,
    cfc_sub (fun _ : ℝ => (3 : ℝ)) (fun x : ℝ => x * x) A, hid, hsq, h3]

/-- **Perturbation of the sign of a Hermitian matrix**: for Hermitian $\mathbf{A}, \mathbf{B}$
and $a > 0$ with $\lvert \lambda \rvert \ge a$ for every eigenvalue $\lambda$ of $\mathbf{A}$,
$$\|\operatorname{sign}(\mathbf{A}) - \operatorname{sign}(\mathbf{B})\|_2 \le
\frac{2\|\mathbf{A} - \mathbf{B}\|_2}{a} \,.$$
[Shah2024, Lemma 2.2], there $n\|\mathbf{A} - \mathbf{B}\|_2/(a - \|\mathbf{A} - \mathbf{B}\|_2)$
for $\|\mathbf{A} - \mathbf{B}\|_2 < a$ and any matrices, by a contour integral; for Hermitian
matrices the bound is dimension-free and needs no size condition.
Proof: if $\|\mathbf{E}\|_2 \ge a$, $\mathbf{E} = \mathbf{B} - \mathbf{A}$, the left side is at
most $2$ (`Matrix.IsHermitian.specNorm_cfc_le` with $\lvert\operatorname{sign}\rvert \le 1$). Else
$\mathbf{A}$ has $p$ eigenvalues $\ge a$ and $\mathbf{B}$ exactly $p$ eigenvalues
$\ge a - \|\mathbf{E}\|_2 > 0$ and none in $(-(a - \|\mathbf{E}\|_2), a - \|\mathbf{E}\|_2)$
(`Matrix.IsHermitian.abs_eigenvalue_sub_le`); $\operatorname{sign} = 2\mathbf{P} - \mathbf{I}$
for the top-$p$ eigenprojectors (`HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose`);
`Matrix.IsHermitian.specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap` with
$\lambda_{p-1}(\mathbf{A}) - \lambda_p(\mathbf{A}) \ge 2a$ gives
$\|(\mathbf{I} - \mathbf{P})\mathbf{P}'\|_2 \le \|\mathbf{E}\|_2/a$, and for projectors of equal
rank $\|\mathbf{P} - \mathbf{P}'\|_2 = \|(\mathbf{I} - \mathbf{P})\mathbf{P}'\|_2$
(`IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq`). Cases $p = 0$ and
$p = \lvert n \rvert$ separately (then the sign is $\mp\mathbf{I}$ for both). M, about 70 lines. -/
theorem _root_.Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {a : ℝ} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ A, a ≤ |x|) :
    specNorm (cfc Real.sign A - cfc Real.sign B) ≤ 2 * specNorm (A - B) / a := by
  sorry

/-- The Newton–Schulz map does not change the sign: for Hermitian $\mathbf{A}$ with
$0 < \lvert \lambda \rvert < \sqrt3$ for every eigenvalue,
$\operatorname{sign}(g(\mathbf{A})) = \operatorname{sign}(\mathbf{A})$. [Shah2024, proof of
Theorem 2.6].
Proof: `cfc_comp` (Mathlib `cfc_comp'`), and $\operatorname{sign} \circ g = \operatorname{sign}$
on the spectrum (`NLAlib.mul_newtonSchulz_add_pos` at $\xi = u = 0$, or directly:
$g(x) = x(3 - x^2)/2$ has the sign of $x$), `cfc_congr`. M, about 12 lines. -/
theorem _root_.Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ x ∈ spectrum ℝ A, 0 < |x| ∧ |x| < √3) :
    cfc Real.sign (cfc newtonSchulz A) = cfc Real.sign A := by
  sorry

/-- A Hermitian matrix with nearly unimodular eigenvalues is near its sign: if
$\lvert 1 - \lambda^2 \rvert \le \delta$ for every eigenvalue $\lambda$, then
$\|\mathbf{A} - \operatorname{sign}(\mathbf{A})\|_2 \le \delta$. [Shah2024, proof of
Theorem 2.6].
Proof: $\mathbf{A} - \operatorname{sign}(\mathbf{A}) = f(\mathbf{A})$ with
$f(x) = x - \operatorname{sign}(x)$ (`cfc_sub`, `cfc_id'`), and
$\lvert x - \operatorname{sign} x \rvert = \lvert \lvert x \rvert - 1 \rvert \le
\lvert 1 - x^2 \rvert$ for $x \ne 0$ and $0 \le 1$ at $x = 0$; `Matrix.IsHermitian.specNorm_cfc_le`.
S, about 15 lines. -/
theorem _root_.Matrix.IsHermitian.specNorm_sub_cfc_sign_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {δ : ℝ} (hδ : 0 ≤ δ) (h : ∀ x ∈ spectrum ℝ A, |1 - x ^ 2| ≤ δ) :
    specNorm (A - cfc Real.sign A) ≤ δ := by
  sorry

/-- **Frames of the spectral projectors**: for Hermitian $\mathbf{A}$ and $c$ not an eigenvalue,
with $k = i_+(\mathbf{A} - c\mathbf{I})$ (`NLAlib.inertiaPos`), there is
$\mathbf{V} \in \Bbbk^{n \times k}$ with orthonormal columns such that
$\mathbf{V}\mathbf{V}^{\mathsf{H}} = \tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A} -
c\mathbf{I}))$, $\mathbf{A}\mathbf{V} = \mathbf{V}(\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V})$,
and the spectrum of $\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V}$ lies in the spectrum of
$\mathbf{A}$ above $c$. The negative side is this lemma for $-\mathbf{A}$ and $-c$.
[Shah2024, proof of Lemma 4.1].
Proof: take the eigenvectors of `Matrix.IsHermitian.eigenvectorBasis` with eigenvalue $> c$,
reindexed by `Fin k` (`Matrix.IsHermitian.lt_inertiaPos_iff` counts them);
`HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose` for the projector,
`Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq` for the invariance; the compression is
diagonal with those eigenvalues. M, about 60 lines. -/
theorem _root_.Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) :
    ∃ V : Matrix n (Fin (inertiaPos (A - c • (1 : Matrix n n 𝕜)))) 𝕜, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix n n 𝕜))) ∧
      A * V = V * (Vᴴ * A * V) ∧ spectrum ℝ (Vᴴ * A * V) ⊆ spectrum ℝ A ∩ Set.Ioi c := by
  sorry

/-- **The trace of a spectral projector is the inertia**: for Hermitian $\mathbf{A}$ and $c$ not an
eigenvalue, $\operatorname{Re}\operatorname{tr}\tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A}
- c\mathbf{I})) = i_+(\mathbf{A} - c\mathbf{I})$. [Shah2024, proof of Lemma 4.1].
Proof: `Matrix.IsHermitian.re_trace_cfc` for $f(x) = \tfrac12(1 + \operatorname{sign}(x - c))$
(the left side is $\operatorname{tr}$ of `cfc` of it, `cfc_add`, `cfc_const`), which is the
indicator of $(c, \infty)$ on the spectrum; count with `NLAlib.inertiaPos` and
`Matrix.IsHermitian.lt_inertiaPos_iff`. M, about 20 lines. -/
theorem _root_.Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) :
    RCLike.re ((2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix n n 𝕜)))).trace =
      inertiaPos (A - c • (1 : Matrix n n 𝕜)) := by
  have hB : (A - c • (1 : Matrix n n 𝕜)).IsHermitian := by
    refine hA.sub ?_
    unfold Matrix.IsHermitian
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
  have hsp : ∀ x ∈ spectrum ℝ (A - c • (1 : Matrix n n 𝕜)), x ≠ 0 := by
    intro x hx hx0
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hc y hy (sub_eq_zero.mp hx0)
  have hcont : ∀ y : ℝ, y ≠ 0 → ContinuousAt Real.sign y := fun y hy => by
    rcases hy.lt_or_gt with hneg | hpos
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (-1 : ℝ)) y).congr
        (Filter.eventually_of_mem (Iio_mem_nhds hneg) fun z hz => (Real.sign_of_neg hz).symm)
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) y).congr
        (Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun z hz => (Real.sign_of_pos hz).symm)
  have hsign : ContinuousOn Real.sign (spectrum ℝ (A - c • (1 : Matrix n n 𝕜))) :=
    fun x hx => (hcont x (hsp x hx)).continuousWithinAt
  have hcg : cfc (fun y : ℝ => (2⁻¹ : ℝ) * (1 + Real.sign y)) (A - c • (1 : Matrix n n 𝕜)) =
      (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix n n 𝕜))) := by
    rw [cfc_const_mul (2⁻¹ : ℝ) (fun y : ℝ => 1 + Real.sign y) (A - c • (1 : Matrix n n 𝕜)),
      cfc_add (A - c • (1 : Matrix n n 𝕜)) (fun _ : ℝ => (1 : ℝ)) Real.sign
        continuousOn_const hsign,
      cfc_const (1 : ℝ) (A - c • (1 : Matrix n n 𝕜)), map_one]
  rw [← hcg, hB.re_trace_cfc, inertiaPos, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have he := hsp _ (hB.eigenvalue_mem_spectrum (Finset.mem_range.mp hi))
  rcases he.lt_or_gt with hneg | hpos
  · rw [Real.sign_of_neg hneg, if_neg (not_lt.mpr hneg.le)]; norm_num
  · rw [Real.sign_of_pos hpos, if_pos hpos]; norm_num

end NLAlib
