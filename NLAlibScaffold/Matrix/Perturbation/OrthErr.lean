/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.OrthErr
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Compare

/-!
# Nearly orthonormal bases and the orthogonalization guarantee (scaffold)

Statements for `NLAlib/Matrix/Perturbation/OrthErr.lean` (stage LANCZOS-REORTH, design note
`docs/design/Krylov-LanczosReorth.md` §1.1–1.2, ids B3–B8): monotonicity of `NLAlib.IsOrthErr`,
the derived coefficient bound, orthogonality of the normalized output, the column-append identity
for the Gram defect and its $\sqrt{3m}\,\mu$ consequence, injectivity and the dimension count, and
the norm bounds of a nearly orthonormal basis.

## Main results

* `NLAlib.IsOrthErr.mono`, `NLAlib.IsOrthErr.norm_coef_le`,
  `NLAlib.IsOrthErr.norm_transpose_mulVec_smul_le`.
* `NLAlib.frobNorm_gram_sub_one_sq_eq`, `NLAlib.frobNorm_gram_sub_one_le_of_columns`.
* `NLAlib.injective_mulVec_of_specNorm_gram_sub_one_lt_one`,
  `NLAlib.le_of_specNorm_gram_sub_one_lt_one`.
* `NLAlib.specNorm_le_sqrt_of_specNorm_gram_sub_one_le`,
  `NLAlib.frobNorm_le_sqrt_of_specNorm_gram_sub_one_le`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n j : ℕ}

/-- **Norm bound of a nearly orthonormal basis** (B8): if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta$ then $\|\mathbf{V}\|_2 \le
\sqrt{1 + \eta}$. No printed source.
Proof: $\|\mathbf{V}\|_2^2 = \|\mathbf{V}^{\mathsf{T}}\mathbf{V}\|_2 \le 1 + \eta$ by the triangle
inequality against $\mathbf{I}$ (`specNorm_conjTranspose_mul_self`, `specNorm_one_le`, or the
quadratic form $\|\mathbf{V}\mathbf{x}\|^2 = \mathbf{x}^{\mathsf{T}}\mathbf{V}^{\mathsf{T}}
\mathbf{V}\mathbf{x}$), then `Real.le_sqrt`. S, about 15 lines. -/
theorem specNorm_le_sqrt_of_specNorm_gram_sub_one_le {V : Matrix (Fin n) (Fin j) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) : specNorm V ≤ Real.sqrt (1 + η) := by
  have h1 : specNorm (Vᵀ * V) ≤ 1 + η := by
    calc specNorm (Vᵀ * V) = specNorm ((Vᵀ * V - 1) + 1) := by rw [sub_add_cancel]
      _ ≤ specNorm (Vᵀ * V - 1) + specNorm 1 := specNorm_add_le _ _
      _ ≤ η + 1 := add_le_add hV specNorm_one_le
      _ = 1 + η := add_comm _ _
  have h2 : specNorm V ^ 2 = specNorm (Vᵀ * V) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, specNorm_conjTranspose_mul_self]
  exact (Real.le_sqrt (specNorm_nonneg V) ((specNorm_nonneg _).trans h1)).2
    (by rw [← h2] at h1; exact h1)

/-- **Frobenius norm of a nearly orthonormal basis** (B8): if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta$ then $\|\mathbf{V}\|_{\mathsf F}
\le \sqrt{j(1 + \eta)}$ for $j$ columns. No printed source.
Proof: $\|\mathbf{V}\|_{\mathsf F}^2 = \sum_c \|\mathbf{v}_c\|^2 = \operatorname{tr}
(\mathbf{V}^{\mathsf{T}}\mathbf{V})$ and each diagonal entry of $\mathbf{V}^{\mathsf{T}}\mathbf{V}$
is at most $1 + \eta$ (an entry of $\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}$ is bounded by
its spectral norm, `NLAlib.norm_apply_le_specNorm`; `frobNorm_sq_eq_sum` or
`frobNorm_sq_eq_re_trace`). S, about 15 lines. -/
theorem frobNorm_le_sqrt_of_specNorm_gram_sub_one_le {V : Matrix (Fin n) (Fin j) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) : frobNorm V ≤ Real.sqrt (j * (1 + η)) := by
  have hdiag : ∀ i, (Vᵀ * V) i i ≤ 1 + η := fun i => by
    have h := norm_apply_le_specNorm (Vᵀ * V - 1) i i
    rw [Matrix.sub_apply, Matrix.one_apply_eq, Real.norm_eq_abs] at h
    linarith [le_abs_self ((Vᵀ * V) i i - 1)]
  have htr : (Vᵀ * V).trace ≤ j * (1 + η) := by
    rw [Matrix.trace]
    calc ∑ i, (Vᵀ * V) i i ≤ ∑ _i : Fin j, (1 + η) := Finset.sum_le_sum fun i _ => hdiag i
      _ = j * (1 + η) := by simp; ring
  have h2 : frobNorm V ^ 2 ≤ j * (1 + η) := by
    rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.re_to_real]
    exact htr
  exact (Real.le_sqrt (frobNorm_nonneg V) (le_trans (sq_nonneg _) h2)).2 h2

/-- **Monotonicity of the orthogonalization guarantee** (B3): a smaller precondition $\eta_0$ and
larger parameters $\varepsilon_1, \varepsilon_2, \varepsilon_3$ keep `NLAlib.IsOrthErr`.
Proof: both fields: weaken the hypothesis with `le_trans`, then `gcongr` on the right sides
(norms are nonnegative). S, about 8 lines. -/
theorem IsOrthErr.mono {η₀ ε₁ ε₂ ε₃ η₀' ε₁' ε₂' ε₃' : ℝ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w : Fin n → ℝ} {h : Fin j → ℝ} {w' : Fin n → ℝ} (hO : IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (hη : η₀' ≤ η₀) (h₁ : ε₁ ≤ ε₁') (h₂ : ε₂ ≤ ε₂') (h₃ : ε₃ ≤ ε₃') :
    IsOrthErr η₀' ε₁' ε₂' ε₃' V w h w' := by
  sorry

/-- **The coefficients of an orthogonalization step are small when the input is nearly
orthogonal** (B4): under `NLAlib.IsOrthErr` with $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} -
\mathbf{I}\|_2 \le \eta_0 < 1$,
$$\|\mathbf{h}\| \le \frac{\|\mathbf{V}^{\mathsf{T}}\mathbf{w}\| + \|\mathbf{V}^{\mathsf{T}}
\mathbf{w}'\| + \sqrt{1 + \eta_0}\,\varepsilon_2\|\mathbf{w}\|}{1 - \eta_0}.$$
No printed source; `docs/design/Krylov-LanczosReorth.md` §1.1.
Proof: with $\mathbf{f} = \mathbf{w} - \mathbf{V}\mathbf{h} - \mathbf{w}'$,
$\mathbf{V}^{\mathsf{T}}\mathbf{V}\mathbf{h} = \mathbf{V}^{\mathsf{T}}\mathbf{w} -
\mathbf{V}^{\mathsf{T}}\mathbf{w}' - \mathbf{V}^{\mathsf{T}}\mathbf{f}$; the left side has norm at
least $(1 - \eta_0)\|\mathbf{h}\|$ (subtract $(\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I})
\mathbf{h}$), and $\|\mathbf{V}^{\mathsf{T}}\mathbf{f}\| \le \sqrt{1+\eta_0}\,\varepsilon_2
\|\mathbf{w}\|$ by `NLAlib.specNorm_le_sqrt_of_specNorm_gram_sub_one_le` (the transpose has the
same spectral norm) and `IsOrthErr.residual`. Divide by $1 - \eta_0 > 0$. S, about 25 lines. -/
theorem IsOrthErr.norm_coef_le {η₀ ε₁ ε₂ ε₃ : ℝ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w : Fin n → ℝ} {h : Fin j → ℝ} {w' : Fin n → ℝ} (hO : IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hη : η₀ < 1) (hε₂ : 0 ≤ ε₂) :
    ‖WithLp.toLp 2 h‖ ≤ (‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ + ‖WithLp.toLp 2 (Vᵀ *ᵥ w')‖ +
      Real.sqrt (1 + η₀) * ε₂ * ‖WithLp.toLp 2 w‖) / (1 - η₀) := by
  sorry

/-- **Orthogonality of the normalized output** (B5): under `NLAlib.IsOrthErr` and the
precondition, for $\mathbf{w}' \ne \mathbf{0}$,
$\|\mathbf{V}^{\mathsf{T}}(\mathbf{w}'/\|\mathbf{w}'\|)\| \le \varepsilon_1 + \varepsilon_3
\|\mathbf{w}\|/\|\mathbf{w}'\|$. The ratio $\|\mathbf{w}\|/\|\mathbf{w}'\|$ is what
admissibility controls. No printed source.
Proof: `Matrix.mulVec_smul`, `norm_smul`, `IsOrthErr.orth`, divide by $\|\mathbf{w}'\| > 0$
(`norm_pos_iff`). S, about 10 lines. -/
theorem IsOrthErr.norm_transpose_mulVec_smul_le {η₀ ε₁ ε₂ ε₃ : ℝ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w : Fin n → ℝ} {h : Fin j → ℝ} {w' : Fin n → ℝ} (hO : IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hw' : w' ≠ 0) :
    ‖WithLp.toLp 2 (Vᵀ *ᵥ (‖WithLp.toLp 2 w'‖⁻¹ • w'))‖ ≤
      ε₁ + ε₃ * ‖WithLp.toLp 2 w‖ / ‖WithLp.toLp 2 w'‖ := by
  sorry

/-- **The Gram defect when a column is appended** (B6): for $\mathbf{V} = [\mathbf{V}',
\mathbf{x}]$,
$$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_{\mathsf F}^2 =
\|\mathbf{V}'^{\mathsf{T}}\mathbf{V}' - \mathbf{I}\|_{\mathsf F}^2 +
2\|\mathbf{V}'^{\mathsf{T}}\mathbf{x}\|^2 + (\|\mathbf{x}\|^2 - 1)^2.$$
No printed source.
Proof: expand `frobNorm` as the sum of squared entries (`frobNorm_sq_eq_sum` or the definition)
over `Fin (m + 1)` × `Fin (m + 1)` with `Fin.sum_univ_castSucc` twice: the old block, the two
off-diagonal strips (entries $\mathbf{v}_c^{\mathsf{T}}\mathbf{x}$, equal by symmetry) and the
corner $\|\mathbf{x}\|^2 - 1$; `EuclideanSpace.norm_sq_eq`. S, about 30 lines. -/
theorem frobNorm_gram_sub_one_sq_eq {m : ℕ} (V : Matrix (Fin n) (Fin (m + 1)) ℝ) :
    frobNorm (Vᵀ * V - 1) ^ 2 =
      frobNorm ((V.submatrix id Fin.castSucc)ᵀ * V.submatrix id Fin.castSucc - 1) ^ 2 +
      2 * ‖WithLp.toLp 2 ((V.submatrix id Fin.castSucc)ᵀ *ᵥ fun i => V i (Fin.last m))‖ ^ 2 +
      (‖WithLp.toLp 2 (fun i => V i (Fin.last m))‖ ^ 2 - 1) ^ 2 := by
  sorry

/-- **Column-wise orthogonality accumulates as $\sqrt{3m}$** (B6): if each vector
$\mathbf{v}_{c+1}$ of a sequence satisfies $\|\mathbf{V}_c^{\mathsf{T}}\mathbf{v}_{c+1}\| \le \mu$
and $|\|\mathbf{v}_{c+1}\|^2 - 1| \le \mu$ ($\mathbf{V}_c$ the first $c$ vectors), then the first
$m$ vectors satisfy $\|\mathbf{V}_m^{\mathsf{T}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le
\sqrt{3m}\,\mu$. No printed source; `docs/design/Krylov-LanczosReorth.md` §1.2.
Proof: induction on $m$ with `NLAlib.frobNorm_gram_sub_one_sq_eq` (the submatrix of the
$(m+1)$-column matrix is the $m$-column one: `Matrix.submatrix`, `Fin.val_castSucc`), so the
square is at most $3m\mu^2$; take square roots (`Real.sqrt_le_sqrt`, `Real.sqrt_mul_self`).
S, about 25 lines. -/
theorem frobNorm_gram_sub_one_le_of_columns (v : ℕ → Fin n → ℝ) (m : ℕ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hg : ∀ c < m, ‖WithLp.toLp 2
      ((Matrix.of fun i (d : Fin c) => v ((d : ℕ) + 1) i)ᵀ *ᵥ v (c + 1))‖ ≤ μ)
    (hd : ∀ c < m, |‖WithLp.toLp 2 (v (c + 1))‖ ^ 2 - 1| ≤ μ) :
    frobNorm ((Matrix.of fun i (d : Fin m) => v ((d : ℕ) + 1) i)ᵀ *
      (Matrix.of fun i (d : Fin m) => v ((d : ℕ) + 1) i) - 1) ≤ Real.sqrt (3 * m) * μ := by
  sorry

/-- **A nearly orthonormal basis has independent columns** (B7): if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 < 1$ then $\mathbf{x} \mapsto
\mathbf{V}\mathbf{x}$ is injective. No printed source.
Proof: if $\mathbf{V}\mathbf{x} = \mathbf{0}$ then $\mathbf{x} = -(\mathbf{V}^{\mathsf{T}}
\mathbf{V} - \mathbf{I})\mathbf{x}$, so $\|\mathbf{x}\| \le \eta\|\mathbf{x}\|$ with $\eta < 1$
(`NLAlib.norm_toLp_mulVec_le`), hence $\mathbf{x} = 0$.
S, about 15 lines. -/
theorem injective_mulVec_of_specNorm_gram_sub_one_lt_one {V : Matrix (Fin n) (Fin j) ℝ}
    (hV : specNorm (Vᵀ * V - 1) < 1) : Function.Injective V.mulVec := by
  sorry

/-- **A nearly orthonormal $n \times j$ basis has $j \le n$** (B7). No printed source.
Proof: `NLAlib.injective_mulVec_of_specNorm_gram_sub_one_lt_one` gives an injective linear map
`Matrix.mulVecLin` from `Fin j → ℝ` to `Fin n → ℝ`; compare `Module.finrank`
(`LinearMap.finrank_le_finrank_of_injective`, `Module.finrank_fin_fun`). S, about 10 lines. -/
theorem le_of_specNorm_gram_sub_one_lt_one {V : Matrix (Fin n) (Fin j) ℝ}
    (hV : specNorm (Vᵀ * V - 1) < 1) : j ≤ n := by
  sorry

end NLAlib
