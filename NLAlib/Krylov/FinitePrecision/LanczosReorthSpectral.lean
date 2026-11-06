/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthBackward
public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Krylov.Eigenvalues.Ritz
public import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# Spectral consequences of the backward model of a reorthogonalized run

With $e$ = `NLAlib.LanczosReorthRun.backwardRadius`: the Ritz values interlace the eigenvalues of
$\mathbf{H}$ up to $e$; converged Ritz values are not duplicated (a residual-gated count;
interlacing alone gives no count, see the note's counterexample); Ritz-pair residuals; the
Kaniel–Paige–Saad bound for the backward model; Gauss quadrature exactness and its transfer to
$\mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}$ for Lipschitz $f$. Eigenvalues are indexed
decreasingly from $0$ (`NLAlib.eigenvalue`). Design: `docs/design/Krylov-LanczosReorth.md`
§3.2.

Common hypotheses as in `NLAlib/Krylov/FinitePrecision/LanczosReorthBackward.lean`.

## Main results

* `NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_le_add`,
  `NLAlib.LanczosReorthRun.eigenvalue_sub_le_eigenvalue_tridiagonal`: interlacing (F1).
* `NLAlib.LanczosReorthRun.card_le_card_eigenvalue_mem`: no duplicated converged Ritz values (F2).
* `NLAlib.LanczosReorthRun.exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul`,
  `NLAlib.LanczosReorthRun.exists_abs_eigenvalue_sub_le_of_β_le`: Ritz residuals (F3).
* `NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_mem_Icc`: containment (F4).
* `NLAlib.LanczosReorthRun.exists_backward_kaniel_paige_saad`: KPS transfer (F5).
* `NLAlib.LanczosReorthRun.exists_pure_backward_gauss`,
  `NLAlib.LanczosReorthRun.exists_pure_backward_abs_quadForm_cfc_sub_le`: quadrature (F6, F7).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- **Ritz values interlace from above up to $e$**: $\theta_i \le \lambda_i(\mathbf{H}) + e$
for $i < k$. [Simon1984b] in substance; [HornJohnson2013, Corollary 4.3.37] for the exact case. -/
theorem eigenvalue_tridiagonal_le_add (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.toLanczosData.tridiagonal i ≤ eigenvalue L.H i + L.backwardRadius := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have hgram := L.frobNorm_gram_sub_one_le hη hsmall (k + 1) le_rfl
  have hsq : Real.sqrt (3 * (((k + 1 : ℕ)) : ℝ)) = Real.sqrt (3 * ((k : ℝ) + 1)) := by
    push_cast; ring_nf
  rw [hsq] at hgram
  have hspec : specNorm ((basisOf L.v (k + 1))ᵀ * basisOf L.v (k + 1) - 1) ≤ 1 / 100 :=
    (specNorm_le_frobNorm _).trans (by linarith)
  have hPo := hasOrthonormalCols_polarFactor hspec (by norm_num)
  set P := polarFactor (basisOf L.v (k + 1)) with hPdef
  have hU : HasOrthonormalCols (P.submatrix id Fin.castSucc) :=
    hPo.submatrix (Equiv.refl _) (Fin.castSucc_injective _)
  have hH : L.H.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact L.transpose_H
  have hE' : E.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hEs
  have hA := hH.add hE'
  have hz : ∀ j : Fin k, ∑ x, P x (Fin.castSucc j) * P x (Fin.last k) = 0 := fun j => by
    have h := congrFun (congrFun (hPo.conjTranspose_mul_self) (Fin.castSucc j)) (Fin.last k)
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne] at h
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have hc : (P.submatrix id Fin.castSucc)ᴴ *ᵥ (L.β k • fun i => P i (Fin.last k)) = 0 := by
    funext j
    have hj : ((P.submatrix id Fin.castSucc)ᴴ *ᵥ (L.β k • fun i => P i (Fin.last k))) j =
        L.β k * ∑ x, P x (Fin.castSucc j) * P x (Fin.last k) := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm]
    rw [hj, hz j, mul_zero]; rfl
  have hT : (P.submatrix id Fin.castSucc)ᴴ * (L.H + E) * P.submatrix id Fin.castSucc =
      L.toLanczosData.tridiagonal := by
    rw [Matrix.mul_assoc, hid, Matrix.mul_add, ← Matrix.mul_assoc,
      hU.conjTranspose_mul_self, Matrix.one_mul, Matrix.mul_vecMulVec, hc]
    ext a b; simp [Matrix.vecMulVec]
  have hPoin := Matrix.IsHermitian.eigenvalue_conjTranspose_mul_mul_le hA hU
    (k := i) (by simpa using hi)
  rw [hT] at hPoin
  have hW := Matrix.IsHermitian.abs_eigenvalue_sub_le hA hH i
  have hd : specNorm ((L.H + E) - L.H) ≤ frobNorm E := by
    rw [add_sub_cancel_left]; exact specNorm_le_frobNorm E
  have := le_abs_self (eigenvalue (L.H + E) i - eigenvalue L.H i)
  linarith

/-- **Ritz values interlace from below up to $e$**:
$\lambda_{i + n - k}(\mathbf{H}) - e \le \theta_i$ for $i < k$ (and $k \le n$ by
`NLAlib.LanczosReorthRun.succ_le_card`). [Simon1984b] in substance. -/
theorem eigenvalue_sub_le_eigenvalue_tridiagonal (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.H (i + (n - k)) - L.backwardRadius ≤ eigenvalue L.toLanczosData.tridiagonal i := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have hkn := L.succ_le_card hη hsmall
  have hgram := L.frobNorm_gram_sub_one_le hη hsmall (k + 1) le_rfl
  have hsq : Real.sqrt (3 * (((k + 1 : ℕ)) : ℝ)) = Real.sqrt (3 * ((k : ℝ) + 1)) := by
    push_cast; ring_nf
  rw [hsq] at hgram
  have hspec : specNorm ((basisOf L.v (k + 1))ᵀ * basisOf L.v (k + 1) - 1) ≤ 1 / 100 :=
    (specNorm_le_frobNorm _).trans (by linarith)
  have hPo := hasOrthonormalCols_polarFactor hspec (by norm_num)
  set P := polarFactor (basisOf L.v (k + 1)) with hPdef
  have hU : HasOrthonormalCols (P.submatrix id Fin.castSucc) :=
    hPo.submatrix (Equiv.refl _) (Fin.castSucc_injective _)
  have hH : L.H.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact L.transpose_H
  have hE' : E.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hEs
  have hA := hH.add hE'
  have hz : ∀ j : Fin k, ∑ x, P x (Fin.castSucc j) * P x (Fin.last k) = 0 := fun j => by
    have h := congrFun (congrFun (hPo.conjTranspose_mul_self) (Fin.castSucc j)) (Fin.last k)
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne] at h
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have hc : (P.submatrix id Fin.castSucc)ᴴ *ᵥ (L.β k • fun i => P i (Fin.last k)) = 0 := by
    funext j
    have hj : ((P.submatrix id Fin.castSucc)ᴴ *ᵥ (L.β k • fun i => P i (Fin.last k))) j =
        L.β k * ∑ x, P x (Fin.castSucc j) * P x (Fin.last k) := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm]
    rw [hj, hz j, mul_zero]; rfl
  have hT : (P.submatrix id Fin.castSucc)ᴴ * (L.H + E) * P.submatrix id Fin.castSucc =
      L.toLanczosData.tridiagonal := by
    rw [Matrix.mul_assoc, hid, Matrix.mul_add, ← Matrix.mul_assoc,
      hU.conjTranspose_mul_self, Matrix.one_mul, Matrix.mul_vecMulVec, hc]
    ext a b; simp [Matrix.vecMulVec]
  have hPoin := Matrix.IsHermitian.eigenvalue_le_eigenvalue_conjTranspose_mul_mul hA hU
    (k := i) (d := n - k) (by simpa using hi) (by simp; omega)
  rw [hT] at hPoin
  have hW := Matrix.IsHermitian.abs_eigenvalue_sub_le hA hH (i + (n - k))
  have hd : specNorm ((L.H + E) - L.H) ≤ frobNorm E := by
    rw [add_sub_cancel_left]; exact specNorm_le_frobNorm E
  have := neg_abs_le (eigenvalue (L.H + E) (i + (n - k)) - eigenvalue L.H (i + (n - k)))
  linarith

/-- **Converged Ritz values are not duplicated**: for $r$ orthonormal eigenvectors
$\mathbf{y}_i$ of $\mathbf{T}_k$ with eigenvalues $\theta_i \in [a, b]$ and residuals
$\beta_k|\mathbf{e}_{k-1}^{\mathsf{T}}\mathbf{y}_i| < (g - 2e)/\sqrt r$, $g > 2e$, the matrix
$\mathbf{H}$ has at least $r$ eigenvalues in $(a - g, b + g)$. With $[a, b]$ a window around a
simple isolated eigenvalue this forbids two converged copies; the residual condition cannot be
dropped (`docs/design/Krylov-LanczosReorth.md` §3.2, counterexample $\operatorname{diag}(1,0,-1)$).
The phenomenon: [Paige1971], [Parlett1998, Ch. 13]; this statement: no printed source. -/
theorem card_le_card_eigenvalue_mem (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {r : ℕ} {Y : Matrix (Fin k) (Fin r) ℝ}
    (hY : HasOrthonormalCols Y) {θ : Fin r → ℝ}
    (hTY : ∀ i, L.toLanczosData.tridiagonal *ᵥ (fun c => Y c i) = θ i • fun c => Y c i)
    {a b g : ℝ} (hθ : ∀ i, θ i ∈ Set.Icc a b) (hg : 2 * L.backwardRadius < g)
    (hres : ∀ i, L.β k * |Y L.toLanczosData.lastIndex i| <
      (g - 2 * L.backwardRadius) / Real.sqrt r) :
    r ≤ ((Finset.range n).filter fun i => eigenvalue L.H i ∈ Set.Ioo (a - g) (b + g)).card := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have he0 : 0 ≤ L.backwardRadius := (frobNorm_nonneg E).trans hE
  have hgram := L.frobNorm_gram_sub_one_le hη hsmall (k + 1) le_rfl
  have hsq : Real.sqrt (3 * (((k + 1 : ℕ)) : ℝ)) = Real.sqrt (3 * ((k : ℝ) + 1)) := by
    push_cast; ring_nf
  rw [hsq] at hgram
  have hspec : specNorm ((basisOf L.v (k + 1))ᵀ * basisOf L.v (k + 1) - 1) ≤ 1 / 100 :=
    (specNorm_le_frobNorm _).trans (by linarith)
  have hPo := hasOrthonormalCols_polarFactor hspec (by norm_num)
  set P := polarFactor (basisOf L.v (k + 1)) with hPdef
  have hU : HasOrthonormalCols (P.submatrix id Fin.castSucc) :=
    hPo.submatrix (Equiv.refl _) (Fin.castSucc_injective _)
  have hH : L.H.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact L.transpose_H
  have hE' : E.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hEs
  have hA := hH.add hE'
  have hβ : 0 ≤ L.β k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [L.β_zero]
    · have hadm := L.admissible (k - 1) (by omega)
      have hk : k - 1 + 1 = k := by omega
      rw [hk] at hadm
      have hz := L.abs_ν_sub_le (k - 1) (by omega)
      rw [hk] at hz
      have hz' := (abs_le.mp hz).1
      have hnn : 0 ≤ ‖WithLp.toLp 2 (L.z k)‖ := norm_nonneg _
      have hε := L.ε_le
      have hε0 := L.ε_nonneg
      have hντ : 0 ≤ L.τ * L.ν k := mul_nonneg L.τ_pos.le (by nlinarith)
      linarith
  set U := P.submatrix id Fin.castSucc with hUdef
  set u : Fin n → ℝ := fun i => P i (Fin.last k) with hudef
  have hu : ‖WithLp.toLp 2 u‖ = 1 := by
    have h1 := hPo.norm_toLp_mulVec (Pi.single (Fin.last k) 1)
    have h2 : P *ᵥ Pi.single (Fin.last k) 1 = u := by
      funext i; simp [hudef]
    rw [h2] at h1
    rw [h1]
    simp
  have hres' : ∀ i, (L.H + E) *ᵥ (U *ᵥ fun c => Y c i) - θ i • (U *ᵥ fun c => Y c i) =
      (Y L.toLanczosData.lastIndex i * L.β k) • u := by
    intro i
    have hmul : (L.H + E) *ᵥ (U *ᵥ fun c => Y c i) = θ i • (U *ᵥ fun c => Y c i) +
        Matrix.vecMulVec (L.β k • u) (Pi.single L.toLanczosData.lastIndex 1) *ᵥ
          (fun c => Y c i) := by
      rw [Matrix.mulVec_mulVec, hid, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hTY i,
        Matrix.mulVec_smul]
    rw [hmul, add_sub_cancel_left]
    funext a
    simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply, hudef, mul_comm,
      mul_left_comm]
  have hX : HasOrthonormalCols (U * Y) := by
    change (U * Y)ᴴ * (U * Y) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ U Y,
      hU.conjTranspose_mul_self, Matrix.one_mul]
    exact hY
  have hd : 0 < g - L.backwardRadius := by linarith
  have hcard := card_le_card_eigenvalue_mem_of_hasOrthonormalCols hA hX hd hθ (fun i => by
    change ‖WithLp.toLp 2 ((L.H + E) *ᵥ (fun c => (U * Y) c i) - θ i • fun c => (U * Y) c i)‖ <
      (g - L.backwardRadius) / Real.sqrt r
    have hcol : (fun c => (U * Y) c i) = U *ᵥ fun c => Y c i := rfl
    have hle : (g - 2 * L.backwardRadius) / Real.sqrt r ≤ (g - L.backwardRadius) / Real.sqrt r := by
      gcongr; linarith
    rw [hcol, hres' i, WithLp.toLp_smul, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hβ, mul_comm]
    linarith [hres i])
  refine hcard.trans (Finset.card_le_card fun i hi => ?_)
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo] at hi ⊢
  have hW := abs_le.mp ((Matrix.IsHermitian.abs_eigenvalue_sub_le hA hH i).trans
    ((by rw [add_sub_cancel_left]; exact specNorm_le_frobNorm E : specNorm ((L.H + E) - L.H) ≤
      frobNorm E).trans hE))
  constructor
  · exact hi.1
  · constructor <;> linarith [hi.2.1, hi.2.2, hW.1, hW.2]

/-- **Ritz-pair residuals**: every unit eigenvector $\mathbf{y}$ of $\mathbf{T}_k$ with
eigenvalue $\theta$ gives an eigenvalue of $\mathbf{H}$ within $\beta_k|y_{k-1}| + e$.
[Paige1980] for plain Lanczos; standard. -/
theorem exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) [NeZero n] {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.toLanczosData.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    ∃ i < n, |eigenvalue L.H i - θ| ≤ L.β k * |y L.toLanczosData.lastIndex| +
      L.backwardRadius := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have hgram := L.frobNorm_gram_sub_one_le hη hsmall (k + 1) le_rfl
  have hsq : Real.sqrt (3 * (((k + 1 : ℕ)) : ℝ)) = Real.sqrt (3 * ((k : ℝ) + 1)) := by
    push_cast; ring_nf
  rw [hsq] at hgram
  have hspec : specNorm ((basisOf L.v (k + 1))ᵀ * basisOf L.v (k + 1) - 1) ≤ 1 / 100 :=
    (specNorm_le_frobNorm _).trans (by linarith)
  have hPo := hasOrthonormalCols_polarFactor hspec (by norm_num)
  set P := polarFactor (basisOf L.v (k + 1)) with hPdef
  have hU : HasOrthonormalCols (P.submatrix id Fin.castSucc) :=
    hPo.submatrix (Equiv.refl _) (Fin.castSucc_injective _)
  have hH : L.H.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact L.transpose_H
  have hE' : E.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hEs
  have hA := hH.add hE'
  have hβ : 0 ≤ L.β k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [L.β_zero]
    · have hadm := L.admissible (k - 1) (by omega)
      have hk : k - 1 + 1 = k := by omega
      rw [hk] at hadm
      have hz := L.abs_ν_sub_le (k - 1) (by omega)
      rw [hk] at hz
      have hz' := (abs_le.mp hz).1
      have hnn : 0 ≤ ‖WithLp.toLp 2 (L.z k)‖ := norm_nonneg _
      have hε := L.ε_le
      have hε0 := L.ε_nonneg
      have hντ : 0 ≤ L.τ * L.ν k := mul_nonneg L.τ_pos.le (by nlinarith)
      linarith
  set U := P.submatrix id Fin.castSucc with hUdef
  set u : Fin n → ℝ := fun i => P i (Fin.last k) with hudef
  set x := U *ᵥ y with hxdef
  have hres : (L.H + E) *ᵥ x - θ • x = (y L.toLanczosData.lastIndex * L.β k) • u := by
    have hmul : (L.H + E) *ᵥ (U *ᵥ y) = θ • (U *ᵥ y) +
        Matrix.vecMulVec (L.β k • u) (Pi.single L.toLanczosData.lastIndex 1) *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hid, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hy,
        Matrix.mulVec_smul]
    rw [hxdef, hmul, add_sub_cancel_left]
    funext i
    simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply, hudef, mul_comm,
      mul_left_comm]
  have hu : ‖WithLp.toLp 2 u‖ = 1 := by
    have h1 := hPo.norm_toLp_mulVec (Pi.single (Fin.last k) 1)
    have h2 : P *ᵥ Pi.single (Fin.last k) 1 = u := by
      funext i; simp [hudef]
    rw [h2] at h1
    rw [h1]
    simp
  have hx : ‖WithLp.toLp 2 x‖ = 1 := by
    rw [hxdef, hU.norm_toLp_mulVec]; exact hy1
  obtain ⟨i, hi, hab⟩ := Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le hA x θ
  refine ⟨i, by simpa using hi, ?_⟩
  have hW := Matrix.IsHermitian.abs_eigenvalue_sub_le hA hH i
  have hd : specNorm ((L.H + E) - L.H) ≤ frobNorm E := by
    rw [add_sub_cancel_left]; exact specNorm_le_frobNorm E
  have hr : ‖WithLp.toLp 2 ((L.H + E).mulVec x - θ • x)‖ ≤
      L.β k * |y L.toLanczosData.lastIndex| := by
    rw [hres, WithLp.toLp_smul, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hβ, mul_comm]
  rw [hx, mul_one] at hab
  linarith [abs_sub_le (eigenvalue L.H i) (eigenvalue (L.H + E) i) θ,
    abs_sub_comm (eigenvalue (L.H + E) i) (eigenvalue L.H i)]

/-- **A small last coefficient makes the computed space nearly invariant** (F3, the
non-admissible stop): if $\beta_k \le \rho$, every Ritz value is within $\rho + e$ of an
eigenvalue of $\mathbf{H}$ (with $\rho = \tau\nu_{k+1}$-type bounds when the next step fails the
criterion). [Paige1970] (the stopping criterion). -/
theorem exists_abs_eigenvalue_sub_le_of_β_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) [NeZero n] {ρ : ℝ} (hρ : L.β k ≤ ρ)
    {i : ℕ} (hi : i < k) :
    ∃ l < n, |eigenvalue L.H l - eigenvalue L.toLanczosData.tridiagonal i| ≤
      ρ + L.backwardRadius := by
  have hT : L.toLanczosData.tridiagonal.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      LanczosData.transpose_tridiagonal]
  obtain ⟨y, hy1, hy⟩ := hT.exists_norm_eq_one_and_mulVec_eq (k := i) (by simpa using hi)
  obtain ⟨l, hl, hab⟩ := L.exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul hη hsmall hrec hτ hy hy1
  refine ⟨l, hl, hab.trans ?_⟩
  have hβ : 0 ≤ L.β k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [L.β_zero]
    · have hadm := L.admissible (k - 1) (by omega)
      have hk : k - 1 + 1 = k := by omega
      rw [hk] at hadm
      have hz := L.abs_ν_sub_le (k - 1) (by omega)
      rw [hk] at hz
      have hz' := (abs_le.mp hz).1
      have hnn : 0 ≤ ‖WithLp.toLp 2 (L.z k)‖ := norm_nonneg _
      have hε := L.ε_le
      have hε0 := L.ε_nonneg
      have hντ : 0 ≤ L.τ * L.ν k := mul_nonneg L.τ_pos.le (by nlinarith)
      linarith
  have hyl : |y L.toLanczosData.lastIndex| ≤ 1 := by
    have := PiLp.norm_apply_le (WithLp.toLp 2 y) L.toLanczosData.lastIndex
    rw [hy1, Real.norm_eq_abs] at this
    exact this
  have : L.β k * |y L.toLanczosData.lastIndex| ≤ ρ :=
    (mul_le_of_le_one_right hβ hyl).trans hρ
  linarith

/-- **Containment**: every Ritz value lies in $[\lambda_{n-1}(\mathbf{H}) - e,
\lambda_0(\mathbf{H}) + e]$. [Paige1980] for plain Lanczos. -/
theorem eigenvalue_tridiagonal_mem_Icc (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.toLanczosData.tridiagonal i ∈
      Set.Icc (eigenvalue L.H (n - 1) - L.backwardRadius)
        (eigenvalue L.H 0 + L.backwardRadius) := by
  have hkn := L.succ_le_card hη hsmall
  have hH : L.H.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact L.transpose_H
  have hup := L.eigenvalue_tridiagonal_le_add hη hsmall hrec hτ hi
  have hlo := L.eigenvalue_sub_le_eigenvalue_tridiagonal hη hsmall hrec hτ hi
  have h0 := Matrix.IsHermitian.eigenvalue_le_eigenvalue hH (i := 0) (j := i)
    (Nat.zero_le _) (by simp; omega)
  have hn := Matrix.IsHermitian.eigenvalue_le_eigenvalue hH (i := i + (n - k)) (j := n - 1)
    (by omega) (by simp; omega)
  constructor
  · linarith
  · linarith

/-- **Kaniel–Paige–Saad for the backward model**: the proved bound
`Matrix.IsHermitian.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le` holds for
$(\mathbf{H} + \mathbf{E}, \mathbf{u}_1)$ with $\mathbf{T}_k$ in place of the compression, and
$\lambda_0(\mathbf{H} + \mathbf{E})$ is within $e$ of $\lambda_0(\mathbf{H})$. Stating the tangent
in
$\mathbf{H}$'s data needs Davis–Kahan (later). [Saad2011, Theorem 6.4] for the exact bound. -/
theorem exists_backward_kaniel_paige_saad (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ frobNorm E ≤ L.backwardRadius ∧
      |eigenvalue (L.H + E) 0 - eigenvalue L.H 0| ≤ L.backwardRadius ∧
      ∀ {a c : ℝ}, a < c → c < eigenvalue (L.H + E) 0 →
        spectrum ℝ (L.H + E) ⊆ Set.Icc a c ∪ {eigenvalue (L.H + E) 0} →
        0 < (spectralMeasure (L.H + E)
          (colSeq (polarFactor (basisOf L.v (k + 1))) 1)).real {eigenvalue (L.H + E) 0} →
        eigenvalue (L.H + E) 0 - eigenvalue L.toLanczosData.tridiagonal 0 ≤
          4 * (eigenvalue (L.H + E) 0 - a) *
            spectralTangentSq (L.H + E) (colSeq (polarFactor (basisOf L.v (k + 1))) 1)
              (eigenvalue (L.H + E) 0) *
            ((Real.sqrt (eigenvalue (L.H + E) 0 - a) - Real.sqrt (eigenvalue (L.H + E) 0 - c)) /
              (Real.sqrt (eigenvalue (L.H + E) 0 - a) +
                Real.sqrt (eigenvalue (L.H + E) 0 - c))) ^ (2 * (k - 1)) := by
  obtain ⟨E, hEt, hEf, hst, hT, -⟩ := L.exists_lanczosState_backward hη hsmall hrec hτ
  set U := polarFactor (basisOf L.v (k + 1))
  have hM : (L.H + E).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_add,
      L.transpose_H, hEt]
  -- the polar factor is orthonormal, so are the first `k` Lanczos vectors
  have hU : HasOrthonormalCols U := by
    refine hasOrthonormalCols_polarFactor_iff.mpr
      (injective_mulVec_of_specNorm_gram_sub_one_lt_one ((specNorm_le_frobNorm _).trans_lt
        ((L.frobNorm_gram_sub_one_le hη hsmall (k + 1) le_rfl).trans_lt ?_)))
    push_cast
    linarith
  have hQ : HasOrthonormalCols (arnoldiMatrix (L.H + E) (colSeq U 1) k) := by
    rw [← hM.lanczosMatrix_eq_arnoldiMatrix]
    have hQU : lanczosMatrix (L.H + E) (colSeq U 1) k =
        U.submatrix (Equiv.refl _) Fin.castSucc := by
      ext i j
      simp only [lanczosMatrix, Matrix.of_apply, hst j j.isLt, colSeq, Matrix.submatrix_apply,
        Equiv.refl_apply]
      rw [dif_pos (by omega)]
      rfl
    rw [hQU]
    exact hU.submatrix _ (Fin.castSucc_injective _)
  refine ⟨E, hEt, hEf, ?_, fun {a c} hac hc hs hb => ?_⟩
  · have hH : L.H.IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, L.transpose_H]
    refine (hM.abs_eigenvalue_sub_le hH 0).trans ?_
    rw [add_sub_cancel_left]
    exact (specNorm_le_frobNorm E).trans hEf
  · have hK : LinearMap.range (arnoldiMatrix (L.H + E) (colSeq U 1) k).mulVecLin =
        krylovSpace (L.H + E) (colSeq U 1) (k - 1 + 1) := by
      rw [range_arnoldiMatrix, Nat.sub_add_cancel L.k_pos]
    have h := hM.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le hac hc hs hb hQ hK
    rwa [← hM.lanczosTridiagonal_eq, hT] at h

/-- Powers of degree below $2m$ pass to the compression onto an orthonormal basis of
$\mathcal K_m(\mathbf{A}, \mathbf{b})$, for symmetric $\mathbf{A}$. -/
private theorem dotProduct_pow_mulVec_eq_compression {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {b : Fin n → ℝ} {Q : Matrix (Fin n) (Fin m) ℝ} (hQ : HasOrthonormalCols Q)
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b m) {j : ℕ} (hj : j < 2 * m) :
    b ⬝ᵥ (A ^ j *ᵥ b) = (Qᵀ *ᵥ b) ⬝ᵥ ((Qᵀ * A * Q) ^ j *ᵥ (Qᵀ *ᵥ b)) := by
  have hQQ : Qᵀ * Q = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQ
  have hproj : ∀ i < m, Q *ᵥ (Qᵀ *ᵥ (A ^ i *ᵥ b)) = A ^ i *ᵥ b := fun i hi => by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hK ▸ pow_mulVec_mem_krylovSpace A b hi)
    rw [Matrix.mulVecLin_apply] at hy
    rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hpow : ∀ i ≤ m, Qᵀ *ᵥ (A ^ i *ᵥ b) = (Qᵀ * A * Q) ^ i *ᵥ (Qᵀ *ᵥ b) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ← hproj i (by omega), ih (by omega), pow_succ',
        ← Matrix.mulVec_mulVec (Qᵀ *ᵥ b)]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hdot : ∀ {l : ℕ} (M : Matrix (Fin l) (Fin l) ℝ), Mᵀ = M → ∀ a c (x : Fin l → ℝ),
      x ⬝ᵥ (M ^ (a + c) *ᵥ x) = (M ^ a *ᵥ x) ⬝ᵥ (M ^ c *ᵥ x) := fun M hM a c x => by
    rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_pow, hM]
  have hC : (Qᵀ * A * Q)ᵀ = Qᵀ * A * Q := by
    simp only [Matrix.transpose_mul, hA, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨a, c, rfl, ha, hc⟩ : ∃ a c, j = a + c ∧ a < m ∧ c ≤ m :=
    ⟨j - min j m, min j m, by omega, by omega, by omega⟩
  rw [hdot A hA, hdot _ hC, ← hproj a ha, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, hpow a ha.le, hpow c hc]

/-- Polynomials of degree below $2m$ pass to the compression onto an orthonormal basis of
$\mathcal K_m(\mathbf{A}, \mathbf{b})$, for symmetric $\mathbf{A}$. -/
private theorem dotProduct_aeval_mulVec_eq_compression {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {b : Fin n → ℝ} {Q : Matrix (Fin n) (Fin m) ℝ} (hQ : HasOrthonormalCols Q)
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b m) {p : Polynomial ℝ}
    (hp : p.natDegree < 2 * m) :
    b ⬝ᵥ (Polynomial.aeval A p *ᵥ b) =
      (Qᵀ *ᵥ b) ⬝ᵥ (Polynomial.aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b)) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec,
    Matrix.sum_mulVec, dotProduct_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
    dotProduct_pow_mulVec_eq_compression hA hQ hK (by have := Finset.mem_range.mp hi; omega)]

/-- **Gauss quadrature on the backward model**: with $\mathbf{H}'$ from
`NLAlib.LanczosReorthRun.exists_pure_backward`, $\|\mathbf{b}\|^2\,[p(\mathbf{T}_k)]_{00} =
\mathbf{b}^{\mathsf{T}}p(\mathbf{H}')\mathbf{b}$ for every polynomial of degree at most $2k - 1$:
the computed tridiagonal is the Gauss rule of the spectral measure of $(\mathbf{H}', \mathbf{b})$.
[GolubMeurant2010, Theorem 6.6] (locator to verify). -/
theorem exists_pure_backward_gauss (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {b : Fin n → ℝ} (hb : b ≠ 0) {δb : ℝ}
    (hδ : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ δb) :
    ∃ H' : Matrix (Fin n) (Fin n) ℝ, H'ᵀ = H' ∧
      frobNorm (H' - L.H) ≤ L.backwardRadius +
        3 * specNorm L.H * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * k - 1 →
        ‖WithLp.toLp 2 b‖ ^ 2 *
            (Polynomial.aeval L.toLanczosData.tridiagonal p) ⟨0, L.k_pos⟩ ⟨0, L.k_pos⟩ =
          b ⬝ᵥ (Polynomial.aeval H' p *ᵥ b) := by
  obtain ⟨H', hH't, hbd, hT⟩ := L.exists_pure_backward hη hsmall hrec hτ hb hδ
  refine ⟨H', hH't, hbd, fun p hp => ?_⟩
  have hA : H'.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hH't]
  obtain ⟨q, hq⟩ : ∃ q, k = q + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos L.k_pos).symm⟩
  subst hq
  -- the grade is at least `k`: `b ≠ 0`, and `β_j > 0` is an entry of the tridiagonal
  have hgr : q + 1 ≤ krylovGrade H' b := by
    rcases q with _ | q
    · by_contra h
      have h0 := krylovGrade_le_iff.mp (by omega : krylovGrade H' b ≤ 0)
      rw [krylovSpace_zero, pow_zero, Matrix.one_mulVec, Submodule.mem_bot] at h0
      exact hb h0
    · have hβ : (lanczosState H' b (q + 1)).beta = L.β (q + 1) := by
        have h := congrFun (congrFun hT ⟨q + 1, by omega⟩) ⟨q, by omega⟩
        simpa [lanczosTridiagonal, LanczosData.tridiagonal, toLanczosData] using h
      have hν : 0 ≤ L.ν (q + 1) := by
        have h2 := L.abs_ν_sub_le q (by omega)
        nlinarith [abs_le.mp h2, L.ε_le, norm_nonneg (WithLp.toLp 2 (L.z (q + 1)))]
      have hpos : 0 < L.β (q + 1) := by
        nlinarith [L.admissible q (by omega), mul_nonneg L.τ_pos.le hν]
      by_contra h
      exact hpos.ne' (hβ ▸ (hA.lanczosState_beta_eq_zero_iff b q).mpr (by omega))
  set Q := arnoldiMatrix H' b (q + 1)
  have hTQ : L.toLanczosData.tridiagonal = Qᵀ * H' * Q := by
    rw [← hT, hA.lanczosTridiagonal_eq, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hQb : Qᵀ *ᵥ b = ‖WithLp.toLp 2 b‖ • Pi.single 0 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    simpa using conjTranspose_arnoldiMatrix_mulVec_self H' b q
  -- both sides are quadratic forms of the compression `T = Qᵀ H' Q`
  rw [dotProduct_aeval_mulVec_eq_compression hH't (hasOrthonormalCols_arnoldiMatrix_iff.mpr hgr)
    (range_arnoldiMatrix _ _ _) (by omega), ← hTQ, hQb]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, Matrix.mulVec_single_one,
    single_one_dotProduct, Matrix.col_apply, smul_eq_mul, Fin.zero_eta]
  ring

/-- **Transfer to $\mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}$**: with $\mathbf{H}'$
as
in `NLAlib.LanczosReorthRun.exists_pure_backward_gauss`, for every $1$-Lipschitz $f$,
$|\mathbf{b}^{\mathsf{T}}f(\mathbf{H}')\mathbf{b} - \mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}|
\le \|\mathbf{b}\|^2\|\mathbf{H}' - \mathbf{H}\|_{\mathsf F}$, so the exact quadrature error theory
for $(\mathbf{H}', \mathbf{b})$ transfers with that additive term. [Kittaneh1985]. -/
theorem exists_pure_backward_abs_quadForm_cfc_sub_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {b : Fin n → ℝ} (hb : b ≠ 0) {δb : ℝ}
    (hδ : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ δb) :
    ∃ H' : Matrix (Fin n) (Fin n) ℝ, H'ᵀ = H' ∧
      frobNorm (H' - L.H) ≤ L.backwardRadius +
        3 * specNorm L.H * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) ∧
      lanczosTridiagonal H' b k = L.toLanczosData.tridiagonal ∧
      ∀ f : ℝ → ℝ, LipschitzWith 1 f →
        |b ⬝ᵥ (cfc f H' *ᵥ b) - b ⬝ᵥ (cfc f L.H *ᵥ b)| ≤
          ‖WithLp.toLp 2 b‖ ^ 2 * frobNorm (H' - L.H) := by
  obtain ⟨H', hH'T, hfrob, htri⟩ := L.exists_pure_backward hη hsmall hrec hτ hb hδ
  have hH' : H'.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hH'T]
  refine ⟨H', hH'T, hfrob, htri, fun f hf => ?_⟩
  have hH : L.H.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, L.transpose_H]
  have h := norm_star_dotProduct_mulVec_le (cfc f H' - cfc f L.H) b b
  have hc := hH'.frobNorm_cfc_sub_cfc_le hH hf
  have e : b ⬝ᵥ (cfc f H' *ᵥ b) - b ⬝ᵥ (cfc f L.H *ᵥ b) =
      b ⬝ᵥ ((cfc f H' - cfc f L.H) *ᵥ b) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [e, ← Real.norm_eq_abs]
  rw [star_trivial] at h
  calc ‖b ⬝ᵥ ((cfc f H' - cfc f L.H) *ᵥ b)‖
      ≤ ‖WithLp.toLp 2 b‖ * specNorm (cfc f H' - cfc f L.H) * ‖WithLp.toLp 2 b‖ := h
    _ ≤ ‖WithLp.toLp 2 b‖ * frobNorm (cfc f H' - cfc f L.H) * ‖WithLp.toLp 2 b‖ := by
        gcongr; exact specNorm_le_frobNorm _
    _ ≤ ‖WithLp.toLp 2 b‖ * frobNorm (H' - L.H) * ‖WithLp.toLp 2 b‖ := by gcongr
    _ = ‖WithLp.toLp 2 b‖ ^ 2 * frobNorm (H' - L.H) := by ring

end LanczosReorthRun

end NLAlib
