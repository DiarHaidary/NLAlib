/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Matrix.QRIteration.Ritz

/-!
# Forward-approximate Ritz values are optimal or decouple early (scaffold)

Statements for a new `NLAlib/Matrix/QRIteration/Dichotomy.lean` (stage SHIFTED-QR, wave W3,
design note `docs/design/Eigensolvers-ShiftedQR.md` §3.7): the exact-arithmetic dichotomy of
[BanksGarzaVargasSrivastava2022, §4.1]. If shifts within $\beta$ of the Ritz values fail to be
$\theta$-optimal, then one of them is close to an eigenvalue of large last-row weight, and the
degree $k$ step with that shift has a large $\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} -
r\mathbf{I})^{-k}\|$ (it decouples early). It is the bridge from the forward-approximate Ritz
values a small eigensolver computes to the $\theta$-optimal ones the strategy needs; no
arithmetic model is involved.

## Main results

* `NLAlib.sum_lastRowWeights_mul_norm_eval_sq_sub_le`: perturbing roots raises the weighted
  second moment only through weight near the roots.
* `NLAlib.IsUpperHessenberg.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le`: the dichotomy.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- An eigenvalue of the diagonalization is at most the spectral norm. -/
private theorem norm_le_specNorm_of_mul_eq_mul_diagonal
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (i : Fin (n + 1)) : ‖d i‖ ≤ specNorm H := by
  set x := V *ᵥ Pi.single i 1
  have hx : H *ᵥ x = d i • x := by
    rw [Matrix.mulVec_mulVec, hHV, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, Pi.single_eq_of_ne h]
  have hx0 : WithLp.toLp 2 x ≠ 0 := by
    intro h0
    have h1 : x = V *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      exact congrArg WithLp.ofLp h0
    have := congrFun (Matrix.mulVec_injective_iff_isUnit.mpr hV h1) i
    simp at this
  have h := norm_toLp_mulVec_le H x
  rw [hx, WithLp.toLp_smul, norm_smul] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hx0)

/-- The modulus of the shift polynomial is the product of the distances to the shifts. -/
private theorem norm_eval_shiftPoly (ss : List ℂ) (z : ℂ) :
    ‖(shiftPoly ss).eval z‖ = (ss.map fun s => ‖z - s‖).prod := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons a l ih =>
    simp only [shiftPoly, List.map_cons, List.prod_cons, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_mul] at ih ⊢
    rw [ih]

/-- Perturbing the shifts one by one: if each perturbed factor is at most $C f(s)$, the perturbed
shift polynomial is at most $C^k\prod f(s)$. -/
private theorem norm_eval_shiftPoly_le_of_forall₂ {β C : ℝ} (hC : 0 ≤ C) {f : ℂ → ℝ}
    (hf : ∀ s, 0 ≤ f s) {z : ℂ} {ss ss' : List ℂ}
    (h : List.Forall₂ (fun s s' => ‖s - s'‖ ≤ β) ss ss')
    (hpt : ∀ s ∈ ss, ∀ s', ‖s - s'‖ ≤ β → ‖z - s'‖ ≤ C * f s) :
    ‖(shiftPoly ss').eval z‖ ≤ C ^ ss.length * (ss.map f).prod := by
  induction h with
  | nil => simp [shiftPoly]
  | @cons a b l₁ l₂ hab _ ih =>
    have ih' := ih (fun s hs => hpt s (List.mem_cons_of_mem _ hs))
    have hp : 0 ≤ (l₁.map f).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
        exact hf s
    simp only [shiftPoly, List.map_cons, List.prod_cons, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_mul,
      List.length_cons] at ih' ⊢
    calc ‖z - b‖ * ‖Polynomial.eval z (l₂.map fun s => Polynomial.X - Polynomial.C s).prod‖
        ≤ (C * f a) * (C ^ l₁.length * (l₁.map f).prod) :=
          mul_le_mul (hpt a List.mem_cons_self b hab) ih' (norm_nonneg _)
            (mul_nonneg hC (hf a))
      _ = C ^ (l₁.length + 1) * (f a * (l₁.map f).prod) := by ring

/-- **Instability implies support**: let $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$ with $\mathbf{V}$ invertible and last-row weights $w$, the eigenvalues separated by
$\lvert\mathbf{d}_i - \mathbf{d}_j\rvert \ge \Gamma$ for $i \ne j$; let $c > 0$,
$0 \le \beta \le c\Gamma$, and let `ss`, `ss'` be lists of $k$ shifts with
$\lvert s_i - s_i'\rvert \le \beta$ and $\lvert s_i\rvert \le \|\mathbf{H}\|_2$. With
$q = \prod_i (z - s_i)$, $q' = \prod_i (z - s_i')$,
$$\sum_i w_i\lvert q'(\mathbf{d}_i)\rvert^2 - (1 + 2c)^{2k}\sum_i w_i\lvert q(\mathbf{d}_i)
\rvert^2 \le \bigl(2(\|\mathbf{H}\|_2 + \beta)(1 + 2c)\bigr)^{2k}\sum_{i\,:\,\exists s \in
\mathrm{ss},\ \lvert\mathbf{d}_i - s\rvert \le \beta/(2c)} w_i\,.$$
[BanksGarzaVargasSrivastava2022, Lemma 4.2].
Proof: the paper's: group the shifts by their nearest eigenvalue (`Finset.exists_min_image`),
exchange $s_i$ for $s_i'$ one group at a time (Claim 4.4 there): at an eigenvalue other than the
group's, each exchanged factor grows by at most $1 + 2\beta/\Gamma \le 1 + 2c$ (the eigenvalue is
at distance $\ge \Gamma/2$ from the shift); at the group's eigenvalue, either it is farther
than $\beta/(2c)$ from the group (factor $\le 1 + 2c$ again) or the whole term is at most
$(2(\|\mathbf{H}\|_2 + \beta))^{2k}w_j$ ($\lvert\mathbf{d}_j\rvert \le \|\mathbf{H}\|_2$ by
`spectrum.norm_le_norm_of_mem`); induction over the groups. L, about 120 lines (the claim as a
private lemma). -/
theorem sum_lastRowWeights_mul_norm_eval_sq_sub_le {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {Γ c β : ℝ}
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hc : 0 < c) (hβ : 0 ≤ β) (hβc : β ≤ c * Γ)
    {ss ss' : List ℂ} (hclose : List.Forall₂ (fun s s' => ‖s - s'‖ ≤ β) ss ss')
    (hss : ∀ s ∈ ss, ‖s‖ ≤ specNorm H) :
    ∑ i, lastRowWeights V i * ‖(shiftPoly ss').eval (d i)‖ ^ 2 -
        (1 + 2 * c) ^ (2 * ss.length) * ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2 ≤
      (2 * (specNorm H + β) * (1 + 2 * c)) ^ (2 * ss.length) *
        ∑ i ∈ Finset.univ.filter (fun i => ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c)),
          lastRowWeights V i := by
  set K := ss.length
  set M := 2 * (specNorm H + β)
  have hc1 : 1 ≤ (1 + 2 * c) ^ (2 * K) := one_le_pow₀ (by linarith)
  have hM : 0 ≤ M := by have := specNorm_nonneg H; positivity
  have hpt : ∀ i, lastRowWeights V i * ‖(shiftPoly ss').eval (d i)‖ ^ 2 ≤
      (1 + 2 * c) ^ (2 * K) * (lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2) +
        if ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c) then
          (M * (1 + 2 * c)) ^ (2 * K) * lastRowWeights V i else 0 := by
    intro i
    have hw := lastRowWeights_nonneg V i
    split_ifs with hS
    · have hle := norm_eval_shiftPoly_le_of_forall₂ hM (f := fun _ => 1) (fun _ => zero_le_one)
        (z := d i) hclose fun s hs s' hss' => by
          have h1 := norm_le_specNorm_of_mul_eq_mul_diagonal hV hHV i
          have h2 := hss s hs
          have h3 : ‖s'‖ ≤ ‖s‖ + β := by
            have := norm_sub_norm_le s' s
            rw [norm_sub_rev] at this
            linarith
          have h4 := norm_sub_le (d i) s'
          simp only [M, mul_one]
          linarith
      simp only [List.map_const', List.prod_replicate, one_pow, mul_one] at hle
      have hsq : ‖(shiftPoly ss').eval (d i)‖ ^ 2 ≤ M ^ (2 * K) := by
        rw [pow_mul']
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      have hMc : M ^ (2 * K) ≤ (M * (1 + 2 * c)) ^ (2 * K) := by
        rw [mul_pow M (1 + 2 * c)]
        exact le_mul_of_one_le_right (by positivity) hc1
      have := mul_le_mul_of_nonneg_left (hsq.trans hMc) hw
      have : 0 ≤ (1 + 2 * c) ^ (2 * K) * (lastRowWeights V i *
          ‖(shiftPoly ss).eval (d i)‖ ^ 2) := by positivity
      linarith
    · push Not at hS
      have hle := norm_eval_shiftPoly_le_of_forall₂ (by linarith : (0 : ℝ) ≤ 1 + 2 * c)
        (f := fun s => ‖d i - s‖) (fun _ => norm_nonneg _) (z := d i) hclose
        fun s hs s' hss' => by
          have h1 := hS s hs
          have h2 : β ≤ 2 * c * ‖d i - s‖ := by
            rw [div_lt_iff₀ (by positivity)] at h1
            linarith
          have h3 : ‖d i - s'‖ ≤ ‖d i - s‖ + ‖s - s'‖ := by
            rw [← sub_add_sub_cancel (d i) s s']
            exact norm_add_le _ _
          nlinarith
      rw [← norm_eval_shiftPoly] at hle
      have hsq : ‖(shiftPoly ss').eval (d i)‖ ^ 2 ≤
          (1 + 2 * c) ^ (2 * K) * ‖(shiftPoly ss).eval (d i)‖ ^ 2 := by
        rw [pow_mul', ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      have := mul_le_mul_of_nonneg_left hsq hw
      linarith
  calc ∑ i, lastRowWeights V i * ‖(shiftPoly ss').eval (d i)‖ ^ 2 -
        (1 + 2 * c) ^ (2 * K) * ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2
      ≤ ∑ i, (if ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c) then
          (M * (1 + 2 * c)) ^ (2 * K) * lastRowWeights V i else 0) := by
        rw [Finset.mul_sum, sub_le_iff_le_add, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => (hpt i).trans_eq (add_comm _ _)
    _ = _ := by rw [← Finset.sum_filter, Finset.mul_sum]

/-- **The dichotomy for forward-approximate Ritz values**: let $\mathbf{H}$ be upper Hessenberg
with $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible,
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$, eigenvalues separated by $\Gamma$; let
$1 \le k \le n$, $x = (2\kappa^4)^{1/(2k)} < \theta$, $c = \tfrac12(\theta/x - 1)$,
$0 < \beta < c\Gamma$, and let `rs` be within $\beta$ of the Ritz values of order $k$, entry by
entry. Then `rs` is a set of $\theta$-optimal Ritz values, or some $r$ in `rs` is an eigenvalue,
or
$$\tfrac25\,\psi_k(\mathbf{H})\Bigl(1 - \frac x\theta\Bigr) \le \kappa^{2/k}(\|\mathbf{H}\|_2 +
\beta)\,\beta\,\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|^{1/k}$$
for some $r$ in `rs`. [BanksGarzaVargasSrivastava2022, Theorem 4.1], there with $\tfrac12$ for
$\tfrac25$ (a factor $k^{-1/(2k)}/2 \ge 2/5$ is lost in its last display; gap G10) and
$\beta \le c\Gamma$ (which can let two eigenvalues share a Ritz value).
Proof: if `rs` is not optimal, $\sum_i w_i\lvert p(\mathbf{d}_i)\rvert^2 \ge
2(1 + 2c)^{2k}\sum_i w_i\lvert\chi_k(\mathbf{d}_i)\rvert^2$
(`NLAlib.sum_lastRowWeights_mul_sq_le`, `NLAlib.norm_mul_diagonal_mul_inv_last_sq_le`,
`NLAlib.IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq`, the shift polynomial of
`NLAlib.ritzValues` is $\chi_k$); `NLAlib.sum_lastRowWeights_mul_norm_eval_sq_sub_le` (with
`NLAlib.norm_le_specNorm_of_mem_ritzValues`) gives weight $\ge \psi^{2k}/(\kappa^2(2(\|\mathbf{H}
\|_2 + \beta))^{2k})$ within $\beta/(2c)$ of the Ritz values; each Ritz value has at most one
eigenvalue that close ($\beta/c < \Gamma$), so one eigenvalue $\mathbf{d}_j$ carries $1/k$ of it
and is within $\beta(1 + 1/(2c))$ of some $r_i$; then `NLAlib.sum_lastRowWeights_mul_sq_le` for
$(\mathbf{H} - r_i\mathbf{I})^{-k}$ and $k^{-1/(2k)} \ge 4/5$. L, about 90 lines (pigeonhole over
the $k$ Ritz values with the `List.Forall₂` bookkeeping).
Result: shifted-qr-ritz-dichotomy -/
theorem IsUpperHessenberg.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {Γ θ β : ℝ} (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖)
    (hθ : (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) < θ) (hβ : 0 < β)
    (hβΓ : β < (θ / (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) - 1) / 2 * Γ)
    {rs : List ℂ} (hclose : List.Forall₂ (fun ρ r => ‖ρ - r‖ ≤ β) (ritzValues k H) rs) :
    IsOptimalRitzValues θ H rs ∨ ∃ r ∈ rs,
      (H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0 ∨
        2 / 5 * hessenbergPotential k H *
            (1 - (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) / θ) ≤
          pseudoConditionNumber V ^ ((2 : ℝ) / k) * (specNorm H + β) * β *
            ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
              (Fin.last n))‖ ^ ((k : ℝ)⁻¹) := by
  sorry

end NLAlib
