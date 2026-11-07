/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.Strategy
public import NLAlibScaffold.Matrix.QRIteration.Ritz

/-!
# Global convergence of $\mathrm{Sh}_{k,B}$ in exact arithmetic (scaffold)

Statements for `NLAlib/Matrix/QRIteration/Strategy.lean` (stage SHIFTED-QR, waves W2–W4, design
note `docs/design/Eigensolvers-ShiftedQR.md` §3.5–§3.6): stagnation of a promising shift forces
the last-row weights onto a disk ([BanksGarzaVargasSrivastava2021, Lemma 4.6]), so some
exceptional shift on a grid over that disk succeeds (Lemma 4.7 there); hence every iteration of
$\mathrm{Sh}_{k,B}$ decouples exactly or reduces the potential by $1 - \gamma$, and the iteration
$\delta$-decouples within $\lceil\log(1/\delta)/\log(1/(1 - \gamma))\rceil$ steps on every
diagonalizable Hessenberg matrix with $\kappa_V \le B$ (Theorem 1.6 there), with the normal case
(Theorem 1.2 there) as a corollary.

## Main results

* `NLAlib.IsOptimalRitzValues.sq_mul_pow_le_mul_sum_lastRowWeights_filter`: stagnation implies
  support.
* `NLAlib.exists_mem_squareGrid_norm_sub_le`, `NLAlib.length_squareGrid_le`,
  `NLAlib.norm_sub_le_of_mem_squareGrid`: the grid.
* `NLAlib.IsOptimalRitzValues.exists_mem_squareGrid_det_eq_zero_or_one_le`: an exceptional shift
  succeeds.
* `NLAlib.IsUpperHessenberg.isDecoupled_zero_shqrStep_or_hessenbergPotential_le`: one iteration.
* `NLAlib.IsUpperHessenberg.exists_le_isDecoupled_shqrIterate`: rapid decoupling.
* `NLAlib.length_shqrCandidates_le`, `NLAlib.exceptionalSpacing_ge`: the number of shifts tried.
* `IsStarNormal.exists_le_isDecoupled_shqrIterate_ritzValues`: normal matrices.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-! ### Stagnation implies support -/

/-- **Stagnation implies support**: let $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$ with $\mathbf{V}$ invertible, $\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ and
last-row weights $w$; let the $k$ shifts `ss` be $\theta$-optimal Ritz values of $\mathbf{H}$,
none an eigenvalue, $r$ an $\alpha$-promising member, $\alpha, \theta \ge 0$, and
$\psi = \psi_k(\mathbf{H}) > 0$. If the shift $(z - r)^k$ stagnates with ratio $\xi > 0$,
$\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|\,(\xi\psi)^k \le 1$ (that is
$\tau_{(z-r)^k}(\mathbf{H}) \ge \xi\psi$), then for $0 < t < 1$
$$(1 - t)^2\xi^{2k} \le \kappa^4(\alpha\theta)^{2k}\sum_{i\,:\,\lvert\mathbf{d}_i - r\rvert \le
\alpha\theta(\kappa/t)^{1/k}\psi} w_i\,.$$
[BanksGarzaVargasSrivastava2021, Lemma 4.6], with the weaker stagnation hypothesis of
[BanksGarzaVargasSrivastava2022, (2.2)] in place of $\psi_k(\widehat{\mathbf{H}}) \ge
(1 - \gamma)\psi$ (which implies it by
`NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le`).
Proof: with $X_i = \lvert\mathbf{d}_i - r\rvert^{-k}$: $\mathbb{E}X^2 \le \kappa^2(\xi\psi)^{-2k}$
(`NLAlib.sum_lastRowWeights_mul_sq_le` with `NLAlib.inv_aeval_eq_mul_diagonal_mul_inv`,
`NLAlib.mul_diagonal_mul_inv_pow` for $(z - r)^k$), $\mathbb{E}X \ge
\kappa^{-1}(\alpha\theta\psi)^{-k}$
(`NLAlib.IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div`),
and Paley–Zygmund (`Finset.sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter`); the event
$X_i > t\,\mathbb{E}X$ lies in the disk (`Real.rpow_le_rpow_left_iff`,
`Finset.sum_le_sum_of_subset`).
M, about 60 lines. -/
theorem IsOptimalRitzValues.sq_mul_pow_le_mul_sum_lastRowWeights_filter {θ α ξ t : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    (hss : IsOptimalRitzValues θ H ss) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hd : ∀ i, ∀ s ∈ ss, d i ≠ s) (hr : IsPromisingRitzValue α V d ss r) (hα : 0 ≤ α)
    (hθ : 0 ≤ θ) (hξ : 0 < ξ) (ht0 : 0 < t) (ht1 : t < 1)
    (hψ : 0 < hessenbergPotential ss.length H)
    (hstag : ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^
        ss.length) (Fin.last n))‖ * (ξ * hessenbergPotential ss.length H) ^ ss.length ≤ 1) :
    (1 - t) ^ 2 * ξ ^ (2 * ss.length) ≤
      pseudoConditionNumber V ^ 4 * (α * θ) ^ (2 * ss.length) *
        ∑ i ∈ Finset.univ.filter (fun i => ‖d i - r‖ ≤ α * θ *
          (pseudoConditionNumber V / t) ^ ((ss.length : ℝ)⁻¹) *
            hessenbergPotential ss.length H), lastRowWeights V i := by
  sorry

/-! ### The grid of exceptional shifts -/

/-- **The square grid covers the disk**: for $R \ge 0$, $\varepsilon > 0$ and
$\lvert z - c\rvert \le R$, some point $s$ of `NLAlib.squareGrid` $c$ $R$ $\varepsilon$ has
$\lvert z - s\rvert \le \varepsilon R$.
Proof: with $m = \lceil\sqrt2/\varepsilon\rceil \ge 1$, round the real and imaginary parts of
$(z - c)/R$ (in $[-1, 1]$) to the grid $2i/m - 1$ (`Nat.floor`, `round`); each coordinate errs by
at most $1/m$, so $\lvert z - s\rvert \le \sqrt2R/m \le \varepsilon R$ (`Complex.abs_apply`,
`Nat.le_ceil`); the case $R = 0$ is the centre. M, about 50 lines. -/
theorem exists_mem_squareGrid_norm_sub_le {c z : ℂ} {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hz : ‖z - c‖ ≤ R) : ∃ s ∈ squareGrid c R ε, ‖z - s‖ ≤ ε * R := by
  rcases hR.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨c, ?_, by simpa using hz⟩
    unfold squareGrid
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨0, Nat.succ_pos _, 0, Nat.succ_pos _, by simp⟩
  set m : ℕ := ⌈Real.sqrt 2 / ε⌉₊ with hm_def
  have hs0 : 0 < Real.sqrt 2 / ε := by positivity
  have hmR : Real.sqrt 2 / ε ≤ (m : ℝ) := Nat.le_ceil _
  have hm_pos : (0 : ℝ) < m := lt_of_lt_of_le hs0 hmR
  have hsε : Real.sqrt 2 ≤ (m : ℝ) * ε := by rwa [div_le_iff₀ hε] at hmR
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- rounding one coordinate of a point of the disk to the grid
  have hround : ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
      ∃ i : ℕ, i < m + 1 ∧ |2 * (i : ℝ) / m - 1 - x| ≤ 1 / m := by
    intro x hx1 hx2
    have hnn : 0 ≤ (x + 1) * m / 2 + 1 / 2 := by nlinarith
    have h1 := Nat.floor_le hnn
    have h2 := Nat.lt_floor_add_one ((x + 1) * m / 2 + 1 / 2)
    refine ⟨⌊(x + 1) * m / 2 + 1 / 2⌋₊, ?_, ?_⟩
    · have h3 : ((⌊(x + 1) * m / 2 + 1 / 2⌋₊ : ℕ) : ℝ) < m + 1 := by nlinarith
      exact_mod_cast h3
    · set i : ℝ := (⌊(x + 1) * m / 2 + 1 / 2⌋₊ : ℝ)
      have e : 2 * i / m - 1 - x = (2 * i - (x + 1) * m) / m := by field_simp; ring
      rw [e, abs_div, abs_of_pos hm_pos, div_le_div_iff_of_pos_right hm_pos, abs_le]
      constructor <;> linarith
  -- the normalised point and its coordinates lie in the square
  set w : ℂ := (z - c) / R with hw_def
  have hwn : ‖w‖ ≤ 1 := by
    rw [hw_def, norm_div, Complex.norm_real, Real.norm_of_nonneg hR, div_le_one hpos]
    exact hz
  have hwre := abs_le.mp ((Complex.abs_re_le_norm w).trans hwn)
  have hwim := abs_le.mp ((Complex.abs_im_le_norm w).trans hwn)
  obtain ⟨i, hi, hia⟩ := hround w.re hwre.1 hwre.2
  obtain ⟨j, hj, hjb⟩ := hround w.im hwim.1 hwim.2
  refine ⟨c + (R : ℂ) * ⟨2 * (i : ℝ) / m - 1, 2 * (j : ℝ) / m - 1⟩, ?_, ?_⟩
  · unfold squareGrid
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨i, hi, j, hj, rfl⟩
  have hdiff : z - (c + (R : ℂ) * ⟨2 * (i : ℝ) / m - 1, 2 * (j : ℝ) / m - 1⟩) =
      (R : ℂ) * (w - ⟨2 * (i : ℝ) / m - 1, 2 * (j : ℝ) / m - 1⟩) := by
    rw [hw_def]; field_simp; ring
  have hu : ‖w - ⟨2 * (i : ℝ) / m - 1, 2 * (j : ℝ) / m - 1⟩‖ ≤ Real.sqrt 2 * (1 / m) := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    have hA := abs_le.mp hia
    have hB := abs_le.mp hjb
    have ha2 : (w.re - (2 * (i : ℝ) / m - 1)) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 :=
      sq_le_sq' (by linarith [hA.1, hA.2]) (by linarith [hA.1, hA.2])
    have hb2 : (w.im - (2 * (j : ℝ) / m - 1)) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 :=
      sq_le_sq' (by linarith [hB.1, hB.2]) (by linarith [hB.1, hB.2])
    have hR2 : (Real.sqrt 2 * (1 / m)) ^ 2 = 2 * (1 / m) ^ 2 := by rw [mul_pow, hsq]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [ha2, hb2, hR2]
  have hεm : Real.sqrt 2 * (1 / m) ≤ ε := by
    rw [mul_one_div, div_le_iff₀ hm_pos]; linarith
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR]
  nlinarith [mul_le_mul_of_nonneg_left hu hR, mul_le_mul_of_nonneg_left hεm hR]

/-- **The size of the square grid**: for $0 < \varepsilon \le 1$, `NLAlib.squareGrid` $c$ $R$
$\varepsilon$ has at most $12/\varepsilon^2$ points.
Proof: $(m + 1)^2$ points with $m = \lceil\sqrt2/\varepsilon\rceil < \sqrt2/\varepsilon + 1$
(`List.length_flatMap`, `List.length_range`, `Nat.ceil_lt_add_one`), and
$(\sqrt2/\varepsilon + 2)^2 \le (\sqrt2 + 2)^2/\varepsilon^2 \le 12/\varepsilon^2$.
S, about 20 lines. -/
theorem length_squareGrid_le (c : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((squareGrid c R ε).length : ℝ) ≤ 12 / ε ^ 2 := by
  have hlen :
      (squareGrid c R ε).length = (⌈Real.sqrt 2 / ε⌉₊ + 1) * (⌈Real.sqrt 2 / ε⌉₊ + 1) := by
    simp [squareGrid, List.length_flatMap, List.length_map, List.length_range]
  rw [hlen]
  push_cast
  have hs0 : 0 ≤ Real.sqrt 2 / ε := by positivity
  have hmlt : (⌈Real.sqrt 2 / ε⌉₊ : ℝ) < Real.sqrt 2 / ε + 1 := Nat.ceil_lt_add_one hs0
  have hmε : (⌈Real.sqrt 2 / ε⌉₊ : ℝ) * ε < Real.sqrt 2 + ε := by
    have := mul_lt_mul_of_pos_right hmlt hε
    rwa [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at this
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs15 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hu : ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ε ≤ Real.sqrt 2 + 2 * ε := by linarith
  have hu0 : 0 ≤ ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ε := by positivity
  have hsq2 := pow_le_pow_left₀ hu0 hu 2
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hε1 (Real.sqrt_nonneg 2),
    mul_le_mul_of_nonneg_left hε1 hε.le]

/-- **The grid stays near its centre**: every point $s$ of `NLAlib.squareGrid` $c$ $R$
$\varepsilon$, $R \ge 0$, $\varepsilon > 0$, has $\lvert s - c\rvert \le \sqrt2R$.
Proof: both coordinates of $(s - c)/R$ are in $[-1, 1]$ (`List.mem_flatMap`, `List.mem_map`,
`List.mem_range`). S, about 15 lines. -/
theorem norm_sub_le_of_mem_squareGrid {c s : ℂ} {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hs : s ∈ squareGrid c R ε) : ‖s - c‖ ≤ Real.sqrt 2 * R := by
  have hbd : ∀ i : ℕ, i < ⌈Real.sqrt 2 / ε⌉₊ + 1 →
      -1 ≤ 2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1 ∧
        2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1 ≤ 1 := by
    intro i hi
    rcases Nat.eq_zero_or_pos ⌈Real.sqrt 2 / ε⌉₊ with h0 | hpos
    · have : i = 0 := by omega
      subst this
      simp [h0]
    · have hm : (0 : ℝ) < (⌈Real.sqrt 2 / ε⌉₊ : ℝ) := by exact_mod_cast hpos
      have hi' : (i : ℝ) ≤ (⌈Real.sqrt 2 / ε⌉₊ : ℝ) := by exact_mod_cast (by omega : i ≤ _)
      have h0' : 0 ≤ 2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) := by positivity
      have h1' : 2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hm]; linarith
      constructor <;> linarith
  unfold squareGrid at hs
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hs
  obtain ⟨i, hi, j, hj, rfl⟩ := hs
  obtain ⟨ha1, ha2⟩ := hbd i hi
  obtain ⟨hb1, hb2⟩ := hbd j hj
  have hnorm : ‖(⟨2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1,
      2 * (j : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1⟩ : ℂ)‖ ≤ Real.sqrt 2 := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [Complex.sq_norm, Complex.normSq_mk]
    nlinarith
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR]
  nlinarith [mul_le_mul_of_nonneg_left hnorm hR]

/-- **An exceptional shift succeeds**: let $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$ with $\mathbf{V}$ invertible and $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$; let
the $k \ge 2$ shifts `ss` be $\theta$-optimal Ritz values of $\mathbf{H}$, $\theta \ge 1$, none
an eigenvalue, $r$ an $\alpha$-promising member, $\alpha \ge 1$, $0 < \gamma < 1$,
$0 < \xi \le 1$, $\psi = \psi_k(\mathbf{H}) > 0$, and let $(z - r)^k$ stagnate with ratio $\xi$:
$\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|\,(\xi\psi)^k \le 1$. Then some point
$s$ of the grid of spacing $\varepsilon = \bigl(\xi(1 - \gamma)/((14B^4)^{1/k}\alpha^2\theta^2)
\bigr)^{k/(k-1)}$ on the disk of radius $(2B)^{1/k}\theta\alpha\psi$ about $r$ is an eigenvalue
or has
$$1 \le ((1 - \gamma)\psi)^k\,\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - s\mathbf{I})^{-k}\|\,,$$
so that $\tau_{(z-s)^k}(\mathbf{H}) \le (1 - \gamma)\psi$.
[BanksGarzaVargasSrivastava2021, Lemma 4.7] (Exc), there with $\xi = 1 - \gamma$, constant
$12$ and a maximal net; the grid has up to $12/\varepsilon^2$ points, whence $14 \ge \sqrt{192}$.
Proof: `NLAlib.IsOptimalRitzValues.sq_mul_pow_le_mul_sum_lastRowWeights_filter` with $t = 1/2$
puts weight $P \ge \xi^{2k}/(4B^4(\alpha\theta)^{2k})$ on the disk (radius monotone in $\kappa$);
every such $\mathbf{d}_i$ is within $\varepsilon R$ of a grid point
(`NLAlib.exists_mem_squareGrid_norm_sub_le`); average over the grid
(`NLAlib.length_squareGrid_le`, $\varepsilon \le 1$) and
`NLAlib.sum_lastRowWeights_mul_sq_le` give $\max_s\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} -
s\mathbf{I})^{-k}\|^2 \ge \varepsilon^2P/(12B^2(\varepsilon R)^{2k})$, which the choice of
$\varepsilon$ makes $\ge ((1 - \gamma)\psi)^{-2k}$; a grid point equal to some $\mathbf{d}_i$ is
the first alternative. L, about 90 lines (split the averaging step off). -/
theorem IsOptimalRitzValues.exists_mem_squareGrid_det_eq_zero_or_one_le {θ α ξ γ B : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    (hss : IsOptimalRitzValues θ H ss) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hB : pseudoConditionNumber V ≤ B) (hd : ∀ i, ∀ s ∈ ss, d i ≠ s)
    (hr : IsPromisingRitzValue α V d ss r) (hk : 2 ≤ ss.length) (hθ : 1 ≤ θ) (hα : 1 ≤ α)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hψ : 0 < hessenbergPotential ss.length H)
    (hstag : ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^
        ss.length) (Fin.last n))‖ * (ξ * hessenbergPotential ss.length H) ^ ss.length ≤ 1) :
    ∃ s ∈ squareGrid r (exceptionalRadius ss.length B θ α (hessenbergPotential ss.length H))
        (exceptionalSpacing ss.length B θ α (ξ * (1 - γ))),
      (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0 ∨
        1 ≤ ((1 - γ) * hessenbergPotential ss.length H) ^ ss.length *
          ‖WithLp.toLp 2 (((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^
            ss.length) (Fin.last n))‖ := by
  sorry

/-! ### One iteration and the decoupling theorem -/

/-- **One iteration of $\mathrm{Sh}_{k,B}$ decouples or reduces the potential**: let
$\mathbf{H}$ be upper Hessenberg with $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$, $\mathbf{V}$ invertible and $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$; let
$k = 2^m$ with $m \ge 1$ and $k \le n$, `ss` a list of $k$ $\theta$-optimal Ritz values,
$\theta \ge 1$, $\alpha \ge 1$ with $B^{4m} \le \alpha^k$, and $0 < \gamma < 1$. Then
$\widehat{\mathbf{H}} = \mathsf{shqrStep}(\mathbf{H}, \mathrm{ss})$ has a zero subdiagonal entry
or $\psi_k(\widehat{\mathbf{H}}) \le (1 - \gamma)\psi_k(\mathbf{H})$.
[BanksGarzaVargasSrivastava2021, Theorem 1.6, proof of rapid convergence], with the singular
cases made explicit.
Proof: if $\mathbf{H}$ is reduced (in particular if $\psi_k(\mathbf{H}) = 0$),
`NLAlib.IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep`. If a Ritz value is an
eigenvalue, the first clause of `NLAlib.shqrShift` picks one and
`NLAlib.IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero` applies. Otherwise
$r$ = `NLAlib.findRitz` is $\alpha$-promising (`NLAlib.isPromisingRitzValue_findRitz`,
$\kappa^{4m} \le B^{4m} \le \alpha^k$); if it is a success it is found first; else by
`NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le` it stagnates with
$\xi = 1 - \gamma$, and `NLAlib.IsOptimalRitzValues.exists_mem_squareGrid_det_eq_zero_or_one_le`
gives a grid point that succeeds (by the same two lemmas); `List.find?` returns a success when
one exists (`Classical.choose_spec` on the `∃` of `NLAlib.shqrShift`); E1's spacing at
$\xi = 1 - \gamma$ is `exceptionalSpacing … ((1 - γ) * (1 - γ))`, the candidates' is
`… ((1 - γ) ^ 2)`: one `sq` rewrite. L, about 80 lines. -/
theorem IsUpperHessenberg.isDecoupled_zero_shqrStep_or_hessenbergPotential_le
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {B θ α γ : ℝ}
    (hB : pseudoConditionNumber V ≤ B) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n) {ss : List ℂ}
    (hlen : ss.length = 2 ^ m) (hss : IsOptimalRitzValues θ H ss) (hθ : 1 ≤ θ) (hα1 : 1 ≤ α)
    (hα : B ^ (4 * m) ≤ α ^ 2 ^ m) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsDecoupled 0 (shqrStep B θ α γ m H ss) ∨
      hessenbergPotential (2 ^ m) (shqrStep B θ α γ m H ss) ≤
        (1 - γ) * hessenbergPotential (2 ^ m) H := by
  sorry

/-- **The iterates of $\mathrm{Sh}_{k,B}$ are upper Hessenberg**: if $\mathbf{H}_0$ is, so is
every `NLAlib.shqrIterate` $\mathbf{H}_t$, for every Ritz-value oracle.
Proof: induction on $t$ with `NLAlib.IsUpperHessenberg.isUpperHessenberg_multiShiftedQRStep`.
S, about 6 lines. -/
theorem IsUpperHessenberg.isUpperHessenberg_shqrIterate {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H₀) (B θ α γ : ℝ) (m : ℕ)
    (ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ) (t : ℕ) :
    IsUpperHessenberg (shqrIterate B θ α γ m ritz H₀ t) := by
  sorry

/-- **The iterates of $\mathrm{Sh}_{k,B}$ have the norm of $\mathbf{H}_0$**:
$\|\mathbf{H}_t\|_2 = \|\mathbf{H}_0\|_2$ for every $t$ and every Ritz-value oracle.
Proof: induction on $t$ with `NLAlib.specNorm_multiShiftedQRStep`. S, about 6 lines. -/
theorem specNorm_shqrIterate (B θ α γ : ℝ) (m : ℕ)
    (ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ)
    (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (t : ℕ) :
    specNorm (shqrIterate B θ α γ m ritz H₀ t) = specNorm H₀ := by
  sorry

/-- **The iterates of $\mathrm{Sh}_{k,B}$ keep the eigenvector condition number**: if
$\mathbf{H}_0\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$
invertible, every $\mathbf{H}_t$ has $\mathbf{H}_t\mathbf{V}' = \mathbf{V}'\operatorname{diag}(
\mathbf{d})$ for an invertible $\mathbf{V}'$ with $\|\mathbf{V}'\|_2\|\mathbf{V}'^{-1}\|_2 =
\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$.
Proof: induction on $t$ with `NLAlib.exists_isUnit_mul_eq_mul_diagonal_multiShiftedQRStep`.
S, about 10 lines. -/
theorem exists_isUnit_mul_eq_mul_diagonal_shqrIterate
    {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H₀ * V = V * Matrix.diagonal d) (B θ α γ : ℝ) (m : ℕ)
    (ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ) (t : ℕ) :
    ∃ V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnit V' ∧
      shqrIterate B θ α γ m ritz H₀ t * V' = V' * Matrix.diagonal d ∧
      pseudoConditionNumber V' = pseudoConditionNumber V := by
  sorry

/-- **Rapid decoupling of the Hessenberg shifted QR algorithm** with the strategy
$\mathrm{Sh}_{k,B}$: let $\mathbf{H}_0$ be upper Hessenberg and diagonalizable,
$\mathbf{H}_0\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible
and $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ (so $\kappa_V(\mathbf{H}_0) \le B$); let
$k = 2^m$, $m \ge 1$, $k \le n$; $\theta \ge 1$; $\alpha \ge 1$ with $B^{4m} \le \alpha^k$ (e.g.
$\alpha = B^{4\log_2 k/k}$); $0 < \gamma < 1$; and let the Ritz-value oracle return, on every
upper Hessenberg matrix with $\psi_k > 0$, $k$ $\theta$-optimal Ritz values (as
[BanksGarzaVargasSrivastava2021, Definition 1.5] requires only when the minimum is nonzero).
Then for every $\delta > 0$ some
$$t \le \Bigl\lceil\frac{\log(1/\delta)}{\log(1/(1 - \gamma))}\Bigr\rceil$$
has $\mathsf{shqrIterate}(\mathbf{H}_0)_t$ $\delta$-decoupled: a subdiagonal entry of modulus at
most $\delta\|\mathbf{H}_t\|_2$. [BanksGarzaVargasSrivastava2021, Theorem 1.6, item 1], printed
as $\mathrm{dec}_\delta(\mathbf{H}_0) \le 4\log_2(1/\delta)$, which is false for $\delta$ near
$1$ (gap G2 of the design note); here with the ceiling, $\le 4\log_2(1/\delta) + 1$ at
$\gamma = 0.2$.
Proof: by induction on $t$, as long as no iterate is reduced,
$\psi_k(\mathbf{H}_t) \le (1 - \gamma)^t\psi_k(\mathbf{H}_0)$
(`NLAlib.IsUpperHessenberg.isDecoupled_zero_shqrStep_or_hessenbergPotential_le`, with the
invariants `NLAlib.IsUpperHessenberg.isUpperHessenberg_shqrIterate`,
`NLAlib.exists_isUnit_mul_eq_mul_diagonal_shqrIterate`); a reduced iterate is decoupled for every
$\delta \ge 0$. At the stated $t$, $(1 - \gamma)^t \le \delta$ (`Nat.le_ceil`, `Real.log_le_log`,
`Real.rpow_natCast`), so $\psi_k(\mathbf{H}_t) \le \delta\|\mathbf{H}_0\|_2 =
\delta\|\mathbf{H}_t\|_2$ (`NLAlib.hessenbergPotential_le_specNorm`,
`NLAlib.specNorm_shqrIterate`), and `NLAlib.isDecoupled_of_hessenbergPotential_le`; the oracle is
used only at unreduced iterates, where $\psi_k > 0$. For $\delta \ge 1$ the ceiling is $0$
(`Real.log (1/δ) ≤ 0`) and $\mathbf{H}_0$ is $\delta$-decoupled since `Fin n` is nonempty
($n \ge 2^m \ge 2$) and every entry is at most $\|\mathbf{H}_0\|_2 \le \delta\|\mathbf{H}_0\|_2$;
`IsDecoupled 0` implies `IsDecoupled δ` for $\delta \ge 0$. L, about 80 lines.
Result: shifted-qr-rapid-decoupling -/
theorem IsUpperHessenberg.exists_le_isDecoupled_shqrIterate
    {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H₀)
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H₀ * V = V * Matrix.diagonal d)
    {B θ α γ : ℝ} (hB : pseudoConditionNumber V ≤ B) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n)
    (hθ : 1 ≤ θ) (hα1 : 1 ≤ α) (hα : B ^ (4 * m) ≤ α ^ 2 ^ m) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ}
    (hritz : ∀ H', IsUpperHessenberg H' → 0 < hessenbergPotential (2 ^ m) H' →
      (ritz H').length = 2 ^ m ∧ IsOptimalRitzValues θ H' (ritz H'))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t ≤ ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊,
      IsDecoupled δ (shqrIterate B θ α γ m ritz H₀ t) := by
  sorry

/-- **The number of shifts tried per iteration**: for $B, \theta, \alpha \ge 1$,
$0 < \gamma < 1$ and $m \ge 1$, the candidate list `NLAlib.shqrCandidates` has at most
$1 + 12/\varepsilon^2$ entries, $\varepsilon$ = `NLAlib.exceptionalSpacing` $2^m$ $B$ $\theta$
$\alpha$ $(1 - \gamma)^2$. Each candidate costs one degree $k$ QR step, besides the
$2\log_2 k$ degree $k/2$ steps of `NLAlib.findRitz`. [BanksGarzaVargasSrivastava2021,
Theorem 1.6, item 2], in count form.
Proof: `List.length_cons` and `NLAlib.length_squareGrid_le`, with $0 < \varepsilon \le 1$ since
the base of the power is in $(0, 1]$ (`Real.rpow_le_one`, `Real.rpow_pos_of_pos`).
S, about 20 lines. -/
theorem length_shqrCandidates_le {B θ α γ : ℝ} (hB : 1 ≤ B) (hθ : 1 ≤ θ) (hα : 1 ≤ α)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) {m : ℕ} (hm : 1 ≤ m)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    ((shqrCandidates B θ α γ m H ss).length : ℝ) ≤
      1 + 12 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2) ^ 2 := by
  sorry

/-- **The spacing at the paper's parameters**: for $m \ge 1$, $B \ge 1$, $\theta = 2$,
$\gamma = 0.2$ and $\alpha = B^{4m/2^m}$,
$$\varepsilon \ge 0.0018\,B^{-(8m + 4)/(2^m - 1)}\,,$$
so the number of shifts per iteration is $O(B^{(16\log_2 k + 8)/(k-1)})$, which is $O(1)$ for
$k \ge C\log B\log\log B$. [BanksGarzaVargasSrivastava2021, Lemma 4.7, proof], there
$0.002B^{-(8\log k + 4)/(k-1)}$ for the constant $12$ (the statement of Lemma 4.7 there prints
$k$ for $k - 1$; gap G6).
Proof: unfold `NLAlib.exceptionalSpacing`; the base is $0.16\cdot14^{-1/k}B^{-(4 + 8m)/k}$;
raise to $k/(k - 1) \le 2$ (`Real.rpow_le_rpow_of_exponent_ge` for the factors below $1$,
`Real.rpow_mul`, `Real.rpow_natCast`): $0.16^{k/(k-1)}14^{-1/(k-1)} \ge 0.16^2/14 \ge 0.0018$.
L, about 60 lines (three monotonicity steps in `Real.rpow`). -/
theorem exceptionalSpacing_ge {B : ℝ} (hB : 1 ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    0.0018 * B ^ (-(8 * m + 4 : ℝ) / ((2 : ℝ) ^ m - 1)) ≤
      exceptionalSpacing (2 ^ m) B 2 (B ^ ((4 * m : ℝ) / (2 : ℝ) ^ m)) ((1 - 0.2) ^ 2) := by
  unfold exceptionalSpacing
  push_cast
  set k : ℝ := (2 : ℝ) ^ m with hk_def
  have hk : 2 ≤ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ k := pow_le_pow_right₀ (by norm_num) hm
  have hk1 : 0 < k - 1 := by linarith
  have hB0 : 0 < B := by linarith
  set c : ℝ := 0.16 / (14 : ℝ) ^ k⁻¹ with hc_def
  have h14 : (14 : ℝ) ^ k⁻¹ ≤ 3.75 := by
    have hk2 : k⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hk2).trans ?_
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
    norm_num
  have hc0 : 0.0425 ≤ c := by
    rw [hc_def, le_div_iff₀ (by positivity)]; nlinarith
  have hc1 : c ≤ 1 := by
    rw [hc_def, div_le_one (by positivity)]
    linarith [Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 14) (inv_nonneg.mpr (by linarith : 0 ≤ k))]
  have hbase : (1 - 0.2 : ℝ) ^ 2 / ((14 * B ^ 4) ^ k⁻¹ * (B ^ ((4 * m : ℝ) / k)) ^ 2 * 2 ^ 2) =
      c * B ^ (-(8 * m + 4 : ℝ) / k) := by
    have e : (8 * m + 4 : ℝ) / k = (4 : ℕ) * k⁻¹ + 4 * m / k * (2 : ℕ) := by push_cast; ring
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast B 4,
      ← Real.rpow_mul hB0.le, ← Real.rpow_natCast (B ^ _) 2, ← Real.rpow_mul hB0.le, neg_div,
      Real.rpow_neg hB0.le, hc_def, e, Real.rpow_add hB0]
    field_simp
    norm_num
  have hexp : (-(8 * m + 4 : ℝ) / k) * (k / (k - 1)) = -(8 * m + 4 : ℝ) / (k - 1) := by
    field_simp
  rw [hbase, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hB0.le, hexp]
  gcongr
  calc (0.0018 : ℝ) ≤ c ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    _ ≤ c ^ (k / (k - 1)) := Real.rpow_le_rpow_of_exponent_ge (by linarith) hc1
        (by rw [div_le_iff₀ hk1]; linarith)

/-- **Rapid decoupling for normal Hessenberg matrices**: let $\mathbf{H}_0$ be normal and upper
Hessenberg, $k = 2^m$ with $m \ge 1$ and $k \le n$, and $0 < \gamma < 1$. With the exact Ritz
values and $B = \theta = \alpha = 1$, the iteration $\mathrm{Sh}_{k,1}$ is $\delta$-decoupled
at some
$$t \le \Bigl\lceil\frac{\log(1/\delta)}{\log(1/(1 - \gamma))}\Bigr\rceil$$
for every $\delta > 0$, trying at most $1 + 12/\varepsilon^2$ shifts per iteration with
$\varepsilon = ((1 - \gamma)^2/14^{1/k})^{k/(k-1)}$. [BanksGarzaVargasSrivastava2021,
Theorem 1.2] (Theorem 3.3 there for $k = 2$), which uses the separate strategy $\mathrm{Sh}_{2,1}$
with a quadratic shift $(z - r)^2$ and whose exceptional-shift count does not reduce the
potential as printed (gap G1); here as the case $B = 1$ of the general strategy.
Proof: `IsStarNormal.exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_eq_one`,
`NLAlib.IsUpperHessenberg.isOptimalRitzValues_one_ritzValues`, `NLAlib.length_ritzValues`, then
`NLAlib.IsUpperHessenberg.exists_le_isDecoupled_shqrIterate` with $B = \theta = \alpha = 1$.
S, about 15 lines.
Result: shifted-qr-normal-decoupling -/
theorem _root_.IsStarNormal.exists_le_isDecoupled_shqrIterate_ritzValues
    {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hN : IsStarNormal H₀)
    (hH : IsUpperHessenberg H₀) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t ≤ ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊,
      IsDecoupled δ (shqrIterate 1 1 1 γ m (ritzValues (2 ^ m)) H₀ t) := by
  sorry

end NLAlib
