/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Sphere
public import NLAlibScaffold.ForMathlib.Probability.Distributions.Beta
public import NLAlibScaffold.Probability.Distributions.ChiSquare

/-!
# Projections of a uniform unit vector: the Beta law and the sharp sub-Gaussian tail

Statements for `NLAlib/RandomMatrix/Haar/Sphere.lean` whose proofs are deferred
(`docs/design/Probability-Beta.md`, §3.4, β3–β6). For $\mathbf{u}$ uniform on the unit sphere of
$\mathbb{R}^n$ and $\mathbf{V}$ with $k$ orthonormal columns, $0 < k < n$,
$\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 \sim \mathrm{Beta}(k/2, (n-k)/2)$: write
$\mathbf{u} = \mathbf{g}/\|\mathbf{g}\|$, rotate $\mathbf{V}$ to the first $k$ coordinates, and
the two blocks of $\mathbf{g}$ give independent chi-square laws, whose ratio is Beta. With the
Beta sub-Gaussian proxy [MarchalArbel2017], $\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 - k/n$ has
variance proxy $1/(2(n+2))$ for every $0 \le k \le n$, and Hoeffding gives the tail
$2e^{-m(n+2)\tau^2}$ of the mean of $m$ independent copies (the last theorem of the file; its
name is too long for this list).

## Main results

* `NLAlib.hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector`: the Beta law.
* `NLAlib.hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector`:
  the sub-Gaussian proxy $1/(2(n+2))$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k] [DecidableEq k] {u : Ω → n → ℝ} {V : Matrix n k ℝ}

/-! ### Helpers -/

omit [DecidableEq k] in
/-- The two blocks of a standard Gaussian vector indexed by $k \oplus p$ have independent sums of
squares.
Proof: M, about 20 lines (with the two laws below, 30 to 50 in all).
`measurePreserving_sumPiEquivProdPi` splits `gaussianVector (k ⊕ p)` as
`(gaussianVector k).prod (gaussianVector p)`; `indepFun_iff_map_prod_eq_prod_map_map`,
`IndepFun.comp` with the two sums of squares; `Measure.map_map`. -/
private theorem indepFun_sum_sq_inl_sum_sq_inr_of_hasLaw_gaussianVector {p : Type*} [Fintype p]
    {h : Ω → k ⊕ p → ℝ} (hh : HasLaw h (gaussianVector (k ⊕ p)) μ) :
    IndepFun (fun ω => ∑ i, h ω (Sum.inl i) ^ 2) (fun ω => ∑ j, h ω (Sum.inr j) ^ 2) μ := by
  have hpair : HasLaw (fun ω => (fun i => h ω (Sum.inl i), fun j => h ω (Sum.inr j)))
      ((gaussianVector k).prod (gaussianVector p)) μ :=
    (measurePreserving_sumPiEquivProdPi (fun _ : k ⊕ p => gaussianReal 0 1)).fun_comp_hasLaw hh
  have := hh.isProbabilityMeasure
  have hX : HasLaw (fun ω => fun i => h ω (Sum.inl i)) (gaussianVector k) μ :=
    (measurePreserving_fst).fun_comp_hasLaw hpair
  have hY : HasLaw (fun ω => fun j => h ω (Sum.inr j)) (gaussianVector p) μ :=
    (measurePreserving_snd).fun_comp_hasLaw hpair
  have hind : IndepFun (fun ω => fun i => h ω (Sum.inl i))
      (fun ω => fun j => h ω (Sum.inr j)) μ := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hX.map_eq,
      hY.map_eq]
    exact hpair.map_eq
  exact hind.comp (φ := fun x : k → ℝ => ∑ i, x i ^ 2) (ψ := fun y : p → ℝ => ∑ j, y j ^ 2)
    (by fun_prop) (by fun_prop)

omit [DecidableEq k] in
/-- The first block of a standard Gaussian vector indexed by $k \oplus p$, $k$ nonempty, has a
chi-square sum of squares, $\mathrm{Gamma}(\lvert k\rvert/2, 1/2)$.
Proof: S, about 12 lines. The first block has law `gaussianVector k`
(`measurePreserving_sumPiEquivProdPi`, `Measure.map_fst_prod`, `HasLaw.comp`); then
`hasLaw_sum_sq_of_hasLaw_pi_gaussianReal`. -/
private theorem hasLaw_sum_sq_inl_of_hasLaw_gaussianVector {p : Type*} [Fintype p] [Nonempty k]
    {h : Ω → k ⊕ p → ℝ} (hh : HasLaw h (gaussianVector (k ⊕ p)) μ) :
    HasLaw (fun ω => ∑ i, h ω (Sum.inl i) ^ 2) (gammaMeasure (Fintype.card k / 2) (1 / 2)) μ :=
  hasLaw_sum_sq_of_hasLaw_pi_gaussianReal (hasLaw_comp_inl_gaussianVector.comp hh)

omit [DecidableEq k] in
/-- The second block of a standard Gaussian vector indexed by $k \oplus p$, $p$ nonempty, has a
chi-square sum of squares, $\mathrm{Gamma}(\lvert p\rvert/2, 1/2)$.
Proof: S, about 12 lines. As `hasLaw_sum_sq_inl_of_hasLaw_gaussianVector` with
`Measure.map_snd_prod`. -/
private theorem hasLaw_sum_sq_inr_of_hasLaw_gaussianVector {p : Type*} [Fintype p] [Nonempty p]
    {h : Ω → k ⊕ p → ℝ} (hh : HasLaw h (gaussianVector (k ⊕ p)) μ) :
    HasLaw (fun ω => ∑ j, h ω (Sum.inr j) ^ 2) (gammaMeasure (Fintype.card p / 2) (1 / 2)) μ := by
  have hP := (measurePreserving_sumPiEquivProdPi
    (fun _ : k ⊕ p => gaussianReal 0 1)).fun_comp_hasLaw hh
  have hq : HasLaw (fun ω j => h ω (Sum.inr j)) (gaussianVector p) μ :=
    MeasurePreserving.fun_comp_hasLaw measurePreserving_snd hP
  exact hasLaw_sum_sq_of_hasLaw_pi_gaussianReal hq

/-- The projected length of a normalised vector in the rotated coordinates: if
$\mathbf{W} = \begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}$ has orthonormal columns
and is square ($\lvert k\rvert + \lvert p\rvert = \lvert n\rvert$), then for every $\mathbf{g}$,
with $\mathbf{h} = \mathbf{W}^{\mathsf{H}}\mathbf{g}$,
$\|\mathbf{V}^{\mathsf{H}}(\mathbf{g}/\|\mathbf{g}\|)\|^2 = \sum_i \mathbf{h}_{\mathrm{inl}\,i}^2 /
(\sum_i \mathbf{h}_{\mathrm{inl}\,i}^2 + \sum_j \mathbf{h}_{\mathrm{inr}\,j}^2)$.
Proof: S, about 25 lines. The file's `norm_conjTranspose_mulVec_inv_norm_smul_sq`; the
`Matrix.fromCols` mulVec on `Sum.inl` (as `hWl` in `measureReal_mem_le_of_two_weights`);
$\|\mathbf{W}^{\mathsf{H}}\mathbf{g}\| = \|\mathbf{g}\|$ for square $\mathbf{W}$
(`HasOrthonormalCols.conjTranspose_of_card_eq`); `EuclideanSpace.real_norm_sq_eq`,
`Fintype.sum_sum_type`. -/
private theorem norm_conjTranspose_mulVec_inv_norm_smul_sq_eq_div {p : Type*} [Fintype p]
    [DecidableEq p] {V' : Matrix n p ℝ} (hVV' : HasOrthonormalCols (Matrix.fromCols V V'))
    (hcard : Fintype.card k + Fintype.card p = Fintype.card n) (g : n → ℝ) :
    ‖WithLp.toLp 2 (Vᴴ *ᵥ (‖WithLp.toLp 2 g‖⁻¹ • g))‖ ^ 2 =
      (∑ i, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) ^ 2) /
        (∑ i, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) ^ 2 +
          ∑ j, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inr j) ^ 2) := by
  classical
  have hWn : HasOrthonormalCols (Matrix.fromCols V V')ᴴ :=
    hVV'.conjTranspose_of_card_eq (by rw [Fintype.card_sum]; exact hcard.symm)
  have hWl (i : k) : ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) = (Vᴴ *ᵥ g) i := by
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.fromCols_apply_inl]
  have hG : ‖WithLp.toLp 2 g‖ ^ 2 = ∑ i, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) ^ 2 +
      ∑ j, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inr j) ^ 2 := by
    rw [← Fintype.sum_sum_type (fun x => ((Matrix.fromCols V V')ᴴ *ᵥ g) x ^ 2),
      ← hWn.norm_toLp_mulVec g, EuclideanSpace.real_norm_sq_eq]
  have hV : ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2 =
      ∑ i, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [hWl]
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, mul_pow, norm_inv, norm_norm, inv_pow,
    inv_mul_eq_div, hV, hG]

/-! ### The Beta law -/

/-- **The projection of a uniform unit vector is Beta**: for $\mathbf{u}$ uniform on the unit
sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`) and $\mathbf{V}$ with $k$ orthonormal
columns, $0 < k < n$,
$\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 \sim \mathrm{Beta}(k/2, (n-k)/2)$.
No printed source.
Proof: M, about 50 lines. `Nat.exists_eq_add_of_le` and `HasOrthonormalCols.exists_fromCols`
for a square $\mathbf{W} = \begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}$; reduce to
`gaussianVector n` (`uniformSphereVector`, `HasLaw.fun_comp`, `measurable_inv_norm_smul`,
`HasLaw.id`); `hasLaw_mulVec_of_hasLaw_gaussianVector` for $\mathbf{W}^{\mathsf{H}}\mathbf{g}$
(allows `Matrix (k ⊕ p) n`); `norm_conjTranspose_mulVec_inv_norm_smul_sq_eq_div` pointwise
(`HasLaw.congr`); `hasLaw_div_add_of_hasLaw_gammaMeasure` with $a = k/2$, $b = p/2$, $r = 1/2$
from the three block lemmas; `Nat.cast_add`.
Result: sphere-projection-beta -/
theorem hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V)
    (hk : 0 < Fintype.card k) (hkn : Fintype.card k < Fintype.card n) :
    HasLaw (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2)
      (betaMeasure (Fintype.card k / 2) (((Fintype.card n : ℝ) - Fintype.card k) / 2)) μ := by
  sorry

/-! ### The sharp sub-Gaussian tail -/

/-- A variable that is almost surely $0$ is sub-Gaussian with any proxy. -/
private lemma hasSubgaussianMGF_of_ae_eq_zero [IsProbabilityMeasure μ] {Y : Ω → ℝ} (c : ℝ≥0)
    (hY : Y =ᵐ[μ] 0) : HasSubgaussianMGF Y c μ := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · refine (integrable_const (1 : ℝ)).congr ?_
    filter_upwards [hY] with ω hω
    simp [hω]
  · calc mgf Y μ t = ∫ _ : Ω, (1 : ℝ) ∂μ := integral_congr_ae (by
          filter_upwards [hY] with ω hω
          simp [hω])
      _ ≤ Real.exp (c * t ^ 2 / 2) := by
          rw [integral_const, probReal_univ, smul_eq_mul, mul_one]
          exact Real.one_le_exp (by positivity)

/-- **Projections of a uniform unit vector are sub-Gaussian**: for $\mathbf{u}$ uniform on the
unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`) and $\mathbf{V}$ with $k$
orthonormal columns, any $0 \le k \le n$,
$\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 - k/n$ satisfies the sub-Gaussian moment generating
function bound with variance proxy $1/(2(n+2))$. For $0 < k < n$ this is the Beta proxy
$1/(4(\alpha+\beta+1))$ at $\alpha + \beta = n/2$; for $k \in \{0, n\}$ the variable is $0$
almost surely. Compared with the Chernoff tails of this file
(`NLAlib.measureReal_norm_conjTranspose_mulVec_sq_ge_mul_div_le_of_hasLaw_uniformSphereVector`
and its lower twin), whose exponent near the mean is about $n^2\tau^2/(4k)$ at deviation $\tau$
against $(n+2)\tau^2$ here: this bound is better when $k \gtrsim n/4$ and worse for small $k$.
[MarchalArbel2017, Theorem 1] for the Beta proxy.
Proof: M, about 50 lines. Cases: $k = 0$ (`Fintype.card_eq_zero_iff`; the variable is $0$,
`HasSubgaussianMGF.zero` with `congr`); $k = n$ (`ae_norm_eq_one_uniformSphereVector`;
$\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\| = \|\mathbf{u}\|$ for square $\mathbf{V}$ by
`HasOrthonormalCols.conjTranspose_of_card_eq`; `congr` to $0$); otherwise
`hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector` and
`hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure`, with $\alpha + \beta = n/2$ and
$\alpha/(\alpha+\beta) = k/n$ rewritten (`field_simp`; proxies equal in `ℝ≥0` by `NNReal.eq`). -/
theorem hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) :
    HasSubgaussianMGF
      (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2 - Fintype.card k / Fintype.card n)
      ‖1 / (2 * ((Fintype.card n : ℝ) + 2))‖₊ μ := by
  classical
  have : IsProbabilityMeasure μ := hu.isProbabilityMeasure
  have hk : Fintype.card k ≤ Fintype.card n := hV.card_le
  rcases Nat.eq_zero_or_pos (Fintype.card k) with h0 | hpos
  · have he : IsEmpty k := Fintype.card_eq_zero_iff.mp h0
    have hz : ∀ x : k → ℝ, ‖WithLp.toLp 2 x‖ = 0 := fun x => by
      rw [show x = 0 from funext fun i => isEmptyElim i]
      simp
    refine hasSubgaussianMGF_of_ae_eq_zero _ (Filter.Eventually.of_forall fun ω => ?_)
    simp [hz]
  rcases hk.eq_or_lt with heq | hlt
  · have hn : 0 < Fintype.card n := heq ▸ hpos
    have : Nonempty n := Fintype.card_pos_iff.mp hn
    have hVc : HasOrthonormalCols Vᴴ := hV.conjTranspose_of_card_eq heq.symm
    have hae : ∀ᵐ ω ∂μ, ‖WithLp.toLp 2 (u ω)‖ = 1 :=
      ae_of_ae_map hu.aemeasurable (by rw [hu.map_eq]; exact ae_norm_eq_one_uniformSphereVector)
    refine hasSubgaussianMGF_of_ae_eq_zero _ ?_
    filter_upwards [hae] with ω hω
    have hn' : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [Pi.zero_apply, hVc.norm_toLp_mulVec, hω, heq]
    simp [hn']
  · have hnpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos.trans hlt
    have hX := hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector hu hV hpos hlt
    have hα : (0 : ℝ) < Fintype.card k / 2 := half_pos (by exact_mod_cast hpos)
    have hβ : (0 : ℝ) < ((Fintype.card n : ℝ) - Fintype.card k) / 2 :=
      half_pos (sub_pos.mpr (by exact_mod_cast hlt))
    have key := hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure hα hβ hX
    have hab : (Fintype.card k : ℝ) / 2 + ((Fintype.card n : ℝ) - Fintype.card k) / 2 =
        Fintype.card n / 2 := by ring
    have hratio : (Fintype.card k : ℝ) / 2 /
        ((Fintype.card k : ℝ) / 2 + ((Fintype.card n : ℝ) - Fintype.card k) / 2) =
        Fintype.card k / Fintype.card n := by
      rw [hab]
      field_simp
    have hprox : ‖1 / (4 * ((Fintype.card k : ℝ) / 2 +
        ((Fintype.card n : ℝ) - Fintype.card k) / 2 + 1))‖₊ =
        ‖1 / (2 * ((Fintype.card n : ℝ) + 2))‖₊ := by
      rw [hab]
      congr 1
      field_simp
      ring
    rw [hratio, hprox] at key
    exact key

-- The declaration name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The sample mean of projected uniform unit vectors**: for $\mathbf{u}_1, \dots, \mathbf{u}_m$
independent and each uniform on the unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`),
$\mathbf{V}$ with $k$ orthonormal columns and $\tau \ge 0$,
$$\mathbb{P}\Bigl[\tau \le \Bigl\lvert\frac1m\sum_j\|\mathbf{V}^{\mathsf{H}}\mathbf{u}_j\|^2 -
\frac kn\Bigr\rvert\Bigr] \le 2e^{-m(n+2)\tau^2}\,.$$
Every rank $0 \le k \le n$ is allowed, and for $m = 0$ the bound is $2$.
[MarchalArbel2017, Theorem 1] for the Beta proxy, then Hoeffding's inequality.
Proof: M, about 30 lines. `iIndepFun.isProbabilityMeasure`; empty `m`: `measureReal_le_one`;
`iIndepFun.comp` with the centred projections;
`hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector` for each $j$,
`HasSubgaussianMGF.sum_of_iIndepFun`, `HasSubgaussianMGF.measureReal_abs_ge_le` at
$\varepsilon = m\tau$; the event equality (`Finset.sum_sub_distrib`, `Finset.sum_const`,
`abs_div`, `le_div_iff₀`); the exponent $(m\tau)^2/(2 \cdot m/(2(n+2))) = m(n+2)\tau^2$.
Result: sphere-projection-tail -/
theorem
measureReal_abs_sum_norm_conjTranspose_mulVec_sq_div_card_sub_div_card_ge_le_of_hasLaw_uniformSphereVector
    {m : Type*} [Fintype m] {u : m → Ω → n → ℝ} (hind : iIndepFun u μ)
    (hu : ∀ j, HasLaw (u j) (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ u j ω)‖ ^ 2) / Fintype.card m -
        Fintype.card k / Fintype.card n|} ≤
      2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  have := hind.isProbabilityMeasure
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card m)).eq_or_lt with hm | hm
  · rw [← hm]
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans (by norm_num)
  have hg : ∀ j : m, Measurable fun x : n → ℝ =>
      ‖WithLp.toLp 2 (Vᴴ *ᵥ x)‖ ^ 2 - (Fintype.card k / Fintype.card n : ℝ) := fun _ => by
    fun_prop
  have hs := HasSubgaussianMGF.sum_of_iIndepFun (hind.comp _ hg) (s := Finset.univ)
    fun j _ => hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector
      (hu j) hV
  refine le_of_eq_of_le ?_ ((hs.measureReal_abs_ge_le (t := Fintype.card m * τ)
    (by positivity)).trans_eq ?_)
  · congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Function.comp_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ u j ω)‖ ^ 2) / (Fintype.card m : ℝ) -
        Fintype.card k / Fintype.card n = ((∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ u j ω)‖ ^ 2) -
        Fintype.card m * (Fintype.card k / Fintype.card n)) / Fintype.card m by field_simp,
      abs_div, abs_of_pos hm, le_div_iff₀ hm, mul_comm]
  · rw [NNReal.coe_sum]
    simp only [coe_nnnorm, Real.norm_of_nonneg (by positivity :
      (0 : ℝ) ≤ 1 / (2 * (Fintype.card n + 2))), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    congr 2
    field_simp

end NLAlib
