/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisection
public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.Matrix.Computation.NewtonSchulzSign

/-!
# Deterministic analysis of randomized spectral bisection (scaffold)

Statements for `NLAlib/Matrix/Computation/SpectralBisection.lean` (stage HDIAG, wave W4, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.8): the local guarantee of one
node of the machine algorithm, read through the decoding, given its good events and the
guarantees of its children ([Shah2024, Lemma 4.1]), the depth
of the recursion, the number of nodes and of splits, and the global deterministic guarantee: if
every internal node of the recursion tree has a good sample, the output is an approximate
diagonalization with residual $2\varepsilon R_0$ and singular values of $\mathbf{U}$ in
$[1 - \varepsilon/3, 1 + \varepsilon/3]$. The probability is in
`NLAlibScaffold/Eigensolvers/SpectralBisection.lean`.

## Main results

* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le`: the computed
  projectors.
* `NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`: rank recovery.
* `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split`:
  frames, deflated bases and compressions at a split.
* `NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some`: the child
  invariant.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`:
  Lemma 4.1.
* `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`: the depth.
* `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params`: the parameters of the nodes.
* `NLAlib.FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le`,
  `NLAlib.encard_eighNodeAt_isSplit_le`: the counts.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`: the
  global deterministic guarantee.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib


/-- **The computed spectral projectors are accurate on Event I**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub` (without the leaf test
and the size condition), for a seed $v \in [-1, 1]$ whose ideal shift $c' = (R/\ell)v$ is at
distance at least $w$ from every eigenvalue of $\mathbf{A}$, the stored projectors of
`NLAlib.eighStep`, $\mathbf{P}_+ = (\mathbf{B} + \mathbf{I})/2$ and $\mathbf{P}_- =
-(\mathbf{B} - \mathbf{I})/2$ with $\mathbf{B}$ the Newton–Schulz sign of the stored shifted
matrix, are within $\beta$ of $\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} -
c'\mathbf{I}))$. [Shah2024, proof of Lemma 4.1], (4.4)–(4.9).
Proof: the stored shift $c = \mathrm{unif}(\mathrm{fl}(R/\mathrm{fl}(\ell)), v)$ has
$|c - c'| \le 0.15uR + 2u\tau \le 0.33uR$ ($\tau \le \sqrt{\rho/2}/(4k^{3/2}) \le 1/16$ and
$\tau \le \varepsilon R_0/(4k^{3/2})$, so $\mathrm{fl}(\ell)$ is a relative rounding), and
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le` adds $1.051uR$: the stored
shifted matrix is within $1.4uR$ of $\mathbf{A} - c'\mathbf{I}$, whose eigenvalues have modulus
$\ge w$; by Weyl (`Matrix.IsHermitian.abs_eigenvalue_sub_le`) its eigenvalues have modulus
$\ge a := w - 1.4uR$. Apply
`NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le` with this
$a$ and $b' = \mathrm{fl}(2R) \in [2R(1 - u), 2R(1 + u)]$: $a/b' \ge w/(4R)$ and
$N(a/(2b'), \beta/(16k)) \le N(w/(8R), \beta/(16k))$ (`NLAlib.newtonSchulzSteps_le_of_le_abs`), so
`husign` and `hfuel` give its hypotheses with a factor-2 margin; the modulus $w/2$ would not.
`Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le` moves the sign from the stored to the ideal
shift ($2.8uR/w$); the shift by $\mp1$ and the division by $\mathrm{fl}(2)$ cost
$1.05u + 1.01u\sqrt k + 2ku\tau$
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le`,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermScale_le`,
`NLAlib.FloatMachine.IsAccurate.decodeMatrix_negMat`). Total $\le \beta/2 + 2.8uR/w + 1.05u +
1.01u\sqrt k + 2ku\tau \le 0.51\beta$. M, about 100 lines. -/
theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    {smp : EighSample ℝ ℂ N} (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    specNorm (decodeMatrix dec (M.hermScale (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)) -
      (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)))) ≤ dec β ∧
    specNorm (decodeMatrix dec (M.hermScale (M.negMat (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) M.one)) (M.ofNat 2)) -
      (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)))) ≤ dec β := by
  sorry

private theorem abs_sub_le_of_isRoundingOf_aux {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha : |a| ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : |a - z| ≤ u * (|a| + τ) := by
  have hmax : max |a| τ ≤ |a| + τ := max_le (by linarith) (by linarith [abs_nonneg a])
  exact (h ha).trans (mul_le_mul_of_nonneg_left hmax hu)

private theorem newtonSchulzSteps_nonneg_aux {s ε : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2) : 0 ≤ newtonSchulzSteps s ε := by
  have h₁ : 0 ≤ Real.logb 2 (min |s| (1 / 2))⁻¹ := by
    rw [abs_of_pos hs, min_eq_left hs₁]
    exact Real.logb_nonneg one_lt_two (one_le_inv₀ hs |>.mpr (by linarith))
  have h₂ : 0 ≤ Real.logb 2 (Real.logb 2 ε⁻¹) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [← Real.logb_self_eq_one one_lt_two]
    exact Real.logb_le_logb_of_le one_lt_two two_pos ((le_inv_comm₀ two_pos hε).mpr (by linarith))
  unfold newtonSchulzSteps
  linarith

private theorem toNat_add_traceRe_div_eq_aux {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) {k : ℕ} (hk1 : (1 : ℝ) ≤ k) (hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000)
    (hkτ : (k : ℝ) * τ ≤ 1 / 4) (hΩ : 16 * k ≤ Ω) (X : Matrix (Fin k) (Fin k) (F × F)) {r : ℕ}
    (hrk : (r : ℝ) ≤ k) (hdiag : |∑ i, dec (X i i).1 - r| ≤ 1 / 57600)
    (hsabs : ∑ i, |dec (X i i).1| ≤ 2 * k) :
    M.toNat (M.add (M.traceRe X) (M.div M.one (M.ofNat 2))) = r := by
  have hkk : (k : ℝ) ≤ k ^ 2 := by nlinarith
  have hku : (k : ℝ) * u ≤ 1 / 100000 := by linarith [mul_le_mul_of_nonneg_right hkk hu]
  have hu1 : u ≤ 1 / 100000 := by linarith [mul_le_mul_of_nonneg_right hk1 hu]
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  -- the rounded trace
  have htrace := abs_le.mp (hM.abs_sum_sub_traceRe_le hu hτ₀ (by linarith) X (by linarith))
  have htr2 := mul_le_mul_of_nonneg_left (by linarith : ∑ i, |dec (X i i).1| + k * τ ≤ 3 * k)
    (by positivity : (0 : ℝ) ≤ 2 * k * u)
  have hdiag' := abs_le.mp hdiag
  -- the rounded half
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.ofNat 2)
    (by norm_num; linarith) hu hτ₀)
  push_cast at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have hd2 : 1.9 ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2.1 := by constructor <;> linarith
  have hd20 : 0 < dec (M.ofNat 2) := by linarith
  have hh2 : 1 / dec (M.ofNat 2) ≤ 1 := by rw [div_le_one hd20]; linarith
  have hh := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.div M.one (M.ofNat 2) hd20.ne')
    (by rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)]; linarith) hu hτ₀)
  rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)] at hh
  have hh1 : |1 / dec (M.ofNat 2) - 1 / 2| ≤ u := by
    rw [div_sub_div _ _ hd20.ne' (by norm_num), abs_div, abs_of_pos (mul_pos hd20 two_pos),
      div_le_iff₀ (mul_pos hd20 two_pos), abs_le]
    have := mul_le_mul_of_nonneg_left hd2.1 hu
    constructor <;> linarith
  have hh1' := abs_le.mp hh1
  have := mul_le_mul_of_nonneg_left hh2 hu
  have hdh : |dec (M.div M.one (M.ofNat 2)) - 1 / 2| ≤ 3 * u := by
    rw [abs_le]; constructor <;> linarith
  have hdh' := abs_le.mp hdh
  -- their rounded sum
  have hzabs : |dec (M.traceRe X) + dec (M.div M.one (M.ofNat 2))| ≤ k + 1 := by
    rw [abs_le]; constructor <;> linarith
  have hz := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.add (M.traceRe X)
    (M.div M.one (M.ofNat 2))) (by linarith) hu hτ₀)
  have hzu := mul_le_mul_of_nonneg_left hzabs hu
  rw [hM.toNat_eq, Nat.floor_eq_iff (by linarith)]
  constructor <;> linarith

private theorem bisection_small_aux {u τ ρ w R ε β μ X : ℝ} {k ℓ : ℕ} (hk : 1 ≤ k)
    (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hρ₁ : ρ ≤ 1) (hw : 0 < w)
    (hwR : w ≤ R) (hβ : 0 < β) (hβtol : β ≤ bisectionSignTol k ε ρ ℓ) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (husign : 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u ≤ w / (4 * R) * β)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * k * √(k : ℝ)) ≤ min (√(ρ / 2)) X) :
    (k : ℝ) * β ≤ 1 / 57600 ∧ (k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (k : ℝ) * τ ≤ 1 / 4 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hsq := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) k)
  have hkk : (k : ℝ) ≤ k * √(k : ℝ) := le_mul_of_one_le_right (by linarith) hsq1
  have hR0 : 0 < R := hw.trans_le hwR
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  -- the accuracy, the roundoff and the floor are small
  have hβk : β * (k * √(k : ℝ)) ≤ 1 / 57600 := by
    refine (mul_le_mul_of_nonneg_right hβtol (by positivity)).trans ?_
    unfold bisectionSignTol
    have hX : (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) ≤ 1 / 800 := by
      have : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith [div_pos one_pos (by linarith : (0 : ℝ) < ℓ)]
    have hX0 : 0 ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) := by
      have : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact div_nonneg (mul_nonneg (by linarith) hε.le) (by positivity)
    have hρ' : √ρ ≤ 1 := Real.sqrt_le_one.mpr hρ₁
    have hL := Real.sqrt_nonneg (2 * Real.log (4 / ρ))
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul hX hρ' (Real.sqrt_nonneg _) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ k * √(k : ℝ))
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k) hL]
  have hNs := newtonSchulzSteps_nonneg_aux (s := w / (8 * R)) (ε := β / (16 * k))
    (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hw4 : w / (4 * R) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hku3 : k * √(k : ℝ) * u ≤ β / 20480 := by
    have h1 : 5120 * (k * √(k : ℝ)) * u ≤ 640 * k * √(k : ℝ) * (8 + μ) *
        (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u := by
      have := mul_le_mul (by linarith : (8 : ℝ) ≤ 8 + μ) (by linarith : (1 : ℝ) ≤
        newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) zero_le_one
        (by linarith)
      have h0 : 0 ≤ 640 * (k * √(k : ℝ)) * u := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_right hw4 hβ.le
    linarith
  have hkk1 : (1 : ℝ) ≤ k * √(k : ℝ) := hk1.trans hkk
  have hβ1 : β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_left hkk1 hβ.le]
  have hku : (k : ℝ) * u ≤ 1 / 2 := by linarith [mul_le_mul_of_nonneg_right hkk hu]
  have hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have : (k : ℝ) ^ 2 * u = (k * √(k : ℝ) * u) * √(k : ℝ) := by
      rw [pow_two]; nth_rewrite 1 [← hsq]; ring
    rw [this]
    have h1 := mul_le_mul_of_nonneg_right hku3 (Real.sqrt_nonneg (k : ℝ))
    have h2 : β * √(k : ℝ) ≤ β * (k * √(k : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hk1) hβ.le
    linarith
  have hkβ : (k : ℝ) * β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_left hkk hβ.le]
  have hkτ : (k : ℝ) * τ ≤ 1 / 4 := by
    have : √(ρ / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have := hτ.trans (min_le_left _ _)
    linarith [mul_le_mul_of_nonneg_right hkk hτ₀]
  exact ⟨hkβ, hk2u, hkτ⟩

/-- **Rank recovery on Event I**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`
(contracts, precision, step limit, floor and range), for an internal node ($k \ge 2$, $R >
\varepsilon R_0$) and a seed $v \in [-1, 1]$ whose ideal shift $c' = (R/\ell)v$ is at distance at
least $w$ from every eigenvalue (Event I), the node's step splits exactly when $0 < i_+(\mathbf{A}
- c'\mathbf{I}) < k$; moreover then $k_+ = i_+(\mathbf{A} - c'\mathbf{I})$. [Shah2024, proof of
Lemma 4.1], "the estimates $k_\pm$ are the exact ranks".
Proof: `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le` puts the
stored $\mathbf{P}_+$ within $\beta$ of the true projector (there the rounded shift is within
$1.4uR$ of $\mathbf{A} - c'\mathbf{I}$ and the sign is applied with modulus $a = w - 1.4uR$, not
$w/2$, which `husign` would not cover; $\tau \le \sqrt{\rho/2}/(4k^{3/2}) \le 1/16$); its
diagonal sum is within $k\beta$ of the trace
(`NLAlib.norm_apply_le_specNorm`), which is the inertia
(`Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign`); with the rounded sum
(`NLAlib.FloatMachine.IsAccurate.abs_sum_sub_traceRe_le`) the rounded trace is within
$k\beta + 2.2k^2u + (k + 1.5)u < 1/4$ of the inertia, so $\mathrm{fl}(t +
\mathrm{fl}(1/2))$ lies in $(r + 1/4, r + 3/4)$ for the inertia $r$ and its floor (`toNat_eq`,
`Nat.floor_eq_iff`) is $r$; unfold `NLAlib.eighStep`. M, about 60 lines. -/
theorem FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) {smp : EighSample ℝ ℂ N}
    (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp).IsSplit ↔
      0 < inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ∧
      inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) < y.k := by
  set r := inertiaPos (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) with hr
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  -- the accuracy, the roundoff and the floor are small
  obtain ⟨hkβ, hk2u, hkτ⟩ := bisection_small_aux (by omega) hℓ hε hε₁ hρ₁ hw hwR hβ hβtol
    hμM hu husign hτ₀ hτ
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  -- the computed projector is near the ideal one, whose trace is the inertia
  obtain ⟨hP, -⟩ := hM.specNorm_sub_decodeMatrix_eighProjectors_le (N := N)
    (signFuel := signFuel) (R₀ := R₀) hμM hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol
    husign hfuel hτ₀ hτ hΩ hv hI
  set Pp := M.hermScale (M.hermShift (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)
    with hPp
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  have hS : specNorm S ≤ 1 := by
    refine Matrix.IsHermitian.specNorm_cfc_le (hA.sub ?_) zero_le_one fun x _ => ?_
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
    · rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul]
    have := (specNorm_add_le 1 S).trans (add_le_add specNorm_one_le hS)
    rw [abs_of_pos (by norm_num)]
    linarith
  have htr := hA.re_trace_smul_one_add_cfc_sign (c := dec y.R / y.ℓ * smp.1) fun x hx h => by
    have := hI x hx
    rw [h, sub_self, abs_zero] at this
    linarith
  rw [← hr] at htr
  have hentry : ∀ i, |dec (Pp i i).1 - RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i)| ≤ dec β := by
    intro i
    have h := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm (decodeMatrix dec Pp - (2⁻¹ : ℝ) • (1 + S)) i i).trans hP)
    simpa [decodeMatrix, decodeComplex] using h
  have hentry' : ∀ i, |dec (Pp i i).1| ≤ 1 + dec β := by
    intro i
    have h1 := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm ((2⁻¹ : ℝ) • (1 + S)) i i).trans hPid)
    have h2 := abs_sub_abs_le_abs_sub (dec (Pp i i).1) (RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i))
    linarith [hentry i]
  have hdiag : |∑ i, dec (Pp i i).1 - r| ≤ y.k * dec β := by
    rw [← htr, Matrix.trace, map_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry i
  have hsabs : ∑ i, |dec (Pp i i).1| ≤ y.k * (1 + dec β) := by
    rw [mul_add, mul_one]
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry' i
  have hrk : (r : ℝ) ≤ y.k := by
    have : r ≤ y.k := by
      rw [hr, inertiaPos]
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hβ2 : 1 + dec β ≤ 2 := by linarith
  have hk2 := mul_le_mul_of_nonneg_left hβ2 (Nat.cast_nonneg (α := ℝ) y.k)
  have hfl := toNat_add_traceRe_div_eq_aux hM hu hτ₀ hk1 hk2u hkτ
    (by linarith [Real.sqrt_nonneg (Real.log (4 / ρ))]) Pp hrk (hdiag.trans (by linarith))
    (hsabs.trans (by linarith))
  have hkp : min y.k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))) = r := by
    rw [hfl]; exact min_eq_right (by exact_mod_cast hrk)
  -- unfold the step
  unfold eighStep
  rw [if_neg (by omega), if_neg (by simp [hint])]
  dsimp only
  rw [hPp] at hkp
  clear_value r
  split_ifs with h1 h2
  · rw [hkp] at h1
    exact iff_of_false id (by rw [h1]; exact fun h => h.2.false)
  · rw [hkp] at h2
    exact iff_of_false id (by rw [h2]; exact fun h => h.1.false)
  · rw [hkp] at h1 h2
    exact iff_of_true trivial ⟨Nat.pos_of_ne_zero h2, lt_of_le_of_ne (by exact_mod_cast hrk) h1⟩

/-- **The children of a good node satisfy the node invariant**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` (without
the children's guarantee), every child $y'$ of the node (`NLAlib.eighChild`) has a Hermitian matrix
with $\|\mathbf{A}'\|_2 \le R'$, its own window. [Shah2024, proof of Lemma 4.1], (4.10)–(4.13).
Proof: leaves have no child. A shift child (all eigenvalues on one side of $c'$, by
`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub` and the inertia) has
spectrum of $\mathbf{A} \mp (R/2)\mathbf{I}$ in $[-(1/2 + 1/\ell)R, (1/2 + 1/\ell)R]$ since $\lvert
c'\rvert \le R/\ell$; the diagonal rounding
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le`,
`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`) gives $\|\mathbf{A}'\|_2 \le
(1/2 + 1/\ell)R + 1.06uR$ against $R' \ge (1/2 + 2/\ell)R - 2.5uR$ (`NLAlib.eighNextParams`). A
split child: Hermitian by `NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`; for
the norm,
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split`
gives the compression
$\mathbf{W}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V}\mathbf{W}$ with spectrum in
$[c', R]$ (resp. $[-R, c']$), so its shift by $\mp\sigma$ has norm at most $(1/2 + 1/\ell)R + 3uR$,
and the child within $(2 + 2\eta)R\eta \le 0.06R/\ell$ of it. M, about 60 lines. -/
theorem FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hudefl : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y smp)
    {b : Bool} {y' : EighNode F} (hy' : eighChild M N signFuel R₀ β y smp b = some y') :
    (decodeMatrix dec y'.A).IsHermitian ∧ specNorm (decodeMatrix dec y'.A) ≤ dec y'.R := by
  sorry

/-- **A split node: frames, deflated bases and compressions**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some`, if the node's
step (`NLAlib.eighStep`) is a split with sizes $k_+$, $k - k_+$, bases $\mathbf{Q}_\pm$, stored
children $\mathbf{A}_\pm$ and stored shift $\sigma$, then $\sigma$ is within $3u$ (relative) of
$R/2$ and, with $\eta = (1 - 1/\ell)\varepsilon/(5\ell)$ and $c' = (R/\ell)v$, each side has an
orthonormal frame $\mathbf{V}$ of the true spectral projector
$\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c'\mathbf{I}))$ whose compression has
spectrum in $[c', R]$ (resp. $[-R, c']$), a unitary $\mathbf{W}$ with
$\|\mathbf{V}\mathbf{W} - \mathbf{Q}_\pm\|_2 \le \eta$, and
$\|\mathbf{A}_\pm - (\mathbf{W}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V}\mathbf{W}
\mp \sigma\mathbf{I})\|_2 \le (2 + 2\eta)R\eta$. [Shah2024, proof of Lemma 4.1], (4.10)–(4.13).
(The shift bound is $3u$ rather than $u$: $\mathrm{fl}(2)$ is a rounded conversion.)
Proof: the split and the ranks come from
`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`'s argument, here via
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le` and the inertia;
the frames from `Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq` (for the minus
side applied to $-\mathbf{A}$, $-c'$, with `NLAlib.inertiaNeg_eq_inertiaPos_neg` and
`Matrix.IsHermitian.inertiaPos_add_inertiaNeg` to identify $k - k_+$); deflation by
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` with
$\mathbf{S} = \mathbf{I}_r$ ($6m\beta \le (2 + \beta)\eta/3 \le 0.67\eta$; its floor and range
hypotheses from `hτ` and `hΩ`, $\tau\sqrt k \le x/4$, $2(1 + \beta)t \le \Omega$); the compressions
through `NLAlib.FloatMachine.IsAccurate.decodeMatrix_conjTransposeMat`, the product contract,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le`,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le` and
`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`. L, about 150 lines. -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hudefl : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y smp)
    {kp : ℕ} {hkp : kp ≤ y.k} {Qp : Matrix (Fin y.k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (F × F)} {σ : F}
    (hsplit : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp = .split kp hkp Qp Qm Ap Am σ) :
    |dec σ - dec y.R / 2| ≤ 3 * u * (dec y.R / 2) ∧
    (∃ V : Matrix (Fin y.k) (Fin kp) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec y.A -
          (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) ∧
      spectrum ℝ (Vᴴ * decodeMatrix dec y.A * V) ⊆ Set.Icc (dec y.R / y.ℓ * smp.1) (dec y.R) ∧
      ∃ W : Matrix (Fin kp) (Fin kp) ℂ, HasOrthonormalCols W ∧
        specNorm (V * W - decodeMatrix dec Qp) ≤ ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) ∧
        specNorm (decodeMatrix dec Ap - (Wᴴ * (Vᴴ * decodeMatrix dec y.A * V) * W -
          dec σ • (1 : Matrix (Fin kp) (Fin kp) ℂ))) ≤
            (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
              ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) ∧
    (∃ V : Matrix (Fin y.k) (Fin (y.k - kp)) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec y.A -
          (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) ∧
      spectrum ℝ (Vᴴ * decodeMatrix dec y.A * V) ⊆ Set.Icc (-dec y.R) (dec y.R / y.ℓ * smp.1) ∧
      ∃ W : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) ℂ, HasOrthonormalCols W ∧
        specNorm (V * W - decodeMatrix dec Qm) ≤ ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) ∧
        specNorm (decodeMatrix dec Am - (Wᴴ * (Vᴴ * decodeMatrix dec y.A * V) * W +
          dec σ • (1 : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) ℂ))) ≤
            (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
              ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) := by
  sorry

/-- **Local guarantee of a node of spectral bisection** (Lemma 4.1): let the machine meet
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with $u \ge 0$ and constants
$\mu_{\mathrm{MM}}(k), \mu_{\mathrm{QR}}(k), c_{\mathrm N} \ge 0$. Let the node $y$ have a stored
matrix with Hermitian decoding $\mathbf{A}$ of size $k$, $\|\mathbf{A}\|_2 \le R$, $\ell \ge 20$,
$0 < \varepsilon \le 1/8$ (decoded stored values), let $R_0 > 0$, $0 < \rho \le 1$,
$0 < w \le R$, the stored accuracy $\beta$ with $0 < \beta \le$ `NLAlib.bisectionSignTol` $k$
$\varepsilon$ $\rho$ $\ell$, and $N_y = N(w/(8R), \beta/(16k))$ (`NLAlib.newtonSchulzSteps`).
Suppose
$$640\,k^{3/2}(8 + \mu_{\mathrm{MM}}(k))(N_y + 1)\,u \le \frac{w}{4R}\,\beta \,, \qquad
(4\mu_{\mathrm{QR}}(k) + 4\sqrt k(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(k) + 1)\,u \le \beta
\,,$$
the sign step limit is at least $N_y$, $0 \le \tau$,
$4k^{3/2}\tau \le \min(\sqrt{\rho/2}, \varepsilon R_0)$ and
$16(R_0 + R + k + \ell + \sqrt{\log(4/\rho)}) \le \Omega$; that, when $k \ge 2$ and the
machine's leaf test $R \le \mathrm{fl}(\varepsilon R_0)$ fails, the
node's sample satisfies `NLAlib.IsEighGoodSample` with $w$, $x = \sqrt{\rho/2}/k$ and
$t = \sqrt2(2\sqrt k + \sqrt{2\log(4/\rho)})$; and that every child $y'$ of the node returns an
approximate diagonalization of its matrix with residual $\varepsilon'(R' + R_0)$ and singular
values within $\varepsilon'/3$ of $1$ (its own tolerance and window). Then the node returns an
approximate diagonalization (`NLAlib.IsApproxDiagonalization`) of $\mathbf{A}$ with residual
$\varepsilon(R + R_0)$ and singular values within $\varepsilon/3$ of $1$. [Shah2024, Lemma 4.1],
there with the probabilities of the events folded in, $R_0$-free bounds on the children's
$\|\mathbf{D}_\pm\|_2$ (the $R_0$ part is absorbed by the slack $\varepsilon R_0/\ell$), and
Events I–III as conditions.
Proof: unfold `NLAlib.eighAux` and `NLAlib.eighStep`. Leaves: $k \le 1$ is exact; on the
test-true leaf $R \le \mathrm{fl}(\varepsilon R_0)$ the residual is $\|\mathbf{A}\|_2 \le R \le
\varepsilon R_0(1 + u)$, and $uR_0 \le R$ when $R > \varepsilon R_0$ since $u < \varepsilon$. Note
$\tau \le \sqrt{\rho/2}/(4k^{3/2}) \le 1/16$ (SN4's $2k\tau \le 1$; $\mathrm{fl}(\ell)$ relative).
Otherwise follow [Shah2024, proof of Lemma 4.1]: the branch is the true one
(`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`), with
$\|\mathbf{P}_\pm - \mathbf{\Pi}_\pm\|_2 \le \beta$ from
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le`; the children satisfy
the node invariant
(`NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some`); on a split,
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split`
gives the frames $\mathbf{V}_\pm$, unitaries $\mathbf{W}_\pm$ with
$\|\mathbf{Q}_\pm - \mathbf{V}_\pm\mathbf{W}_\pm\|_2 \le \eta$ and the compressions; replace
$\mathbf{V}_\pm$ by $\mathbf{V}_\pm\mathbf{W}_\pm$ (assembly through
`NLAlib.FloatMachine.IsAccurate.decodeMatrix_conjTransposeMat`,
`NLAlib.FloatMachine.IsAccurate.decodeMatrix_identityMat`,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le` and the product contract).
The children's window and tolerance are the machine's `NLAlib.eighNextParams`: $R' \le (1/2 +
2/\ell)R(1 + \delta)$ and $(1 - 1/\ell)\varepsilon(1 - \delta) \le \varepsilon' \le (1 -
1/\ell)\varepsilon(1 + \delta)$ with $\delta \le 4u + u\tau/\varepsilon$ (each `ofNat`, `div`,
`add`/`sub`, `mul` one rounding, `IsRoundingOf`). The source's estimates are too loose at
$\varepsilon' = 1/8$; use this budget ($\eta = \varepsilon'/(5\ell)$; `husign` gives $u \le
10^{-13}\varepsilon\theta^{3/2}$, so every $u$-term is $< 0.01R\varepsilon'$):
$\|\mathbf{X}_\pm\|_2 \le \eta(1 + \varepsilon'/3)(1 + \mu u/\eta) \le 1.044\eta$ (not the source's
$(1 + 2\varepsilon')$), $\|\mathbf{D}_\pm\|_2 \le (R'(1 + \varepsilon') + \varepsilon'R_0)/(1 -
\varepsilon'/3)^2$, the term (4.21) on both sides $\le 5.4R\eta + 4.8\varepsilon'R_0\eta$ (the
source undercounts it), (4.20) $\le 2R\eta$, (4.18) $\le 0.334R\varepsilon'$; the residual is at
most $$\varepsilon'\Bigl[\Bigl(\frac12 + \frac2\ell\Bigr)(1 + \delta)^2 + 0.334 +
\frac{1.48}{\ell}\Bigr]R + \varepsilon'\Bigl(1 + \delta + \frac{0.12}{\ell}\Bigr)R_0 \le
\varepsilon(R + R_0) \,,$$
which closes only **using $\varepsilon' = (1 - 1/\ell)\varepsilon$** (the source never needs the
factor): $(1 - 1/\ell)(0.834 + 3.48/\ell) \le 0.958$ at $\ell = 20$, decreasing in $\ell$ (a
margin of 4.3 %). Singular values: $\varepsilon'/3 + \sqrt2 \cdot 1.044\eta \le (1 +
0.89/\ell)\varepsilon'/3$ and $(1 + 0.89/\ell)(1 - 1/\ell)(1 + \delta) \le 1$. Split into private
lemmas: assembly of $\mathbf{U}$, singular values, residual. H, about 150 lines. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hudefl : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3)) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  sorry

/-- A rounding of a nonnegative number in range, with the floor as an absolute term. -/
private lemma le_and_le_of_isRoundingOf {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha0 : 0 ≤ a) (ha : a ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) :
    a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) := by
  have h1 := (h (by rwa [abs_of_nonneg ha0])).trans
    (mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (abs_nonneg _) hτ) hu)
  rw [abs_of_nonneg ha0] at h1
  constructor <;> linarith [(abs_le.mp h1).1, (abs_le.mp h1).2]

/-- The real arithmetic of the next window of `NLAlib.eighNextParams`. -/
private lemma le_of_isRoundingOf_eighNextParams_fst {u τ Ω m t L a1 a2 c p1 r : ℝ}
    (hu : 0 ≤ u) (hum : 25 * m ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * m ≤ Ω) (hr : 0 ≤ r) (hrΩ : r ≤ Ω)
    (ht : IsRoundingOf u τ Ω 2 t) (hL : IsRoundingOf u τ Ω m L)
    (ha1 : t ≠ 0 → IsRoundingOf u τ Ω (1 / t) a1) (ha2 : L ≠ 0 → IsRoundingOf u τ Ω (t / L) a2)
    (hc : IsRoundingOf u τ Ω (a1 + a2) c) (hp1 : IsRoundingOf u τ Ω (c * r) p1) :
    p1 ≤ (1 / 2 + 2 / m) * (1 + 22 * u) * r + u * τ := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have huw : 25 * u ≤ w ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hum (sq_nonneg w)
    have h' : w ^ 2 * (25 * m ^ 2 * u) = 25 * u * (w * m) ^ 2 := by ring
    rw [h', hwm] at h; linarith
  have hww : w ^ 2 ≤ w / 20 := by
    have := mul_le_mul_of_nonneg_left hw20 hw0.le; rw [sq]; linarith
  have hu' : u ≤ w / 500 := by linarith
  have hu1 : u ≤ 1 / 10000 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huu : u * u ≤ u / 10000 := by have := mul_le_mul_of_nonneg_left hu1 hu; linarith
  have huu0 : 0 ≤ u * u := mul_nonneg hu hu
  have huw' : u * w ≤ u / 20 := by have := mul_le_mul_of_nonneg_left hw20 hu; linarith
  have huw0 : 0 ≤ u * w := mul_nonneg hu hw0.le
  have hum1 : u * (w * m) = u := by rw [hwm, mul_one]
  have hum' : u * m ≤ 1 / 500 := by
    have := mul_le_mul_of_nonneg_right hu' hm0.le
    have h2 : w / 500 * m = (w * m) / 500 := by ring
    rw [h2, hwm] at this; linarith
  have hwuτ : w * (u * τ) ≤ u * τ := mul_le_of_le_one_left huτ0 (by linarith)
  -- the stored `2` and `ℓ`
  obtain ⟨ht1, ht2⟩ := rnd ht (by norm_num) (by linarith)
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hwL1 : 1 - 2 * u ≤ w * L := by
    have := mul_le_mul_of_nonneg_left hL1 hw0.le; linarith
  have hwL2 : w * L ≤ 1 + 2 * u := by
    have := mul_le_mul_of_nonneg_left hL2 hw0.le; linarith
  -- `fl(1/2)`
  have hit1 : 1 / t ≤ 1 / 2 + u := by
    rw [div_le_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left (by linarith : 2 - 3 * u ≤ t) (by linarith : 0 ≤ 1 / 2 + u)
    linarith
  have hit2 : 1 / 2 - u ≤ 1 / t := by
    rw [le_div_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left (by linarith : t ≤ 2 + 3 * u) (by linarith : 0 ≤ 1 / 2 - u)
    linarith
  obtain ⟨ha11, ha12⟩ := rnd (ha1 ht0.ne') (one_div_nonneg.mpr ht0.le) (by linarith)
  have hut := mul_le_mul_of_nonneg_left hit1 hu
  have hA1 : a1 ≤ 1 / 2 + 3 * u := by linarith
  have hA1' : 1 / 2 - 3 * u ≤ a1 := by linarith
  -- `fl(2/ℓ)`
  have hq1 : t / L ≤ (2 + 8 * u) * w := by
    rw [div_le_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL1 (by linarith : 0 ≤ 2 + 8 * u)
    linarith
  have hq0 : 0 ≤ t / L := div_nonneg ht0.le hL0.le
  have hq5 : t / L ≤ 1 / 5 := by linarith
  obtain ⟨ha21, ha22⟩ := rnd (ha2 hL0.ne') hq0 (by linarith)
  have huq := mul_le_mul_of_nonneg_left hq5 hu
  have huq0 := mul_nonneg hu hq0
  have hA2 : a2 ≤ 2 * w + 2 * u := by linarith
  have hA2' : -2 * u ≤ a2 := by linarith
  -- `fl(fl(1/2) + fl(2/ℓ))`
  obtain ⟨hc1, hc2⟩ := rnd hc (by linarith) (by linarith)
  have huS := mul_le_mul_of_nonneg_left (by linarith : a1 + a2 ≤ 61 / 100) hu
  have huS0 := mul_nonneg hu (by linarith : (0 : ℝ) ≤ a1 + a2)
  have hC : c ≤ (1 / 2 + 2 * w) * (1 + 14 * u) := by linarith
  have hC0 : 0 ≤ c := by linarith
  have hC1 : c ≤ 1 := by linarith
  obtain ⟨-, hp⟩ := rnd hp1 (mul_nonneg hC0 hr) (by linarith [mul_le_of_le_one_left hr hC1])
  have hK : 0 ≤ (1 / 2 + 2 * w) * r := mul_nonneg (by linarith) hr
  have h22 : (1 + 14 * u) * (1 + u) ≤ 1 + 22 * u := by linarith
  have hcr : c * r ≤ (1 / 2 + 2 * w) * (1 + 14 * u) * r := mul_le_mul_of_nonneg_right hC hr
  have h1 := mul_le_mul_of_nonneg_right hcr (by linarith : (0 : ℝ) ≤ 1 + u)
  have h2 := mul_le_mul_of_nonneg_left h22 hK
  have : (2 : ℝ) / m = 2 * w := by rw [hw_def]; ring
  rw [this]
  linarith

/-- The real arithmetic of the next tolerance of `NLAlib.eighNextParams`. -/
private lemma le_and_le_of_isRoundingOf_eighNextParams_snd {u τ Ω m L e1 d p2 e : ℝ}
    (hu : 0 ≤ u) (hum : 25 * m ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * m ≤ Ω) (he : 0 ≤ e) (he₁ : e ≤ 1) (hL : IsRoundingOf u τ Ω m L)
    (he1 : L ≠ 0 → IsRoundingOf u τ Ω (1 / L) e1) (hd : IsRoundingOf u τ Ω (1 - e1) d)
    (hp2 : IsRoundingOf u τ Ω (d * e) p2) :
    (1 - 1 / m) * (1 - 9 * u) * e - u * τ ≤ p2 ∧ p2 ≤ (1 - 1 / (2 * m)) * e + u * τ := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have huw : 25 * u ≤ w ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hum (sq_nonneg w)
    have h' : w ^ 2 * (25 * m ^ 2 * u) = 25 * u * (w * m) ^ 2 := by ring
    rw [h', hwm] at h; linarith
  have hww : w ^ 2 ≤ w / 20 := by
    have := mul_le_mul_of_nonneg_left hw20 hw0.le; rw [sq]; linarith
  have hu' : u ≤ w / 500 := by linarith
  have hu1 : u ≤ 1 / 10000 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huu : u * u ≤ u / 10000 := by have := mul_le_mul_of_nonneg_left hu1 hu; linarith
  have huu0 : 0 ≤ u * u := mul_nonneg hu hu
  have huw' : u * w ≤ u / 20 := by have := mul_le_mul_of_nonneg_left hw20 hu; linarith
  have huw0 : 0 ≤ u * w := mul_nonneg hu hw0.le
  have hum1 : u * (w * m) = u := by rw [hwm, mul_one]
  have hum' : u * m ≤ 1 / 500 := by
    have := mul_le_mul_of_nonneg_right hu' hm0.le
    have h2 : w / 500 * m = (w * m) / 500 := by ring
    rw [h2, hwm] at this; linarith
  have hwuτ : w * (u * τ) ≤ u * τ := mul_le_of_le_one_left huτ0 (by linarith)
  -- the stored `2` and `ℓ`
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have hL0 : 0 < L := by linarith
  have hwL1 : 1 - 2 * u ≤ w * L := by
    have := mul_le_mul_of_nonneg_left hL1 hw0.le; linarith
  have hwL2 : w * L ≤ 1 + 2 * u := by
    have := mul_le_mul_of_nonneg_left hL2 hw0.le; linarith
  -- `fl(1/ℓ)` and `fl(1 - fl(1/ℓ))`
  have hiL1 : 1 / L ≤ (1 + 3 * u) * w := by
    rw [div_le_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL1 (by linarith : 0 ≤ 1 + 3 * u)
    linarith
  have hiL2 : (1 - 3 * u) * w ≤ 1 / L := by
    rw [le_div_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL2 (by linarith : 0 ≤ 1 - 3 * u)
    linarith
  have hiL0 : 0 ≤ 1 / L := one_div_nonneg.mpr hL0.le
  have hiL10 : 1 / L ≤ 1 / 10 := by linarith
  obtain ⟨he11, he12⟩ := rnd (he1 hL0.ne') hiL0 (by linarith)
  have huL := mul_le_mul_of_nonneg_left hiL10 hu
  have huL0 := mul_nonneg hu hiL0
  have hE1 : e1 ≤ w + 2 * u := by linarith
  have hE1' : w - 2 * u ≤ e1 := by linarith
  obtain ⟨hd1, hd2⟩ := rnd hd (by linarith) (by linarith)
  have hue := mul_le_mul_of_nonneg_left (by linarith : 1 - e1 ≤ 1 - w + 2 * u) hu
  have hue' := mul_le_mul_of_nonneg_left (by linarith : 1 - w - 2 * u ≤ 1 - e1) hu
  have hD : (1 - w) * (1 - 5 * u) ≤ d := by linarith
  have hD' : d ≤ 1 - w + 5 * u := by linarith
  have hD0 : 0 ≤ d := by linarith
  have hD1 : d ≤ 1 := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨hp, -⟩ := rnd hp2 (mul_nonneg hD0 he) (by linarith [mul_le_one₀ hD1 he he₁])
    have hde : (1 - w) * (1 - 5 * u) * e ≤ d * e := mul_le_mul_of_nonneg_right hD he
    have h9 : (1 - w) * (1 - 9 * u) ≤ (1 - w) * ((1 - 5 * u) * (1 - u)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_right hde (by linarith : (0 : ℝ) ≤ 1 - u)
    have h2 := mul_le_mul_of_nonneg_right h9 he
    rw [← hw_def]
    linarith
  · obtain ⟨-, hp⟩ := rnd hp2 (mul_nonneg hD0 he) (by linarith [mul_le_one₀ hD1 he he₁])
    have hde : d * e ≤ (1 - w + 5 * u) * e := mul_le_mul_of_nonneg_right hD' he
    have hkey : (1 - w + 5 * u) * (1 + u) ≤ 1 - w / 2 := by linarith
    have h1 := mul_le_mul_of_nonneg_right hde (by linarith : (0 : ℝ) ≤ 1 + u)
    have h2 := mul_le_mul_of_nonneg_right hkey he
    have : 1 / (2 * m) = w / 2 := by rw [hw_def]; field_simp
    rw [this]
    linarith

/-- One level of the machine's next window and tolerance (`NLAlib.eighNextParams`). -/
private lemma dec_eighNextParams_le {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R ε : F} {m : ℕ}
    (hu : 0 ≤ u) (hum : 25 * (m : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * (m : ℝ) ≤ Ω) (hR : 0 ≤ dec R) (hRΩ : dec R ≤ Ω) (hε : 0 ≤ dec ε)
    (hε₁ : dec ε ≤ 1) :
    dec (eighNextParams M R ε m).1 ≤ (1 / 2 + 2 / m) * (1 + 22 * u) * dec R + u * τ ∧
    (1 - 1 / m) * (1 - 9 * u) * dec ε - u * τ ≤ dec (eighNextParams M R ε m).2 ∧
    dec (eighNextParams M R ε m).2 ≤ (1 - 1 / (2 * m)) * dec ε + u * τ := by
  have h2 := hM.ofNat 2
  push_cast at h2
  have hm' : (20 : ℝ) ≤ m := by exact_mod_cast hm
  exact ⟨le_of_isRoundingOf_eighNextParams_fst hu hum hτ₀ hτ hm' hmΩ hR hRΩ h2 (hM.ofNat m)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (fun h => hM.div _ _ h) (hM.add _ _) (hM.mul _ _),
    le_and_le_of_isRoundingOf_eighNextParams_snd hu hum hτ₀ hτ hm' hmΩ hε hε₁ (hM.ofNat m)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (hM.dec_one ▸ hM.sub _ _) (hM.mul _ _)⟩

/-- The children of a node that is not a leaf: the machine's test failed, and the child carries
the next parameters of `NLAlib.eighNextParams`. -/
private lemma le_eq_false_and_eq_of_eighChild_eq_some {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} {x y : EighNode F}
    {smp : EighSample Su Sg N} {b : Bool} (h : eighChild M N signFuel R₀ β x smp b = some y) :
    M.le x.R (M.mul x.ε R₀) = false ∧ y.R = (eighNextParams M x.R x.ε x.ℓ).1 ∧
      y.ε = (eighNextParams M x.R x.ε x.ℓ).2 ∧ y.ℓ = x.ℓ + 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hle
    rw [Bool.not_eq_false] at hle
    have hst : ∃ U d, eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ smp = .leaf U d := by
      unfold eighStep
      by_cases hk : x.k ≤ 1
      · rw [if_pos hk]; exact ⟨_, _, rfl⟩
      · rw [if_neg hk, if_pos hle]; exact ⟨_, _, rfl⟩
    obtain ⟨U, d, hst⟩ := hst
    simp [eighChild, hst] at h
  · unfold eighChild at h
    split at h
    · simp at h
    · split_ifs at h; cases h; exact ⟨rfl, rfl, rfl⟩
    · split_ifs at h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

/-- The tolerance of a node of depth $j \le \ell$ stays above $\varepsilon/3$. -/
private lemma div_three_le_of_le_depth {x j u τ ε₀ Φ : ℝ} (hx : 20 ≤ x) (hj0 : 0 ≤ j)
    (hj : j ≤ x) (hu : 0 ≤ u) (hxu : 100 * x ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : 100 * τ ≤ ε₀)
    (hε₀ : 0 < ε₀) (hΦ : 1 - 9 * (j * u) ≤ Φ) :
    ε₀ / 3 ≤ ε₀ * ((x - 1) / (x + j - 1)) * Φ - j * (u * τ) := by
  have hxu' : 20 * (x * u) ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_right hx (mul_nonneg (by linarith : (0 : ℝ) ≤ x) hu); nlinarith
  have hju : j * u ≤ x * u := mul_le_mul_of_nonneg_right hj hu
  have hρ : 2 / 5 ≤ (x - 1) / (x + j - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hΦ' : 99 / 100 ≤ Φ := by linarith
  have h1 := mul_le_mul hρ hΦ' (by norm_num) (by linarith)
  have h2 := mul_le_mul_of_nonneg_left h1 hε₀.le
  have hjuτ : j * (u * τ) ≤ ε₀ / 100 := by
    have : j * (u * τ) = (j * u) * τ := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right (hju.trans (by linarith : x * u ≤ 1)) hτ₀
    linarith
  nlinarith

/-- $(1 + 22u)^n \le 1 + 23nu$ for $nu \le 1/1000$. -/
private lemma one_add_pow_le_of_mul_le {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hnu : (n : ℝ) * u ≤ 1 / 1000) :
    (1 + 22 * u) ^ n ≤ 1 + 23 * (n * u) := by
  have h1 : (1 + 22 * u) ^ n ≤ Real.exp (n * (22 * u)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (22 * u)]) n
  have hy0 : 0 ≤ (n : ℝ) * (22 * u) := by positivity
  have hy : |(n : ℝ) * (22 * u)| ≤ 1 := by rw [abs_of_nonneg hy0]; linarith
  have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hy)).2
  have h3 : ((n : ℝ) * (22 * u)) ^ 2 ≤ (n * (22 * u)) * (22 / 1000) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) hy0
  linarith

/-- The telescoped product of the windows against the tolerance factor: for $x \ge 20$,
$$\frac{1}{32}\frac{2x(2x+1)(2x+2)(2x+3)}{x(x+1)(x+2)(x+3)} \le \frac{x-1}{2x-1} - \frac1x \,.$$ -/
private lemma div_le_sub_one_div_of_le {x : ℝ} (hx : 20 ≤ x) :
    (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3)) / 32 ≤
      (x - 1) / (x + x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  set P := (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3))
  set ρ := (x - 1) / (x + x - 1)
  have hpoly : 0 ≤ 4 * x ^ 3 - 62 * x ^ 2 - 101 * x + 48 := by
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ x - 20),
      mul_nonneg hx0.le (by linarith : 0 ≤ 18 * x - 101)]
  have h2x : x + x - 1 ≠ 0 := by linarith
  have hQ : x * (x + 1) * (x + 2) * (x + 3) ≠ 0 := by positivity
  have hρ' : ρ * (x + x - 1) = x - 1 := div_mul_cancel₀ _ h2x
  have hP' : P * (x * (x + 1) * (x + 2) * (x + 3)) =
      (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) := div_mul_cancel₀ _ hQ
  have hx' : 1 / x * x = 1 := one_div_mul_cancel hx0.ne'
  have key : (ρ - 1 / x - P / 32) * (8 * x * (x + x - 1) * (x + 2) * (x + 3) * (x + 1)) =
      (4 * x ^ 3 - 62 * x ^ 2 - 101 * x + 48) * (x + 1) := by
    linear_combination (8 * x * (x + 2) * (x + 3) * (x + 1)) * hρ' -
      (8 * (x + x - 1) * (x + 2) * (x + 3) * (x + 1)) * hx' - ((x + x - 1) / 4) * hP'
  have hD : 0 < 8 * x * (x + x - 1) * (x + 2) * (x + 3) * (x + 1) :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hx0) (by linarith))
      (by linarith)) (by linarith)) (by linarith)
  have : 0 ≤ ρ - 1 / x - P / 32 :=
    le_of_mul_le_mul_right (by rw [zero_mul, key]; exact mul_nonneg hpoly (by linarith)) hD
  linarith

/-- The real arithmetic of the leaf test at depth $\ell$. -/
private lemma le_of_le_depth_eq {x u τ R₀ ε₀ X Ψ Φ R e z : ℝ} (hx : 20 ≤ x) (hu : 0 ≤ u)
    (hxu : 100 * x ^ 2 * u ≤ 1) (hτ1 : 100 * τ ≤ ε₀ * R₀) (hτ2 : 100 * τ ≤ ε₀)
    (hR₀ : 0 < R₀) (hε₀ : 0 < ε₀) (hX : X ≤ ε₀ / 32) (hΨ0 : 0 ≤ Ψ)
    (hΨ : Ψ ≤ 1 + 23 * (x * u)) (hΦ : 1 - 9 * (x * u) ≤ Φ)
    (hR : R ≤ R₀ * (X * ((x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) /
      (x * (x + 1) * (x + 2) * (x + 3))) * Ψ) + x * (u * τ))
    (he : ε₀ * ((x - 1) / (x + x - 1)) * Φ - x * (u * τ) ≤ e)
    (hz : e * R₀ - u * (e * R₀ + τ) ≤ z) : R ≤ z := by
  have hx0 : 0 < x := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = x * u := ⟨_, rfl⟩
  have hwτ : x * (u * τ) = w * τ := by rw [hw]; ring
  rw [← hw] at hΨ hΦ
  rw [hwτ] at hR he
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwx : 100 * w * x ≤ 1 := by rw [hw]; linarith
  have hw1 : w ≤ 1 / 2000 := by
    have := mul_le_mul_of_nonneg_left hx hw0; linarith
  have huw : 20 * u ≤ w := by
    have := mul_le_mul_of_nonneg_right hx hu; rw [hw]; linarith
  set P := (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3))
  set ρ := (x - 1) / (x + x - 1)
  have hP0 : 0 ≤ P := by positivity
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hP : P / 32 ≤ ρ - 1 / x := div_le_sub_one_div_of_le hx
  have hP16 : P / 32 ≤ 1 / 2 := by have : 0 < 1 / x := by positivity
                                   linarith
  set Y := ε₀ * R₀
  have hY : 0 < Y := by positivity
  have hYx : 100 * (w * Y) ≤ Y / x := by
    rw [le_div_iff₀ hx0]
    have := mul_le_mul_of_nonneg_left hwx hY.le
    linarith
  -- the window
  have hA1 : R₀ * (X * P * Ψ) ≤ Y / 32 * P * Ψ := by
    have := mul_le_mul_of_nonneg_right hX (mul_nonneg (mul_nonneg hR₀.le hP0) hΨ0)
    simp only [Y]; linarith
  have hA2 := mul_le_mul_of_nonneg_left hΨ (mul_nonneg (by positivity : 0 ≤ Y / 32) hP0)
  have hA3 := mul_le_mul_of_nonneg_left hP hY.le
  have hA4 := mul_le_mul_of_nonneg_left hP16 (mul_nonneg hw0 hY.le)
  have hA5 : w * τ ≤ w * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ1 hw0; simp only [Y]; linarith
  -- the test
  have hB1 := mul_le_mul_of_nonneg_right he hR₀.le
  have hB2 := mul_le_mul_of_nonneg_left hΦ (mul_nonneg hY.le hρ0)
  have hB3 : w * τ * R₀ ≤ w * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ2 (mul_nonneg hw0 hR₀.le); simp only [Y]; linarith
  have hB4 := mul_le_mul_of_nonneg_left hρ1 (mul_nonneg hw0 hY.le)
  have hlow : Y * ρ * (1 - 9 * w) - w * Y / 100 ≤ e * R₀ := by
    have : ε₀ * ρ * Φ * R₀ = Y * ρ * Φ := by simp only [Y]; ring
    linarith
  have hlow2 : Y * ρ * (1 - 9 * w) - w * Y / 100 ≤ Y / 2 := by
    have := mul_le_mul_of_nonneg_left hρ1 hY.le
    have := mul_nonneg (mul_nonneg hY.le hρ0) hw0
    have := mul_nonneg hw0 hY.le
    linarith
  have hC1 := mul_le_mul_of_nonneg_right hlow (by linarith : (0 : ℝ) ≤ 1 - u)
  have hC2 := mul_le_mul_of_nonneg_left hlow2 hu
  have hC3 : u * τ ≤ u * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ1 hu; simp only [Y]; linarith
  have hC4 := mul_le_mul_of_nonneg_left huw hY.le
  have hwY := mul_nonneg hw0 hY.le
  clear_value Y P ρ
  have h1 : Y / 32 * P * (1 + 23 * w) = Y * (P / 32) + 23 * (w * Y * (P / 32)) := by ring
  have h2 : Y * (ρ - 1 / x) = Y * ρ - Y / x := by ring
  have hup : R ≤ Y * ρ - Y / x + 23 / 2 * (w * Y) + w * Y / 100 := by
    linarith only [hR, hA1, hA2, hA3, hA4, hA5, h1, h2]
  have hdown : Y * ρ - 9 / 2 * (w * Y) - w * Y / 100 - 51 / 100 * (u * Y) ≤ z := by
    linarith only [hz, hC1, hC2, hC3, hB4]
  linarith only [hup, hdown, hYx, hC4, hwY]

/-- One level of the tolerance bound: $(1 - 1/m)(\ell - 1)/(m - 1) = (\ell - 1)/m$ for
$m = \ell + j$. -/
private lemma mul_div_sub_one_pow_succ (ε u : ℝ) {ℓ j : ℕ} (hm0 : (0 : ℝ) < ℓ + j)
    (hm1 : (ℓ : ℝ) + j - 1 ≠ 0) :
    ε * (((ℓ : ℝ) - 1) / (ℓ + (j + 1) - 1)) * (1 - 9 * u) ^ (j + 1) =
      (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) * (ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) *
        (1 - 9 * u) ^ j) := by
  have : (ℓ : ℝ) + j ≠ 0 := hm0.ne'
  have h' : (ℓ : ℝ) + (j + 1) - 1 = ℓ + j := by ring
  rw [h', pow_succ]; field_simp

/-- One level of the window bound: $(1/2 + 2/m)\,m(m+1)(m+2)(m+3) =
\tfrac12(m+1)(m+2)(m+3)(m+4)$ for $m = \ell + j$. -/
private lemma mul_window_bound_eq (R u : ℝ) {ℓ j : ℕ} (hm0 : (0 : ℝ) < ℓ + j) :
    (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) * (R * (2⁻¹ ^ j *
      (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
        ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j)) =
      R * (2⁻¹ ^ (j + 1) * (((ℓ : ℝ) + (j + 1)) * (ℓ + (j + 1) + 1) * (ℓ + (j + 1) + 2) *
        (ℓ + (j + 1) + 3) / ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) *
          (1 + 22 * u) ^ (j + 1)) := by
  have : (ℓ : ℝ) + j ≠ 0 := hm0.ne'
  rw [pow_succ, pow_succ]; field_simp; ring

/-- One level of the invariants of the recursion below a node at depth $j < \ell$. -/
private lemma invariants_of_eighChild_eq_some {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {N signFuel : ℕ} {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : 20 ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ1 : 100 * τ ≤ dec ε * dec R₀) (hτ2 : 100 * τ ≤ dec ε) (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω)
    {j : ℕ} (hj : j < ℓ) {x y : EighNode F} {smp : EighSample ℝ ℂ N} {b : Bool}
    (hxy : eighChild M N signFuel R₀ β x smp b = some y) (h1 : x.ℓ = ℓ + j)
    (h2 : dec x.ε ≤ 1)
    (h3 : dec ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) * (1 - 9 * u) ^ j - j * (u * τ) ≤ dec x.ε)
    (h4 : dec x.R ≤ dec R₀)
    (h5 : dec x.R ≤ dec R₀ * (2⁻¹ ^ j * (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j) + j * (u * τ)) :
    y.ℓ = ℓ + (j + 1) ∧ dec y.ε ≤ 1 ∧
    dec ε * (((ℓ : ℝ) - 1) / (ℓ + ((j + 1 : ℕ) : ℝ) - 1)) * (1 - 9 * u) ^ (j + 1) -
      ((j + 1 : ℕ) : ℝ) * (u * τ) ≤ dec y.ε ∧ dec y.R ≤ dec R₀ ∧
    dec y.R ≤ dec R₀ * (2⁻¹ ^ (j + 1) * (((ℓ : ℝ) + ((j + 1 : ℕ) : ℝ)) *
      (ℓ + ((j + 1 : ℕ) : ℝ) + 1) * (ℓ + ((j + 1 : ℕ) : ℝ) + 2) * (ℓ + ((j + 1 : ℕ) : ℝ) + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ (j + 1)) +
      ((j + 1 : ℕ) : ℝ) * (u * τ) := by
  obtain ⟨hle, hyR, hyε, hyℓ⟩ := le_eq_false_and_eq_of_eighChild_eq_some M hxy
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hjℓ : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  have hℓu : 20 * ((ℓ : ℝ) * u) ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_right hℓ' (mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ) hu)
    linarith
  have hu40 : u ≤ 1 / 40000 := by
    have := mul_le_mul_of_nonneg_right hℓ' hu; linarith
  have hτ1' : τ ≤ 1 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ1'
  have hjuτ : 0 ≤ j * (u * τ) := mul_nonneg hj0 (mul_nonneg hu hτ₀)
  have hεx : dec ε / 3 ≤ dec x.ε := by
    refine (div_three_le_of_le_depth hℓ' hj0 (by linarith) hu hu₁ hτ₀ hτ2 hε ?_).trans h3
    have := one_add_mul_le_pow (a := -(9 * u)) (by linarith) j
    rw [← sub_eq_add_neg] at this
    linarith
  -- the window is nonnegative at a node that is not a leaf
  have hxR0 : dec x.ε * dec R₀ ≤ dec R₀ := mul_le_of_le_one_left hR₀.le h2
  have hRx : 0 ≤ dec x.R := by
    have hmul := (le_and_le_of_isRoundingOf (hM.mul x.ε R₀)
      (mul_nonneg (by linarith) hR₀.le) (by linarith) hu hτ₀).1
    have hnot : ¬ dec x.R ≤ dec (M.mul x.ε R₀) := fun h => by
      rw [← hM.le_iff] at h; rw [h] at hle; exact Bool.noConfusion hle
    have h1' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hεx hR₀.le) (by linarith : (0 : ℝ) ≤ 1 - u)
    have h2' := mul_le_mul_of_nonneg_left hτ1 hu
    have h3' := mul_le_mul_of_nonneg_left hu40 (mul_nonneg hε.le hR₀.le)
    linarith
  have hm : 25 * ((x.ℓ : ℕ) : ℝ) ^ 2 * u ≤ 1 := by
    rw [h1]; push_cast
    have := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith) (by linarith : (ℓ : ℝ) + j ≤ 2 * ℓ) 2) hu
    nlinarith
  obtain ⟨s1, s2, s3⟩ := dec_eighNextParams_le hM (R := x.R) (ε := x.ε) (m := x.ℓ) hu hm hτ₀
    hτ1' (by omega) (by rw [h1]; push_cast; linarith) hRx (by linarith) (by linarith) h2
  rw [← hyR] at s1
  rw [← hyε] at s2 s3
  rw [h1] at s1 s2 s3
  rw [hyℓ, h1]
  push_cast at s1 s2 s3 ⊢
  have hm0 : (0 : ℝ) < ℓ + j := by linarith
  have hc : (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) ≤ 61 / 100 := by
    have : 2 / ((ℓ : ℝ) + j) ≤ 1 / 10 := by rw [div_le_iff₀ hm0]; linarith
    have := mul_le_mul (by linarith : 1 / 2 + 2 / ((ℓ : ℝ) + j) ≤ 6 / 10)
      (by linarith : 1 + 22 * u ≤ 1 + 22 / 40000) (by linarith) (by norm_num)
    linarith
  have hc0 : 0 ≤ (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) := by positivity
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · have hu2 : u ≤ 1 / (2 * ((ℓ : ℝ) + j)) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left (by linarith : (j : ℝ) ≤ ℓ) hu
      linarith
    have : (1 - 1 / (2 * ((ℓ : ℝ) + j))) * dec x.ε ≤ 1 - 1 / (2 * ((ℓ : ℝ) + j)) :=
      mul_le_of_le_one_right (by rw [sub_nonneg, div_le_one (by positivity)]; linarith) h2
    linarith
  · have hk0 : 0 ≤ (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) :=
      mul_nonneg (by rw [sub_nonneg, div_le_one hm0]; linarith) (by linarith)
    have hk1 : (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) ≤ 1 :=
      mul_le_one₀ (by have : 0 < 1 / ((ℓ : ℝ) + j) := by positivity
                      linarith) (by linarith) (by linarith)
    have hid := mul_div_sub_one_pow_succ (dec ε) u hm0 (by linarith : (ℓ : ℝ) + j - 1 ≠ 0)
    rw [hid]
    have := mul_le_mul_of_nonneg_left h3 hk0
    have := mul_le_of_le_one_left hjuτ hk1
    linarith
  · have := mul_le_mul_of_nonneg_left h4 hc0
    have := mul_le_mul_of_nonneg_right hc hR₀.le
    have := mul_le_of_le_one_left hτ₀ (by linarith : u ≤ 1)
    have := mul_le_of_le_one_left hR₀.le hε₁
    linarith
  · have hid := mul_window_bound_eq (dec R₀) u hm0
    have := mul_le_mul_of_nonneg_left h5 hc0
    have := mul_le_of_le_one_left hjuτ (hc.trans (by norm_num))
    linarith

/-- A node at depth $\ell$ with the invariants of the recursion is a leaf. -/
private lemma eighChild_eq_none_of_invariants {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {N signFuel : ℕ} {R₀ β ε : F} (hε : 0 < dec ε) (hR₀ : 0 < dec R₀) {ℓ : ℕ} (hℓ : 20 ≤ ℓ)
    (hhalf : (2⁻¹ : ℝ) ^ ℓ ≤ dec ε / 32) (hu : 0 ≤ u) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1)
    (hτ₀ : 0 ≤ τ) (hτ1 : 100 * τ ≤ dec ε * dec R₀) (hτ2 : 100 * τ ≤ dec ε)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {x : EighNode F} (smp : EighSample ℝ ℂ N) (b : Bool)
    (h2 : dec x.ε ≤ 1)
    (h3 : dec ε * (((ℓ : ℝ) - 1) / (ℓ + ℓ - 1)) * (1 - 9 * u) ^ ℓ - ℓ * (u * τ) ≤ dec x.ε)
    (h5 : dec x.R ≤ dec R₀ * (2⁻¹ ^ ℓ * (((ℓ : ℝ) + ℓ) * (ℓ + ℓ + 1) * (ℓ + ℓ + 2) * (ℓ + ℓ + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ ℓ) + ℓ * (u * τ)) :
    eighChild M N signFuel R₀ β x smp b = none := by
  rcases hc : eighChild M N signFuel R₀ β x smp b with _ | y
  · rfl
  exfalso
  have hle := (le_eq_false_and_eq_of_eighChild_eq_some M hc).1
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓu : (ℓ : ℝ) * u ≤ 1 / 2000 := by
    have := mul_le_mul_of_nonneg_right hℓ' (mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ) hu)
    linarith
  have hεx : dec ε / 3 ≤ dec x.ε := by
    refine (div_three_le_of_le_depth hℓ' (by positivity) le_rfl hu hu₁ hτ₀ hτ2 hε ?_).trans h3
    have := one_add_mul_le_pow (a := -(9 * u)) (by nlinarith) ℓ
    rw [← sub_eq_add_neg] at this
    linarith
  have hmul := (le_and_le_of_isRoundingOf (hM.mul x.ε R₀)
    (mul_nonneg (by linarith) hR₀.le) (by nlinarith) hu hτ₀).1
  have hR : dec x.R ≤ dec (M.mul x.ε R₀) := by
    refine le_of_le_depth_eq hℓ' hu hu₁ hτ1 hτ2 hR₀ hε hhalf (by positivity)
      (one_add_pow_le_of_mul_le hu (hℓu.trans (by norm_num))) ?_ h5 h3 hmul
    have := one_add_mul_le_pow (a := -(9 * u)) (by nlinarith) ℓ
    rw [← sub_eq_add_neg] at this
    linarith
  rw [← hM.le_iff] at hR
  rw [hR] at hle
  exact Bool.noConfusion hle

/-- **The recursion stops by depth $\ell$**: under `NLAlib.FloatMachine.IsAccurate` with
$0 \le u$, $100\ell^2u \le 1$, $0 \le \tau$, $100\tau \le \varepsilon\min(R_0, 1)$ (an absolute
floor bound: the rounded parameters $\mathrm{fl}(2/\ell)$, $\mathrm{fl}((1 - 1/\ell)\varepsilon_j)$
have floor errors $u\tau$) and $16(R_0 + \ell) \le \Omega$, for stored $\varepsilon$, $R_0$ with $0
< \varepsilon \le 2^{-15}$, $R_0 > 0$ and a depth counter $\ell \ge \lceil \log_2(1/\varepsilon)
\rceil + 5$ (`NLAlib.bisectionDepth`), the tree of `NLAlib.eighNodeAt` from the root
$(\mathbf{A}, R_0, \varepsilon, \ell)$ has no node at a path longer than $\ell$, for every
accuracy and samples. [Shah2024, proof of Theorem 4.2], "the
depth of the tree $d$ is no more than $\ell$".
Proof: a node at depth $j$ has window $R_j$ within a factor $(1 + u)^{4j}$ of
$R_0\prod_{i<j}(1/2 + 2/(\ell + i))$ and tolerance $\varepsilon_j$ within $(1 - u)^{4j}$ of
$\varepsilon(\ell - 1)/(\ell + j - 1)$ (the machine's rounded parameters, `NLAlib.eighNextParams`)
and depth parameter $\ell + j$ (induction on the path, unfolding `NLAlib.eighChild`); the products
telescope: $\prod_{i<\ell}(\ell + i + 4)/(\ell + i) = \frac{2\ell(2\ell+1)(2\ell+2)(2\ell+3)}
{\ell(\ell+1)(\ell+2)(\ell+3)} =: P_\ell$; with $2^{-\ell} \le \varepsilon/32$ (`Nat.le_ceil`,
`Real.rpow_logb`) it suffices that $P_\ell/32 \le (\ell - 1)/(2\ell - 1)$, i.e.
$(2\ell+1)(2\ell+3)(2\ell-1) \le 8(\ell-1)(\ell+2)(\ell+3)$, whose difference is
$20\ell^2 + 10\ell - 45 > 0$ for $\ell \ge 2$ (at $\ell = 20$: $0.4355 \le 0.487$), so
$R_\ell \le \varepsilon_\ell R_0$ with a relative margin of order $1/\ell$, which absorbs
$(1 + u)^{8\ell} \le 1 + 1/(10\ell)$ and the rounding of the test $\mathrm{fl}(\varepsilon_\ell
R_0)$ (floor: $\tau \le \varepsilon R_0/100$), and
the node at depth $\ell$ is a leaf of `NLAlib.eighStep`. Since $\ell$ is any number $\ge$
`NLAlib.bisectionDepth`, $R_j$ may drop below $\tau$: state the invariant with the additive floor
term, $R_{j+1} \le (\tfrac12 + \tfrac2{\ell_j})R_j(1 + u)^4 + u\tau$, summed $\le 2\ell u\tau \le
\varepsilon R_0/(5000\ell)$, far inside the margin. L, about 60 lines (path induction with four
roundings per level, the telescoping identity over $\mathbb{N}$, `Real.logb`). -/
theorem FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} (ha : ℓ < a.length) :
    eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = none := by
  -- $2^\ell \ge 32/\varepsilon$, hence $\ell \ge 20$
  have hpow : 32 ≤ dec ε * 2 ^ ℓ := by
    have hlog : Real.logb 2 (dec ε)⁻¹ ≤ (ℓ : ℝ) - 5 := by
      have h2 : ((⌈Real.logb 2 (dec ε)⁻¹⌉₊ + 5 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
      push_cast at h2
      linarith [Nat.le_ceil (Real.logb 2 (dec ε)⁻¹)]
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hε)).mp hlog
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast] at h
    norm_num at h
    have := mul_le_mul_of_nonneg_left h hε.le
    rw [mul_inv_cancel₀ hε.ne'] at this
    linarith
  have hℓ20 : 20 ≤ ℓ := by
    have h := hpow.trans (mul_le_mul_of_nonneg_right hε₁ (by positivity))
    have h' : (2 : ℝ) ^ 20 ≤ 2 ^ ℓ := by norm_num at h ⊢; linarith
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h'
  have hhalf : (2⁻¹ : ℝ) ^ ℓ ≤ dec ε / 32 := by
    rw [inv_pow, ← one_div, div_le_iff₀ (by positivity)]; linarith
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hτ1 : 100 * τ ≤ dec ε * dec R₀ :=
    hτ.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hε.le)
  have hτ2 : 100 * τ ≤ dec ε := hτ.trans (mul_le_of_le_one_right hε.le (min_le_right _ _))
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ20
  -- induction on the path with the invariants of the recursion
  have key : ∀ (a : List Bool) (j : ℕ) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N),
      j ≤ ℓ → x.ℓ = ℓ + j → dec x.ε ≤ 1 →
      dec ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) * (1 - 9 * u) ^ j - j * (u * τ) ≤ dec x.ε →
      dec x.R ≤ dec R₀ →
      dec x.R ≤ dec R₀ * (2⁻¹ ^ j * (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
        ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j) + j * (u * τ) →
      ℓ < j + a.length → eighNodeAt M N signFuel R₀ β a x s = none := by
    intro a
    induction a with
    | nil => intro j x s hj _ _ _ _ _ hlt; simp only [List.length_nil] at hlt; omega
    | cons b a ih =>
      intro j x s hj h1 h2 h3 h4 h5 hlt
      simp only [eighNodeAt]
      rcases hc : eighChild M N signFuel R₀ β x (s []) b with _ | y
      · rfl
      rcases Nat.lt_or_ge j ℓ with hjl | hjl
      · obtain ⟨g1, g2, g3, g4, g5⟩ := invariants_of_eighChild_eq_some hM hε hε1 hR₀ hℓ20 hu
          hu₁ hτ₀ hτ1 hτ2 hΩ hjl hc h1 h2 h3 h4 h5
        exact ih (j + 1) y _ (by omega) g1 g2 g3 g4 g5
          (by simp only [List.length_cons] at hlt; omega)
      · obtain rfl : j = ℓ := by omega
        rw [eighChild_eq_none_of_invariants hM hε hR₀ hℓ20 hhalf hu hu₁ hτ₀ hτ1 hτ2 hΩ _ _ h2
          h3 h5] at hc
        exact absurd hc (by simp)
  have hQ : (ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3) ≠ 0 := by positivity
  refine key a 0 _ s (Nat.zero_le _) rfl hε1 ?_ le_rfl ?_ (by simpa using ha)
  · rw [Nat.cast_zero, add_zero, div_self (by linarith), pow_zero]; simp
  · simp only [Nat.cast_zero, add_zero, pow_zero, div_self hQ, mul_one, zero_mul]
    exact le_rfl

private theorem eighChild_eq_some_params_aux {F : Type*} {M : FloatMachine F ℝ ℂ}
    {N signFuel : ℕ} {R₀ β : F} {x y : EighNode F} {s : EighSample ℝ ℂ N} {b : Bool}
    (h : eighChild M N signFuel R₀ β x s b = some y) :
    y.k ≤ x.k ∧ y.ℓ = x.ℓ + 1 ∧ y.R = (eighNextParams M x.R x.ε x.ℓ).1 ∧
      y.ε = (eighNextParams M x.R x.ε x.ℓ).2 ∧ M.le x.R (M.mul x.ε R₀) = false := by
  unfold eighChild eighStep at h
  by_cases h1 : x.k ≤ 1
  · simp [h1] at h
  by_cases h2 : M.le x.R (M.mul x.ε R₀) = true
  · simp [h1, h2] at h
  simp only [h1, h2, if_false] at h
  split_ifs at h <;> dsimp only at h <;> (try split_ifs at h) <;> cases h <;>
    exact ⟨by dsimp only; omega, rfl, rfl, rfl, by simpa using h2⟩

private theorem rnd_aux_of_nonneg {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z) (ha0 : 0 ≤ a)
    (ha : a ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) :
    a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) := by
  have hmax : max |a| τ ≤ a + τ := max_le (by rw [abs_of_nonneg ha0]; linarith) (by linarith)
  have := abs_le.mp ((h (by rwa [abs_of_nonneg ha0])).trans (mul_le_mul_of_nonneg_left hmax hu))
  constructor <;> linarith [this.1, this.2]

private theorem eighNextParams_snd_aux {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (r e : F)
    {L : ℕ} (hu : 0 ≤ u) (huL : u * L ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 100)
    (he0 : 0 < dec e) (hτe : 30 * τ ≤ dec e) (he1 : dec e ≤ 1) (hL : 5 ≤ L)
    (hΩ : 2 + L ≤ Ω) :
    dec (eighNextParams M r e L).2 ≤ dec e ∧
      dec e * (L - 1) - 3 * u * L * dec e ≤ dec (eighNextParams M r e L).2 * L := by
  have hL' : (5 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hu5 : u ≤ 1 / 5000 := by nlinarith
  simp only [eighNextParams]
  obtain ⟨hla, hlb⟩ := rnd_aux_of_nonneg (hM.ofNat L) hL0.le (by linarith) hu hτ₀
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  have hdl : L - 0.002 ≤ dec (M.ofNat L) ∧ dec (M.ofNat L) ≤ L + 0.002 := by
    constructor <;> linarith
  have hdl0 : 0 < dec (M.ofNat L) := by linarith
  have hiL1 : 1 / (L : ℝ) * L = 1 := by field_simp
  have hiL5 : 1 / (L : ℝ) ≤ 1 / 5 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have huiL : u ≤ 1 / (L : ℝ) / 1000 := by
    rw [le_div_iff₀ (by norm_num), le_div_iff₀ hL0]; linarith
  -- the reciprocal of the depth counter
  have hq0 : |1 / dec (M.ofNat L) - 1 / L| ≤ u / 4 := by
    rw [div_sub_div _ _ hdl0.ne' hL0.ne', abs_div, abs_of_pos (mul_pos hdl0 hL0),
      div_le_iff₀ (mul_pos hdl0 hL0), abs_le]
    have h1 : L + τ ≤ dec (M.ofNat L) * L / 4 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ dec (M.ofNat L) - 4.99) hL0.le]
    have h2 := mul_le_mul_of_nonneg_left h1 hu
    constructor <;> linarith
  have hq0' := abs_le.mp hq0
  obtain ⟨hqa, hqb⟩ := rnd_aux_of_nonneg (hM.div M.one (M.ofNat L) hdl0.ne')
    (by rw [hM.dec_one]; positivity) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hqa hqb
  have hq021 : 1 / dec (M.ofNat L) ≤ 0.21 := by linarith
  have hdq : 1 / L - u / 2 ≤ dec (M.div M.one (M.ofNat L)) ∧
      dec (M.div M.one (M.ofNat L)) ≤ 1 / L + u / 2 := by
    have := mul_le_mul_of_nonneg_left hq021 hu
    constructor <;> linarith
  obtain ⟨hsa, hsb⟩ := rnd_aux_of_nonneg (hM.sub M.one (M.div M.one (M.ofNat L)))
    (by rw [hM.dec_one]; linarith) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hsa hsb
  have hds : 1 - 1 / L - 1.6 * u ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) ∧
      dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 - 1 / L + 1.6 * u := by
    have := mul_le_mul_of_nonneg_left (show 1 - dec (M.div M.one (M.ofNat L)) ≤ 1 by linarith) hu
    constructor <;> linarith
  have hds0 : 0 ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) := by linarith
  have hds1 : dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 := by linarith
  have hdse := mul_le_of_le_one_left he0.le hds1
  obtain ⟨hea, heb⟩ := rnd_aux_of_nonneg (hM.mul (M.sub M.one (M.div M.one (M.ofNat L))) e)
    (mul_nonneg hds0 he0.le) (by linarith) hu hτ₀
  have hde : (1 - 1 / L) * dec e - 3 * u * dec e ≤
      dec (M.mul (M.sub M.one (M.div M.one (M.ofNat L))) e) ∧
      dec (M.mul (M.sub M.one (M.div M.one (M.ofNat L))) e) ≤
        (1 - 1 / L) * dec e + 3 * u * dec e := by
    have h1 := mul_le_mul_of_nonneg_right hds.1 he0.le
    have h2 := mul_le_mul_of_nonneg_right hds.2 he0.le
    have h3 := mul_le_mul_of_nonneg_left hdse hu
    have h4 := mul_le_mul_of_nonneg_left hτe hu
    constructor <;> linarith
  have hue := mul_le_mul_of_nonneg_right huiL he0.le
  refine ⟨by linarith, ?_⟩
  have := mul_le_mul_of_nonneg_right hde.1 hL0.le
  linear_combination this + dec e * hiL1

private theorem eighNextParams_fst_aux {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R₀ r : F} (e : F)
    {L : ℕ} (hu : 0 ≤ u) (huL : u * L ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 100)
    (he0 : 0 < dec e) (hτeR : 30 * τ ≤ dec e * dec R₀) (he1 : dec e ≤ 1) (hL : 5 ≤ L)
    (hΩ : 2 + L + dec R₀ ≤ Ω) (hR₀ : 0 < dec R₀) (hr : dec r ≤ dec R₀)
    (hint : M.le r (M.mul e R₀) = false) :
    dec (eighNextParams M r e L).1 ≤ dec r := by
  have hL' : (5 : ℝ) ≤ L := by exact_mod_cast hL
  have hu5 : u ≤ 1 / 5000 := by nlinarith
  simp only [eighNextParams]
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  obtain ⟨h2a, h2b⟩ := rnd_aux_of_nonneg (hM.ofNat 2) (by norm_num) (by push_cast; linarith)
    hu hτ₀
  obtain ⟨hla, hlb⟩ := rnd_aux_of_nonneg (hM.ofNat L) (by positivity) (by linarith) hu hτ₀
  push_cast at h2a h2b
  have hd2 : 1.99 ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2.01 := by constructor <;> linarith
  have hdl : L - 0.002 ≤ dec (M.ofNat L) := by linarith
  have hdl0 : 0 < dec (M.ofNat L) := by linarith
  -- the factor is at most `0.95`
  have hh1 : 1 / dec (M.ofNat 2) ≤ 0.51 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hh2 : 0.49 ≤ 1 / dec (M.ofNat 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨hha, hhb⟩ := rnd_aux_of_nonneg (hM.div M.one (M.ofNat 2) (by linarith))
    (by rw [hM.dec_one]; positivity) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hha hhb
  have ht1 : dec (M.ofNat 2) / dec (M.ofNat L) ≤ 0.41 := by rw [div_le_iff₀ hdl0]; linarith
  have ht0 : 0 ≤ dec (M.ofNat 2) / dec (M.ofNat L) := div_nonneg (by linarith) hdl0.le
  obtain ⟨hta, htb⟩ := rnd_aux_of_nonneg (hM.div (M.ofNat 2) (M.ofNat L) hdl0.ne') ht0
    (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left hh1 hu
  have := mul_le_mul_of_nonneg_left ht1 hu
  have hdh : 0.48 ≤ dec (M.div M.one (M.ofNat 2)) ∧ dec (M.div M.one (M.ofNat 2)) ≤ 0.52 := by
    constructor <;> linarith
  have hdt : -0.01 ≤ dec (M.div (M.ofNat 2) (M.ofNat L)) ∧
      dec (M.div (M.ofNat 2) (M.ofNat L)) ≤ 0.42 := by
    constructor <;> linarith
  obtain ⟨haa, hab⟩ := rnd_aux_of_nonneg (hM.add (M.div M.one (M.ofNat 2))
    (M.div (M.ofNat 2) (M.ofNat L))) (by linarith) (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left (show dec (M.div M.one (M.ofNat 2)) +
    dec (M.div (M.ofNat 2) (M.ofNat L)) ≤ 0.94 by linarith) hu
  have hda : 0 ≤ dec (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ∧
      dec (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ≤ 0.95 := by
    constructor <;> linarith
  -- the window is above the floor
  have heR := mul_le_of_le_one_left hR₀.le he1
  have hm := rnd_aux_of_nonneg (hM.mul e R₀) (mul_pos he0 hR₀).le (by linarith) hu hτ₀
  have hrm : dec (M.mul e R₀) < dec r := by
    rw [← not_le, ← hM.le_iff]; simp [hint]
  have := mul_le_mul_of_nonneg_left heR hu
  have := mul_le_mul_of_nonneg_right hu5 (mul_pos he0 hR₀).le
  have := mul_le_mul_of_nonneg_right hu5 hτ₀
  have hr0 : 29 * τ ≤ dec r := by linarith [hm.1]
  have hdar := mul_le_of_le_one_left (by linarith : 0 ≤ dec r) (by linarith : dec (M.add
    (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ≤ 1)
  obtain ⟨hra, hrb⟩ := rnd_aux_of_nonneg (hM.mul (M.add (M.div M.one (M.ofNat 2))
    (M.div (M.ofNat 2) (M.ofNat L))) r) (mul_nonneg hda.1 (by linarith)) (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left hdar hu
  have := mul_le_mul_of_nonneg_right hda.2 (by linarith : 0 ≤ dec r)
  have := mul_le_mul_of_nonneg_right hu5 (by linarith : 0 ≤ dec r)
  linarith

/-- **The parameters of the nodes**: under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`, every node $y$ of the tree at a
path $a$ has $\lvert a \rvert \le \ell$, size at most the root's, depth counter $\ell +
\lvert a\rvert$, tolerance in $[\varepsilon/3, \varepsilon]$ and window at most $R_0$. (Not
$R_y \ge 0$: a rounded product can be $-u\tau$; such a node is a leaf.) [Shah2024, proof of
Theorem 4.2].
Proof: induction on the path with the invariants of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`'s proof (sizes do not grow: a
split partitions, a shift keeps; $\varepsilon_j \ge \tfrac{19}{39}(1 - \delta)^\ell\varepsilon$;
$R_j \le R_0$ since $(1/2 + 2/\ell)(1 + u)^4 \le 1$ plus the summed floor term). M, about 80
lines. -/
theorem FloatMachine.IsAccurate.eighNodeAt_eq_some_params
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} {y : EighNode F}
    (h : eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = some y) :
    a.length ≤ ℓ ∧ y.k ≤ k ∧ y.ℓ = ℓ + a.length ∧ dec ε / 3 ≤ dec y.ε ∧ dec y.ε ≤ dec ε ∧
      dec y.R ≤ dec R₀ := by
  have hℓ20 : (20 : ℝ) ≤ ℓ := by
    have h15 : (15 : ℝ) ≤ Real.logb 2 (dec ε)⁻¹ := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), show (15 : ℝ) = (15 : ℕ) by
        norm_num, Real.rpow_natCast, ← inv_inv ((2 : ℝ) ^ 15), ← inv_pow]
      exact inv_anti₀ hε (by simpa using hε₁)
    have := (h15.trans (Nat.le_ceil _))
    have : (bisectionDepth (dec ε) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    simp only [bisectionDepth, Nat.cast_add] at this
    push_cast at this
    linarith
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hτε : 100 * τ ≤ dec ε := hτ.trans (mul_le_of_le_one_right hε.le (min_le_right _ _))
  have hτR : 100 * τ ≤ dec ε * dec R₀ := hτ.trans (by gcongr; exact min_le_left _ _)
  have huℓ : u * ℓ ≤ 1 / 2000 := by nlinarith
  -- the tolerance stays above a third of the root's
  have hlow : ∀ (x : EighNode F) (j : ℕ), j ≤ ℓ → x.ℓ = ℓ + j →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) → dec ε / 3 ≤ dec x.ε := by
    intro x j hj hxℓ hx
    have hj' : (j : ℝ) ≤ ℓ := by exact_mod_cast hj
    rw [hxℓ] at hx
    push_cast at hx
    have h1 := mul_le_mul_of_nonneg_left hj' (by positivity : 0 ≤ u * ℓ)
    have h2 := mul_le_mul_of_nonneg_right h1 hε.le
    by_contra hlt
    have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
    nlinarith [mul_lt_mul_of_pos_right (not_le.mp hlt) (by linarith : (0 : ℝ) < ℓ + j - 1)]
  have key : ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N) (j : ℕ)
      (y : EighNode F), j + a.length ≤ ℓ → x.k ≤ k → x.ℓ = ℓ + j → dec x.ε ≤ dec ε →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) → dec x.R ≤ dec R₀ →
      eighNodeAt M N signFuel R₀ β a x s = some y →
      y.k ≤ k ∧ y.ℓ = ℓ + (j + a.length) ∧ dec y.ε ≤ dec ε ∧
        dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * (j + a.length : ℕ) ≤ dec y.ε * (y.ℓ - 1) ∧
        dec y.R ≤ dec R₀ := by
    intro a
    induction a with
    | nil =>
      intro x s j y _ h1 h2 h3 h4 h5 h
      cases Option.some.inj h
      exact ⟨h1, h2, h3, by simpa using h4, h5⟩
    | cons b a ih =>
      intro x s j y hj h1 h2 h3 h4 h5 h
      simp only [eighNodeAt, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, hy⟩ := h
      obtain ⟨hzk, hzℓ, hzR, hzε, hint⟩ := eighChild_eq_some_params_aux hz
      simp only [List.length_cons] at hj
      have hxε := hlow x j (by omega) h2 h4
      have hx0 : 0 < dec x.ε := by linarith
      have hxℓ : (x.ℓ : ℝ) ≤ 2 * ℓ := by
        rw [h2]; push_cast; linarith [(by exact_mod_cast (by omega : j ≤ ℓ) : (j : ℝ) ≤ ℓ)]
      have hxℓ5 : 5 ≤ x.ℓ := by
        have : (5 : ℝ) ≤ x.ℓ := by rw [h2]; push_cast; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
        exact_mod_cast this
      have huL : u * x.ℓ ≤ 1 / 1000 := by nlinarith
      have hR := mul_le_mul_of_nonneg_right hxε hR₀.le
      obtain ⟨hs1, hs2⟩ := eighNextParams_snd_aux hM x.R x.ε hu huL hτ₀ (by linarith) hx0
        (by linarith) (by linarith) hxℓ5 (by linarith)
      have hf := eighNextParams_fst_aux hM x.ε hu huL hτ₀ (by linarith) hx0 (by linarith)
        (by linarith) hxℓ5 (by linarith) hR₀ h5 hint
      have hloss := mul_le_mul_of_nonneg_left
        (mul_le_mul hxℓ h3 hx0.le (by positivity)) (by positivity : (0 : ℝ) ≤ 3 * u)
      obtain ⟨r1, r2, r3, r4, r5⟩ := ih z (fun a' => s (b :: a')) (j + 1) y (by omega)
        (by omega) (by omega) (by rw [hzε]; linarith) (by
          rw [hzε, hzℓ]; push_cast at hs2 ⊢; nlinarith) (by rw [hzR]; linarith) hy
      rw [show j + (b :: a).length = j + 1 + a.length by simp only [List.length_cons]; omega]
      exact ⟨r1, r2, r3, r4, r5⟩
  have hlen : a.length ≤ ℓ := by
    by_contra hlt
    rw [eighNodeAt_eq_none_of_lt_length hM hε hε₁ hR₀ hℓ hu hu₁ hτ₀ hτ hΩ A s
      (not_le.mp hlt)] at h
    cases h
  obtain ⟨r1, r2, r3, r4, r5⟩ := key a ⟨k, A, R₀, ε, ℓ⟩ s 0 y (by omega) le_rfl rfl le_rfl
    (by simp) le_rfl h
  rw [zero_add] at r2 r4
  exact ⟨hlen, r1, r2, hlow y _ hlen r2 r4, r3, r5⟩

/-- **The recursion tree has at most $(k + 1)(\ell + 1)$ nodes**: under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`, the set of paths at which
`NLAlib.eighNodeAt` has a node has at most $(k + 1)(\ell + 1)$ elements, $k$ the size of the root.
[Shah2024, proof of Theorem 4.2], $\lvert X \rvert \le nd$ there.
Proof: below the root every node has size at least $1$, and the sizes of the nodes at one depth
sum to at most $k$ (a split partitions its size, a shift keeps it, a leaf has no child: unfold
`NLAlib.eighChild`, `NLAlib.eighStep`); with the depth bound, at most $k + 1$ nodes at each of the
depths $0, \dots, \ell$ (`Set.encard_le_card`-type counting over `List Bool` of bounded length,
`Set.encard_iUnion_le`). L, about 70 lines. -/
theorem FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N) :
    {a : List Bool | eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}.encard ≤
      (k + 1) * (ℓ + 1) := by
  sorry

/-- A split of `NLAlib.eighStep` has both parts nonempty. -/
private lemma pos_and_lt_of_eighStep_eq_split {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ} {s : EighSample Su Sg N} {kp : ℕ}
    {h : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (hst : eighStep M N signFuel R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ) :
    0 < kp ∧ kp < k := by
  unfold eighStep at hst
  dsimp only at hst
  split_ifs at hst with h1 h2 h3 h4
  obtain ⟨rfl, -⟩ := EighStep.split.inj hst
  omega

/-- The split paths of length less than `m` number at most $k - 1$. -/
private lemma encard_eighNodeAt_isSplit_length_lt_le {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} (m : ℕ) :
    ∀ (x : EighNode F) (s : List Bool → EighSample Su Sg N),
    {a : List Bool | a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
      (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.encard ≤ (x.k - 1 : ℕ) := by
  induction m with
  | zero => intro x s; simp
  | succ m ih =>
    intro x s
    have hmem : ∀ a ∈ {a : List Bool | a.length < m + 1 ∧
        ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
          (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit},
        (a = [] ∧ (eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (s [])).IsSplit) ∨
        ∃ b a', a = b :: a' ∧ ∃ y', eighChild M N signFuel R₀ β x (s []) b = some y' ∧
          a' ∈ {a : List Bool | a.length < m ∧
            ∃ y, eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (b :: a))).IsSplit} := by
      rintro (_ | ⟨b, a'⟩) ⟨hlen, y, hy, hsp⟩
      · simp only [eighNodeAt, Option.some.injEq] at hy
        subst hy
        exact Or.inl ⟨rfl, hsp⟩
      · simp only [eighNodeAt, Option.bind_eq_some_iff] at hy
        obtain ⟨y', hy', hy⟩ := hy
        exact Or.inr ⟨b, a', rfl, y', hy', by simpa using hlen, y, hy, hsp⟩
    rcases hst : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (s []) with
      ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
    · refine le_of_eq_of_le (b := 0) (Set.encard_eq_zero.mpr ?_) bot_le
      refine Set.eq_empty_of_forall_notMem fun a ha => ?_
      rcases hmem a ha with ⟨-, h⟩ | ⟨b, a', -, y', hy', -⟩
      · rw [hst] at h; exact h
      · simp [eighChild, hst] at hy'
    · set y' : EighNode F := ⟨x.k, A', (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := List.cons b '' {a : List Bool | a.length < m ∧
            ∃ y, eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (b :: a))).IsSplit})
          fun a ha => ?_).trans ?_
      · rcases hmem a ha with ⟨-, h⟩ | ⟨b', a', rfl, z, hz, ha'⟩
        · rw [hst] at h; exact h.elim
        · simp only [eighChild, hst] at hz
          split_ifs at hz with hb
          · subst hb
            simp only [Option.some.injEq] at hz
            subst hz
            exact ⟨a', ha', rfl⟩
      · rw [(List.cons_injective).encard_image]
        exact ih y' _
    · obtain ⟨hkp0, hkpk⟩ := pos_and_lt_of_eighStep_eq_split M hst
      set yp : EighNode F := ⟨kp, Ap, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      set ym : EighNode F := ⟨x.k - kp, Am, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := {[]} ∪ (List.cons true '' {a : List Bool |
            a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β a yp (fun a' => s (true :: a')) =
              some y ∧ (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (true :: a))).IsSplit} ∪
          List.cons false '' {a : List Bool | a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β
            a ym (fun a' => s (false :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (false :: a))).IsSplit}))
          fun a ha => ?_).trans ?_
      · rcases hmem a ha with ⟨rfl, -⟩ | ⟨b', a', rfl, z, hz, ha'⟩
        · exact Or.inl rfl
        · simp only [eighChild, hst] at hz
          cases b'
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz
            subst hz
            exact Or.inr (Or.inr ⟨a', ha', rfl⟩)
          · simp only [↓reduceIte, Option.some.injEq] at hz
            subst hz
            exact Or.inr (Or.inl ⟨a', ha', rfl⟩)
      · refine (Set.encard_union_le _ _).trans ?_
        refine (add_le_add le_rfl (Set.encard_union_le _ _)).trans ?_
        rw [Set.encard_singleton, (List.cons_injective).encard_image,
          (List.cons_injective).encard_image]
        refine (add_le_add le_rfl (add_le_add (ih yp _) (ih ym _))).trans ?_
        have hk : 1 + (yp.k - 1 + (ym.k - 1)) ≤ x.k - 1 := by simp only [yp, ym]; omega
        exact_mod_cast hk

/-- **At most $k$ nodes split**: for every machine, root of size $k$, accuracy and samples, the set
of paths at which `NLAlib.eighNodeAt` has a node whose step `NLAlib.eighStep` (with that path's
sample) is a split has at most $k$ elements. [Shah2024, proof of Theorem 4.2],
$\lvert X_D \rvert = n - 1$ there.
Proof: the tree may be infinite (chains of shifts), so do not induct on the size alone: prove
$S_m(x) \le \max(k - 1, 0)$ for the splits at paths of length at most $m$, by induction on $m$
uniformly in $x$ (a shift: $S_m(x) = S_{m-1}(x')$ with the same size; a split: children of sizes
$k_+, k - k_+ \ge 1$ and $\max(k_+ - 1, 0) + \max(k - k_+ - 1, 0) + 1 \le k - 1$; a leaf: $0$;
count with `Set.encard_union_le` over the paths starting with `true` and `false`), then pass to
the union over $m$ (`Set.encard_iUnion_le`-type monotone limit). L, about 80 lines. -/
theorem encard_eighNodeAt_isSplit_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (s : List Bool → EighSample Su Sg N) :
    {a : List Bool | ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
      (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.encard ≤ x.k := by
  by_contra hlt
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt (not_le.mp hlt))
  have htf : t.Finite := Set.finite_of_encard_eq_coe (k := x.k + 1) (by simpa using htc)
  obtain ⟨m, hm⟩ := (htf.image List.length).bddAbove
  have hsub := Set.encard_le_encard (s := t) (t := {a : List Bool | a.length < m + 1 ∧
      ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
        (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit})
    fun a ha => ⟨Nat.lt_succ_of_le (hm ⟨a, ha, rfl⟩), hts ha⟩
  have h := hsub.trans (encard_eighNodeAt_isSplit_length_lt_le M (m + 1) x s)
  rw [htc] at h
  have h' : x.k + 1 ≤ x.k - 1 := by exact_mod_cast h
  omega

/-- **Global deterministic guarantee of spectral bisection**: let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u \ge 0$ and
$\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$ monotone and nonnegative and $c_{\mathrm N} \ge 0$; let
the stored $\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, for stored
$R_0 > 0$, $\varepsilon$ and $\beta$ (decoded values) with $0 < \varepsilon \le 2^{-15}$,
$0 < \theta \le 1$, a depth counter $\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$, and an
accuracy (a precomputed threshold)
$$0 < \beta \le \frac{\varepsilon\sqrt\theta}{2880\,\ell\, n^{3/2}\bigl(2\sqrt n +
\sqrt{2\log(16n/\theta)}\bigr)} \,, \qquad
N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac{\beta}{16n}\Bigr) \,.$$
Suppose $640\,n^{3/2}(8 + \mu_{\mathrm{MM}}(n))(N_* + 1)\cdot16n(n+1)\ell(\ell+1)\,u \le
\theta\beta$, $(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u
\le \beta$, the sign step limit is at least $N_*$, $0 \le \tau$,
$100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$ and
$16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)}) \le \Omega$ (each node has $R_y \le R_0$
and $\ell_y \le 2\ell$). If every internal node $y$ (size at
least $2$, and the machine's test $R_y \le \mathrm{fl}(\varepsilon_y R_0)$ fails) of the tree of
`NLAlib.eighNodeAt` has a good sample (`NLAlib.IsEighGoodSample` with $w_y = \theta
R_y/(2k_y\ell_y(n+1)(\ell+1))$, $x_y = \sqrt{\theta/(8n)}/k_y$, $t_y = \sqrt2(2\sqrt{k_y} +
\sqrt{2\log(16n/\theta)})$), then the decoded output of $\mathsf{eigh}(\mathbf{A}, \varepsilon)$
(`NLAlib.eigh`) is an approximate diagonalization of $\mathbf{A}$ with residual $2\varepsilon R_0$
and singular values within $\varepsilon/3$ of $1$. [Shah2024, Theorem 4.2], deterministic part.
Proof: induct on the fuel with the node-level hypotheses as a predicate over paths (the
children's trees are `eighNodeAt a y' (fun a' => s (b :: a'))` definitionally, so no snoc lemma
is needed); the depth is at most $\ell$
(`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`), so the budget $\ell + 1$ of
`NLAlib.eigh` is never exhausted. Treat leaves directly ($k \le 1$ exact; $R \le \varepsilon_y R_0$
residual $\le \varepsilon_y R_0$; the local lemma's $0 < w$ fails at a leaf with $R_y = 0$). At an
internal node apply
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`, its
matrix hypotheses coming from the parent through
`NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some` (at the root from
`hA`, `hR₀`), and its parameter hypotheses from the depth $j$: $k_y \le n$, $\ell \le \ell_y \le
2\ell$, $\varepsilon_y \ge \varepsilon/3$, $R_y \le R_0$, hence `NLAlib.bisectionSignTol` at $y$ is
at least $\beta$
(`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params`), $w_y/(4R_y) \ge
\theta/(16n(n+1)\ell(\ell+1))$ and $N_y \le N_*$ (`NLAlib.newtonSchulzSteps_le_of_le_abs`,
`NLAlib.newtonSchulzSteps_le_of_le`, monotone $\mu$), all up to the factors $(1 \pm u)^{4j}$ of the
machine-computed parameters: `husign` forces $u \le 10^{-11}\varepsilon$ and `hτ` bounds the floor
absolutely, so the floor error $u\tau$ in each $\varepsilon_j$ is negligible; the node floor
condition ($4k^{3/2}\tau \le \min(\sqrt{\rho/2}, \varepsilon_yR_0)$) and the depth lemmas'
($100\tau \le \varepsilon\min(R_0, 1)$) follow from `hτ` since $\varepsilon_y \ge \varepsilon/3$.
At the root $R = R_0$ gives residual $2\varepsilon R_0$. H, about 200 lines. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian) {R₀ ε β : F}
    {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω)
    {s : List Bool → EighSample ℝ ℂ n}
    (hgood : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
          (√(θ / (8 * n)) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (16 * n / θ)))) y
          (s a)) :
    IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β s).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β s).2 i)) (2 * dec ε * dec R₀) (dec ε / 3) := by
  sorry

end NLAlib
