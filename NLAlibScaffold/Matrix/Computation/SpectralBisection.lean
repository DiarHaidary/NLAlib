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
  sorry

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
  sorry

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
