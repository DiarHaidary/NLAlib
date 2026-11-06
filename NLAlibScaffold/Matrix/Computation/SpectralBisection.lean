/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisection.Global
public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.Matrix.Computation.NewtonSchulzSign

/-!
# Spectral bisection with sharper precision budgets (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/Matrix/Computation/SpectralBisection/` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, items I2, I3, I7–I10). The node
lemmas of [Shah2024, Lemma 4.1] are restated generically in the parameters $(w, x, t)$ of the good
event (shift distance, smallest singular value and norm thresholds of the Gaussian blocks), with
their precision hypotheses bundled in `NLAlib.FloatMachine.IsEighNodeBudget`: the probabilistic
choice of $(x, t)$ moves to the probability files, and the deflation tolerance becomes the single
condition $2t\beta/x \le \eta$. The global theorem EB5' uses a size-weighted union bound (each
node charged in proportion to its size, item I3), the sharp tolerance at the deepest node (EB2a',
item I2), and the sign theorem SN4' and deflation theorem DF2'.

## Main definitions

* `NLAlib.FloatMachine.IsEighNodeBudget`: the precision hypotheses of one node.

## Main results

* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget`
  (EB1c'), `NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_isEighNodeBudget` (EB1b'),
  `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget`
  (EB1d'), `NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_isEighNodeBudget`
  (EB1a'), `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget`
  (EB1').
* `NLAlib.FloatMachine.IsAccurate.mul_le_dec_ε_of_eighNodeAt_eq_some` (EB2a'),
  `NLAlib.sum_k_eighNodeAt_ofFn_le` (EB3').
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample'` (EB5').
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- `M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y`: the **precision budget of the
node $y$** of spectral bisection for a good event with shift distance $w$, smallest singular value
threshold $x$ and norm threshold $t$: the node's matrix is Hermitian with norm at most its window
$R$, its depth counter is at least $20$, $0 < \varepsilon \le 1/8$, $0 < w \le R$, $0 < x \le 1$,
$t \ge 2\sqrt2\sqrt k$, and, with $\nu = 4\mu_{\mathrm{MM}}(k) + 10 + 10\sqrt k$ and
$N_0 = N(w/(5R), \beta/(16k))$: the deflation tolerance $2t\beta/x \le
(1 - 1/\ell)\varepsilon/(5\ell)$, the sign condition $32\nu u \le (1 - 2^{-7})\,w\beta/(2R)$, the
stopping condition $2048(k + N_0 + 1)\nu u \le \beta$, the deflation rounding condition
$16(4\mu_{\mathrm{QR}}(k) + 4\sqrt k(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(k) + 1)u \le \beta$,
$k\beta \le 1/57600$, at least $N_0$ sign steps, and the floor and range conditions
$4k^{3/2}\tau \le \min(x, \varepsilon R_0)$, $16(R_0 + R + k + \ell + t) \le \Omega$. The
hypotheses of [Shah2024, Lemma 4.1] with the constants of SN4' and DF2'. -/
structure FloatMachine.IsEighNodeBudget {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    (u τ Ω : ℝ) (μM μQ : ℕ → ℝ) (cN : ℝ) (R₀ β : F) (signFuel : ℕ) (w x t : ℝ)
    (y : EighNode F) : Prop where
  /-- The product constant is nonnegative. -/
  nonneg_μM : 0 ≤ μM y.k
  /-- The QR constant is nonnegative. -/
  nonneg_μQ : 0 ≤ μQ y.k
  /-- The sampler constant is nonnegative. -/
  nonneg_cN : 0 ≤ cN
  /-- The unit roundoff is nonnegative. -/
  nonneg_u : 0 ≤ u
  /-- The node's matrix is Hermitian. -/
  isHermitian : (decodeMatrix dec y.A).IsHermitian
  /-- The node's matrix lies in its window. -/
  specNorm_le : specNorm (decodeMatrix dec y.A) ≤ dec y.R
  /-- The depth counter is at least $20$. -/
  twenty_le : 20 ≤ y.ℓ
  /-- The tolerance is positive. -/
  pos_ε : 0 < dec y.ε
  /-- The tolerance is at most $1/8$. -/
  ε_le : dec y.ε ≤ 1 / 8
  /-- The root scale is positive. -/
  pos_R₀ : 0 < dec R₀
  /-- The shift distance is positive. -/
  pos_w : 0 < w
  /-- The shift distance is at most the window. -/
  w_le : w ≤ dec y.R
  /-- The singular value threshold is positive. -/
  pos_x : 0 < x
  /-- The singular value threshold is at most $1$. -/
  x_le : x ≤ 1
  /-- The norm threshold is at least $2\sqrt2\sqrt k$. -/
  le_t : 2 * √2 * √(y.k : ℝ) ≤ t
  /-- The accuracy is positive. -/
  pos_β : 0 < dec β
  /-- The deflation tolerance. -/
  defl_tol : 2 * t / x * dec β ≤ (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)
  /-- The sign condition. -/
  sign_tol : 32 * (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤
    (1 - 2⁻¹ ^ 7) * w / (2 * dec y.R) * dec β
  /-- The stopping condition. -/
  stop_tol : 2048 * (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) *
    (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤ dec β
  /-- The deflation rounding condition. -/
  defl_u : 16 * (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β
  /-- The accuracy is small against the size. -/
  mul_β_le : (y.k : ℝ) * dec β ≤ 1 / 57600
  /-- Enough sign steps. -/
  fuel : newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel
  /-- The floor is nonnegative. -/
  nonneg_τ : 0 ≤ τ
  /-- The floor condition. -/
  τ_le : τ * (4 * y.k * √(y.k : ℝ)) ≤ min x (dec y.ε * dec R₀)
  /-- The range condition. -/
  Ω_le : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + t) ≤ Ω

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
  {N signFuel : ℕ} {R₀ β : F} {w x t : ℝ} {y : EighNode F}

/-- **Computed spectral projectors under a node budget** (EB1'c): at an internal node with
budget `NLAlib.FloatMachine.IsEighNodeBudget` and Event I (seed in $[-1, 1]$, every eigenvalue at
distance at least $w$ from the ideal shift), the stored $\mathbf{P}_\pm$ are within $\beta$ of
$\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c'\mathbf{I}))$. [Shah2024, proof of
Lemma 4.1].
Proof: Smallness facts: re-derive the conjuncts of `NLAlib.mul_le_of_le_bisectionSignTol` from the
budget ($k\beta \le 1/57600$ is `mul_β_le`; $k^2u$, $k^{3/2}u \le \beta/20480$ and $u \le
\beta/147456$ from `stop_tol`; $k\tau \le 1/4$ from `τ_le`; $10^6\ell u$, $10^5\ell\mu u \le
\varepsilon$ from `defl_tol` and `stop_tol`); the conjunct $k^{3/2}uR \le w\beta/20480$ is gone
(not derivable) and is replaced by the $\beta/64$ shift budget below. EB1c's proof with SN4'
(`NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le`)
at modulus $a = w - 4uR \ge (1 - 2^{-8})w$ and scale $b = \mathrm{fl}(2R) \le 2R(1 + 7u)$, so
$a/b \ge (1 - 2^{-7})w/(2R)$ (the field `sign_tol`) and $a/(2b) \ge w/(5R)$ (NS11 for the
step count and `stop_tol`); the shift error $4uR$ moves the sign by at most $8uR/w \le \beta/64$
(`Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le`), the rounded halving by at most
$u(\sqrt k + 2k\tau) \le \beta/64$. M, about 150 lines. -/
theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    (hint : M.le y.R (M.mul y.ε R₀) = false)
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

/-- The stored $\mathrm{fl}(2)$ is within $3u$ of $2$ (for $u \ge 0$, $0 \le \tau \le 1/4$ and
$2 \le \Omega$). -/
private theorem FloatMachine.IsAccurate.abs_dec_ofNat_two_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 4)
    (hΩ : 2 ≤ Ω) : 2 - 3 * u ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2 + 3 * u := by
  have h := le_and_le_of_isRoundingOf (hM.ofNat 2) (by norm_num) (by push_cast; linarith) hu hτ₀
  push_cast at h
  have := mul_le_mul_of_nonneg_left hτ1 hu
  constructor <;> linarith [h.1, h.2]

/-- The rounded trace $\mathrm{fl}(t + \mathrm{fl}(1/2))$ of a stored $\mathbf{X}$ whose diagonal
sum is within $1/57600$ of $r \le k$ (with $\sum_i \lvert x_{ii}\rvert \le 2k$) has floor $r$. -/
private theorem FloatMachine.IsAccurate.toNat_add_traceRe_div_eq {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) {k : ℕ}
    (hk1 : (1 : ℝ) ≤ k) (hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000) (hkτ : (k : ℝ) * τ ≤ 1 / 4)
    (hΩ : 16 * k ≤ Ω) (X : Matrix (Fin k) (Fin k) (F × F)) {r : ℕ} (hrk : (r : ℝ) ≤ k)
    (hdiag : |∑ i, dec (X i i).1 - r| ≤ 1 / 57600) (hsabs : ∑ i, |dec (X i i).1| ≤ 2 * k) :
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
  obtain ⟨h2a, h2b⟩ := hM.abs_dec_ofNat_two_sub_le hu hτ₀ hτ1 (by linarith)
  have hd2 : 1.9 ≤ dec (M.ofNat 2) := by linarith
  have hd20 : 0 < dec (M.ofNat 2) := by linarith
  have hh2 : 1 / dec (M.ofNat 2) ≤ 1 := by rw [div_le_one hd20]; linarith
  have hh := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.div M.one (M.ofNat 2) hd20.ne')
    (by rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)]; linarith) hu hτ₀)
  rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)] at hh
  have hh1 : |1 / dec (M.ofNat 2) - 1 / 2| ≤ u := by
    rw [div_sub_div _ _ hd20.ne' (by norm_num), abs_div, abs_of_pos (mul_pos hd20 two_pos),
      div_le_iff₀ (mul_pos hd20 two_pos), abs_le]
    have := mul_le_mul_of_nonneg_left hd2 hu
    constructor <;> linarith
  have hh1' := abs_le.mp hh1
  have := mul_le_mul_of_nonneg_left hh2 hu
  have hdh : |dec (M.div M.one (M.ofNat 2)) - 1 / 2| ≤ 3 * u := by
    rw [abs_le]; constructor <;> linarith
  have hdh' := abs_le.mp hdh
  -- their rounded sum
  have hzabs : |dec (M.traceRe X) + dec (M.div M.one (M.ofNat 2))| ≤ k + 1 := by
    rw [abs_le]; constructor <;> linarith
  have hz := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.add (M.traceRe X)
    (M.div M.one (M.ofNat 2))) (by linarith) hu hτ₀)
  have hzu := mul_le_mul_of_nonneg_left hzabs hu
  rw [hM.toNat_eq, Nat.floor_eq_iff (by linarith)]
  constructor <;> linarith

/-- The smallness facts of a node budget used for the rounded trace: $k^2u \le 10^{-5}$,
$k\tau \le 1/4$ and $16k \le \Omega$. -/
private theorem FloatMachine.IsEighNodeBudget.sq_mul_le
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk1 : (1 : ℝ) ≤ y.k) :
    (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (y.k : ℝ) * τ ≤ 1 / 4 ∧ 16 * (y.k : ℝ) ≤ Ω := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  have hkβ := hB.mul_β_le
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  have hsk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  -- smallness of `k u` and `k τ`
  have hku : (y.k : ℝ) * u ≤ dec β / 20480 := by
    have hN : (y.k : ℝ) ≤
        y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1 := by
      have hR := hB.pos_w.trans_le hB.w_le
      linarith [newtonSchulzSteps_nonneg (s := w / (5 * dec y.R)) (ε := dec β / (16 * y.k))
        (by have := hB.pos_w; positivity)
        (by rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le]) (by positivity)
        (by rw [div_le_iff₀ (by positivity)]; linarith)]
    have hν : (10 : ℝ) ≤ 4 * μM y.k + 10 + 10 * √(y.k : ℝ) := by
      linarith [hB.nonneg_μM, Real.sqrt_nonneg (y.k : ℝ)]
    have := mul_le_mul hN hν (by norm_num) (by linarith)
    have := mul_le_mul_of_nonneg_right this hu
    linarith [hB.stop_tol]
  have hk2u : (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have := mul_le_mul_of_nonneg_left hku (by linarith : (0 : ℝ) ≤ y.k)
    nlinarith
  have hkτ : (y.k : ℝ) * τ ≤ 1 / 4 := by
    have h1 := hB.τ_le.trans ((min_le_left _ _).trans hB.x_le)
    have := mul_le_mul_of_nonneg_left hsk (by positivity : (0 : ℝ) ≤ y.k * τ)
    nlinarith
  have hΩ : 16 * (y.k : ℝ) ≤ Ω := by
    have := hB.Ω_le
    have : (0 : ℝ) ≤ y.ℓ := by positivity
    linarith [hB.pos_R₀, hB.pos_w.trans_le hB.w_le, hB.le_t, 
      (by positivity : (0 : ℝ) ≤ 2 * √2 * √(y.k : ℝ))]
  exact ⟨hk2u, hkτ, hΩ⟩

/-- **Rank recovery under a node budget** (EB1b'): at an internal node of size $k \ge 2$ with
budget and Event I, the step splits iff $0 < i_+(\mathbf{A} - c'\mathbf{I}) < k$. [Shah2024,
proof of Lemma 4.1].
Proof: EB1b's proof with EB1c' in place of EB1c: the rounded trace of $\mathbf{P}_+$ is within
$k\beta + 2ku(k + k\tau) < 1/2$ of the inertia (`mul_β_le`, `stop_tol`). M, about 80 lines. -/
theorem FloatMachine.IsAccurate.eighStep_isSplit_iff_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) {smp : EighSample ℝ ℂ N}
    (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp).IsSplit ↔
      0 < inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ∧
      inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) < y.k := by
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  have hkβ := hB.mul_β_le
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  obtain ⟨hk2u, hkτ, hΩ⟩ := hB.sq_mul_le hk1
  -- the computed projector is near the ideal one, whose trace is the inertia
  obtain ⟨hP, -⟩ := hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget hB hint
    (smp := smp) hv hI
  set r := inertiaPos (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) with hr
  set Pp := M.hermScale (M.hermShift (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  have hA := hB.isHermitian
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul, abs_of_pos (by norm_num)]
    linarith [(specNorm_add_le 1 S).trans (add_le_add specNorm_one_le
      ((hA.sub (isHermitian_real_smul_one _)).specNorm_cfc_le zero_le_one fun x _ => by
        rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num))]
  have htr := hA.re_trace_smul_one_add_cfc_sign (c := dec y.R / y.ℓ * smp.1) fun x hx h => by
    have := hI x hx
    rw [h, sub_self, abs_zero] at this
    linarith [hB.pos_w]
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
  have hrk : r ≤ y.k := by
    rw [hr, inertiaPos]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hk2 := mul_le_mul_of_nonneg_left (by linarith : 1 + dec β ≤ 2) (Nat.cast_nonneg (α := ℝ) y.k)
  have hkp : min y.k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))) = r := by
    rw [hM.toNat_add_traceRe_div_eq hu hτ₀ hk1 hk2u hkτ hΩ Pp (by exact_mod_cast hrk)
      (hdiag.trans (by linarith)) (hsabs.trans (by linarith))]
    exact min_eq_right hrk
  unfold eighStep
  rw [if_neg (by omega), if_neg (by simp [hint])]
  dsimp only
  clear_value r
  split_ifs with h1 h2
  · rw [hkp] at h1
    exact iff_of_false id (by rw [h1]; exact fun h => h.2.false)
  · rw [hkp] at h2
    exact iff_of_false id (by rw [h2]; exact fun h => h.1.false)
  · rw [hkp] at h1 h2
    exact iff_of_true trivial ⟨Nat.pos_of_ne_zero h2, lt_of_le_of_ne hrk h1⟩

/-- **A split node under a node budget** (EB1d'): with budget and a good sample
(`NLAlib.IsEighGoodSample` with parameters $(w, x, t)$), a split gives frames $\mathbf{V}_\pm$,
unitaries $\mathbf{W}_\pm$ with $\|\mathbf{V}_\pm\mathbf{W}_\pm - \mathbf{Q}_\pm\|_2 \le \eta =
(1 - 1/\ell)\varepsilon/(5\ell)$ and children within $(2 + 2\eta)R\eta$ of the shifted
compressions, as EB1d. [Shah2024, proof of Lemma 4.1].
Proof: EB1d's proof with EB1c', EB1b' and DF2'
(`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`)
for $\mathbf{A} = \mathbf{V}\mathbf{V}^{\mathsf H}$, $\mathbf{S} = \mathbf{I}$: on Event II
$\|\mathbf{G}\|_2 < t$ and $\sigma_{\min}(\mathbf{V}^{\mathsf H}\mathbf{G}_1) > x$, so
$m \le (1 + 2\beta + 1/8)t/x$ and $\tfrac32 m\beta \le 2t\beta/x \le \eta$ (`defl_tol`). L, about
250 lines (EB1d's assembly reused). -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y smp)
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

/-- **Child invariant under a node budget** (EB1a'): with budget and a good sample, every child
has a Hermitian matrix of norm at most its window. [Shah2024, proof of Lemma 4.1].
Proof: EB1a's proof with EB1d' and EB1b' in place of EB1d and EB1b. M, about 120 lines. -/
theorem FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y smp)
    {b : Bool} {y' : EighNode F} (hy' : eighChild M N signFuel R₀ β y smp b = some y') :
    (decodeMatrix dec y'.A).IsHermitian ∧ specNorm (decodeMatrix dec y'.A) ≤ dec y'.R := by
  sorry

/-- **Local guarantee under a node budget** (EB1'): with budget, a good sample when internal and
children that are approximate diagonalizations with $(\varepsilon'(R' + R_0), \varepsilon'/3)$,
the node's output is one with $(\varepsilon(R + R_0), \varepsilon/3)$. [Shah2024, Lemma 4.1].
Proof: Smallness facts: re-derive the conjuncts of `NLAlib.mul_le_of_le_bisectionSignTol` from the
budget ($k\beta \le 1/57600$ is `mul_β_le`; $k^2u$, $k^{3/2}u \le \beta/20480$ and $u \le
\beta/147456$ from `stop_tol`; $k\tau \le 1/4$ from `τ_le`; $10^6\ell u$, $10^5\ell\mu u \le
\varepsilon$ from `defl_tol` and `stop_tol`); the conjunct $k^{3/2}uR \le w\beta/20480$ is gone
(not derivable) and is replaced by the $\beta/64$ shift budget below. EB1's proof (the residual
budget closing through $\varepsilon' = (1 - 1/\ell)\varepsilon$
is unchanged, since the deflation error is still at most $\eta$) with EB1c', EB1b', EB1d', EB1a'.
H, about 300 lines (EB1's private node budget reused). -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y (s []))
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

/-- The rounded next tolerance of a node: $\varepsilon' \le \varepsilon$ and
$\varepsilon(L - 1) - 3uL\varepsilon \le \varepsilon' L$. -/
private theorem FloatMachine.IsAccurate.le_dec_eighNextParams_snd_mul {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
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
  obtain ⟨hla, hlb⟩ := le_and_le_of_isRoundingOf (hM.ofNat L) hL0.le (by linarith) hu hτ₀
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
  obtain ⟨hqa, hqb⟩ := le_and_le_of_isRoundingOf (hM.div M.one (M.ofNat L) hdl0.ne')
    (by rw [hM.dec_one]; positivity) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hqa hqb
  have hq021 : 1 / dec (M.ofNat L) ≤ 0.21 := by linarith
  have hdq : 1 / L - u / 2 ≤ dec (M.div M.one (M.ofNat L)) ∧
      dec (M.div M.one (M.ofNat L)) ≤ 1 / L + u / 2 := by
    have := mul_le_mul_of_nonneg_left hq021 hu
    constructor <;> linarith
  obtain ⟨hsa, hsb⟩ := le_and_le_of_isRoundingOf (hM.sub M.one (M.div M.one (M.ofNat L)))
    (by rw [hM.dec_one]; linarith) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hsa hsb
  have hds : 1 - 1 / L - 1.6 * u ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) ∧
      dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 - 1 / L + 1.6 * u := by
    have := mul_le_mul_of_nonneg_left (show 1 - dec (M.div M.one (M.ofNat L)) ≤ 1 by linarith) hu
    constructor <;> linarith
  have hds0 : 0 ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) := by linarith
  have hds1 : dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 := by linarith
  have hdse := mul_le_of_le_one_left he0.le hds1
  obtain ⟨hea, heb⟩ := le_and_le_of_isRoundingOf (hM.mul (M.sub M.one (M.div M.one (M.ofNat L))) e)
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

/-- **The tolerance at a node, telescoped** (EB2a'): under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params`, every node $y$ below the root has
$$\varepsilon_y \ge (1 - 2^{-8})\,\frac{\ell - 1}{\ell_y - 1}\,\varepsilon \,,$$
in particular $\varepsilon_y \ge (1 - 2^{-8})(\ell - 1)\varepsilon/(2\ell - 1)$ since
$\ell_y \le 2\ell$; EB2a has $\varepsilon/3$. [Shah2024, proof of Theorem 4.2].
Proof: induction on the path as in EB2a: each level multiplies by $\mathrm{fl}(1 -
\mathrm{fl}(1/\ell_j)) \ge (1 - 1/\ell_j)(1 - 5u)$
(`NLAlib.FloatMachine.IsAccurate.dec_eighNextParams_le` and its lower companion), the exact
factors telescope to $(\ell - 1)/(\ell_y - 1)$, and
$(1 - 5u)^{\ell} \ge 1 - 5\ell u \ge 1 - 2^{-8}$ from $100\ell^2u \le 1$, $\ell \ge 20$. M, about
120 lines. -/
theorem FloatMachine.IsAccurate.mul_le_dec_ε_of_eighNodeAt_eq_some
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15)
    (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} {y : EighNode F}
    (h : eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = some y) :
    (1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((y.ℓ : ℝ) - 1)) * dec ε ≤ dec y.ε := by
  obtain ⟨hlen, -, hyℓ, -⟩ := hM.eighNodeAt_eq_some_params hε hε₁ hR₀ hℓ hu hu₁ hτ₀ hτ hΩ A s h
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
  -- each level loses at most `3 u ℓ_x ε_x ≤ 6 u ℓ ε` of `ε_x (ℓ_x - 1)`
  have key : ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N) (j : ℕ)
      (y : EighNode F), j + a.length ≤ ℓ → x.ℓ = ℓ + j → dec x.ε ≤ dec ε →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) →
      eighNodeAt M N signFuel R₀ β a x s = some y →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * (j + a.length : ℕ) ≤ dec y.ε * (y.ℓ - 1) := by
    intro a
    induction a with
    | nil =>
      intro x s j y _ h2 _ h4 h
      cases Option.some.inj h
      simpa using h4
    | cons b a ih =>
      intro x s j y hj h2 h3 h4 h
      simp only [eighNodeAt, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, hy⟩ := h
      obtain ⟨-, -, -, -, hzε, hzℓ⟩ := le_eq_false_and_le_and_eq_of_eighChild_eq_some hz
      simp only [List.length_cons] at hj
      have hxε := hlow x j (by omega) h2 h4
      have hx0 : 0 < dec x.ε := by linarith
      have hxℓ : (x.ℓ : ℝ) ≤ 2 * ℓ := by
        rw [h2]; push_cast; linarith [(by exact_mod_cast (by omega : j ≤ ℓ) : (j : ℝ) ≤ ℓ)]
      have hxℓ5 : 5 ≤ x.ℓ := by
        have : (5 : ℝ) ≤ x.ℓ := by rw [h2]; push_cast; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
        exact_mod_cast this
      have huL : u * x.ℓ ≤ 1 / 1000 := by nlinarith
      obtain ⟨hs1, hs2⟩ := hM.le_dec_eighNextParams_snd_mul x.R x.ε hu huL hτ₀ (by linarith) hx0
        (by linarith) (by linarith) hxℓ5 (by linarith)
      have hloss := mul_le_mul_of_nonneg_left
        (mul_le_mul hxℓ h3 hx0.le (by positivity)) (by positivity : (0 : ℝ) ≤ 3 * u)
      have r := ih z (fun a' => s (b :: a')) (j + 1) y (by omega) (by omega)
        (by rw [hzε]; linarith) (by
          rw [hzε, hzℓ]; push_cast at hs2 ⊢; nlinarith) hy
      rwa [show j + (b :: a).length = j + 1 + a.length by simp only [List.length_cons]; omega]
  have r := key a ⟨k, A, R₀, ε, ℓ⟩ s 0 y (by omega) rfl le_rfl (by simp) h
  rw [zero_add, hyℓ] at r
  rw [hyℓ]
  push_cast at r ⊢
  have hlen' : (a.length : ℝ) ≤ ℓ := by exact_mod_cast hlen
  have hd : (0 : ℝ) < ℓ + a.length - 1 := by linarith [(a.length.cast_nonneg : (0 : ℝ) ≤ _)]
  rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hd]
  have h1 := mul_le_mul_of_nonneg_left hlen' (by positivity : 0 ≤ 6 * u * ℓ * dec ε)
  have h2 : 6 * u * ℓ * dec ε * ℓ ≤ 6 / 100 * dec ε := by nlinarith
  nlinarith

/-- The sizes of the two children of a node sum to at most its size. -/
private lemma sum_k_eighChild_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (smp : EighSample Su Sg N) :
    (eighChild M N signFuel R₀ β x smp true).elim 0 EighNode.k +
      (eighChild M N signFuel R₀ β x smp false).elim 0 EighNode.k ≤ x.k := by
  unfold eighChild
  split
  · simp
  · rename_i b' _ _ _
    cases b' <;> simp
  · rename_i kp hkp _ _ _ _ _ _
    simp only [if_true, Option.elim_some, Bool.false_eq_true, if_false]
    omega

/-- **The sizes at one depth sum to at most the root size** (EB3'): for every machine, node
$x$, tree of samples and depth $j$, the sizes of the nodes at the paths of length $j$ sum to at
most $k_x$ (a node has no child, one child of its size, or two children of sizes $k_+$ and
$k - k_+$). [Shah2024, proof of Theorem 4.2], "$\sum_{x \in X_k} n_x \le n$".
Proof: induction on $j$ generalizing $x$ and the samples: split a path of length $j + 1$ by its
head (`Fin.consEquiv`, `List.ofFn_succ`, `Fintype.sum_prod_type`); `NLAlib.eighNodeAt` at
$b :: a$ is the node at $a$ below `NLAlib.eighChild` on side $b$; the induction hypothesis bounds
each side by its child's size (for its use in EV6' over the depths $j \le \ell$:
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` gives $|a| \le \ell$ and $\ell_y = \ell +
|a|$); the children's sizes sum to at most $k_x$ by cases on
`NLAlib.eighStep` (`Nat.add_sub_cancel'`). L, about 120 lines (EB4's case analysis reused). -/
theorem sum_k_eighNodeAt_ofFn_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (s : List Bool → EighSample Su Sg N) (j : ℕ) :
    ∑ a : Fin j → Bool,
      ((eighNodeAt M N signFuel R₀ β (List.ofFn a) x s).elim 0 EighNode.k) ≤ x.k := by
  induction j generalizing x s with
  | zero => simp [eighNodeAt]
  | succ j ih =>
    rw [← (Fin.consEquiv fun _ : Fin (j + 1) => Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      eighNodeAt]
    have hb : ∀ b : Bool, ∑ a : Fin j → Bool,
        ((eighChild M N signFuel R₀ β x (s []) b).bind fun y =>
          eighNodeAt M N signFuel R₀ β (List.ofFn fun i => a i) y
            fun a' => s (b :: a')).elim 0 EighNode.k ≤
        (eighChild M N signFuel R₀ β x (s []) b).elim 0 EighNode.k := by
      intro b
      rcases eighChild M N signFuel R₀ β x (s []) b with _ | y
      · simp
      · exact ih y _
    exact (add_le_add (hb true) (hb false)).trans (sum_k_eighChild_le M x (s []))

/-- **Global deterministic guarantee of spectral bisection, sharp budget** (EB5'): let the
machine meet `NLAlib.FloatMachine.IsAccurate` with $u \ge 0$, $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$ monotone and nonnegative and $c_{\mathrm N} \ge 0$; let the stored
$\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, $R_0 > 0$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $\ell \ge$ `NLAlib.bisectionDepth`
$\varepsilon$, $m = \min(n, \ell + 1)$, $\hat T = 2\sqrt2\sqrt n + \sqrt{\log(96nm/\theta)}$,
$\nu = 4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n$, the accuracy
$$0 < \beta \le \frac{(\ell - 1)^2\,\varepsilon\sqrt\theta}{52\,\ell^2(2\ell - 1)
\sqrt{n m \min(n, e)}\;\hat T} \,, \qquad
N_* = N\Bigl(\frac{\theta}{12n\ell(\ell + 1)}, \frac{\beta}{16n}\Bigr) \,,$$
$146\,n\ell(\ell + 1)\,\nu u \le \theta\beta$, $2048(n + N_* + 1)\nu u \le \beta$,
$16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u \le \beta$,
at least $N_*$ sign steps, $0 \le \tau$, $100n^{3/2}\tau \le \min(\sqrt{\theta/(8nm)},
\varepsilon\min(R_0, 1))$ and $16(2R_0 + n + 2\ell + \hat T) \le \Omega$. If every internal node
$y$ has a good sample with $w_y = 4\theta R_y/(9n\ell(\ell + 1))$, $\rho_y = \theta k_y/(6nm)$,
$x_y = \sqrt{15\rho_y/(16\min(k_y^2, e k_y))}$ and $t_y = 2\sqrt2\sqrt{k_y} +
\sqrt{\log(16/\rho_y)}$, then `NLAlib.eigh` is an approximate diagonalization of $\mathbf{A}$
with residual $2\varepsilon R_0$ and singular values within $\varepsilon/3$ of $1$. [Shah2024,
Theorem 4.2], deterministic part.
Proof: EB5's induction over the tree with EB1' and EB1a' in place of EB1 and EB1a (the node
lemmas re-derive their smallness facts from the budget, not from
`NLAlib.mul_le_of_le_bisectionSignTol`; the $k^{3/2}uR$ conjunct is gone): at each node,
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` (EB2a) and EB2a' give $k_y \le n$,
$\ell \le \ell_y \le 2\ell$, $\varepsilon_y \ge (1 - 2^{-8})(\ell -
1)\varepsilon/(2\ell - 1)$, $R_y \le R_0$; then `NLAlib.FloatMachine.IsEighNodeBudget` at
$(w_y, x_y, t_y)$: `defl_tol` since $x_y/t_y \ge \sqrt{5\theta/(32nm\min(n, e))}/\hat T$ and
$\eta_y \ge (1 - 2^{-8})(\ell - 1)^2\varepsilon/(10\ell^2(2\ell - 1))$; `sign_tol` from the
$146$-condition and monotone $\mu_{\mathrm{MM}}$; `fuel`, `stop_tol` by NS11/NS12 since
$w_y/(5R_y) \ge \theta/(12n\ell(\ell + 1))$; floor and range from the global ones. H, about 300
lines (EB5's skeleton reused). -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample'
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian) {ε : F}
    {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω)
    {s : List Bool → EighSample ℝ ℂ n}
    (hgood : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
          (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
            (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
          (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))))))
          y (s a)) :
    IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β s).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β s).2 i)) (2 * dec ε * dec R₀) (dec ε / 3) := by
  sorry

end NLAlib
