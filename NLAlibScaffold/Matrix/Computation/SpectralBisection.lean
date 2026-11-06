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

/-- A Hermitian eigenvalue is bounded by the spectral norm. -/
private theorem abs_le_of_mem_spectrum_of_specNorm_le {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {R x : ℝ} (hR : specNorm X ≤ R) (hx : x ∈ spectrum ℝ X) : |x| ≤ R := by
  rw [hX.spectrum_eq_image_eigenvalue] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact (hX.abs_eigenvalue_le_specNorm j).trans hR

/-- The frame of the positive spectral projector, with a prescribed column count. -/
private theorem exists_frame_pos {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) {R c : ℝ} (hR : specNorm A ≤ R) (hc : ∀ x ∈ spectrum ℝ A, x ≠ c)
    {r : ℕ} (hr : inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) = r) :
    ∃ V : Matrix (Fin k) (Fin r) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ∧
      spectrum ℝ (Vᴴ * A * V) ⊆ Set.Icc c R := by
  subst hr
  obtain ⟨V, hV, hVV, -, hsp⟩ := hA.exists_hasOrthonormalCols_mul_conjTranspose_eq hc
  refine ⟨V, hV, hVV, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hsp hx
  exact ⟨le_of_lt h2, (le_abs_self x).trans (abs_le_of_mem_spectrum_of_specNorm_le hA hR h1)⟩

/-- The frame of the negative spectral projector, with the complementary column count. -/
private theorem exists_frame_neg {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) {R c : ℝ} (hR : specNorm A ≤ R) (hc : ∀ x ∈ spectrum ℝ A, x ≠ c)
    {m : ℕ} (hm : inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) = m) (hmk : m ≤ k) :
    ∃ V : Matrix (Fin k) (Fin (k - m)) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ∧
      spectrum ℝ (Vᴴ * A * V) ⊆ Set.Icc (-R) c := by
  set X := A - c • (1 : Matrix (Fin k) (Fin k) ℂ) with hXdef
  have hX : X.IsHermitian := hA.sub (isHermitian_real_smul_one c)
  have hc' : ∀ x ∈ spectrum ℝ (-A), x ≠ -c := by
    intro x hx hxc
    rw [← spectrum.neg_eq] at hx
    exact hc (-x) (Set.mem_neg.mp hx) (by rw [hxc, neg_neg])
  have heq : -A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ) = -X := by
    rw [hXdef, neg_smul]; abel
  have hunit : IsUnit X := by
    have hcn : c ∉ spectrum ℝ A := fun h => hc c h rfl
    rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hcn
    rw [show X = -(c • (1 : Matrix (Fin k) (Fin k) ℂ) - A) by rw [hXdef]; abel]
    exact hcn.neg
  have hrank : X.rank = k := by rw [Matrix.rank_of_isUnit X hunit, Fintype.card_fin]
  have hrk : inertiaPos (-A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ)) = k - m := by
    rw [heq, ← inertiaNeg_eq_inertiaPos_neg]
    have := hX.inertiaPos_add_inertiaNeg
    omega
  have key := hA.neg.exists_hasOrthonormalCols_mul_conjTranspose_eq hc'
  rw [hrk] at key
  obtain ⟨V, hV, hVV, -, hsp⟩ := key
  refine ⟨V, hV, ?_, fun x hx => ?_⟩
  · rw [hVV, heq]
    have hs : cfc Real.sign (-X) = -cfc Real.sign X := by
      rw [← cfc_comp_neg Real.sign X ((X.finite_real_spectrum.image _).continuousOn _)
        hX.isSelfAdjoint]
      rw [show (fun x : ℝ => Real.sign (-x)) = fun x => -Real.sign x from
        funext fun x => Real.sign_neg, cfc_neg]
    rw [hs, ← sub_eq_add_neg]
  · have hx' : -x ∈ spectrum ℝ (Vᴴ * -A * V) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, ← spectrum.neg_eq]
      exact Set.neg_mem_neg.mpr hx
    obtain ⟨h1, h2⟩ := hsp hx'
    rw [← spectrum.neg_eq] at h1
    have := abs_le_of_mem_spectrum_of_specNorm_le hA hR (by simpa using h1)
    rw [Set.mem_Ioi] at h2
    exact ⟨(neg_abs_le x).trans' (by linarith), by linarith⟩

/-- A square matrix whose action is bounded below by `x` is a unit with inverse of norm `≤ 1/x`. -/
private lemma isUnit_and_specNorm_inv_le {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ}
    {x : ℝ} (hx : 0 < x)
    (h : ∀ z : Fin r → ℂ, x * ‖WithLp.toLp 2 z‖ ≤ ‖WithLp.toLp 2 (M *ᵥ z)‖) :
    IsUnit M ∧ specNorm M⁻¹ ≤ 1 / x := by
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have h0 : x * ‖WithLp.toLp 2 (a - b)‖ ≤ 0 := by
      have := h (a - b)
      rw [Matrix.mulVec_sub, hab, sub_self] at this
      simpa using this
    have hn : ‖WithLp.toLp 2 (a - b)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (WithLp.toLp 2 (a - b))]) (norm_nonneg _)
    simpa [sub_eq_zero] using hn
  have hU : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  refine ⟨hU, (specNorm_le_iff (by positivity)).2 fun y => ?_⟩
  have h1 := h (M⁻¹ *ᵥ y)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hU),
    Matrix.one_mulVec] at h1
  rw [one_div_mul_eq_div, le_div_iff₀ hx]
  linarith [mul_comm x ‖WithLp.toLp 2 (M⁻¹ *ᵥ y)‖]

/-- The product contract through `decodeMatrix`. -/
private theorem FloatMachine.IsAccurate.specNorm_mul_sub_decodeMatrix_mm_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (F × F))
    (B : Matrix (Fin m) (Fin n) (F × F))
    (h : specNorm (decodeMatrix dec A) * specNorm (decodeMatrix dec B) ≤ Ω) :
    specNorm (decodeMatrix dec A * decodeMatrix dec B - decodeMatrix dec (M.mm A B)) ≤
      μM (max l (max m n)) * u *
        max (specNorm (decodeMatrix dec A) * specNorm (decodeMatrix dec B)) τ :=
  hM.isMatMulErr.specNorm_mul_sub_le A B h

/-- Replacing the frame $\mathbf{Z}$ ($\|\mathbf{Z}\|_2 \le 1$) of a compression by a matrix
within $e$ of it costs at most $Re(2 + e)$, for $\|\mathbf{A}\|_2 \le R$. -/
private theorem specNorm_conjTranspose_mul_mul_sub_le {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m m ℂ} {Z Q : Matrix m n ℂ} {R e : ℝ} (hA : specNorm A ≤ R)
    (hZ : specNorm Z ≤ 1) (he : specNorm (Z - Q) ≤ e) :
    specNorm (Zᴴ * A * Z - Qᴴ * A * Q) ≤ R * (e * (2 + e)) := by
  have hR0 : 0 ≤ R := (specNorm_nonneg _).trans hA
  have he0 : 0 ≤ e := (specNorm_nonneg _).trans he
  have hQ : specNorm Q ≤ 1 + e := by
    rw [show Q = Z - (Z - Q) by abel]; exact (specNorm_sub_le _ _).trans (add_le_add hZ he)
  have hZA : specNorm (Zᴴ * A) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul (by rw [specNorm_conjTranspose]; exact hZ) hA
      (specNorm_nonneg _) zero_le_one).trans (one_mul R).le)
  rw [show Zᴴ * A * Z - Qᴴ * A * Q = Zᴴ * A * (Z - Q) + (Z - Q)ᴴ * A * Q by
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]; abel]
  refine (specNorm_add_le _ _).trans ?_
  have h1 : specNorm (Zᴴ * A * (Z - Q)) ≤ R * e :=
    (specNorm_mul_le _ _).trans (mul_le_mul hZA he (specNorm_nonneg _) hR0)
  have h2 : specNorm ((Z - Q)ᴴ * A * Q) ≤ R * e * (1 + e) := by
    refine (specNorm_mul_le _ _).trans (mul_le_mul ?_ hQ (specNorm_nonneg _) (mul_nonneg hR0 he0))
    refine (specNorm_mul_le _ _).trans ?_
    rw [specNorm_conjTranspose, mul_comm R]
    exact mul_le_mul he hA (specNorm_nonneg _) he0
  linarith [show R * e + R * e * (1 + e) = R * (e * (2 + e)) by ring]

/-- The two stored products of a compression, against the exact compression by `V W`. -/
private theorem FloatMachine.IsAccurate.specNorm_compress_sub_decodeMatrix_mm_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hrk : r ≤ k) {β e R : ℝ}
    (hu0 : 0 ≤ u) (hμ0 : 0 ≤ μM k) (hμ : μM k * u ≤ β / 2)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 500)
    (hR0 : 0 < R) (hτ0 : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R) (hΩ : 4 * R ≤ Ω)
    {As : Matrix (Fin k) (Fin k) (F × F)} (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {Q : Matrix (Fin k) (Fin r) (F × F)} {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hW : HasOrthonormalCols W)
    (he : specNorm (V * W - decodeMatrix dec Q) ≤ e) :
    specNorm ((V * W)ᴴ * decodeMatrix dec As * (V * W) -
      decodeMatrix dec (M.mm (M.mm (M.conjTransposeMat Q) As) Q)) ≤
        R * (e * (2 + e)) + 136 / 100 * β * R := by
  set A := decodeMatrix dec As with hAdef
  set Qb := decodeMatrix dec Q with hQbdef
  have heR' : (1 + e) * R ≤ 1002 / 1000 * R := mul_le_mul_of_nonneg_right (by linarith) hR0.le
  have hτR : τ ≤ R / 3 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith [mul_le_mul_of_nonneg_right this hτ0]
  have hβR := mul_le_mul_of_nonneg_right hβ1 hR0.le
  have hβR0 := mul_nonneg hβ0 hR0.le
  have hA0 := specNorm_nonneg A
  have hμu0 : 0 ≤ μM k * u := mul_nonneg hμ0 hu0
  have hQ : specNorm Qb ≤ 1 + e := by
    rw [show Qb = V * W - (V * W - Qb) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith [(hV.mul hW).specNorm_le_one])
  have hQ0 := specNorm_nonneg Qb
  -- the first product
  have hQH : decodeMatrix dec (M.conjTransposeMat Q) = Qbᴴ := hM.decodeMatrix_conjTransposeMat Q
  have hQA : specNorm Qbᴴ * specNorm A ≤ (1 + e) * R := by
    rw [specNorm_conjTranspose]; exact mul_le_mul hQ hAR hA0 (by linarith)
  have hm1 := hM.specNorm_mul_sub_decodeMatrix_mm_le (M.conjTransposeMat Q) As
    (by rw [hQH]; linarith)
  rw [hQH, ← hAdef, show max r (max k k) = k by omega] at hm1
  set C1 := decodeMatrix dec (M.mm (M.conjTransposeMat Q) As) with hC1def
  have hd1 : specNorm (Qbᴴ * A - C1) ≤ β / 2 * (134 / 100 * R) :=
    hm1.trans ((mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hμu0).trans
      (mul_le_mul_of_nonneg_right hμ (by linarith)))
  have hC1 : specNorm C1 ≤ 1003 / 1000 * R := by
    rw [show C1 = Qbᴴ * A - (Qbᴴ * A - C1) by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith [(specNorm_mul_le Qbᴴ A).trans hQA]
  -- the second product
  have hC1Q : specNorm C1 * specNorm Qb ≤ 1006 / 1000 * R := by
    have := mul_le_mul hC1 hQ hQ0 (by linarith)
    have h2 : 1003 / 1000 * R * (1 + e) ≤ 1003 / 1000 * R * (1002 / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hm2 := hM.specNorm_mul_sub_decodeMatrix_mm_le (M.mm (M.conjTransposeMat Q) As) Q
    (by rw [← hC1def]; linarith)
  rw [← hC1def, ← hQbdef, show max r (max k r) = k by omega] at hm2
  set C2 := decodeMatrix dec (M.mm (M.mm (M.conjTransposeMat Q) As) Q)
  have hd2 : specNorm (C1 * Qb - C2) ≤ β / 2 * (134 / 100 * R) :=
    hm2.trans ((mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hμu0).trans
      (mul_le_mul_of_nonneg_right hμ (by linarith)))
  -- the exact compression
  have hHQ := specNorm_conjTranspose_mul_mul_sub_le hAR (hV.mul hW).specNorm_le_one he
  rw [show (V * W)ᴴ * A * (V * W) - C2 = ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb) +
    (Qbᴴ * A - C1) * Qb + (C1 * Qb - C2) by rw [Matrix.sub_mul]; abel]
  have h3 := specNorm_add_le ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb + (Qbᴴ * A - C1) * Qb)
    (C1 * Qb - C2)
  have h4 := specNorm_add_le ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb) ((Qbᴴ * A - C1) * Qb)
  have h1 := (specNorm_mul_le (Qbᴴ * A - C1) Qb).trans (mul_le_mul hd1 hQ hQ0 (by positivity))
  have : β / 2 * (134 / 100 * R) * (1 + e) ≤ β / 2 * (134 / 100 * R) * (1 + 1 / 500) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- The Hermitian average $d^{-1}(\mathbf{C} + \mathbf{C}^{\mathsf{H}})$, for
$\lvert d - 2\rvert \le 3u$ ($u \le 1/1000$), of a $\mathbf{C}$ within $\delta \le R/100$ of a
Hermitian $\mathbf{H}$ with $\|\mathbf{H}\|_2 \le R$, is within $\delta + 3uR/100 + 3uR$ of
$\mathbf{H}$. -/
private theorem specNorm_sub_inv_smul_add_conjTranspose_le {n : Type*} [Fintype n]
    {H C : Matrix n n ℂ} {R δ u d : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 1000) (hHh : Hᴴ = H)
    (hH : specNorm H ≤ R) (hHC : specNorm (H - C) ≤ δ) (hδ : δ ≤ R / 100)
    (hd : |d - 2| ≤ 3 * u) :
    specNorm (H - d⁻¹ • (C + Cᴴ)) ≤ δ + 3 * u * (R / 100) + 3 * u * R := by
  obtain ⟨hda, hdb⟩ := abs_le.mp hd
  have hd1 : 1 ≤ d := by linarith
  have ha : d⁻¹ * d = 1 := inv_mul_cancel₀ (by linarith)
  have ha0 : 0 < d⁻¹ := inv_pos.mpr (by linarith)
  have ha1 : d⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd1
  have h2a : 2 * d⁻¹ ≤ 1 + 3 * u := by
    linarith [mul_le_mul_of_nonneg_left (by linarith : 2 - 3 * u ≤ d) ha0.le,
      mul_le_mul_of_nonneg_right ha1 (by linarith : 0 ≤ 3 * u)]
  have h1a : |1 - 2 * d⁻¹| ≤ 3 * u := by
    rw [show 1 - 2 * d⁻¹ = d⁻¹ * (d - 2) by rw [mul_sub, ha]; ring, abs_mul, abs_of_pos ha0]
    linarith [mul_le_mul_of_nonneg_left hd ha0.le,
      mul_le_mul_of_nonneg_right ha1 (by linarith : 0 ≤ 3 * u)]
  rw [show H - d⁻¹ • (C + Cᴴ) = d⁻¹ • ((H - C) + (H - C)ᴴ) + (1 - 2 * d⁻¹) • H by
    rw [Matrix.conjTranspose_sub, hHh]; module]
  refine (specNorm_add_le _ _).trans ?_
  rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos ha0]
  have hHC0 := specNorm_nonneg (H - C)
  have h1 : specNorm ((H - C) + (H - C)ᴴ) ≤ 2 * specNorm (H - C) := by
    have := specNorm_add_le (H - C) (H - C)ᴴ
    rw [specNorm_conjTranspose] at this; linarith
  have h2 := mul_le_mul_of_nonneg_left h1 ha0.le
  have h3 := mul_le_mul_of_nonneg_right h2a hHC0
  have h4 := mul_le_mul h1a hH (specNorm_nonneg _) (by linarith)
  have h5 := mul_le_mul_of_nonneg_left (hHC.trans hδ) (by linarith : 0 ≤ 3 * u)
  linarith

/-- The stored Hermitian average and shift of a matrix near a Hermitian `H`. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_hermShift_hermAvg_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {r : ℕ} {β R δ : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hβ1 : β ≤ 1 / 115200) (hR0 : 0 < R)
    (hτ0 : 0 ≤ τ) (hτR : τ ≤ R / 3) (hrτ : (r : ℝ) * τ ≤ R / 3) (hsr : √(r : ℝ) * u ≤ β / 4)
    (hΩ : 4 * R ≤ Ω) {H : Matrix (Fin r) (Fin r) ℂ} (hHh : Hᴴ = H) (hH : specNorm H ≤ R)
    {X : Matrix (Fin r) (Fin r) (F × F)} (hHC2 : specNorm (H - decodeMatrix dec X) ≤ δ)
    (hδ : δ ≤ R / 100) {two s : F} (htwo : |dec two - 2| ≤ 3 * u) (hs : |dec s| ≤ R) :
    specNorm (decodeMatrix dec (M.hermShift (M.hermAvg X two) s) -
      (H - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
        δ + 3 * u * (R / 100) + 3 * u * R + (3 * (β / 4) * (102 / 100 * R) + 2 * (u * R)) +
          u * (21 / 10 * R + R / 3) := by
  have hβR : β * R ≤ R / 115200 := by nlinarith [mul_le_mul_of_nonneg_right hβ1 hR0.le]
  set C2 := decodeMatrix dec X with hC2def
  set d := dec two with hddef
  have hd1 : 1 ≤ d := by linarith [(abs_le.mp htwo).1]
  set Hs := d⁻¹ • (C2 + C2ᴴ) with hHsdef
  have hHHs := specNorm_sub_inv_smul_add_conjTranspose_le hu0 (by linarith) hHh hH hHC2 hδ htwo
  rw [← hHsdef] at hHHs
  have huR : u * R ≤ β * R := mul_le_mul_of_nonneg_right hu1 hR0.le
  have hHs : specNorm Hs ≤ 102 / 100 * R := by
    rw [show Hs = H - (H - Hs) by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith
  have hC2 : specNorm C2 ≤ 101 / 100 * R := by
    rw [show C2 = H - (H - C2) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith)
  have hAvg := hM.specNorm_sub_decodeMatrix_hermAvg_le hu0 (by linarith) hτ0 X (c := two)
    (by rw [← hddef, abs_of_pos (by linarith)]; exact hd1) (by rw [← hC2def]; linarith)
  rw [← hC2def, ← hddef, ← hHsdef] at hAvg
  set Y := decodeMatrix dec (M.hermAvg X two) with hYdef
  have hHsY : specNorm (Hs - Y) ≤ 3 * (β / 4) * (102 / 100 * R) + 2 * (u * R) := by
    refine hAvg.trans ?_
    rw [show 3 * u * (√(r : ℝ) * specNorm Hs + 2 * r * τ) =
      3 * (√(r : ℝ) * u) * specNorm Hs + 6 * u * (r * τ) by ring]
    have h1 : 3 * (√(r : ℝ) * u) * specNorm Hs ≤ 3 * (β / 4) * (102 / 100 * R) :=
      mul_le_mul (by linarith) hHs (specNorm_nonneg _) (by linarith)
    linarith [mul_le_mul_of_nonneg_left hrτ (by linarith : 0 ≤ 6 * u)]
  -- the shift
  set I := (1 : Matrix (Fin r) (Fin r) ℂ)
  have hs1 : specNorm (dec s • I) ≤ R := by
    rw [specNorm_real_smul]
    exact (mul_le_mul hs specNorm_one_le (specNorm_nonneg _) hR0.le).trans (mul_one R).le
  have hYs : specNorm (Y - dec s • I) ≤ 21 / 10 * R := by
    rw [show Y - dec s • I = Hs - (Hs - Y) - dec s • I by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith [specNorm_sub_le Hs (Hs - Y)]
  have hYh : Y.IsHermitian := hM.isHermitian_decodeMatrix_hermFrom _ _
  have hSh := (hM.specNorm_sub_decodeMatrix_hermShift_le hu0 hYh s (by linarith)).trans
    (mul_le_mul_of_nonneg_left (max_le (c := 21 / 10 * R + R / 3) (by linarith) (by linarith)) hu0)
  rw [← hYdef] at hSh
  rw [show decodeMatrix dec (M.hermShift (M.hermAvg X two) s) - (H - dec s • I) =
    -((H - Hs) + (Hs - Y)) - ((Y - dec s • I) - decodeMatrix dec (M.hermShift (M.hermAvg X two) s))
      by abel]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_neg]
  linarith [specNorm_add_le (H - Hs) (Hs - Y)]

/-- The stored compression of a deflated basis near `V W`. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_compress_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hrk : r ≤ k) {β η R : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β / 1000) (hμ0 : 0 ≤ μM k) (hμ : μM k * u ≤ β / 2)
    (hsk : √(k : ℝ) * u ≤ β / 4) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (hβη : β ≤ η / 8)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 800)
    (hR0 : 0 < R) (hτ0 : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R) (hΩ : 4 * R ≤ Ω)
    {As : Matrix (Fin k) (Fin k) (F × F)} (hAh : (decodeMatrix dec As).IsHermitian)
    (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {Q : Matrix (Fin k) (Fin r) (F × F)} {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hW : HasOrthonormalCols W)
    (he : specNorm (V * W - decodeMatrix dec Q) ≤ 17 / 20 * η)
    {two s : F} (htwo : |dec two - 2| ≤ 3 * u) (hs : |dec s| ≤ R) :
    specNorm (decodeMatrix dec
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) As) Q) two) s) -
      (Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
        (2 + 2 * η) * R * η := by
  have hP1 := hM.specNorm_compress_sub_decodeMatrix_mm_le hk1 hrk hu0 hμ0 hμ hβ0 hβ1
    (by positivity) (by linarith) hR0 hτ0 hkτ hΩ hAR hV hW he
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hsr : √(r : ℝ) * u ≤ β / 4 := by
    linarith [mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hrk') hu0]
  have hHh : ((V * W)ᴴ * decodeMatrix dec As * (V * W))ᴴ =
      (V * W)ᴴ * decodeMatrix dec As * (V * W) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hAh.eq,
      Matrix.mul_assoc]
  have hZ1 : specNorm (V * W) ≤ 1 := (hV.mul hW).specNorm_le_one
  have hH : specNorm ((V * W)ᴴ * decodeMatrix dec As * (V * W)) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul ((specNorm_mul_le _ _).trans
      ((mul_le_mul (by rw [specNorm_conjTranspose]; exact hZ1) hAR (specNorm_nonneg _)
        zero_le_one).trans (one_mul R).le)) hZ1 (specNorm_nonneg _) hR0.le).trans (mul_one R).le)
  have h4 : R * η * η ≤ R * η * (1 / 800) := mul_le_mul_of_nonneg_left hη1 (by positivity)
  have h5 : R * η ≤ R * (1 / 800) := mul_le_mul_of_nonneg_left hη1 hR0.le
  have hP2 := hM.specNorm_decodeMatrix_hermShift_hermAvg_sub_le hu0 (by linarith) hβ1 hR0 hτ0
    (by linarith [mul_le_mul_of_nonneg_right hk1' hτ0])
    (by linarith [mul_le_mul_of_nonneg_right hrk' hτ0]) hsr hΩ hHh hH hP1
    (by nlinarith [mul_le_mul_of_nonneg_right hβ1 hR0.le]) htwo hs
  rw [show Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W = (V * W)ᴴ * decodeMatrix dec As * (V * W) by
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]]
  refine hP2.trans ?_
  have h3 : β * R ≤ η / 8 * R := mul_le_mul_of_nonneg_right hβη hR0.le
  have h6 : 0 ≤ R * η * η := by positivity
  have huR : u * R ≤ β / 1000 * R := mul_le_mul_of_nonneg_right hu1 hR0.le
  have huR0 : 0 ≤ u * R := mul_nonneg hu0 hR0.le
  nlinarith

/-- A split of `NLAlib.eighStep` happens at an internal node whose leaf test fails. -/
private theorem two_le_and_le_eq_false_of_eighStep_eq_split {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N signFuel : ℕ} {R₀ β : F} {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ} {smp : EighSample Su Sg N} {kp : ℕ}
    {hkp : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (h : eighStep M N signFuel R₀ β A R ε ℓ smp = .split kp hkp Qp Qm Ap Am σ) :
    2 ≤ k ∧ M.le R (M.mul ε R₀) = false := by
  unfold eighStep at h
  by_cases hk : k ≤ 1
  · rw [if_pos hk] at h; cases h
  cases hle : M.le R (M.mul ε R₀)
  · exact ⟨by omega, rfl⟩
  · rw [if_neg hk, if_pos hle] at h; cases h

/-- The stored $\mathrm{fl}(2)$ is within $3u$ of $2$ (for $u \ge 0$, $0 \le \tau \le 1/4$ and
$2 \le \Omega$). -/
private theorem FloatMachine.IsAccurate.abs_dec_ofNat_two_sub_le_eb1d {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 4)
    (hΩ : 2 ≤ Ω) : 2 - 3 * u ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2 + 3 * u := by
  have h := le_and_le_of_isRoundingOf (hM.ofNat 2) (by norm_num) (by push_cast; linarith) hu hτ₀
  push_cast at h
  have := mul_le_mul_of_nonneg_left hτ1 hu
  constructor <;> linarith [h.1, h.2]

/-- The sign of a shifted Hermitian matrix has norm at most $1$. -/
private theorem specNorm_cfc_sign_sub_smul_one_le {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    specNorm (cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ≤ 1 :=
  (hA.sub (isHermitian_real_smul_one c)).specNorm_cfc_le zero_le_one fun x _ => by
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

/-- The rounded trace $\mathrm{fl}(t + \mathrm{fl}(1/2))$ of a stored $\mathbf{X}$ whose diagonal
sum is within $1/57600$ of $r \le k$ (with $\sum_i \lvert x_{ii}\rvert \le 2k$) has floor $r$. -/
private theorem FloatMachine.IsAccurate.toNat_add_traceRe_div_eq_eb1d {F : Type*}
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
  obtain ⟨h2a, h2b⟩ := hM.abs_dec_ofNat_two_sub_le_eb1d hu hτ₀ hτ1 (by linarith)
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


/-- The rounded rank estimate of a stored projector within $\beta$ of the ideal spectral
projector $\tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A} - c\mathbf{I}))$ is the
inertia, for $k\beta \le 1/57600$. -/
private theorem FloatMachine.IsAccurate.min_toNat_eq_inertiaPos_of_specNorm_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) {k : ℕ}
    (hk1 : (1 : ℝ) ≤ k) (hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000) (hkτ : (k : ℝ) * τ ≤ 1 / 4)
    (hΩ : 16 * k ≤ Ω) {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) {β : ℝ} (hβ0 : 0 ≤ β) (hkβ : k * β ≤ 1 / 57600)
    {Pp : Matrix (Fin k) (Fin k) (F × F)}
    (hP : specNorm (decodeMatrix dec Pp -
      (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)))) ≤ β) :
    min k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))) =
      inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  set r := inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) with hr
  have hβ1 : β ≤ 1 / 57600 := by nlinarith
  set S := cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul, abs_of_pos (by norm_num)]
    linarith [(specNorm_add_le 1 S).trans (add_le_add specNorm_one_le
      (specNorm_cfc_sign_sub_smul_one_le hA _))]
  have htr := hA.re_trace_smul_one_add_cfc_sign (c := c) fun x hx h => hc x hx h
  rw [← hr] at htr
  have hentry : ∀ i, |dec (Pp i i).1 - RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i)| ≤ β := by
    intro i
    have h := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm (decodeMatrix dec Pp - (2⁻¹ : ℝ) • (1 + S)) i i).trans hP)
    simpa [decodeMatrix, decodeComplex] using h
  have hentry' : ∀ i, |dec (Pp i i).1| ≤ 1 + β := by
    intro i
    have h1 := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm ((2⁻¹ : ℝ) • (1 + S)) i i).trans hPid)
    have h2 := abs_sub_abs_le_abs_sub (dec (Pp i i).1) (RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i))
    linarith [hentry i]
  have hdiag : |∑ i, dec (Pp i i).1 - r| ≤ k * β := by
    rw [← htr, Matrix.trace, map_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry i
  have hsabs : ∑ i, |dec (Pp i i).1| ≤ k * (1 + β) := by
    rw [mul_add, mul_one]
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry' i
  have hrk : (r : ℝ) ≤ k := by
    have : r ≤ k := by
      rw [hr, inertiaPos]
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hk2 := mul_le_mul_of_nonneg_left (by linarith : 1 + β ≤ 2) (Nat.cast_nonneg (α := ℝ) k)
  rw [hM.toNat_add_traceRe_div_eq_eb1d hu hτ₀ hk1 hk2u hkτ hΩ Pp hrk (hdiag.trans hkβ)
    (hsabs.trans (by linarith))]
  exact min_eq_right (by exact_mod_cast hrk)

/-- Deflation of a true spectral projector `V Vᴴ` through a stored approximation, on Event II:
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`
with $\mathbf{S} = \mathbf{I}_r$, for $2t\beta/x \le \eta \le 1/800$. -/
private theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_deflate_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x η : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr0 : 0 < r) (hr : r ≤ n)
    (hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u)
    {V : Matrix (Fin n) (Fin r) ℂ} (hV : HasOrthonormalCols V) {P : Matrix (Fin n) (Fin n) (F × F)}
    (hP : specNorm (V * Vᴴ - decodeMatrix dec P) ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200)
    {G : Matrix (Fin n) (Fin n) ℂ} (hGt : specNorm G < t) (hx : 0 < x)
    (hσ : x < singularValues (Vᴴ * G.submatrix id (Fin.castLE hr)) (r - 1))
    (htx : 2 * t / x * β ≤ η) (hη : η ≤ 1 / 800)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ0 : 0 ≤ τ)
    (hτ : τ * √(n : ℝ) ≤ x) (hΩ : 16 * t ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (V * W - decodeMatrix dec (deflate M r P G)) ≤ 17 / 20 * η := by
  set B := Vᴴ * G.submatrix id (Fin.castLE hr)
  obtain ⟨hGu, hinv⟩ := isUnit_and_specNorm_inv_le hx fun z =>
    (mul_le_mul_of_nonneg_right hσ.le (norm_nonneg _)).trans
      (singularValues_last_mul_norm_le B (k := r - 1) (by rw [Fintype.card_fin]; omega) z)
  have hVn : specNorm Vᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hV.specNorm_le_one
  have hMG : specNorm B ≤ specNorm G :=
    (specNorm_mul_le _ _).trans ((mul_le_mul hVn (specNorm_submatrix_le G Function.injective_id
      (Fin.castLE_injective hr)) (specNorm_nonneg _) zero_le_one).trans (one_mul _).le)
  have hxG : x ≤ specNorm G := hσ.le.trans ((singularValues_le_specNorm _ _).trans hMG)
  have hn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ n))
  have : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  have hS1 : specNorm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := specNorm_one
  have hG0 := specNorm_nonneg G
  have ht0 : 0 < t := lt_of_le_of_lt hG0 hGt
  have hη0 : 0 ≤ η := le_trans (by positivity) htx
  have htxβ : t / x * β ≤ η / 2 := by
    have : 2 * t / x * β = 2 * (t / x * β) := by ring
    linarith
  have hmval : (1 + 2 * β + specNorm (1 : Matrix (Fin r) (Fin r) ℂ) / 8) *
      specNorm (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹ * specNorm G * specNorm B⁻¹ ≤
        (9 / 8 + 2 * β) * (t / x) := by
    rw [inv_one, hS1, mul_one]
    calc (1 + 2 * β + 1 / 8) * specNorm G * specNorm B⁻¹ ≤ (1 + 2 * β + 1 / 8) * t * (1 / x) := by
          gcongr
      _ = (9 / 8 + 2 * β) * (t / x) := by ring
  have hmβ : (9 / 8 + 2 * β) * (t / x) * β ≤ (9 / 8 + 2 * β) * (η / 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left htxβ (by linarith)
  have hmβ' := (mul_le_mul_of_nonneg_right hmval hβ0).trans hmβ
  have hu' : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β := hu
  obtain ⟨W, hW, hWb⟩ := hM.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le hμM
    hu₀ hr hV hV isUnit_one (by rw [Matrix.mul_one]) hP hGu rfl (hmβ'.trans (by nlinarith)) hu'
    (by rw [hS1, one_mul]; nlinarith) (hτ.trans hxG) (by rw [hS1]; nlinarith) (by linarith)
  refine ⟨W, hW, hWb.trans ?_⟩
  change 3 / 2 * ((1 + 2 * β + specNorm (1 : Matrix (Fin r) (Fin r) ℂ) / 8) *
    specNorm (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹ * specNorm G * specNorm B⁻¹) * β ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hβ1 hη0]

/-- One side of a split under a node budget: the frame `V` of a true spectral projector, through
the deflation of the stored projector (Event II) and the compression of the node's matrix. -/
private theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hr0 : 0 < r) (hrk : r ≤ k)
    {β η R t x : ℝ} (hμM : 0 ≤ μM k) (hu : 0 ≤ u) (huβ : u ≤ β / 1000) (hμ : μM k * u ≤ β / 2)
    (hsk : √(k : ℝ) * u ≤ β / 4) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (hβη : β ≤ η / 8)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 800) (hR0 : 0 < R) (hτ₀ : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R)
    (hΩ : 4 * R ≤ Ω) (hx : 0 < x) (htx : 2 * t / x * β ≤ η)
    (hdefl : 16 * (4 * μQ k + 4 * √(k : ℝ) * cN + 2 * μM k) * u ≤ β) (hτx : τ * √(k : ℝ) ≤ x)
    (hΩt : 16 * t ≤ Ω) {As : Matrix (Fin k) (Fin k) (F × F)}
    (hAh : (decodeMatrix dec As).IsHermitian) (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {two : F} (htwo : |dec two - 2| ≤ 3 * u) {V : Matrix (Fin k) (Fin r) ℂ}
    (hV : HasOrthonormalCols V) {P : Matrix (Fin k) (Fin k) (F × F)}
    (hP : specNorm (V * Vᴴ - decodeMatrix dec P) ≤ β) {G : Matrix (Fin k) (Fin k) ℂ}
    (hGt : specNorm G < t)
    (hσ : x < singularValues (Vᴴ * G.submatrix id (Fin.castLE hrk)) (r - 1))
    {s : F} (hs : |dec s| ≤ R) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (V * W - decodeMatrix dec (deflate M r P G)) ≤ η ∧
      specNorm (decodeMatrix dec (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat
        (deflate M r P G)) As) (deflate M r P G)) two) s) -
        (Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
          (2 + 2 * η) * R * η := by
  obtain ⟨W, hW, hWb⟩ := hM.exists_hasOrthonormalCols_specNorm_sub_deflate_le_of_mul_le hr0 hrk
    hμM hu hV hP hβ0 hβ1 hGt hx hσ htx hη1 hdefl hτ₀ hτx hΩt
  exact ⟨W, hW, hWb.trans (by linarith), hM.specNorm_decodeMatrix_compress_sub_le hk1 hrk hu huβ
    hμM hμ hsk hβ0 hβ1 hβη hη0 hη1 hR0 hτ₀ hkτ hΩ hAh hAR hV hW hWb htwo hs⟩

/-- The roundoff budget of a node from the stopping condition of
`NLAlib.FloatMachine.IsEighNodeBudget`. -/
private theorem FloatMachine.IsEighNodeBudget.le_of_stop_tol
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk2 : 2 ≤ y.k) :
    u ≤ dec β / 1000 ∧ μM y.k * u ≤ dec β / 2 ∧ √(y.k : ℝ) * u ≤ dec β / 4 ∧
      dec β ≤ 1 / 115200 ∧ (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
  have hk2' : (2 : ℝ) ≤ y.k := by exact_mod_cast hk2
  have hsqk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hsk2 : √(y.k : ℝ) * √(y.k : ℝ) = y.k := Real.mul_self_sqrt (by linarith)
  have hsqk' : √(y.k : ℝ) ≤ y.k := by nlinarith
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hμM := hB.nonneg_μM
  have hβ := hB.pos_β
  -- the stopping condition
  set ν := 4 * μM y.k + 10 + 10 * √(y.k : ℝ) with hν
  have hνu : 0 ≤ ν * u := mul_nonneg (by positivity) hu
  have hkβ := hB.mul_β_le
  have hβ1 : dec β ≤ 1 / 115200 := by nlinarith
  have hN := newtonSchulzSteps_nonneg (s := w / (5 * dec y.R)) (ε := dec β / (16 * y.k))
    (div_pos hB.pos_w (by positivity))
    (by rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le]) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hstop : 2048 * (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) *
      ν * u ≤ dec β := hB.stop_tol
  have hX : (y.k + 1) * (ν * u) ≤
      (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) * (ν * u) :=
    mul_le_mul_of_nonneg_right (by linarith) hνu
  have hkνu : 2048 * (y.k * (ν * u)) ≤ dec β := by linarith
  have hνu3 : 2048 * 3 * (ν * u) ≤ dec β := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : (3 : ℝ) ≤ y.k + 1) hνu]
  have hνe : ν * u = 4 * (μM y.k * u) + 10 * u + 10 * (√(y.k : ℝ) * u) := by rw [hν]; ring
  have hμu := mul_nonneg hμM hu
  have hsu := mul_le_mul_of_nonneg_right hsqk hu
  have hu1β : u ≤ dec β / 1000 := by linarith
  have hμ : μM y.k * u ≤ dec β / 2 := by linarith
  have hsk : √(y.k : ℝ) * u ≤ dec β / 4 := by linarith
  have hkνe : y.k * (ν * u) = 4 * (y.k * (μM y.k * u)) + 10 * (y.k * u) +
      10 * (y.k * √(y.k : ℝ) * u) := by rw [hν]; ring
  have hk3u : y.k * √(y.k : ℝ) * u ≤ dec β / 20480 := by
    have : 0 ≤ (y.k : ℝ) * (μM y.k * u) := by positivity
    have : 0 ≤ (y.k : ℝ) * u := by positivity
    linarith
  have hk2u : (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have h1 : (y.k : ℝ) ^ 2 * u = √(y.k : ℝ) * (y.k * √(y.k : ℝ) * u) := by
      rw [show √(y.k : ℝ) * (y.k * √(y.k : ℝ) * u) = y.k * (√(y.k : ℝ) * √(y.k : ℝ)) * u by ring,
        hsk2]
      ring
    have h2 := mul_le_mul_of_nonneg_right hsqk' (by positivity : 0 ≤ y.k * √(y.k : ℝ) * u)
    have h3 := mul_le_mul_of_nonneg_left hk3u (by positivity : (0 : ℝ) ≤ y.k)
    linarith
  exact ⟨hu1β, hμ, hsk, hβ1, hk2u⟩

/-- The scalar budget of a split node under `NLAlib.FloatMachine.IsEighNodeBudget`. -/
private theorem FloatMachine.IsEighNodeBudget.split_numerics
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk2 : 2 ≤ y.k)
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hint : M.le y.R (M.mul y.ε R₀) = false) :
    u ≤ 1 / 1000 ∧ τ ≤ 1 / 8 ∧ 6 * τ ≤ dec y.R ∧ 3 * y.k * τ ≤ dec y.R ∧ 2 ≤ Ω ∧
      4 * dec y.R ≤ Ω ∧ μM y.k * u ≤ dec β / 2 ∧ √(y.k : ℝ) * u ≤ dec β / 4 ∧
      u ≤ dec β / 1000 ∧ dec β ≤ 1 / 115200 ∧
      dec β ≤ (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) / 8 ∧
      0 < (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ∧
      (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 / 800 ∧
      (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (y.k : ℝ) * τ ≤ 1 / 4 ∧ 16 * (y.k : ℝ) ≤ Ω ∧
      τ * √(y.k : ℝ) ≤ x ∧
      16 * (4 * μQ y.k + 4 * √(y.k : ℝ) * cN + 2 * μM y.k) * u ≤ dec β ∧ 16 * t ≤ Ω := by
  have hk2' : (2 : ℝ) ≤ y.k := by exact_mod_cast hk2
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hsqk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  obtain ⟨hu1β, hμ, hsk, hβ1, hk2u⟩ := hB.le_of_stop_tol hk2
  -- the norm threshold
  have ht4 : 4 ≤ t := by
    have h2 : √2 * √(y.k : ℝ) = √(2 * y.k) := (Real.sqrt_mul (by norm_num) _).symm
    have h4 : (2 : ℝ) ≤ √(2 * y.k) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
    have := hB.le_t
    rw [mul_assoc, h2] at this
    linarith
  have hΩ := hB.Ω_le
  have hR₀ := hB.pos_R₀
  have hRlt := hM.mul_sub_lt_of_le_eq_false hu hτ₀ hB.pos_ε.le hR₀.le
    (by linarith [mul_le_mul_of_nonneg_right hB.ε_le hR₀.le]) hint
  -- the floor and the range
  have hτ := hB.τ_le
  have hτx : τ * (4 * y.k * √(y.k : ℝ)) ≤ x := hτ.trans (min_le_left _ _)
  have hτε : τ * (4 * y.k * √(y.k : ℝ)) ≤ dec y.ε * dec R₀ := hτ.trans (min_le_right _ _)
  have hkτ4 : 4 * y.k * τ ≤ τ * (4 * y.k * √(y.k : ℝ)) := by
    linarith [mul_le_mul_of_nonneg_left hsqk (by positivity : (0 : ℝ) ≤ 4 * y.k * τ)]
  have hτk : τ * √(y.k : ℝ) ≤ τ * (4 * y.k * √(y.k : ℝ)) := by
    linarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 4 * y.k)
      (mul_nonneg hτ₀ (Real.sqrt_nonneg (y.k : ℝ)))]
  have hx1 := hB.x_le
  have hkτ : (y.k : ℝ) * τ ≤ 1 / 4 := by linarith
  have h2τ := mul_le_mul_of_nonneg_right hk2' hτ₀
  have hτ1 : τ ≤ 1 / 8 := by linarith
  have hu1 : u ≤ 1 / 1000 := by linarith
  have hkτR : 3 * y.k * τ ≤ dec y.R := by
    linarith [mul_le_mul_of_nonneg_left (hkτ4.trans hτε) (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_le_mul_of_nonneg_right hu1 hτ₀,
      mul_le_mul_of_nonneg_right hu1 (by positivity : (0 : ℝ) ≤ y.k * τ)]
  -- the tolerance
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  set η := (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) with hηdef
  have hℓinv : 1 / (y.ℓ : ℝ) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hℓinv0 : 0 < 1 / (y.ℓ : ℝ) := by positivity
  have hη0 : 0 < η := div_pos (mul_pos (by linarith) hε) (by linarith)
  have hη1 : η ≤ 1 / 800 := by
    rw [hηdef, div_le_iff₀ (by linarith)]
    linarith [mul_nonneg hℓinv0.le hε.le]
  have hx := hB.pos_x
  have htx : t ≤ t / x := by
    rw [le_div_iff₀ hx]; exact mul_le_of_le_one_right (by linarith) hx1
  have hβη : dec β ≤ η / 8 := by
    have h := hB.defl_tol
    have : 2 * 4 * dec β ≤ 2 * t / x * dec β := by
      rw [mul_div_assoc]; gcongr; linarith
    linarith
  have hdefl := hB.defl_u
  have hcN := hB.nonneg_cN
  refine ⟨hu1, hτ1, by linarith, hkτR, by linarith, by linarith, hμ, hsk, hu1β, hβ1, hβη, hη0,
    hη1, hk2u, hkτ, by linarith, by linarith, ?_, by linarith⟩
  linarith [mul_nonneg (Real.sqrt_nonneg (y.k : ℝ)) hu]

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
  obtain ⟨hk2, hint⟩ := two_le_and_le_eq_false_of_eighStep_eq_split hsplit
  obtain ⟨⟨hv, hI⟩, hII⟩ := hgood hk2 hint
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  obtain ⟨hu1, hτ1, hτR6, hkτR, hΩ2, hΩ4, hμ, hsk, huβ, hβ1, hβη, hη0, hη1, hk2u, hkτ, hΩk,
    hτx, hdefl, hΩt⟩ := hB.split_numerics hk2 hM hint
  -- the shift
  have hσ := hM.abs_dec_div_ofNat_two_sub_le hu (by linarith) hτ₀ hτ1 hτR6 hΩ2 (by linarith)
  have hhalf : |dec (M.div y.R (M.ofNat 2))| ≤ dec y.R := by
    have h1 := abs_sub_abs_le_abs_sub (dec (M.div y.R (M.ofNat 2))) (dec y.R / 2)
    rw [abs_of_pos (by linarith : 0 < dec y.R / 2)] at h1
    linarith [mul_le_mul_of_nonneg_right hu1 hR0.le]
  have htwo : |dec (M.ofNat 2) - 2| ≤ 3 * u := by
    have h := abs_sub_le_of_isRoundingOf (hM.ofNat 2) (by push_cast; rw [abs_two]; exact hΩ2) hu
      hτ₀
    push_cast at h
    rw [abs_two, abs_sub_comm] at h
    linarith [mul_le_mul_of_nonneg_left (by linarith : τ ≤ 1) hu]
  -- Event I: the ideal shift is not an eigenvalue
  have hc : ∀ x ∈ spectrum ℝ (decodeMatrix dec y.A), x ≠ dec y.R / y.ℓ * smp.1 :=
    fun x hx hxc => by have := hI x hx; rw [hxc, sub_self, abs_zero] at this; linarith [hB.pos_w]
  obtain ⟨hPp, hPm⟩ :=
    hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget hB hint hv hI
  have hkpr := hM.min_toNat_eq_inertiaPos_of_specNorm_sub_le hu hτ₀ hk1 hk2u hkτ hΩk
    hB.isHermitian hc hB.pos_β.le hB.mul_β_le hPp
  -- unfold the step
  unfold eighStep at hsplit
  rw [if_neg (by omega), if_neg (by simp [hint])] at hsplit
  dsimp only at hsplit
  split_ifs at hsplit with h1 h2
  cases hsplit
  refine ⟨hσ, ?_, ?_⟩
  · -- the positive side
    obtain ⟨V, hV, hVV, hsp⟩ := exists_frame_pos hB.isHermitian hB.specNorm_le hc hkpr.symm
    have hr0 := Nat.pos_of_ne_zero h2
    have hrk := lt_of_le_of_ne (min_le_left _ _) h1
    obtain ⟨hGt, hσG⟩ := hII true _ V hr0 hrk hV (by rw [if_pos rfl, one_smul]; exact hVV)
    rw [specNorm_sub_comm, ← hVV] at hPp
    exact ⟨V, hV, hVV, hsp, hM.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le (by omega)
      hr0 hrk.le hB.nonneg_μM hu huβ hμ hsk hB.pos_β.le hβ1 hβη hη0 hη1 hR0 hτ₀ hkτR hΩ4
      hB.pos_x hB.defl_tol hdefl hτx hΩt hB.isHermitian hB.specNorm_le htwo hV hPp hGt
      (hσG hrk.le) hhalf⟩
  · -- the negative side
    obtain ⟨V, hV, hVV, hsp⟩ := exists_frame_neg hB.isHermitian hB.specNorm_le hc hkpr.symm
      (min_le_left _ _)
    have hr0 := Nat.sub_pos_of_lt (lt_of_le_of_ne (min_le_left _ _) h1)
    have hrk : y.k - _ < y.k := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero h2)
    obtain ⟨hGt, hσG⟩ := hII false _ V hr0 hrk hV
      (by rw [if_neg (by simp), neg_one_smul, ← sub_eq_add_neg]; exact hVV)
    rw [specNorm_sub_comm, ← hVV] at hPm
    obtain ⟨W, hW, hWb, hC⟩ := hM.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le
      (by omega) hr0 hrk.le hB.nonneg_μM hu huβ hμ hsk hB.pos_β.le hβ1 hβη hη0 hη1 hR0 hτ₀
      hkτR hΩ4 hB.pos_x hB.defl_tol hdefl hτx hΩt hB.isHermitian hB.specNorm_le htwo hV hPm hGt
      (hσG hrk.le) (s := M.neg (M.div y.R (M.ofNat 2))) (by rw [hM.dec_neg, abs_neg]; exact hhalf)
    rw [hM.dec_neg, neg_smul, sub_neg_eq_add] at hC
    exact ⟨V, hV, hVV, hsp, W, hW, hWb, hC⟩

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
