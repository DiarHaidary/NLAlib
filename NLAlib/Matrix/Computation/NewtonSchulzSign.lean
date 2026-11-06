/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.EntrywiseRounding
public import NLAlib.Matrix.Functions.Sign
public import NLAlib.Polynomial.Approximation.NewtonSchulz

/-!
# The matrix sign function by the Newton–Schulz iteration on a floating-point machine

`NLAlib.newtonSchulzSign M ε b N A` approximates the sign $\operatorname{sign}(\mathbf{A})$ of a
stored nonsingular Hermitian $\mathbf{A}$ with $\|\mathbf{A}\|_2 \le b$ by the inverse-free
iteration $\mathbf{A}_{k+1} = \tfrac12\mathbf{A}_k(3\mathbf{I} - \mathbf{A}_k^2)$ from
$\mathbf{A}_0 = \mathbf{A}/b$ ([Shah2024, Algorithm 1]), written over a `NLAlib.FloatMachine`:
two black-box products per step and the entrywise operations of
`NLAlib/Matrix/Computation/EntrywiseRounding.lean`. Each step stores the rounded Hermitian part
of the computed product, which [Shah2024] leaves implicit; the threshold $\varepsilon/(4n)$ of
the stopping test is computed by the machine; the iteration stops when every part of every entry
of the computed $\mathrm{mm}(\mathbf{A}_k, \mathbf{A}_k) - \mathbf{I}$ is at most the threshold
in absolute value, or after $N$ steps. The definitions are computable: they use the machine and
`ℕ` only.

## Main definitions

* `NLAlib.newtonSchulzRounded`: one step.
* `NLAlib.newtonSchulzTest`: the stopping test.
* `NLAlib.newtonSchulzLoop`, `NLAlib.newtonSchulzSign`: the iteration and the algorithm.

## Main results

* `NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzRounded`,
  `NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzSign`.
* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le`: one step.
* `NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le`: the
  algorithm.
-/

@[expose] public section

namespace NLAlib

variable {F Su Sg : Type*} {n : ℕ}

/-- **One rounded Newton–Schulz step** on the machine `M`: with $\mathbf{X} =
\mathrm{mm}(\mathbf{A}, \mathbf{A})$ and $\mathbf{B} = -(\mathbf{X} - 3\mathbf{I})$ (rounded
shift, exact negation), the result is the stored Hermitian
$(\mathbf{Y} + \mathbf{Y}^{\mathsf{H}})/4$ for $\mathbf{Y} = \mathrm{mm}(\mathbf{A}, \mathbf{B})$
(`NLAlib.FloatMachine.hermAvg`), which in exact arithmetic is
$g(\mathbf{A}) = \tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$. [Shah2024, (2.4)], there
without the Hermitian part.
Algorithm: newton-schulz-sign -/
def newtonSchulzRounded (M : FloatMachine F Su Sg) (A : Matrix (Fin n) (Fin n) (F × F)) :
    Matrix (Fin n) (Fin n) (F × F) :=
  M.hermAvg (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) (M.ofNat 4)

/-- **The Newton–Schulz stopping test** at the stored threshold $\eta$: every real and imaginary
part of every entry of $\mathbf{T} = \mathrm{mm}(\mathbf{A}, \mathbf{A}) - \mathbf{I}$ (rounded
shift) lies in $[-\eta, \eta]$, by the machine's comparisons. [Shah2024, Algorithm 1], there
$\|\mathbf{I} - \mathbf{T}\|_{\max} \le \eta$. -/
def newtonSchulzTest (M : FloatMachine F Su Sg) (η : F) (A : Matrix (Fin n) (Fin n) (F × F)) :
    Bool :=
  let T := M.hermShift (M.mm A A) M.one
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    M.le (M.neg η) (T i j).1 && M.le (T i j).1 η && M.le (M.neg η) (T i j).2 && M.le (T i j).2 η

/-- **The Newton–Schulz loop** with at most $N$ steps: return $\mathbf{A}$ if it passes the test
at threshold $\eta$ (`NLAlib.newtonSchulzTest`) or $N = 0$, and otherwise continue from the
rounded step `NLAlib.newtonSchulzRounded`.
Algorithm: newton-schulz-sign -/
def newtonSchulzLoop (M : FloatMachine F Su Sg) (η : F) :
    ℕ → Matrix (Fin n) (Fin n) (F × F) → Matrix (Fin n) (Fin n) (F × F)
  | 0, A => A
  | N + 1, A =>
    if newtonSchulzTest M η A then A else newtonSchulzLoop M η N (newtonSchulzRounded M A)

/-- **The Newton–Schulz sign algorithm** $\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$
with at most $N$ steps, for stored $\varepsilon$ and $b$: the loop `NLAlib.newtonSchulzLoop` at
the computed threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ from the stored Hermitian
$\mathbf{A}/b$ (`NLAlib.FloatMachine.hermScale`). [Shah2024, Algorithm 1], there with no step
limit.
Algorithm: newton-schulz-sign -/
def newtonSchulzSign (M : FloatMachine F Su Sg) (ε b : F) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) (F × F)) : Matrix (Fin n) (Fin n) (F × F) :=
  newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N (M.hermScale A b)

section Accuracy

open scoped Matrix

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μ μQ : ℕ → ℝ}
  {n : ℕ}

/-- The rounded Newton–Schulz step decodes to a Hermitian matrix, under
`NLAlib.FloatMachine.IsAccurate`. -/
theorem FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzRounded
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (A : Matrix (Fin n) (Fin n) (F × F)) :
    (decodeMatrix dec (newtonSchulzRounded M A)).IsHermitian := by
  unfold newtonSchulzRounded FloatMachine.hermAvg
  exact hM.isHermitian_decodeMatrix_hermFrom _ _

/-- The Newton–Schulz sign algorithm returns a matrix with Hermitian decoding, for every input and
step limit, under `NLAlib.FloatMachine.IsAccurate`. -/
theorem FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzSign
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (ε b : F) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) (F × F)) :
    (decodeMatrix dec (newtonSchulzSign M ε b N A)).IsHermitian := by
  have key : ∀ (η : F) (N : ℕ) (B : Matrix (Fin n) (Fin n) (F × F)),
      (decodeMatrix dec B).IsHermitian →
        (decodeMatrix dec (newtonSchulzLoop M η N B)).IsHermitian := by
    intro η N
    induction N with
    | zero => intro B hB; exact hB
    | succ N ih =>
      intro B hB
      unfold newtonSchulzLoop
      split
      · exact hB
      · exact ih _ (hM.isHermitian_decodeMatrix_newtonSchulzRounded B)
  unfold newtonSchulzSign FloatMachine.hermScale
  exact key _ N _ (hM.isHermitian_decodeMatrix_hermFrom _ _)

/-- The stored conversion of a natural number $k$ with $\tau \le k \le \Omega$ errs by at most
$ku$. -/
private theorem abs_sub_dec_ofNat_le (hM : M.IsAccurate dec u τ Ω μ μQ cN) {k : ℕ}
    (hkΩ : (k : ℝ) ≤ Ω) (hkτ : τ ≤ k) : |(k : ℝ) - dec (M.ofNat k)| ≤ k * u := by
  have h := hM.ofNat k (by rwa [Nat.abs_cast])
  rwa [Nat.abs_cast, max_eq_left hkτ, mul_comm] at h

/-- The stored $3\mathbf{I} - \mathrm{mm}(\mathbf{A}, \mathbf{A})$ of a rounded Newton–Schulz
step is within $1.21\mu u + 7.5u$ of $3\mathbf{I} - \mathbf{A}^2$. -/
private theorem specNorm_sub_decodeMatrix_negMat_hermShift_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ : τ ≤ 1 / 2) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm (((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A) -
        decodeMatrix dec (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) ≤
      121 / 100 * μ n * u + 15 / 2 * u := by
  set a := decodeMatrix dec A
  set x := decodeMatrix dec (M.mm A A)
  set t := dec (M.ofNat 3)
  have ht : |3 - t| ≤ 3 * u := by
    have h := abs_sub_dec_ofNat_le (k := 3) hM (by norm_num; linarith) (by norm_num; linarith)
    simpa only [Nat.cast_ofNat] using h
  have hx : x.IsHermitian := hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose A A hA.eq.symm
  have ha0 := specNorm_nonneg a
  have hsq : specNorm a * specNorm a ≤ 121 / 100 := by nlinarith
  have hw : μ n * u ≤ 1 / 10 := by nlinarith
  have e1 : specNorm (a * a - x) ≤ μ n * u * (121 / 100) := by
    have h := hM.isMatMulErr.specNorm_mul_sub_le A A (hsq.trans (by linarith))
    simp only [max_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (max_le hsq (by linarith)) (mul_nonneg hμ hu₀))
  have h1 := specNorm_one_le (n := Fin n) (𝕜 := ℂ)
  have hK : specNorm (x - t • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 9 / 2 := by
    have hxa := specNorm_sub_le (a * a) (a * a - x)
    rw [sub_sub_cancel] at hxa
    have hat := specNorm_mul_le a a
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_real_smul]
    have htt : |t| ≤ 3 + 3 * u := abs_le.mpr ⟨by linarith [(abs_le.mp ht).2],
      by linarith [(abs_le.mp ht).1]⟩
    nlinarith [abs_nonneg t, specNorm_nonneg (1 : Matrix (Fin n) (Fin n) ℂ)]
  have e2 := hM.specNorm_sub_decodeMatrix_hermShift_le hu₀ hx (M.ofNat 3) (hK.trans (by linarith))
  rw [hM.decodeMatrix_negMat]
  have heq : ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a) -
      -decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)) =
      -((a * a - x) + (t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((x - t • 1) - decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)))) := by
    module
  rw [heq, specNorm_neg]
  have h3 : specNorm ((t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 3 * u := by
    rw [specNorm_real_smul, abs_sub_comm]; nlinarith [abs_nonneg (3 - t)]
  have h4 : u * max (specNorm (x - t • (1 : Matrix (Fin n) (Fin n) ℂ))) τ ≤ u * (9 / 2) :=
    mul_le_mul_of_nonneg_left (max_le hK (by linarith)) hu₀
  linarith [specNorm_add_le (a * a - x) ((t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ)),
    specNorm_add_le (a * a - x + (t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ))
      ((x - t • 1) - decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)))]

/-- The stored $\mathrm{mm}(\mathbf{A}, 3\mathbf{I} - \mathbf{A}^2)$ of a rounded Newton–Schulz
step is within $6.3\mu u + 8.25u$ of $\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$. -/
private theorem specNorm_decodeMatrix_mm_negMat_hermShift_sub_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ : τ ≤ 1 / 2) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm (decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) -
      decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        decodeMatrix dec A * decodeMatrix dec A)) ≤ 63 / 10 * μ n * u + 33 / 4 * u := by
  have eB := specNorm_sub_decodeMatrix_negMat_hermShift_le hM hμ hu₀ hu hτ hΩ hA hA₁
  set a := decodeMatrix dec A
  set b := decodeMatrix dec (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))
  set z := (3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a
  have ha0 := specNorm_nonneg a
  have hw : μ n * u ≤ 1 / 10 := by nlinarith
  have hz : specNorm z ≤ 3 + 121 / 100 := by
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_real_smul]
    nlinarith [specNorm_one_le (n := Fin n) (𝕜 := ℂ), specNorm_mul_le a a]
  have hb : specNorm b ≤ 9 / 2 := by
    have h := specNorm_sub_le z (z - b)
    rw [sub_sub_cancel] at h
    nlinarith
  have hab : specNorm a * specNorm b ≤ 99 / 20 :=
    (mul_le_mul hA₁ hb (specNorm_nonneg b) (by norm_num)).trans (by norm_num)
  have e3 := hM.isMatMulErr.specNorm_mul_sub_le A
    (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))) (hab.trans (by linarith))
  simp only [max_self] at e3
  have e3' : specNorm (a * b - decodeMatrix dec
      (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))))) ≤ μ n * u * (99 / 20) :=
    e3.trans (mul_le_mul_of_nonneg_left (max_le hab (by linarith)) (mul_nonneg hμ hu₀))
  have heq : decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) - a * z =
      -(a * b - decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))))) +
        a * (b - z) := by
    rw [Matrix.mul_sub a b z]; abel
  rw [heq]
  refine (specNorm_add_le _ _).trans ?_
  rw [specNorm_neg]
  have h5 := (specNorm_mul_le a (b - z)).trans
    (mul_le_mul hA₁ ((specNorm_sub_comm b z).trans_le eB) (specNorm_nonneg _) (by norm_num))
  nlinarith

/-- The Hermitian part divided by $t$ is near $\mathbf{G}$ when $\mathbf{Y}$ is near
$2\mathbf{G}$, for Hermitian $\mathbf{G}$ and $t > 0$. -/
private theorem specNorm_sub_smul_add_conjTranspose_le {g y : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ = g) {t e : ℝ} (ht : 0 < t) (hE : specNorm (y - (2 : ℝ) • g) ≤ e) :
    specNorm (g - t⁻¹ • (y + yᴴ)) ≤ |1 - 4 * t⁻¹| * specNorm g + 2 * t⁻¹ * e := by
  set E := y - (2 : ℝ) • g with hE_def
  have hy : y = E + (2 : ℝ) • g := by rw [hE_def, sub_add_cancel]
  have heq : g - t⁻¹ • (y + yᴴ) = (1 - 4 * t⁻¹) • g - t⁻¹ • (E + Eᴴ) := by
    rw [hy, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hg, star_trivial]
    module
  rw [heq]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos (inv_pos.mpr ht)]
  have h := (specNorm_add_le E Eᴴ).trans_eq (by rw [specNorm_conjTranspose])
  have h2 : specNorm (E + Eᴴ) ≤ 2 * e := by linarith
  nlinarith [inv_pos.mpr ht]

/-- **One rounded Newton–Schulz step** (Lemma 2.1): under the machine contract
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with product constant $\mu$,
$\mu(n) \ge 0$, $u \ge 0$, $u(8 + \mu(n)) \le 1/10$, $0 \le \tau$, $2n\tau \le 1$ and
$\Omega \ge 9$, every stored $\mathbf{A}$ whose decoding (still written $\mathbf{A}$) is
Hermitian with $\|\mathbf{A}\|_2 \le 11/10$ satisfies
$$\Bigl\|\tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2) - \tilde g(\mathbf{A})\Bigr\|_2 \le
4\sqrt n\,(8 + \mu(n))\,u \,,$$
$\tilde g$ the decoded rounded step `NLAlib.newtonSchulzRounded` (constants $3$ and $4$ computed by
the machine's conversion). [Shah2024, Lemma 2.1], there
$\tfrac12(7 + (6 + \mu)a^2)a\,u$ for $\|\mathbf{A}\|_2 \le a$ without the Hermitian part; the
factor $\sqrt n$ is the cost of storing the result exactly Hermitian, and the statement is for
the regime $a \le 11/10$ of the iteration. -/
theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm ((2⁻¹ : ℝ) • (decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A)) - decodeMatrix dec (newtonSchulzRounded M A)) ≤
        4 * √(n : ℝ) * (8 + μ n) * u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ X : Matrix (Fin 0) (Fin 0) ℂ, specNorm X = 0 := fun X => by
      rw [Subsingleton.elim X 0, specNorm_zero]
    rw [h0]; simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hτ' : τ ≤ 1 / 2 := by nlinarith
  have hs : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hw : 8 * u + μ n * u ≤ 1 / 10 := by linarith [mul_add u 8 (μ n)]
  have hw0 := mul_nonneg hμ hu₀
  have hu' : u ≤ 1 / 80 := by linarith
  have eY := specNorm_decodeMatrix_mm_negMat_hermShift_sub_le hM hμ hu₀ hu hτ' hΩ hA hA₁
  set a := decodeMatrix dec A
  set Y := M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))
  set g := (2⁻¹ : ℝ) • (a * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a))
  have hgc : cfc newtonSchulz a = g := hA.cfc_newtonSchulz
  have hgH : gᴴ = g := by
    have h : (cfc newtonSchulz a).IsHermitian := cfc_predicate newtonSchulz a
    rw [hgc] at h; exact h.eq
  have hg1 : specNorm g ≤ 1 := by
    rw [← hgc]
    refine hA.specNorm_cfc_le zero_le_one fun x hx => abs_newtonSchulz_le_one ?_
    rw [hA.spectrum_eq_image_eigenvalue] at hx
    obtain ⟨k, -, rfl⟩ := hx
    linarith [hA.abs_eigenvalue_le_specNorm k]
  have h2g : a * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a) = (2 : ℝ) • g := by
    rw [smul_smul]; norm_num
  rw [h2g] at eY
  set t := dec (M.ofNat 4)
  have ht : |4 - t| ≤ 4 * u := by
    have h := abs_sub_dec_ofNat_le (k := 4) hM (by norm_num; linarith) (by norm_num; linarith)
    simpa only [Nat.cast_ofNat] using h
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  have ht0 : 0 < t := by linarith
  have htinv : t⁻¹ ≤ 10 / 39 :=
    (inv_anti₀ (by norm_num) (by linarith : (39 / 10 : ℝ) ≤ t)).trans_eq (by norm_num)
  have htinv0 : 0 < t⁻¹ := inv_pos.mpr (by linarith)
  have h4 : |1 - 4 * t⁻¹| ≤ 2 * u := by
    rw [show 1 - 4 * t⁻¹ = (t - 4) * t⁻¹ by field_simp, abs_mul, abs_of_pos htinv0,
      abs_sub_comm]
    nlinarith [abs_nonneg (4 - t)]
  set D := specNorm (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ))
  have hD : D ≤ 2 * u + 2 * (10 / 39) * (63 / 10 * μ n * u + 33 / 4 * u) :=
    (specNorm_sub_smul_add_conjTranspose_le hgH (by linarith) eY).trans
      (add_le_add (by nlinarith [specNorm_nonneg g])
        (by gcongr))
  have hy : specNorm (decodeMatrix dec Y) ≤ 263 / 100 := by
    have h := specNorm_add_le ((2 : ℝ) • g) (decodeMatrix dec Y - (2 : ℝ) • g)
    rw [add_sub_cancel, specNorm_real_smul, abs_two] at h
    nlinarith
  have e5 := hM.specNorm_sub_decodeMatrix_hermAvg_le hu₀ (by linarith) hτ₀ Y (c := M.ofNat 4)
    (by rw [abs_of_pos (by linarith)]; linarith) (by linarith)
  have hN1 : specNorm (t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ)) ≤ 2 := by
    have h := specNorm_sub_le g (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ))
    rw [sub_sub_cancel] at h
    nlinarith [mul_nonneg hμ hu₀]
  have hfin : g - decodeMatrix dec (newtonSchulzRounded M A) =
      (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ)) +
        (t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ) -
          decodeMatrix dec (M.hermAvg Y (M.ofNat 4))) := by
    rw [sub_add_sub_cancel]; rfl
  rw [hfin]
  refine (specNorm_add_le _ _).trans ?_
  have k1 := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hN1 (Real.sqrt_nonneg (n : ℝ)))
    ((by linarith : 2 * (n : ℝ) * τ ≤ 1).trans hs)) (by positivity : (0 : ℝ) ≤ 3 * u)
  have k2 : D ≤ √(n : ℝ) * D := le_mul_of_one_le_left (specNorm_nonneg _) hs
  have k3 := mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg (n : ℝ))
  have k4 := mul_le_mul_of_nonneg_left hs (mul_nonneg hμ hu₀)
  have k5 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (mul_nonneg hμ hu₀)
  have k6 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hu₀
  linarith

/-! ### Spectral helpers for the accuracy proof -/

private theorem abs_le_specNorm_of_mem_spectrum {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ X) : |x| ≤ specNorm X := by
  rw [hX.spectrum_eq_image_eigenvalue] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact hX.abs_eigenvalue_le_specNorm j

private theorem exists_mem_spectrum_abs_sub_le {k : ℕ} {X Y : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) {y : ℝ} (hy : y ∈ spectrum ℝ Y) :
    ∃ x ∈ spectrum ℝ X, |x - y| ≤ specNorm (X - Y) := by
  rw [hY.spectrum_eq_image_eigenvalue] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  exact ⟨_, hX.eigenvalue_mem_spectrum hj, hX.abs_eigenvalue_sub_le hY j⟩

private theorem exists_mem_spectrum_eq_mul {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) (c : ℝ) {y : ℝ} (hy : y ∈ spectrum ℝ (c • X)) :
    ∃ x ∈ spectrum ℝ X, y = c * x := by
  rw [← cfc_const_mul_id c X hX.isSelfAdjoint, cfc_map_spectrum _ _ hX.isSelfAdjoint] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, rfl⟩

private theorem cfc_sign_smul {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 < c) : cfc Real.sign (c • X) = cfc Real.sign X := by
  rw [← cfc_const_mul_id c X hX.isSelfAdjoint,
    ← cfc_comp' Real.sign (c * ·) X ((X.finite_real_spectrum.image _).continuousOn _)]
  congr 1
  funext x
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hc h)]
  · rw [mul_zero]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hc h)]

private theorem cfc_sq_sub_one {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => x ^ 2 - 1) X = X * X - 1 := by
  rw [cfc_sub (fun x : ℝ => x ^ 2) (fun _ => 1) X, cfc_pow_id X 2 hX.isSelfAdjoint,
    cfc_const_one ℝ X, sq]

private theorem abs_one_sub_sq_le_specNorm {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ X) : |1 - x ^ 2| ≤ specNorm (X * X - 1) := by
  rw [← cfc_sq_sub_one hX]
  have hH : (cfc (fun x : ℝ => x ^ 2 - 1) X).IsHermitian := cfc_predicate _ X
  rw [abs_sub_comm]
  refine abs_le_specNorm_of_mem_spectrum hH ?_
  rw [cfc_map_spectrum (fun x : ℝ => x ^ 2 - 1) X hX.isSelfAdjoint]
  exact ⟨x, hx, rfl⟩

private theorem specNorm_mul_self_sub_one_le {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ X, |1 - x ^ 2| ≤ c) :
    specNorm (X * X - 1) ≤ c := by
  rw [← cfc_sq_sub_one hX]
  exact hX.specNorm_cfc_le hc fun x hx => abs_sub_comm (x ^ 2) 1 ▸ h x hx

/-- A $k \times k$ matrix with entries of modulus at most $c$ has spectral norm at most $kc$. -/
private theorem specNorm_le_card_mul_of_norm_apply_le {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖X i j‖ ≤ c) :
    specNorm X ≤ k * c := by
  refine (specNorm_le_frobNorm X).trans ?_
  refine (pow_le_pow_iff_left₀ (frobNorm_nonneg X) (by positivity) two_ne_zero).mp ?_
  rw [frobNorm_sq_eq_sum]
  calc ∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ ∑ _i : Fin k, ∑ _j : Fin k, c ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (k * c) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Scalar chains of the perturbed iteration -/

/-- `y` is reached at step `k` by a perturbed Newton–Schulz chain with errors at most `δ` from a
start of modulus in `[s, 11/10]`. -/
private def IsNewtonSchulzChain (s δ y : ℝ) (k : ℕ) : Prop :=
  ∃ x : ℕ → ℝ, x k = y ∧ s ≤ |x 0| ∧ |x 0| ≤ 11 / 10 ∧
    ∀ j, |x (j + 1) - newtonSchulz (x j)| ≤ δ

private theorem isNewtonSchulzChain_zero {s δ y : ℝ} (hδ : 0 ≤ δ) (h₁ : s ≤ |y|)
    (h₂ : |y| ≤ 11 / 10) : IsNewtonSchulzChain s δ y 0 :=
  ⟨fun j => newtonSchulz^[j] y, rfl, h₁, h₂, fun j => by
    simp only [Function.iterate_succ_apply', sub_self, abs_zero]; exact hδ⟩

private theorem IsNewtonSchulzChain.succ {s δ y z : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hδ : 0 ≤ δ) (hz : |z - newtonSchulz y| ≤ δ) :
    IsNewtonSchulzChain s δ z (k + 1) := by
  obtain ⟨x, hxk, h₁, h₂, hstep⟩ := h
  refine ⟨fun j => if j ≤ k then x j else newtonSchulz^[j - (k + 1)] z, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa using h₁
  · simpa using h₂
  · intro j
    rcases lt_trichotomy j k with hj | rfl | hj
    · simp only [show j + 1 ≤ k by omega, hj.le, if_true]
      exact hstep j
    · simp only [le_refl, if_true, show ¬ j + 1 ≤ j by omega, if_false, Nat.sub_self,
        Function.iterate_zero, id, hxk]
      exact hz
    · simp only [show ¬ j + 1 ≤ k by omega, show ¬ j ≤ k by omega, if_false,
        show j + 1 - (k + 1) = (j - (k + 1)) + 1 by omega, Function.iterate_succ_apply',
        sub_self, abs_zero]
      exact hδ

private theorem IsNewtonSchulzChain.le_abs {s δ y : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hs : s ≤ 1 / 2) (hδ : 20 * δ ≤ s) : s ≤ |y| := by
  obtain ⟨x, rfl, h₁, h₂, hstep⟩ := h
  have := min_abs_le_abs_of_abs_sub_newtonSchulz_le (by linarith) (by linarith) (by linarith)
    hstep k
  exact le_trans (le_min h₁ hs) this

private theorem IsNewtonSchulzChain.abs_le {s δ y : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hδ : δ ≤ 1 / 10) : |y| ≤ 11 / 10 := by
  obtain ⟨x, rfl, h₁, h₂, hstep⟩ := h
  rcases k with _ | k
  · exact h₂
  · have := abs_le_one_add_of_abs_sub_newtonSchulz_le (by linarith) (by linarith) hstep k
    linarith

private theorem IsNewtonSchulzChain.abs_one_sub_sq_le {s δ y ε : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hs : 0 < s) (hδ : 20 * δ ≤ s) (hε : 0 < ε)
    (hε₁ : 10 * δ ≤ ε) (hε₂ : ε ≤ 3 / 80) (hk : newtonSchulzSteps s ε ≤ k) :
    |1 - y ^ 2| ≤ ε := by
  obtain ⟨x, rfl, h₁, h₂, hstep⟩ := h
  exact abs_one_sub_sq_le_of_newtonSchulzSteps_le hε hε₁ hε₂ (by linarith) (by linarith)
    (by linarith) hstep ((newtonSchulzSteps_le_of_le_abs hs h₁).trans hk)

/-! ### One step of the matrix iteration -/

private theorem specNorm_le_of_forall_mem_spectrum_abs_le {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ spectrum ℝ X, |x| ≤ c) : specNorm X ≤ c := by
  have := hX.specNorm_cfc_le (f := id) hc h
  rwa [cfc_id ℝ X hX.isSelfAdjoint] at this

/-- One rounded step keeps every eigenvalue on a perturbed scalar chain, and moves the sign by at
most `2δ/s`. -/
private theorem newtonSchulzRounded_chain_and_specNorm_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n)
    (hu₀ : 0 ≤ u) (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1)
    (hΩ : 9 ≤ Ω) {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hδ : 20 * (4 * √(n : ℝ) * (8 + μ n) * u) ≤ s) {k : ℕ}
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hch : ∀ y ∈ spectrum ℝ (decodeMatrix dec X),
      IsNewtonSchulzChain s (4 * √(n : ℝ) * (8 + μ n) * u) y k) :
    (∀ z ∈ spectrum ℝ (decodeMatrix dec (newtonSchulzRounded M X)),
      IsNewtonSchulzChain s (4 * √(n : ℝ) * (8 + μ n) * u) z (k + 1)) ∧
    specNorm (cfc Real.sign (decodeMatrix dec X) -
      cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X))) ≤
        2 * (4 * √(n : ℝ) * (8 + μ n) * u) / s := by
  set δ := 4 * √(n : ℝ) * (8 + μ n) * u
  have hδ₀ : 0 ≤ δ := by positivity
  have hY := hM.isHermitian_decodeMatrix_newtonSchulzRounded X
  have hgX : (cfc newtonSchulz (decodeMatrix dec X)).IsHermitian := cfc_predicate _ _
  have hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10 :=
    specNorm_le_of_forall_mem_spectrum_abs_le hX (by norm_num) fun y hy =>
      (hch y hy).abs_le (by linarith)
  have herr : specNorm (cfc newtonSchulz (decodeMatrix dec X) -
      decodeMatrix dec (newtonSchulzRounded M X)) ≤ δ := by
    rw [hX.cfc_newtonSchulz]
    exact hM.specNorm_sub_decodeMatrix_newtonSchulzRounded_le hμ hu₀ hu hτ₀ hτ hΩ hX hXn
  have hchY : ∀ z ∈ spectrum ℝ (decodeMatrix dec (newtonSchulzRounded M X)),
      IsNewtonSchulzChain s δ z (k + 1) := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := exists_mem_spectrum_abs_sub_le hgX hY hz
    rw [cfc_map_spectrum newtonSchulz (decodeMatrix dec X) hX.isSelfAdjoint
      ((decodeMatrix dec X).finite_real_spectrum.continuousOn _)] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    exact (hch y hy).succ hδ₀ (by rw [abs_sub_comm]; exact hwz.trans herr)
  refine ⟨hchY, ?_⟩
  have h3 : (11 / 10 : ℝ) < √3 := Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [← hX.cfc_sign_cfc_newtonSchulz fun y hy =>
    ⟨hs.trans_le ((hch y hy).le_abs hs₁ hδ), ((hch y hy).abs_le (by linarith)).trans_lt h3⟩,
    specNorm_sub_comm]
  refine (hY.specNorm_cfc_sign_sub_cfc_sign_le hgX hs fun z hz =>
    (hchY z hz).le_abs hs₁ hδ).trans ?_
  rw [specNorm_sub_comm]
  gcongr

/-! ### The stopping test -/

/-- The stored threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ is close to
$\varepsilon/(4n)$. -/
private theorem threshold_bounds (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hu₀ : 0 ≤ u)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F}
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2) (hu : 640 * n * u ≤ dec ε) :
    n * dec (M.div ε (M.ofNat (4 * n))) ≤ 13 / 50 * dec ε ∧
      dec ε / 5 ≤ n * dec (M.div ε (M.ofNat (4 * n))) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := hM.ofNat (4 * n) (by push_cast; rw [abs_of_nonneg (by positivity)]; linarith)
  push_cast at hc
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * n),
    max_eq_left (by nlinarith : τ ≤ 4 * n)] at hc
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  set c := dec (M.ofNat (4 * n))
  have hu₁ : u ≤ 1 / 1280 := by nlinarith
  have hcpos : 0 < c := by nlinarith
  set q := dec ε / c with hqdef
  have hq : q * c = dec ε := div_mul_cancel₀ _ hcpos.ne'
  have hq₀ : 0 < q := div_pos hε hcpos
  have hq₁ : q ≤ 1 / 4 := by nlinarith
  have hd := hM.div ε (M.ofNat (4 * n)) hcpos.ne' (by rw [abs_of_pos hq₀]; linarith)
  rw [← hqdef, abs_of_pos hq₀] at hd
  have hd' : |q - dec (M.div ε (M.ofNat (4 * n)))| ≤ u * (q + τ) :=
    hd.trans (mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hu₀)
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp hd'
  have hnτ : n * τ ≤ 1 / 2 := by linarith
  constructor <;> nlinarith [mul_nonneg hu₀ hq₀.le, mul_le_mul_of_nonneg_left hnτ hu₀]

/-- The computed test matrix $\mathrm{mm}(\mathbf{X}, \mathbf{X}) - \mathbf{I}$ is within
$2(8 + \mu(n))u$ of $\mathbf{X}^2 - \mathbf{I}$. -/
private theorem specNorm_mul_self_sub_one_sub_decodeMatrix_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₁ : τ ≤ 1) (hΩ : 9 ≤ Ω)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10) :
    specNorm ((decodeMatrix dec X * decodeMatrix dec X - 1) -
      decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤ 2 * (8 + μ n) * u := by
  set Xd := decodeMatrix dec X
  set P := decodeMatrix dec (M.mm X X)
  have hX₀ := specNorm_nonneg Xd
  have hsq : specNorm Xd * specNorm Xd ≤ 121 / 100 := by nlinarith
  have hE₁ : specNorm (Xd * Xd - P) ≤ μ n * u * (121 / 100) := by
    have h := hM.isMatMulErr.specNorm_mul_sub_le X X (le_trans hsq (by linarith))
    simp only [max_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (max_le hsq (by linarith)) (by positivity))
  have hPH : P.IsHermitian := hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose X X hX.symm
  have hX₁ : specNorm (Xd * Xd - 1) ≤ 1 :=
    specNorm_mul_self_sub_one_le hX zero_le_one fun x hx => by
      have := (abs_le_specNorm_of_mem_spectrum hX hx).trans hXn
      rw [abs_le]; constructor <;> nlinarith [abs_nonneg x, sq_abs x]
  have hP₁ : specNorm (P - 1) ≤ 2 := by
    have : P - 1 = (Xd * Xd - 1) - (Xd * Xd - P) := by abel
    rw [this]
    refine (specNorm_sub_le _ _).trans ?_
    nlinarith
  have hE₂ := hM.specNorm_sub_decodeMatrix_hermShift_le hu₀ hPH M.one
    (by rw [hM.dec_one, one_smul]; linarith)
  rw [hM.dec_one, one_smul] at hE₂
  have hE₂' : specNorm ((P - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤ 2 * u :=
    hE₂.trans (by nlinarith [mul_le_mul_of_nonneg_left (max_le hP₁ (by linarith : τ ≤ 2)) hu₀])
  have : (Xd * Xd - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one) =
      (Xd * Xd - P) + ((P - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one)) := by abel
  rw [this]
  refine (specNorm_add_le _ _).trans ?_
  nlinarith

private theorem newtonSchulzTest_eq_true_iff (hM : M.IsAccurate dec u τ Ω μ μQ cN) (η : F)
    (X : Matrix (Fin n) (Fin n) (F × F)) :
    newtonSchulzTest M η X = true ↔ ∀ i j,
      |dec (M.hermShift (M.mm X X) M.one i j).1| ≤ dec η ∧
        |dec (M.hermShift (M.mm X X) M.one i j).2| ≤ dec η := by
  simp only [newtonSchulzTest, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.and_eq_true, hM.le_iff, hM.dec_neg, abs_le, and_assoc]

/-- The size condition $640n(8 + \mu(n))u \le \varepsilon \le 1/2$ bounds $640nu$ by
$\varepsilon$ and $u(8 + \mu(n))$ by $1/10$. -/
private theorem unitRoundoff_bounds {μn u ε : ℝ} (hn : 0 < n) (hμ : 0 ≤ μn) (hu₀ : 0 ≤ u)
    (hε₁ : ε ≤ 1 / 2) (hk : 640 * n * (8 + μn) * u ≤ ε) :
    640 * n * u ≤ ε ∧ u * (8 + μn) ≤ 1 / 10 := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · nlinarith [mul_nonneg hμ hu₀, mul_nonneg hu₀ (by positivity : (0 : ℝ) ≤ n)]
  · nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μn)]

/-- If the test passes, the iterate is within `2ε/3` of its sign. -/
private theorem specNorm_sub_cfc_sign_le_of_newtonSchulzTest
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10)
    (htest : newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true) :
    specNorm (decodeMatrix dec X - cfc Real.sign (decodeMatrix dec X)) ≤ 2 / 3 * dec ε := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hun, hu⟩ := unitRoundoff_bounds hn hμ hu₀ hε₁ hk
  have hη := (threshold_bounds hM hu₀ hτ₀ hτ hΩ hn hε hε₁ hun).1
  set η := dec (M.div ε (M.ofNat (4 * n)))
  have hE := specNorm_mul_self_sub_one_sub_decodeMatrix_le hM hμ hu₀ hu (by nlinarith)
    (by linarith) hX hXn
  rw [newtonSchulzTest_eq_true_iff hM] at htest
  have hη₀ : 0 ≤ η := le_trans (abs_nonneg _) (htest ⟨0, hn⟩ ⟨0, hn⟩).1
  have hT := specNorm_le_card_mul_of_norm_apply_le
    (X := decodeMatrix dec (M.hermShift (M.mm X X) M.one)) (by positivity : 0 ≤ 2 * η)
    fun i j => (Complex.norm_le_abs_re_add_abs_im _).trans
      ((add_le_add (htest i j).1 (htest i j).2).trans_eq (two_mul η).symm)
  have hS : specNorm (decodeMatrix dec X * decodeMatrix dec X - 1) ≤ 2 / 3 * dec ε := by
    have := specNorm_add_le (decodeMatrix dec X * decodeMatrix dec X - 1 -
      decodeMatrix dec (M.hermShift (M.mm X X) M.one))
      (decodeMatrix dec (M.hermShift (M.mm X X) M.one))
    rw [sub_add_cancel] at this
    nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μ n)]
  exact hX.specNorm_sub_cfc_sign_le (by positivity) fun x hx =>
    (abs_one_sub_sq_le_specNorm hX hx).trans hS

/-- If every eigenvalue is close to `±1`, the test passes. -/
private theorem newtonSchulzTest_of_forall_mem_spectrum
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10)
    (h : ∀ x ∈ spectrum ℝ (decodeMatrix dec X), |1 - x ^ 2| ≤ dec ε / (16 * n)) :
    newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hun, hu⟩ := unitRoundoff_bounds hn hμ hu₀ hε₁ hk
  have hη := (threshold_bounds hM hu₀ hτ₀ hτ hΩ hn hε hε₁ hun).2
  set η := dec (M.div ε (M.ofNat (4 * n)))
  have hE := specNorm_mul_self_sub_one_sub_decodeMatrix_le hM hμ hu₀ hu (by nlinarith)
    (by linarith) hX hXn
  have hS := specNorm_mul_self_sub_one_le hX (by positivity) h
  have hT : specNorm (decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤
      dec ε / (16 * n) + 2 * (8 + μ n) * u := by
    have := specNorm_sub_le (decodeMatrix dec X * decodeMatrix dec X - 1)
      (decodeMatrix dec X * decodeMatrix dec X - 1 -
        decodeMatrix dec (M.hermShift (M.mm X X) M.one))
    rw [sub_sub_cancel] at this
    linarith
  have hη' : dec ε / (16 * n) + 2 * (8 + μ n) * u ≤ η := by
    rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μ n)]
  rw [newtonSchulzTest_eq_true_iff hM]
  intro i j
  have hij := (norm_apply_le_specNorm _ i j).trans (hT.trans hη')
  exact ⟨(Complex.abs_re_le_norm _).trans hij, (Complex.abs_im_le_norm _).trans hij⟩

/-! ### The loop -/

/-- **The loop invariant**: from an iterate at step `k` whose eigenvalues lie on perturbed scalar
chains, the loop returns a matrix within `2ε/3` plus `2δ/s` per remaining step of the sign. -/
private theorem specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzLoop_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε) {s : ℝ} (hs : 0 < s)
    (hs₁ : s ≤ 1 / 2) (hδs : 20 * (4 * √(n : ℝ) * (8 + μ n) * u) ≤ s)
    (hδε : 10 * (4 * √(n : ℝ) * (8 + μ n) * u) ≤ dec ε / (16 * n)) (N k : ℕ)
    (X : Matrix (Fin n) (Fin n) (F × F)) (hX : (decodeMatrix dec X).IsHermitian)
    (hch : ∀ y ∈ spectrum ℝ (decodeMatrix dec X),
      IsNewtonSchulzChain s (4 * √(n : ℝ) * (8 + μ n) * u) y k)
    (hN : newtonSchulzSteps s (dec ε / (16 * n)) ≤ k + N) :
    specNorm (cfc Real.sign (decodeMatrix dec X) -
      decodeMatrix dec (newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N X)) ≤
        2 / 3 * dec ε + max 0 (newtonSchulzSteps s (dec ε / (16 * n)) + 1 - k) *
          (2 * (4 * √(n : ℝ) * (8 + μ n) * u) / s) := by
  set δ := 4 * √(n : ℝ) * (8 + μ n) * u
  set N₀ := newtonSchulzSteps s (dec ε / (16 * n))
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ₀ : 0 ≤ δ := by positivity
  have hε' : 0 < dec ε / (16 * n) := by positivity
  have hε'₁ : dec ε / (16 * n) ≤ 3 / 80 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hε'₂ : dec ε / (16 * n) ≤ 2 / 3 * dec ε := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hXn : ∀ {j : ℕ} {Y : Matrix (Fin n) (Fin n) (F × F)}, (decodeMatrix dec Y).IsHermitian →
      (∀ y ∈ spectrum ℝ (decodeMatrix dec Y), IsNewtonSchulzChain s δ y j) →
        specNorm (decodeMatrix dec Y) ≤ 11 / 10 := fun hY hchY =>
    specNorm_le_of_forall_mem_spectrum_abs_le hY (by norm_num) fun y hy =>
      (hchY y hy).abs_le (by linarith)
  induction N generalizing k X with
  | zero =>
    have hrest : 0 ≤ max 0 (N₀ + 1 - k) * (2 * δ / s) := by positivity
    have h := hX.specNorm_sub_cfc_sign_le hε'.le fun y hy =>
      (hch y hy).abs_one_sub_sq_le hs hδs hε' hδε hε'₁ (by simpa using hN)
    rw [newtonSchulzLoop, specNorm_sub_comm]
    linarith
  | succ N ih =>
    rw [newtonSchulzLoop]
    by_cases ht : newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true
    · rw [if_pos ht, specNorm_sub_comm]
      have hrest : 0 ≤ max 0 (N₀ + 1 - k) * (2 * δ / s) := by positivity
      have := specNorm_sub_cfc_sign_le_of_newtonSchulzTest hM hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk hX
        (hXn hX hch) ht
      linarith
    · rw [if_neg ht]
      have hkN : (k : ℝ) < N₀ := by
        by_contra hk'
        exact ht (newtonSchulzTest_of_forall_mem_spectrum hM hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk hX
          (hXn hX hch) fun y hy =>
            (hch y hy).abs_one_sub_sq_le hs hδs hε' hδε hε'₁ (not_lt.mp hk'))
      obtain ⟨hchY, hstep⟩ := newtonSchulzRounded_chain_and_specNorm_le hM hμ hu₀
        (unitRoundoff_bounds hn hμ hu₀ hε₁ hk).2 hτ₀ hτ
        (by linarith) hs hs₁ hδs hX hch
      have hIH := ih (k + 1) (newtonSchulzRounded M X)
        (hM.isHermitian_decodeMatrix_newtonSchulzRounded X) hchY (by push_cast at hN ⊢; linarith)
      have htri := specNorm_add_le
        (cfc Real.sign (decodeMatrix dec X) -
          cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X)))
        (cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X)) - decodeMatrix dec
          (newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N (newtonSchulzRounded M X)))
      rw [sub_add_sub_cancel] at htri
      push_cast at hIH
      rw [max_eq_right (by linarith)] at hIH ⊢
      linarith

/-- **Accuracy of the Newton–Schulz sign algorithm** (Theorem 2.6): under the machine contract
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with product constant $\mu$,
$\mu(n) \ge 0$, $u \ge 0$, $0 \le \tau$, $2n\tau \le 1$ and $9(n + 1) \le \Omega$, let the
stored $\mathbf{A}$ have Hermitian decoding (written $\mathbf{A}$) with
$\|\mathbf{A}\|_2 \le b$ and every eigenvalue of modulus at least $a > 0$, for stored $b$ and
$\varepsilon$ with $0 < \varepsilon \le 1/2$ (decoded values). With $N_0 = N(a/(2b),
\varepsilon/(16n))$ (`NLAlib.newtonSchulzSteps`), if
$$640\, n^{3/2}\,(8 + \mu(n))\,(N_0 + 1)\,u \le \frac{a}{b}\,\varepsilon$$
and the step limit is at least $N_0$, then
$$\|\operatorname{sign}(\mathbf{A}) - \mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)\|_2 \le
\varepsilon \,,$$
$\mathsf{newtonSchulzSign}$ the algorithm `NLAlib.newtonSchulzSign`. [Shah2024, Theorem 2.6],
there with
$u \le (a/b)\varepsilon/(4\max(N n\mu_g(n, 1.1), n^2))$, $N = N(a/b, \varepsilon/(8n))$ and
the contour bound of Lemma 2.2; here the perturbation bound is dimension-free and the factor
$n^{3/2}$ comes from the Hermitian rounding and the stopping test. -/
theorem FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {a : ℝ} {b ε : F} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ (decodeMatrix dec A), a ≤ |x|)
    (hb : specNorm (decodeMatrix dec A) ≤ dec b) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2)
    (hu : 640 * n * √(n : ℝ) * (8 + μ n) *
      (newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1) * u ≤ a / dec b * dec ε)
    {N : ℕ} (hN : newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) ≤ N) :
    specNorm (cfc Real.sign (decodeMatrix dec A) - decodeMatrix dec (newtonSchulzSign M ε b N A)) ≤
      dec ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim (_ - _) 0, specNorm_zero]
    exact hε.le
  set Ad := decodeMatrix dec A
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn₁
  -- the scale `b` is positive and at least `a`
  have hab : a ≤ dec b := by
    have hx := hA.eigenvalue_mem_spectrum (k := 0) (by simpa using hn)
    exact ((hspec _ hx).trans (abs_le_specNorm_of_mem_spectrum hA hx)).trans hb
  have hb₀ : 0 < dec b := ha.trans_le hab
  set r := a / dec b with hr
  have hr₀ : 0 < r := div_pos ha hb₀
  have hr₁ : r ≤ 1 := (div_le_one hb₀).mpr hab
  have hs : a / (2 * dec b) = r / 2 := by rw [hr]; field_simp
  rw [hs] at hu hN
  set N₀ := newtonSchulzSteps (r / 2) (dec ε / (16 * n))
  have hN₀ : 0 ≤ N₀ := newtonSchulzSteps_nonneg (by positivity) (by linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  set δ := 4 * √(n : ℝ) * (8 + μ n) * u
  have hδ₀ : 0 ≤ δ := by positivity
  have hK : 160 * n * δ * (N₀ + 1) ≤ r * dec ε := by linarith
  have hK₁ : 160 * n * δ ≤ r * dec ε := by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) hδ₀]
  have hk : 640 * n * (8 + μ n) * u ≤ dec ε := by
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ n)
      (by linarith : (0 : ℝ) ≤ 8 + μ n)) hu₀]
  have hδs : 20 * δ ≤ r / 2 := by nlinarith
  have hδε : 10 * δ ≤ dec ε / (16 * n) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  -- the start `A₀ = fl(A / b)`
  have hA₀ : (decodeMatrix dec (M.hermScale A b)).IsHermitian :=
    hM.isHermitian_decodeMatrix_hermFrom _ _
  have hAs : ((dec b)⁻¹ • Ad).IsHermitian := hA.smul (IsSelfAdjoint.all _)
  have hAs₁ : specNorm ((dec b)⁻¹ • Ad) ≤ 1 :=
    specNorm_le_of_forall_mem_spectrum_abs_le hAs zero_le_one fun y hy => by
      obtain ⟨x, hx, rfl⟩ := exists_mem_spectrum_eq_mul hA _ hy
      rw [abs_mul, abs_of_pos (inv_pos.mpr hb₀), inv_mul_le_one₀ hb₀]
      exact (abs_le_specNorm_of_mem_spectrum hA hx).trans hb
  have hrx : ∀ x ∈ spectrum ℝ Ad, r ≤ |(dec b)⁻¹ * x| := fun x hx => by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hb₀), hr, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hspec x hx) (inv_pos.mpr hb₀).le
  have he := hM.specNorm_sub_decodeMatrix_hermScale_le hu₀ hτ₀ hA hb₀.ne'
    (by rw [abs_of_pos hb₀, div_le_iff₀ hb₀]; nlinarith [specNorm_nonneg Ad])
  have he' : specNorm ((dec b)⁻¹ • Ad - decodeMatrix dec (M.hermScale A b)) ≤ δ / 16 := by
    refine he.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hAs₁ (by positivity : (0 : ℝ) ≤ u * √(n : ℝ)),
      mul_nonneg hu₀ hμ, mul_nonneg hu₀ (by positivity : (0 : ℝ) ≤ √(n : ℝ))]
  have hch₀ : ∀ y ∈ spectrum ℝ (decodeMatrix dec (M.hermScale A b)),
      IsNewtonSchulzChain (r / 2) δ y 0 := by
    intro y hy
    obtain ⟨w, hw, hwy⟩ := exists_mem_spectrum_abs_sub_le hAs hA₀ hy
    have hw₁ := (abs_le_specNorm_of_mem_spectrum hAs hw).trans hAs₁
    obtain ⟨x, hx, rfl⟩ := exists_mem_spectrum_eq_mul hA _ hw
    have hw₂ := hrx x hx
    have h₁ := abs_sub_abs_le_abs_sub ((dec b)⁻¹ * x) y
    have h₂ := abs_sub_abs_le_abs_sub y ((dec b)⁻¹ * x)
    rw [abs_sub_comm] at h₂
    exact isNewtonSchulzChain_zero hδ₀ (by linarith) (by linarith)
  have hloop := specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzLoop_le hM hμ hu₀ hτ₀ hτ hΩ hn hε
    hε₁ hk (by positivity) (by linarith) hδs hδε N 0 _ hA₀ hch₀ (by simpa using hN)
  rw [Nat.cast_zero, sub_zero, max_eq_right (by linarith)] at hloop
  change _ ≤ 2 / 3 * dec ε + (N₀ + 1) * (2 * δ / (r / 2)) at hloop
  -- the first rounding moves the sign by at most `2‖A/b − A₀‖₂ / (a/b)`
  have hsign := hAs.specNorm_cfc_sign_sub_cfc_sign_le hA₀ hr₀ fun y hy => by
    obtain ⟨x, hx, rfl⟩ := exists_mem_spectrum_eq_mul hA _ hy
    exact hrx x hx
  rw [cfc_sign_smul hA (inv_pos.mpr hb₀)] at hsign
  have htri := specNorm_add_le (cfc Real.sign Ad - cfc Real.sign
    (decodeMatrix dec (M.hermScale A b))) (cfc Real.sign (decodeMatrix dec (M.hermScale A b)) -
      decodeMatrix dec (newtonSchulzSign M ε b N A))
  rw [sub_add_sub_cancel, newtonSchulzSign] at htri
  have h₁ : 2 * specNorm ((dec b)⁻¹ • Ad - decodeMatrix dec (M.hermScale A b)) / r ≤
      dec ε / 160 := by
    have := mul_nonneg (sub_nonneg.mpr hn₁) hδ₀
    rw [div_le_iff₀ hr₀]; linarith
  have h₂ : (N₀ + 1) * (2 * δ / (r / 2)) ≤ dec ε / 40 := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hn₁) hδ₀) (by linarith : 0 ≤ N₀ + 1)
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
  exact htri.trans (by linarith [hsign.trans h₁])

end Accuracy

end NLAlib
