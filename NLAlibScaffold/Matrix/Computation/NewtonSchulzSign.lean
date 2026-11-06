/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.NewtonSchulzSign
public import NLAlibScaffold.Matrix.Computation.EntrywiseRounding
public import NLAlibScaffold.Matrix.Functions.Sign
public import NLAlibScaffold.Polynomial.Approximation.NewtonSchulz

/-!
# Accuracy of the Newton–Schulz sign algorithm (scaffold)

Statements for `NLAlib/Matrix/Computation/NewtonSchulzSign.lean` (stage HDIAG, wave W2, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.4): the error of one rounded
step (Lemma 2.1 of [Shah2024], with the Hermitian part) and the accuracy of the algorithm
(Theorem 2.6), both under the machine contract `NLAlib.FloatMachine.IsAccurate`, for decoded
matrices.

## Main results

* `NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzRounded`,
  `NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzSign`.
* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le`: one step.
* `NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le`: the
  algorithm.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μ μQ : ℕ → ℝ}
  {n : ℕ}

/-- The rounded Newton–Schulz step decodes to a Hermitian matrix, under
`NLAlib.FloatMachine.IsAccurate`.
Proof: it is a `NLAlib.FloatMachine.hermAvg`, a `NLAlib.FloatMachine.hermFrom`;
`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`. S, 2 lines. -/
theorem FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzRounded
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (A : Matrix (Fin n) (Fin n) (F × F)) :
    (decodeMatrix dec (newtonSchulzRounded M A)).IsHermitian := by
  unfold newtonSchulzRounded FloatMachine.hermAvg
  exact hM.isHermitian_decodeMatrix_hermFrom _ _

/-- The Newton–Schulz sign algorithm returns a matrix with Hermitian decoding, for every input and
step limit, under `NLAlib.FloatMachine.IsAccurate`.
Proof: induction on the step limit in `NLAlib.newtonSchulzLoop`: its result is the start (a
`NLAlib.FloatMachine.hermScale`) or a rounded step, both `NLAlib.FloatMachine.hermFrom`
(`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`,
`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzRounded`). S, about 10
lines. -/
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
the regime $a \le 11/10$ of the iteration.
Proof: follow [Shah2024, proof of Lemma 2.1] with the contracts: $\mathbf{X} =
\mathrm{mm}(\mathbf{A}, \mathbf{A})$ has error $\le 1.21\mu u$; $\mathbf{B}$ = rounded
$3\mathbf{I} - \mathbf{X}$ (with the stored $3$, within $3u$ of $3$) has error
$\le u\max(\|3\mathbf{I} - \mathbf{X}\|_2, \tau) + 3u \le 7.4u$
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le`,
`NLAlib.FloatMachine.IsAccurate.decodeMatrix_negMat`), $\|\mathbf{B}\|_2 \le 4.4$;
$\mathbf{Y} = \mathrm{mm}(\mathbf{A}, \mathbf{B})$ has error $\le 4.83\mu u$; so
$\|\mathbf{Y} - 2g(\mathbf{A})\|_2 \le 6.2\mu u + 8.2u$; $(\mathbf{Y} + \mathbf{Y}^{\mathsf{H}})/4$
is within half of that of $g(\mathbf{A})$ (the Hermitian part is a contraction fixing
$2g(\mathbf{A})$, `NLAlib.specNorm_conjTranspose`), the stored $4$ costs a relative $u$, and the
stored average errs by at most $3u(1.34\sqrt n + 1)$
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le`, $\lvert g \rvert \le 1$ on
$[-1.1, 1.1]$). Sum: $\le \sqrt n\,u(3.1\mu + 13)$, within $4\sqrt n(8 + \mu)u$. Check each
$\Omega$ and $\tau$ side condition (all magnitudes are at most $4.9$, except the input of the
stored average: $3\|\mathbf{Y}\|_2 + \tau \le 8.35$, whence $\Omega \ge 9$). Split into private
lemmas per step. M, about 80 lines. -/
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
$u \le \frac{a}{b}\varepsilon/(4\max(N n\mu_g(n, 1.1), n^2))$, $N = N(a/b, \varepsilon/(8n))$ and
the contour bound of Lemma 2.2; here the perturbation bound is dimension-free and the factor
$n^{3/2}$ comes from the Hermitian rounding and the stopping test.
Proof: (1) $\mathbf{A}_0$ = stored $\mathbf{A}/b$ is within $2\sqrt n u$ of $\mathbf{A}/b$
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermScale_le`), so its eigenvalues have
modulus in $[a/(2b), 3/2]$ (`Matrix.IsHermitian.abs_eigenvalue_sub_le`). (2) Every step errs by
$\nu u$, $\nu = 4\sqrt n(8 + \mu(n))$
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le`,
with `Matrix.IsHermitian.cfc_newtonSchulz`), so every eigenvalue of $\mathbf{A}_{k+1}$ is
$g(\lambda) + \xi$ for an eigenvalue $\lambda$ of $\mathbf{A}_k$ and $\lvert \xi \rvert \le \nu u$
(Weyl for Hermitian matrices, `Matrix.IsHermitian.abs_eigenvalue_sub_le` and
`Matrix.IsHermitian.eigenvalue_cfc_of_monotoneOn` or a spectrum-inclusion argument); scalar chains
from eigenvalues of $\mathbf{A}_0$ satisfy the hypotheses of
`NLAlib.abs_one_sub_sq_le_of_newtonSchulzSteps_le` at tolerance $\varepsilon/(16n)$ and of
`NLAlib.min_abs_le_abs_of_abs_sub_newtonSchulz_le`, so the moduli stay in $[a/(2b), 1.1]$ and the
test passes by step $\lceil N_0 \rceil$ (the computed test matrix is within
$1.21\mu u + u(\cdots)$ of $\mathbf{A}_k^2 - \mathbf{I}$, `NLAlib.norm_apply_le_specNorm`; the
stored threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ is within a factor $(1 \pm u)^2$ of
$\varepsilon/(4n)$, and the comparisons are exact).
(3) At the stopping step $M \le N_0 + 1$, componentwise entries $\le \varepsilon/(4n)$ give
$\|\mathbf{I} - \mathbf{A}_M^2\|_2 \le 0.37\varepsilon$ (`NLAlib.specNorm_le_frobNorm`), hence
$\|\mathbf{A}_M - \operatorname{sign}(\mathbf{A}_M)\|_2 \le \varepsilon/2$
(`Matrix.IsHermitian.specNorm_sub_cfc_sign_le`). (4) Telescoping the signs:
$\operatorname{sign}(\mathbf{A}_k) = \operatorname{sign}(g(\mathbf{A}_k))$
(`Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz`) and
`Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le` with modulus $a/(2b)$ bound each step by
$4b\nu u/a$, and the start by $4\sqrt n\,b u/a$; the total is $\le 8(N_0 + 1)\nu u\,b/a \le
\varepsilon/(20n)$. Split into private lemmas (1)–(4) and the loop invariant of
`NLAlib.newtonSchulzLoop`. L, about 200 lines. -/
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
  sorry

end NLAlib
