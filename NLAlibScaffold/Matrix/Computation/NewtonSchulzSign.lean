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
  sorry

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
  sorry

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
