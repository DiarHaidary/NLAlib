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
(Theorem 2.6), both under the contracts `NLAlib.IsMatMulErr` and `NLAlib.IsRoundingFn`.

## Main results

* `NLAlib.isHermitian_newtonSchulzRounded`, `NLAlib.isHermitian_newtonSchulzSign`.
* `NLAlib.IsMatMulErr.specNorm_sub_newtonSchulzRounded_le`: one step.
* `NLAlib.IsMatMulErr.specNorm_cfc_sign_sub_newtonSchulzSign_le`: the algorithm.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The rounded Newton–Schulz step is Hermitian.
Proof: it is a `NLAlib.roundHermitian`; `NLAlib.isHermitian_roundHermitian`. S, 1 line. -/
theorem isHermitian_newtonSchulzRounded (mm : MatMulMap 𝕜) (fl : ℝ → ℝ)
    (A : Matrix (Fin n) (Fin n) 𝕜) : (newtonSchulzRounded mm fl A).IsHermitian := by
  sorry

/-- The Newton–Schulz sign algorithm returns a Hermitian matrix, for every input and step limit.
Proof: induction on the step limit in `NLAlib.newtonSchulzLoop`: its result is the start or a
rounded step, both `NLAlib.roundHermitian` (`NLAlib.isHermitian_roundHermitian`,
`NLAlib.isHermitian_newtonSchulzRounded`). S, about 10 lines. -/
theorem isHermitian_newtonSchulzSign (mm : MatMulMap 𝕜) (fl : ℝ → ℝ) (ε b : ℝ) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) 𝕜) : (newtonSchulzSign mm fl ε b N A).IsHermitian := by
  sorry

/-- **One rounded Newton–Schulz step** (Lemma 2.1): under `NLAlib.IsMatMulErr` $u$ $\tau$ $\Omega$
$\mu$ and `NLAlib.IsRoundingFn` $u$ $\tau$ $\Omega$, with $\mu(n) \ge 0$,
$u(8 + \mu(n)) \le 1/10$, $0 \le \tau$, $2n\tau \le 1$ and $\Omega \ge 8$, every Hermitian
$\mathbf{A} \in \Bbbk^{n \times n}$ with $\|\mathbf{A}\|_2 \le 11/10$ satisfies
$$\Bigl\|\tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2) - \tilde g(\mathbf{A})\Bigr\|_2 \le
4\sqrt n\,(8 + \mu(n))\,u \,,$$
$\tilde g$ the rounded step `NLAlib.newtonSchulzRounded`. [Shah2024, Lemma 2.1], there
$\tfrac12(7 + (6 + \mu)a^2)a\,u$ for $\|\mathbf{A}\|_2 \le a$ without the Hermitian part; the
factor $\sqrt n$ is the cost of storing the result exactly Hermitian, and the statement is for
the regime $a \le 11/10$ of the iteration.
Proof: follow [Shah2024, proof of Lemma 2.1] with the contracts: $\mathbf{X} =
\mathrm{mm}(\mathbf{A}, \mathbf{A})$ has error $\le 1.21\mu u$; $\mathbf{B}$ = rounded
$3\mathbf{I} - \mathbf{X}$ has error $\le u\max(\|3\mathbf{I} - \mathbf{X}\|_2, \tau) \le 4.33u$
(`NLAlib.IsRoundingFn.specNorm_sub_roundDiag_le`), $\|\mathbf{B}\|_2 \le 4.39$;
$\mathbf{Y} = \mathrm{mm}(\mathbf{A}, \mathbf{B})$ has error $\le 4.83\mu u$; so
$\|\mathbf{Y} - 2g(\mathbf{A})\|_2 \le 6.17\mu u + 4.77u$; the Hermitian part is a contraction
and fixes $2g(\mathbf{A})$ (`NLAlib.hermitianPart_sub`,
`Matrix.IsHermitian.hermitianPart_eq`, `hermitianPart` $= \tfrac12(\mathbf{E} +
\mathbf{E}^{\mathsf{H}})$ with `NLAlib.specNorm_conjTranspose`), and the last rounding errs by
at most $u(1.34\sqrt n + 1)$ (`NLAlib.IsRoundingFn.specNorm_sub_roundHermitian_le`, $\lvert g
\rvert \le 1$ on $[-1.1, 1.1]$). Sum: $\le \sqrt n\,u(3.1\mu + 4.8)$. Check each $\Omega$ and
$\tau$ side condition (all magnitudes are at most $4.9$). Split into private lemmas per step.
M, about 80 lines. -/
theorem IsMatMulErr.specNorm_sub_newtonSchulzRounded_le {u τ Ω : ℝ} {μ : ℕ → ℝ}
    {mm : MatMulMap 𝕜} {fl : ℝ → ℝ} (hmm : IsMatMulErr u τ Ω μ mm)
    (hfl : IsRoundingFn u τ Ω fl) (hμ : 0 ≤ μ n) (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 8 ≤ Ω) {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (hA₁ : specNorm A ≤ 11 / 10) :
    specNorm ((2⁻¹ : ℝ) • (A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) 𝕜) - A * A)) -
      newtonSchulzRounded mm fl A) ≤ 4 * √(n : ℝ) * (8 + μ n) * u := by
  sorry

/-- **Accuracy of the Newton–Schulz sign algorithm** (Theorem 2.6): under `NLAlib.IsMatMulErr`
$u$ $\tau$ $\Omega$ $\mu$ and `NLAlib.IsRoundingFn` $u$ $\tau$ $\Omega$ with $\mu(n) \ge 0$,
$0 \le \tau$, $2n\tau \le 1$ and $\Omega \ge 8$, let $\mathbf{A} \in \Bbbk^{n \times n}$ be
Hermitian with $\|\mathbf{A}\|_2 \le b$ and every eigenvalue of modulus at least $a > 0$, and
$0 < \varepsilon \le 1/2$. With $N_0 = N(a/(2b), \varepsilon/(16n))$
(`NLAlib.newtonSchulzSteps`), if
$$640\, n^{3/2}\,(8 + \mu(n))\,(N_0 + 1)\,u \le \frac{a}{b}\,\varepsilon$$
and the step limit is at least $N_0$, then
$$\|\operatorname{sign}(\mathbf{A}) - \mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)\|_2 \le
\varepsilon \,,$$
$\mathsf{newtonSchulzSign}$ the algorithm `NLAlib.newtonSchulzSign`. [Shah2024, Theorem 2.6],
there with
$u \le \frac{a}{b}\varepsilon/(4\max(N n\mu_g(n, 1.1), n^2))$, $N = N(a/b, \varepsilon/(8n))$ and
the contour bound of Lemma 2.2; here the perturbation bound is dimension-free and the factor
$n^{3/2}$ comes from the Hermitian rounding and the stopping test.
Proof: (1) $\mathbf{A}_0$ = rounded $\mathbf{A}/b$ is within $2\sqrt n u$ of $\mathbf{A}/b$
(`NLAlib.IsRoundingFn.specNorm_sub_roundHermitian_le`), so its eigenvalues have modulus in
$[a/(2b), 3/2]$ (`Matrix.IsHermitian.abs_eigenvalue_sub_le`). (2) Every step errs by
$\nu u$, $\nu = 4\sqrt n(8 + \mu(n))$ (`NLAlib.IsMatMulErr.specNorm_sub_newtonSchulzRounded_le`,
with `Matrix.IsHermitian.cfc_newtonSchulz`), so every eigenvalue of $\mathbf{A}_{k+1}$ is
$g(\lambda) + \xi$ for an eigenvalue $\lambda$ of $\mathbf{A}_k$ and $\lvert \xi \rvert \le \nu u$
(Weyl for Hermitian matrices, `Matrix.IsHermitian.abs_eigenvalue_sub_le` and
`Matrix.IsHermitian.eigenvalue_cfc_of_monotoneOn` or a spectrum-inclusion argument); scalar chains
from eigenvalues of $\mathbf{A}_0$ satisfy the hypotheses of
`NLAlib.abs_one_sub_sq_le_of_newtonSchulzSteps_le` at tolerance $\varepsilon/(16n)$ and of
`NLAlib.min_abs_le_abs_of_abs_sub_newtonSchulz_le`, so the moduli stay in $[a/(2b), 1.1]$ and the
test passes by step $\lceil N_0 \rceil$ (the computed test matrix is within
$1.21\mu u + u(\cdots)$ of $\mathbf{I} - \mathbf{A}_k^2$, `NLAlib.norm_apply_le_specNorm`).
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
theorem IsMatMulErr.specNorm_cfc_sign_sub_newtonSchulzSign_le {u τ Ω : ℝ} {μ : ℕ → ℝ}
    {mm : MatMulMap 𝕜} {fl : ℝ → ℝ} (hmm : IsMatMulErr u τ Ω μ mm)
    (hfl : IsRoundingFn u τ Ω fl) (hμ : 0 ≤ μ n) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1)
    (hΩ : 8 ≤ Ω) {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) {a b ε : ℝ} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ A, a ≤ |x|) (hb : specNorm A ≤ b) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2)
    (hu : 640 * n * √(n : ℝ) * (8 + μ n) *
      (newtonSchulzSteps (a / (2 * b)) (ε / (16 * n)) + 1) * u ≤ a / b * ε)
    {N : ℕ} (hN : newtonSchulzSteps (a / (2 * b)) (ε / (16 * n)) ≤ N) :
    specNorm (cfc Real.sign A - newtonSchulzSign mm fl ε b N A) ≤ ε := by
  sorry

end NLAlib
