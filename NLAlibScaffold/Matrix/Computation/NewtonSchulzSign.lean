/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.NewtonSchulzSign

/-!
# Sharper constants for the rounded Newton–Schulz sign (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/Matrix/Computation/NewtonSchulzSign.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, items I8 and I9): one rounded
step with the $\sqrt n$ of the Hermitian rounding on the rounding constant only, not on
$\mu_{\mathrm{MM}}$ (SN3'), and [Shah2024, Theorem 2.6] with the step errors summed as a
geometric series, so that the step count no longer multiplies the precision condition and the
dimension factor of the componentwise stopping test sits in a separate, non-binding condition
(SN4').

## Main results

* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add` (SN3').
* `NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le`
  (SN4').
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μ μQ : ℕ → ℝ}
  {n : ℕ}

/-- **One rounded Newton–Schulz step, sharp form** (SN3'): under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le`,
$$\|g(\mathbf{A}) - \tilde g(\mathbf{A})\|_2 \le \bigl(4\mu(n) + 10 + 10\sqrt n\bigr)u \,.$$
The $\sqrt n$ comes only from the entrywise rounding of the stored Hermitian part (gap G1 of
[Shah2024]); the product errors are normwise. [Shah2024, Lemma 2.1].
Proof: the proof of SN3 with its last step changed: the bound on the Hermitian part of the
product, $(3.23\mu + 6.23)u$, and the rounding of `NLAlib.FloatMachine.hermAvg`,
$3u(\sqrt n\|\mathbf{Z}\|_2 + 2n\tau) \le 3u(2\sqrt n + 1)$
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le`), are added instead of
multiplying the first by $\sqrt n$; $3.23\mu + 9.23 + 6\sqrt n \le 4\mu + 10 + 10\sqrt n$.
M, about 120 lines (mostly SN3's, made public or copied). -/
theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm ((2⁻¹ : ℝ) • (decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A)) - decodeMatrix dec (newtonSchulzRounded M A)) ≤
        (4 * μ n + 10 + 10 * √(n : ℝ)) * u := by
  sorry

/-- **Accuracy of the rounded Newton–Schulz sign with geometric error propagation** (SN4'): let
the machine meet `NLAlib.FloatMachine.IsAccurate`, $\mathbf{A}$ have Hermitian decoding with
$\|\mathbf{A}\|_2 \le b$ and every eigenvalue of modulus at least $a > 0$, $0 < \varepsilon \le
1/2$, $\nu = 4\mu(n) + 10 + 10\sqrt n$, $N_0 = N(a/(2b), \varepsilon/(16n))$ and
$$32\,\nu u \le \frac ab\,\varepsilon \,, \qquad 640\,(n + N_0 + 1)\,\nu u \le \varepsilon \,.$$
Then `NLAlib.newtonSchulzSign` with at least $N_0$ steps is within $\varepsilon$ of
$\operatorname{sign}\mathbf{A}$. Compared with
`NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le`
($640n^{3/2}(8 + \mu)(N_0 + 1)u \le (a/b)\varepsilon$), the step count and the dimension factor
of the stopping test leave the binding condition. [Shah2024, Theorem 2.6].
Proof: as SN4 (start error, stopping test, final $\|\mathbf{X} - \operatorname{sign}\mathbf{X}\|_2
\le \|\mathbf{I} - \mathbf{X}^2\|_2$ by `Matrix.IsHermitian.specNorm_sub_cfc_sign_le`),
except the propagation: with $a_k$ the least eigenvalue modulus of the $k$-th stored iterate and
$\delta = \nu u$ (SN3'), Weyl and NS13 give $a_{k+1} \ge \tfrac{11}{8}a_k - \delta \ge
1.325\,a_k$ while $a_k \le 1/2$, and $a_{k+1} \ge 1/2$ afterwards
(`NLAlib.abs_newtonSchulz_le_one`, NS9); each step changes the sign by at most
$2\delta/g(a_k)$ (`Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le` with
`Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz`), so the total is at most
$\delta(5.93/a_0 + 2.91(N_0 + 1))$ with $a_0 \ge a/b - 2\sqrt n u$; the first condition bounds
the first term by $0.19\varepsilon$, the second the rest, and the stopping test leaves
$\tfrac23\varepsilon$ as in SN4. The second condition implies $640n(8 + \mu)u \le \varepsilon$
(since $\nu \ge 8 + \mu$), the hypothesis `hk` of SN4's private stopping-test lemmas, for every
$n$. L, about 250 lines (SN4's private lemmas reused). -/
theorem FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {a : ℝ} {b ε : F} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ (decodeMatrix dec A), a ≤ |x|)
    (hb : specNorm (decodeMatrix dec A) ≤ dec b) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2)
    (hu : 32 * (4 * μ n + 10 + 10 * √(n : ℝ)) * u ≤ a / dec b * dec ε)
    (hstop : 640 * (n + newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1) *
      (4 * μ n + 10 + 10 * √(n : ℝ)) * u ≤ dec ε)
    {N : ℕ} (hN : newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) ≤ N) :
    specNorm (cfc Real.sign (decodeMatrix dec A) - decodeMatrix dec (newtonSchulzSign M ε b N A)) ≤
      dec ε := by
  sorry

end NLAlib
