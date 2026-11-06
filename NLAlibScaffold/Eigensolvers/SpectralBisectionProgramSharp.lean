/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.SpectralBisectionProgram

/-!
# The sharp bit count, for the program (scaffold, blocked on HDIAG-BOUNDS)

**This file depends on a theorem of the HDIAG-BOUNDS stage that is not on this branch**: EV7', the
sharp bit count of Hermitian diagonalization, stated on `research/hdiag-bounds` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md` there; the primed bit-count theorem
of the machine contract, …_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw' in
`NLAlibScaffold/Eigensolvers/SpectralBisection.lean` there), being proved now. The statement
below is its transfer to the registered tree `NLAlib.eighProg.compiled`, by the same reduction as
`NLAlib.matrixFreeRoundedProbEigh` (design note `docs/design/Computation-EighProgram.md`, §7.3). It
is not in this stage's targets file; it is dispatched when EV7' lands, and its statement follows
EV7''s hypotheses at the machine roundoff $u_{\mathrm M}$ and normal-sampler constant
$c_{\mathrm N}$ of the ideal machine (re-check them against EV7' as merged).

## Main results

* `NLAlib.matrixFreeRoundedProb_eighProg_of_logb_le'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

open Computation

/-- **The sharp bit count of Hermitian diagonalization, for the program**: the registered tree
`NLAlib.eighProg.compiled` meets the rounded probabilistic model with the hypotheses of
`NLAlib.MatrixFreeRoundedProbEigh` but the precision conditions those of EV7' (HDIAG-BOUNDS) at the
machine roundoff $u_{\mathrm M} = (c(\mathrm{uniform}) + 1)u > 0$ and normal-sampler constant
$c_{\mathrm N} = 2(c(\mathrm{gaussian}) + 3)$: $\log_2(1/\varepsilon) + \tfrac32\log_2(1/\theta) +
O(\log n + \log\log(1/\varepsilon))$ bits with $n^{2.5}\max(\mu_{\mathrm{MM}}, \sqrt n)$ in place
of EV7's $n^5\mu_{\mathrm{MM}}$. [Shah2024, Theorem 4.2], for the program. No printed source.
Proof: as the transfer of the shallow bit count (`NLAlib.matrixFreeRoundedProb_eighProg_of_logb_le`,
scaffold), with EV7' of HDIAG-BOUNDS in place of the shallow bit count. M, about 90 lines. -/
theorem matrixFreeRoundedProb_eighProg_of_logb_le' (P ι : Type) [DecidableEq P] (p : P)
    (mm qr : ι) (K : Type) [Inhabited K] (dec : P → K → ℝ) (u Ω θ : ℝ) (μM μQ : ℕ → ℝ)
    (c : Dist → ℝ) :
    MatrixFreeRoundedProb p (eighProg.compiled p mm qr) (fun _ _ => True)
      (fun N _ => EighData K N)
      (fun N _ x => ![(pairLayout.toArray x.A).map some, #[some x.R₀, some x.ε, some x.β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none])
      (fun N _ I => IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem ∧
        IsExactIntLit dec I.sem (N + 4) ∧ IsExactToNat dec I.sem ∧ MulShrinks dec I.sem ∧
        (∃ mmR : MatMulMap (K × K), IsMatMulKernel I mm pairLayout mmR ∧
          IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mmR) ∧
        ∃ qrR : QRMap (K × K), IsQRKernel I qr pairLayout qrR ∧
          IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qrR)
      (fun ρ => IsTapeRounding dec p u 0 (2 * Ω) c ρ ∧
        (∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y) ∧
        ∀ g : Dist, (Set.range (ρ g 0)).Countable ∧ ∀ z, MeasurableSet (ρ g 0 ⁻¹' {z}))
      (fun N n x =>
        let uM := (c .uniform + 1) * u
        let cN := 2 * (c .gaussian + 3)
        let ℓ := n 0
        let βb := ((ℓ : ℝ) - 1) ^ 2 * dec p x.ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
          √(N * min (N : ℝ) (ℓ + 1) * min (N : ℝ) (Real.exp 1)) *
          (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))))
        let Nst := newtonSchulzSteps (θ / (12 * N * ℓ * (ℓ + 1))) (dec p x.β / (16 * N))
        (decodeMatrix (dec p) x.A).IsHermitian ∧
        specNorm (decodeMatrix (dec p) x.A) ≤ dec p x.R₀ ∧ 0 < dec p x.R₀ ∧
        0 < dec p x.ε ∧ dec p x.ε ≤ 2⁻¹ ^ 15 ∧ 0 < θ ∧ θ ≤ 1 ∧ bisectionDepth (dec p x.ε) ≤ ℓ ∧
        0 < dec p x.β ∧ dec p x.β ≤ βb ∧ βb / (1 + 2⁻¹ ^ 6) ≤ dec p x.β ∧
        0 < u ∧ 0 ≤ c .uniform ∧ 0 ≤ c .gaussian ∧ (c .gaussian + 3) * u ≤ 1 / 10 ∧
        Monotone μM ∧ Monotone μQ ∧ 0 ≤ μM 0 ∧ 0 ≤ μQ 0 ∧
        Real.logb 2 (dec p x.ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
          Real.logb 2 (N * (4 * μM N + 10 + 10 * √(N : ℝ))) +
          1 / 2 * Real.logb 2 (N * min (N : ℝ) (ℓ + 1) * min (N : ℝ) (Real.exp 1)) +
          Real.logb 2 (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))) +
          Real.logb 2 (ℓ * (ℓ + 1)) +
          Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) + 13 ≤
            Real.logb 2 uM⁻¹ ∧
        Real.logb 2 (dec p x.β)⁻¹ +
          Real.logb 2 (2048 * (N + Nst + 1) * (4 * μM N + 10 + 10 * √(N : ℝ)) +
            16 * (4 * μQ N + 4 * √(N : ℝ) * (cN + 1) + 2 * μM N + 1)) ≤ Real.logb 2 uM⁻¹ ∧
        Nst ≤ n 1 ∧
        16 * (2 * dec p x.R₀ + N + 2 * ℓ + 2 * √2 * √(N : ℝ) +
          √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))) ≤ Ω)
      (fun N _ x st => ∃ (U : Matrix (Fin N) (Fin N) (K × K)) (d : Fin N → K),
        pairLayout.Holds st.store p 2 0 U ∧ (∀ i : Fin N, st.store.read p 3 i = some (d i)) ∧
        IsApproxDiagonalization (decodeMatrix (dec p) x.A) (decodeMatrix (dec p) U)
          (fun i => dec p (d i)) (2 * dec p x.ε * dec p x.R₀) (dec p x.ε / 3))
      (fun _ _ _ => θ) := by
  sorry

end NLAlib
