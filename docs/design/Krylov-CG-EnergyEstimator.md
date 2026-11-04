# Physical delayed CG energy estimators

Design, 2026-11-04. This work concerns the actual computed iterates of the existing real
`CGRun`, with its successful divisions, zero initial iterate, local error bounds, and
terminal-zero convention. No algorithm, hypothesis interface, or Mathlib deviation is added.
The parent reviewed the signatures and derivation before implementation.

## Objects, interfaces, and consumers

Reuse Mathlib quadratic forms, spectral inclusion and finite intervals, and NLAlib's `CGRun`,
physical solution equation, a priori physical energy and residual-gap bounds. There is no
second energy or estimator definition: the estimator is the interval sum of existing
`γ i * ρ i ^ 2`. Its exact real-valued evaluation is analyzed; additional arithmetic in
summing the scalar estimator is outside this run model.

The numerical vocabulary extends the existing finite-precision CG accumulation row by
`cgEnergyEstimatorFactor j d`, currently `150 * (d : ℝ) * (j + d)`. It is a rounding budget,
not a separate mathematical object, and needs no Mathlib bridge. It is registered in
`docs/constants.toml`; its nonnegativity and one-sided comparison API permit improvement.

Future stopping criteria consume the interval error directly. Physical/model comparisons
consume the start-zero case and the existing initial-energy perturbation bound. Certification
of a small terminal tail remains a necessary input for an upper bound from delayed decrements;
a lower estimator alone does not certify stopping.

## Exact statements

All declarations below are in `namespace CGRun`, with `{n k : ℕ} (C : CGRun n k)`.
The common hypotheses are written explicitly in each implemented theorem:

```lean
{a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
(hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
{xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b)
```

The headline has the exact additional binders and conclusion:

```lean
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le
    {j d : ℕ} (hjd : j + d ≤ k) :
    |(quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d))) -
      ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2| ≤
    cgEnergyEstimatorFactor j d * C.ε * (a' / a) *
      (‖WithLp.toLp 2 C.b‖ ^ 2 / a)
```

Useful corollaries have conclusions `sum - remainder ≤ physical energy`, and
`|physical energy - sum| ≤ terminal energy + remainder`. A sufficient stopping theorem takes
`hterminal : quadForm C.A (xs - C.x (j + d)) ≤ tail` and
`hstop : sum + remainder + tail ≤ tolerance` and concludes
`quadForm C.A (xs - C.x j) ≤ tolerance`.

The physical/model absolute comparison takes an additional solution
`hy : C.backwardH *ᵥ ys = C.dilatedRhs` and `hj : j ≤ k`, and concludes

```lean
|quadForm C.A (xs - C.x j) -
    quadForm C.backwardH (ys - cgIterate C.backwardH C.dilatedRhs 0 j)| ≤
  2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 +
  cgEnergyEstimatorFactor 0 j * C.ε * (a' / a) *
    (‖WithLp.toLp 2 C.b‖ ^ 2 / a)
```

## Derivation and file placement

Write `z=εκ`, `u=‖b‖²/a`, `s_i=γ_iρ_i²` and `E_i=Q_A(xs-x_i)`.
The retained local absolute defects give
`|p_i·r_i-ρ_i²|≤26izρ_i²` and `|γ_i²p_i·Ap_i-s_i|≤7zs_i`.
The already proved physical a priori energy and Rayleigh lower bound give
`‖xs-x_i‖≤2‖b‖/a`; hence `‖x_i‖≤3‖b‖/a`,
`‖xs-x_i-γ_ip_i‖≤3.5‖b‖/a`, and `‖ex_i‖≤4.5ε‖b‖/a`.
The full quadratic iterate-update error is bounded by
`(31.5ε + 20.25ε²)κu ≤32zu` using the certified precision window.
The gap term is at most `36izu`. Thus
`|E_i-E_(i+1)-s_i|≤(52i+7)zs_i+(36i+32)zu≤150(i+1)zu`, since `s_i≤2u`.
Summation over the interval gives `150d(j+d)zu`. No Euclidean or energy monotonicity is assumed;
all quadratic errors are retained. Delay zero and precision zero have zero remainder.

* `CGAccuracy.lean`: strengthen the existing pairing proof to an absolute-defect theorem,
  and reprove its existing lower-bound theorem as a corollary. This owns pairing arithmetic.
  Keep the hard 1500-line limit; no second induction or duplicate proof is introduced.
* New `CGEnergyEstimator.lean`, importing `CGEnergy`: numerical budget, absolute local
  curvature/update estimates, interval theorem, lower estimate, reliability/stopping consumers,
  and physical/model absolute comparison. These statements concern physical energy estimation.
* Parent owns `docs/constants.toml`, the existing vocabulary row, and generated root imports.

Mathlib searches found no finite-precision CG energy estimator or local arithmetic analysis.
Reuse `EuclideanSpace.abs_dotProduct_le_norm`, `norm_sub_le`, `norm_toLp_mulVec_le`,
`Finset.sum_Ico_succ_top`, `abs_add`, and scalar order arithmetic. Existing NLAlib lower and
upper Rayleigh bounds, physical energy a priori theorem and model decrement identity are reused.

## Material and limits

Read `Krylov-CG-FinitePrecision-Bounds.md`, `Krylov-CG-Certificates.md`, and the existing
`CGAccuracy`, `CGEnergy` and `CGBackward` APIs. Read Strakos–Tichy (2002), Theorem 10.1,
printed page 76, equations (10.6)–(10.9):
<https://etna.ricam.oeaw.ac.at/vol.13.2002/pp56-80.dir/pp56-80.pdf>.
Its physical delayed-energy identity motivates this theorem. Its asymptotic remainder and
near-monotonicity reasoning are replaced with explicit bounds from the proved a priori
window. This is an adaptation under this library's arithmetic model, not a verbatim
formalization of their hypotheses or constants. No unrestricted fixed-precision horizon or
IEEE execution claim is made.

## Review and validation

No unresolved interface decision. Builds are serialized in this checkout with
`LEAN_NUM_THREADS=2` and log files. Targeted warning-fatal checking, source rules, constants,
and the parent's complete stage audit are required. No checks, pins, targets, approvals,
allowlists or baselines are edited; no commit or push.

## Completed targeted validation

Independent integration review accepted the direct local expansion, all product and quadratic
rounding terms, the constants, and the explicit terminal-tail premise in the stopping theorem.
`CGAccuracy.lean` compiled successfully in the warning-free dependency build of
`CGSpectralConvergence` on 2026-11-04; it remains 1492 lines. The complete new
`CGEnergyEstimator.lean` passed `LEAN_NUM_THREADS=2 lake lean` with the 8000 MB cap,
exit 0 and no warnings (`/tmp/cg-estimator-build.log`). This checks every interval, lower,
absolute estimator, stopping, and physical/model theorem, including zero delay and zero
precision in the theorem signatures. The complete mathematical documentation rendering check
passed with zero problems (`/tmp/cg-estimator-latex.log`). The parent owns integration and the
mandatory complete stage audit; these targeted checks do not replace that audit.
