# Input-based finite-precision CG certificates

Design, 2026-11-02. The user requested continuing the explicit-bound investigation and
committing validated milestones. Independent mathematical review accepted the scalar
certificate interface and the prefix induction below before implementation.

## Objects and interfaces

Introduce `CGBackwardCertificate k ε a a'`, data depending only on the iteration count,
precision and spectral endpoints. Its scalar fields are `P`, `K`, `B`, and `d`. They are
chosen bounds, not measured quantities from a CG execution. The structure constructor
accepts the following scalar certificates directly:

* `P_nonneg : 0 ≤ P`, `d_nonneg : 0 ≤ d`, and `d_lt : d < a`;
* `curvature_margin : 0 < a - ε * (2 + ε) * a'`;
* `curvature_le : a' * (1 + ε)^2 ≤ K * (a - ε * (2 + ε) * a')`;
* `direction_le : Λ^(k-1) * ((a'+d)/(a-d)) ≤ P^2`;
* `coefficient_le : (1+4*ε)*(a'+d) ≤ B`;
* `backward_le : normalizedBackwardBound k f p ≤ d`.

Here the existing factors define

```
t = cgLineSearchFactor (k-1) ε * (1+P+K)
Λ = (1+3*t+4*ε+2*ε^2)*(1+4*ε)^2
f = 8*ε*(a'*(1+P)^2+B)
p = cgAdjacentInnerFactor k ε * (a'*(1+P)^2+B*(1+P)).
```

The direction field can use a `let t` expression; no second definition of the accumulated
factors is introduced. Their current values are the finite geometric sums already registered
in `docs/constants.toml`. The certificate is one vocabulary row with its constructor and
theorems as its bridge to the arithmetic `CGRun` model. No new matrix notion or Mathlib
deviation is introduced.

Consumers supply a `CGRun`, so nonnegative local precision, `ε≤1/100`, successful taken
divisions and `k≥1` are inherited. Spectral inclusion for the run implies `a≤a'` because
the run has a nonzero initial residual. The certificate implies `a>0`, `K≥0`, `B≥0` and
`P≥1` in this setting; do not duplicate these as constructor obligations.
The curvature-margin field remains an explicit scalar check. With the current numerical
backward budget it is derivable in a valid run, but it is not a consequence of the abstract
record alone; stating it separately keeps curvature certification independent of subsequent
improvements to the backward bound.

## Statements and consumers

With `C : CGRun n k`, `S : CGBackwardCertificate k C.ε a a'`, and
`hs : spectrum ℝ C.A ⊆ Set.Icc a a'`, expose the following shapes:

```lean
theorem CGRun.norm_p_sq_le_of_certificate
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (S : CGBackwardCertificate k C.ε a a') {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ S.P ^ 2 * C.ρ j ^ 2

theorem CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificate
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (S : CGBackwardCertificate k C.ε a a') :
    frobNorm (C.backwardH - C.dilatedH) ≤ S.d

theorem CGRun.ρ_le_chebyshev_of_certificate
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (S : CGBackwardCertificate k C.ε a a') {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt ((a' + S.d) / (a - S.d)) *
      ((Real.sqrt ((a' + S.d) / (a - S.d)) - 1) /
        (Real.sqrt ((a' + S.d) / (a - S.d)) + 1)) ^ j *
      ‖WithLp.toLp 2 C.b‖
```

Expose the corresponding curvature, Lanczos coefficient and direction-update coefficient
inequalities for the existing numerical specialization. The proof engine may return a
private conjunction, but public independently useful inequalities remain separate.

The old fixed-condition API is a consumer: construct a certificate with
`P=√(3.3κ)`, `K=1.05κ`, `B=1.6a'`, `d=a/2` under
`k^2*√k*ε*κ^2≤10⁻⁵`, then derive its old certificate conclusions from the general engine.
Keep its sharper final `6000*k^2*√k*ε*κ*a'` conclusion through the existing posterior bound.
There must be one prefix-induction engine, not parallel restricted and unrestricted proofs.

## Derivation and edge cases

The curvature margin gives
`μ_j ≥ [a-ε(2+ε)a']*‖p_j‖²` and `γ_j μ_j ≤ (1+ε)²ρ_j²`.
The rational optimal choice of `K` is therefore
`a'(1+ε)²/[a-ε(2+ε)a']`; the record uses a division-free inequality so that a convenient
larger `K` is equally usable.

The current direction recursion actually holds for every `t≥0`. Retaining
`‖r_(i+1)+δ_i p_i‖² ≤ [1+2(1+4ε)t]u`, where
`u=ρ_(i+1)²+δ_i²‖p_i‖²`, gives the coefficient
`1+3ε+2ε²+(2+10ε+8ε²)t`. Local `ε≤.01` bounds it by
`1+3t+4ε+2ε²`. Thus remove the old auxiliary `t≤.1` assumption without changing the factor.

At step `j`, earlier certificates construct the prefix-`j` model and bound residual-ratio
sums. The geometric line-search estimate and unrolled direction recursion then give `P_j`.
The prefix-`j+1` model uses this direction bound and only the coefficient certificates
strictly before `j`, giving the next coefficient bounds. This order avoids circularity.
All closure inequalities may be non-strict; the curvature denominator and `a-d` must be
strictly positive. The terminal residual may vanish and is never divided by. At `k=1`,
the direction factor uses a zero-step geometric sum. Zero precision requires no division
by precision. This is an input-based sufficient certificate, not a proof of feasibility for
every horizon, residual monotonicity, or unrestricted convergence.

### A feasible example beyond the fixed condition

An exact-rational calculation checks the proposed certificate at
`k=400`, `ε=10⁻¹²`, `a=1`, `a'=10`, with
`P=19/5`, `K=11`, `B=11`, `d=1/4`.
The direction expression is at most `13.667090 < P²=14.44`; the backward expression is
at most `0.207077 < d=0.25`. The curvature and coefficient conditions also hold. The old
fixed-condition expression is `k²√k ε κ²=0.00032`, which exceeds `10⁻⁵` by a factor of 32.

The resulting model interval has ratio `(a'+d)/(a-d)=41/3<16`. Its Chebyshev envelope
therefore gives `ρ_400/‖b‖ < 8*(3/5)^400 < 1.5·10⁻⁸⁸` for every successful 400-step run
with these spectral and arithmetic assumptions. The last inequality is also checked with
exact rationals. This is a finite-horizon bound far below the precision parameter; it is
neither stepwise monotonicity nor an unrestricted fixed-precision convergence claim.

The calculation uses rational upper bounds, not floating-point comparisons:
`(1+x)^m ≤ 1/(1-m*x)` and `∑_{i<m}(1+x)^i ≤ m/(1-m*x)` for
`0≤x≤1`, `m*x<1`, obtained from Bernoulli's inequality and
`(1+x)^m(1-x)^m=(1-x²)^m≤1`. Decimal values above are rounded upward for presentation.
This is a checked scalar example, not a Lean instance of the record, a simulated run, or
an asymptotic claim. The reproducible calculation is
`/home/ubuntu/work/cg-residual-experiment/certificate_example.py` in the working environment.

## Placement, reuse and review

* `CGModel.lean`, importing `CGRunModel`: move the prefix constructor, exact backward-model
  bridges and residual-ratio theorem from `CGBackward` here.
  Preserve public names; expose only shared run-specific helpers needed by both consumers.
  Newly public helper names follow the library grammar: `CGRun.isHermitian` and
  `CGRun.norm_dilatedRhs` replace their former private spellings.
* `CGCertificates.lean`, importing `CGModel`: scalar certificate, general direction
  inequalities, curvature estimate, single prefix induction and public certificate bounds.
* `CGBackward.lean`, importing `CGCertificates`: fixed smallness specialization, its scalar
  feasibility proof and existing accuracy/model-energy consequences. Remove the old induction.
  The generic Chebyshev transfer and its new certificate corollary stay here, avoiding
  unnecessary exposure or relocation of their private matrix helpers (design amendment,
  2026-11-02, accepted during implementation planning).
* `CGAccuracy.lean`: reuse the shared `CGRun.n_pos` and `CGRun.isHermitian` lemmas, removing
  the private copies that previously duplicated the backward-analysis helpers.
* `LinearSystems/CGTridiagonal.lean`: public `Matrix.PosDef.one_div_le_cgAlpha`, over `RCLike`
  and arbitrary finite index types and initial iterate. It replaces the long real-only private
  copy in `CGBackward` using this file's existing conjugacy and Rayleigh lemmas. Its subject
  is exact CG, so it belongs here rather than in finite-precision analysis.
* `CONTRIBUTING.md`: the certificate vocabulary row. `NLAlib.lean`: generated imports.

Mathlib has no finite-precision CG model or scalar certificate of this kind (searched).
Reuse Mathlib finite sums, powers, order and positivity, and NLAlib's existing spectral
inclusion, normalized backward bound and exact-CG API. In particular, the new step-length
lemma reuses `cgAlpha_mul_re_quadForm`, `re_quadForm_p_le_r`, and `rayleigh_of_spectrum` in
`CGTridiagonal`, replacing a duplicate proof. No new literature constant is claimed.

Validation: independent review of the actual theorem statements and edge cases, warning-fatal
builds, source-rule checks and the complete `scripts/stage_check.sh` audit before completion.
One Lean build runs at a time in this checkout. No checker, target, baseline or pin changes.

## Completed validation

Independent review accepted the actual induction, scalar specialization, geometric indices,
curvature bound, zero precision, one-step runs and terminal breakdown. Warning-fatal builds
passed for the new modules and the existing `CGBackward` and `CGAccuracy` consumers.
An arbitrary-horizon zero-precision certificate with `P=K=B=1`, `d=0` and `[a,a']=[1,1]`
compiled in `/tmp/cg-certificate-zero.lean`. The numerical example above passed exact-rational
checks; it is not represented as a Lean instance.

The complete `scripts/stage_check.sh` finished with exit 0 on 2026-11-02, recorded in
`/tmp/cg-input-certificates-stage-complete.log`:

* 514 proved modules built with zero compiler warnings.
* 15,804 declarations passed the axiom/unsafe/partial audit, with zero violations.
* All 14 environment linters, generated imports and build freshness checks passed.
* Kernel replay checked 16,034 constants across 519 modules with zero violations.
* Program, target, access-model, reference, constant and mathematical-documentation checks passed.
* The 109-rule check reported zero errors, 73 baseline entries and 495 heuristic warnings.
* Duplicate reporting found six private-only classes, down from eight before this change,
  and no private/public or public/public duplicates.
