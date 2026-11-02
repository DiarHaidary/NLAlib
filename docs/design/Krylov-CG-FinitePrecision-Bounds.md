# Finite-precision CG: iteration dependence and residual decay

Design, 2026-11-02. Continues the Lanczos bounds work in the same checkout. The task is to
propagate the improved dilation estimate into CG and understand how the recursively updated
residual can decrease after the true residual of the computed iterate stagnates.

## Objects and existing material

Use the existing `CGRun`, its normalized Lanczos data, prefix runs, backward matrix, and
`cgKStar`. Keep the arithmetic model and terminal zero-residual convention unchanged.
No new algorithm, rounding semantics, hypothesis structure, or registered program target.

Introduce one numerical API in `CGBackward.lean`:

```lean
noncomputable irreducible_def cgBackwardFactor (k : ℕ) : ℝ :=
  6000 * (k : ℝ) ^ 2 * Real.sqrt k
theorem cgBackwardFactor_nonneg (k : ℕ) : 0 ≤ cgBackwardFactor k
theorem cgBackwardFactor_le (k : ℕ) :
  cgBackwardFactor k ≤ 6000 * (k : ℝ) ^ 2 * Real.sqrt k
```

Register this factor in `docs/constants.toml` and the existing finite-precision bound vocabulary
row in `CONTRIBUTING.md`. It is a scalar bound, not a parallel mathematical object; no Mathlib
bridge is needed. Searches found no CG backward-error theorem in pinned Mathlib. Reuse
`Real.one_le_sqrt`, `Real.sqrt_le_sqrt`, `Real.sqrt_le_self_iff`, and ordinary monotone products
for the scalar comparisons, rather than introduce an unrelated scalar API.

## Derivation and headline statement

The existing run certificates give the uniform local bounds

```
f ≤ 81.6 ε κ a'
p ≤ 245.12 k ε κ a'
```

where `κ = a'/a ≥ 1`. The newly proved normalized backward estimate is
`22 k² f + 17 k √k p`. Hence the model distance is at most

```
(1795.2 k² + 4167.04 k² √k) ε κ a'
  ≤ 6000 k² √k ε κ a',   k ≥ 1.
```

The existing induction supplies the certificates using prefix backward models. Its other
smallness estimates require at most `k² ε κ²`. Replace the old window `k³ ε κ² ≤ 10⁻⁵` by
`k² √k ε κ² ≤ 10⁻⁵`. The model distance is then at most `0.06 a`, which is below the existing
`a/2` margin. Keep that spectral enclosure and its downstream condition number `2κ+1` to
avoid changing independent constants in this task.

```lean
theorem CGRun.frobNorm_backwardH_sub_dilatedH_le {n k : ℕ} (C : CGRun n k)
    {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    frobNorm (C.backwardH - C.dilatedH) ≤ cgBackwardFactor k * C.ε * (a' / a) * a'
```

All existing CGBackward a priori certificate, spectral, recurrence reproduction and energy
comparison theorems take the weaker window. Energy comparison conclusions consume the named
factor. CGAccuracy takes the same weaker window throughout; its existing accuracy constants
and conclusions remain unchanged. No new stronger hypothesis is introduced to prove a smaller
bound. The old cubic hypothesis implies the new one because `√k ≤ k` for `k ≥ 1`.

## Residual question and consumers

Retain the existing arbitrary-δ result, with the weaker window:

```lean
theorem CGRun.ρ_le_of_cgKStar_le {n k : ℕ} (C : CGRun n k)
    {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) {δ : ℝ} (hδ : 0 < δ)
    {j : ℕ} (hkj : cgKStar (a' / a) C.ε δ ≤ j) (hj : j ≤ k) :
    C.ρ j ≤ 8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖
```

The binder order agrees with the implemented declaration. This result already expresses
decay below any prescribed multiple of the error parameter, provided the required iteration
fits the admissible horizon. It does not assert stepwise monotonicity or convergence as the
iteration tends to infinity at fixed precision. The recurrence for residuals and search
directions does not depend on the computed iterate updates; iterate rounding can therefore
produce a gap while the recursive residual keeps decreasing.

The existing `cgKStar_cube_mul_le` remains a stronger sufficient scalar condition, with its
documentation distinguishing it from the new window. Its old conclusion remains true.
The existing over-relaxed bounded-error example rules out unqualified infinite-horizon
convergence in that error model, but does not realize an IEEE round-to-nearest execution.

## Files and validation

* `CGBackward.lean`: named factor and existing induction/conclusions; no duplicate induction.
* `CGAccuracy.lean`: propagate the weaker window and explain arbitrary-δ residual decay.
* Registry and vocabulary: the new numerical factor only.
* This note: derivation, review, final evidence and limits.
* A separate reproducible numerical experiment in `/home/ubuntu/work/cg-residual-experiment`
  compares stored residuals with true residuals evaluated at high precision for the stored
  floating-point matrix, right-hand side and iterate. It is evidence, not a theorem or an
  IEEE realization of `CGRun`.

Builds are serialized in this checkout, with two Lean threads and redirected logs. Run targeted
warning-fatal builds and the mandatory full stage check. Do not change tests, check scripts,
targets, approval files, or baselines. No commit or push is requested for this task.

## Review before implementation

Parent arithmetic/API review: the two contributions sum to `5962.24 k²√k`; rounding to 6000
is valid for `k ≥ 1`. Prefix monotonicity and the lower-power smallness consequences close
using `√k ≥ 1`. The new hypothesis is weaker, and the terminal zero residual remains allowed.
The two implementation agents reviewed their dependency boundaries, and the residual agent
independently reviewed the mathematical interpretation. No unresolved maintainer decision
was needed for this numerical strengthening.

Independent mathematical review, 2026-11-02: **ACCEPT**. The residual agent checked the constants,
prefix monotonicity, lower-power estimates and the `0.06a` model-distance consequence.

## Why the two residuals can separate

The following elementary construction is an independently checked mathematical derivation,
not a Lean theorem or an IEEE round-to-nearest realization. It demonstrates that the separation
is allowed even by the local error model, without an experiment or an assumption of random errors.

Take the scalar system `A=b=1`, `x₀=0`, `r₀=p₀=1`, and `0<ε≤1/2`. Make every residual,
direction, product and dot-product operation exact, but choose the admissible relative division
error `eγ_j = -ε`. Put `c=1-ε`. The resulting recurrences satisfy

```
p_j = (1+jε) r_j,
γ_j = c/(1+jε)²,
r_(j+1) = ((j+1)ε/(1+jε)) r_j.
```

Every residual is positive, and the last ratio is less than one. In fact it is at most
`(j+1)/(j+2)` because `2ε≤1`, so induction gives `r_j≤1/(j+1)` and hence `r_j→0`.
Choose the iterate updates so that `x_j=c` for every `j≥1`: the first update is exact and later
errors are `ex_j=-γ_j p_j`. These errors are admissible. Indeed the intended step
`s_j=c r_j/(1+jε)` decreases, so for `j≥1`,

```
|ex_j| = s_j ≤ s_1 = cε/(1+ε) ≤ ε|x_j| ≤ ε(|x_j|+|γ_j| |p_j|).
```

Thus the true residual `b-Ax_j=ε` is exactly constant after the first iteration, while the
recursive residual tends to zero. All divisions are positive. Under the local restriction
`ε≤1/100`, any finite prefix fits the generalized `CGRun` interface described in
`Krylov-FinitePrecision-Runs.md`; the former `kε≤1/100` interface restriction has been removed.
The infinite sequence is an algebraic example, not a formal limit theorem. This establishes
possibility, not universal convergence for arbitrary allowed local errors.

## Floating-point experiment

The independent experiment uses binary64 Hestenes–Stiefel CG on the exactly representable
diagonal matrix `diag(1²,...,64²)` with `b=(1,...,1)` and `x₀=0`. Its condition number is 4096.
There is no restart, reorthogonalization or residual replacement. Diagnostics use 120-digit
Decimal arithmetic on exact conversions of stored binary64 inputs, never fed back to CG.

The last change in the stored iterate occurs at iteration 150. From then through iteration 700,
the true relative residual is constant at approximately `7.72747422136e-16`. The recursive
relative residual changes from `2.18947161999e-18` at iteration 150 to `6.45620297508e-127`
at iteration 700. There are 211 individual increases over the entire run: the trend is not
stepwise monotonic. The recurrence dot products remain normal throughout the experiment.

Reproduction and raw output are in `/home/ubuntu/work/cg-residual-experiment/`: `experiment.py`,
`residuals.csv`, `states.npz`, `summary.json`, `residuals.svg`, and `residuals.png`.
This high-condition-number run is outside the proved smallness window. It demonstrates the
behavior in an actual finite floating-point execution; it does not validate the error theorem's
hypotheses for that execution or establish an infinite-iteration claim.

The stored iterates from 150 through 700 are bitwise identical. A second diagnostic using exact
rational arithmetic at iterations 0, 1, 75, 100, 150, 300 and 700 agrees with the Decimal true
residual norm to relative error below `1.25e-120`. A strict NumPy floating-point exception run
also completed; the recurrence dot products and their nonzero summands stayed above underflow.
The accompanying `validate.py` and `validation.json` record these checks.

Literature context: [Meurant, chapter 6](https://epubs.siam.org/doi/10.1137/1.9780898718140.ch6)
discusses the residual gap and attainable accuracy. The
[Bake–Carson–Ma preprint, conclusions](https://arxiv.org/html/2510.11379v3#S6) establishes
conditional attainment of small PCG residuals and explains the remaining iteration-dependent
assumptions. These sources do not justify an unrestricted infinite-iteration guarantee for
every floating-point implementation. The elementary construction above is a separate derivation.

## Research question: decay of the computed residual itself

The user's clarification is essential: the residual-gap analysis explains the true-residual
floor conditional on the recursive residual becoming small. A construction or experiment
showing that separation can occur does not supply a general theorem that the recursive residual
does become small. The research target is to bound the iteration needed to reach a prescribed
recursive-residual tolerance from input and arithmetic assumptions, without assuming that
residual decay in the analysis.

[Greenbaum–Liu–Chen, introduction](https://arxiv.org/html/1905.05874v2#S1) explicitly states that
updated residuals may or may not keep decreasing after separating from true residuals; its main
analysis concerns the earlier stage. The latest checked
[Bake–Carson–Ma revision (v3, July 2026), Theorem 2](https://arxiv.org/html/2510.11379v3#S4.SS3)
first establishes an existential index for small auxiliary-energy decrement, then assumes that
index satisfies the iteration-dependent condition (91) to conclude small residuals at some
index no later than it. This is meaningful conditional progress, not a universal prescribed
tolerance iteration bound. The compatibility of the existential index with that condition
must not be silently assumed.

Our Chebyshev theorem supplies an explicit iteration bound in its stated smallness regime.
Improving that regime, and determining what is possible for longer executions under specified
rounding semantics, remains distinct from the residual-gap problem. No claim is made here that
the unrestricted question is settled, or that the literature search proves a novelty claim.

An exploratory route beyond the implemented bound preserves the sign of adjacent defects.
Writing `a_i` for the weighted adjacent inner product gives a transport factor
`q_i = δ_i ρ_i²/ρ_(i+1)²`, with `|q_i-1|≤4ε`. Consecutive differences then have a transported
term `(q_i-1)a_i` of second order, plus local forcing. The existing local estimates suggest a
uniform commutator-diagonal bound, which could reduce the backward estimate to
`4000 k² ε κ a'` and the smallness window to `k² ε κ²≤10⁻⁵`. This is a concrete proposed next
proof, **not a result implemented or certified by the present checks**.

## Retaining the certified model error (2026-11-02)

The fixed smallness hypothesis has two different roles: proving input-only certificates by
prefix induction, and simplifying the resulting model interval. Only the second role is
removed in this amendment. At this stage the run structure still assumed
$k\varepsilon\le 1/100$; the later `Krylov-FinitePrecision-Runs.md` amendment removes that field.

No objects or interfaces are introduced. Use the existing `CGRun`, Mathlib spectral inclusion,
and Frobenius norm. Add the following results in `CGBackward.lean`, with the general spectral
form first and the existing `ρ_le_chebyshev` reproved from it:

```lean
theorem CGRun.ρ_le_chebyshev_of_spectrum_backwardH {l l' : ℝ} (hl : 0 < l)
    (hH : spectrum ℝ C.backwardH ⊆ Set.Icc l l') {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt (l' / l) *
      ((Real.sqrt (l' / l) - 1) / (Real.sqrt (l' / l) + 1)) ^ j *
        ‖WithLp.toLp 2 C.b‖

theorem CGRun.ρ_le_chebyshev_of_frobNorm_le {a a' d : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hd : d < a)
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ d) {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt ((a' + d) / (a - d)) *
      ((Real.sqrt ((a' + d) / (a - d)) - 1) /
        (Real.sqrt ((a' + d) / (a - d)) + 1)) ^ j * ‖WithLp.toLp 2 C.b‖
```

Consumers are a posteriori run certification and future parameterized a priori estimates.
The norm-certificate theorem consumes the already proved
`NormalizedLanczosData.spectrum_backwardH_subset_Icc`; spectral-to-residual transfer consumes
`CGRun.norm_cgState_backwardH_r_of_posDef` and
`Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow`. Mathlib was searched for a CG
residual theorem: none; NLAlib's exact-CG and spectral APIs are reused, not rederived.
There are no new Mathlib deviations, named numerical constants, or files.

The certificate $d$ can come from measured defects with rigorous bounds or from the existing
a posteriori theorem in terms of $\Pi,K,B$. Inserting the current input-only formula for $d$
does not remove its smallness hypothesis: that formula still depends on the prefix induction.
If $d\ge a$, this spectral certificate becomes inconclusive, not a divergence result.

Validation of the two new residual theorems: independent review accepted the general proof,
including the zero-step, singleton-interval and terminal-zero-residual cases. Warning-fatal
builds of `CGBackward` and its consumer `CGAccuracy` passed. The full stage audit completed
with exit 0 on 2026-11-02; log `/tmp/krylov-parameter-stage.log`. The proposed bootstrap and
algebraic examples below are investigation results, not additional Lean theorems.

### Candidate input-only bootstrap with explicit factors

Read-only derivation from the existing inequalities, not yet a formalized theorem. With
$\kappa=a'/a$, positive curvature follows when
$\varepsilon(2+\varepsilon)\kappa<1$, and the curvature certificate can retain
$$K=\frac{\kappa(1+\varepsilon)^2}{1-\varepsilon(2+\varepsilon)\kappa}.$$
Indeed the arithmetic model gives
$\mu_j\ge[a-\varepsilon(2+\varepsilon)a']\|p_j\|^2$ and
$\gamma_j\mu_j\le(1+\varepsilon)^2\rho_j^2$.

Choose $P\ge1$, $B,d\ge0$, and set
$$t=5k\varepsilon(1+P+K),\qquad
\Lambda=(1+3t+4\varepsilon+2\varepsilon^2)(1+4\varepsilon)^2.$$
The existing prefix-induction strategy can retain the scalar conditions
$$t\le1/10,\quad d<a,\quad
P^2\ge\Lambda^k\frac{a'+d}{a-d},\quad
B\ge(1+4\varepsilon)(a'+d),\quad F_k(P,K,B)\le d,$$
where
$$F_k(P,K,B)=22k^2f+17k\sqrt{k}p,$$
$$f=8\varepsilon[a'(1+P)^2+B],\qquad
p=16k\varepsilon[a'(1+P)^2+B(1+P+K)].$$
These are finite scalar feasibility conditions depending only on the input and chosen
certificates; they do not assume measured direction or residual bounds. Prefix certificates
give the prefix model, its spectrum controls residual-ratio sums, and the explicit
$\Lambda^j$ controls directions at the next step. This replaces fixed numeric margins by
conditions that can be checked, but does not guarantee feasibility at arbitrary horizons.
The auxiliary $t\le1/10$ and the linear defect estimates in this candidate bootstrap require
further work to remove. The later `Krylov-FinitePrecision-Runs.md` amendment removes the base
run horizon and provides geometric defect estimates; it does not formalize this bootstrap.

### Why a small backward error does not by itself control CG accuracy

An algebraic example, checked against the run equations but not instantiated in Lean: take
$k=1$, $0<\varepsilon\le.01$, $\lambda=\varepsilon/2$, $A=\operatorname{diag}(\lambda,1)$,
$b=e_1$, and $0<s<\lambda$. Let the only arithmetic error be the matrix-vector error
$e^s_0=(s-\lambda)e_1$. Then the computed product is $se_1$, the curvature is $s>0$,
the step is $1/s$, the computed iterate is $e_1/s$, and the recursive residual is zero.
The error is admissible since $\|e^s_0\|<\varepsilon\|A\|\|p_0\|$; all other operation
errors can vanish, including the terminal residual-norm and direction updates.

The true residual norm is $\lambda/s-1$, unbounded as $s\downarrow0$ at fixed
$k,\varepsilon,\kappa=2/\varepsilon$. Nevertheless exact CG on
$\widetilde A=\operatorname{diag}(s,1)$ reproduces the step with perturbation
$\|A-\widetilde A\|=\lambda-s\le\varepsilon/2$. The critical loss is the inverse margin
$\lambda-(\lambda-s)=s$, not unbounded backward error. This explains why Lanczos backward
estimates and CG forward/true-residual estimates need different assumptions.

## Implementation review and checks

The CG backward and accuracy agents completed the changes within their assigned files.
The warning-fatal builds of `CGBackward` (3023 jobs) and `CGAccuracy` (3025 jobs) passed.
Source rule checks report zero errors; existing heuristic warnings remain. The named-factor
registry check reports 52 constants and zero problems.

The full `LEAN_NUM_THREADS=2 bash scripts/stage_check.sh` audit completed with exit 0 on
2026-11-02; its log is `/tmp/cg-stage-final.log`. It checked 510 proved modules, with zero
build warnings, 15,576 declarations in the axiom/unsafe/partial audit and zero violations,
14 environment linters, fresh generated imports and object files, and successful kernel replay
of 15,806 constants from 515 modules (with the standard 18 compiler auxiliaries excluded).
Program, target, access-model, reference, constant and LaTeX checks passed. The 109-rule audit
reported zero new errors, 73 existing baseline entries and 496 heuristic warnings. The duplicate
report retained eight private-only classes and found no public duplicates. No checks, targets,
approval files, build pins, or baselines were changed. Changes remain uncommitted.
