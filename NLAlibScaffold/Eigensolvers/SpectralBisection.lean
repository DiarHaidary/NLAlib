/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.RandomizedDeflation
public import NLAlibScaffold.Matrix.Computation.SpectralBisection
public import NLAlibScaffold.Probability.AdaptiveUnionBound
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import NLAlib.Computation.BinaryFloat

/-!
# Hermitian diagonalization in linear precision (scaffold)

Statements for a new file `NLAlib/Eigensolvers/SpectralBisection.lean` (stage HDIAG, wave W4,
design note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.9; the folder
`NLAlib/Eigensolvers` is open question OQ1). The main theorem ([Shah2024, Theorem 4.2]):
randomized spectral bisection (`NLAlib.eigh`) on a floating-point machine with black-box
multiplication and QR returns, with
probability at least $1 - \theta$, an approximate diagonalization with residual
$2\varepsilon R_0$ and $\mathbf{U}$ within $\varepsilon/3$ of unitary, using
$\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ bits of
precision. The samples of the nodes are independent, each with the law `NLAlib.eighSampleLaw`
(a uniform seed on $[-1, 1]$ and two independent standard complex Gaussian matrices); the
computed samples are deterministic functions of them with countably many values, which is all the
probability argument needs about the algorithm's measurability.

## Main definitions

* `NLAlib.eighSampleLaw`.

## Main results

* `NLAlib.measureReal_exists_abs_sub_lt_le`: a random shift avoids the spectrum.
* `NLAlib.FloatMachine.IsAccurate.measure_not_isEighGoodSample_le`: the good events of a node.
* `NLAlib.countable_range_eighNodeAt`, `NLAlib.measurableSet_eighNodeAt_eq`,
  `NLAlib.indepFun_eighNodeAt_eq`: the nodes are computed from earlier samples.
* `NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le`: Theorem 4.2.
* `NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le`:
  its bit count.
*
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le`:
  the bounded format, with $\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

namespace NLAlib


/-- The **law of the ideal sample of a node**: a seed uniform on $[-1, 1]$ and two independent
standard complex Gaussian $N \times N$ matrices, independent of the seed. -/
noncomputable def eighSampleLaw (N : ℕ) : Measure (EighSample ℝ ℂ N) :=
  (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).prod
    (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N))

/-- **A random shift avoids a finite set** (Event I): for a finite set $\Lambda$ of reals,
$c > 0$, $w \ge 0$ and $v$ uniform on $[-1, 1]$,
$$\mathbb{P}[\exists \lambda \in \Lambda,\ \lvert \lambda - cv \rvert < w] \le
\frac{\lvert\Lambda\rvert\,w}{c} \,.$$
[Shah2024, proof of Lemma 4.1], there with the density $\ell/(2R)$ of the shift and the bound
$nw/R$, which drops the factor $\ell$; here $c = R/\ell$ gives $nw\ell/R$.
Proof: the event is the union over $\lambda$ of $\{v : \lvert v - \lambda/c \rvert < w/c\}$, each
of uniform measure at most $(2w/c)/2$ (`ProbabilityTheory.cond_apply`,
`Real.volume_Ioo`, `MeasureTheory.measure_mono` to the interval, `Real.volume_Icc`);
`MeasureTheory.measure_biUnion_finset_le`. M, about 25 lines. -/
theorem measureReal_exists_abs_sub_lt_le (Λ : Finset ℝ) {c w : ℝ} (hc : 0 < c) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).real
      {v | ∃ e ∈ Λ, |e - c * v| < w} ≤ Λ.card * w / c := by
  sorry

/-- **Probability of the good events of a node**: under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` on the
node $y$ (contracts, precision, step limit, floor and range) with $2 \le k \le N$ and the machine's
leaf test $R \le \mathrm{fl}(\varepsilon R_0)$ failing, the
sample law `NLAlib.eighSampleLaw` $N$ gives the bad events (`NLAlib.IsEighGoodSample` with $w$,
$x = \sqrt{\rho/2}/k$, $t = \sqrt2(2\sqrt k + \sqrt{2\log(4/\rho)})$ failing) probability at most
$$\frac{kw\ell}{R} + 2\rho\,\mathbb{P}[\text{the node splits}] \,,$$
the node splitting when `NLAlib.eighStep` is `NLAlib.EighStep.split`. [Shah2024, Lemma 4.1],
"Event I occurs with probability at least $1 - wn/R$ and Event II with probability at least
$1 - 2\rho$".
Proof: Event I fails with probability at most $kw\ell/R$
(`NLAlib.measureReal_exists_abs_sub_lt_le` with $\Lambda$ the eigenvalues, $c = R/\ell$; the
first marginal of `NLAlib.eighSampleLaw`; the seed lies in $[-1, 1]$ almost surely). On Event I
the node splits exactly when the true projector has rank strictly between $0$ and $k$
(`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`), and the split depends
on the seed only. Given the seed, the two Gaussian matrices are independent with the complex
Gaussian law (`MeasureTheory.Measure.prod_apply`, `MeasureTheory.Measure.pi_pi`), and for each side
the leading block fails Event II with probability at most $2e^{-\log(4/\rho)} + k^2 \cdot
\rho/(2k^2) = \rho$
(`NLAlib.FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le`'s two tails:
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`,
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`,
`NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix` for the leading block). Fubini over the
seed. L, about 120 lines. -/
theorem FloatMachine.IsAccurate.measure_not_isEighGoodSample_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hk : 2 ≤ y.k) (hkN : y.k ≤ N) (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8)
    (hR₀ : 0 < dec R₀) (hint : M.le y.R (M.mul y.ε R₀) = false) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hudefl : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω) :
    eighSampleLaw N {s | ¬ IsEighGoodSample dec w (√(ρ / 2) / y.k)
      (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y s} ≤
      ENNReal.ofReal (y.k * w * y.ℓ / dec y.R) + ENNReal.ofReal (2 * ρ) *
        eighSampleLaw N {s | (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ s).IsSplit} := by
  sorry

/-- **The nodes take countably many values**: if the computed samples have countably many values
(the uniform sampler at every scale and the normal sampler have countable ranges, as the
floating-point numbers do), then for every root and path the node `NLAlib.eighNodeAt` ranges over
a countable set as the samples vary. No printed source.
The algorithm can reach its ideal samples only through the samplers, since their types are
abstract in `NLAlib.eighStep` (§2.0 of the note).
Proof: induction on the path: the node at `b :: a` is a function of the root, of the computed
shift $\mathrm{unif}(\mathrm{fl}(R/\ell), v)$ (countable range for each stored scale; the
stored scales of the nodes form a countable set because they are computed from the root and
earlier countably-valued samples) and of
the computed leading blocks $(\mathrm{normal}(\mathbf{G}_{i,j}))$ of the root's sample (countably
many for each of countably many sizes; `Set.Countable.image`, `Set.countable_iUnion`,
`Set.Countable.prod`, `Set.countable_setOf_finite_subset`-type lemmas for finite tuples), and of
the node at `a` in the subtree. M, about 50 lines. -/
theorem countable_range_eighNodeAt {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunif : ∀ c, (Set.range (M.unif c)).Countable) (hnormal : (Set.range M.normal).Countable)
    (N signFuel : ℕ) (R₀ β : F) (a : List Bool) (x : EighNode F) :
    (Set.range fun s : List Bool → EighSample ℝ ℂ N =>
      eighNodeAt M N signFuel R₀ β a x s).Countable := by
  sorry

/-- **The node at a path is an event of the earlier samples**: if the samplers have measurable
fibres and countable ranges and each sample $\zeta_b$ is measurable, then for every root $x$, path
$a$ and possible node $y$, the set of outcomes at which the node at $a$ is $y$ is measurable. No
printed source.
Proof: the node at $a$ is a function of the computed samples at the proper prefixes of $a$, a
finite tuple of measurable maps into countable sets
(`NLAlib.countable_range_eighNodeAt`'s decomposition); its fibre at $y$ is a countable union of
fibres of that tuple (`MeasurableSet.iUnion`, `measurableSet_eq_fun`-type lemmas,
`Measurable.comp`). L, about 60 lines. -/
theorem measurableSet_eighNodeAt_eq {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunif : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormal : (Set.range M.normal).Countable)
    {N signFuel : ℕ} {R₀ β : F} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {ζ : List Bool → Ω' → EighSample ℝ ℂ N} (hζ : ∀ b, Measurable (ζ b)) (a : List Bool)
    (x : EighNode F) (y : Option (EighNode F)) :
    MeasurableSet {ω | eighNodeAt M N signFuel R₀ β a x (fun b => ζ b ω) = y} := by
  sorry

/-- **The node at a path is independent of its own sample**: under the hypotheses of
`NLAlib.measurableSet_eighNodeAt_eq` and independence of the samples
($(\zeta_b)_b$ mutually independent), the event that the node at the path $a$ is $y$ is
independent of $\zeta_a$. No printed source; [Shah2024, proof of Theorem 4.2] uses it implicitly
("Event I ... $c'$ is sampled from a density bounded by $\ell/2R$").
Proof: the event is measurable with respect to $\sigma(\zeta_b : b \text{ a proper prefix of }
a)$ (the decomposition of `NLAlib.measurableSet_eighNodeAt_eq`, with each computed sample a
function of one $\zeta_b$), and $a$ is not a proper prefix of itself;
`ProbabilityTheory.iIndepFun.indepFun_finset` (disjoint finite index sets $\{a\}$ and the proper
prefixes) and `ProbabilityTheory.IndepFun.comp`. H, about 90 lines (the decomposition through the
prefixes, shared with `NLAlib.measurableSet_eighNodeAt_eq`, is the work). -/
theorem indepFun_eighNodeAt_eq {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunif : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormal : (Set.range M.normal).Countable)
    {N signFuel : ℕ} {R₀ β : F} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {ζ : List Bool → Ω' → EighSample ℝ ℂ N} (hζ : ∀ b, Measurable (ζ b)) (hind : iIndepFun ζ μ)
    (a : List Bool) (x : EighNode F) (y : Option (EighNode F)) :
    IndepFun (fun ω => eighNodeAt M N signFuel R₀ β a x (fun b => ζ b ω) = y) (ζ a) μ := by
  sorry

/-- **Hermitian diagonalization in linear precision** (Theorem 4.2): let the machine meet
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ (constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$, $c_{\mathrm N}$), with $\mu_{\mathrm{MM}}, \mu_{\mathrm{QR}}$ monotone
and nonnegative, $c_{\mathrm N} \ge 0$, and the samplers with measurable fibres and countable
ranges. Let the stored $\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, for
stored $R_0 > 0$, $\varepsilon$, $\beta$ (decoded values) with $0 < \varepsilon \le 2^{-15}$, $0 <
\theta \le 1$, a depth counter $\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$, and the
precomputed accuracy $$0 < \beta \le \frac{\varepsilon\sqrt\theta}{2880\,\ell\, n^{3/2}\bigl(2\sqrt
n + \sqrt{2\log(16n/\theta)}\bigr)} \,, \qquad
N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac{\beta}{16n}\Bigr) \,.$$
If $640\,n^{3/2}(8 + \mu_{\mathrm{MM}}(n))(N_* + 1)\cdot16n(n+1)\ell(\ell+1)\,u \le
\theta\beta$, $(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u
\le \beta$, the sign step limit is at least $N_*$, $0 \le \tau$,
$4n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon R_0/3)$,
$16(R_0 + n + \ell + \sqrt{\log(16n/\theta)}) \le \Omega$, and the node samples $\zeta_a$ are
independent, each of law `NLAlib.eighSampleLaw` $n$, then
$$\mathbb{P}\bigl[\mathsf{eigh}(\mathbf{A}, \varepsilon, \theta) \text{ is not an approximate
diagonalization with residual } 2\varepsilon R_0 \text{ and } \mathbf{U} \text{ within }
\varepsilon/3 \text{ of unitary}\bigr] \le \theta \,,$$
$\mathsf{eigh}$ the decoded output of `NLAlib.eigh`. [Shah2024, Theorem 4.2], there with
$R_0 = \|\mathbf{A}\|_2$, node-dependent accuracies, the bit count of
`NLAlib.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le` with other constants, and an
operation count (not formalized).
Proof: the bad event is contained in "some internal node of the tree has a bad sample"
(contrapositive of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`). Apply
`NLAlib.measureReal_exists_mem_le_of_forall_measure_le_lintegral` with index the paths, state $X_a$
the node at $a$ (`NLAlib.countable_range_eighNodeAt`, `NLAlib.measurableSet_eighNodeAt_eq`,
`NLAlib.indepFun_eighNodeAt_eq`), bad set the complement of `NLAlib.IsEighGoodSample` at internal
nodes (empty elsewhere) and charge $k w \ell/R + 2\rho\,[\text{split}]$ = $\theta/(2(n+1)(\ell+1))
+ (\theta/(2n))[\text{split}]$ (`NLAlib.FloatMachine.IsAccurate.measure_not_isEighGoodSample_le`);
the charges sum to at most $\theta/2 + \theta/2$ by
`NLAlib.FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le` and
`NLAlib.encard_eighNodeAt_isSplit_le`. The node hypotheses come from the global ones as in the
proof of `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`
(factor out that parameter lemma). L, about 120 lines. -/
theorem FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (4 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * dec R₀ / 3))
    (hΩ : 16 * (dec R₀ + n + ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  sorry

/-- **The bit count of Hermitian diagonalization** (Theorem 4.2, in bits): under the hypotheses
of `NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le` with the two
precision conditions replaced by $u > 0$, the accuracy within a factor $2$ of its bound,
$\beta_* /2 \le \beta \le \beta_*$ ($\beta_*$ the right side of that bound), and
$$\begin{aligned}\log_2\frac1u \ge{}& \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta +
\log_2\Bigl(n^4(n + 1)(8 + \mu_{\mathrm{MM}}(n)) + n^{3/2}\bigl(4\mu_{\mathrm{QR}}(n) +
4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1\bigr)\Bigr) \\
&+ \log_2(N_* + 1) + 3\log_2(\ell + 1) +
\log_2\bigl(2\sqrt n + \sqrt{2\log(16n/\theta)}\bigr) + 26 \,,\end{aligned}$$
the failure probability is at most $\theta$. Since $\ell = O(\log(1/\varepsilon))$ and
$N_* = O(\log(n\ell/\theta) + \log\log(n/(\varepsilon\theta)))$, this is
$\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ bits.
[Shah2024, Theorem 4.2], there $\log_2(1/\varepsilon) + \log_2\max(n^{1.5}\mu_{\mathrm{QR}},
n^{1.5}\sqrt n c_{\mathrm N}, n^{4.5}\mu_{\mathrm{MM}}) + 2\log_2\log_2(1/\varepsilon) +
1.5\log_2(1/\theta) + \log_2\log_2(n\log_2(1/\varepsilon)/\theta) + 23$; the exponent of $n$ and
the third power of $\ell$ (from the corrected shift-avoidance probability) differ.
Proof: exponentiate (`Real.logb_le_logb`, `Real.rpow_logb`, `Real.logb_mul`, `Real.logb_rpow`)
to get both precision conditions of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le` for $n \ge 1$ (at
$n = 0$ the condition on $\beta = 0$ is unreachable, so handle $n = 0$ directly: the empty matrices
are an approximate diagonalization and the event is empty) ($2 \cdot 640 \cdot 16 \cdot 2880 \le
2^{26}$, the factor $2$ from $\beta \ge \beta_*/2$, $\ell^2(\ell + 1) \le (\ell + 1)^3$,
$\log_2(N_* + 1) \ge 0$), and apply it. M, about 50 lines. -/
theorem FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))))
    (hβge : dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) / 2 ≤ dec β)
    {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hu : 0 < u)
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n ^ 4 * (n + 1) * (8 + μM n) +
        n * √(n : ℝ) * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) +
      Real.logb 2 (Nst + 1) + 3 * Real.logb 2 (ℓ + 1) +
      Real.logb 2 (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) + 26 ≤ Real.logb 2 u⁻¹)
    {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (4 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * dec R₀ / 3))
    (hΩ : 16 * (dec R₀ + n + ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  sorry

/-- **Hermitian diagonalization in a bounded binary format: $\log_2\log_2(n/(\varepsilon\theta)) +
O(1)$ exponent bits suffice** (Theorem 4.2 for a finite exponent range): let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u = 2^{-p}$, floor $2^{e_{\min} + p - 1}$ (the smallest
normal number) and range the largest finite number of a binary format with $E \ge 2$ exponent
bits, precision $p$ and smallest exponent $e_{\min}$ (as
`NLAlib.exists_floatMachine_isAccurate_binaryFloatRound` provides), with the other hypotheses of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le`, the
input scaled so that $1/2 \le R_0 \le 1$ (an exact power-of-two scaling), the precision condition
there with $\log_2(1/u) = p$, and
$$\log_2\Bigl(\log_2\frac{1536\,(n + \ell + 2)^2}{\varepsilon\theta} + 2\Bigr) + 1 \le E \,.$$
Then the failure probability is at most $\theta$. With $\ell = O(\log(1/\varepsilon))$ this is
$\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits, the claim of [Shah2024, Section 1.2]
("$\lg\lg(n/\varepsilon) + O(1)$ bits to store the exponent"), with the $\theta$ it omits.
Proof: for a binary format, $e_{\min} + p - 1 = 2 - 2^{E - 1}$ and the largest finite number is
at least $2^{2^{E-1} - 1}$ (`Float.Model.Format.minExponent_eq`, the bias $2^{E-1} - 1$,
`Float.Model.Format.maxFinite`); the exponent condition gives $2^{E-1} \ge \log_2 L + 2$ for the
displayed $L$, hence floor $\le 1/L \le \varepsilon\theta/(24n^2)$, which implies the floor
hypothesis $4n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon R_0/3)$, and range
$\ge 2L \ge 16(R_0 + n + \ell + \sqrt{\log(16n/\theta)})$; then apply
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le`. M,
about 70 lines. -/
theorem FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} (fmt : Float.Model.Format)
    (hE : 2 ≤ fmt.exponentBits) {cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀)
    (hR₀half : 1 / 2 ≤ dec R₀) (hR₀one : dec R₀ ≤ 1) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))))
    (hβge : dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) / 2 ≤ dec β)
    {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n ^ 4 * (n + 1) * (8 + μM n) +
        n * √(n : ℝ) * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) +
      Real.logb 2 (Nst + 1) + 3 * Real.logb 2 (ℓ + 1) +
      Real.logb 2 (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) + 26 ≤ fmt.mantissaBits)
    (hexp : Real.logb 2 (Real.logb 2 (1536 * (n + ℓ + 2) ^ 2 / (dec ε * θ)) + 2) + 1 ≤
      fmt.exponentBits)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n} (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  sorry

end NLAlib
