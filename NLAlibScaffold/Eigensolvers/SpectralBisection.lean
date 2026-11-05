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

/-!
# Hermitian diagonalization in linear precision (scaffold)

Statements for a new file `NLAlib/Eigensolvers/SpectralBisection.lean` (stage HDIAG, wave W4,
design note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.9; the folder
`NLAlib/Eigensolvers` is open question OQ1). The main theorem ([Shah2024, Theorem 4.2]):
randomized spectral bisection (`NLAlib.eigh`) with black-box multiplication and QR returns, with
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
* `NLAlib.measure_not_isEighGoodSample_le`: the good events of a node.
* `NLAlib.countable_range_eighNodeAt`, `NLAlib.measurableSet_eighNodeAt_eq`,
  `NLAlib.indepFun_eighNodeAt_eq`: the nodes are computed from earlier samples.
* `NLAlib.measureReal_not_isApproxDiagonalization_eigh_le`: Theorem 4.2.
* `NLAlib.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le`: its bit count.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

namespace NLAlib

/-- The **law of the ideal sample of a node**: a seed uniform on $[-1, 1]$ and two independent
standard complex Gaussian $N \times N$ matrices, independent of the seed. -/
noncomputable def eighSampleLaw (N : ℕ) : Measure (EighSample N) :=
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
`MeasureTheory.measure_biUnion_finset_le`. S, about 25 lines. -/
theorem measureReal_exists_abs_sub_lt_le (Λ : Finset ℝ) {c w : ℝ} (hc : 0 < c) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).real
      {v | ∃ e ∈ Λ, |e - c * v| < w} ≤ Λ.card * w / c := by
  sorry

/-- **Probability of the good events of a node**: under the hypotheses of
`NLAlib.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` on the node $y$ (contracts,
precision, step limit, floor and range) with $2 \le k \le N$ and $R > \varepsilon R_0$, the
sample law `NLAlib.eighSampleLaw` $N$ gives the bad events (`NLAlib.IsEighGoodSample` with $w$,
$x = \sqrt{\rho/2}/k$, $t = \sqrt2(2\sqrt k + \sqrt{2\log(4/\rho)})$ failing) probability at most
$$\frac{kw\ell}{R} + 2\rho\,\mathbb{P}[\text{the node splits}] \,,$$
the node splitting when `NLAlib.eighStep` is `NLAlib.EighStep.split`. [Shah2024, Lemma 4.1],
"Event I occurs with probability at least $1 - wn/R$ and Event II with probability at least
$1 - 2\rho$".
Proof: Event I fails with probability at most $kw\ell/R$
(`NLAlib.measureReal_exists_abs_sub_lt_le` with $\Lambda$ the eigenvalues, $c = R/\ell$; the
first marginal of `NLAlib.eighSampleLaw`). On Event I the node splits exactly when the true
projector has rank strictly between $0$ and $k$ (the rank recovery inside the proof of
`NLAlib.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`; factor it out as a private
lemma). Given the seed, the two Gaussian matrices are independent with the complex Gaussian law
(`MeasureTheory.Measure.prod_apply`, `MeasureTheory.Measure.pi_pi`), and for each side the
leading block fails Event II with probability at most $2e^{-\log(4/\rho)} + k^2 \cdot
\rho/(2k^2) = \rho$
(`NLAlib.IsMatMulErr.measureReal_not_exists_specNorm_mul_sub_deflate_le_le`'s two tails:
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`,
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`,
`NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix` for the leading block). Fubini over the
seed. L, about 120 lines. -/
theorem measure_not_isEighGoodSample_le {P : EighPrimitives} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hmm : IsMatMulErr u τ Ω μM P.mm) (hqr : IsQRErr u τ Ω μQ P.qr)
    (hfl : IsRoundingFn u τ Ω P.fl) (hunif : IsUnifSampler u P.unif)
    (hnormal : IsNormalSampler u cN P.normal) {N signFuel : ℕ} {R₀ ρ w : ℝ} {y : EighNode}
    (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hA : y.A.IsHermitian)
    (hR : specNorm y.A ≤ y.R) (hk : 2 ≤ y.k) (hkN : y.k ≤ N) (hℓ : 20 ≤ y.ℓ) (hε : 0 < y.ε)
    (hε₁ : y.ε ≤ 1 / 8) (hR₀ : 0 ≤ R₀) (hRε : y.ε * R₀ < y.R) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hw : 0 < w) (hwR : w ≤ y.R)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * y.R)) (bisectionSignTol y.k y.ε ρ y.ℓ / (16 * y.k)) + 1) * u ≤
        w / (4 * y.R) * bisectionSignTol y.k y.ε ρ y.ℓ)
    (hudefl : (4 * μQ y.k + 2 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤
      bisectionSignTol y.k y.ε ρ y.ℓ)
    (hfuel : newtonSchulzSteps (w / (8 * y.R)) (bisectionSignTol y.k y.ε ρ y.ℓ / (16 * y.k)) ≤
      signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k) ≤ min (√(ρ / 2)) (y.ε * R₀))
    (hΩ : 16 * (y.R + y.k + √(Real.log (4 / ρ))) ≤ Ω) :
    eighSampleLaw N {s | ¬ IsEighGoodSample w (√(ρ / 2) / y.k)
      (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y s} ≤
      ENNReal.ofReal (y.k * w * y.ℓ / y.R) + ENNReal.ofReal (2 * ρ) *
        eighSampleLaw N {s | (eighStep P N signFuel R₀ ρ y.A y.R y.ε y.ℓ s).IsSplit} := by
  sorry

/-- **The nodes take countably many values**: if the computed samples have countably many values
(the uniform sampler at every scale and the normal sampler have countable ranges, as the
floating-point numbers do), then for every root and path the node `NLAlib.eighNodeAt` ranges over
a countable set as the samples vary. No printed source.
Proof: induction on the path: the node at `b :: a` is a function of the root, of the computed
shift $\mathrm{unif}(R/\ell, v)$ (countable range, the scale depending only on the depth) and of
the computed leading blocks $(\mathrm{normal}(\mathbf{G}_{i,j}))$ of the root's sample (countably
many for each of countably many sizes; `Set.Countable.image`, `Set.countable_iUnion`,
`Set.Countable.prod`, `Set.countable_setOf_finite_subset`-type lemmas for finite tuples), and of
the node at `a` in the subtree. M, about 50 lines. -/
theorem countable_range_eighNodeAt {P : EighPrimitives}
    (hunif : ∀ s, (Set.range (P.unif s)).Countable) (hnormal : (Set.range P.normal).Countable)
    (N signFuel : ℕ) (R₀ ρ : ℝ) (a : List Bool) (x : EighNode) :
    (Set.range fun s : List Bool → EighSample N => eighNodeAt P N signFuel R₀ ρ a x s).Countable :=
  by
  sorry

/-- **The node at a path is an event of the earlier samples**: if the samplers are measurable
with countable ranges and each sample $\zeta_b$ is measurable, then for every root $x$, path $a$
and possible node $y$, the set of outcomes at which the node at $a$ is $y$ is measurable. No
printed source.
Proof: the node at $a$ is a function of the computed samples at the proper prefixes of $a$, a
finite tuple of measurable maps into countable sets
(`NLAlib.countable_range_eighNodeAt`'s decomposition); its fibre at $y$ is a countable union of
fibres of that tuple (`MeasurableSet.iUnion`, `measurableSet_eq_fun`-type lemmas,
`Measurable.comp`). M, about 60 lines. -/
theorem measurableSet_eighNodeAt_eq {P : EighPrimitives} (hunifm : ∀ s, Measurable (P.unif s))
    (hunif : ∀ s, (Set.range (P.unif s)).Countable) (hnormalm : Measurable P.normal)
    (hnormal : (Set.range P.normal).Countable) {N signFuel : ℕ} {R₀ ρ : ℝ} {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {ζ : List Bool → Ω' → EighSample N} (hζ : ∀ b, Measurable (ζ b))
    (a : List Bool) (x : EighNode) (y : Option EighNode) :
    MeasurableSet {ω | eighNodeAt P N signFuel R₀ ρ a x (fun b => ζ b ω) = y} := by
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
theorem indepFun_eighNodeAt_eq {P : EighPrimitives} (hunifm : ∀ s, Measurable (P.unif s))
    (hunif : ∀ s, (Set.range (P.unif s)).Countable) (hnormalm : Measurable P.normal)
    (hnormal : (Set.range P.normal).Countable) {N signFuel : ℕ} {R₀ ρ : ℝ} {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample N}
    (hζ : ∀ b, Measurable (ζ b)) (hind : iIndepFun ζ μ) (a : List Bool) (x : EighNode)
    (y : Option EighNode) :
    IndepFun (fun ω => eighNodeAt P N signFuel R₀ ρ a x (fun b => ζ b ω) = y) (ζ a) μ := by
  sorry

/-- **Hermitian diagonalization in linear precision** (Theorem 4.2): let the primitives meet
`NLAlib.IsMatMulErr` $u$ $\tau$ $\Omega$ $\mu_{\mathrm{MM}}$, `NLAlib.IsQRErr` $u$ $\tau$ $\Omega$
$\mu_{\mathrm{QR}}$, `NLAlib.IsRoundingFn` $u$ $\tau$ $\Omega$, `NLAlib.IsUnifSampler` $u$ and
`NLAlib.IsNormalSampler` $u$ $c_{\mathrm N}$, with $\mu_{\mathrm{MM}}, \mu_{\mathrm{QR}}$ monotone
and nonnegative, $c_{\mathrm N} \ge 0$, and the samplers measurable with countable ranges. Let
$\mathbf{A} \in \mathbb{C}^{n \times n}$ be Hermitian with $\|\mathbf{A}\|_2 \le R_0$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $\ell$ = `NLAlib.bisectionDepth`
$\varepsilon$, and
$$\beta = \frac{\varepsilon\sqrt\theta}{2880\,\ell\, n^{3/2}\bigl(2\sqrt n +
\sqrt{2\log(16n/\theta)}\bigr)} \,, \qquad
N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac{\beta}{16n}\Bigr) \,.$$
If $640\,n^{3/2}(8 + \mu_{\mathrm{MM}}(n))(N_* + 1)\cdot16n(n+1)\ell(\ell+1)\,u \le
\theta\beta$, $(4\mu_{\mathrm{QR}}(n) + 2\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u
\le \beta$, the sign step limit is at least $N_*$, $0 \le \tau$,
$4n\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon R_0/3)$,
$16(R_0 + n + \sqrt{\log(16n/\theta)}) \le \Omega$, and the node samples $\zeta_a$ are
independent, each of law `NLAlib.eighSampleLaw` $n$, then
$$\mathbb{P}\bigl[\mathsf{eigh}(\mathbf{A}, \varepsilon, \theta) \text{ is not an approximate
diagonalization with residual } 2\varepsilon R_0 \text{ and } \mathbf{U} \text{ within }
\varepsilon/3 \text{ of unitary}\bigr] \le \theta \,,$$
$\mathsf{eigh}$ the algorithm `NLAlib.eigh`. [Shah2024, Theorem 4.2], there with
$R_0 = \|\mathbf{A}\|_2$, the bit count of
`NLAlib.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le` with other constants, and an
operation count (not formalized).
Proof: the bad event is contained in "some internal node of the tree has a bad sample"
(contrapositive of `NLAlib.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`). Apply
`NLAlib.measureReal_exists_mem_le_of_forall_measure_le_lintegral` with index the paths, state
$X_a$ the node at $a$ (`NLAlib.countable_range_eighNodeAt`,
`NLAlib.measurableSet_eighNodeAt_eq`, `NLAlib.indepFun_eighNodeAt_eq`), bad set the complement of
`NLAlib.IsEighGoodSample` at internal nodes (empty elsewhere) and charge
$k w \ell/R + 2\rho\,[\text{split}]$ = $\theta/(2(n+1)(\ell+1)) + (\theta/(2n))[\text{split}]$
(`NLAlib.measure_not_isEighGoodSample_le`); the charges sum to at most $\theta/2 + \theta/2$ by
`NLAlib.encard_eighNodeAt_ne_none_le` and `NLAlib.encard_eighNodeAt_isSplit_le`. The node
hypotheses come from the global ones as in the proof of
`NLAlib.isApproxDiagonalization_eigh_of_forall_isEighGoodSample` (factor out that parameter
lemma). L, about 120 lines. -/
theorem measureReal_not_isApproxDiagonalization_eigh_le {P : EighPrimitives} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hmm : IsMatMulErr u τ Ω μM P.mm) (hqr : IsQRErr u τ Ω μQ P.qr)
    (hfl : IsRoundingFn u τ Ω P.fl) (hunif : IsUnifSampler u P.unif)
    (hnormal : IsNormalSampler u cN P.normal) (hunifm : ∀ s, Measurable (P.unif s))
    (hunifc : ∀ s, (Set.range (P.unif s)).Countable) (hnormalm : Measurable P.normal)
    (hnormalc : (Set.range P.normal).Countable) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) {R₀ ε θ : ℝ} (hR₀ : specNorm A ≤ R₀) (hε : 0 < ε)
    (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : ℓ = bisectionDepth ε) {β : ℝ}
    (hβ : β = ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * β)
    (hudefl : (4 * μQ n + 2 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (4 * n) ≤ min (√(θ / (8 * n))) (ε * R₀ / 3))
    (hΩ : 16 * (R₀ + n + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample n} (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization A (eigh P signFuel A R₀ ε θ fun a => ζ a ω).1
      (eigh P signFuel A R₀ ε θ fun a => ζ a ω).2 (2 * ε * R₀) (ε / 3)} ≤ θ := by
  sorry

/-- **The bit count of Hermitian diagonalization** (Theorem 4.2, in bits): under the hypotheses
of `NLAlib.measureReal_not_isApproxDiagonalization_eigh_le` with the two precision conditions
replaced by $u > 0$ and
$$\begin{aligned}\log_2\frac1u \ge{}& \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta +
\log_2\Bigl(n^4(n + 1)(8 + \mu_{\mathrm{MM}}(n)) + n^{3/2}\bigl(4\mu_{\mathrm{QR}}(n) +
2\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1\bigr)\Bigr) \\
&+ \log_2(N_* + 1) + 3\log_2(\ell + 1) +
\log_2\bigl(2\sqrt n + \sqrt{2\log(16n/\theta)}\bigr) + 25 \,,\end{aligned}$$
the failure probability is at most $\theta$. Since $\ell = O(\log(1/\varepsilon))$ and
$N_* = O(\log(n\ell/\theta) + \log\log(n/(\varepsilon\theta)))$, this is
$\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ bits.
[Shah2024, Theorem 4.2], there $\log_2(1/\varepsilon) + \log_2\max(n^{1.5}\mu_{\mathrm{QR}},
n^{1.5}\sqrt n c_{\mathrm N}, n^{4.5}\mu_{\mathrm{MM}}) + 2\log_2\log_2(1/\varepsilon) +
1.5\log_2(1/\theta) + \log_2\log_2(n\log_2(1/\varepsilon)/\theta) + 23$; the exponent of $n$ and
the third power of $\ell$ (from the corrected shift-avoidance probability) differ.
Proof: exponentiate (`Real.logb_le_logb`, `Real.rpow_logb`, `Real.logb_mul`, `Real.logb_rpow`)
to get both precision conditions of
`NLAlib.measureReal_not_isApproxDiagonalization_eigh_le` ($640 \cdot 16 \cdot 2880 \le 2^{25}$,
$\ell^2(\ell + 1) \le (\ell + 1)^3$, $\log_2(N_* + 1) \ge 0$), and apply it. M, about 50
lines. -/
theorem measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le {P : EighPrimitives}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hmm : IsMatMulErr u τ Ω μM P.mm)
    (hqr : IsQRErr u τ Ω μQ P.qr) (hfl : IsRoundingFn u τ Ω P.fl)
    (hunif : IsUnifSampler u P.unif) (hnormal : IsNormalSampler u cN P.normal)
    (hunifm : ∀ s, Measurable (P.unif s)) (hunifc : ∀ s, (Set.range (P.unif s)).Countable)
    (hnormalm : Measurable P.normal) (hnormalc : (Set.range P.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {R₀ ε θ : ℝ}
    (hR₀ : specNorm A ≤ R₀) (hε : 0 < ε) (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1)
    {ℓ : ℕ} (hℓ : ℓ = bisectionDepth ε) {β : ℝ}
    (hβ : β = ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (β / (16 * n)))
    (hu : 0 < u)
    (hbits : Real.logb 2 ε⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n ^ 4 * (n + 1) * (8 + μM n) +
        n * √(n : ℝ) * (4 * μQ n + 2 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) +
      Real.logb 2 (Nst + 1) + 3 * Real.logb 2 (ℓ + 1) +
      Real.logb 2 (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) + 25 ≤ Real.logb 2 u⁻¹)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (4 * n) ≤ min (√(θ / (8 * n))) (ε * R₀ / 3))
    (hΩ : 16 * (R₀ + n + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample n} (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization A (eigh P signFuel A R₀ ε θ fun a => ζ a ω).1
      (eigh P signFuel A R₀ ε θ fun a => ζ a ω).2 (2 * ε * R₀) (ε / 3)} ≤ θ := by
  sorry

end NLAlib
