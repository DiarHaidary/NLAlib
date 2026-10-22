# Design note: JL moments at high order, the SRHT's JL and multiplication properties, Haar sample sizes, and matrix Bernstein without replacement

**Approved by the maintainer, 2026-10-22:** MD2 to MD4 as recommended, full scope (§8 Q8 default).

Draft of 2026-10-21 for `docs/design/Sketching-Moments.md`. Worktree `nlalib-block`, branch
`cleanup/consolidation`, read only. Nothing here was elaborated: the signatures are written against
the current source (read in full where cited) and are checked at the skeleton. Locators are given
only where this note's author saw them in the library's docstrings, design notes or
`docs/PORT_SKETCHING.md` §7.1; every other one says "locator to check".

The round has four parts, in dependency order:

* **M1. JL moments beyond $p = 2$** (§2): a tail-to-moment lemma, the high-order JL moment of every
  family with an exponential JL tail, and the consumers that move from $1/\delta$ to
  $\log(1/\delta)$.
* **M2. The SRHT as a JL sketch** (§3): "an OSE for dimension 1 has the JL property", the SRHT JL
  tail and size, and a direct second JL moment of the SRHT, which gives it approximate
  multiplication (AMM), projection-cost preservation (PCP), relative-error sketch-and-solve and the
  $(1+\varepsilon)$ randomized SVD.
* **M3. Haar $1 \mp \varepsilon$ sample sizes** (§4) by JL plus a net, and the three deferred Haar
  corollaries.
* **M4. Matrix Bernstein and the Chernoff means without replacement** (§5), the spectral AMM tails
  for row sampling and the SRHT, and the list of downstream items they make reachable.

---

## Decisions for the maintainer

Only the decisions that many later statements would inherit. Everything else is in §8 with a
recommendation and proceeds as recommended unless corrected.

*Confirmation, not a decision:* `HasJLMoment` (`JohnsonLindenstrauss.lean:92`) is already Kane and
Nelson's property at every real $p$, and every consumer already takes a general `p` (§1); the
round adds instances and changes no interface.

**MD2. How the improved failure probability is written: a named bound whose body is the Gamma
form, with the readable bound as API.**
The layer-cake integral of the tail $2e^{-\min(t^2/(2v),\,t/(2b))}$ against $p t^{p-1}$ is
$$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^p\Gamma(p)\,,$$
valid for every $p > 0$. For $p \ge 2$, $\Gamma(x) \le x^{x-1}$ ($x \ge 1$) bounds it by the
readable $2(vp)^{p/2} + 2(2bp)^p$, the literature's shape
($\|\cdot\|_{L^p} \lesssim \sqrt{vp} + bp$). That step loses a factor **exponential in $p$**
(about $e^{p/2}/\sqrt{\pi p}$ on the first term and $e^p/\sqrt{2\pi p}$ on the second, by Stirling),
which in the size inversion is a constant factor of about $e$ in `jlMomentDim` (the $128$ of §2.4;
the reviewer estimates about $47$ through Stirling, not checked here). So B6 does not license the
readable form as the statement; §5.2 rule 2 (a named bound with an improvable body) does.
Options: (a) `noncomputable irreducible_def subexponentialMomentBound (v b p : ℝ) : ℝ :=
p * (2 * v) ^ (p / 2) * Real.Gamma (p / 2) + 2 * p * (2 * b) ^ p * Real.Gamma p`, for every
$p > 0$, registered in `docs/constants.toml`, with API `subexponentialMomentBound_nonneg`,
`subexponentialMomentBound_mono` and the readable comparison
`subexponentialMomentBound_le : 2 ≤ p → subexponentialMomentBound v b p ≤ 2 * (v * p) ^ (p / 2) + 2 * (2 * b * p) ^ p`,
through which every size form inverts; the precedent is `HasSubgaussianMGF.integral_abs_rpow_le`
(`SubGaussian/Moments.lean:64`), which states the Gamma form; (b) the readable formula as the body,
$p \ge 2$ only; (c) either formula inline. Recommendation (a): the statements carry the exact
layer-cake value, the readable bound is one API lemma, and a Stirling-sharp inversion later lowers
`jlMomentDim`'s constant by editing its body and its comparison lemma, with no statement change.
Rework if changed: about eight statements and the size inversions.

**MD3. The exponent in the size forms: $p = \max(2, \log(1/\delta))$, written out.**
The family size corollaries conclude `HasJLMoment S ε δ (max 2 (Real.log (1 / δ))) μ` once
$\lvert k\rvert \ge$ `jlMomentDim ε δ` (Gaussian, Haar) or `subgaussianJLMomentDim c ε δ`. The proof
shows the moment bound is at most $\varepsilon^p e^{-p} \le \varepsilon^p\delta$. Options: (a) the
explicit `max 2 (Real.log (1 / δ))`; (b) `∃ p, 2 ≤ p ∧ HasJLMoment S ε δ p μ` (consumers
`obtain` it; hides $p$, but a hidden exponent is never needed downstream); (c) a free `p ≥ 2` with
$\delta = e^{-p}$ in the conclusion and the size in $p$. Recommendation (a): the consumer
discharges `2 ≤ p` with `le_max_left`, a reader sees Kane and Nelson's $p = \log(1/\delta)$, and no
existential appears in a conclusion. (c) moves the inversion to every consumer, against §5.2's
"inverting the tail is done once". Rework if changed: the size corollaries (five) and their
asymptotic forms.

**MD4. The existing $1/\delta$ family consumers: keep the explicit forms, add $\log(1/\delta)$
explicit forms, upgrade the asymptotic forms in place.**
Six explicit family statements reach their failure probability through a `p = 2` JL moment
(§2.6): Gaussian and sub-Gaussian PCP, Gaussian sketch-and-solve, Gaussian early truncation,
sub-Gaussian relative-error randomized SVD and early truncation. With M1 each gets a twin whose
second size is `jlMomentDim` at the budget the proof uses (product form
$(d+1)\log(1/\delta)/\varepsilon^2$ in place of $(d+1)/(\varepsilon^2\delta)$). The explicit twins
are incomparable with the old ones (the old constant $16$ to $384$ beats the new $128\cdot\max(2,
\log)$ for $\delta$ above roughly $10^{-2}$), so rule 4 keeps both. The asymptotic forms are
dominated in the $O(\cdot)$ sense ($\log(1/\delta) \le 1/\delta$ for $\delta \le 1/2$). Options:
(a) keep each `exists_forall_` name and change its threshold to the $\log(1/\delta)$ one, proved
from the new explicit form, recorded in `docs/renames/2026-10-sketching-moments.json` under
`statementChanged` (the explorer's Rates rows update); (b) keep the old asymptotic forms and add new
`exists_forall_` names (two asymptotic forms of one result, which N17's derivation cannot name
apart); (c) deprecate the old ones. Recommendation (a), as `docs/design/LowRank-S9.md` Q3 already
anticipated ("the current asymptotic form is reproved from it or deprecated by rule 6, and the
explicit `_of_le_card` forms keep their names"). Rework if changed: six asymptotic forms, the Rates
overlay.

---

## 1. What exists, verified against the code

| Claim of the gap surveys | Verdict |
|---|---|
| Every JL moment instance is at $p = 2$, so every AMM-based bound pays $1/\delta$ (sketching survey 1.1) | **True for the instances; the interface is already general** (the confirmation before MD2): AMM, its tail and the OSE constructor (`MatrixMultiplication.lean`, `2 ≤ p`), Frobenius preservation (`1 ≤ p`), the PCP constructor (`ProjectionCost.lean:532`), sketch-and-solve (`Regression/Oblivious.lean:360`) and the LowRank range-finder, Nyström and early-truncation tails all take any `p`. |
| "the sub-Gaussian Hutch++ route, whose JL-moment step costs $1/\delta$" (sketching survey 1.1, citing `Estimation-HutchPP.md`) | **Out of date.** The maintainer's TE5 (a) replaced it: `measureReal_abs_trace_sub_hutchpp_ge_le_of_isSubgaussianVector` (`HutchPlusPlusTail.lean:196`) uses the constant-factor range finder `measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`, already $\log(1/\delta)$. No Hutch++ statement improves with M1. |
| The SRHT has OSE and OSI but no JL statement (both surveys) | True (`Structured/SRHT.lean`: OSE/OSI tails, sizes, asymptotic forms, both models; no `HasJLProperty`, no `HasJLMoment`). |
| Haar OSE/OSI: a short composition of the Haar JL tail with `HasJLProperty.isObliviousSubspaceEmbedding`, as the sign file does (sketching survey 1.2) | **True** (§4.1). |
| Haar sizes need spectral bounds for Haar blocks, R-2 (probability survey §0 item 3, R-2) | **Not for the $1 \mp \varepsilon$ size forms.** R-2 is needed only for a sharp form near $k = n$ and for spectral moments of $(\mathbf{W}\mathbf{Q})^{+}$ (Haar spectral co-range bounds), which none of the three deferred corollaries uses (§4.1). |
| Matrix Bernstein without replacement through Hoeffding's comparison (probability survey P-2) | True that it is missing; the comparison applies verbatim with $s$ = Hermitian matrices in place of the PSD cone (§5.1). |
| Spectral AMM by sampling: "about 150 lines, rectangular Bernstein exists" (`Sketching-REPORT.md` §6.1 item 3, `Sketching-S4.md` Q8) | True with replacement; without replacement and for the SRHT it needs M4's Bernstein. |

The planned deferrals this note picks up: `Sketching-S2.md` Q4 ("General `p` needs the tail for all
`t` and a named Gamma-integral constant; deferred to a consumer"), `Sketching-REPORT.md` §6.1 items 3
and 5 ("the JL moment at `p ≠ 2` (S2 Q4)", "Haar sizes … (S2 Q6, §6)"), `LowRank-S9.md` §6 D1, D3,
D4, `LowRank-S7.md` D3, D6, `Regression-SketchPrecondition.md` §7 "Haar corollary",
`Sketching-S5.md` §6 (scalar Bernstein without replacement, "one short corollary when one
appears"). S2 Q4's "tail for all `t`" is exactly what M1 supplies: every dense family has a JL tail
valid at every threshold (§2.2).

## 2. M1: JL moments beyond $p = 2$

### 2.1 The mathematics

If $D = \lvert\|\mathbf{S}\mathbf{x}\|^2 - 1\rvert$ has
$\mathbb{P}[t \le D] \le 2\exp(-\min(t^2/(2v), t/(2b)))$ for every $t > 0$, then by the layer-cake
formula, for $p > 0$,
$$\mathbb{E}D^p \le p\int_0^\infty t^{p-1}\,2\bigl(e^{-t^2/(2v)} + e^{-t/(2b)}\bigr)\,dt
= p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^p\Gamma(p)\,,$$
and for $p \ge 2$ this is at most $2(vp)^{p/2} + 2(2bp)^p$ by $\Gamma(x) \le x^{x-1}$ for $x \ge 1$
(a loss exponential in $p$, MD2; the inversion below uses this readable bound). For a sketch with $v = b = 4/\lvert k\rvert$ (Gaussian,
Haar) and $\lvert k\rvert \ge 128\,p/\varepsilon^2$, $\varepsilon \le 1$, both terms divided by
$\varepsilon^p$ are below $e^{-p}/2$ for $p \ge 2$; at $p = \max(2, \log(1/\delta))$ this is
$\varepsilon^p\delta$. So $\lvert k\rvert = O(\log(1/\delta)/\varepsilon^2)$ rows give the
$(\varepsilon, \delta, \log(1/\delta))$ JL moment property, and AMM at failure $\delta$ follows from
the existing generic theorem. (Woodruff 2014 states the property, Definition 12, and AMM from it,
Theorem 13; that dense families have it at $p = \log(1/\delta)$ is Kane and Nelson's, not in hand:
locator to check. The constants here are the proof's.)

### 2.2 Which families have a tail at every threshold

| Family | Tail at every $t > 0$ | $(v, b)$ |
|---|---|---|
| Gaussian | Dasgupta–Gupta one-sided tails of $\chi^2$: `measureReal_norm_sq_ge_mul_card_le_of_hasLaw_gaussianVector` ($\beta \ge 1$), `measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector` ($0 < \beta \le 1$), `ChiSquare.lean:156`, `:183` | $(4/\lvert k\rvert, 4/\lvert k\rvert)$, by $s - \log(1+s) \ge \min(s^2, s)/4$ and $-s - \log(1-s) \ge s^2/2$ |
| Haar | The same one-sided tails for a sphere projection, `Haar/Sphere.lean:336`, `:393`, through `hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame` | $(4/\lvert k\rvert, 4/\lvert k\rvert)$ |
| sub-Gaussian rows, proxy $c$ | `hasJLProperty_of_isSubgaussianVector` (`SubGaussian.lean:347`), $2e^{-C\lvert k\rvert\min(\varepsilon^2/c^2,\varepsilon/c)}$ for every $\varepsilon$, $C$ = `subgaussianJLConstant` | $(c^2/(2C\lvert k\rvert),\ c/(2C\lvert k\rvert))$ |
| signs | the sub-Gaussian row at $c = 1$ (`isSubgaussianVector_of_hasLaw_rademacherVector`); the sign file's own tail is Dasgupta–Gupta's polynomial exponent, useless beyond $\varepsilon = 3/2$ | as sub-Gaussian, $c = 1$ |
| CountSketch | none (Chebyshev only) | stays at $p = 2$ |
| SRHT | the M2 tail has a flattening floor $\lvert n\rvert e^{-t}$; no sub-exponential tail | M2 gives $p = 2$ (§3.3) |
| row sampling | not oblivious | — |

The Gaussian and Haar existing two-sided tails
(`measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`, the Haar JL tail) have
the polynomial exponent $\varepsilon^2/4 - \varepsilon^3/6$, negative beyond $3/2$, so the one-sided
$\beta$ forms are the input.

### 2.3 Statements, Probability and ForMathlib layers

**ForMathlib** (`NLAlib/ForMathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`, namespace `Real`;
Mathlib searched: `Mathlib/Analysis/SpecialFunctions/Gamma/*`, `Stirling.lean`, no upper bound of
this shape; only `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`, log-convexity):
```lean
/-- For $x \ge 1$, $\Gamma(x) \le x^{x-1}$: $\Gamma \le 1$ on $[1, 2]$ by convexity and
$\Gamma(1) = \Gamma(2) = 1$, then $\Gamma(x + 1) = x\Gamma(x)$. Upstream candidate. -/
theorem Real.Gamma_le_rpow_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.Gamma x ≤ x ^ (x - 1)
```
(`NLAlib/ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean`, beside `log_one_add_le_cubic`; Mathlib
searched `Mathlib/Analysis/SpecialFunctions/Log/`, none):
```lean
theorem Real.log_one_add_le_sub_sq_div {s : ℝ} (hs : 0 ≤ s) :
    Real.log (1 + s) ≤ s - s ^ 2 / (2 * (1 + s))
```

**Probability** (`NLAlib/Probability/Tail.lean`, 325 lines, the file of the layer-cake bound
`integral_le_of_measureReal_ge_le`; about +200):
```lean
/-- The **sub-exponential moment bound** <!-- value subexponentialMomentBound v b p -->
$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^p\Gamma(p)$: for $p > 0$, the bound on the $p$-th moment of a
nonnegative variable whose tail is at most $2\exp(-\min(t^2/(2v), t/(2b)))$
(`NLAlib.integral_rpow_le_of_measureReal_ge_le_two_mul_exp`), the layer-cake integral of that tail
exactly. For $p \ge 2$ it is at most $2(vp)^{p/2} + 2(2bp)^p$ (`subexponentialMomentBound_le`, by
$\Gamma(x) \le x^{x-1}$), a comparison that loses a factor exponential in $p$, about
$e^{p/2}/\sqrt{\pi p}$ and $e^p/\sqrt{2\pi p}$ on the two terms. Consumers use
`subexponentialMomentBound_nonneg`, `subexponentialMomentBound_mono` and
`subexponentialMomentBound_le`. -/
noncomputable irreducible_def subexponentialMomentBound (v b p : ℝ) : ℝ :=
  p * (2 * v) ^ (p / 2) * Real.Gamma (p / 2) + 2 * p * (2 * b) ^ p * Real.Gamma p

/-- The readable comparison: for $p \ge 2$ and $v, b \ge 0$,
<!-- value subexponentialMomentBound v b p -->$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^p\Gamma(p)
\le 2(vp)^{p/2} + 2(2bp)^p$. Every size form inverts through it. -/
theorem subexponentialMomentBound_le {v b p : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 2 ≤ p) :
    subexponentialMomentBound v b p ≤ 2 * (v * p) ^ (p / 2) + 2 * (2 * b * p) ^ p

/-- The layer-cake bound for $p$-th moments: for $f \ge 0$, $p > 0$ and
$\mathbb{P}[t \le f] \le F(t)$ for $t > 0$, with $t^{p-1}F(t)$ integrable on $(0, \infty)$,
$f^p$ is integrable and $\mathbb{E} f^p \le p\int_0^\infty t^{p-1}F(t)\,dt$. -/
theorem integral_rpow_le_of_measureReal_ge_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {p : ℝ} (hp : 0 < p) {F : ℝ → ℝ}
    (hF : IntegrableOn (fun t => t ^ (p - 1) * F t) (Set.Ioi 0))
    (htail : ∀ t, 0 < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    Integrable (fun ω => f ω ^ p) μ ∧
      ∫ ω, f ω ^ p ∂μ ≤ p * ∫ t in Set.Ioi 0, t ^ (p - 1) * F t

/-- **Moments from a sub-exponential tail**: for $f \ge 0$ with
$\mathbb{P}[t \le f] \le 2\exp(-\min(t^2/(2v), t/(2b)))$ for every $t > 0$, $v, b > 0$ and
$p > 0$, <!-- value subexponentialMomentBound v b p -->
$$\mathbb{E} f^p \le p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^p\Gamma(p)\,,$$
the bound being `subexponentialMomentBound v b p`. [Vershynin2018, Proposition 2.7.1] for the
equivalence of tails and moments, unspecified constants (2020 draft; locator to check). -/
theorem integral_rpow_le_of_measureReal_ge_le_two_mul_exp [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {v b p : ℝ} (hv : 0 < v)
    (hb : 0 < b) (hp : 0 < p)
    (htail : ∀ t, 0 < t → μ.real {ω | t ≤ f ω} ≤
      2 * Real.exp (-min (t ^ 2 / (2 * v)) (t / (2 * b)))) :
    Integrable (fun ω => f ω ^ p) μ ∧ ∫ ω, f ω ^ p ∂μ ≤ subexponentialMomentBound v b p

/-- **Two-sided sub-exponential tail from Dasgupta–Gupta tails**: if
$\mathbb{P}[\beta a \le Y] \le e^{(K/2)(1 - \beta + \log\beta)}$ for $\beta \ge 1$ and
$\mathbb{P}[Y \le \beta a] \le e^{(K/2)(1 - \beta + \log\beta)}$ for $0 < \beta \le 1$, with
$a > 0$, $K \ge 0$, then for $t \ge 0$
$\mathbb{P}[t \le \lvert Y/a - 1\rvert] \le 2e^{-(K/8)\min(t^2, t)}$. The input of the Gaussian and
Haar JL moments. -/
theorem measureReal_abs_div_sub_one_ge_le_two_mul_exp [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (hup : ∀ β : ℝ, 1 ≤ β → μ.real {ω | β * a ≤ Y ω} ≤ Real.exp (K / 2 * (1 - β + Real.log β)))
    (hlow : ∀ β : ℝ, 0 < β → β ≤ 1 →
      μ.real {ω | Y ω ≤ β * a} ≤ Real.exp (K / 2 * (1 - β + Real.log β)))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |Y ω / a - 1|} ≤ 2 * Real.exp (-(K / 8 * min (t ^ 2) t))
```
`P(Y ≤ 0) = 0` is not a hypothesis: for $K > 0$ it is the limit $\beta \to 0$ of `hlow`
($\log\beta \to -\infty$); for $K = 0$ the bound is $2$.

`NLAlib/Probability/SubExponential/Tail.lean` (the survey's P-4, one corollary, since the
library's `HasSubexponentialMGF X v b μ` tail is exactly the hypothesis above):
```lean
theorem HasSubexponentialMGF.integral_abs_rpow_le {v b : ℝ≥0} (h : HasSubexponentialMGF X v b μ)
    (hv : 0 < v) (hb : 0 < b) {p : ℝ} (hp : 0 < p) :
    ∫ ω, |X ω| ^ p ∂μ ≤ subexponentialMomentBound (v : ℝ) (b : ℝ) p
```
(`HasSubexponentialMGF X v b μ` has `v b : ℝ≥0`, `SubExponential/Basic.lean:52`; the bound takes
their coercions to ℝ, and `NNReal.coe_pos` turns `hv`, `hb` into the real hypotheses of the
Probability lemma.)

### 2.4 Statements, Sketching layer

`NLAlib/Sketching/Properties/JohnsonLindenstrauss.lean` (495 lines; +40), the bridge:
```lean
/-- **Moments from tails**: if $\mathbf{S}$ has the JL property at every distortion $t > 0$ with
failure probability $2\exp(-\min(t^2/(2v), t/(2b)))$, $v, b > 0$, then for $\varepsilon > 0$ and
$p > 0$ it has the JL moment property with exponent $p$ and
failure <!-- value subexponentialMomentBound v b p -->
$\delta = (p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^p\Gamma(p))/\varepsilon^p$. The converse direction of
`NLAlib.HasJLMoment.hasJLProperty`. [Woodruff2014, Definition 12], the property; that dense
sketches have it at $p = \log(1/\delta)$ is Kane and Nelson's (not in hand, locator to check). -/
theorem hasJLMoment_of_forall_hasJLProperty [IsProbabilityMeasure μ] (hS : AEMeasurable S μ)
    {v b : ℝ} (hv : 0 < v) (hb : 0 < b)
    (h : ∀ t : ℝ, 0 < t →
      HasJLProperty S t (2 * Real.exp (-min (t ^ 2 / (2 * v)) (t / (2 * b)))) μ)
    (hε : 0 < ε) (hp : 0 < p) :
    HasJLMoment S ε (subexponentialMomentBound v b p / ε ^ p) p μ
```

The new size, beside `jlDim` (its home after the §6 split is `Sketching/Gaussian/Gaussian.lean`):
```lean
/-- The **JL moment dimension** <!-- value jlMomentDim \varepsilon \delta -->
$128\max(2, \log(1/\delta))/\varepsilon^2$: a Gaussian or Haar sketch with at least this many rows
has the JL moment property with distortion $\varepsilon \le 1$, failure probability $\delta$ and
exponent $\max(2, \log(1/\delta))$. The value the proof reaches. Junk: $0$ at $\varepsilon = 0$. -/
noncomputable irreducible_def jlMomentDim (ε δ : ℝ) : ℝ :=
  128 * max 2 (Real.log (1 / δ)) / ε ^ 2
-- API: jlMomentDim_nonneg, jlMomentDim_mono (antitone in ε on (0, 1], in δ), jlMomentDim_le

/-- The sub-Gaussian JL moment dimension, <!-- value subgaussianJLMomentDim c \varepsilon \delta -->
$16 c^2\max(2, \log(1/\delta))/(C\varepsilon^2)$ with
<!-- value subgaussianJLConstant -->$C = 1/36$ (`subgaussianJLConstant`), for $\varepsilon \le c$. -/
noncomputable irreducible_def subgaussianJLMomentDim (c ε δ : ℝ) : ℝ :=
  16 * c ^ 2 * max 2 (Real.log (1 / δ)) / (subgaussianJLConstant * ε ^ 2)
```
(The constants $128$ and $16/C$ are this note's arithmetic through `subexponentialMomentBound_le`,
§2.1; the skeleton writes what the proof reaches. A Stirling-sharp comparison would lower them by a
factor of about $e$ (the review's estimate for `jlMomentDim` is about $47$), a body change only
(MD2). Both registered in `docs/constants.toml` with their asymptotic comparison lemmas.)

Family instances, each in its family file, two per family plus an asymptotic form (B5):
```lean
-- Sketching/Gaussian/Gaussian.lean
/-- **The JL moment property of a Gaussian sketch at every order**: for $\varepsilon > 0$,
$p > 0$ and $\mathbf{S} = \lvert k\rvert^{-1/2}\mathbf{G}$ with $\mathbf{G}$ standard Gaussian,
the JL moment property holds with exponent $p$ and failure
probability <!-- value subexponentialMomentBound (4/\lvert k \rvert) (4/\lvert k \rvert) p -->
$\bigl(p(2(4/\lvert k\rvert))^{p/2}\Gamma(p/2) + 2p(2(4/\lvert k\rvert))^p\Gamma(p)\bigr)/\varepsilon^p$.
Incomparable with `NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix` (the exact $p = 2$ variance,
better at $p = 2$). -/
theorem hasJLMoment_subexponentialMomentBound_of_hasLaw_gaussianMatrix [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hp : 0 < p) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε
      (subexponentialMomentBound (4 / Fintype.card k) (4 / Fintype.card k) p / ε ^ p) p μ

/-- **Gaussian JL moments, sample-size form**: at least <!-- value jlMomentDim \varepsilon \delta -->
$128\max(2, \log(1/\delta))/\varepsilon^2$ rows give the JL moment property with distortion
$0 < \varepsilon \le 1$, failure probability $\delta > 0$ and exponent $\max(2, \log(1/\delta))$;
approximate multiplication with failure $\delta$ follows
(`NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le`).
[Woodruff2014, Definition 12 and Theorem 13]. Asymptotic form:
`NLAlib.exists_forall_hasJLMoment_of_hasLaw_gaussianMatrix`.
Result: jl-moment-gaussian -/
theorem hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
    (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : jlMomentDim ε δ ≤ Fintype.card k) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε δ (max 2 (Real.log (1 / δ))) μ

theorem exists_forall_hasJLMoment_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      (μ : Measure Ω) (G : Ω → Matrix k n ℝ) (ε δ : ℝ),
      HasLaw G (gaussianMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε δ (max 2 (Real.log (1 / δ))) μ
```
(At $\delta \le 1/2$, $\max(2, \log(1/\delta)) \le 3\log(1/\delta)$, so $C = 384$.)

The same three for Haar (`Sketching/Gaussian/Haar.lean`, with `hk : card k ≤ card n`, sketch
`√(card n / card k) • (Q ω)ᴴ`, names `…_of_hasLaw_haarFrame`, `Result: jl-moment-haar`) and for
sub-Gaussian rows (`Sketching/Gaussian/SubGaussian.lean`, hypotheses `hind hsub hiso` as in
`hasJLMoment_of_isSubgaussianVector`, failure
`subexponentialMomentBound (c ^ 2 / (2 * subgaussianJLConstant * card k)) (c / (2 * subgaussianJLConstant * card k)) p / ε ^ p`,
size `subgaussianJLMomentDim c ε δ` with `hεc : ε ≤ c`, threshold
$C c^2\log(1/\delta)/\varepsilon^2$ in the asymptotic form). Signs: no separate statement; the
module docstring of `Rademacher.lean` shows the two-line discharge at $c = 1$, as
`LowRank/Oblivious/SubGaussian.lean:40` already does. CountSketch: unchanged.

Not stated: per-family AMM sizes. AMM at failure $\delta$ is the generic tail applied to the size
form in two lines; the module docstrings show it.

### 2.5 Proof routes and sizes

* `Real.Gamma_le_rpow_sub_one`: convexity on $[1,2]$, then induction on $\lfloor x\rfloor$ with
  `Real.Gamma_add_one`. About 40 lines.
* `integral_rpow_le_of_measureReal_ge_le`: Mathlib's
  `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul`, as in
  `HasSubgaussianMGF.integral_abs_rpow_le` (`SubGaussian/Moments.lean:64`). About 50.
* The closed form: Mathlib's `integral_rpow_mul_exp_neg_mul_rpow` at exponents $2$ and $1$ (the
  private `integral_Ioi_two_mul_exp_mul_rpow` of `SubGaussian/Moments.lean` is its exponent-2 case
  and becomes public there or is reused); `subexponentialMomentBound_le` by
  `Real.Gamma_le_rpow_sub_one`. About 60.
* Dasgupta–Gupta to sub-exponential: `Real.log_one_add_le_sub_sq_div` and
  `Real.log_one_sub_le_quadratic` (exists, `Log/Deriv.lean:87`: $\log(1 - u) \le -u - u^2/2$, so
  $1 - \beta + \log\beta \le -(1-\beta)^2/2$ on the lower side) for the two sides, a union. About 60.
* Each family: the tail (Gaussian: `hasLaw_mulVec_of_hasLaw_gaussianMatrix` and the χ² tails; Haar:
  the sphere tails at `a = card k / card n`; sub-Gaussian: the existing JL tail rewritten in
  $(v,b)$), the bridge, then the size inversion. About 80 per family with the asymptotic form.

Total M1 core: about 600 lines.

### 2.6 Consumers that improve, and how

| Existing statement (file:line) | Its $1/\delta$ hypothesis | New explicit twin (MD4) | Asymptotic form, upgraded in place |
|---|---|---|---|
| `hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card` (`Gaussian.lean:709`) | `projectionCostTailDim 2 d ε δ` $= 768(d+1)/(\varepsilon^2\delta)$ | `…_of_jlMomentDim_le`, second size `jlMomentDim (ε / (8 * √(d + 1))) (δ / 6)` | `exists_forall_hasProjectionCostPreserving_of_hasLaw_gaussianMatrix`: $C(d + \log(1/\delta))/\varepsilon^2 + C(d+1)\log(1/\delta)/\varepsilon^2$ |
| `hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card` (`SubGaussian.lean:755`) | `projectionCostTailDim (16c²−1) d ε δ` | `…_of_subgaussianJLMomentDim_le` | likewise, with $c^2$ |
| `measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix` (`Regression/Gaussian.lean:70`) | $16(r+1) \le \varepsilon\delta p$ | `…_of_jlMomentDim_le`, `jlMomentDim (√(ε / (4 * (r + 1)))) (δ / 2)` $= 512(r+1)\max(2,\log(2/\delta))/\varepsilon$ | `exists_forall_…`: $C(r+1)\log(1/\delta)/\varepsilon$ |
| `measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix` (`LowRank/Oblivious/Gaussian.lean:79`) | $216k/(\varepsilon^2\delta)$ | `…_of_jlMomentDim_le` | $Ck\log(1/\delta)/\varepsilon^2$ |
| `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector` (`LowRank/Oblivious/SubGaussian.lean:134`) | $8(16c^2-1)k/(\varepsilon\delta)$ | `…_of_subgaussianJLMomentDim_le` | $Cc^2k\log(1/\delta)/\varepsilon$ |
| `measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector` (`:252`) | as above | `…_of_subgaussianJLMomentDim_le` | likewise |

Each new explicit twin is the old proof with the JL-moment instance swapped (the generic theorem
takes any `2 ≤ p`); about 50 lines each plus the asymptotic re-proof, about 600 in all.

**Side conditions.** The size forms hold only for distortion at most $1$ (Gaussian, Haar) or at
most $c$ (sub-Gaussian), so each twin needs its JL budget in that range. PCP's
$\varepsilon/(8\sqrt{d+1})$ is at most $1$ under the existing `hε2 : ε ≤ 2`, and early truncation's
$\varepsilon/(6\sqrt{k})$ under `hε1 : ε ≤ 1`. Sketch-and-solve's $\sqrt{\varepsilon/(4(r+1))}$ is
not covered by the existing hypotheses (the old theorem has no upper bound on $\varepsilon$), so the
twin adds `hε4 : ε ≤ 4`, which gives $\sqrt{\varepsilon/(4(r+1))} \le 1$ since $r + 1 \ge 1$. The
sub-Gaussian randomized SVD's $\sqrt{\varepsilon/(4k)}$ needs $\le c$, which follows from the same
`ε ≤ 4`, $k \ge 1$ (the case $k = 0$ is handled first, as in the existing proof) and isotropy's
$c \ge 1$. The asymptotic forms already carry `ε ≤ ε₀`, so they take $\varepsilon_0 \le 1$.
The product form $(d+1)\log(1/\delta)$ is what JL moments give through these generic routes; the
additive $(d + \log(1/\delta))/\varepsilon^2$ of CEMMP Lemma 11 and the optimal Gaussian
sketch-and-solve rate need stable-rank spectral AMM (`LowRank-S9.md` D1), which this round does not
supply for dense sketches (M4's Bernstein gives it for the SRHT only; §5.5).

Not improved: Hutch++ (§1), CountSketch everywhere (no higher moment), Gaussian HMT-type tails
(already $\log(1/\delta)$ by other routes), the Haar relative-error sketch-and-solve and RSVD
(none stated by this route; §4.3).

Also reachable with no further work, and recommended as one statement each because no
$1/\delta$ form exists to twin: **sub-Gaussian relative-error sketch-and-solve**
(`Regression/SubGaussian.lean`, sketching survey 2.2: "assembly … with the existing OSI sizes"),
stated directly in the $\log(1/\delta)$ form with its asymptotic form, about 120 lines.

## 3. M2: the SRHT as a JL sketch

### 3.1 OSE for dimension 1 gives the JL property

For a unit $\mathbf{x}$, the column matrix $\mathbf{U} = [\mathbf{x}]$ has rank at most $1$, and
$\mathbf{S}$ embeds $\operatorname{range}\mathbf{U}$ with constants $a, b$ iff
$a \le \|\mathbf{S}\mathbf{x}\|^2 \le b$. With $1 - \varepsilon < a$ and $b < 1 + \varepsilon$ that
gives $\lvert\|\mathbf{S}\mathbf{x}\|^2 - 1\rvert < \varepsilon$, so the JL event
$\{\varepsilon \le \lvert\cdot\rvert\}$ lies in the OSE failure event. Strictness is needed: the JL
event is non-strict (S1 §3.5), and the SRHT law is discrete, so the boundary may carry mass.

`Sketching/Properties/JohnsonLindenstrauss.lean`, section "From subspace embeddings to the JL
property" (after "From the JL property to subspace embeddings"; about 30 lines):
```lean
/-- **An OSE for dimension one has the JL property**: if $\mathbf{S}$ is an oblivious subspace
embedding for dimension $1$ with constants $a, b$ and failure probability $\delta$, and
$1 - \varepsilon < a$, $b < 1 + \varepsilon$, then it has the JL property with distortion
$\varepsilon$ and failure probability $\delta$. The converse of
`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding` at $d = 1$, without its net factor.
[Woodruff2014, Definitions 2 and 3], there for $1 \mp \varepsilon$. -/
theorem IsObliviousSubspaceEmbedding.hasJLProperty (h : IsObliviousSubspaceEmbedding S 1 a b δ μ)
    (ha : 1 - ε < a) (hb : b < 1 + ε) : HasJLProperty S ε δ μ
```
Proof: `IsObliviousSubspaceEmbedding.hasSubspaceEmbedding` at `Matrix.replicateCol Unit x`
(rank at most `card Unit = 1` by `Matrix.rank_le_card_width`), `isSubspaceEmbedding_iff_forall_mem_range`,
`measureReal_mono`. No finite-measure hypothesis.

The other OSE families gain nothing from it (their JL tails are better or equal); it exists for the
SRHT and for any future family with an OSE but no JL analysis.

### 3.2 The SRHT JL tail and size

`Sketching/Structured/SRHTMultiplication.lean` (new, §6; the SRHT file is at 1050 lines):
```lean
/-- **Distributional JL for the SRHT**: for a bounded orthonormal $\mathbf{F}$ with constant
$\beta$, $0 \le \varepsilon \le 1$ and $t \ge 0$, the SRHT has the JL property with distortion
$\varepsilon$ and failure probability
$$2\exp\Bigl(-\frac{\varepsilon^2\lvert k\rvert}{3\beta(1 + 2\sqrt{t} + 2t)}\Bigr)
+ \lvert n\rvert e^{-t}\,,$$
the OSE bound of `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht` at $d = 1$.
[Woodruff2014, Theorem 7] and [Tropp2011a, Theorems 1.3 and 3.1] for the SRHT as an embedding
(the locators of `isObliviousSubspaceEmbedding_of_hasLaw_srht`, `SRHT.lean:578`); the fast JL
transform of Ailon and Chazelle (not in hand). Any field.
Result: jl-srht -/
theorem hasJLProperty_of_hasLaw_srht (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    HasJLProperty S ε (2 * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (1 + 2 * √t + 2 * t)))) +
      Fintype.card n * Real.exp (-t)) μ

theorem hasJLProperty_of_hasLaw_srht_of_samplingEmbeddingDim_le (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingEmbeddingDim 1 (β * srhtRowBound (Fintype.card n) 1 (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    HasJLProperty S ε δ μ

theorem exists_forall_hasJLProperty_of_hasLaw_srht :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype k]
      [Fintype n] [DecidableEq n] (μ : Measure Ω) (S : Ω → Matrix k n 𝕜) (F : Matrix n n 𝕜)
      (β ε δ : ℝ),
      IsBoundedOrthonormal F β → HasLaw S (srht k F) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (β * (1 + Real.log (Fintype.card n / δ)) * Real.log (1 / δ) / ε ^ 2) ≤
        Fintype.card k →
      HasJLProperty S ε δ μ
```
(The binder list and threshold mirror `exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_srht`
at $d = 1$, $C = 72$ there. With-replacement twins: `…_of_hasLaw_srhtWithReplacement`, three
more.) Proof of the tail: for every $\varepsilon' < \varepsilon$ the bridge applies to the OSE at
$\varepsilon'$, the event at $\varepsilon$ is inside the one at $\varepsilon'$, and the bound is
continuous in $\varepsilon'$, so `ge_of_tendsto` at $\varepsilon' \to \varepsilon^-$ closes it
(about 40 lines; fallback, if the limit costs more: the tail at $\varepsilon/2$'s constants). The
JL lemma for $N$ points through the SRHT is then
`HasJLProperty.measureReal_exists_abs_norm_mulVec_sq_sub_ge_le`, no new statement.

### 3.3 The SRHT JL moment at $p = 2$, directly

The JL moment does *not* follow usefully from the tail of §3.2: the flattening floor
$\lvert n\rvert e^{-t}$ must be pushed below $\varepsilon^p\delta(\lvert k\rvert/\lvert n\rvert)^p$
(the distortion is bounded only by $\lvert n\rvert/\lvert k\rvert$), which costs $p\log(n/(k\varepsilon))$
in $t$ and a $\log^2(1/\delta)$ in the size. A direct second moment is cleaner and has no
$\log n$ at all:

With $\mathbf{z} = \mathbf{F}\mathbf{D}\mathbf{x}$ ($\|\mathbf{z}\| = 1$) and
$y_i = \lvert n\rvert\lvert z_i\rvert^2$ (mean $1$ over the population), $\|\mathbf{S}\mathbf{x}\|^2
- 1$ is the mean of $\lvert k\rvert$ draws of $y_i - 1$. Without replacement its second moment is
at most the with-replacement one, $\sigma^2/\lvert k\rvert$ with
$\sigma^2 = \lvert n\rvert\sum_i\lvert z_i\rvert^4 - 1$ (Hoeffding's comparison,
`integral_uniformOn_injective_le_integral_pi`, at $f = (\cdot)^2$; or the exact
$(n - k)/(n - 1)$ factor). Over the signs,
$\mathbb{E}\lvert z_i\rvert^4 \le 3(\sum_j \lvert F_{ij}\rvert^2\lvert x_j\rvert^2)^2 \le 3\beta^2/\lvert n\rvert^2$
(fourth moment of a Rademacher sum), so
$$\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - 1)^2 \le \frac{3\beta^2 - 1}{\lvert k\rvert}\,,$$
the Gaussian's $2/\lvert k\rvert$ at $\beta = 1$ (Walsh–Hadamard).
```lean
/-- **The JL moment of the SRHT** at $p = 2$: for a bounded orthonormal $\mathbf{F}$ with constant
$\beta$, $k$ nonempty and $\varepsilon > 0$, the SRHT has the JL moment property with exponent $2$
and $\delta = (3\beta^2 - 1)/(\lvert k\rvert\varepsilon^2)$; the Gaussian sketch's at $\beta = 1$.
No $\log\lvert n\rvert$: the flattening is not used. [Woodruff2014, Definition 12] for the
property; the bound is this proof's (no printed source in hand). -/
theorem hasJLMoment_of_hasLaw_srht [Nonempty k] (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (hε : 0 < ε) :
    HasJLMoment S ε ((3 * β ^ 2 - 1) / (Fintype.card k * ε ^ 2)) 2 μ
-- and hasJLMoment_of_hasLaw_srhtWithReplacement [Nonempty k] [Nonempty n]
```
Field: over `𝕜` if the complex-coefficient fourth moment
($\mathbb{E}\lvert\sum_j a_j\xi_j\rvert^4 = 2(\sum\lvert a_j\rvert^2)^2 + \lvert\sum a_j^2\rvert^2 -
2\sum\lvert a_j\rvert^4$) comes from `integral_norm_quadForm_sub_trace_sq`
(`QuadraticForm/Moments.lean:280`) in under 50 lines, else ℝ (every downstream consumer below is
real). About 150 lines with the conditioning on the signs (`srht_eq_map_prod`, and the product-law
facts private in `SRHT.lean:281–308`, made public in a Probability home: survey 1.11).

### 3.4 What follows for the SRHT (assembly, real $\mathbf{F}$)

Through existing generic theorems, real only (AMM is real, `MatrixMultiplication.lean` Q2):
* AMM in Frobenius norm at failure $\delta$ from
  $\lvert k\rvert \ge (3\beta^2 - 1)/(\varepsilon^2\delta)$: generic, no statement.
* **PCP** (`LowRank-S9.md` D3, "SRHT at dimension $O(k)$"):
  `hasProjectionCostPreserving_of_hasLaw_srht_of_le_card` with sizes
  `samplingEmbeddingDim d (β * srhtRowBound (card n) d (δ / 4)) (ε / 2) (δ / 4)` and
  `projectionCostTailDim (3 * β ^ 2 - 1) d ε δ` (the named Dim's $v$ is exactly this family's
  constant), plus `exists_forall_…`. In `Sketching/Structured/SRHTMultiplication.lean`. About 120.
* **Sketch-and-solve to relative error**: `measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_srht`
  and `exists_forall_…` in `Regression/SRHT.lean` (206 lines), via the SRHT OSI size and
  `HasJLMoment.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le`. Woodruff's Theorem 23 is the
  standard citation (there sparse embeddings). About 120.
* **$(1 + \varepsilon)$ randomized SVD and early truncation** (`LowRank-S7.md` D6, SRHT half):
  `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht_of_le_card` (the plain name is taken by
  the constant-factor `δ + 1/t` statement, `LowRank/Oblivious/SRHT.lean:83`; the distinguishing
  hypothesis is the second size, §8 Q5) and
  `measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht`, each with an asymptotic
  form, in `LowRank/Oblivious/SRHT.lean` (180 lines). About 200.

Recommendation: include these four (about 450 lines): each was deferred only for want of an SRHT
multiplication tail, and each is a composition. The $1/\delta$ in their second size is the price
of $p = 2$; §5.5 records the $\log(1/\delta)$ route.

## 4. M3: Haar sample sizes and the three deferred corollaries

### 4.1 Which survey is right

The Haar OSE of `HaarEmbedding.lean:626` is Gordon's route: lower constant
$(1 - (\sqrt d + t)/\sqrt{\lvert k\rvert})^2/(1 + (\sqrt{\lvert k\rvert} + s)/\sqrt{\lvert n\rvert})^2$,
whose denominator is at least $(1 + \sqrt{k/n})^2$, so no choice of $(t, s)$ reaches $1 - \varepsilon$
unless $k/n \to 0$; that is why S2 Q6 found no size form ("inversion needs a condition on $n$ too").
The JL route avoids it: `hasJLProperty_of_hasLaw_haarFrame` (`Haar.lean:279`) holds with the
Gaussian's exponent at every $\varepsilon \ge 0$ for `card k ≤ card n`, and
`HasJLProperty.isObliviousSubspaceEmbedding` (`JohnsonLindenstrauss.lean:480`) turns it into an OSE
with constants $1 \mp \varepsilon$ at distortion $4\varepsilon/5$ and failure
$2\cdot 21^d e^{-\lvert k\rvert(4\varepsilon^2/25 - 32\varepsilon^3/375)}$, exactly as
`isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix` does for signs. The size inversion is the
sign file's private `two_mul_twentyOne_pow_mul_exp_le_of_jlDim_le` (`Rademacher.lean:287`). So the
**sketching survey is right**: $(d + \log(1/\delta))/\varepsilon^2$ rows, the optimal order, with no
Haar-block spectral input. R-2 (spectral moments and tails of $(\mathbf{W}\mathbf{Q})^{+}$) stays a
RandomMatrix item for Haar spectral co-range bounds and a sharp form near $k = n$; none of the
three corollaries below needs it.

### 4.2 Statements

`Sketching/Gaussian/Gaussian.lean`: the helper becomes public beside `two_mul_exp_le_of_jlDim_le`
(rule S5; the sign and Haar files both need it):
```lean
theorem two_mul_twentyOne_pow_mul_exp_le_of_jlDim_le {d : ℕ} {K : ℝ} (hε : 0 < ε)
    (hε3 : ε < 15 / 8) (hδ : 0 < δ) (hk : jlDim (4 * ε / 5) (δ / 21 ^ d) ≤ K) :
    2 * 21 ^ d * Real.exp (-(K * (4 * ε ^ 2 / 25 - 32 * ε ^ 3 / 375))) ≤ δ
```
`Sketching/Gaussian/HaarEmbedding.lean` (687 lines; +180):
```lean
/-- **The Haar OSE by JL and a net**: for $\varepsilon \ge 0$ and $\lvert k\rvert \le \lvert n\rvert$,
the Haar sketch $\mathbf{S} = \sqrt{\lvert n\rvert/\lvert k\rvert}\,\mathbf{Q}^{\mathsf{H}}$ is an
oblivious subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$ and failure
probability $2\cdot 21^d e^{-\lvert k\rvert(4\varepsilon^2/25 - 32\varepsilon^3/375)}$
(`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding` at $4\varepsilon/5$). Incomparable with
Gordon's `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame` (rule 4): this one reaches
$1 \mp \varepsilon$ at every $k \le n$, that one is sharper in its constants for $k \ll n$.
[Vershynin2018, Lemma 5.3.2] for the Haar JL fact, unspecified constant (2020 draft).
Result: haar-sketch-ose -/
theorem isObliviousSubspaceEmbedding_one_sub_one_add_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ)
    (hε : 0 ≤ ε) :
    IsObliviousSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      (1 - ε) (1 + ε)
      (2 * 21 ^ d * Real.exp (-(Fintype.card k * (4 * ε ^ 2 / 25 - 32 * ε ^ 3 / 375)))) μ

theorem isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_jlDim_le
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε)
    (hε3 : ε < 15 / 8) (hδ : 0 < δ) (hk' : jlDim (4 * ε / 5) (δ / 21 ^ d) ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      (1 - ε) (1 + ε) δ μ

theorem isObliviousSubspaceInjection_of_hasLaw_haarFrame_of_jlDim_le [DecidableEq n] [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε)
    (hε3 : ε < 15 / 8) (hδ : 0 < δ) (hk' : jlDim (4 * ε / 5) (δ / 21 ^ d) ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      (1 - ε) δ μ

theorem exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      [DecidableEq k] (μ : Measure Ω) (Q : Ω → Matrix n k ℝ) (d : ℕ) (ε δ : ℝ),
      HasLaw Q (haarFrame n k) μ → Fintype.card k ≤ Fintype.card n →
      0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((d + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card k →
      IsObliviousSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
        (1 - ε) (1 + ε) δ μ
-- and exists_forall_isObliviousSubspaceInjection_of_hasLaw_haarFrame (adds [DecidableEq n])
```
$C = 58$, $\varepsilon_0 = 1$ as for signs. The OSI is the OSE plus
`isIsotropicSketch_of_hasLaw_haarFrame` through `IsObliviousSubspaceEmbedding.isObliviousSubspaceInjection`.
About 180 lines.

### 4.3 The three deferred Haar corollaries

1. **Haar sketch-and-precondition** (`Regression-SketchPrecondition.md` §7 "Haar corollary"). New
   `Regression/Haar.lean` (§6), three statements mirroring `Regression/SubGaussian.lean:65`, `:101`,
   `:136`:
   ```lean
   theorem measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame
       (hQ : HasLaw Q (haarFrame m k) μ) (hkm : Fintype.card k ≤ Fintype.card m)
       {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) (y : m → ℝ) {x₀ : Ω → n → ℝ}
       (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution
         (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ * A)
         (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ *ᵥ y) (x₀ ω))
       {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
       (hk : jlDim (4 * ε / 5) (δ / 21 ^ (Fintype.card n + 1)) ≤ Fintype.card k)
       {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
       μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
         ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A
           (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ) y (x₀ ω) q)‖ ^ 2} ≤ δ
   ```
   with the sketch-and-solve-start form `…_pinv_mulVec_…_of_hasLaw_haarFrame` (no asymptotic form,
   as for the other families) and `exists_forall_…_of_hasLaw_haarFrame` ($|k| \ge C(\lvert n\rvert + 1
   + \log(1/\delta))$, $q \ge C\log(1/\tau)$). About 150 lines.
2. **Haar PCP** (`LowRank-S9.md` D4, "about 70 lines after that form exists"). In the dense-family
   PCP file (§6), mirroring `Gaussian.lean:709`:
   ```lean
   theorem hasProjectionCostPreserving_of_hasLaw_haarFrame_of_le_card
       (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n)
       {m : Type*} [Fintype m] (A : Matrix m n ℝ) (d : ℕ) (hε : 0 < ε) (hε2 : ε ≤ 2) (hδ : 0 < δ)
       (hk₁ : jlDim (2 * ε / 5) (δ / 2 / 21 ^ d) ≤ Fintype.card k)
       (hk₂ : projectionCostTailDim 2 d ε δ ≤ Fintype.card k) :
       HasProjectionCostPreserving (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) A d
         (1 - ε) (1 + ε) δ μ
   ```
   ($v = 2$: the Haar JL moment's $2(n-k)/(k(n+2)\varepsilon^2) \le 2/(k\varepsilon^2)$), its
   `_of_jlMomentDim_le` twin from M1, and one asymptotic form in the $\log(1/\delta)$ shape (MD4).
   About 150 lines.
3. **Haar early truncation, OSI route** (`LowRank-S7.md` D3, "Haar early truncation and Haar
   instances of the OSI route"). New `LowRank/Oblivious/Haar.lean` (S7 §4 noted "there is no such
   file"), mirroring `LowRank/Oblivious/Gaussian.lean:79` and `:160`: the OSI at $1 - \varepsilon/6$,
   failure $\delta/3$, and the Haar JL moment for the two multiplication tails,
   `measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame` and its asymptotic form
   (with M1, the size is `jlMomentDim (ε / (6 * √k)) (δ / 3)`; without it, $216k/(\varepsilon^2\delta)$).
   The Haar relative-error RSVD by this route is dominated by HT1 (Tropp–Webber through the range
   transfer, `RangeFinderTailHaar.lean`) and is not stated (S7 Q7). About 120 lines.

Also reachable and small, recommended with item 1: **Haar sketch-and-solve with high probability**
(sketching survey 2.2: only expectation forms exist, `SketchAndSolve.lean:664`, `:844`), in the
$\log(1/\delta)$ form, `Regression/Haar.lean`, about 100 lines.

## 5. M4: matrix Bernstein and the Chernoff means without replacement

### 5.1 Why the comparison applies

`integral_uniformOn_injective_le_integral_pi` (`ConvexOrder.lean:265`) holds for any $f$ convex and
continuous on a closed $s$ containing every with-replacement sum. The Chernoff file uses
$f = \operatorname{re}\operatorname{tr} e^{\theta\,\cdot}$ on the PSD cone
(`ChernoffWithoutReplacement.lean:102`, via `convexOn_re_trace_exp.comp_linearMap` and `.subset`).
For Bernstein the summands are centred, so $s$ is the Hermitian matrices, on which
`convexOn_re_trace_exp` (`Matrix/Functions/TraceFunctions.lean:417`) is stated directly (closed:
`isClosed_eq` of `conjTranspose` and `id`, one line; no named lemma found in NLAlib or Mathlib), and
the same $f$; the i.i.d. side is
`NLAlib.HasMatrixMGFBound.integral_re_trace_exp_sum_le` (`MGFBound.lean:143`, inside
`namespace HasMatrixMGFBound`; not the root `NLAlib.integral_re_trace_exp_sum_le` of
`Subadditivity.lean:270`, the subadditivity of cumulants) with
`hasMatrixMGFBound_of_integral_eq_zero_of_le` (`Bernstein.lean:178`) for uniform draws from a
centred population. No new convexity fact is needed.

### 5.2 Statements, Probability layer

`MatrixConcentration/Bernstein.lean` (399 lines; +90), the trace-form layer the Chernoff file
already has (`measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le`, `Chernoff.lean:216`):
```lean
/-- **Matrix Bernstein from a trace bound**: if $\mathbf{Y}$ is almost surely Hermitian,
$\mathbf{W}$ Hermitian, $L > 0$, and for every $0 < \theta < 3/L$
$\mathbb{E}\operatorname{tr}e^{\theta\mathbf{Y}}
\le \operatorname{tr}\exp\bigl(\tfrac{\theta^2/2}{1 - L\theta/3}\mathbf{W}\bigr)$, then for $t \ge 0$
$$\mathbb{P}[\lambda_0(\mathbf{Y}) \ge t] \le \lvert n\rvert
\exp\Bigl(\frac{-t^2/2}{\|\mathbf{W}\|_2 + Lt/3}\Bigr)\,.$$
[Tropp2015, Theorem 6.6.1], whose proof goes through this trace bound. -/
theorem measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le [Nonempty n]
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hW : W.IsHermitian) (hL : 0 < L)
    (hint : ∀ θ ∈ Set.Ioo 0 (3 / L), Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ ∈ Set.Ioo 0 (3 / L), ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • W)).trace) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (specNorm W + L * t / 3))

theorem integral_eigenvalue_zero_le_bernstein_of_integral_le [Nonempty n]
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hYi : Integrable Y μ) (hW : W.IsHermitian) (hL : 0 < L)
    (hint : …) (htr : …) :
    ∫ ω, eigenvalue (Y ω) 0 ∂μ ≤
      √(2 * specNorm W * Real.log (Fintype.card n)) + L * Real.log (Fintype.card n) / 3
```
The i.i.d. tails are then reproved through these (rule 6: same names, same statements; optional).

New `MatrixConcentration/BernsteinWithoutReplacement.lean` (about 300 lines), for a **centred
population** $\mathbf{X} : n \to \Bbbk^{m\times m}$ (§8 Q7), a uniform injection
$\iota : k \to n$ and $v = (\lvert k\rvert/\lvert n\rvert)\|\sum_i\mathbf{X}_i^2\|_2$:
```lean
variable {ι : Ω → k → n} {X : n → Matrix m m 𝕜}

/-- **The matrix Bernstein trace bound without replacement**: for Hermitian $\mathbf{X}_i$ with
$\sum_i \mathbf{X}_i = \mathbf{0}$ and $\mathbf{X}_i \preceq L\mathbf{I}$, $L > 0$, a uniformly random
injection $\iota : k \to n$ and $0 < \theta < 3/L$,
$$\mathbb{E}\operatorname{tr}\exp\Bigl(\theta\sum_j\mathbf{X}_{\iota(j)}\Bigr) \le
\operatorname{tr}\exp\Bigl(\frac{\theta^2/2}{1 - L\theta/3}\cdot
\frac{\lvert k\rvert}{\lvert n\rvert}\sum_i\mathbf{X}_i^2\Bigr)\,,$$
the bound of the i.i.d. sum with the same variance. Hoeffding's comparison on the Hermitian matrices
and [Tropp2015, Lemma 6.6.2]. [GrossNesme2010, Section D]; [Tropp2011a, proof of Theorem 2.1]
(the same comparison for the Chernoff bound, as `ChernoffWithoutReplacement.lean:95` cites it). -/
theorem integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hX : ∀ i, (X i).IsHermitian) (hsum : ∑ i, X i = 0)
    (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (3 / L)) :
    ∫ ω, RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) •
        (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i ^ 2))).trace

/-- **Matrix Bernstein without replacement**, Hermitian summands … [Tropp2015, Theorem 6.6.1]
(the i.i.d. form, the same bound).
Result: matrix-bernstein-without-replacement -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective
    [Nonempty m] (hι : …) (hL : 0 < L) (hX : …) (hsum : …) (hle : …) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ j, X (ι ω j)) 0} ≤
      Fintype.card m * Real.exp (-(t ^ 2 / 2) /
        ((Fintype.card k : ℝ) / Fintype.card n * specNorm (∑ i, X i ^ 2) + L * t / 3))

theorem integral_eigenvalue_zero_sum_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty m] … :
    ∫ ω, eigenvalue (∑ j, X (ι ω j)) 0 ∂μ ≤
      √(2 * ((Fintype.card k : ℝ) / Fintype.card n * specNorm (∑ i, X i ^ 2)) *
        Real.log (Fintype.card m)) + L * Real.log (Fintype.card m) / 3

/-- Rectangular, through the dilation: $\mathbf{S} : n \to \Bbbk^{q\times r}$ with
$\sum_i\mathbf{S}_i = \mathbf{0}$, $\|\mathbf{S}_i\|_2 \le L$, variance
$v = (\lvert k\rvert/\lvert n\rvert)\max(\|\sum_i\mathbf{S}_i\mathbf{S}_i^{\mathsf{H}}\|_2,
\|\sum_i\mathbf{S}_i^{\mathsf{H}}\mathbf{S}_i\|_2)$, dimension $\lvert q\rvert + \lvert r\rvert$.
[Tropp2015, Theorem 6.1.1] (the i.i.d. form). -/
theorem measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty r]
    {S : n → Matrix q r 𝕜} (hι : …) (hL : 0 < L) (hsum : ∑ i, S i = 0)
    (hle : ∀ i, specNorm (S i) ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ j, S (ι ω j))} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(t ^ 2 / 2) /
        ((Fintype.card k : ℝ) / Fintype.card n *
          max (specNorm (∑ i, S i * (S i)ᴴ)) (specNorm (∑ i, (S i)ᴴ * S i)) + L * t / 3))

theorem integral_specNorm_sum_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty r] … :
    ∫ ω, specNorm (∑ j, S (ι ω j)) ∂μ ≤ √(2 * v * Real.log d) + L * Real.log d / 3
    -- v and d = card q + card r written out as above

/-- **Bernstein's inequality without replacement**, the $1\times 1$ case (Hoeffding 1963's
setting): for $a : n \to \mathbb{R}$ with $\sum_i a_i = 0$, $a_i \le L$ … -/
theorem measureReal_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective {a : n → ℝ} (hι : …)
    (hL : 0 < L) (hsum : ∑ i, a i = 0) (hle : ∀ i, a i ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ j, a (ι ω j)} ≤
      Real.exp (-(t ^ 2 / 2) / ((Fintype.card k : ℝ) / Fintype.card n * ∑ i, a i ^ 2 + L * t / 3))
```
No `card k ≤ card n`: the zero law forces $\mu = 0$ (S5 Q8). Lower tails by $\mathbf{X} \mapsto
-\mathbf{X}$ (a corollary only if a consumer asks; the rectangular form covers two-sided Hermitian
use).

The **Chernoff means** without replacement, `ChernoffWithoutReplacement.lean` (299 lines; +60),
from its trace bound and `Laplace.lean`'s `integral_eigenvalue_zero_le`, `le_integral_eigenvalue`:
```lean
theorem integral_eigenvalue_zero_sum_le_chernoff_of_hasLaw_uniformOn_injective [Nonempty m]
    (hι : …) (hL : 0 < L) (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • 1) :
    ∫ ω, eigenvalue (∑ j, X (ι ω j)) 0 ∂μ ≤
      (Real.exp 1 - 1) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 +
        L * Real.log (Fintype.card m)

theorem le_integral_eigenvalue_sum_chernoff_of_hasLaw_uniformOn_injective
    (hι : …) (hk : Fintype.card k ≤ Fintype.card n) (hL : 0 < L) (hpsd : …) (hle : …) {j : ℕ}
    (hj : j + 1 = Fintype.card m) :
    (1 - Real.exp (-1)) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) j -
      L * Real.log (Fintype.card m) ≤ ∫ ω, eigenvalue (∑ j', X (ι ω j')) j ∂μ
```
(The lower mean needs `hk`: with $\mu = 0$ the left side need not be $\le 0$.)
Cited [Tropp2015, Theorem 5.1.1] (the i.i.d. means). Total Probability part: about 450 lines.

### 5.3 Spectral AMM by row sampling

`Sketching/Sampling/MatrixMultiplication.lean` (387 lines; +150). The atoms are
$\mathbf{Z}_j = (\lvert k\rvert p_{\iota_j})^{-1}\mathbf{A}_{\iota_j}^{\mathsf{H}}\mathbf{B}_{\iota_j} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}/\lvert k\rvert$; under $\|\mathbf{A}_i\|^2 \le a\,p_i$ and
$\|\mathbf{B}_i\|^2 \le b\,p_i$ (rows; a zero weight forces zero rows, so no support hypothesis),
$\|\mathbf{Z}_j\|_2 \le 2\sqrt{ab}/\lvert k\rvert$ and the variance is at most
$\max(b\|\mathbf{A}\|_2^2, a\|\mathbf{B}\|_2^2)/\lvert k\rvert$:
```lean
/-- **Approximate matrix multiplication in the spectral norm by row sampling**: for weights $p$
summing to $1$ with $\|\mathbf{A}_i\|^2 \le a p_i$ and $\|\mathbf{B}_i\|^2 \le b p_i$ for every row
$i$, $a, b \ge 0$, and $t \ge 0$,
$$\mathbb{P}\bigl[t \le \|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B}
- \mathbf{A}^{\mathsf{H}}\mathbf{B}\|_2\bigr] \le (\lvert q\rvert + \lvert r\rvert)
\exp\Bigl(-\frac{\lvert k\rvert t^2/2}{\max(b\|\mathbf{A}\|_2^2, a\|\mathbf{B}\|_2^2)
+ 2\sqrt{ab}\,t/3}\Bigr)\,.$$
At $p_i \propto \|\mathbf{A}_i\|^2 + \|\mathbf{B}_i\|^2$ this is the stable-rank form.
[MartinssonTropp2020, §7.3, Theorem 7.2]; [Tropp2015, §6.4] (locator of the corollary to check).
Result: amm-sampling-spectral -/
theorem measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch [Nonempty k]
    [Nonempty r] (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * p i)
    (hB : ∀ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ b * p i) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(Fintype.card k * t ^ 2 / 2) /
        (max (b * specNorm A ^ 2) (a * specNorm B ^ 2) + 2 * √(a * b) * t / 3))
```
(over `𝕜`, i.i.d. rectangular Bernstein; about 100 lines).

**Why two dominations.** The Frobenius AMM takes one product domination,
`hdom : ∀ i, ‖A i‖ * ‖B i‖ ≤ L * p i` (`Sampling/MatrixMultiplication.lean:293`, `:342`), because
its only input is the second moment $\sum_i \|\mathbf{A}_i\|^2\|\mathbf{B}_i\|^2/p_i$. Matrix
Bernstein needs that uniform atom bound and, in addition, the two one-sided variances
$\|\sum_i (\|\mathbf{B}_i\|^2/p_i)\mathbf{A}_i^{\mathsf{H}}\mathbf{A}_i\|_2$ and
$\|\sum_i (\|\mathbf{A}_i\|^2/p_i)\mathbf{B}_i^{\mathsf{H}}\mathbf{B}_i\|_2$. The product domination
does not bound them: a row with $\|\mathbf{A}_i\|$ large and $\|\mathbf{B}_i\|$ small passes it but
makes the second variance large. Separate dominations bound the variances by
$b\|\mathbf{A}\|_2^2$ and $a\|\mathbf{B}\|_2^2$, and they imply the product one with
$L = \sqrt{ab}$. Any consumer inherits this, among them `LowRank-S9.md` D1 and D2: their sampling
distributions must dominate each side separately ($p_i \propto \|\mathbf{A}_i\|^2 +
\|\mathbf{B}_i\|^2$, or ridge leverage scores of both factors), not the product of the row norms.

Its without-replacement twin
`…_of_hasLaw_samplingSketchWithoutReplacement` takes uniform weights, i.e.
$\|\mathbf{A}_i\|^2 \le a/\lvert n\rvert$, through the rectangular Bernstein of §5.2 with the centred
population $(\lvert n\rvert/\lvert k\rvert)\mathbf{A}_i^{\mathsf{H}}\mathbf{B}_i -
\mathbf{A}^{\mathsf{H}}\mathbf{B}/\lvert k\rvert$ (about 60). Mean forms: not stated (no consumer).

### 5.4 Spectral AMM for the SRHT

Two pieces. **General-matrix flattening** (`Structured/Flattening.lean`, 435 lines; +60;
`LowRank-S9.md` D3's "row-norm flattening lemma for a general matrix"): the existing proof of
`measureReal_exists_leverageScore_mul_diagonal_gt_le_of_hasLaw_rademacherVector` already bounds
$\|\mathbf{M}_i\boldsymbol{\xi}\|^2$ by Hsu–Kakade–Zhang with
$\|\mathbf{M}_i\|_{\mathsf{F}}^2 \le \beta\|\mathbf{A}\|_{\mathsf{F}}^2/\lvert n\rvert$ and
$\|\mathbf{M}_i\|_2^2 \le \beta\|\mathbf{A}\|_2^2/\lvert n\rvert$; for a general $\mathbf{A}$ it
reads, with a new named bound,
```lean
/-- The **flattened row-norm bound** <!-- value srhtRowNormBound A t -->
$\|\mathbf{A}\|_{\mathsf{F}}^2 + 2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{t} +
2\|\mathbf{A}\|_2^2 t$; at an orthonormal $\mathbf{U}$ of rank $d$ it is $d + 2\sqrt{dt} + 2t$,
the bracket of `NLAlib.srhtRowBound`. -/
noncomputable irreducible_def srhtRowNormBound (A : Matrix n r 𝕜) (t : ℝ) : ℝ :=
  frobNorm A ^ 2 + 2 * frobNorm A * specNorm A * √t + 2 * specNorm A ^ 2 * t

theorem measureReal_exists_norm_mul_diagonal_mul_apply_sq_gt_le_of_hasLaw_rademacherVector
    (hF : IsBoundedOrthonormal F β) (hξ : HasLaw ξ (rademacherVector n) μ) (A : Matrix n r 𝕜)
    (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹ <
      ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * A) i)‖ ^ 2} ≤
      Fintype.card n * Real.exp (-t)
```
(the leverage-score form becomes its corollary at $\mathbf{U}$'s orthonormal basis; rule 6, name
kept). **The SRHT spectral AMM** (`Structured/SRHTMultiplication.lean`): condition on the signs
(`srht_eq_map_prod`), apply §5.3's without-replacement form to $\mathbf{F}\mathbf{D}\mathbf{A}$,
$\mathbf{F}\mathbf{D}\mathbf{B}$ on the flattening event of both:
```lean
theorem measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_srht [Nonempty r]
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ) (A : Matrix n q 𝕜)
    (B : Matrix n r 𝕜) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(Fintype.card k * t ^ 2 / 2) /
        (max (β * srhtRowNormBound B s * specNorm A ^ 2) (β * srhtRowNormBound A s * specNorm B ^ 2) +
          2 * β * √(srhtRowNormBound A s * srhtRowNormBound B s) * t / 3)) +
      2 * Fintype.card n * Real.exp (-s)
```
For $\mathbf{A} = \mathbf{B}$ with $\|\mathbf{A}\|_2 = 1$ and stable rank $r_s$ this is
$\lvert k\rvert = O(\beta(r_s + \log(n/\delta))\log((q + r)/\delta)/\varepsilon^2)$, the SRHT OSE
size with $d$ replaced by $r_s$. About 150 lines with the with-replacement twin (same proof through
the i.i.d. Bernstein).

### 5.5 What M4 makes reachable downstream, and the recommendation

| Item | Needs beyond M4 | Recommendation |
|---|---|---|
| `LowRank-S7.md` D5: late-truncated GN, spectral noise term (T11 needs spectral AMM) | a generic statement taking a spectral multiplication tail; per-family instances | **record** (S7 cut D5 as additive; no consumer asked) |
| `LowRank-S9.md` D2: column-sampling PCP by CEMMP's route | ridge-leverage sampling distribution, the CEMMP reduction; S9 also has a route without spectral AMM | **record** |
| `LowRank-S9.md` D1 for the SRHT: head–tail PCP at $(k + \log(n/\delta))\log(k/\delta)/\varepsilon^2$ through stable-rank spectral AMM | CEMMP Lemma 10's reduction (frame of width $2k$, scaled tail, trace condition), 600 to 900 lines | **record**; M4 supplies the SRHT AMM it takes, dense families still need CNW |
| SRHT $(1+\varepsilon)$ RSVD / early truncation at $\log(1/\delta)$ through spectral AMM ($\|\cdot\|_{\mathsf{F}} \le \sqrt{k}\|\cdot\|_2$ on the rank-$k$ multiplication error) | none, but quadratic in $k$ ($\beta k(k + \log)\log/\varepsilon$); the §3.4 JL-moment forms are linear in $k$ at $1/\delta$ | **record**: incomparable, add on demand |
| Hutch++ with SRHT, CountSketch or sampling sketches (sketching survey 4.3) | with the existing constant-factor range finders it is assembly, but SRHT's and sampling's fail with $\delta + 1/t$; a $\log(1/\delta)$ SRHT version needs a constant-factor SRHT range finder through $\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2$ controlled by §5.2's scalar Bernstein without replacement after §5.4's flattening (about 150) | **record** for an Estimation pass; CountSketch's is pure assembly and can go there too |
| Random row pavings for block Kaczmarz (`Regression-Kaczmarz.md` §6) | an `IsRowPaving` interface | **record** |

So M4's in-round consumers are the two spectral AMM tails themselves; everything downstream is
recorded with its exact need.

## 6. Files and placement

Placement by topic: probability statements in Probability (and RandomMatrix, untouched here),
sketch statements in Sketching, consumers where their topic lives.

| File | Change | Lines (now → about) | Reason |
|---|---|---|---|
| `ForMathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` | `Real.Gamma_le_rpow_sub_one` | +40 | scalar Gamma fact (P9), upstream candidate |
| `ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean` | `Real.log_one_add_le_sub_sq_div` | +15 | beside the other log inequalities |
| `Probability/Tail.lean` | `subexponentialMomentBound` and API, `integral_rpow_le_of_measureReal_ge_le`, `integral_rpow_le_of_measureReal_ge_le_two_mul_exp`, `measureReal_abs_div_sub_one_ge_le_two_mul_exp` | 325 → 525 | layer-cake moments and tail conversions of a scalar variable |
| `Probability/SubExponential/Tail.lean` | `HasSubexponentialMGF.integral_abs_rpow_le` | +15 | API of the sub-exponential predicate |
| `Probability/MatrixConcentration/Bernstein.lean` | two trace-form statements | 399 → 490 | the Bernstein topic |
| `Probability/MatrixConcentration/BernsteinWithoutReplacement.lean` | new: §5.2 | 300 | sibling of `ChernoffWithoutReplacement.lean` |
| `Probability/MatrixConcentration/ChernoffWithoutReplacement.lean` | two means | 299 → 360 | its topic |
| `Sketching/Properties/JohnsonLindenstrauss.lean` | `hasJLMoment_of_forall_hasJLProperty`, `IsObliviousSubspaceEmbedding.hasJLProperty` | 495 → 570 | JL and its relation to OSEs |
| `Sketching/Gaussian/Gaussian.lean` | `jlMomentDim` and API, public `two_mul_twentyOne_pow_mul_exp_le_of_jlDim_le`, the Gaussian high-order moment and size, **minus** its PCP section | 914 → about 900 | Gaussian family |
| `Sketching/Gaussian/Rademacher.lean` | the helper moves out (now private there) | 406 → 390 | — |
| `Sketching/Gaussian/SubGaussian.lean` | `subgaussianJLMomentDim`, moment, size, **minus** its PCP section | 895 → about 830 | sub-Gaussian family |
| `Sketching/Gaussian/Haar.lean` | Haar high-order moment and size | 428 → 520 | Haar JL results live here |
| `Sketching/Gaussian/HaarEmbedding.lean` | Haar OSE/OSI tail and size forms | 687 → 870 | Haar embeddings |
| `Sketching/Gaussian/ProjectionCost.lean` | **new (flag, §8 Q6)**: the Gaussian and sub-Gaussian PCP statements moved from their family files, Haar PCP, the three `_of_…JLMomentDim_le` twins, asymptotic forms | about 650 | PCPs of the dense families; the two family files would pass 1000 lines otherwise |
| `Sketching/Sampling/MatrixMultiplication.lean` | spectral AMM, both models | 387 → 540 | AMM by sampling |
| `Sketching/Structured/Flattening.lean` | `srhtRowNormBound`, general-matrix flattening | 435 → 500 | flattening |
| `Sketching/Structured/SRHTMultiplication.lean` | **new**: SRHT JL tail, size, asymptotic; JL moment; PCP; spectral AMM | about 550 | the SRHT as a JL and multiplication sketch; `SRHT.lean` is at 1050 |
| `Regression/SRHT.lean` | SRHT relative-error sketch-and-solve + asymptotic | 206 → 330 | SRHT regression corollaries |
| `Regression/SubGaussian.lean` | sub-Gaussian relative-error sketch-and-solve + asymptotic | 181 → 300 | family file |
| `Regression/Gaussian.lean` | `_of_jlMomentDim_le` twin; asymptotic upgraded | 287 → 340 | family file |
| `Regression/Haar.lean` | **new**: Haar S&P (3), Haar sketch-and-solve HP (2) | about 250 | per-family regression files |
| `LowRank/Oblivious/Gaussian.lean`, `SubGaussian.lean` | twins; asymptotic upgraded | 189 → 240, 689 → 800 | family files |
| `LowRank/Oblivious/SRHT.lean` | SRHT $(1+\varepsilon)$ RSVD, early truncation, asymptotic | 180 → 380 | family file |
| `LowRank/Oblivious/Haar.lean` | **new**: Haar early truncation + asymptotic | about 120 | per-family oblivious files; S7 §4 noted its absence |

The private product-law helpers of `SRHT.lean:281–308` (`hasLaw_fst_prod`, `hasLaw_snd_prod`,
`indepFun_snd_mul_diagonal`, `hasLaw_map_prod`) become public when `SRHTMultiplication.lean` needs
them: the first two in `Probability/Law.lean` (generic `HasLaw` facts), the others stay in
`SRHT.lean` as public SRHT API. No flag remains open after the round except Q6's if the maintainer
prefers a different split.

## 7. Material

* **Quarry** (`atlas/declarations.json`, read): `Sketching.Properties.JL.JL` (8, ported in S1/S2),
  `Sketching.Properties.ApproxMatrixMultiplication.ApproxMultiplication` (4; its $L^p$ step is the
  private helper of `MatrixMultiplication.lean`), `Sketching.Sampling.SamplingMultiplication(Bounds)`
  (Frobenius only, ported in S4), `Sketching.Sampling.SamplingWithoutReplacement(Tails)` (Chernoff
  only, ported in S5; the two-sided population form cut, S5 §6),
  `Probability.Concentration.Matrix.MatrixBernstein` (i.i.d., ported in P5a),
  `RandomMatrix.SubGaussian.SubGaussianJL` (superseded), `Sketching.Structured.SRHT*` (ported in
  S6). **Nothing to reuse** for M1 (no JL moment beyond $p = 2$ anywhere in the quarry), M2 (no SRHT
  JL or AMM), M4 (no Bernstein without replacement, no spectral AMM). Not reproduced: nothing.
* **Library proofs reused**: the sub-Gaussian absolute-moment proof (`SubGaussian/Moments.lean:64`)
  for the layer cake; Chernoff without replacement (`ChernoffWithoutReplacement.lean:102`) line for
  line for the Bernstein trace bound; the sign file's OSE size proof for Haar; the flattening proof
  for general matrices.
* **Sources**: as cited in each docstring, with the locators of `docs/PORT_SKETCHING.md` §7.1
  (Woodruff Definitions 2, 3, 12, Theorems 7, 13, 23; MT §7.3 Theorem 7.2, §8.6, §9.3; Tropp 2015
  Theorems 5.1.1, 6.1.1, 6.6.1, Lemma 6.6.2). Kane and Nelson 2014 (the JL moment property at
  $p = \log(1/\delta)$) is not in `docs/references.bib` and not in hand; cited by name with
  "locator to check", or added as a key if the PDF is fetched.

## 8. Other decisions, with recommendations (proceed unless corrected)

**Q0. The tail hypothesis of the tail-to-moment lemma**. The hypothesis is a family of
JL tails, `∀ t, 0 < t → HasJLProperty S t (2 * rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b)))) μ`,
written with the existing interface. It appears once, in `hasJLMoment_of_forall_hasJLProperty`
(§2.4), and the family proofs establish it inside their own proofs. Options: (a) as stated, with no
predicate; (b) a predicate `HasSubexponentialJLTail S v b μ`; (c) an $L^p$-norm restatement of
`HasJLMoment` (a second spelling, rejected by §1 rule 4). Recommendation (a): one occurrence is not
an interface (§1 rule 2 says "a second time"). If a second consumer appears, the predicate is a
one-field structure.

**Q1. Which families get $p > 2$.** Gaussian, Haar, sub-Gaussian (signs through it). CountSketch
cannot (no tail beyond Chebyshev); the SRHT's tail has a floor (§3.3). Recommendation as stated.

**Q2. Gaussian and Haar through Dasgupta–Gupta tails, not through an MGF.** The Gaussian could use
the exact χ² Laplace transform to get `HasSubexponentialMGF`; Haar has no MGF in the library. One
Probability lemma (§2.3) serves both. Recommendation: the tail route.

**Q3. OSE → JL bridge strictness.** Strict hypotheses `1 - ε < a`, `b < 1 + ε`; the SRHT tail
recovers the non-strict endpoint by continuity of its bound (§3.2). Alternative: change
`HasJLProperty`'s event to strict (an interface change across S1 to S9). Recommendation: strict
hypotheses.

**Q4. SRHT JL moment by direct computation** (§3.3), not by integrating the §3.2 tail.
Recommendation as stated; field ℝ unless the complex fourth moment is cheap.

**Q5. Names.** Proposed above; the coexisting-forms names follow N8 and need the checker at the
skeleton: `hasJLMoment_subexponentialMomentBound_of_…` (beside the `p = 2` `hasJLMoment_of_…`),
`isObliviousSubspaceEmbedding_one_sub_one_add_of_hasLaw_haarFrame` (beside Gordon's
`isObliviousSubspaceEmbedding_of_hasLaw_haarFrame`), `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht_of_le_card`
(beside the constant-factor `…_of_hasLaw_srht`), `_of_jlMomentDim_le` for the M1 twins.
Recommendation: as proposed; alternatives decided at the skeleton.

**Q6. The dense-family PCP file.** Options: (a) new `Sketching/Gaussian/ProjectionCost.lean`
holding the Gaussian, sub-Gaussian and Haar PCPs (moved, names unchanged); (b) keep each PCP in
its family file and split `Gaussian.lean` and `SubGaussian.lean` otherwise; (c) accept files of
about 1100 lines (F10 is a warning). Recommendation (a), recorded as a dated amendment of the S1/S3
file lists.

**Q7. Bernstein without replacement on a centred population** (`∑ i, X i = 0`). Alternative: any
population with the mean subtracted in the statement (`∑ j, X (ι ω j) - (card k / card n) • ∑ i, X i`),
which consumers would rewrite into anyway. Recommendation: centred; the sampling AMM consumer
centres its atoms in one line.

**Q8. Scope of consumers this round.** The full scope is the recommended default: M1 core and the
six twins with upgraded asymptotic forms (MD4), sub-Gaussian sketch-and-solve, M2 with the four
SRHT assemblies (§3.4), M3 with the three Haar corollaries and Haar sketch-and-solve with high
probability, and M4 with the two spectral AMM tails. Everything in §5.5 is recorded. This is
about 4,000 to 4,500 lines in five stages (M1 core; M3; M2; M4; consumer twins). The stages run
in sequence. After M1 core they are independent, except that M3's PCP and early-truncation twins
and §2.6 wait for M1. Fallback if the maintainer wants the round smaller: M1 core with the six
twins, M3, and M2 with §3.4 (about 2,900 lines). M4 is then deferred whole to the round that
consumes it; its only in-round consumers are its own two spectral AMM tails (§5.5).

**Q9. No per-family AMM statements.** AMM is the generic tail applied to each size form;
module docstrings show the two lines. Recommendation as stated.

**Q10. Mathlib deviations.** None: the new objects are named bounds and theorems; no Mathlib notion
is re-spelled. `docs/design/Mathlib-deviations.md` gets no entry.

## Changes during the skeleton (2026-10-22)

The skeleton is on `sketching/moments` (worktree `nlalib-block`, from `1e5334f`). Every declaration
of §§2–5 and §6 is stated with its final docstring and elaborates; definitions are written out in
full; the statements listed under "Proved now" are proved, the others are `sorry`. Changes against
the note:

* **Measure hypotheses.** The three §2.3 Probability lemmas and
  `hasJLMoment_of_forall_hasJLProperty` take `[IsFiniteMeasure μ]` in place of
  `[IsProbabilityMeasure μ]` (weaker; finiteness is what the `μ.real` tails need).
  `IsObliviousSubspaceEmbedding.hasJLProperty` takes `[IsFiniteMeasure μ]`, against §3.1's "no
  finite-measure hypothesis": with `μ.real`, an infinite-measure failure event has real measure
  $0$, so without finiteness the implication fails. Every consumer has a probability measure.
  The Bernstein trace forms (§5.2) take `[IsProbabilityMeasure μ]` and write their bound variable
  `∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) → …` (T10).
* **`Real.Gamma_le_rpow_sub_one`** needs Mathlib's `Real.convexOn_Gamma`, so
  `ForMathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` now also imports
  `Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup`; its module docstring names that file as
  the upstream home of the new bound. `Probability/Tail.lean` imports the ForMathlib Gamma and log
  files and `Mathlib.Analysis.Complex.ExponentialBounds` (for $\log 2 > 0.693$), as do
  `Gaussian.lean` and `SubGaussian.lean` (the latter two for `jlMomentDim_le` and
  `subgaussianJLMomentDim_le`).
* **Named-bound API.** `subexponentialMomentBound_nonneg` ($v, b, p \ge 0$),
  `subexponentialMomentBound_mono` (in $v$ and $b$, $p \ge 0$), `subexponentialMomentBound_le` as
  in MD2, and one more lemma, **`subexponentialMomentBound_le_mul_exp_neg`**: for $p \ge 2$,
  $32vp \le \varepsilon^2$ and $32bp \le \varepsilon$ the bound is at most $\varepsilon^p e^{-p}$.
  It is the inversion step the three family size forms share (S5: one public lemma, not three
  copies); it goes through `subexponentialMomentBound_le`, so a sharper body leaves it true.
  `jlMomentDim_nonneg` (no hypothesis), `jlMomentDim_mono` (antitone in $\varepsilon > 0$ and
  $\delta > 0$; no $\varepsilon \le 1$ needed), `jlMomentDim_le`
  ($\le 384\log(1/\delta)/\varepsilon^2$ for $0 < \delta \le 1/2$); `subgaussianJLMomentDim_nonneg`,
  `_mono` (monotone in $c \ge 0$), `_le` ($\le 1728c^2\log(1/\delta)/\varepsilon^2$). The registry
  template of `subexponentialMomentBound` writes the second power as `(2#2)^{#3}`, so docstrings
  show $(2b)^{p}$ with braces.
* **Files.** As §6. The PCP section of `Gaussian.lean` and `SubGaussian.lean` (with the private
  empty-column helper) moved to the new `Sketching/Gaussian/ProjectionCost.lean` (Q6 (a)); the two
  family files no longer import `Sketching/Properties/ProjectionCost.lean`. `srhtRowNormBound`
  and the general flattening sit in a new section of `Flattening.lean` after the variables
  (the definition takes the file's `{n r 𝕜}`); its value is displayed (`$$…$$`) wherever it
  appears, since the filled template does not fit an inline span of 100 characters. The private
  product-law helpers of `SRHT.lean` stay private: the note's `hasLaw_fst_prod`,
  `hasLaw_snd_prod` do not exist under those names (the helpers are `indepFun_snd_mul_diagonal`,
  `measurable_mul_diagonal_fst`, `hasLaw_map_prod`, `mul_diagonal_eq`), and §6 makes them public
  only when `SRHTMultiplication.lean` needs them, which is a proof-time step.
* **Asymptotic thresholds.** The PCP forms state the single product term
  $C(d+1)\log(1/\delta)/\varepsilon^2$ (sub-Gaussian $Cc^2(d+1)\log(1/\delta)/\varepsilon^2$): §2.6's
  first summand $C(d + \log(1/\delta))/\varepsilon^2$ is dominated by it for $\delta \le 1/2$. The
  LowRank forms use $Ck\log(1/\delta)/\varepsilon^2$ (Gaussian, Haar early truncation),
  $Cc^2k\log(1/\delta)/\varepsilon$ and $Cc^2k\log(1/\delta)/\varepsilon^2$ (sub-Gaussian), with
  $k = 0$ trivial; sketch-and-solve $C(r+1)\log(1/\delta)/\varepsilon$ (Gaussian, Haar) and
  $Cc^2(r+1)\log(1/\delta)/\varepsilon$ (sub-Gaussian). The note gave no threshold for the SRHT
  forms; they are the OSE/OSI size plus the JL-moment size,
  $C(\beta(d + \log(\lvert n\rvert/\delta))\log(d/\delta)/\varepsilon^2 + \beta^2(d+1)/(\varepsilon^2\delta))$
  (PCP), $C(\beta(r + \log(\lvert m\rvert/\delta))\log(r/\delta) + \beta^2(r+1)/(\varepsilon\delta))$
  (sketch-and-solve), and the corresponding $k$ forms for the randomized SVD and early truncation;
  the SRHT JL form is $C\beta(1 + \log(\lvert n\rvert/\delta))\log(1/\delta)/\varepsilon^2$.
  Constants are left to the proofs (not stated in the asymptotic docstrings).
* **Statement details.** The SRHT JL moment, PCP, sketch-and-solve, randomized SVD and early
  truncation are over ℝ (Q4 default); the SRHT JL tails and spectral AMM over `𝕜`. The SRHT size
  hypotheses are the family's own named sizes with the failure split the proofs use:
  `samplingEmbeddingDim 1 (β * srhtRowBound (card n) 1 (δ / 2)) ε (δ / 2)` (JL),
  `samplingEmbeddingDim d (β * srhtRowBound (card n) d (δ / 4)) (ε / 2) (δ / 4)` (PCP),
  `samplingInjectionDim r (β * srhtRowBound (card m) r (δ / 4)) (1 / 2) (δ / 4)` with
  `8 * (3 * β ^ 2 - 1) * (r + 1) ≤ ε * δ * card k` (sketch-and-solve; the randomized SVD has the
  same with $k$), and `samplingInjectionDim k (β * srhtRowBound (card n) k (δ / 6)) (ε / 6) (δ / 6)`
  with `108 * (3 * β ^ 2 - 1) * k ≤ ε ^ 2 * δ * card l` (early truncation). The sampling spectral
  AMM without replacement takes `‖A i‖² ≤ a * (card n)⁻¹`, the without-replacement file's form of
  uniform weights; both sampling models and both SRHT models take `[Nonempty r]`, the
  with-replacement ones also `[Nonempty k]`. The rectangular Bernstein without replacement needs
  no `DecidableEq` on the factor index types. The Haar early truncation states its injection size
  as `jlDim (2 * ε / 15) (δ / 3 / 21 ^ k)`, the size form of the Haar OSI at $\varepsilon/6$ (since
  $4(\varepsilon/6)/5 = 2\varepsilon/15$). Haar sketch-and-solve with high probability uses the
  unnormalized $\mathbf{Q}^{\mathsf{H}}$ (as the expectation forms do), sizes
  `jlDim (2 / 5) (δ / 2 / 21 ^ A.rank)` and `jlMomentDim (√(ε / (4 * (A.rank + 1)))) (δ / 2)`, and
  `ε ≤ 4`. Sub-Gaussian sketch-and-solve is stated once, in the $\log(1/\delta)$ form, under the
  plain name `measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_isSubgaussianVector` (no
  coexisting form to tell apart), with `[Nonempty k]` and `ε ≤ 4`.
* **Docstrings of the old explicit forms.** The six $1/\delta$ explicit theorems no longer say
  "Asymptotic form: …" (`scripts/check_refs.py` requires the named form's tag to point back); each
  names its $\log(1/\delta)$ twin as incomparable (rule 4) and says that the asymptotic form is
  proved from the twin. The JL-moment asymptotic forms and the SRHT JL asymptotic forms carry a
  citation for C1 ([Woodruff2014, Definition 12 and Theorem 13]; [Woodruff2014, Theorem 7];
  [MartinssonTropp2020, §9.3]).
* **Citations.** `KaneNelson2014` is added to `docs/references.bib` from the metadata of
  `docs/PORT_SKETCHING.md` §7.2 only (surnames, title, J. ACM 61, 2014), with a `note` that the
  given names, issue, article number and DOI are to confirm; it is cited bare in the module
  docstring of `JohnsonLindenstrauss.lean`, and declaration docstrings say "Kane and Nelson's
  (2014; locator to check)". The SRHT spectral AMM has no printed source in the note: its
  docstrings cite [Tropp2011a, Lemma 3.3] for flattening and say the bound is the proof's. The
  scalar Bernstein without replacement cites [Hoeffding1963, Theorem 4], the locator the library
  already uses (`ConvexOrder.lean`). No new locator was invented.
* **Result ids.** New: `jl-moment-gaussian`, `jl-moment-haar`, `jl-moment-subgaussian`, `jl-srht`,
  `haar-pcp`, `srht-pcp`, `matrix-bernstein-without-replacement`, `amm-sampling-spectral`,
  `amm-srht-spectral`. Reused: `haar-sketch-ose`, `haar-sketch-osi`, `gaussian-pcp`,
  `subgaussian-pcp`, `sketch-and-solve-ls`, `sketch-and-precondition-ls`, `etrsvd`,
  `randomized-svd-tail`.
* **Signs.** No statement (§2.4): the module docstring of `Rademacher.lean` shows the discharge of
  `hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le` at $c = 1$.
* **Proved now.** ForMathlib: `Real.Gamma_le_rpow_sub_one`, `Real.log_one_add_le_sub_sq_div`.
  Probability: everything of §2.3 (the four bound lemmas, the layer cake, the sub-exponential
  moments, the Dasgupta–Gupta conversion, `HasSubexponentialMGF.integral_abs_rpow_le`), the two
  Bernstein trace forms and the two Chernoff means without replacement. Sketching: both
  `JohnsonLindenstrauss.lean` bridges; the Gaussian, Haar and sub-Gaussian JL moments at every
  order, their size forms and asymptotic forms, the `jlMomentDim` and `subgaussianJLMomentDim`
  API, the public `two_mul_twentyOne_pow_mul_exp_le_of_jlDim_le`; the five Haar
  $1 \mp \varepsilon$ embedding statements of §4.2; `srhtRowNormBound_nonneg` and the general
  flattening (two private row lemmas for a general matrix; the leverage-score form is not yet
  rederived from it, both are proved). Regression: Haar sketch-and-precondition and its
  sketch-and-solve start. The moved PCP proofs are unchanged. So `Probability/Tail.lean`,
  `JohnsonLindenstrauss.lean`, the four dense family files, `Flattening.lean`, `Bernstein.lean`
  and `ChernoffWithoutReplacement.lean` stay sorry-free.
* **Asymptotic forms left `sorry`.** All six upgraded in place (MD4): the Gaussian and
  sub-Gaussian PCP, Gaussian sketch-and-solve, Gaussian early truncation, sub-Gaussian randomized
  SVD and early truncation; their old proofs were for the $1/\delta$ thresholds and are replaced by
  `sorry` until the twins are proved.
* **Review warnings left.** B5 now flags the three $1/\delta$ PCP forms and the two sub-Gaussian
  LowRank $1/\delta$ forms (their asymptotic forms are tagged to the $\log(1/\delta)$ twins, MD4)
  and `isObliviousSubspaceEmbedding_one_sub_one_add_of_hasLaw_haarFrame` (a tail form; its size
  form has the asymptotic form). Checks at the skeleton: `lake build NLAlib` 3995 jobs, 48 `sorry`
  warnings and no other; `check_rules.py` on the extraction 0 errors (names included);
  `check_refs.py`, `check_constants.py`, `gen_rules_md.py --check`, `mk_all --check` clean;
  `proved_modules.py`: 383 proved, 13 not yet (the 12 files with `sorry` and
  `Estimation/Trace/HutchPlusPlusTail.lean`, which imports `LowRank/Oblivious/SubGaussian.lean`).

## Changes during the proofs (2026-10-22)

* **SRHT helper made public** (proof agent B): `NLAlib.measureReal_le_one_of_hasLaw_srht`
  (`Sketching/Structured/SRHT.lean`), every event has probability at most one under the SRHT law;
  `SRHTMultiplication.lean` needs it for the JL tail at $\varepsilon = 0$ and the size forms.
* **SRHT size arithmetic made public** (proof agent B): `NLAlib.samplingEmbeddingDim_srhtRowBound_le`
  (`Sketching/Structured/SRHT.lean`), the bound
  $72\beta(d + \log(\lvert n\rvert/\delta))\log(d/\delta)/\varepsilon^2$ on the flattened
  row-sampling size, extracted from the two SRHT OSE asymptotic proofs (which now cite it) and
  used by the SRHT JL and PCP asymptotic forms. `SRHTMultiplication.lean` also imports
  `Probability/QuadraticForm/Moments.lean` (the Rademacher fourth moment of the JL moment proof).
  The product-law helpers of `SRHT.lean` stay private: the proofs restate the two one-line facts
  they need.
* **SRHT injection-size arithmetic made public** (proof agent B):
  `NLAlib.samplingInjectionDim_srhtRowBound_le` (`Sketching/Structured/SRHT.lean`), the bound
  $32\beta(d + \log(\lvert n\rvert/\delta))\log(d/\delta)/\varepsilon^2$ on the flattened
  row-sampling injection size, extracted from the two SRHT OSI asymptotic proofs (which now cite
  it) and used by the SRHT sketch-and-solve, randomized SVD and early-truncation asymptotic forms.
* **Empty-column PCP made public** (round close, 2026-10-22):
  `NLAlib.hasProjectionCostPreserving_of_isEmpty`, every sketch is a projection-cost-preserving
  sketch when $n$ is empty, was a private helper of `Sketching/Gaussian/ProjectionCost.lean`. It
  moves to `Sketching/Properties/ProjectionCost.lean`, next to the definition, and is stated over
  any `RCLike` field instead of $\mathbb{R}$.
* **Shared $(1 + \varepsilon)$ forms made public** (round close, 2026-10-22): the early-truncation
  and sketch-and-solve family proofs repeated one body each, with only the JL size form or the
  sketch family swapped. Two generic theorems now carry it, each at a rescaled sketch
  $c\,\mathbf{\Omega}$ so that a family's normalisation stays inside:
  `NLAlib.HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le`
  (`LowRank/Oblivious/EarlyTruncation.lean`; injection at $1 - \varepsilon/6$, JL moment at
  $\varepsilon/(6\sqrt{k})$, failure $\delta + 2\delta'$), used by the Gaussian (both forms), Haar,
  sub-Gaussian (both forms) and SRHT early truncation; and
  `NLAlib.HasJLMoment.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_one_add_mul_le`
  (`Regression/Oblivious.lean`; injection constant $a \ge 1/2$, JL moment at
  $\sqrt{\varepsilon/(4(r+1))}$, failure $\delta + \delta'$), used by the Gaussian (both forms),
  Haar and sub-Gaussian sketch-and-solve. No public statement changed. The SRHT sketch-and-solve
  and the sub-Gaussian randomized SVD pair keep their proofs: what they would share beyond the
  existing generic `NLAlib.HasJLMoment.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le` and
  `NLAlib.HasJLMoment.measureReal_frobNorm_sub_rsvd_sq_gt_le` is a few lines.
* **Duplicated helpers made public** (final review, 2026-10-22; rule S5). Each replaces private
  copies in two or more files; no public statement changed.
  `NLAlib.HasOrthonormalCols.hasOrthonormalCols_mul_diagonal` (`Sketching/Structured/Flattening.lean`):
  a unitary times a diagonal of signs is unitary, the deterministic step of the a.e. form, which
  now derives from it; the private copy of `SRHTMultiplication.lean` goes.
  `NLAlib.row_eq_zero_of_norm_sq_le` (`Sketching/Sampling/RowSampling.lean`): a row of zero
  weight vanishes under $\|\mathbf{b}_i\|_2^2 \le L p_i$; the private copy of
  `MatrixMultiplication.lean` goes. `Real.log_two_le_log_one_div` and
  `Real.log_two_div_le_two_mul_log_one_div` (`ForMathlib/Analysis/SpecialFunctions/Log/Basic.lean`):
  $\log 2 \le \log(1/\delta)$ and $\log(2/\delta) \le 2\log(1/\delta)$ for
  $0 < \delta \le 1/2$, which the asymptotic forms of the sketching, regression and low-rank files
  inlined some twenty times; the private `log_two_le_log_one_div` of
  `Sketching/Gaussian/ProjectionCost.lean` goes, and `Sketching/Gaussian/SubGaussian.lean` imports
  the Log file. `NLAlib.srhtRowBound_div_two_le` (`Sketching/Structured/Flattening.lean`, with the
  rest of the row bound's API): $\mathrm{srhtRowBound}(n, d, \delta/2) \le
  8(d + \log(n/\delta))$ for $n \ge 1$ and $0 < \delta \le 1/2$, the step
  `NLAlib.samplingEmbeddingDim_srhtRowBound_le` and `NLAlib.samplingInjectionDim_srhtRowBound_le`
  repeated.
* **Unused hypothesis dropped** (round close, 2026-10-22): the skeleton gave
  `NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_subgaussianJLMomentDim_le` an
  instance `[Nonempty k]` that the proof does not use (the environment linter's
  `unusedArguments`, once the file counted as proved). It is removed; the statement is otherwise
  unchanged and its callers, the asymptotic form included, are unaffected.
