# Design note: best polynomial approximation (stage Poly-Best)

Status: draft for the maintainer, 2026-10-25; skeleton written the same day (branch
`design/polybest`, from `df3f025`). Not yet reviewed by Fable.

The minimax error $E_n(f; s)$, existence of a best uniform approximant, Chebyshev's
equioscillation theorem (characterisation and uniqueness), de la Vallée Poussin's lower bound,
the interpolation property of the best approximant, and the glue that restates the existing
Lanczos-FA, Lanczos-quadrature, Gauss-rule and SLQ bounds, now stated with an arbitrary
approximant `p` and `Metric.IsUniformApproxOn … ε`, with $E_n(f)$ as the papers state them.

The gap report (`~/nlalib-harness/reports/Gaps-MatrixAnalysis-Polynomials.md`, row 2 and "Top
three" item 2) chose this stage. It is independent of KS8 (Hermite remainder, designed in
parallel); the two touch no common file except that both may add to
`NLAlib/Polynomial/Orthogonal/Gauss.lean` (here one corollary, §3.4).

Every signature in §3 is in the skeleton and elaborates: `lake build NLAlibScaffold` (with the two
new `NLAlib` modules built under `--wfail`) gives 36 `sorry` warnings and nothing else;
`scripts/check_rules.py --files` and `scripts/check_refs.py` pass on the new files. The
extraction-based name check (`check_names.py`, N1–N18) was not run (it needs
`explore_data.sh`); the names were chosen by hand against §4 and are listed for review in §9.

## 0. Summary

| | |
|---|---|
| New definitions | `minimaxError f s n` (in `NLAlib`), the predicate `AlternatesOn g s k ε` (in `NLAlib`) |
| New files | `Polynomial/Approximation/MinimaxError.lean`, `Polynomial/Approximation/Equioscillation.lean`; three ForMathlib files |
| Statements | 36 sorried (S 23, M 11, L 2, H 0), in 12 scaffold files |
| Glue | 8 corollaries in 7 existing files: Lanczos-FA, Lanczos quadrature, Gauss rule, SLQ (split and tail), Jackson, Bernstein ellipse, $1/x$ |
| Prototype | `Polynomial/BestApproximation/{Basic,MinimaxError,Affine,AlternationLowerBound,EquioscillationCertificate,ExtremalSigns,Equioscillation,AlternatingInterpolant,BestInterpolant}` and three ForMathlib files: every L/M statement here has a proved prototype counterpart (§6) |
| Mathlib overlap | none for the theory (searched, §7); reused: Weierstrass, `IsCompact.exists_isLeast`, Chebyshev `node`/`eval_T_real_node`, `Lagrange`, `eq_zero_of_degree_lt_of_eval_index_eq_zero` |
| Open questions | 7 (§10), each with a recommendation |

Three choices carry the design:

1. **$E_n$ is a function of a raw `f : ℝ → ℝ` and a set**, defined as the infimum of the errors
   `ε` for which some polynomial of degree at most `n` satisfies
   `Metric.IsUniformApproxOn (fun x => p.eval x) f s ε`. Consumers hold exactly this
   (`f : ℝ → ℝ`, `Set.Icc a a'`, the `IsUniformApproxOn` interface), so the glue is
   "`obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_minimaxError …`" and one
   application. The prototype's `C(s, ℝ)` / `Metric.infDist` form becomes the bridge
   `minimaxError_eq_infDist` (OQ1).
2. **One alternation predicate** `AlternatesOn g s k ε`: $k$ increasing points of $s$ and a sign
   $\sigma \in \{\pm1\}$ with $\varepsilon \le \sigma(-1)^i g(x_i)$. It is de la Vallée Poussin's
   hypothesis (level $\varepsilon$ a lower bound on the modulus) and, at the level
   $E_n$, the conclusion of the equioscillation theorem; one predicate replaces the prototype's
   three spellings (sign products `… * … < 0` with `ε ≤ |…|`, `σ * (-1)^i * ‖·‖` equalities,
   extremal sets) (OQ4).
3. **The glue uses $q + 1$ steps and $E_q$ / $E_{2q+1}$**, as the existing Lipschitz and analytic
   corollaries already do (`…_le_of_lipschitzOnWith`, `lanczosFA A f b (q + 1)`), so no natural
   subtraction appears (OQ3).

## 1. Scope

In: the definition and basic algebra of $E_n(f; s)$; existence of a best approximant on any
compact set; affine invariance and the change of interval to $[-1, 1]$; $E_n \to 0$ on an
interval (Weierstrass); de la Vallée Poussin (on any set, any $f$); the equioscillation theorem on
$[a, b]$ (sufficiency on any set, necessity on intervals), uniqueness, interpolation at $n + 1$
interior points; the Chebyshev example $E_n(x^{n+1}; [-1, 1]) = 2^{-n}$; $E_n$ forms of
Jackson, Bernstein-ellipse and $1/x$ upper bounds; $E_n$ forms of the five Krylov/SLQ/Gauss
bounds.

Out, deliberately (§11 has what each needs): weighted and rational best approximation; the
Lebesgue constant and near-best interpolation (ATAP 15.1, prototype `norm_sub_projection_le_minimaxError`
and the 30 `Lebesgue*`/`Interpolation*`/`Gap*` files: gap report row 6); the explicit lower
bounds ($E_n(1/x)$ exact, $\lvert x\rvert$, sign, $e^{-x}$: gap report rows 3 and 2's
"prerequisite"); Remez; Haar spaces and equioscillation on general compact sets; complex-valued
$f$ (Kolmogorov criterion); strong uniqueness and continuity of the best-approximation operator;
odd/even symmetry of best approximants; a named best-approximation function (OQ6); the
`MatchesMoments` and spectral-density (Wasserstein) restatements.

## 2. Objects

### 2.1 `minimaxError` (in `NLAlib/Polynomial/Approximation/MinimaxError.lean`, written)

```lean
noncomputable def minimaxError (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : ℝ :=
  sInf {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
    Metric.IsUniformApproxOn (fun x => p.eval x) f s ε}
```

Junk values (in the docstring): $0$ when no polynomial of degree at most $n$ is within a finite
distance of $f$ on $s$ (the set is empty), and $0$ for $s = \emptyset$ (the set is $\mathbb{R}$,
not bounded below, and Mathlib's `Real.sInf` is $0$). Everywhere else it is the true value: if
some $p_0$ is within finite distance, polynomials that are not (e.g. degree-$n$ growth on an
unbounded $s$) simply do not contribute. This is why the `sInf`-of-errors form was preferred to
the `⨅ p, ⨆ x ∈ s, |f x - p.eval x|` form of `residualMinimax`: there an unbounded error of one
$p$ has supremum $0$ (Mathlib's `Real.iSup` junk) and pulls the infimum to $0$ (on $s = \mathbb{R}$
with $f = \sin$ and $n = 1$, the `iSup` form gives $0$, the `sInf` form the true value $1$).

§5.3 row (added in the implementing PR):

| minimax error | `minimaxError f s n : ℝ`, `f : ℝ → ℝ`, `s : Set ℝ`, degree at most `n`; the infimum of the `ε` with `Metric.IsUniformApproxOn (fun x => p.eval x) f s ε`; junk `0` when no degree-`n` polynomial is within finite distance and for `s = ∅`; theorems assume `IsCompact s` and `ContinuousOn f s` where needed | `minimaxError_eq_infDist` (Mathlib's `Metric.infDist` in `C(s, ℝ)` to the restricted `degreeLE ℝ n`); `exists_degree_le_isUniformApproxOn_minimaxError`; Mathlib has none |

### 2.2 `AlternatesOn` (in `NLAlib/Polynomial/Approximation/Equioscillation.lean`, written)

```lean
def AlternatesOn (g : ℝ → ℝ) (s : Set ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  ∃ x : Fin k → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i : Fin k, ε ≤ σ * (-1) ^ (i : ℕ) * g (x i)
```

with the raw-condition constructor `alternatesOn_iff` (`Iff.rfl`, written and built). For
$\varepsilon > 0$ it says: $k$ ordered points of $s$ where $g$ alternates in sign with modulus at
least $\varepsilon$. With $\lvert g\rvert \le \varepsilon$ on $s$ it is equioscillation
(`AlternatesOn.exists_eq_of_abs_le`). For $\varepsilon \le 0$ it is weaker than a sign change,
which costs nothing: every theorem is true there (de la Vallée Poussin's conclusion is then
trivial, and $E_n \ge 0$).

§5.3 row:

| alternation (equioscillation) | `AlternatesOn g s k ε`: `k` increasing points of `s`, a sign `σ = 1 ∨ σ = -1`, `ε ≤ σ * (-1) ^ i * g (x i)`; equioscillation of an error `f - p` is `AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε` together with `Metric.IsUniformApproxOn (fun x => p.eval x) f s ε` | `alternatesOn_iff`; `AlternatesOn.exists_eq_of_abs_le`; Mathlib has none |

## 3. Statement shapes

All in `namespace NLAlib` with `open Polynomial` unless said. IDs are the dispatch IDs of
`~/nlalib-harness/pilot/polybest-targets.json` (`note_id`). Docstrings with `Proof:` lines are in
the skeleton; here the signatures, and the reasons where the shape is a choice.

### 3.1 ForMathlib (scaffold; root, `ContinuousMap`, `Submodule` namespaces)

* **F1** `NLAlibScaffold/ForMathlib/Topology/Order/IntermediateValue.lean`, S:
  ```lean
  theorem exists_strictMono_eq_zero_of_mul_neg {k : ℕ} {f : ℝ → ℝ} {v : Fin (k + 1) → ℝ}
      (hv : StrictMono v) (hf : ContinuousOn f (Set.Icc (v 0) (v (Fin.last k))))
      (hsign : ∀ i : Fin k, f (v i.castSucc) * f (v i.succ) < 0) :
      ∃ c : Fin k → ℝ, StrictMono c ∧
        ∀ i, c i ∈ Set.Ioo (v i.castSucc) (v i.succ) ∧ f (c i) = 0
  ```
  Consumers E3, E10; also KS8 (interlacing of zeros) may want it.
* **F2** `NLAlibScaffold/ForMathlib/Topology/ContinuousMap/Compact.lean`, M:
  ```lean
  theorem ContinuousMap.exists_pos_norm_sub_smul_lt {K : Type*} [TopologicalSpace K]
      [CompactSpace K] (e h : C(K, ℝ)) (he : 0 < ‖e‖)
      (hsign : ∀ x, |e x| = ‖e‖ → 0 < e x * h x) : ∃ t : ℝ, 0 < t ∧ ‖e - t • h‖ < ‖e‖
  ```
  The descent step of E7. Stated on `C(K, ℝ)` (Mathlib's normed space) because the proof is
  about the sup norm; E7 restricts $f - p$ to `C(Set.Icc a b, ℝ)` internally.
* **F3** `NLAlibScaffold/ForMathlib/Analysis/Normed/Module/FiniteDimension.lean`, M:
  ```lean
  theorem Submodule.exists_infDist_eq_dist {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
      [ProperSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] (S : Submodule 𝕜 E)
      [FiniteDimensional 𝕜 S] (x : E) : ∃ y ∈ S, Metric.infDist x (S : Set E) = dist x y
  ```
  Named after Mathlib's `IsCompact.exists_infDist_eq_dist`; the prototype's version is over ℝ.
  Searched: Mathlib has `IsClosed.exists_infDist_eq_dist` only for a proper ambient space.

### 3.2 `Polynomial/Approximation/MinimaxError.lean` (B1–B13)

Hypotheses: theorems that need attainment take `(hs : IsCompact s) (hf : ContinuousOn f s)`
(OQ1); the purely set-theoretic ones (B1, B2, B8, B9, B11) take none.

| ID | Name | Shape | Diff |
|---|---|---|---|
| B1 | `minimaxError_nonneg` | `0 ≤ minimaxError f s n` | S |
| B2 | `minimaxError_le_of_isUniformApproxOn` | `p.degree ≤ n → 0 ≤ ε → IsUniformApproxOn p.eval f s ε → minimaxError f s n ≤ ε` | S |
| B3 | `exists_degree_le_isUniformApproxOn_minimaxError` | `IsCompact s → ContinuousOn f s → ∃ p, p.degree ≤ n ∧ IsUniformApproxOn p.eval f s (minimaxError f s n)` | M |
| B4 | `isLeast_minimaxError` | `IsLeast {ε | ∃ p, …} (minimaxError f s n)`, compact nonempty `s` | S |
| B5 | `minimaxError_eq_infDist` | `[CompactSpace s] (g : C(s, ℝ)) (hg : ∀ x : s, g x = f x) : minimaxError f s n = Metric.infDist g ((degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap : Set C(s, ℝ))` | M |
| B6 | `antitone_minimaxError` | `Antitone (minimaxError f s)` | S |
| B7 | `minimaxError_le_minimaxError_of_subset` | `IsCompact t → ContinuousOn f t → s ⊆ t → minimaxError f s n ≤ minimaxError f t n` | S |
| B8 | `minimaxError_add_eval` | `q.degree ≤ n → minimaxError (fun x => f x + q.eval x) s n = minimaxError f s n` | S |
| B9 | `minimaxError_const_mul` | `minimaxError (fun x => c * f x) s n = |c| * minimaxError f s n` | M |
| B10 | `minimaxError_add_le` | `minimaxError (fun x => f x + g x) s n ≤ minimaxError f s n + minimaxError g s n` | S |
| B11 | `minimaxError_comp_mul_add` | `α ≠ 0 → minimaxError (fun t => f (α * t + β)) ((fun t => α * t + β) ⁻¹' s) n = minimaxError f s n` | M |
| B12 | `minimaxError_comp_Icc_neg_one_one` | `a < b → minimaxError (fun t => f (((b - a) * t + b + a) / 2)) (Set.Icc (-1) 1) n = minimaxError f (Set.Icc a b) n` | S |
| B13 | `tendsto_minimaxError_atTop` | `ContinuousOn f (Set.Icc a b) → Tendsto (minimaxError f (Set.Icc a b)) atTop (𝓝 0)` | S |

Notes. B2 takes `0 ≤ ε` rather than `s.Nonempty`, like `residualMinimax_le`: it is the weaker
requirement, and a consumer with nonempty `s` gets it from `hε.nonneg hs`. B5 takes a
continuous-map `g` with an agreement hypothesis instead of building
`⟨s.restrict f, hf.restrict⟩` in the statement (T9: no proof terms in statements). B8, B9 and
B11 hold for every `f` and `s`, junk values included (the two sets coincide or scale); B9 is M
only for the junk bookkeeping. B12 uses the affine map of `AnalyticApproximation` and the
Krylov analytic corollaries, so that B12 rewrites their hypotheses. B6 is stated as `Antitone`
on the partial application, which the argument order `f s n` makes possible.

### 3.3 `Polynomial/Approximation/Equioscillation.lean` (E1–E12)

| ID | Name | Shape | Diff |
|---|---|---|---|
| E1 | `AlternatesOn.mono` | `AlternatesOn g s k ε → s ⊆ t → η ≤ ε → AlternatesOn g t k η` | S |
| E2 | `AlternatesOn.exists_eq_of_abs_le` | `AlternatesOn g s k ε → (∀ x ∈ s, |g x| ≤ ε) → ∃ x, StrictMono x ∧ (∀ i, x i ∈ s) ∧ ∃ σ, (σ = 1 ∨ σ = -1) ∧ ∀ i, g (x i) = σ * (-1) ^ i * ε` | S |
| E3 | `AlternatesOn.exists_le_abs_sub_eval` | `AlternatesOn (f - p) s (n + 2) ε → p.degree ≤ n → q.degree ≤ n → ∃ x ∈ s, ε ≤ |f x - q.eval x|` | M |
| E4 | `AlternatesOn.le_minimaxError` | `AlternatesOn (f - p) s (n + 2) ε → p.degree ≤ n → IsUniformApproxOn p.eval f s η → ε ≤ minimaxError f s n` | S |
| E5 | `AlternatesOn.minimaxError_eq` | `AlternatesOn (f - p) s (n + 2) ε → p.degree ≤ n → IsUniformApproxOn p.eval f s ε → minimaxError f s n = ε` | S |
| E6 | `exists_degree_le_or_alternatesOn` (private) | sign-block induction, see below | L |
| E7 | `alternatesOn_of_isUniformApproxOn_minimaxError` | `a < b → ContinuousOn f (Icc a b) → p.degree ≤ n → IsUniformApproxOn p.eval f (Icc a b) (minimaxError f (Icc a b) n) → AlternatesOn (f - p) (Icc a b) (n + 2) (minimaxError f (Icc a b) n)` | L |
| E8 | `isUniformApproxOn_minimaxError_iff_exists_alternatesOn` | best `↔ ∃ ε, IsUniformApproxOn p.eval f (Icc a b) ε ∧ AlternatesOn (f - p) (Icc a b) (n + 2) ε` | S |
| E9 | `eq_of_isUniformApproxOn_minimaxError` | two best approximants of degree at most `n` on `Icc a b` are equal | M |
| E10 | `exists_eval_eq_of_isUniformApproxOn_minimaxError` | best `p` → `∃ t : Finset ℝ, t.card = n + 1 ∧ ↑t ⊆ Ioo a b ∧ ∀ x ∈ t, p.eval x = f x` | M |
| E11 | `alternatesOn_eval_T_real` | `AlternatesOn (fun x => (T ℝ n).eval x) (Icc (-1) 1) (n + 1) 1` | M |
| E12 | `minimaxError_pow_Icc_neg_one_one` | `minimaxError (fun x => x ^ (n + 1)) (Icc (-1) 1) n = (2 ^ n)⁻¹` | M |

(`f - p` abbreviates `fun x => f x - p.eval x` in the table.)

E6, the induction (private: its extra clause "$e(a)q(x) > 0$ for $x \le a$" exists only to
make the induction compose; a later weighted version would restate it):

```lean
private theorem exists_degree_le_or_alternatesOn (n : ℕ) {e : ℝ → ℝ} {a b E : ℝ}
    (he : ContinuousOn e (Set.Icc a b)) (hE : 0 < E) (hab : a ≤ b) (hea : |e a| = E) :
    (∃ q : ℝ[X], q.degree ≤ n ∧ (∀ x ∈ Set.Icc a b, |e x| = E → 0 < e x * q.eval x) ∧
      ∀ x ≤ a, 0 < e a * q.eval x) ∨
    AlternatesOn e {x | x ∈ Set.Icc a b ∧ |e x| = E} (n + 2) E
```

The prototype states it for `Continuous e` on ℝ and extends $f$ by `IccExtendCM`; with
`ContinuousOn` on $[a, b]$ (compactness of level sets by `ContinuousOn.preimage_isClosed_of_isClosed`)
E7 needs no extension.

Why these shapes.

* **De la Vallée Poussin is on any set and any `f`** (E3–E5): its proof is root counting for
  the polynomial $q - p$, so neither continuity of $f$ nor an interval is used. This matters for
  Krylov: the set can be a finite spectrum or a union of intervals (indefinite problems). E4's
  `hη` (some finite error of the certificate polynomial) is the only hypothesis that excludes the
  junk value; it is free in every use (in E5 it is `hε`).
* **Necessity (E7) is on intervals.** On a general compact set the theorem needs $n + 2$ points
  in $s$ and a sign-block argument across gaps; the prototype proves only $[a, b]$, every
  consumer has $[a, b]$, and the general version is a later strengthening that keeps the name
  (OQ5).
* **Equioscillation is the conjunction** "uniform error $\varepsilon$ and alternation at level
  $\varepsilon$" (E5, E8) rather than a third predicate: the uniform half is the library's
  `IsUniformApproxOn`, and E2 extracts the equalities when they are wanted.
* **E10's conclusion is a `Finset`**, the form of `Lagrange.interpolate s v` and of the
  `dividedDifference` row; the Lagrange identity is one Mathlib lemma
  (`Lagrange.eq_interpolate_of_eval_eq`) and is not stated.
* **E12** is the classical example, an existing result in $E_n$ language (`Result:
  chebyshev-monic-minimal`, the id of `isLeast_chebyshev_monic_minimax`), and exercises the
  certificate E5 with E11; it is also the check that the definition is the right one.

### 3.4 Glue: the papers' $E_n$ forms (G1–G8)

Each is a corollary in the file of the bound it restates (placement: the subject is the
existing bound; CONTRIBUTING §5.2 "corollaries after, in the same file"); proofs are B3 (or B2)
plus one application, S each.

| ID | File (`NLAlib/…`) | Name | Conclusion |
|---|---|---|---|
| G1 | `Krylov/Functions/LanczosFA.lean` | `Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_continuousOn` | `‖f(A)b − lanczosFA A f b (q + 1)‖ ≤ 2 * minimaxError f (Icc a a') q * ‖b‖` |
| G2 | `Krylov/Functions/Quadrature.lean` | `Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_continuousOn` | `‖bᴴ(f(A)b − lanczosFA A f b (q + 1))‖ ≤ 2 * minimaxError f (Icc a a') (2q + 1) * ‖b‖ ^ 2` |
| G3 | `Polynomial/Orthogonal/Gauss.lean` | `abs_integral_sub_integral_gaussQuadrature_le_of_continuousOn` | `|∫ f dμ − ∫ f d(gaussQuadrature μ (k + 1))| ≤ 2 * minimaxError f (Icc a b) (2k + 1) * μ.real univ` |
| G4 | `Estimation/Trace/StochasticLanczosQuadrature.lean` | `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_continuousOn` | `‖tr f(A) − slq A f Ω (q + 1)‖ ≤ ‖tr f(A) − girardHutchinson (f(A)) Ω‖ + 2 * minimaxError f (Icc a a') (2q + 1) * frobNorm Ω ^ 2 / card m` |
| G5 | same | `measureReal_abs_trace_cfc_sub_slq_ge_le_of_continuousOn` | the Hanson–Wright tail with the quadrature term `2 * minimaxError … (2q + 1) * frobNorm (X ω) ^ 2 / card m` inside the event |
| G6 | `Polynomial/Approximation/Jackson.lean` | `minimaxError_le_of_lipschitzOnWith` | `minimaxError f (Icc a b) N ≤ jacksonApproximationConstant * L * (b - a) / (2 * (N + 2))` |
| G7 | `Polynomial/Approximation/AnalyticApproximation.lean` | `minimaxError_le_of_differentiableOn` | `minimaxError f (Icc a b) N ≤ 2 * M / (ρ ^ N * (ρ - 1))` |
| G8 | `Polynomial/Approximation/Inverse.lean` | `minimaxError_inv_le` | `minimaxError (fun x => x⁻¹) (Icc a b) n ≤ (2 / a) * ((√b − √a) / (√b + √a)) ^ (n + 1)` |

G1–G5 take `hf : ContinuousOn f (Set.Icc a a')` in place of `p`, `hp`, `ε`, `hε`; G3 also drops
`Integrable f μ` (continuity on the support's interval gives it, as in the existing Lipschitz
corollary). The `_of_isUniformApproxOn` theorems stay primary: they are the general form (any
approximant, any error), the $E_n$ forms are their corollaries, and the existing Lipschitz and
analytic corollaries are not rerouted through $E_n$ (they would gain nothing).

Names: the siblings are named by their distinguishing hypothesis (`_of_isUniformApproxOn`,
`_of_lipschitzOnWith`, `_of_differentiableOn`), so the new ones are `_of_continuousOn` (N8, N9)
(OQ7). G6–G8 are named by their conclusion `minimaxError_le`.

Real scalars only: G6 and G7 specialise the `𝕜`-valued constructors to ℝ, because `minimaxError`
is real (OQ2).

## 4. Consumers

* G1–G5: the Krylov-functions and SLQ notes' statements in the papers' form
  ($\lVert f(\mathbf A)\mathbf b - \mathsf{lanczosFA}\rVert \le 2E_{q}(f)\lVert\mathbf b\rVert$,
  [ChenPersson2026, (2)]); later the Lanczos-FA near-optimality round (`Krylov/Functions/NearOptimality.lean`).
* E3–E5: every lower bound to come (gap report: $1/x$, sign, $e^{-x}$; Poly4's lower halves),
  and Krylov sharpness statements on finite spectra (Greenbaum-type worst cases, where the set is
  the spectrum).
* E7, E9, E10: Lebesgue constants and near-best interpolation (gap report row 6) and the Remez
  algorithm; E10 is the "best approximant interpolates" step used to compare Lanczos-FA with
  interpolation at Ritz values.
* B11, B12: every interval statement proved on $[-1, 1]$ (Chebyshev, Bernstein ellipse).
* B5: the Lebesgue-constant stage (projections onto the restricted polynomial subspace live in
  `C(s, ℝ)`; prototype `norm_sub_projection_le_minimaxError` is stated there).

## 5. Files and placement

New in `NLAlib` (written, built under `--wfail`): `Polynomial/Approximation/MinimaxError.lean`
(the definition), `Polynomial/Approximation/Equioscillation.lean` (the predicate and
`alternatesOn_iff`). Directory: `Polynomial/Approximation` holds the existing approximation
theory (Jackson, Inverse, Chebyshev series, Bernstein ellipse); a new `BestApproximation`
directory for two files was not worth it. Expected final sizes: MinimaxError about 350 lines,
Equioscillation about 500 lines.

Scaffold (same paths under `NLAlibScaffold`): the two files above (B1–B13, E1–E12), three
ForMathlib files (F1–F3), and seven glue files at the consumers' paths (G1–G8).

Additions outside the stage's own files (each moves into the existing `NLAlib` file when
proved; that file then imports `NLAlib.Polynomial.Approximation.MinimaxError`, which imports only
Mathlib and ForMathlib, so P11 holds for the Polynomial ones):

| Declaration | Home | Reason |
|---|---|---|
| F1 | new `ForMathlib/Topology/Order/IntermediateValue.lean` | IVT fact, no NLAlib vocabulary (P4, P7) |
| F2 | new `ForMathlib/Topology/ContinuousMap/Compact.lean` | sup-norm fact on `C(K, ℝ)` |
| F3 | new `ForMathlib/Analysis/Normed/Module/FiniteDimension.lean` | next to Mathlib's nearest-point lemmas |
| G1 | `Krylov/Functions/LanczosFA.lean` | corollary of `…_lanczosFA_le_of_isUniformApproxOn` |
| G2 | `Krylov/Functions/Quadrature.lean` | corollary of the quadrature bound there |
| G3 | `Polynomial/Orthogonal/Gauss.lean` | corollary of the Gauss-rule bound there |
| G4, G5 | `Estimation/Trace/StochasticLanczosQuadrature.lean` | corollaries of the SLQ split and tail there |
| G6 | `Polynomial/Approximation/Jackson.lean` | Jackson's theorem in $E_N$ form |
| G7 | `Polynomial/Approximation/AnalyticApproximation.lean` | Bernstein-ellipse rate in $E_N$ form |
| G8 | `Polynomial/Approximation/Inverse.lean` | the $1/x$ rate in $E_n$ form |

No flags (nothing placed away from its home).

## 6. Material: the prototype

`~/nlalib-proto` (`tchen-research/NLAlib`, `cda0338`), `NLAlib/Polynomial/BestApproximation/`:
86 modules, of which the core read here is about 1,000 lines, all proved. Mapping:

| Here | Prototype (file: declaration) | Reuse |
|---|---|---|
| `minimaxError` | `Basic: minimaxError` (`Metric.infDist f (polynomialApproximationSpace s n)` on `C(s, ℝ)`) | redesigned (OQ1); its form is B5 |
| B3, B4 | `MinimaxError: exists_degree_le_norm_sub_eq_minimaxError`, `isLeast_minimaxError` | proof route |
| F3 | `ForMathlib/Analysis/Normed/Approximation: exists_norm_sub_eq_infDist_of_finiteDimensional` | proof, generalised to a proper field |
| B6, B8, B9, B10, B13 | `MinimaxError: minimaxError_antitone, _add_of_mem, _smul, _add_le, tendsto_minimaxError_atTop` | proofs (our junk handling differs for B9) |
| B11, B12 | `Affine: minimaxError_comp_le_of_affine, _comp_homeomorph_of_affine, _comp_affine_interval` | proof route; our statement is a preimage, not a homeomorphism |
| F1 | `ForMathlib/Topology/Order/IntermediateValue: exists_strictMono_eq_zero_of_mul_neg` | proof |
| E3, E4 | `AlternationLowerBound: exists_abs_sub_eval_ge_of_alternation, le_minimaxError_of_alternation, not_forall_eval_mul_eval_neg_of_degree_le` | proofs; hypothesis restated as `AlternatesOn` |
| E5 | `EquioscillationCertificate: norm_sub_eq_minimaxError_of_equioscillation` | proof |
| E6 | `ExtremalSigns: exists_polynomial_extremal_sign_or_alternation` (150 lines) | proof, `ContinuousOn` instead of `Continuous` |
| F2 | `ForMathlib/Analysis/Normed/UniformApproximation: exists_pos_norm_sub_smul_lt_of_extremal_sign` | proof |
| E7, E8 | `Equioscillation: exists_alternating_extrema_of_norm_sub_eq_minimaxError, exists_equioscillation_…, norm_sub_eq_minimaxError_iff_equioscillation` | proof |
| E9 | `Equioscillation: eq_of_norm_sub_eq_minimaxError` | proof |
| E10 | `AlternatingInterpolant: exists_interpolate_eq_of_alternation`; `BestInterpolant: exists_interpolate_eq_of_norm_sub_eq_minimaxError` | proof; `Finset` conclusion |
| E11, E12 | none (prototype `Minimax.lean` has the monic minimax, already ported as Poly1) | new, from Mathlib's `node` and E5 |

Not reproduced: the `polynomialApproximationSpace` definition (inlined in B5; OQ1),
`Basic`'s Lebesgue, rational and node-simplex definitions (out of scope), the aggregator
`BestApproximation.lean`, the `ForMathlib/Topology/Order/IntermediateValue` helpers
`mul_sub_mul_sub_neg_of_abs_lt`, `exists_strictMono_mem_Ioo`, `exists_sign_of_alternating_abs_eq`
(proof-local here; `AlternatesOn` absorbs the sign normalisation), and `isLeast_minimaxError_pointwise`
(our definition is already pointwise). The prototype's "atlas" ids are reused as `Result:` ids
where they exist (`equioscillation`, `de-la-vallee-poussin`, `best-approximant-interpolates`);
new: `best-approximation-existence`, `best-approximation-uniqueness`.

## 7. Mathlib search (pinned `v4.33.1`)

Searched `Mathlib/` for `equioscillat`, `alternation`, `best approximation`, `minimax`,
`Vallée`, `Haar condition`, `Chebyshev system`: only `Topology/Sion.lean`, `Order/SaddlePoint`
and decision theory (unrelated). No best-approximation theory, as the gap report said.

Used: `exists_polynomial_near_of_continuousOn` (`Topology/ContinuousMap/Weierstrass`, B13);
`IsCompact.exists_infDist_eq_dist`, `IsClosed.exists_infDist_eq_dist` (the latter needs a proper
ambient space, so F3 is new); `FiniteDimensional.proper` (F3); `Polynomial.toContinuousMapOnAlgHom`,
`Polynomial.degreeLE`, `degreeLTEquiv` (B3, B5); `Polynomial.Chebyshev.node`,
`eval_T_real_node`, `strictAntiOn_node`, `node_mem_Icc`, `abs_eval_T_real_le_one`
(`Analysis/SpecialFunctions/Trigonometric/Chebyshev/{Extremal,RootsExtrema}`, E11, E12);
`Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero`,
`Polynomial.eq_of_degree_sub_lt_of_eval_index_eq`, `Lagrange.eq_interpolate_of_eval_eq`
(E3, E9, E10); `intermediate_value_Ioo` (F1). Mathlib's `Extremal.lean` proves the leading
coefficient bound by evaluation at the nodes, a discrete argument of the same kind as
de la Vallée Poussin, but states nothing about approximation.

Within NLAlib: `Polynomial.Chebyshev.isLeast_chebyshev_monic_minimax` (ForMathlib, Poly1) is the
monic-minimax form of E12; `residualMinimax` (`Chebyshev/Residual`) is a constrained minimax
value with a different definition form (§2.1) and is not related by a theorem here.

## 8. Deviations

None numbered. `minimaxError` is an addition where Mathlib has nothing; its nearest Mathlib
notion, `Metric.infDist` in `C(s, ℝ)` to the restricted polynomial subspace, is reached by B5.
A paragraph for `docs/design/Mathlib-deviations.md` "Additions where Mathlib has nothing" is in
this commit.

## 9. Names for review

`minimaxError_comp_mul_add` follows Mathlib's `integral_comp_mul_add`. `minimaxError_const_mul`
follows `integral_const_mul` for `fun x => c * f x`. `minimaxError_add_eval` names the added
`q.eval`. `antitone_minimaxError` (N3 allows `antitone`). E3–E5 live in the `AlternatesOn`
namespace (N9: the predicate is the first explicit argument). E7 and E9/E10 keep
`_of_isUniformApproxOn_minimaxError` to say which uniform approximation is assumed.
`alternatesOn_eval_T_real` follows Mathlib's `eval_T_real_…`. These should be confirmed by
`check_names.py` on the extraction before the first proof PR.

## 10. Open questions for the maintainer

**OQ1. The definition of $E_n$.** (a) `sInf` of the errors `ε` of degree-`n` polynomials,
through `Metric.IsUniformApproxOn`, on a raw `f : ℝ → ℝ` and `s : Set ℝ`; theorems needing
attainment assume `IsCompact s`, `ContinuousOn f s` (recommended). (b) The `⨅ p, ⨆ x ∈ s` form of
`residualMinimax`: shorter, same spelling as its sibling, but a wrong junk value whenever one
polynomial has unbounded error (§2.1). (c) The prototype: `Metric.infDist` in `C(s, ℝ)`,
`[CompactSpace s]`: the cleanest analysis, but every consumer has to build a continuous map from
`f` and `hf` and convert `‖·‖` back to pointwise bounds; it is kept as the bridge B5.
Recommendation (a): the consumers' shape, junk only where the true value is $+\infty$.

**OQ2. Real or `RCLike` values.** (a) `f : ℝ → ℝ` only (recommended). (b) `f : ℝ → 𝕜` with
`𝕜[X]`: existence and the algebra generalise, but equioscillation is false for complex values
(the characterisation is Kolmogorov's criterion), and the consumers are real. Recommendation
(a); a complex `minimaxError` is a later definition with a bridge, if a non-Hermitian consumer
appears.

**OQ3. Degree convention in the glue.** (a) `q + 1` Lanczos steps (Gauss points) with $E_q$ /
$E_{2q+1}$, as the existing Lipschitz and analytic corollaries (recommended). (b) `q` steps with
a hypothesis `n < q` (or `2 * n < …`) and $E_n$: more flexible, one more hypothesis. (c) `q`
steps and $E_{q-1}$ with natural subtraction: wrong at `q = 0`. Recommendation (a).

**OQ4. The alternation predicate.** (a) One predicate `AlternatesOn g s k ε` with the sign
$\sigma$ and a level (recommended). (b) No predicate: the prototype's raw tuples
(`StrictMono v`, products `< 0`, `ε ≤ |…|`) in each statement, which CONTRIBUTING §5.4 forbids
once repeated. (c) Two predicates (alternation; equioscillation with equalities). Recommendation
(a): E2 gives the equalities, and the uniform half is the existing interface.

**OQ5. Domain of the necessity theorem.** (a) $[a, b]$, $a < b$, now; the general compact set
with at least $n + 2$ points later, same name (recommended). (b) General compact sets now (an
extra L for the gaps between components). Recommendation (a): no consumer needs more, and
sufficiency and de la Vallée Poussin are already general.

**OQ6. A named best approximant.** (a) No definition; existence (B3) and uniqueness (E9) only
(recommended). (b) `minimaxPoly f a b n : ℝ[X]` by choice, canonical on intervals by E9, with the
API `degree_le`, `isUniformApproxOn`, `eq_of_…`. Recommendation (a) until a consumer (Remez,
Lebesgue constants) needs to refer to "the" best approximation as data.

**OQ7. Names of the glue.** (a) `…_le_of_continuousOn`, by the distinguishing hypothesis like
the siblings `…_of_lipschitzOnWith`, `…_of_differentiableOn` (recommended, N8/N9). (b)
`…_le_minimaxError`, by the right-hand side, which says "the $E_n$ form" but breaks the family
pattern. Recommendation (a); the docstrings say $E_n$ in the first sentence.

## 11. Deferred, with what each needs

* Lebesgue constant, $\lVert f - L f\rVert \le (1 + \lVert L\rVert)E_n$ (ATAP 15.1), Chebyshev
  and equispaced Lebesgue growth: B5 and E10; gap report row 6.
* Lower bounds $E_n(1/x; [a, b])$ (exact value), $E_n(\operatorname{sign})$, $E_n(e^{-x})$,
  $E_n(\lvert x\rvert)$: E4/E5 with explicit alternants (prototype `ExponentialReciprocalLower`,
  `AbsoluteLower`, `RootSampleLower`).
* Weighted best approximation (prototype `WeightedMinimax`): E6 with a weight.
* Rational best approximation (prototype `Rational*`, 9 files).
* Equioscillation on compact sets (OQ5); Haar spaces; Remez.
* Strong uniqueness, Lipschitz continuity of the best-approximation operator.
* Odd/even best approximants (prototype `OddMinimax*`), used for sign and $\lvert x\rvert$.
* `MatchesMoments.abs_integral_sub_integral_le_of_continuousOn` and spectral-density
  (Wasserstein) restatements: one-line corollaries when a consumer asks.

## 12. Proof plan for dispatch

36 targets (`~/nlalib-harness/pilot/polybest-targets.json`), waves by dependency:

* wave 0 (independent): F1, F2, F3, B1, B2, B8, B9, B11, E1, E2;
* wave 1: B3 (F3), B12 (B11), B13 (B1, B2), E3 (F1);
* wave 2: B4, B5, B6, B7, B10, G1–G8 (B3 or B2), E4 (E3), E6;
* wave 3: E5 (E4, B2), E7 (E6, F2, E1, B2), E11;
* wave 4: E8, E9, E10, E12.

The two L rows (E6, E7) have complete prototype proofs (150 and 100 lines); their outlines cite
them, and they are the rows for the Fable outline review. Everything else is S or M with a
proved prototype counterpart or a direct Mathlib route.
