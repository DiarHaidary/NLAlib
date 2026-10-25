# Design note: interpolation remainders, Gauss–Radau and Gauss–Lobatto rules, and two-sided bounds on quadratic forms (stage KS8)

Status: draft for the maintainer, 2026-10-25; skeleton written the same day (branch
`design/ks8`, from `df3f025` = `stage/ks7-slq-beta`). The decision sheet is
`~/nlalib-harness/state/decisions/KS8.json`; the dispatch targets are
`~/nlalib-harness/pilot/ks8-targets.json`.

Every signature in §4 is in the skeleton and elaborates: `lake build NLAlibScaffold` succeeds
with the 65 statements of this note sorried and the 7 definitions, 2 instances and 2 `rfl`
lemmas of §2 proved (`NLAlib/Polynomial/Orthogonal/RadauLobatto.lean`). No proof was attempted
otherwise. `scripts/check_refs.py` and `scripts/check_rules.py --files` pass on the new files
(the name checker N1–N18 needs an extraction and was not run; names were checked by hand against
§4 of CONTRIBUTING).

## What earlier notes deferred to this stage

- `Krylov-Spectral.md` §8 item 3: "Gauss–Radau and Lobatto bounds, and the sign of the Gauss
  error for $f$ with sign-definite derivatives. They need the Hermite interpolation remainder
  (gap survey P1), which is missing."
- `Polynomial-OrthogonalStructure.md` (KS7) §8 item 4: the rules "are algebraically cheap here
  (Radau at $a$ is $\delta$-augmented `gaussQuadrature` of
  `μ.withDensity (fun x => ENNReal.ofReal (x - a))`, exact to degree $2k$), but their use,
  two-sided bounds on $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ for $f$ with sign-definite
  derivatives, needs the Hermite interpolation remainder … Consumer: SLQ and CG error estimation.
  Defer both together." KS7's consumer table adds "CG files: … Gauss–Radau upper bounds for the
  CG error (Golub–Meurant Ch. 12) need §8 item 4", and the zeros row "later interlacing,
  Gauss–Radau".
- `Estimation-SLQ.md` §0 (out of scope: "Gauss–Radau") and its consumer table (`slqMeasure`
  rows: "any future quadrature-type density bound (Gauss–Radau, …)").
- Gap survey (`~/nlalib-harness/reports/Gaps-MatrixAnalysis-Polynomials.md`, candidate #1):
  "the derivative-form Gauss remainder and the Golub–Meurant two-sided bounds … The main design
  question is the Hermite API: confluent nodes as a `Multiset`, or the iterated-Rolle remainder
  for Lagrange only, with Gauss as its limit."

**A correction to KS7 §8 item 4.** The Radau rule is not the Gauss rule of
$(x - a)\,d\mu$ with an atom added at $a$: its *free nodes* are the Gauss nodes of
$(x - a)\,d\mu$, but its weights are the interpolatory weights of $\mu$ at the $k + 1$ nodes
(the free-node weights are $\lambda_i/(x_i - a)$, $\lambda_i$ the weights of the modified Gauss
rule, and the weight at $a$ is what is left of the mass). The definition below builds the rule
the way KS7 built `gaussQuadrature`: nodes, then `interpolatoryQuadrature μ`.

## 0. Summary and main choices

1. **Scope.** The Hermite interpolation remainder for nodes with multiplicity; the
   derivative-form remainders of the Gauss, Gauss–Radau and Gauss–Lobatto rules; the rules
   themselves (exactness, support, mass, nonnegative weights, Radau uniqueness); Golub's
   modified Jacobi matrix for the Radau rule and its Golub–Welsch theorem; and the consumers:
   two-sided bounds on $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ (Lanczos, Radau,
   Lobatto), the CG error identity with the Golub–Meurant (Golub–Strakoš) upper and lower bounds,
   and the sign of the SLQ bias. **65 declarations to prove** (41 S, 19 M, 5 L, no H) and **7
   definitions** (proved in the skeleton with their instances); 8 new files and additions to 4
existing ones (§5).
2. **Hermite interpolation has no definition** (OQ1). Nodes with multiplicity are a
   `Multiset ℝ`; the remainder theorem is stated for *any* polynomial $H$ of degree less than
   $\lvert m\rvert$ matching the jets of $f$, and two theorems give existence and uniqueness of
   such $H$ (linear algebra: the jet map on `degreeLT` is injective by root counting). The
   quadrature proofs pick $H$ by existence; a user interpolating values uses Mathlib's
   `Lagrange.interpolate`, for which the Lagrange remainder is a corollary. The prototype's
   explicit double-node and endpoint cardinal formulas are not reproduced.
3. **Smoothness is two Mathlib predicates** (OQ2): `ContinuousOn f (Set.Icc a b)` and
   `ContDiffOn ℝ N f (Set.Ioo a b)`; signs are `∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv N f x`. Only
   continuity is asked at the endpoints, so $\sqrt{x}$ on $[0, b]$ and $\log$, $x^{-1}$ on
   $[a, b]$, $a > 0$, all qualify with `fun_prop`-style proofs.
4. **One Radau definition for both endpoints** (OQ3): `radauQuadrature μ c k` is the
   interpolatory rule of $\mu$ at $c$ and the Gauss nodes of `radauMeasure μ c` =
   $\lvert x - c\rvert\,d\mu$. For $\mu$ in $[a, b]$, $c = a$ is the left and $c = b$ the right
   Radau rule; exactness and the remainder take `hc : c = a ∨ c = b`, the bounds fix $c$.
   Lobatto: `lobattoQuadrature μ a b k`, density $\lvert(x - a)(x - b)\rvert$. $k$ counts the
   free nodes (OQ4): Radau has $k + 1$ nodes and degree $2k$, Lobatto $k + 2$ and $2k + 1$.
5. **Unconditional where true, as in KS7** (KS7 OQ2 (a)). Exactness, support and mass of both
   rules hold for every $k$: when the modified measure has too few support points the rule is
   $\mu$ itself (the terminating case), exactly as `gaussQuadrature` past the support size. The
   remainders hold for every $k$ (Gauss: $k > 0$); in the terminating case both sides are $0$.
   Definiteness appears only in the counting lemmas, the Radau Jacobi matrix and its
   Golub–Welsch theorem.
6. **Mean-value form first, signs as corollaries** (OQ5). The headline remainders are
   Gautschi's: $\int f - Q(f) = \frac{f^{(N)}(\xi)}{N!}\int\omega\,d\mu$. The passage from the
   pointwise remainder to one $\xi$ needs no measurable selection (an integral mean value theorem
   for pointwise intermediate values, ported from the prototype). The bounds are two-line
   corollaries, in both sign orientations (OQ8).
7. **Matrix-level bounds in measure form, plus one bridge** (OQ7). The Radau and Lobatto bounds
   on $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ are stated with
   `∫ x, f x ∂radauQuadrature (spectralMeasure A b) a q`, which needs no grade hypothesis; one
   bridge rewrites the Radau integral as $\|\mathbf{b}\|^2 f(\tilde{\mathbf{J}})_{0,0}$ for the
   modified Lanczos tridiagonal, under $q + 1 \le$ grade. The Lobatto matrix is deferred (OQ6).
8. **No new interface, no Mathlib deviation.** The stage consumes KS7's `MatchesMoments`,
   `IsOrthogonalPolynomial`, `IsMomentPosDef` and support hypothesis
   `∀ᵐ x ∂μ, x ∈ Set.Icc a b`, and the Matrix layer's `spectrum ℝ A ⊆ Set.Icc a a'`.

## 1. Scope

In scope (statement IDs of §4):

| Topic | IDs |
|---|---|
| ForMathlib: top derivative of a polynomial; iterated derivative of a polynomial function; Rolle with multiplicities; integral mean value for pointwise intermediate values | F1–F5 |
| Hermite interpolation: uniqueness, existence, remainder; Lagrange remainder | H1–H4 |
| Gauss nodes interior (more than $k$ support points) | Z1 |
| Gauss: exactness degree of an interpolatory rule; terminating case; remainder; two bounds | G1–G5 |
| Radau: modified measure; exactness; support; mass; uniqueness; remainder; four bounds | R1–R17 |
| Lobatto: modified measure; exactness; support; mass; remainder; two bounds | L1–L14 |
| Radau Jacobi matrix: eigenvector, $c$ in the spectrum, moments; Golub–Welsch; quadratic-form bridge | J1–J5 |
| Bounds on $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$: Lanczos error and bounds, Radau, Lobatto | K1–K9 |
| CG: error identity, Radau upper and lower bounds | C1–C3 |
| SLQ: sign of the bias against Girard–Hutchinson | S1, S2 |

Out of scope, with what each needs (§12): the Lobatto Jacobi matrix; strict positivity of the
Radau and Lobatto weights; Lobatto uniqueness; a `slqRadau` estimator; block Gauss–Radau;
Peano-kernel and contour (analytic $f$) remainders; Chebyshev–Markov–Stieltjes; anti-Gauss and
Gauss–Kronrod rules.

## 2. Objects

New definitions, all in `NLAlib/Polynomial/Orthogonal/RadauLobatto.lean` (proved in the
skeleton; the file imports only `NLAlib.Polynomial.Orthogonal.Gauss`, so P11 holds):

```lean
noncomputable def radauMeasure (μ : Measure ℝ) (c : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ‖x - c‖ₑ
noncomputable def radauNodes (μ : Measure ℝ) (c : ℝ) (k : ℕ) : Finset ℝ :=
  insert c (gaussNodes (radauMeasure μ c) k)
noncomputable def radauQuadrature (μ : Measure ℝ) (c : ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (radauNodes μ c k)
instance isFiniteMeasure_radauQuadrature …
noncomputable def lobattoMeasure (μ : Measure ℝ) (a b : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ‖(x - a) * (x - b)‖ₑ
noncomputable def lobattoNodes (μ : Measure ℝ) (a b : ℝ) (k : ℕ) : Finset ℝ :=
  insert a (insert b (gaussNodes (lobattoMeasure μ a b) k))
noncomputable def lobattoQuadrature (μ : Measure ℝ) (a b : ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (lobattoNodes μ a b k)
instance isFiniteMeasure_lobattoQuadrature …
noncomputable def radauJacobiAlpha (μ : Measure ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => c
  | k + 1 => c - jacobiBeta μ (k + 1) * (orthogonalPolynomial μ k).eval c /
      (orthogonalPolynomial μ (k + 1)).eval c
noncomputable def radauJacobiMatrix (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = Fin.last k ∧ j = Fin.last k then radauJacobiAlpha μ c k else jacobiMatrix μ (k + 1) i j
```

with `radauJacobiAlpha_zero`, `radauJacobiAlpha_succ` (`rfl`).

§5.3 rows (added with the proof PR that moves the bridges into `NLAlib/`, as KS7 did):

| Concept | Spelling | Bridge |
|---|---|---|
| Radau modified measure $\lvert x - c\rvert\,d\mu$ | `radauMeasure μ c` | `integral_radauMeasure` (R1) |
| Radau rule, prescribed node $c$, $k$ free nodes | `radauQuadrature μ c k`; nodes `radauNodes μ c k` | `matchesMoments_radauQuadrature` (R9), `integral_radauQuadrature` (R8) |
| Lobatto modified measure, rule | `lobattoMeasure μ a b`, `lobattoQuadrature μ a b k`, `lobattoNodes μ a b k` | L1, L8, L9 |
| Radau Jacobi matrix (Golub) | `radauJacobiMatrix μ c k`, corner `radauJacobiAlpha μ c k` | `spectralMeasure_radauJacobiMatrix` (J4) |
| nodes with multiplicity, nodal polynomial | `m : Multiset ℝ`, `(m.map fun y => X - C y).prod` | Mathlib's `Multiset` API; `Lagrange.nodal s id` for a `Finset` |
| jets | `(derivative^[k] H).eval y` (polynomial), `iteratedDeriv k f y` (function) | `Polynomial.iteratedDeriv` (F2) |

Junk values. `radauQuadrature μ c k` for $c$ inside the support is a measure on at most $k + 1$
points with no exactness claimed. `radauJacobiAlpha μ c k = c` when $\pi_k(c) = 0$ ($x/0 = 0$).
The modified measures are finite only under a support hypothesis (R2, L2), so they get theorems,
not instances.

Mathlib objects used directly: `Lagrange.interpolate`, `Lagrange.nodal`, `Lagrange.basis`;
`iteratedDeriv`, `ContDiffOn`, `ContinuousOn`; `Measure.withDensity`, `enorm`; `Multiset`;
`spectrum`. Searched and not found: any Hermite interpolation, confluent interpolation, iterated
Rolle, Gauss–Radau/Lobatto (§7).

## 3. Interfaces

None introduced. The statements take:

- the KS7 support hypothesis `hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b` with `[IsFiniteMeasure μ]`;
- for the remainders `hab : a < b` (the open interval must be nonempty);
- the prescribed node `hc : c = a ∨ c = b` (exactness, remainder) or a fixed `a`/`b` (bounds);
- smoothness `hf : ContinuousOn f (Set.Icc a b)`, `hf' : ContDiffOn ℝ N f (Set.Ioo a b)` with
  $N = 2k$, $2k + 1$, $2k + 2$ (written `(2 * k + 1 : ℕ)` so that the cast is the one the
  lemmas expect);
- signs `hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv N f x` (or `≤ 0`);
- at the matrix level `hs : spectrum ℝ A ⊆ Set.Icc a a'`, `haa' : a < a'`, as KS3/KS7.

The smoothness-and-sign triple recurs in about 30 statements. It is not bundled (OQ9): each part
is a Mathlib predicate a user discharges with `fun_prop` or a formula for `iteratedDeriv`, and a
bundle would hide which order is meant.

Definiteness `IsMomentPosDef ν k` is used for the modified measures (R4–R6, L4–L6) and for $\mu$
itself (Z1, J1, J2, J4), and is derived from `q + 1 ≤ krylovGrade A b` at the matrix level by
KS7's `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff`.

## 4. Statements

All in the skeleton with full docstrings and `Proof:` lines. Difficulty, estimated length and
dependencies are in §10 and in `ks8-targets.json`. Variables as in KS7: `μ ν : Measure ℝ`,
`[IsFiniteMeasure μ]`, `a b c : ℝ`; matrix layer `{𝕜} [RCLike 𝕜] {n} [Fintype n] [DecidableEq n]`.

### 4.1 ForMathlib (upstream candidates)

| ID | Name, file | Statement |
|---|---|---|
| F1 | `Polynomial.iterate_derivative_natDegree`, `ForMathlib/Algebra/Polynomial/Derivative` | `derivative^[p.natDegree] p = C (p.natDegree ! * p.leadingCoeff)`, any `CommSemiring` |
| F2 | `Polynomial.iteratedDeriv` (protected), `ForMathlib/Analysis/Calculus/Deriv/Polynomial` | `iteratedDeriv k (fun x => p.eval x) x = (derivative^[k] p).eval x`, any `NontriviallyNormedField` |
| F3 | `exists_iteratedDeriv_eq_zero_of_multiset`, `ForMathlib/Analysis/Calculus/LocalExtr/Rolle` | multiset of $q + 2$ zeros in $[a, b]$, repeated ones interior, $f$ continuous on $[a, b]$ and $C^{q+1}$ on $(a, b)$ ⇒ $\exists\xi \in (a, b)$, $f^{(q+1)}(\xi) = 0$ |
| F4 | `exists_integral_eq_mul_integral_of_ae_nonneg`, `ForMathlib/MeasureTheory/Integral/MeanValue` | $F = D(\xi_x)W$ a.e., $W \ge 0$, $s$ connected, $D$ continuous on $s$ ⇒ $\int F = D(\xi)\int W$ |
| F5 | `exists_integral_eq_mul_integral_of_ae_nonpos`, same file | the same with $W \le 0$ |

```lean
theorem exists_iteratedDeriv_eq_zero_of_multiset {f : ℝ → ℝ} {a b : ℝ} {m : Multiset ℝ} {q : ℕ}
    (hm : m.card = q + 2) (hmem : ∀ y ∈ m, y ∈ Icc a b)
    (hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b) (hf : ContinuousOn f (Icc a b))
    (hf' : ContDiffOn ℝ (q + 1 : ℕ) f (Ioo a b))
    (hz : ∀ y ∈ m, ∀ j < m.count y, iteratedDeriv j f y = 0) :
    ∃ ξ ∈ Ioo a b, iteratedDeriv (q + 1) f ξ = 0
```

The prototype's version also assumes two distinct points; it is not needed (if all $q + 2$
points coincide, the point is interior and `hz` is the conclusion).

### 4.2 Hermite interpolation (`Polynomial/Interpolation/Hermite.lean`, new)

```lean
-- H1 (uniqueness), over [Field F] [CharZero F] [DecidableEq F]
theorem eq_of_degree_lt_of_forall_iterate_derivative_eval_eq {m : Multiset F} {p q : F[X]}
    (hp : p.degree < m.card) (hq : q.degree < m.card)
    (h : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] p).eval y = (derivative^[k] q).eval y) :
    p = q
-- H2 (existence)
theorem exists_degree_lt_forall_iterate_derivative_eval_eq (m : Multiset F) (r : F → ℕ → F) :
    ∃ H : F[X], H.degree < m.card ∧
      ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] H).eval y = r y k
-- H3 (the remainder)  Result: hermite-interpolation-remainder
theorem exists_sub_eval_eq_iteratedDeriv_mul {a b : ℝ} (hab : a < b) {m : Multiset ℝ}
    (hm : m ≠ 0) (hmem : ∀ y ∈ m, y ∈ Set.Icc a b)
    (hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Set.Ioo a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ m.card f (Set.Ioo a b)) {H : ℝ[X]}
    (hH : H.degree < m.card)
    (hjet : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] H).eval y = iteratedDeriv k f y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, f x - H.eval x =
      iteratedDeriv m.card f ξ / m.card.factorial * ((m.map fun y => X - C y).prod).eval x
-- H4 (Lagrange)  Result: lagrange-interpolation-remainder
theorem exists_sub_eval_interpolate_eq_iteratedDeriv_mul {a b : ℝ} (hab : a < b)
    {s : Finset ℝ} (hs : s.Nonempty) (hsab : (s : Set ℝ) ⊆ Set.Icc a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ s.card f (Set.Ioo a b)) {x : ℝ}
    (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, f x - (Lagrange.interpolate s id f).eval x =
      iteratedDeriv s.card f ξ / s.card.factorial * (Lagrange.nodal s id).eval x
```

$\xi$ is in $(a, b)$, the interval the user names, not in the hull of the nodes and $x$; the
user narrows $[a, b]$ to get the sharper location.

### 4.3 Zeros and the Gauss remainder (additions to `Polynomial/Orthogonal/{Zeros,Gauss}.lean`)

```lean
-- Z1
theorem IsMomentPosDef.gaussNodes_subset_Ioo {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (gaussNodes μ k : Set ℝ) ⊆ Set.Ioo a b
-- G1: an interpolatory rule with nodal polynomial ⊥ degree < m is exact below |s| + m
theorem IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add
    (hs : IsOrthogonalPolynomial μ m (Lagrange.nodal s id)) (hμ) {p : ℝ[X]}
    (hp : p.degree < (s.card + m : ℕ)) :
    ∫ x, p.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x
-- G2
theorem gaussQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero (hμ) {k}
    (h : ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = 0) : gaussQuadrature μ k = μ
-- G3  Result: gauss-quadrature-remainder
theorem exists_integral_sub_integral_gaussQuadrature_eq (hμ) (hab : a < b) {k : ℕ} (hk : 0 < k)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ k =
      iteratedDeriv (2 * k) f ξ / (2 * k).factorial *
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ
-- G4, G5: f^{(2k)} ≥ 0 ⇒ ∫ f ∂gauss ≤ ∫ f ∂μ;  f^{(2k)} ≤ 0 ⇒ ∫ f ∂μ ≤ ∫ f ∂gauss
theorem integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg …
theorem integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos …
```

Z1 is stated with definiteness up to $k + 1$: with exactly $k$ support points the zeros of
$\pi_k$ are the support points and may be $a$ or $b$ ($\mu = \delta_a + \delta_b$, $k = 2$).
G3 needs $k > 0$: at $k = 0$ the rule is $0$ and $\int f\,d\mu = f(\xi)\mu(\mathbb{R})$ with
$\xi$ in the *open* interval fails for $\mu = \delta_a$.

### 4.4 Gauss–Radau (`Polynomial/Orthogonal/RadauLobatto.lean`, scaffold)

| ID | Name | Statement (hypotheses `hμ` and as listed) |
|---|---|---|
| R1 | `integral_radauMeasure` | $\int g\,d\,\mathsf{radauMeasure}(\mu, c) = \int\lvert x - c\rvert g\,d\mu$, every $\mu$, $c$, $g$ |
| R2 | `isFiniteMeasure_radauMeasure` | finite under `hμ` |
| R3 | `ae_mem_Icc_radauMeasure` | supported in $[a, b]$ |
| R4 | `IsMomentPosDef.notMem_gaussNodes_radauMeasure` | definite up to $k$, `hc` ⇒ $c \notin$ free nodes |
| R5 | `IsMomentPosDef.card_radauNodes` | $k + 1$ nodes |
| R6 | `isOrthogonalPolynomial_nodal_radauNodes` | the nodal polynomial is $\mu$-orthogonal to degree $< k$ |
| R7 | `radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero` | terminating case: the rule is $\mu$ |
| R8 | `integral_radauQuadrature` | the rule with interpolatory weights (nonnegative), `hc` |
| R9 | `matchesMoments_radauQuadrature` | `MatchesMoments μ (radauQuadrature μ c k) (2 * k + 1)`, every $k$, `hc`; Result: gauss-radau-quadrature |
| R10 | `ae_mem_Icc_radauQuadrature` | the rule lives in $[a, b]$ |
| R11 | `radauQuadrature_real_univ` | mass $\mu(\mathbb{R})$ |
| R12 | `MatchesMoments.eq_radauQuadrature` | $\nu$ on $c$ and $\le k$ further points matching $2k + 1$ moments is the Radau rule; Result: gauss-radau-quadrature-uniqueness |
| R13 | `exists_integral_sub_integral_radauQuadrature_eq` | the remainder, below; Result: gauss-radau-remainder |
| R14 | `integral_radauQuadrature_le_integral_of_iteratedDeriv_nonneg` | $c = a$, $f^{(2k+1)} \ge 0$: Radau $\le \int f$ |
| R15 | `integral_le_integral_radauQuadrature_of_iteratedDeriv_nonpos` | $c = a$, $f^{(2k+1)} \le 0$: $\int f \le$ Radau |
| R16 | `integral_le_integral_radauQuadrature_of_iteratedDeriv_nonneg` | $c = b$, $f^{(2k+1)} \ge 0$: $\int f \le$ Radau |
| R17 | `integral_radauQuadrature_le_integral_of_iteratedDeriv_nonpos` | $c = b$, $f^{(2k+1)} \le 0$: Radau $\le \int f$ |

```lean
theorem matchesMoments_radauQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    (k : ℕ) : MatchesMoments μ (radauQuadrature μ c k) (2 * k + 1)
theorem exists_integral_sub_integral_radauQuadrature_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) (hc : c = a ∨ c = b) (k : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂radauQuadrature μ c k =
      iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial *
        ∫ x, (x - c) * (orthogonalPolynomial (radauMeasure μ c) k).eval x ^ 2 ∂μ
theorem MatchesMoments.eq_radauQuadrature [IsFiniteMeasure ν] {k : ℕ}
    (h : MatchesMoments μ ν (2 * k + 1)) (hμ) (hc : c = a ∨ c = b)
    {s : Finset ℝ} (hν : ∀ᵐ x ∂ν, x ∈ insert c s) (hs : s.card ≤ k) : ν = radauQuadrature μ c k
```

The remainder keeps Gautschi's weight $(x - c)\tilde\pi_k(x)^2$ against $\mu$, one formula for
both endpoints, nonnegative at $c = a$ and nonpositive at $c = b$.

### 4.5 Gauss–Lobatto (same file)

L1–L3 as R1–R3 for `lobattoMeasure`; L4 `IsMomentPosDef.notMem_gaussNodes_lobattoMeasure`
(`t = a ∨ t = b` is not a free node); L5 `IsMomentPosDef.card_lobattoNodes` ($k + 2$, needs
$a < b$); L6 `isOrthogonalPolynomial_nodal_lobattoNodes`; L7 terminating case; L8
`integral_lobattoQuadrature` (weights nonnegative); L9 `matchesMoments_lobattoQuadrature`
(`(hab : a < b)`, `2 * k + 2`; Result: gauss-lobatto-quadrature); L10, L11 support and mass;
L12 the remainder (Result: gauss-lobatto-remainder):

```lean
theorem exists_integral_sub_integral_lobattoQuadrature_eq (hμ) (hab : a < b) (k : ℕ)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k + 2 : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂lobattoQuadrature μ a b k =
      iteratedDeriv (2 * k + 2) f ξ / (2 * k + 2).factorial *
        ∫ x, (x - a) * (x - b) * (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂μ
```

L13 `integral_le_integral_lobattoQuadrature_of_iteratedDeriv_nonneg` ($f^{(2k+2)} \ge 0$:
$\int f \le$ Lobatto), L14 `integral_lobattoQuadrature_le_integral_of_iteratedDeriv_nonpos`.
The Lobatto statements take $a < b$ throughout: at $a = b$ the two prescribed nodes merge and the
counting argument changes; nobody needs that case.

### 4.6 The Radau Jacobi matrix (J1–J3 in `RadauLobatto`, J4–J5 in `Krylov/Functions/Quadrature`)

```lean
-- J1: v_i = π_i(c)/‖π_i‖ is an eigenvector for c
theorem IsMomentPosDef.radauJacobiMatrix_mulVec_eq {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ) (hc0 : (orthogonalPolynomial μ k).eval c ≠ 0) :
    radauJacobiMatrix μ c k *ᵥ (fun i : Fin (k + 1) => (orthogonalPolynomial μ i).eval c /
        √(∫ x, (orthogonalPolynomial μ i).eval x ^ 2 ∂μ)) =
      c • fun i : Fin (k + 1) => (orthogonalPolynomial μ i).eval c /
        √(∫ x, (orthogonalPolynomial μ i).eval x ^ 2 ∂μ)
-- J2
theorem IsMomentPosDef.mem_spectrum_radauJacobiMatrix {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ) (hc : c = a ∨ c = b) : c ∈ spectrum ℝ (radauJacobiMatrix μ c k)
-- J3: the corner is invisible to walks of length ≤ 2k
theorem radauJacobiMatrix_pow_apply_zero_zero (μ : Measure ℝ) (c : ℝ) {k j : ℕ}
    (hj : j ≤ 2 * k) : (radauJacobiMatrix μ c k ^ j) 0 0 = (jacobiMatrix μ (k + 1) ^ j) 0 0
-- J4  Result: gauss-radau-jacobi-matrix
theorem spectralMeasure_radauJacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a b c : ℝ}
    (hμ) (hc : c = a ∨ c = b) {k : ℕ} (h : IsMomentPosDef μ (k + 1)) :
    spectralMeasure (radauJacobiMatrix μ c k) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) =
      radauQuadrature μ c k
-- J5
theorem Matrix.IsHermitian.integral_radauQuadrature_spectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' c : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (hc : c = a ∨ c = a')
    (b : n → 𝕜) {q : ℕ} (hq : q + 1 ≤ krylovGrade A b) (f : ℝ → ℝ) :
    ∫ x, f x ∂radauQuadrature (spectralMeasure A b) c q =
      ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (radauJacobiMatrix (spectralMeasure A b) c q) 0 0
```

J4's proof needs no characteristic polynomial: J3 gives the moments through degree $2k$ from
KS7's `spectralMeasure_jacobiMatrix`, J2 puts $c$ in the support, and R12 identifies the
measure. J4 mirrors KS7's `spectralMeasure_jacobiMatrix` and lives beside it (KS7 OQ6 (a): the
statement uses `spectralMeasure`, Matrix layer, so it cannot be in `Polynomial/`).

### 4.7 Bounds on $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ (`Krylov/Functions/QuadratureBounds.lean`, new)

```lean
-- K1
theorem Matrix.IsHermitian.exists_re_quadForm_cfc_sub_re_star_dotProduct_lanczosFA_eq
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} (hq : 0 < q)
    (hf' : ContDiffOn ℝ (2 * q : ℕ) f (Set.Ioo a a')) (b : n → 𝕜) :
    ∃ ξ ∈ Set.Ioo a a', RCLike.re (quadForm (cfc f A) b) -
        RCLike.re (star b ⬝ᵥ lanczosFA A f b q) =
      iteratedDeriv (2 * q) f ξ / (2 * q).factorial *
        ‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) q) *ᵥ b)‖ ^ 2
-- K2
theorem Matrix.IsHermitian.re_star_dotProduct_lanczosFA_le_of_iteratedDeriv_nonneg … (hD : ∀ x ∈ Set.Ioo a a', 0 ≤ iteratedDeriv (2 * q) f x) (b : n → 𝕜) :
    RCLike.re (star b ⬝ᵥ lanczosFA A f b q) ≤ RCLike.re (quadForm (cfc f A) b)
-- K3 (≤ 0, reversed): Matrix.IsHermitian.re_quadForm_cfc_le_re_star_dotProduct_lanczosFA_of_iteratedDeriv_nonpos
-- K4–K7 (Radau, no Hermitian hypothesis: both sides are 0 otherwise)
theorem integral_radauQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonneg {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs) (haa') (hf) (q : ℕ) (hf' : ContDiffOn ℝ (2 * q + 1 : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', 0 ≤ iteratedDeriv (2 * q + 1) f x) (b : n → 𝕜) :
    ∫ x, f x ∂radauQuadrature (spectralMeasure A b) a q ≤ RCLike.re (quadForm (cfc f A) b)
-- K5 re_quadForm_cfc_le_integral_radauQuadrature_of_iteratedDeriv_nonpos  (at a)
-- K6 re_quadForm_cfc_le_integral_radauQuadrature_of_iteratedDeriv_nonneg  (at a')
-- K7 integral_radauQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonpos  (at a')
-- K8 re_quadForm_cfc_le_integral_lobattoQuadrature_of_iteratedDeriv_nonneg
-- K9 integral_lobattoQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonpos
```

K1 states the Gauss weight as $\|\pi_q(\mathbf{A})\mathbf{b}\|^2$, the squared norm of the
unnormalised Lanczos vector $q$ (KS7's Lanczos link), rather than $\int\pi_q^2\,d\mu$.

### 4.8 CG (`Krylov/LinearSystems/CGQuadrature.lean`, new) and SLQ (addition to `Estimation/Trace/StochasticLanczosQuadrature.lean`)

```lean
-- C1  Result: cg-error-gauss-quadrature
theorem Matrix.PosDef.re_quadForm_sub_cgIterate_eq_integral_sub {A : Matrix n n 𝕜}
    (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) =
      ∫ x, x⁻¹ ∂spectralMeasure A (b - A *ᵥ x₀) -
        ∫ x, x⁻¹ ∂gaussQuadrature (spectralMeasure A (b - A *ᵥ x₀)) q
-- C2  Result: cg-error-gauss-radau-bounds
theorem Matrix.PosDef.re_quadForm_sub_cgIterate_le_integral_radauQuadrature_sub
    {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ} (ha : 0 < a) (haa' : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      ∫ x, x⁻¹ ∂radauQuadrature (spectralMeasure A (b - A *ᵥ x₀)) a q -
        ∫ x, x⁻¹ ∂gaussQuadrature (spectralMeasure A (b - A *ᵥ x₀)) q
-- C3: the lower bound with the right Radau rule at a'
theorem Matrix.PosDef.integral_radauQuadrature_sub_le_re_quadForm_sub_cgIterate …
-- S1, S2 (no Hermitian hypothesis)
theorem re_slq_le_re_girardHutchinson_cfc_of_iteratedDeriv_nonneg {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs) (haa') {f} (hf) {q : ℕ} (hq : 0 < q) (hf') (hD) (Ω : Matrix n m 𝕜) :
    RCLike.re (slq A f Ω q) ≤ RCLike.re (girardHutchinson (cfc f A) Ω)
theorem re_girardHutchinson_cfc_le_re_slq_of_iteratedDeriv_nonpos …
```

C2/C3 with J5 give the Golub–Meurant estimate in the form a CG implementation computes:
$\|\mathbf{r}_0\|^2\bigl(f(\tilde{\mathbf{T}})_{0,0} - f(\mathbf{T})_{0,0}\bigr)$ with
$f = x^{-1}$, $\mathbf{T}$ and $\tilde{\mathbf{T}}$ the Lanczos and Radau tridiagonals (a corollary
a user writes in two `rw`s; not stated, OQ7).

## 5. Files and placement

New files:

| File | Contents | Lines (est.) |
|---|---|---|
| `NLAlib/Polynomial/Orthogonal/RadauLobatto.lean` | the 7 definitions, 2 instances, 2 `rfl` lemmas (done); later R1–R17, L1–L14, J1–J3 | 750 |
| `NLAlib/Polynomial/Interpolation/Hermite.lean` | H1–H4 | 300 |
| `NLAlib/Krylov/Functions/QuadratureBounds.lean` | K1–K9 | 200 |
| `NLAlib/Krylov/LinearSystems/CGQuadrature.lean` | C1–C3 | 150 |
| `NLAlib/ForMathlib/Analysis/Calculus/LocalExtr/Rolle.lean` | F3 | 200 |
| `NLAlib/ForMathlib/MeasureTheory/Integral/MeanValue.lean` | F4, F5 | 80 |
| `NLAlib/ForMathlib/Analysis/Calculus/Deriv/Polynomial.lean` | F2 | 20 |
| `NLAlib/ForMathlib/Algebra/Polynomial/Derivative.lean` | F1 | 15 |

Additions to existing files (home by subject, P10):

| Declaration | Home | Reason |
|---|---|---|
| Z1 `IsMomentPosDef.gaussNodes_subset_Ioo` | `Polynomial/Orthogonal/Zeros.lean` | a statement about the zeros, beside `gaussNodes_subset_Icc` |
| G1–G5 | `Polynomial/Orthogonal/Gauss.lean` (426 lines now) | the exactness degree of `interpolatoryQuadrature` and the Gauss remainder are Gauss-rule facts |
| J4, J5 | `Krylov/Functions/Quadrature.lean` (775 lines now, +90) | Golub–Welsch for Radau beside `spectralMeasure_jacobiMatrix` |
| S1, S2 | `Estimation/Trace/StochasticLanczosQuadrature.lean` | properties of `slq` |

`Gauss.lean` grows to about 650 lines, `Quadrature.lean` to about 870, under F10. G3 imports
the Hermite file into `Gauss.lean`; the Hermite file imports only Mathlib and ForMathlib, so
P11 holds. The scaffold mirrors these paths; each scaffold file imports its NLAlib counterpart
and the scaffold files it depends on, so every job sees its sorried dependencies. No flags.

The Rolle file was first drafted as `ForMathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean`;
F11 rejects the name "Lemmas", so F2 joins `Deriv/Polynomial`, next to Mathlib's
`Polynomial.deriv`.

## 6. Consumers

| Statement | Consumer |
|---|---|
| H3, H4 | G3, R13, L12; Lebesgue-constant stage (gap survey #6: $\lVert f - p_n\rVert$ for Chebyshev interpolation); Daleckii–Krein divided differences (#8) |
| H1, H2 | the quadrature proofs; any later Hermite–Fejér or osculatory interpolation |
| F3, F4 | H3; the mean-value step of every remainder; later Peano-kernel forms |
| G1 | R8, L8, every later interpolatory rule with a known exactness degree (Gauss–Kronrod, anti-Gauss) |
| G3–G5 | K1–K3, S1, S2, C1 (sign), SLQ density bounds |
| R9–R17, L9–L14 | K4–K9, C2, C3 |
| R12, J1–J5 | J5 is what an implementation computes; consumer: C2/C3 in computable form, SLQ with Radau rules (deferred) |
| K1–K9 | CG and SLQ error estimation; Lanczos-FA a posteriori bounds; the maintainer's Krylov-aware trace estimation |
| C1–C3 | CG stopping criteria (Golub–Meurant Ch. 12); PCG through `pcgIterate_eq_mulVec_cgIterate` |
| S1, S2 | SLQ: the bias sign for $\log\det$, $\operatorname{tr}\mathbf{A}^{-1}$, heat trace |

## 7. Material from the prototype

Read (tchen-research/NLAlib at `cda0338`, `~/nlalib-proto`, read only):
`Polynomial/Interpolation/{Hermite,HermiteEndpoints,HermiteIntegral}.lean`,
`ForMathlib/Analysis/Calculus/RolleMultiplicity.lean`,
`ForMathlib/MeasureTheory/IntegralMeanValue.lean`,
`ForMathlib/Analysis/Calculus/IteratedDeriv.lean` (`iteratedDeriv_sub_eval_eqOn`),
`ForMathlib/Algebra/Polynomial/Basic.lean` (`eval_iterate_derivative_natDegree`),
`Polynomial/Quadrature/{HermiteRemainder,GaussDerivativeRemainder,RadauLobatto,RadauRemainder,
LobattoRemainder,EndpointMeasureRemainder,EndpointBounds,EndpointWeightPositivity,
EndpointJacobiData,EndpointJacobiMoments,EndpointJacobiRules,EndpointJacobiSigns,
RadauJacobiRemainder,EndpointModifiedPolynomials,EndpointDegenerate,EndpointZeroNorm}.lean`,
`Krylov/Quadrature/EndpointMatrixBounds.lean`.

Reused as proof material (cited in the `Proof:` lines and outlines): the multiset Rolle argument
(F3, minus a hypothesis), the mean value theorem without measurable selection (F4, F5), the
remainder by auxiliary function $g = f - H - K\omega$ (H3), the Gauss/Radau/Lobatto remainder
assemblies (G3, R13, L12), the Lobatto weight positivity by product polynomials (L8), the
exactness of endpoint rules from modified orthogonality (G1, R6, L6) and the sign corollaries.
The prototype has every remainder and bound of this stage, for the nondegenerate case.

Not reproduced, and why:

- **Explicit Hermite cardinal formulas** (`Lagrange.hermiteValueBasis`, `hermiteDerivativeBasis`,
  `hermiteInterpolate`, `hermiteEndpointInterpolate`, `hermiteTwoEndpointInterpolate`, 280
  lines): three special cases of one existence theorem (H2); they fix the multiplicity pattern.
- **`Fin`-indexed node families** (`endpointNodeFamily`, `twoEndpointNodeFamily`,
  `EndpointReindex`): our rules are measures on `Finset`s (KS7), so there is nothing to reindex.
- **The moment-functional layer** (`polynomialIntegral`, `HasPolynomialMoments`,
  `hankelMomentDet`, `IsMonicOrthogonalPolynomial` for a linear functional): KS7 works with
  measures and `IsMomentPosDef`; the prototype's support hypotheses
  `(q + 1 : ℕ∞) ≤ μ.support.encard` become `IsMomentPosDef`.
- **The Schur-border Jacobi matrices** (`finSymmetricBorder`, `leftRadauCorner`,
  `leftRadauJacobiMatrix L q a`, `lobattoJacobiMatrix`, about 900 lines with their weights,
  location and simplicity files): our Radau matrix is the Jacobi matrix with one entry changed,
  identified by moments and uniqueness (J1–J4, about 140 lines); Lobatto is deferred (OQ6).
- **Separate left/right theorems for exactness and remainders**: one theorem with
  `hc : c = a ∨ c = b`.
- **Real-only matrix statements** (`Matrix n n ℝ`, `hA.eigenvalues`): ours are over `RCLike 𝕜`
  with `spectrum ℝ A ⊆ Set.Icc a a'`, as KS3/KS7.
- `HermiteIntegral` (Hermite's contour formula), Chebyshev–Lobatto, Clenshaw–Curtis: other
  stages (analytic remainders, Lebesgue constants).

## 8. Mathlib search (pinned `.lake/packages/mathlib`, 2026-08-21)

| Need | Found | Use |
|---|---|---|
| Rolle | `exists_deriv_eq_zero`, `exists_hasDerivAt_eq_zero` (`Analysis/Calculus/LocalExtr/Rolle.lean`); no iterated or multiplicity version | F3 |
| Taylor | `taylor_mean_remainder_lagrange` (one node of full multiplicity) | not used; H3 covers an interior Taylor centre ($m = (n+1)\{x_0\}$, $x_0 \in (a, b)$), not an endpoint one |
| integral mean value | `exists_eq_const_mul_setIntegral_of_ae_nonneg` (`MeasureTheory/Integral/MeanValue.lean`), integrand $f(x)g(x)$ with $f$ continuous | not applicable to a pointwise remainder; F4 |
| top derivative of a polynomial | `natDegree_iterate_derivative`, `coeff_iterate_derivative`, `iterate_derivative_X_sub_pow_self`; no `iterate_derivative_natDegree` | F1 |
| iterated derivative of a polynomial function | `Polynomial.deriv` (first derivative only); searched `iteratedDeriv` in `Analysis/Calculus/Deriv/Polynomial.lean`, `Analysis/Polynomial/`: none | F2 |
| multiplicity and derivatives | `lt_rootMultiplicity_iff_isRoot_iterate_derivative`, `isRoot_iterate_derivative_of_lt_rootMultiplicity` (`Algebra/Polynomial/FieldDivision.lean`), `count_roots`, `roots_multiset_prod_X_sub_C`, `natDegree_multiset_prod_X_sub_C_eq_card` | H1, H3 |
| Lagrange interpolation | `Lagrange.interpolate`, `eval_interpolate_at_node`, `degree_interpolate_lt`, `nodal`, `nodal_insert_eq_nodal`, `basis` | H4, R6, L6 |
| Hermite / confluent interpolation, Gauss–Radau, Lobatto | searched (`hermite`, `Hermite`, `osculat`, `confluent`, `Radau`, `Lobatto`): only the Hermite *polynomials* (`Polynomial.hermite`, `RingTheory/Polynomial/Hermite/Basic.lean`), unrelated | §2 |
| iterated derivative of $x^{-1}$ | `iter_deriv_inv`, `iter_deriv_zpow` (`Analysis/Calculus/Deriv/ZPow.lean`) | C2, C3 |
| linear algebra for H2 | `Polynomial.degreeLT`, `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` | H2 |

Name collision: Mathlib's `Polynomial.hermite` (Hermite polynomials) is unrelated; this stage
introduces no `hermite*` name.

**Mathlib deviations: none.** No new predicate beside a Mathlib one, no new index type, no
scoped-instance replacement; `docs/design/Mathlib-deviations.md` is unchanged.

## 9. Open questions (with recommendations)

The decision sheet `state/decisions/KS8.json` has these in one line each.

**OQ1. The Hermite API.** (a) Multiset nodes; the remainder for any $H$ matching the jets;
existence (H2) and uniqueness (H1); no definition. (b) (a) plus `hermiteInterpolate m f`,
defined by choice from H2 (or as the inverse of the jet `LinearEquiv`) with its API.
(c) The prototype's explicit double-node and endpoint cardinal formulas (`Fin` nodes, three
special cases). (d) Lagrange remainder only, with Gauss as a limit of coalescing nodes.
**Recommendation (a).** Every consumer here picks some $H$ and never computes it, and the
remainder holds for all of them; a definition can be added when a consumer wants to compute
with it (Hermite–Fejér, osculatory error bounds). (c) hard-codes multiplicities; (d) needs a
limit argument (continuity of divided differences in the nodes) that is longer than (a).

**OQ2. Smoothness hypothesis.** (a) `ContinuousOn f (Icc a b)` and
`ContDiffOn ℝ N f (Ioo a b)`. (b) `ContDiffOn ℝ N f (Icc a b)`. (c) The prototype's minimal
form: continuity on $[a, b]$, `DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b)` for $k < N$, and
continuity of the $N$-th derivative on $(a, b)$ for the mean-value forms. **Recommendation
(a).** One standard predicate, discharged by `fun_prop`/`ContDiff` lemmas, and only continuity at
the endpoints, which a Radau node at $0$ for $\sqrt{x}$ or $x\log x$ needs; (b) excludes those;
(c) is weaker by an amount no consumer uses and spreads over three hypotheses.

**OQ3. The Radau definition.** (a) One `radauQuadrature μ c k` with modified measure
$\lvert x - c\rvert\,d\mu$; exactness and remainder for $c \in \{a, b\}$, bounds with $c$ fixed.
(b) Two definitions, left (`(x - a)dμ`) and right (`(b - x)dμ`). (c) Define the rule as the
spectral measure of Golub's modified Jacobi matrix (Golub–Meurant's construction, the
prototype's). **Recommendation (a).** Half the definitions and theorems of (b), the same
remainder formula at both ends; (c) makes exactness a theorem about matrix powers and puts the
definition in the Matrix layer, while (a) keeps it beside `gaussQuadrature` and gets (c) as J4.

**OQ4. What $k$ counts.** (a) The free nodes: Radau has $k + 1$ nodes, exact through degree
$2k$; Lobatto $k + 2$, through $2k + 1$; Radau with $q$ free nodes pairs with $q$ Lanczos steps.
(b) The total number of nodes. **Recommendation (a).** It matches Gautschi's $n$, Golub–Meurant's
$\tilde{\mathbf{J}}_{k+1}$ after $k$ Lanczos steps, and makes the Gauss/Radau pairing in C2
read `gaussQuadrature μ q` against `radauQuadrature μ a q`.

**OQ5. Remainder form.** (a) The mean-value form with $\xi$ (Gautschi Theorem 1.48) as the
headline, sign bounds as corollaries. (b) Sign bounds only (no mean-value lemma, about 60 fewer
lines). (c) Also the Peano-kernel form. **Recommendation (a).** The $\xi$ form is the cited
theorem, gives explicit error bounds ($\lvert f^{(2k)}\rvert \le M$ ⇒ error $\le
M\|\pi_k\|^2/(2k)!$) that (b) cannot, and its extra cost is F4/F5 (one M, one S); (c) has no
consumer.

**OQ6. Jacobi-matrix realisations.** (a) Golub's Radau matrix (one modified corner) with its
Golub–Welsch theorem and the quadratic-form bridge (J1–J5); Lobatto deferred. (b) None:
measure-level rules only. (c) Both, Lobatto with its two modified entries (about 15 more
declarations, one L; the prototype's Schur border). **Recommendation (a).** The Radau matrix is
what Golub–Meurant compute from Lanczos and costs five declarations through moment matching and
uniqueness; the Lobatto matrix needs a $2\times2$ solve and a Lobatto uniqueness theorem, and
Lobatto bounds are used less (for $x^{-1}$ the Lobatto rule bounds from above, as the left Radau
rule already does, and needs one more Lanczos step).

**OQ7. Form of the matrix-level bounds.** (a) Measure form
`∫ x, f x ∂radauQuadrature (spectralMeasure A b) a q`, no grade hypothesis, plus the one bridge
J5 to $\|\mathbf{b}\|^2 f(\tilde{\mathbf{J}})_{0,0}$. (b) Each bound in the Jacobi-matrix form,
with $q + 1 \le$ grade. **Recommendation (a).** The bounds then hold for every $q$ and need no
Hermitian hypothesis; a user wanting the computable form rewrites with J5.

**OQ8. Sign orientations.** (a) Both orientations ($f^{(N)} \ge 0$ and $\le 0$) as separate
theorems at both levels (G4/G5, R14–R17, L13/L14, K2–K9, S1/S2). (b) Only $\ge 0$; users apply
it to $-f$. **Recommendation (a).** The main consumers come in both signs ($x^{-1}$ and $\log$
have alternating derivatives, $e^{x}$ positive ones), and $-f$ costs a `cfc_neg`/`iteratedDeriv_neg`
detour at every use; each extra theorem is S.

**OQ9. Bundle the smoothness and sign hypotheses?** (a) No: keep `ContinuousOn`, `ContDiffOn`
and the pointwise sign of `iteratedDeriv`. (b) A predicate such as
`HasNonnegIteratedDerivOn f N a b`. **Recommendation (a).** They are Mathlib predicates and a
one-line `∀`; a bundle would need its own API (constructors for $x^{-1}$, $\log$, $\exp$) for no
gain in the proofs (CONTRIBUTING §5.4 asks for interfaces for raw conditions on NLAlib objects;
these are conditions on a scalar function).

**OQ10. Consumers in this stage.** (a) Include the CG identity and Golub–Meurant bounds (C1–C3)
and the SLQ bias sign (S1, S2). (b) Stop at K1–K9. **Recommendation (a).** They are the reason
KS7 and Krylov-Spectral deferred the stage, C1 is the classical CG–Gauss identity not yet in the
library, and together they cost five declarations (two M).

**OQ11. Citation locators.** The Gautschi theorem numbers (1.45, 1.48, 3.2, 3.3, 3.6, 3.7,
§1.4.2, §3.1.1), Davis (Theorems 1.6.3, 2.7.1, 3.1.1, 3.5.1), Golub 1973 §7 and Golub–Strakoš §3
are from memory and the prototype's docstrings, marked "locator to check" (KS7 decision L1 (b)).
Golub–Meurant is cited by chapter (KS7 L2 (a)). **Recommendation:** keep "to check" until
verified against the books, as for KS7.

## 10. Proof plan

**Counts.** 65 declarations: 41 S, 19 M, 5 L, 0 H; about 1,600 lines of proof (the sum of the `Proof:` estimates). The five L:
F3 (Rolle with multiplicities, about 180 lines, a port), H3 (Hermite remainder, 120, a port),
G3, R13, L12 (the three quadrature remainders, 70–80 each, assemblies of H2, H3, F4/F5 and
exactness). Every L has a complete prototype proof for the nondegenerate case; our extra work is
the terminating case (two lines given G2/R7/L7) and the `Finset` bookkeeping.

**Waves** (from the `depends_on` lists in `ks8-targets.json`):
0: F1, F2, F3, F4, H1, Z1, G1, G2, R1, R2, R3, L1, L2, L3, J1, J3, C1 (17 jobs);
1: F5, H2, H3, R4, R7, L4, L7, J2; 2: H4, G3, R5, R6, R10, L5, L6, L10;
3: G4, G5, R8, L8, K1; 4: R9, L9, K2, K3, S1, S2; 5: R11, R12, R13, L11, L12;
6: R14–R17, L13, L14, J4; 7: J5, K4–K9; 8: C2, C3. Critical path:
R1 → R4 → R5 → R8 → R9 → R13 → R15 → K5 → C2 (9 waves). The waves are a
safety order; with the scaffold in place later waves can be released early.

**For the prover brief.**

- The terminating cases are part of every unconditional statement (G3, R7–R11, R13, L7–L12):
  a proof that assumes definiteness is incomplete. The pattern is always: norm of the relevant
  orthogonal polynomial $= 0$ ⇒ the rule is $\mu$ (G2, R7, L7) and the weight integral is $0$.
- Integrability of $f$: `ContinuousOn.integrableOn_Icc` and `Measure.restrict_eq_self_of_ae_mem`,
  as in KS7's `abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith`; of polynomials:
  `integrable_eval_of_ae_mem_Icc`.
- Derivatives on the open interval: `ContDiffOn.continuousOn_iteratedDerivWithin`,
  `ContDiffOn.differentiableOn_iteratedDerivWithin`, `iteratedDerivWithin_of_isOpen`.
- `IsOrthogonalPolynomial.integral_eval_eq_sum`'s private helper
  `integral_eval_eq_sum_of_degree_lt` is invisible from the scaffold: G1 re-proves it as a
  private lemma (15 lines) or is proved in place in `NLAlib/`.
- The modified measures are finite only with `hμ` (R2, L2): use
  `haveI := isFiniteMeasure_radauMeasure hμ c` before applying KS7 lemmas to them.

## 11. Literature

In `docs/references.bib`: `Gautschi2004` (Theorems 1.45, 1.48, 3.2, 3.3, 3.6, 3.7; §1.4.2,
§3.1.1; to check), `GolubMeurant2010` (Ch. 6, 7, 12), `Szego1975` (Theorem 3.3.1),
`Trefethen2019` (Ch. 11), `UbaruChenSaad2017` (§3). Added with the skeleton:

- `Davis1975`: P. J. Davis, *Interpolation and Approximation*, Dover, 1975 (Theorem 1.6.3
  generalised Rolle, 2.7.1 Hermite interpolation, 3.1.1 Lagrange remainder, 3.5.1 Hermite
  remainder; to check).
- `Golub1973`: G. H. Golub, "Some modified matrix eigenvalue problems", SIAM Review 15 (1973),
  318–334 (§7, Gauss–Radau and Lobatto by modified Jacobi matrices; to check).
- `GolubStrakos1994`: G. H. Golub and Z. Strakoš, "Estimates in quadratic formulas", Numer.
  Algorithms 8 (1994), 241–268 (§3, CG error bounds; to check).

C8 will warn for the three new keys until a proved declaration cites them (scaffold docstrings
are not read), as for KS7's `GolubWelsch1969`.

New result ids: `hermite-interpolation-remainder`, `lagrange-interpolation-remainder`,
`gauss-quadrature-remainder`, `gauss-radau-quadrature`, `gauss-radau-quadrature-uniqueness`,
`gauss-radau-remainder`, `gauss-lobatto-quadrature`, `gauss-lobatto-remainder`,
`gauss-radau-jacobi-matrix`, `cg-error-gauss-quadrature`, `cg-error-gauss-radau-bounds`. To check
against the explorer's literature map for near-duplicates (R2); the prototype's atlas uses
`gauss-quadrature-derivative-remainder` and `gauss-radau-lobatto`, which may be the existing
ids to reuse.

## 12. Deferred

1. **The Lobatto Jacobi matrix** (Golub 1973; two modified entries from a $2\times2$ system) with
   Golub–Welsch and Lobatto uniqueness. Needs: L9 and a uniqueness argument on $k + 2$ points.
2. **Strictly positive Radau/Lobatto weights** under definiteness (R8/L8 give $\ge 0$). No
   consumer.
3. **A `slqRadau` estimator** and SLQ two-sided bounds per probe; needs a design of the estimator
   (which bound $a$ per probe) in the SLQ layer.
4. **Block Gauss–Radau** for block Lanczos (Krylov-Block).
5. **Analytic remainders**: Hermite's contour formula (prototype `HermiteIntegral`), Gauss error
   for analytic $f$ on a Bernstein ellipse with explicit constants; Peano kernels.
6. **Chebyshev–Markov–Stieltjes inequalities** (KS7 §8 item 3).
7. **Anti-Gauss, Gauss–Kronrod**, which G1 makes cheap to state.
8. **A Hermite interpolant definition** (OQ1 (b)) when a consumer computes with it.
