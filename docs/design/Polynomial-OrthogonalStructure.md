# Design note: the structure theory of orthogonal polynomials (stage KS7)

Status: draft, 2026-10-24, by an Opus agent from the orchestrator's brief; Fable review folded in 2026-10-24; maintainer decisions of 2026-10-24 recorded: OQ1 (a), OQ2 (a), OQ3 (a), OQ6 (a), S1 (a), S2 (c), L1 (b), L2 (a), and the SLQ integration ("Interface for SLQ"); OQ4 and OQ5 still open.

Monic orthogonal polynomials of a finite measure on ℝ with compact support, their three-term
recurrence and Jacobi matrix, their zeros, the canonical Gauss rule, and the link to Lanczos:
the Lanczos vectors are the orthogonal polynomials of $\mu_{\mathbf{A},\mathbf{b}}$ applied to
$\mathbf{b}$, and the Lanczos tridiagonal is the Jacobi matrix of $\mu_{\mathbf{A},\mathbf{b}}$.

Written against the tree at `6a845a2` (worktree `nlalib-design`, branch `design/ks7-slq`;
reference build `~/nlalib`). Every signature in §4 was elaborated with `lake env lean` (with
`set_option autoImplicit false`) in two scratch files, `/tmp/claude-1000/ks7-scratch/Poly.lean`
(the Polynomial layer, importing `NLAlib.Polynomial.Orthogonal.Gauss`) and `…/Krylov.lean` (the
Matrix and Krylov additions, importing `NLAlib.Krylov.Functions.Quadrature` and
`NLAlib.Krylov.Processes.LanczosRecurrence`), with `sorry` bodies; the four recurrence equations
are proved there by `rfl`. No proof was attempted otherwise. The junk-value claims of §0 item 3
were checked in exact rational arithmetic on random atomic measures (`…/check.py`). After the
Fable review the new and changed signatures (the instance, the split steps of §10, the finset
constructor, the Ritz-value bridges, the realisation lemmas) were elaborated again in the same two
files; all elaborate, and `inferInstance` now finds `IsFiniteMeasure (gaussQuadrature μ k)`.

KS7 was deferred by `docs/design/Krylov-Spectral.md` §8 item 1 ("existence and real-rootedness
of the degree-$n$ orthogonal polynomial …, uniqueness of the monic one, the three-term recurrence
…, Christoffel–Darboux, the canonical Gram–Schmidt polynomials (SD4(c)), `jacobiMatrix`, the
continued fraction, and interlacing of zeros"; "no consumer this round"), by SD4 ("(c) waits for
KS7 and a consumer that needs the canonical polynomials, such as the Lanczos polynomials"), §2.4
("No Jacobi matrix or continued fraction (KS7, deferred)"), §5 (Gauss–Radau and Lobatto "later
(KS7)") and §7 (the Lanczos polynomials, `X_mul_poly`, `sub_mul_sum_eval_poly_mul`,
`jacobiMatrix`, `jacobiFraction` "deferred to KS7"). It is the Jackson note's OP1 and the rest of
OP2/OP3 (`Polynomial-Jackson-Moments.md` §5), and PORT_KRYLOV's D6.

## Changes after the Fable review (2026-10-24)

The review is `~/nlalib-harness/reports/Review-Polynomial-OrthogonalStructure.md` (11 comments,
2 blocking). Its verdict: the mathematics is right in every degenerate case and the interface is
the expected one. What I did with each comment:

1. **[blocking] #27 duplicates Mathlib.** Adopted. `Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`
   (`Mathlib/Analysis/Polynomial/Order.lean`) has it, with the root hypothesis vacuous for
   `roots = 0`. The ForMathlib file and job #27 are gone; #30 cites the Mathlib lemma; §11's
   "searched, none" is corrected (my search missed `Order.lean`).
2. **[blocking] `IsFiniteMeasure (gaussQuadrature μ k)`.** Adopted: instance #63
   `isFiniteMeasure_gaussQuadrature` (§2, §4.6), proved in the skeleton by `unfold; infer_instance`;
   checked that `inferInstance` then succeeds and that all signatures still elaborate.
3. **[consider] degenerate analysis; Golub–Welsch past the support.** Adopted the docstring
   sentence: past the support size the extra eigenvalues of $\mathbf{J}_{k+1}$ carry no weight
   (§4.10). No statement change.
4. **[should] record the rejected definitions.** Adopted: §0 item 2 and the Mathlib-deviations
   paragraph now say why Gram–Schmidt in `Lp ℝ 2 μ` and the Heine/Hankel determinant formula lose.
5. **[should] Ritz values = Gauss nodes.** Adopted: #60 `HasOrthonormalCols.nodal_eq_orthogonalPolynomial`
   and #61 `HasOrthonormalCols.gaussNodes_spectralMeasure_eq` (§4.10), both under
   `q ≤ krylovGrade A b` (past the grade the Gauss nodes can contain a spurious $0$). They bridge
   the KS3 Ritz-value vocabulary and the new one; #54 supersedes nothing.
6. **[should] the finset constructor.** Adopted: #57 `isMomentPosDef_iff_forall_finset`
   (§4.2), and OQ5's recommendation now includes it. It carries #30/#31/#34 (through the shared
   helper of item 9) and #49.
7. **[consider] five small items.** (i) `isTridiagonal_jacobiMatrix`: declined; `IsTridiagonal` is
   NLAlib Matrix vocabulary, which P11 keeps out of `Polynomial/`, so it would sit in Krylov with no
   consumer, and `lanczosTridiagonal_eq_jacobiMatrix` with `IsGradedKrylovBasis.isTridiagonal`
   gives it for spectral measures. (ii) `integral_orthogonalPolynomial_sq_eq_prod`: adopted (#62, S);
   it is what makes $\beta_0 = \mu(\mathbb{R})$ pay. (iii) Chihara for the name `IsMomentPosDef`:
   adopted, cited in its docstring with locator to check; new key `Chihara1978`. (iv) the
   `jacobiMatrix` collision is immaterial: adopted in OQ4. (v) "T7: real by subject" for
   `spectralMeasure_jacobiMatrix`: adopted in §4.11 item 4.
8. **[should] the P10 flag's intended home.** Adopted: the home by subject is
   `Matrix/Spectral/SpectralMeasure.lean` (P11 keeps `spectralMeasure` out of Polynomial for
   good); the flag says it is blocked only by the proof's use of Lanczos, and that the charpoly
   route (§8 item 9) would unblock it (§6, OQ6).
9. **[should] #17 depends on #18; one helper for the three zero theorems.** Adopted: #18 is now
   a dependency of #17 (through #17c) and comes first; the private helper #30a
   `IsMomentPosDef.false_of_ae_nonneg_mul` (the reviewer's signature) carries #30, #31 and #34, and
   #30 drops from L to M.
10. **[should] split the four L items.** Adopted: #17 into #58, #59, #17a–#17d and the
    induction; #50 into #50a–#50d and the assembly; #55 into #55a, #55b and the chain; #30 by
    item 9. Every row of §10 is now at most 50 lines; there is no L left.
11. **[consider] literature.** Adopted: §9 records the reviewer's matching recollection of
    Gautschi's Theorems 1.27, 1.19–1.20, 1.31, 3.1, 1.45–1.46 and Szegő's 3.2.1–3.3.2 (still "to
    check" against the book: two memories are not a PDF); positive definiteness is cited to
    Gautschi §1.1, not a theorem; Golub–Welsch 1969 is cited by section (§2); Mathlib's
    `Matrix.gram` / `Matrix.posDef_gram_iff_linearIndependent` is recorded as the future bridge
    of OQ5(b) (§8 item 7, §11).

The reviewer's verdict on each open question is noted beside my recommendation below.

## Maintainer decisions and the SLQ integration (2026-10-24)

The maintainer decided OQ1 (a), OQ2 (a), OQ3 (a), OQ6 (a) (each marked "Decided" below), and the
dashboard items S1 (a) (the Lanczos column formula as drafted, §4.11 item 1), S2 (c) (the weights
form of the Gauss rule and Golub–Welsch over `𝕜`, "we are also doing SLQ"), L1 (b) (locators stay
"to check" until verified against the books) and L2 (a) (Golub–Meurant by chapter; the two
"Theorem 6.6" citations in §4.6 and §4.10 are now "Ch. 6"). OQ4 (names) and OQ5 (definiteness
form; the maintainer asked whether Mathlib has it, answered in OQ5) stay open.

Direction, verbatim: "I want the OP and SLQ stuff to integrate well. I.e. mathematically. we
should think of SLQ and GQ on the individual probe densities." So SLQ is the average over probes
$\boldsymbol{\omega}_j$ of the Gauss rules `gaussQuadrature (spectralMeasure A ω_j) q` of the probe
spectral measures, and Lanczos enters only through
`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`. The new section "Interface for SLQ"
(before §5) fixes what SLQ consumes; it adds seven theorems (#64–#70), marked **[SLQ-1]** in §10
with the existing ones SLQ uses (#40, #42, #43, #54).

## 0. Summary and main findings

1. **Scope chosen: the part with consumers, plus the classical core it rests on.** In scope:
   the canonical monic orthogonal polynomials (by the Stieltjes recurrence), their orthogonality,
   norms, uniqueness and moment invariance; positive definiteness of a measure up to a degree;
   real simple zeros inside any interval carrying the measure; the canonical Gauss rule
   `gaussQuadrature μ k`, its exactness, support, mass, positive weights and **uniqueness**; the
   Jacobi matrix; the Lanczos link (vectors, coefficients, tridiagonal, quadrature); Golub–Welsch
   for an arbitrary measure. Deferred with what each needs (§8): interlacing, strict interior
   zeros, Christoffel–Darboux and the Christoffel function, Chebyshev–Markov–Stieltjes,
   Gauss–Radau and Lobatto, the continued fraction, orthonormal polynomials, a Hankel bridge.
   **73 declarations to prove** (66 public theorems, 1 instance, 6 private steps fixed in the
   skeleton so that each proof stays short) **and 7 definitions**: 42 S (6 of them done in the
   skeleton: 4 `rfl`, 1 move of an existing proof, the instance), 31 M, 0 L; 66 dispatched jobs;
   about 2,250 lines in 3 new files and 6 existing ones (after the review and the SLQ interface).
2. **The definition is the Stieltjes procedure, so the recurrence is `rfl`.**
   `orthogonalPolynomial μ k` is defined by the three-term recurrence with
   $\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$ and $\beta_k = \int\pi_k^2\,d\mu/
   \int\pi_{k-1}^2\,d\mu$ (Lean's $x/0 = 0$). It is monic of degree $k$ for every $k$ and every
   measure, by algebra alone. This is the form Lanczos computes, so the Lanczos link compares
   two recursions with the same coefficients instead of a Gram–Schmidt construction with a
   recursion. Rejected alternatives: Gram–Schmidt in `Lp ℝ 2 μ` (an inner-product space, so
   Mathlib's `InnerProductSpace.gramSchmidt` applies there) returns equivalence classes, not
   polynomials, and cannot recover a degree-$k$ representative when polynomials do not embed
   injectively, which is the case for every finitely supported $\mu$, the main consumer; the
   Heine/Hankel determinant formula divides by a Hankel determinant that vanishes past the
   support. The recurrence definition has Mathlib's precedent: `Polynomial.Chebyshev.T` is a
   recurrence and its characterisations are theorems.
3. **Most theorems need no nondegeneracy hypothesis.** With these junk values, a measure with
   $N$ support points has $\pi_N$ equal to the nodal polynomial of its support and every
   $\pi_k$, $k \ge N$, a multiple of it. So orthogonality
   (`isOrthogonalPolynomial_orthogonalPolynomial`), moment matching of the Gauss rule, its
   support in $[a, b]$, its mass, the identification with the Lanczos rule, the Lanczos vector
   and coefficient formulas and Golub–Welsch hold **for every $k$** (past the support size the
   Gauss rule is $\mu$ itself, as the Lanczos rule is past the grade). Only uniqueness of the
   monic polynomial, real simple zeros, the count of the nodes and strict positivity of the
   weights take the definiteness hypothesis `IsMomentPosDef μ k`. This follows the 2026-10-22
   T13 review of KS3, which removed `q ≤ krylovGrade A b` wherever it was not needed.
4. **Uniqueness of the Gauss rule is one short theorem and carries the consumers.** Any finite
   measure carried by at most $k$ points that matches $2k$ moments of $\mu$ is
   `gaussQuadrature μ k` (`MatchesMoments.eq_gaussQuadrature`). Proof: both are carried by at
   most $2k$ points and agree on polynomials of degree $< 2k$, and two finite measures on a finite
   set $T$ that match $\lvert T\rvert$ moments are equal (`MatchesMoments.eq_of_ae_mem`, Lagrange
   basis). So `lanczosQuadrature A b q = gaussQuadrature (spectralMeasure A b) q` is three lines
   from the existing KS3 theorems, with no frame, no Ritz-value set and no grade hypothesis.
5. **The Lanczos link needs no uniqueness either.** Column $j$ of the canonical Lanczos basis is
   $\pi_j(\mathbf{A})\mathbf{b}/\|\pi_j(\mathbf{A})\mathbf{b}\|$: both $\pi_j(\mathbf{A})\mathbf{b}$
   and $r_j\mathbf{q}_j$ differ from $\mathbf{A}^j\mathbf{b}$ by an element of $\mathcal{K}_j$
   and are orthogonal to $\mathcal{K}_j$, so they are equal. The orthogonality is in real
   polynomials through $\mathcal{K}_j = \operatorname{span}\{\mathbf{A}^i\mathbf{b}\}$, which
   avoids the complex polynomials that `mem_krylovSpace_iff` produces over `ℂ`. Then
   $\alpha_j$, $\beta_j$ and the whole tridiagonal follow from one integral identity,
   $\int x\pi_k\pi_{k+1}\,d\mu = \int\pi_{k+1}^2\,d\mu$.
6. **Golub–Welsch for any measure is a corollary of the Lanczos link, by realisation.** The
   Gauss rule $\nu$ of $\mu$ is the spectral measure of a diagonal matrix $\mathbf{D}$ and a
   vector $\mathbf{w}$; Lanczos on $(\mathbf{D}, \mathbf{w})$ gives
   $\nu = \mu_{\mathbf{J}(\nu),\,\|\mathbf{w}\|\mathbf{e}_0}$, and $\mathbf{J}(\nu) =
   \mathbf{J}(\mu)$ because $\nu$ matches $2k$ moments. No tridiagonal determinant and no
   unreduced-tridiagonal eigenvector theory is needed. The statement needs Matrix vocabulary
   (`spectralMeasure`), so it lives in Krylov (flagged, §6).
7. **Consumers are thinner than the theory.** The parallel SLQ draft
   (`docs/design/Estimation-SLQ.md`, which appeared while this note was being finished; read, not
   edited) says in its §12 that SLQ needs **no KS7 result**: exactness, the Gauss-rule reading,
   Golub–Welsch from the recurrence and M0 all exist (KS3, KS2), and its Kolmogorov bound uses a
   finite Abel summation, not Chebyshev–Markov–Stieltjes. I agree, as Krylov-Spectral §0 item 1
   found for KS3. What KS7 gives SLQ is optional: the frame-free statement of its measure as an
   average of `gaussQuadrature (spectralMeasure A ω_j) q` (the SLQ note's own §12 wish), the
   dependence on $\mu_{\mathbf{A},\boldsymbol{\omega}}$ only through $2q$ moments, and the
   recurrence-coefficient reading of Lanczos. So the stage is justified by the brief and by the
   maintainer's standing wish for the layer (PORT_KRYLOV D6: "a layer the maintainer wants
   explicitly"), not by a blocking consumer; OQ1 offers a minimal variant. The pieces with no
   consumer at all are deferred (§8).
8. **What Mathlib has** (searched at the pinned commit, §11): Lagrange interpolation, roots and
   multiplicities, `Measure.ae_mem_finset_iff` (a measure carried by a finite set is a sum of
   Dirac masses), `setIntegral_finset`, `integral_eq_zero_iff_of_nonneg_ae`, the Chebyshev
   families and Chebyshev–Gauss. Searched, none: general orthogonal polynomials, the Stieltjes
   procedure, a three-term recurrence for a measure, a Jacobi matrix (Mathlib's `jacobiMatrix`
   is the Jacobian of an algebra presentation), Gauss quadrature beyond `measureT`,
   Christoffel–Darboux, Hankel matrices (but `Matrix.gram` is the bridge, §8 item 7).
   Positivity of a root-free real polynomial is in Mathlib
   (`Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`, found by the review).

## Open questions for the maintainer

Each changes a statement or a name that provers will be given fixed. Everything else proceeds as
recommended unless the maintainer objects.

**OQ1. The scope boundary.** **Decided 2026-10-24: (a).**
- (a) As drafted (§0 item 1): the core, the Gauss rule with uniqueness, the Lanczos link and
  general Golub–Welsch.
- (b) (a) without general Golub–Welsch (`spectralMeasure_jacobiMatrix`,
  `HasOrthonormalCols.gaussQuadrature_succ_eq_sum`): no Lean consumer; the Lanczos form exists
  (`Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`). Saves #55a, #55b, #55, #56 (two M, two S).
- (c) (a) plus interlacing and strict interior zeros (Gautschi's Theorems 1.19 and 1.20, locators
  as verified by the Jackson note; §8 item 1), about 250 lines, one L.
- (d) The minimal stage: §4.1–§4.6 and #54 only (the polynomials, zeros, the Gauss rule with
  uniqueness, and the Lanczos identification), without the Jacobi matrix, the Lanczos link
  (§4.9) and Golub–Welsch: about 37 theorems, no L in Krylov. The SLQ note needs none of KS7 (§0
  item 7), so this is the variant a strictly consumer-driven reading gives.
- Recommendation: **(a)**. Golub–Welsch is the result the brief names and the classical reading
  of "nodes are eigenvalues of $\mathbf{J}$, weights are $\beta_0$ times squared first
  components"; its proof is a chain of S steps once the Lanczos link exists. Interlacing waits
  for a consumer (Ritz-value interlacing already follows from Poincaré separation,
  Krylov-Spectral §7).
- Reviewer: agrees with (a).

**OQ2. Junk values and hypotheses: unconditional statements where true.** **Decided 2026-10-24: (a).**
- (a) As drafted: theorems that hold for every $k$ under the junk conventions of §2 are stated
  without a definiteness hypothesis (§0 item 3); definiteness appears only where the statement
  is false without it.
- (b) Every Gauss and zero theorem takes `IsMomentPosDef μ k`, the textbook setting. Shorter
  proofs (no degenerate branch), weaker statements; the Lanczos identification would then need
  `q ≤ krylovGrade A b`, which the 2026-10-22 review removed from the KS3 theorems.
- Recommendation: **(a)**. The degenerate branch costs one M lemma
  (`ae_mem_gaussNodes_of_not_isMomentPosDef`) and one M lemma
  (`interpolatoryQuadrature_eq_self_of_ae_mem`), reused by four theorems.
- Reviewer: agrees with (a); re-derived every degenerate value (comment 3).

**OQ3. The convention for $\beta$.** **Decided 2026-10-24: (a).**
- (a) Gautschi's: `jacobiBeta μ k` $= \int\pi_k^2/\int\pi_{k-1}^2$, the coefficient of the
  monic recurrence, with $\beta_0 = \mu(\mathbb{R})$; the Jacobi matrix has $\sqrt{\beta_k}$ off
  the diagonal; the Lanczos coefficient is `(lanczosState A b (j + 1)).beta = √(jacobiBeta … (j + 1))`.
- (b) The off-diagonal entry itself, $\|\pi_k\|/\|\pi_{k-1}\|$ (Golub–Meurant's $\eta_k$,
  Lanczos's $\beta$): then the Lanczos coefficient is an equality without `√`, and the monic
  recurrence carries `jacobiBeta μ k ^ 2`.
- Recommendation: **(a)**. The recurrence, the norm identity $\|\pi_{k+1}\|^2 =
  \beta_{k+1}\|\pi_k\|^2$ and moment invariance are square-root free, and Gautschi's notation is
  the field's. The square root appears once, in the Jacobi matrix and the Lanczos bridge.
  #62 ($\|\pi_k\|^2 = \prod_{i\le k}\beta_i$) is what the $\beta_0 = \mu(\mathbb{R})$ convention buys.
- Reviewer: agrees with (a).

**OQ4. Names.** **Open.**
- `orthogonalPolynomial μ k` (alternative `monicOrthogonalPolynomial`, if the orthonormal family
  is later added as `orthonormalPolynomial`).
- `IsMomentPosDef μ k` for "positive definite on polynomials of degree $< k$" (alternatives:
  `IsPosDefOnDegreeLT`, `HasPosDefMoments`; "quasi-definite" is wrong, it means nonzero Hankel
  determinants).
- `jacobiAlpha`, `jacobiBeta`, `jacobiMatrix` (alternatives: `recurrenceAlpha`,
  `recurrenceBeta`). `NLAlib.jacobiMatrix` and Mathlib's
  `Algebra.PreSubmersivePresentation.jacobiMatrix` are in different namespaces, and Mathlib's is
  used by dot notation on a presentation, so no `open` reaches it: the collision is immaterial
  (review comment 7(iv)).
- `gaussNodes μ k` as a definition, against writing `(orthogonalPolynomial μ k).roots.toFinset`
  in each statement (it appears in nine).
- Recommendation: **as drafted**. Each name says what the object is (N11), and the
  `jacobi` prefix keeps the three coefficient objects together in search. `IsMomentPosDef`
  follows Chihara's "positive-definite moment functional" and cites it.
- Reviewer: agrees, with comment 7(iii)–(iv) (adopted).

**OQ5. Positive definiteness: the defining form.** **Open.**
- (a) As drafted, the $L^2$ form: `∀ p : ℝ[X], p ≠ 0 → p.degree < k → 0 < ∫ x, p.eval x ^ 2 ∂μ`,
  with the two constructors a consumer has: `isMomentPosDef_succ_iff` (norms of the orthogonal
  polynomials) and `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff` (the grade).
- (b) The Hankel form, `(Matrix.of fun i j : Fin k => ∫ x, x ^ (i + j : ℕ) ∂μ).PosDef`, Mathlib's
  `Matrix.PosDef`; (a) is then a bridge.
- (c) "At least $k$ support points": in finset form, `isMomentPosDef_iff_forall_finset :
  IsMomentPosDef μ k ↔ ∀ s : Finset ℝ, (∀ᵐ x ∂μ, x ∈ s) → k ≤ s.card` (#57), or through Mathlib's
  `Measure.support` and `Set.ncard`.
- Recommendation: **(a) as the definition, with (c) in finset form now (#57)**: it is the
  user-facing reading ("at least $k$ atoms") and the engine of #30, #31, #34 and #49. (b) later,
  through Mathlib's `Matrix.gram` of the monomials in $L^2(\mu)$ and
  `Matrix.posDef_gram_iff_linearIndependent`; the `Measure.support` form stays deferred (§8 item 7).
- Reviewer: (a) plus the finset form of (c) now; (b) later through `Matrix.gram`. Adopted.
- **The maintainer's question, "is this not in mathlib or somewhere else?"** No. The pinned
  Mathlib has no Hankel matrix, no moment-definiteness predicate and no orthogonal-polynomial
  theory of a measure (searched: `hankel`, `Hankel`, `moment` with `PosDef`, `orthogonal` in
  `Polynomial/` and `MeasureTheory/`; its only orthogonal families are the Chebyshev ones for the
  fixed measure `measureT`, §11). NLAlib has none before this stage (§1). The nearest Mathlib
  object is the Gram matrix: the Hankel matrix $(\int x^{i+j}d\mu)_{i,j<k}$ is
  `Matrix.gram ℝ` of the monomials $1, x, \dots, x^{k-1}$ as elements of `Lp ℝ 2 μ`, and
  `Matrix.posDef_gram_iff_linearIndependent` (`Analysis/InnerProductSpace/GramMatrix.lean`) says
  it is positive definite iff they are linearly independent in $L^2(\mu)$, which is
  `IsMomentPosDef μ k` (a nonzero polynomial of degree $< k$ has positive norm). So OQ5(b) is a
  bridge to Mathlib, not a definition to copy; the $L^2$ form stays recommended as the definition
  because every proof uses it and it avoids the `Lp` coercions.

**OQ6. Where general Golub–Welsch lives.** **Decided 2026-10-24: (a).** Its statement uses `spectralMeasure` (Matrix) and
`jacobiMatrix`, `gaussQuadrature` (Polynomial); its proof uses Lanczos. P11 keeps
`spectralMeasure` out of the Polynomial layer for good, so the home by subject is the Matrix
layer, `Matrix/Spectral/SpectralMeasure.lean` (or a new `Matrix/Spectral/JacobiMatrix.lean`),
which imports Polynomial; it is blocked there only by the proof's use of Lanczos. (a) In
`Krylov/Functions/Quadrature.lean`, beside the Lanczos form, flagged (P10) with that intended
home; the charpoly route (§8 item 9) would unblock the move. (b) A new
`Krylov/Functions/GolubWelsch.lean`, same flag. Recommendation: **(a)**; the file stays under
850 lines.
- Reviewer: (a), with the flag's home corrected to the Matrix layer (adopted).

## 1. What exists (checked against the tree)

- **Polynomial/Orthogonal** (KS2): `MatchesMoments μ ν N` with `refl`, `symm`, `trans`, `mono`,
  `matchesMoments_zero`, the `degreeLT` and monomial bridges, `measureReal_univ_eq`, M0
  (`MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn`), `matchesMoments_measureT`
  and `integrable_eval_of_ae_mem_Icc` (`Moments.lean`); `IsOrthogonalPolynomial μ k p`, `.mono`,
  `MatchesMoments.isOrthogonalPolynomial_iff` (`Basic.lean`, 70 lines); `interpolatoryQuadrature
  μ s` with `IsOrthogonalPolynomial.integral_eval_eq_sum` (Gauss exactness under the nodal
  hypothesis), `.integral_eval_basis_eq_integral_sq` (weights), `.matchesMoments_interpolatoryQuadrature`,
  `.integral_interpolatoryQuadrature` (`Gauss.lean`, 203 lines). The module docstring of
  `Gauss.lean` says: "The existence of Gauss nodes for a given measure … is not proved here."
  That is this stage.
- **Matrix/Spectral/SpectralMeasure.lean** (KS1): `spectralMeasure A b`,
  `integral_spectralMeasure`, `Matrix.IsHermitian.integral_eval_spectralMeasure`,
  `.spectralMeasure_real_univ`, `spectralMeasure_compl_spectrum_eq_zero`,
  `HasOrthonormalCols.spectralMeasure_eq_sum` (eigenbasis form, any $\mathbf{U}$ with
  orthonormal columns and as many columns as rows).
- **Krylov/Functions/Quadrature.lean** (KS3): `lanczosQuadrature A b q`,
  `HasOrthonormalCols.lanczosQuadrature_eq` (frame form),
  `Matrix.IsHermitian.lanczosQuadrature_succ_eq` ($= \mu_{\mathbf{T},\|\mathbf{b}\|\mathbf{e}_0}$
  for every $q$), `.lanczosQuadrature_succ_eq_sum` (Golub–Welsch for Lanczos),
  `.matchesMoments_lanczosQuadrature`, `HasOrthonormalCols.isOrthogonalPolynomial_nodal`,
  `.lanczosQuadrature_eq_interpolatoryQuadrature`, `.lanczosQuadrature_real_singleton_pos`,
  `.card_spectrum_conjTranspose_mul_mul_eq`, and the private helpers
  `aeval_mulVec_ne_zero_of_degree_lt_krylovGrade` and `card_spectrum_le_of_range_eq`.
- **Krylov/Processes** (K0): `arnoldiMatrix` with its column API (`arnoldiMatrix_col_eq_col_last`,
  `exists_gramSchmidtR_smul_arnoldiMatrix_col_last`,
  `star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem`, `arnoldiMatrix_col_last_eq_zero_iff`,
  `norm_arnoldiMatrix_col_last`); `lanczosState`, `lanczosAlpha`, `lanczosTridiagonal`,
  `Matrix.IsHermitian.lanczosTridiagonal_eq` ($\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}
  \mathbf{Q}$ for the canonical basis, every $q$), `.lanczosState_beta_eq_zero_iff`.
- **Krylov/Basic**: `krylovSpace_eq_span`, `aeval_mulVec_mem_krylovSpace` (any coefficient ring,
  so real polynomials), `krylovMatrix_mulVec_injective_iff`, `krylovSpace_eq_of_krylovGrade_le`,
  the compression lemmas.
- **Not present**: any orthogonal polynomial of a measure, `IsMomentPosDef` or a Hankel matrix,
  a Jacobi matrix, `gaussQuadrature` (grep of `NLAlib/` for `orthogonalPolynomial`, `jacobi`,
  `gaussQuadrature`, `Hankel`, `Christoffel`, `Radau`: none).

## 2. Objects

Polynomial-layer context: `open MeasureTheory Polynomial`, `namespace NLAlib`. All definitions
are total; the junk values are stated in each docstring.

```lean
/-- The measure $\mu$ is **positive definite on the polynomials of degree less than $k$**:
$\int p^2\,d\mu > 0$ for every nonzero real polynomial $p$ with $\deg p < k$. Equivalently the
Hankel matrix $(\int x^{i+j}\,d\mu)_{i,j<k}$ is positive definite, or $\mu$ has at least $k$
support points (`isMomentPosDef_iff_forall_finset`). Vacuous at $k = 0$. Chihara's
positive-definite moment functional, restricted to degree $< k$. [Chihara1978, Ch. I, Definition
3.1]; [Gautschi2004, §1.1] (locators to check). -/
def IsMomentPosDef (μ : Measure ℝ) (k : ℕ) : Prop :=
  ∀ p : ℝ[X], p ≠ 0 → p.degree < k → 0 < ∫ x, p.eval x ^ 2 ∂μ

/-- The **monic orthogonal polynomials** of $\mu$, by the Stieltjes procedure:
$\pi_0 = 1$, $\pi_1 = x - \alpha_0$ and
$\pi_{k+2} = (x - \alpha_{k+1})\pi_{k+1} - \beta_{k+1}\pi_k$, with
$\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$ and
$\beta_k = \int\pi_k^2\,d\mu/\int\pi_{k-1}^2\,d\mu$ (`jacobiAlpha`, `jacobiBeta`).
$\pi_k$ is monic of degree $k$ for every $\mu$ and $k$. For a finite measure with compact support
it is orthogonal to every polynomial of degree less than $k$
(`isOrthogonalPolynomial_orthogonalPolynomial`), and it is the only monic such polynomial of
degree $k$ when $\mu$ is positive definite up to degree $k$
(`IsMomentPosDef.eq_orthogonalPolynomial`). Junk: a zero norm gives a zero coefficient
($x/0 = 0$); for a measure with $N$ support points, $\pi_N$ is the nodal polynomial of the support
and every later $\pi_k$ is a multiple of it. [Gautschi2004, Theorem 1.27]. -/
noncomputable def orthogonalPolynomial (μ : Measure ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - C ((∫ x, x * (1 : ℝ[X]).eval x ^ 2 ∂μ) / ∫ x, (1 : ℝ[X]).eval x ^ 2 ∂μ)
  | k + 2 =>
    (X - C ((∫ x, x * (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ)) * orthogonalPolynomial μ (k + 1) -
      C ((∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) * orthogonalPolynomial μ k

/-- The **diagonal recurrence coefficient** $\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$;
$0$ when $\pi_k$ has norm $0$. -/
noncomputable def jacobiAlpha (μ : Measure ℝ) (k : ℕ) : ℝ :=
  (∫ x, x * (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) /
    ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ

/-- The **off-diagonal recurrence coefficient** $\beta_k = \int\pi_k^2\,d\mu/
\int\pi_{k-1}^2\,d\mu$ for $k \ge 1$, and $\beta_0 = \mu(\mathbb{R})$ (Gautschi's convention);
$0$ when $\pi_{k-1}$ has norm $0$. The Jacobi matrix carries $\sqrt{\beta_k}$. -/
noncomputable def jacobiBeta (μ : Measure ℝ) : ℕ → ℝ
  | 0 => μ.real Set.univ
  | k + 1 => (∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
      ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ

/-- The **Jacobi matrix** of order $k$: $\alpha_0, \dots, \alpha_{k-1}$ on the diagonal,
$\sqrt{\beta_1}, \dots, \sqrt{\beta_{k-1}}$ beside it; the same layout as `lanczosTridiagonal`. -/
noncomputable def jacobiMatrix (μ : Measure ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then jacobiAlpha μ i
    else if (i : ℕ) = j + 1 then √(jacobiBeta μ i)
    else if (j : ℕ) = i + 1 then √(jacobiBeta μ j)
    else 0

/-- The **Gauss nodes** of order $k$: the distinct real zeros of $\pi_k$. When $\mu$ is positive
definite up to degree $k$ there are $k$ of them, in every interval carrying $\mu$, and
$\pi_k$ is their nodal polynomial. Junk: past the number of support points, the support and
possibly $0$. -/
noncomputable def gaussNodes (μ : Measure ℝ) (k : ℕ) : Finset ℝ :=
  (orthogonalPolynomial μ k).roots.toFinset

/-- The **$k$-point Gauss rule** of $\mu$: the interpolatory rule at the Gauss nodes. It matches
the first $2k$ moments of $\mu$ for every $k$; past the number of support points it is $\mu$
itself. -/
noncomputable def gaussQuadrature (μ : Measure ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (gaussNodes μ k)

/-- The Gauss rule is a finite measure (#63; the definition is not reducible, so
`isFiniteMeasure_interpolatoryQuadrature` is not found through it). -/
instance isFiniteMeasure_gaussQuadrature (μ : Measure ℝ) (k : ℕ) :
    IsFiniteMeasure (gaussQuadrature μ k) := by
  unfold gaussQuadrature; infer_instance
```

Proposed §5.3 rows (added with the skeleton PR, with their bridges):

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| positive definiteness up to a degree | `IsMomentPosDef μ k`: $\int p^2\,d\mu > 0$ for nonzero $p$, $\deg p < k$ | `isMomentPosDef_succ_iff` (norms of $\pi_j$), `isMomentPosDef_iff_forall_finset` (at least $k$ atoms), `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff` (`k ≤ krylovGrade A b`); the Hankel form via Mathlib's `Matrix.gram` is deferred |
| monic orthogonal polynomials | `orthogonalPolynomial μ k`, the Stieltjes recurrence, total, monic of degree $k$ for every $\mu$ | `isOrthogonalPolynomial_orthogonalPolynomial`, `IsMomentPosDef.eq_orthogonalPolynomial`; Mathlib has none (Chebyshev families only) |
| recurrence coefficients, Jacobi matrix | `jacobiAlpha μ k`, `jacobiBeta μ k` (Gautschi's $\beta$, $\beta_0 = \mu(\mathbb{R})$), `jacobiMatrix μ k : Matrix (Fin k) (Fin k) ℝ` with $\sqrt{\beta}$ off the diagonal | `orthogonalPolynomial_add_two` (`rfl`), `Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix`; Mathlib's `jacobiMatrix` is unrelated |
| Gauss nodes and rule | `gaussNodes μ k` (zeros of $\pi_k$), `gaussQuadrature μ k := interpolatoryQuadrature μ (gaussNodes μ k)`; amends the "Gauss rule" row: the canonical rule of a measure | `matchesMoments_gaussQuadrature`, `MatchesMoments.eq_gaussQuadrature`, `Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`, `HasOrthonormalCols.gaussNodes_spectralMeasure_eq` (Ritz values), `spectralMeasure_jacobiMatrix` |

What is deliberately not an object: no orthonormal polynomials $p_k = \pi_k/\|\pi_k\|$ (no
consumer; the Jacobi matrix and the Lanczos vectors write the normalisation inline), no
Christoffel function, no Stieltjes transform or continued fraction, no `gaussRadauQuadrature`
(§8). No separate name for the norm $\int\pi_k^2\,d\mu$: it is an integral, written out.

## 3. Interfaces

- **`IsMomentPosDef μ k`** (new, Basic.lean). Bundles nothing beyond its one condition. It is the
  hypothesis of uniqueness, of real simple zeros and their count, and of strict weight
  positivity; it is never needed for existence, exactness or the Lanczos link (OQ2). API:
  `mono`. Constructors: `isMomentPosDef_iff_forall_finset` (↔ no finite set of fewer than $k$
  points carries $\mu$: the raw "at least $k$ atoms" reading), `isMomentPosDef_succ_iff`
  (↔ the last norm is positive),
  `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff` (↔ `k ≤ krylovGrade A b`, so every
  Lanczos statement below the grade has it). Namespace for its API (N9, N18):
  `IsMomentPosDef.card_gaussNodes` etc.
- **`IsOrthogonalPolynomial μ k p`, `MatchesMoments μ ν N`** (existing): unchanged. The canonical
  polynomial concludes the first (unconditionally); the Gauss rule concludes the second.
- **The support hypothesis** (SD3, existing): `[IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)`,
  on every theorem that integrates. The recurrence equations, monicity, degree, `jacobiBeta_nonneg`,
  `isHermitian_jacobiMatrix` and the moment-invariance theorems take none (T13).

## 4. Statement shapes

A one-line claim follows each signature; headline docstrings are drafted where the citation or
the junk value needs fixing now. Each block lists the `variable` context it was elaborated in.

### 4.1 `Polynomial/Orthogonal/Moments.lean` (addition, about +80 lines)

Context: the file's `variable {μ ν : Measure ℝ} {N : ℕ}`.

```lean
theorem ae_eval_eq_zero_of_integral_sq_eq_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : ∫ x, p.eval x ^ 2 ∂μ = 0) :
    ∀ᵐ x ∂μ, p.eval x = 0
-- a polynomial of norm zero vanishes almost everywhere

theorem integral_eval_mul_eq_zero_of_integral_sq_eq_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : ∫ x, p.eval x ^ 2 ∂μ = 0) (r : ℝ[X]) :
    ∫ x, p.eval x * r.eval x ∂μ = 0
-- … and is orthogonal to everything (#58; the degenerate branch of every recurrence proof)

/-- **Moment determinacy on a finite set**: two finite measures carried by a finite set $s$ that
match their first $\lvert s\rvert$ moments are equal. No printed source. -/
theorem MatchesMoments.eq_of_ae_mem [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Finset ℝ}
    (h : MatchesMoments μ ν s.card) (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) : μ = ν
```

### 4.2 `Polynomial/Orthogonal/Basic.lean` (addition, about +70 lines)

`IsMomentPosDef` (§2), then

```lean
theorem IsMomentPosDef.mono {μ : Measure ℝ} {j k : ℕ} (h : IsMomentPosDef μ k) (hjk : j ≤ k) :
    IsMomentPosDef μ j

/-- **Positive definiteness counts support points**: a finite measure supported in $[a, b]$ is
positive definite on the polynomials of degree less than $k$ exactly when no finite set of fewer
than $k$ points carries it. [Gautschi2004, §1.1] (locator to check). -/
theorem isMomentPosDef_iff_forall_finset {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsMomentPosDef μ k ↔ ∀ s : Finset ℝ, (∀ᵐ x ∂μ, x ∈ s) → k ≤ s.card
```

### 4.3 `Polynomial/Orthogonal/Recurrence.lean` (new, about 700 lines)

In the file, #18 and #59 come before the private steps and #17 (review comment 9). Definitions
`orthogonalPolynomial`, `jacobiAlpha`, `jacobiBeta`, `jacobiMatrix` (§2). Context
`variable {μ ν : Measure ℝ}`, then from `isOrthogonalPolynomial_orthogonalPolynomial` on
`variable [IsFiniteMeasure μ] {a b : ℝ}`.

```lean
theorem orthogonalPolynomial_zero (μ : Measure ℝ) : orthogonalPolynomial μ 0 = 1 := rfl
theorem orthogonalPolynomial_one (μ : Measure ℝ) :
    orthogonalPolynomial μ 1 = X - C (jacobiAlpha μ 0) := rfl
/-- **The three-term recurrence** … [Gautschi2004, Theorem 1.27]; [Szego1975, Theorem 3.2.1]
(locator to check); there as a theorem about the orthogonal polynomials, here the definition.
Result: orthogonal-polynomial-recurrence -/
theorem orthogonalPolynomial_add_two (μ : Measure ℝ) (k : ℕ) :
    orthogonalPolynomial μ (k + 2) =
      (X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1) -
        C (jacobiBeta μ (k + 1)) * orthogonalPolynomial μ k := rfl
theorem jacobiBeta_zero (μ : Measure ℝ) : jacobiBeta μ 0 = μ.real Set.univ := rfl

theorem monic_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) : (orthogonalPolynomial μ k).Monic
theorem natDegree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).natDegree = k
theorem degree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).degree = k
theorem jacobiBeta_nonneg (μ : Measure ℝ) (k : ℕ) : 0 ≤ jacobiBeta μ k

/-- **Existence of the orthogonal polynomials**: for a finite measure $\mu$ supported in
$[a, b]$ and every $k$, the monic polynomial $\pi_k$ of degree $k$ is orthogonal in $L^2(\mu)$
to every real polynomial of degree less than $k$. No nondegeneracy is needed: past the number of
support points, $\pi_k$ vanishes on the support. [Gautschi2004, Theorems 1.6 and 1.27]
(which of Theorems 1.6–1.8 states existence is to check); there for $k$ below the number of
support points.
Result: orthogonal-polynomial-existence -/
theorem isOrthogonalPolynomial_orthogonalPolynomial (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k)

-- Private steps of #17, fixed in the skeleton so that each proof stays short (§10):
private theorem integral_orthogonalPolynomial_add_two_mul_eq_zero_of_degree_lt
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1)))
    (h0 : IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k)) {r : ℝ[X]} (hr : r.degree < k) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * r.eval x ∂μ = 0                    -- #17a
private theorem integral_orthogonalPolynomial_add_two_mul_succ
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1))) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ (k + 1)).eval x ∂μ = 0
                                                                                          -- #17b
private theorem integral_orthogonalPolynomial_add_two_mul_self
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1))) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ k).eval x ∂μ = 0
                                                                                          -- #17c
private theorem isOrthogonalPolynomial_orthogonalPolynomial_add_two
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1)))
    (h0 : IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k)) :
    IsOrthogonalPolynomial μ (k + 2) (orthogonalPolynomial μ (k + 2))                     -- #17d

theorem integral_orthogonalPolynomial_succ_sq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ =
      jacobiBeta μ (k + 1) * ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ
-- ‖π_{k+1}‖² = β_{k+1}‖π_k‖², also when ‖π_k‖ = 0 [Gautschi2004, Theorem 1.27] (eq. to check)

theorem integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (x - jacobiAlpha μ k) * (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = 0
-- #59: the definition of α_k, unconditionally (x / 0 = 0)

theorem integral_orthogonalPolynomial_sq_eq_prod (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = ∏ i ∈ Finset.range (k + 1), jacobiBeta μ i
-- #62: ‖π_k‖² = β_0 β_1 ⋯ β_k [Gautschi2004, Theorem 1.27] (equation to check)

theorem integral_mul_orthogonalPolynomial_mul_orthogonalPolynomial_succ
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, x * (orthogonalPolynomial μ k).eval x * (orthogonalPolynomial μ (k + 1)).eval x ∂μ =
      ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ
-- the off-diagonal entry: x π_k = π_{k+1} + (lower degree)

theorem isMomentPosDef_succ_iff (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsMomentPosDef μ (k + 1) ↔ 0 < ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ
-- definiteness is positivity of the last norm (norms vanish from the first zero one on)

/-- **Uniqueness of the monic orthogonal polynomial** … [Gautschi2004, Theorem 1.6] (locator
to check). -/
theorem IsMomentPosDef.eq_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : p.Monic) (hpk : p.natDegree = k)
    (hpo : IsOrthogonalPolynomial μ k p) : p = orthogonalPolynomial μ k

theorem MatchesMoments.orthogonalPolynomial_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k)) :
    orthogonalPolynomial μ k = orthogonalPolynomial ν k
-- π_k depends only on the first 2k moments (no support hypothesis: a formula in integrals)
theorem MatchesMoments.jacobiAlpha_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 2)) :
    jacobiAlpha μ k = jacobiAlpha ν k
theorem MatchesMoments.jacobiBeta_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 1)) :
    jacobiBeta μ k = jacobiBeta ν k
theorem MatchesMoments.jacobiMatrix_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k)) :
    jacobiMatrix μ k = jacobiMatrix ν k

theorem isHermitian_jacobiMatrix (μ : Measure ℝ) (k : ℕ) : (jacobiMatrix μ k).IsHermitian
```

The moment budgets are the Jackson note's "finite-support warning" (§5 there): orthogonality of
degree $k$ needs $2k - 1$, the norm $2k$, $\alpha_k$ the moment $2k + 1$; in the strict
convention of SD2 these are `2 * k`, `2 * k + 1`, `2 * k + 2`.

### 4.4 (dropped after the review: no ForMathlib file)

Positivity of a real polynomial with positive leading coefficient and no real root is Mathlib's
`Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (hroots : ∀ y, P.IsRoot y → y < x)
(hlc : 0 ≤ P.leadingCoeff) : 0 < P.eval x` (`Mathlib/Analysis/Polynomial/Order.lean`); with
`P.roots = 0` the root hypothesis is vacuous (`mem_roots`). #30 uses it directly (CONTRIBUTING
§8: an exact overlap is never an independent proof). The former #27 is deleted.

### 4.5 `Polynomial/Orthogonal/Zeros.lean` (new, about 330 lines)

`gaussNodes` (§2). Context `variable {μ : Measure ℝ}`, then `[IsFiniteMeasure μ] {a b : ℝ}`.

```lean
theorem card_gaussNodes_le (μ : Measure ℝ) (k : ℕ) : (gaussNodes μ k).card ≤ k

-- #30a, private, the shared step of #30, #31 and #34 (review comment 9):
private theorem IsMomentPosDef.false_of_ae_nonneg_mul {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : IsOrthogonalPolynomial μ k p) {r : ℝ[X]}
    (hr : r.degree < k) (hnn : ∀ᵐ x ∂μ, 0 ≤ (p * r).eval x) {s : Finset ℝ} (hs : s.card < k)
    (hz : ∀ x ∈ Set.Icc a b, (p * r).eval x = 0 → x ∈ s) : False

/-- **The zeros of the orthogonal polynomial are real**: if $\mu$, finite and supported in
$[a, b]$, is positive definite up to degree $k$, then $\pi_k$ has $k$ real zeros counted with
multiplicity. [Gautschi2004, Theorem 1.19]; [Szego1975, Theorem 3.3.1] (locators to check).
Result: orthogonal-polynomial-zeros -/
theorem IsMomentPosDef.card_roots_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : Multiset.card (orthogonalPolynomial μ k).roots = k
theorem IsMomentPosDef.nodup_roots_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (orthogonalPolynomial μ k).roots.Nodup
-- … and simple
theorem IsMomentPosDef.nodal_gaussNodes {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    Lagrange.nodal (gaussNodes μ k) id = orthogonalPolynomial μ k
theorem IsMomentPosDef.card_gaussNodes {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (gaussNodes μ k).card = k
theorem IsMomentPosDef.gaussNodes_subset_Icc {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (gaussNodes μ k : Set ℝ) ⊆ Set.Icc a b
-- the zeros lie in every interval carrying μ, hence in the convex hull of the support

theorem ae_mem_gaussNodes_of_not_isMomentPosDef (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ¬ IsMomentPosDef μ k) : ∀ᵐ x ∂μ, x ∈ gaussNodes μ k
-- the degenerate case: μ is carried by the zeros of π_k
theorem isOrthogonalPolynomial_nodal_gaussNodes (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsOrthogonalPolynomial μ (gaussNodes μ k).card (Lagrange.nodal (gaussNodes μ k) id)
-- the hypothesis of every existing Gauss.lean theorem, for every k
```

Strictness ($a < x < b$ when $\mu$ has $k + 1$ support points) is deferred (§8 item 1): with
$k$ atoms one of which is $a$, $a$ is a node, so `Set.Icc` is what definiteness up to $k$ gives.

### 4.6 `Polynomial/Orthogonal/Gauss.lean` (addition, about +220 lines)

`gaussQuadrature` (§2). Context `variable {μ ν : Measure ℝ}`, then `[IsFiniteMeasure μ] {a b : ℝ}`.
The file imports `Zeros.lean`; the module docstring's "not proved here" paragraph is replaced.

```lean
instance isFiniteMeasure_gaussQuadrature (μ : Measure ℝ) (k : ℕ) :
    IsFiniteMeasure (gaussQuadrature μ k)                                   -- #63, §2
theorem ae_mem_interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) :
    ∀ᵐ x ∂interpolatoryQuadrature μ s, x ∈ s
theorem interpolatoryQuadrature_eq_self_of_ae_mem {s : Finset ℝ} (hs : ∀ᵐ x ∂μ, x ∈ s) :
    interpolatoryQuadrature μ s = μ
-- a measure carried by the nodes is its own interpolatory rule (weights ∫ℓ_x dμ = μ{x})

/-- **Gauss quadrature**: for a finite measure $\mu$ supported in $[a, b]$ and every $k$, the
$k$-point Gauss rule matches the first $2k$ moments of $\mu$: it integrates every real polynomial
of degree less than $2k$ exactly. [Gautschi2004, Theorem 1.45]; [GolubMeurant2010, Ch. 6];
there for $k$ at most the number of support points; past it the rule is $\mu$ itself.
Result: gauss-quadrature -/
theorem matchesMoments_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    MatchesMoments μ (gaussQuadrature μ k) (2 * k)
theorem integral_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussQuadrature μ k =
      ∑ x ∈ gaussNodes μ k, (∫ t, (Lagrange.basis (gaussNodes μ k) id x).eval t ∂μ) * f x
theorem ae_mem_Icc_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∀ᵐ x ∂gaussQuadrature μ k, x ∈ Set.Icc a b
-- with matchesMoments_gaussQuadrature, the two hypotheses M0 needs
theorem gaussQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ} (hk : 0 < k) :
    (gaussQuadrature μ k).real Set.univ = μ.real Set.univ
/-- … weights positive … [Gautschi2004, Theorem 1.46] (locator to check). -/
theorem IsMomentPosDef.gaussQuadrature_real_singleton_pos {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ gaussNodes μ k) :
    0 < (gaussQuadrature μ k).real {x}

/-- **Uniqueness of the Gauss rule**: if a finite measure $\nu$ carried by a set of at most $k$
points matches the first $2k$ moments of a finite measure $\mu$ supported in $[a, b]$, then $\nu$
is the $k$-point Gauss rule of $\mu$. [Gautschi2004, §1.4] (locator to check); there among
interpolatory rules with $k$ distinct nodes and positive weights; here any measure on at most $k$
points.
Result: gauss-quadrature-uniqueness -/
theorem MatchesMoments.eq_gaussQuadrature [IsFiniteMeasure ν] {k : ℕ}
    (h : MatchesMoments μ ν (2 * k)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {s : Finset ℝ}
    (hν : ∀ᵐ x ∂ν, x ∈ s) (hs : s.card ≤ k) : ν = gaussQuadrature μ k
```

### 4.7 `Matrix/Spectral/SpectralMeasure.lean` (addition, about +100 lines)

Context: the file's `{𝕜} [RCLike 𝕜] {n} [Fintype n] [DecidableEq n]`.

```lean
theorem _root_.Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (p r : ℝ[X]) :
    star (aeval A p *ᵥ b) ⬝ᵥ (aeval A r *ᵥ b) =
      ((∫ x, p.eval x * r.eval x ∂spectralMeasure A b : ℝ) : 𝕜)
-- ⟨p(A)b, r(A)b⟩ is the L²(μ_{A,b}) inner product of p and r
theorem _root_.Matrix.IsHermitian.norm_aeval_mulVec_sq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (p : ℝ[X]) :
    ‖WithLp.toLp 2 (aeval A p *ᵥ b)‖ ^ 2 = ∫ x, p.eval x ^ 2 ∂spectralMeasure A b

theorem spectralMeasure_diagonal {r : Type*} [Fintype r] [DecidableEq r] (d : r → ℝ)
    (w : r → 𝕜) :
    spectralMeasure (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) w =
      ∑ i, ENNReal.ofReal (‖w i‖ ^ 2) • Measure.dirac (d i)
-- #55a: the spectral measure of a diagonal matrix (U = 1 in `spectralMeasure_eq_sum`)

/-- Every finite measure carried by a finite set is a spectral measure: of the diagonal matrix of
the points and the vector of square roots of their masses. -/
theorem spectralMeasure_diagonal_sqrt_of_ae_mem {ν : Measure ℝ} [IsFiniteMeasure ν]
    {s : Finset ℝ} (hν : ∀ᵐ x ∂ν, x ∈ s) :
    spectralMeasure (Matrix.diagonal fun x : s => (x : ℝ)) (fun x => √(ν.real {(x : ℝ)})) = ν
-- #55b, over ℝ; reusable by SLQ and Krylov-Sharpness for discrete measures
```

### 4.8 `Krylov/Basic/Grade.lean` (addition, a move)

```lean
theorem aeval_mulVec_ne_zero_of_degree_lt_krylovGrade {A : Matrix n n 𝕜} {b : n → 𝕜}
    {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.degree < krylovGrade A b) : aeval A p *ᵥ b ≠ 0
```

Now private in `Krylov/Functions/Quadrature.lean`; made public here (it is a fact about the
grade), and deleted there. The proof moves unchanged.

### 4.9 `Krylov/Processes/LanczosPolynomials.lean` (new, about 380 lines)

Context `{𝕜} [RCLike 𝕜] {n} [Fintype n] [DecidableEq n]`, `open scoped Matrix ComplexOrder MatrixOrder`.

```lean
theorem _root_.Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (k : ℕ) :
    IsMomentPosDef (spectralMeasure A b) k ↔ k ≤ krylovGrade A b

/-- **The Lanczos vectors are the orthogonal polynomials of the spectral measure**: for
Hermitian $\mathbf{A}$, every $q$ and $j < q$, column $j$ of the canonical Lanczos basis is
$\pi_j(\mathbf{A})\mathbf{b}/\|\pi_j(\mathbf{A})\mathbf{b}\|$, $\pi_j$ the monic orthogonal
polynomial of degree $j$ of $\mu_{\mathbf{A},\mathbf{b}}$; from the grade on both sides are
$\mathbf{0}$. [GolubMeurant2010, Ch. 4] (locator to check).
Result: lanczos-orthogonal-polynomials -/
theorem aeval_orthogonalPolynomial_mulVec_sub_pow_mulVec_mem_krylovSpace (μ : Measure ℝ)
    (A : Matrix n n 𝕜) (b : n → 𝕜) (j : ℕ) :
    aeval A (orthogonalPolynomial μ j) *ᵥ b - A ^ j *ᵥ b ∈ krylovSpace A b j          -- #50b
theorem _root_.Matrix.IsHermitian.star_dotProduct_aeval_orthogonalPolynomial_mulVec_eq_zero_of_mem
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b x : n → 𝕜} {j : ℕ}
    (hx : x ∈ krylovSpace A b j) :
    star x ⬝ᵥ (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) = 0      -- #50a
-- π_j(A)b is orthogonal to the Krylov space K_j
theorem _root_.Matrix.IsHermitian.aeval_orthogonalPolynomial_mulVec_eq_zero_of_krylovGrade_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {j : ℕ} (hj : krylovGrade A b ≤ j) :
    aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b = 0                    -- #50c
private theorem arnoldiMatrix_col_last_eq_of_lt_krylovGrade {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : n → 𝕜} {j : ℕ} (hj : j < krylovGrade A b) :
    (arnoldiMatrix A b (j + 1)).col (Fin.last j) =
      (‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)‖⁻¹ : 𝕜) •
        (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)                  -- #50d

theorem _root_.Matrix.IsHermitian.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} (j : Fin q) :
    (arnoldiMatrix A b q).col j =
      (‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)‖⁻¹ : 𝕜) •
        (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)

theorem _root_.Matrix.IsHermitian.lanczosAlpha_lanczosState {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    lanczosAlpha A (lanczosState A b j) = jacobiAlpha (spectralMeasure A b) j
theorem _root_.Matrix.IsHermitian.lanczosState_beta {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosState A b (j + 1)).beta = √(jacobiBeta (spectralMeasure A b) (j + 1))

/-- **The Lanczos tridiagonal is the Jacobi matrix of the spectral measure**: for Hermitian
$\mathbf{A}$ and every $q$, the tridiagonal matrix of $q$ steps of the Lanczos recurrence from
$\mathbf{b}$ is $\mathbf{J}_q(\mu_{\mathbf{A},\mathbf{b}})$; past the grade both are padded with
the same zeros. [GolubMeurant2010, Ch. 4]; [Gautschi2004, §3.1] (locators to check).
Result: lanczos-jacobi-matrix -/
theorem _root_.Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosTridiagonal A b q = (jacobiMatrix (spectralMeasure A b) q).map (algebraMap ℝ 𝕜)
```

### 4.10 `Krylov/Functions/Quadrature.lean` (addition, about +170 lines, −25 for the move)

The file's context. The file imports `LanczosPolynomials`.

```lean
/-- **Lanczos quadrature is the Gauss rule of the spectral measure**: for Hermitian
$\mathbf{A}$ and every $q$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)$ is the $q$-point Gauss rule of
$\mu_{\mathbf{A},\mathbf{b}}$, for every `RCLike` field (complex Hermitian included).
[GolubMeurant2010, Ch. 6].
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosQuadrature A b q = gaussQuadrature (spectralMeasure A b) q

/-- **The Ritz values are the Gauss nodes** (nodal form): for Hermitian $\mathbf{A}$,
$\mathbf{Q}$ with orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, $q$ at
most the grade and $s$ the set of Ritz values, the nodal polynomial of $s$ is the monic
orthogonal polynomial of degree $q$ of $\mu_{\mathbf{A},\mathbf{b}}$. [GolubMeurant2010, Ch. 4]
(locator to check). -/
theorem HasOrthonormalCols.nodal_eq_orthogonalPolynomial {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {s : Finset ℝ} (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    Lagrange.nodal s id = orthogonalPolynomial (spectralMeasure A b) q                 -- #60
theorem HasOrthonormalCols.gaussNodes_spectralMeasure_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {s : Finset ℝ} (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    gaussNodes (spectralMeasure A b) q = s                                              -- #61
-- `hq` is needed: past the grade `gaussNodes` can contain a spurious 0 of weight 0

/-- **Golub–Welsch**: for a finite measure $\mu$ supported in $[a, c]$ and every $k$, the
$(k+1)$-point Gauss rule of $\mu$ is the spectral measure of its Jacobi matrix and
$\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$: its nodes are the eigenvalues of
$\mathbf{J}_{k+1}(\mu)$ and its weights $\mu(\mathbb{R})$ times the squared first components of
the eigenvectors. Past the support size of $\mu$ the matrix has zero rows, and the extra
eigenvalues carry no weight. [Gautschi2004, Theorem 3.1]; [GolubWelsch1969, §2] (labels to
check).
Result: golub-welsch -/
theorem spectralMeasure_jacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) (k : ℕ) :
    spectralMeasure (jacobiMatrix μ (k + 1)) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) =
      gaussQuadrature μ (k + 1)

theorem HasOrthonormalCols.gaussQuadrature_succ_eq_sum {k : ℕ}
    {U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hU : HasOrthonormalCols U) {μ : Measure ℝ}
    [IsFiniteMeasure μ] {a c : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) {d : Fin (k + 1) → ℝ}
    (hJ : jacobiMatrix μ (k + 1) = U * Matrix.diagonal d * Uᴴ) :
    gaussQuadrature μ (k + 1) =
      ∑ i, ENNReal.ofReal (μ.real Set.univ * U 0 i ^ 2) • Measure.dirac (d i)
-- the explicit Golub–Welsch form, as `lanczosQuadrature_succ_eq_sum`
```

The interval is `[a, c]` in the Krylov files because `b` is the vector there.

### 4.11 Statements I am not sure downstream proofs want in this shape

1. **The Lanczos column formula** (§4.9). Drafted as `q_j = ‖v‖⁻¹ • v`, which holds for all $j$.
   A consumer that needs $\pi_j(\mathbf{A})\mathbf{b}$ from $\mathbf{q}_j$ wants
   `aeval A π_j *ᵥ b = (‖…‖ : 𝕜) • q_j`, which also holds for all $j$; the drafted form is the
   one the coefficient proofs use. Either can be the corollary of the other in two lines.
   **Decided (S1 (a)): as drafted.**
2. **`integral_gaussQuadrature`** gives the weights as $\int\ell_x\,d\mu$, matching
   `IsOrthogonalPolynomial.integral_interpolatoryQuadrature`. SLQ-style statements may prefer
   `∑ x ∈ gaussNodes μ k, (gaussQuadrature μ k).real {x} * f x`.
   **Decided (S2 (c)): added** as #64 `integral_gaussQuadrature_eq_sum` ("Interface for SLQ").
3. **`IsMomentPosDef.gaussNodes_subset_Icc`** is closed-interval (see §4.5). A Gauss–Radau
   consumer would need the strict form; deferred.
4. **`spectralMeasure_jacobiMatrix`** is over ℝ only and at order $k + 1$ (the vector
   $\mathbf{e}_0$ needs a nonempty index). T7: real by subject (the Jacobi matrix is real). A `𝕜`
   version is `(jacobiMatrix …).map (algebraMap ℝ 𝕜)`. **Decided (S2 (c)): added** as #67
   `spectralMeasure_map_jacobiMatrix`, since SLQ works over `𝕜`.
5. **`lanczosState_beta`** relies on OQ3(a); under OQ3(b) it loses the `√`.

## Interface for SLQ (maintainer direction, 2026-10-24)

SLQ is the average over probes of per-probe Gauss rules:
$$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) = \frac{1}{\lvert n\rvert m}\sum_{j=1}^m
\mathsf{gaussQuadrature}(\mu_{\mathbf{A},\boldsymbol{\omega}_j}, q),$$
with $\mu_{\mathbf{A},\boldsymbol{\omega}_j}$ = `spectralMeasure A ω_j` (unnormalised, mass
$\|\boldsymbol{\omega}_j\|^2$). Every per-probe fact is a theorem about `gaussQuadrature` of an
arbitrary finite measure on $[a, b]$; Lanczos enters once, through item 4. The statements below
are final; all elaborate (`/tmp/claude-1000/ks7-scratch/{Poly,Krylov}.lean`). Context in the
Polynomial files: `{μ ν : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}`; in the Krylov file
`{𝕜} [RCLike 𝕜] {n} [Fintype n] [DecidableEq n]`.

**1. The weights form** (#64, Gauss.lean, S2): the rule is a finite sum of point masses at the
Gauss nodes, for every $\mu$ (no support hypothesis needed: it is a statement about a finite Dirac
sum). With the existing `integral_gaussQuadrature` the weight is also $\int\ell_x\,d\mu$.

```lean
theorem integral_gaussQuadrature_eq_sum (μ : Measure ℝ) (k : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussQuadrature μ k = ∑ x ∈ gaussNodes μ k, (gaussQuadrature μ k).real {x} * f x
theorem integrable_gaussQuadrature (μ : Measure ℝ) (k : ℕ) (f : ℝ → ℝ) :
    Integrable f (gaussQuadrature μ k)                                               -- #65
```

**2. The generic Gauss-rule error** (#66, Gauss.lean). M0 already gives it: with
`ν := gaussQuadrature μ k`, `MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn`
applied to `matchesMoments_gaussQuadrature`, `ae_mem_Icc_gaussQuadrature`,
`integrable_gaussQuadrature` and `gaussQuadrature_real_univ` is the bound. #66 is that
composition, stated once so that SLQ (and anyone with a Gauss rule) applies it with `exact`. The
degree condition $\deg p \le 2k - 1$ is written `p.degree < 2 * k` (SD2's strict convention, no
truncated subtraction, V2).

```lean
/-- **The Gauss-rule error from uniform approximation**: for a finite measure $\mu$ supported in
$[a, b]$, $f$ integrable against $\mu$, and a real polynomial $p$ of degree less than $2k$ within
$\varepsilon$ of $f$ on $[a, b]$,
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k)\Bigr\rvert \le
2\varepsilon\,\mu(\mathbb{R})\,.$$
[GolubMeurant2010, Ch. 6]; the composition of exactness with M0. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {f : ℝ → ℝ} (hf : Integrable f μ) {k : ℕ} {p : ℝ[X]}
    (hp : p.degree < 2 * k) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ k| ≤ 2 * ε * μ.real Set.univ

/-- … Lipschitz $f$: <!-- value jacksonApproximationConstant -->
$\frac{\pi L(b - a)}{2k + 3}\mu(\mathbb{R})$ at $k + 1$ nodes … -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) (k : ℕ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ (k + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * k + 3) * μ.real Set.univ    -- #68
```

The Lipschitz corollary (#68) is a one-liner from the existing
`exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith` exactly as the KS4 Lanczos corollary
is (integrability of $f$ follows from continuity on $[a, b]$), so it is here; `Gauss.lean` then
imports `Polynomial/Approximation/Jackson.lean` (P11 holds). The analytic (Bernstein-ellipse)
corollary is **left to SLQ**: its integrability hypothesis is not a one-liner from the ellipse
data, and SLQ's own statement may as well take `Integrable f μ`.

**3. Support and mass** (existing in §4.6, now part of the interface): for every $k$,

```lean
theorem ae_mem_Icc_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∀ᵐ x ∂gaussQuadrature μ k, x ∈ Set.Icc a b                                       -- #42
theorem gaussQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ} (hk : 0 < k) :
    (gaussQuadrature μ k).real Set.univ = μ.real Set.univ                               -- #43
theorem matchesMoments_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    MatchesMoments μ (gaussQuadrature μ k) (2 * k)                                      -- #40
```

The support lies in every interval carrying $\mu$, hence in the convex hull of its support. For a
probe, `ae_mem_Icc_spectralMeasure` gives `hμ` from `spectrum ℝ A ⊆ Set.Icc a b`.

**4. The identification** (#54, Quadrature.lean), over every `RCLike` field: checked, the
signature elaborates with `{𝕜} [RCLike 𝕜]` and the proof route (#45 with
`matchesMoments_lanczosQuadrature`, which is over `𝕜`) has nothing real-only.

```lean
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosQuadrature A b q = gaussQuadrature (spectralMeasure A b) q
```

and Golub–Welsch over `𝕜` (#67, S2 (c)), for SLQ's implementation statement on a complex
Hermitian matrix:

```lean
theorem spectralMeasure_map_jacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) (k : ℕ) :
    spectralMeasure ((jacobiMatrix μ (k + 1)).map (algebraMap ℝ 𝕜))
        ((√(μ.real Set.univ) : 𝕜) • Pi.single 0 1) = gaussQuadrature μ (k + 1)
```

**5. Averaging** (#69, #70, Moments.lean). Moment matching is linear in the pair of measures, so
the average of per-probe Gauss rules matches $2q$ moments of the average of the probe spectral
measures:

```lean
theorem MatchesMoments.smul {N : ℕ} (h : MatchesMoments μ ν N) (c : ℝ≥0∞) :
    MatchesMoments (c • μ) (c • ν) N
theorem MatchesMoments.finsetSum {ι : Type*} {s : Finset ι} {μs νs : ι → Measure ℝ}
    [∀ i, IsFiniteMeasure (μs i)] [∀ i, IsFiniteMeasure (νs i)] {N : ℕ} {a b : ℝ}
    (hμs : ∀ i ∈ s, ∀ᵐ x ∂μs i, x ∈ Set.Icc a b) (hνs : ∀ i ∈ s, ∀ᵐ x ∂νs i, x ∈ Set.Icc a b)
    (h : ∀ i ∈ s, MatchesMoments (μs i) (νs i) N) :
    MatchesMoments (∑ i ∈ s, μs i) (∑ i ∈ s, νs i) N
```

**Remark (why SLQ is an average of rules and not one rule).** `gaussQuadrature` is not linear in
$\mu$: the average of Gauss rules is in general not the Gauss rule of the average. Example:
$\mu_1 = \delta_0$, $\mu_2 = \delta_1$, $k = 1$: each rule is its measure, so the average of the
rules is $\tfrac12(\delta_0 + \delta_1)$, while the one-point Gauss rule of
$\tfrac12(\delta_0 + \delta_1)$ is $\delta_{1/2}$. The average of $m$ per-probe $q$-point rules has
up to $mq$ nodes and matches only $2q$ moments of the averaged measure (items 2 and 5), not the
$2mq$ a Gauss rule with that many nodes would. This is exactly why SLQ is stated per probe:
each probe's rule is the Gauss rule of its own spectral measure (item 4), with that measure's
exactness and error (items 2 and 3), and the estimator averages afterwards. A bound for SLQ is
therefore an average of per-probe Gauss-rule bounds (item 2 applied to each
$\mu_{\mathbf{A},\boldsymbol{\omega}_j}$) plus the probe-averaging error of the spectral measures,
never a Gauss-rule bound for the averaged measure.

**Proof order.** Items 1–5 are marked **[SLQ-1]** in §10: their statements are fixed in the KS7
skeleton, so SLQ's first wave can use them (sorried) from the start, and they are proved first
along their dependency chains. #64, #65, #69, #70 have no KS7 dependency to speak of (waves
0–1); #40, #42, #43, #54, #66, #67, #68 sit at the end of the Gauss chain (waves 9–13), so SLQ
proofs that use them close only when that chain does. Literal wave 1 is impossible for those:
they depend on the zeros and on uniqueness.

## 5. Consumers

| Item | Consumers (stage or layer, and the form they use) |
|---|---|
| `orthogonalPolynomial`, `jacobiAlpha`, `jacobiBeta` and the recurrence | the Lanczos link (§4.9); the moment invariance used by Golub–Welsch; later the maintainer's Lanczos-stability material (coefficients of $\mu_{\mathbf{A},\mathbf{b}}$ under perturbation, PORT_KRYLOV §9's LAA paper; no Lean file yet) |
| `IsMomentPosDef` | uniqueness, zeros, weight positivity; Lanczos below the grade through `isMomentPosDef_spectralMeasure_iff` |
| zeros (`nodal_gaussNodes`, `card_gaussNodes`, `gaussNodes_subset_Icc`) | the Gauss rule's support (`ae_mem_Icc_gaussQuadrature`, needed to apply M0 to a Gauss rule), weight positivity; later interlacing, Gauss–Radau |
| `gaussQuadrature`, `matchesMoments_gaussQuadrature`, `ae_mem_Icc_gaussQuadrature` | SLQ (Estimation; the maintainer's direction of 2026-10-24): `slqMeasure` is the average of the per-probe rules `gaussQuadrature (spectralMeasure A ω_j) q`, through #54; its bounds use the interface items #40, #42, #43, #64–#70 ("Interface for SLQ"); M1 (Probability/Moments) for discrete measures; KPM comparison with SLQ |
| `MatchesMoments.eq_gaussQuadrature`, `MatchesMoments.eq_of_ae_mem` | `lanczosQuadrature_eq_gaussQuadrature`; Golub–Welsch; any later quadrature that is shown Gaussian by moment matching (block Gauss rules, Krylov-aware trace estimation) |
| `HasOrthonormalCols.gaussNodes_spectralMeasure_eq`, `.nodal_eq_orthogonalPolynomial` | every KS3 consumer that moves between the Ritz-value statements of KS3c and the Gauss-rule vocabulary; they coexist with #54, which supersedes nothing (review comment 5) |
| `isMomentPosDef_iff_forall_finset` | #30a (hence #30, #31, #34), #49; users with a discrete measure of at least $k$ atoms |
| `spectralMeasure_diagonal_sqrt_of_ae_mem` | #55; SLQ and Krylov-Sharpness when a discrete measure must be realised as a spectral measure |
| `lanczosQuadrature_eq_gaussQuadrature` | SLQ statements without frames or Ritz-value sets; the fact that Lanczos quadrature depends on $\mathbf{b}$ only through $\mu_{\mathbf{A},\mathbf{b}}$, and on $\mu_{\mathbf{A},\mathbf{b}}$ only through $2q$ moments (with `MatchesMoments.eq_gaussQuadrature`) |
| Lanczos link (§4.9) | SLQ's implementation statement (Krylov-CG.md:455: "`lanczosState`: SLQ's implementation statement"): the computed $\alpha_j, \beta_j$ are the recurrence coefficients of $\mu_{\mathbf{A},\mathbf{b}}$; a later finite-precision round; random-start analyses that want the Lanczos output as a function of $\mu_{\mathbf{A},\mathbf{g}}$ |
| Golub–Welsch (§4.10) | the explorer's "Gauss nodes are eigenvalues of the Jacobi matrix"; no Lean consumer (OQ1) |
| KPM / Jackson (`Polynomial-Jackson-Moments.md`) | nothing new: KPM uses Chebyshev moments and Mathlib's Chebyshev families. A bridge $\pi_k(\mathtt{measureT}) = 2^{1-k}T_k$ is deferred (§8 item 8) |
| CG files | nothing now: CG's error as a Gauss remainder for $1/x$ uses KS3; Gauss–Radau upper bounds for the CG error (Golub–Meurant Ch. 12, locator to check) need §8 item 4 |

**SLQ coordination.** `docs/design/Estimation-SLQ.md` (draft, 1045 lines) appeared in this
worktree while this note was being finished; I read its summary, §1 and §12 and did not edit it.
Its findings agree with this note: no SLQ statement depends on KS7, its uniform (Kolmogorov and
Lipschitz) bounds go through Girard–Hutchinson and an Abel summation, and it lists as later KS7
benefits exactly the frame-free Gauss rule (`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`
here) and Gauss–Radau one-sided bounds (§8 item 4 here, blocked on the Hermite remainder in both
notes). Nothing in either note has to change for the other. If the SLQ maintainer decision wants
`slqMeasure` restated through `gaussQuadrature`, that is one bridge lemma in the SLQ file after
#54; §4.11 item 2 (weights as `(gaussQuadrature μ k).real {x}`) is the shape to confirm then.

## 6. Files, placement, imports, order

| File | New / addition | Content | Lines |
|---|---|---|---|
| `Polynomial/Orthogonal/Moments.lean` | addition | `ae_eval_eq_zero_of_integral_sq_eq_zero`, `integral_eval_mul_eq_zero_of_integral_sq_eq_zero`, `MatchesMoments.eq_of_ae_mem`, `.smul`, `.finsetSum` | +110 |
| `Polynomial/Orthogonal/Basic.lean` | addition | `IsMomentPosDef`, `.mono`, `isMomentPosDef_iff_forall_finset` | +70 |
| `Polynomial/Orthogonal/Recurrence.lean` | new | `orthogonalPolynomial`, `jacobiAlpha`, `jacobiBeta`, `jacobiMatrix`; recurrence, monic, degree, norms (#18, #59, #62), the private steps #17a–#17d, orthogonality, definiteness, uniqueness, moment invariance | 700 |
| `Polynomial/Orthogonal/Zeros.lean` | new | `gaussNodes`; the helper #30a; real simple zeros, count, location, degenerate case | 330 |
| `Polynomial/Orthogonal/Gauss.lean` | addition | `gaussQuadrature` and its instance; exactness, integral (both weight forms), integrability, support, mass, weights, uniqueness, the error bound and its Lipschitz corollary | +310 |
| `Matrix/Spectral/SpectralMeasure.lean` | addition | two polynomial inner-product lemmas; `spectralMeasure_diagonal`, `spectralMeasure_diagonal_sqrt_of_ae_mem` | +100 |
| `Krylov/Basic/Grade.lean` | addition (move) | `aeval_mulVec_ne_zero_of_degree_lt_krylovGrade` | +25 |
| `Krylov/Processes/LanczosPolynomials.lean` | new | definiteness ↔ grade, #50a–#50d, Lanczos vectors, coefficients, tridiagonal | 380 |
| `Krylov/Functions/Quadrature.lean` | addition | `lanczosQuadrature_eq_gaussQuadrature`, the Ritz-value bridges #60, #61, Golub–Welsch (three, one over `𝕜`) | +210 −25 |

Total about 2,250 lines (the review added the instance, nine public and six private lemmas, and
removed the 50-line ForMathlib file; the SLQ interface added seven theorems). Declarations in each new file in the order of §4
(definitions, API, main theorems, corollaries).

**Placement** (CONTRIBUTING §8 item 5).

| Declaration | Home | Reason |
|---|---|---|
| `ae_eval_eq_zero_of_integral_sq_eq_zero` | Moments.lean | beside `integrable_eval_of_ae_mem_Icc`, the other SD3-support fact about polynomials |
| `MatchesMoments.eq_of_ae_mem` | Moments.lean | API of `MatchesMoments` |
| `IsMomentPosDef` | Basic.lean | the second interface of the OP layer, beside `IsOrthogonalPolynomial` |
| `isMomentPosDef_iff_forall_finset` | Basic.lean | a constructor of the interface, beside it |
| SLQ interface #64–#66, #68 | Gauss.lean | theorems about `gaussQuadrature` of any measure; the Lipschitz corollary beside its general form, as KS4 did for Lanczos |
| `MatchesMoments.smul`, `.finsetSum` | Moments.lean | API of `MatchesMoments` |
| `spectralMeasure_map_jacobiMatrix` | Quadrature.lean | **flag**, the same as `spectralMeasure_jacobiMatrix` (intended home Matrix/Spectral), of which it is the `𝕜` form |
| `integral_eval_mul_eq_zero_of_integral_sq_eq_zero` | Moments.lean | beside `ae_eval_eq_zero_of_integral_sq_eq_zero` |
| `spectralMeasure_diagonal`, `spectralMeasure_diagonal_sqrt_of_ae_mem` | `Matrix/Spectral/SpectralMeasure.lean` | facts about spectral measures (diagonal matrices; every finite atomic measure is one), no Krylov vocabulary |
| `aeval_orthogonalPolynomial_mulVec_sub_pow_mulVec_mem_krylovSpace` and #50a, #50c | LanczosPolynomials.lean | Krylov-space facts about $\pi_j(\mathbf{A})\mathbf{b}$, the file's subject |
| `HasOrthonormalCols.nodal_eq_orthogonalPolynomial`, `.gaussNodes_spectralMeasure_eq` | Quadrature.lean | beside the KS3c Ritz-value theorems they bridge (`isOrthogonalPolynomial_nodal`, `card_spectrum_conjTranspose_mul_mul_eq`) |
| `gaussQuadrature` and its theorems | Gauss.lean | the Gauss rule's file; `interpolatoryQuadrature` lives there |
| `star_aeval_mulVec_dotProduct_aeval_mulVec`, `norm_aeval_mulVec_sq` | `Matrix/Spectral/SpectralMeasure.lean` | integrals against the spectral measure, beside `integral_eval_spectralMeasure`; no Krylov vocabulary |
| `aeval_mulVec_ne_zero_of_degree_lt_krylovGrade` | `Krylov/Basic/Grade.lean` | a fact about the grade; now private in Quadrature.lean, needed by a second file |
| `lanczosQuadrature_eq_gaussQuadrature` | Quadrature.lean | its subject is `lanczosQuadrature`; uses the file's private `card_spectrum_le_of_range_eq` |
| `spectralMeasure_jacobiMatrix`, `HasOrthonormalCols.gaussQuadrature_succ_eq_sum` | Quadrature.lean | **flag** (P10): the statement's vocabulary is Matrix (`spectralMeasure`) plus Polynomial, so the home by subject is `Matrix/Spectral/SpectralMeasure.lean` (or a new `Matrix/Spectral/JacobiMatrix.lean`); P11 keeps it out of Polynomial for good; blocked only by the proof's use of Lanczos; the charpoly route (§8 item 9) would unblock it (OQ6) |

Open flags: the one marked.

**Imports.** `Recurrence` imports `Basic` and Mathlib's `Mathlib.LinearAlgebra.Matrix.Hermitian`
(for `isHermitian_jacobiMatrix`); `Basic` adds `Mathlib.LinearAlgebra.Lagrange` (for #57);
`Zeros` imports `Recurrence` and `Mathlib.Analysis.Polynomial.Order` (for
`zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`); `Gauss` imports `Zeros` and
`Polynomial/Approximation/Jackson` (for #68). P11 holds (Mathlib
and Polynomial only; no ForMathlib file is needed now). `LanczosPolynomials` imports `Krylov/Processes/LanczosRecurrence`,
`Matrix/Spectral/SpectralMeasure` and `Polynomial/Orthogonal/Recurrence`; `Quadrature` adds
`LanczosPolynomials`.

**Order.** One skeleton PR with every statement (§10 gives the proof order). Then proofs by
wave; files `Recurrence` and `Zeros` first, `Gauss`, then the Krylov files.

**Mathlib-deviations.md.** The new objects are additions, not deviations. Draft paragraph for
"Additions where Mathlib has nothing", to be added in the skeleton commit (not now: V6 checks that
every Lean name cited in that file exists, and none of these exists yet):

> KS7 (2026-10-24, `docs/design/Polynomial-OrthogonalStructure.md`): `orthogonalPolynomial`,
> the monic orthogonal polynomials of a measure by the Stieltjes recurrence, with `jacobiAlpha`,
> `jacobiBeta` and `jacobiMatrix`; `IsMomentPosDef`; `gaussNodes` and `gaussQuadrature`, the
> canonical Gauss rule, built on `interpolatoryQuadrature`. Mathlib has the Chebyshev, Hermite and
> shifted Legendre families with no measure attached in general, and its `jacobiMatrix`
> (`Algebra.PreSubmersivePresentation.jacobiMatrix`) is the Jacobian of a presentation. Mathlib's
> `InnerProductSpace.gramSchmidt` applies in `Lp ℝ 2 μ`, but returns equivalence classes, not
> polynomials, and cannot recover a degree-$k$ representative when polynomials do not embed
> injectively (every finitely supported $\mu$); the Heine/Hankel determinant formula divides by a
> determinant that vanishes past the support. The recurrence definition follows Mathlib's
> `Polynomial.Chebyshev.T`. `isMomentPosDef_iff_forall_finset` is the support-count reading; a
> Hankel bridge would go through Mathlib's `Matrix.gram`. No numbered deviation is introduced.

## 7. Material

The prototype library, the quarry (`atlas/declarations.json`) and the local PDFs named in earlier
notes are **not on this machine**. I read none of them. What the prototype had for this stage is
known only from Krylov-Spectral §7: `LanczosDecomp.poly` (the Lanczos polynomials), `X_mul_poly`
(their three-term recurrence), `sub_mul_sum_eval_poly_mul` (Christoffel–Darboux),
`charpoly_restrict_T_mul_poly_zero`, `jacobiMatrix`, `jacobiFraction` and the resolvent continued
fraction, all on the `LanczosDecomp` bundle that PORT_KRYLOV D5 dropped, and real-only. Nothing is
reused from it; the design is new:

- the prototype's polynomials were defined from a Lanczos decomposition, so the measure theory
  depended on a matrix; here the polynomials are a function of the measure and Lanczos is the
  theorem (§4.9);
- no bundle, no proof-carrying definitions, `RCLike` throughout the Krylov side.

Mathematics read: the repo (§1), Mathlib (§11), and the literature of §9 from memory. Locators
the Jackson note verified against a PDF are cited plainly; others carry "locator to check".

## 8. Deferred, with what each needs

1. **Interlacing and strict interior zeros** ([Gautschi2004, Theorems 1.19, 1.20];
   [Szego1975, Theorems 3.3.1, 3.3.2], to check). Needs a sorted enumeration of
   `gaussNodes μ k` (as `Fin k → ℝ`, `StrictMono`), the sign alternation of $\pi_{k-1}$ at the
   zeros of $\pi_k$ (from the recurrence and $\beta_k > 0$, or from Christoffel–Darboux) and the
   IVT; about 250 lines, one L. No consumer: Ritz-value interlacing is Poincaré separation.
2. **Christoffel–Darboux and the Christoffel function** ([Gautschi2004, Theorem 1.32]; the
   "multiplied" form first, Jackson note OP1). Consumer when it appears: the Christoffel-function
   formula for Gauss weights and item 3.
3. **Chebyshev–Markov–Stieltjes inequalities** (the distribution function of $\mu$ between the
   partial sums of the Gauss weights). A deterministic Kolmogorov-distance bound between $\mu$
   and its Gauss rule; the SLQ note's Kolmogorov bound does without it (Abel summation over the
   spectrum), so no consumer.
4. **Gauss–Radau and Gauss–Lobatto rules and the sign of the Gauss error.** The rules are
   algebraically cheap here (Radau at $a$ is $\delta$-augmented `gaussQuadrature` of
   `μ.withDensity (fun x => ENNReal.ofReal (x - a))`, exact to degree $2k$), but their use, two-sided
   bounds on $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ for $f$ with sign-definite
   derivatives, needs the Hermite interpolation remainder (Krylov-Spectral §8 item 3, gap survey
   P1), which is missing. Consumer: SLQ and CG error estimation. Defer both together.
5. **The continued fraction / Stieltjes transform** ($\int(z - x)^{-1}d\mu$ and the resolvent
   $\mathbf{e}_0^{\mathsf{H}}(z - \mathbf{J})^{-1}\mathbf{e}_0$). No consumer.
6. **Orthonormal polynomials** $p_k = \pi_k/\|\pi_k\|$ (Jackson note OP1's "normalisation
   bridge"). Wait for item 2.
7. **Bridges of `IsMomentPosDef`** to the Hankel matrix and to `Measure.support`. The Hankel
   matrix is the Gram matrix of the monomials in $L^2(\mu)$, so Mathlib's `Matrix.gram` and
   `Matrix.posDef_gram_iff_linearIndependent` (`Analysis/InnerProductSpace/GramMatrix.lean`) give
   the bridge when a consumer appears. The finset support-count form is in scope (#57). No
   consumer (OQ5).
8. **The Chebyshev bridge** $\pi_k(\mathtt{measureT}) = 2^{1-k}T_k$ ($k \ge 1$). A check that the
   definition fits Mathlib, as `matchesMoments_measureT` was for KS2; needs
   `IsMomentPosDef measureT k` for all $k$ (a positive density on $(-1, 1)$) and Mathlib's
   `Polynomial.Chebyshev.T_add_two`. About 80 lines; no consumer.
9. **`charpoly (jacobiMatrix μ k) = orthogonalPolynomial μ k`**. True unconditionally (the
   tridiagonal determinant recurrence with $\sqrt{\beta}^2 = \beta$); a Laplace expansion twice
   (Mathlib's `Matrix.det_succ_row`). Golub–Welsch makes it unnecessary for the Gauss rule; it
   would let Golub–Welsch be proved without Lanczos and move to its Matrix-layer home (OQ6).

## 9. Literature

In `docs/references.bib`: `Gautschi2004` (metadata to confirm, as Krylov-Spectral's skeleton
noted), `GolubMeurant2010`, `ChenTrogdonUbaru2022`. Locators the Jackson note §2 verified for
Gautschi: §1.1 Theorems 1.2, 1.6–1.8 (positivity, existence, degree budgets); Theorems 1.19–1.20,
p. 7 (zeros, interlacing); Theorems 1.27, 1.29, pp. 10–13 (recurrence, normalisation); Theorem
1.32, p. 14 (Christoffel–Darboux); Theorems 1.45–1.46, pp. 21–23 (Gauss exactness, weights).
PORT_KRYLOV §9 lists Theorems 1.31 and 3.1 as verified; that 1.31 (§1.3.3) is the eigenvalue
characterisation of the zeros and 3.1 (§3.1.1) is Golub–Welsch ($\lambda_\nu =
\beta_0 v_{\nu,1}^2$) is my memory and the reviewer's, **still to check** against the book (two
memories are not a PDF). Positive definiteness is a definition of §1.1, not a theorem, so it is
cited by section. Golub–Meurant
Theorems 2.7, 2.9, 2.11, 2.13–2.14, 6.1–6.2 corroborate (Jackson note); which carries what is to
check, so declaration docstrings cite chapters only.

**Decided 2026-10-24.** L1 (b): every locator above and below stays "to check" until verified
against the books before the skeleton. L2 (a): Golub–Meurant is cited by chapter only (Ch. 4, 6,
12); the two "Theorem 6.6" citations this note had drafted (§4.6, §4.10) are now "Ch. 6". The
existing KS3 docstrings that cite "Theorem 6.6 (locator from the quarry)" are not this stage's
to change; they are listed for the skeleton author to align.

New keys, added with the skeleton (before citing, CONTRIBUTING §6):
- `Szego1975`: G. Szegő, *Orthogonal Polynomials*, 4th ed., AMS Colloquium Publications 23, 1975;
  Theorems 3.2.1 (recurrence), 3.2.2 (Christoffel–Darboux), 3.3.1 (zeros), 3.3.2 (interlacing),
  locators from memory, matching the reviewer's; to check.
- `GolubWelsch1969`: G. H. Golub and J. H. Welsch, "Calculation of Gauss quadrature rules", Math.
  Comp. 23 (1969), 221–230; the eigenvector weight formula is derived in §2, without a numbered
  theorem, so it is cited by section.
- `Chihara1978`: T. S. Chihara, *An Introduction to Orthogonal Polynomials*, Gordon and Breach,
  1978; Ch. I, Definition 3.1 (positive-definite moment functional; the reviewer's "Def. 1.3.1"),
  locator to check; cited in the docstring of `IsMomentPosDef` (review comment 7(iii)).
- Golub–Meurant chapter locators: Ch. 4 (Lanczos and orthogonal polynomials), Ch. 6 (Gauss
  quadrature), Ch. 12 (CG error estimation), plausible to both reviewer and author.

New result ids: `orthogonal-polynomial-recurrence`, `orthogonal-polynomial-existence`,
`orthogonal-polynomial-zeros`, `gauss-quadrature-uniqueness`, `lanczos-orthogonal-polynomials`,
`lanczos-jacobi-matrix`, `golub-welsch`; reused: `gauss-quadrature`, `lanczos-gauss-quadrature`.
Each is to be checked against the explorer's literature map for near-duplicates (R2).

## 10. Proof plan for dispatch

Rewritten after the Fable review (comments 1, 2, 9, 10): no L item is left; each row is one job
with a proof of at most 50 lines including any extra private helper; the four former L items are
split into rows whose statements are fixed in the skeleton (§4: #17a–#17d, #30a and #50d are
private, the rest public).

Every statement is in the skeleton with a `sorry` body before any job starts, so a job can use
every other declaration of the stage as a (sorried) dependency. The waves order the jobs so that
a dependency is proved before the jobs that lean on it; wave $w$ is one more than the largest
wave of the row's in-stage dependencies; within a wave every job is independent. A job may add
private helpers in its own file (the per-job checks are "only the target file changed" and
≤ 80 lines per proof). Lengths are realistic proof lengths. "a.e. zero" is #1, "kills" is #58.

Proved in the skeleton, not dispatched: #9–#12 (`rfl`), #48 (a move of an existing proof), #63
(the instance, `unfold gaussQuadrature; infer_instance`), and the 7 definitions. The former #27 is
deleted (Mathlib's `Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`).

| # | Name | File | Depends on (in stage) | Diff., length | Key lemmas and route | Wave |
|---|---|---|---|---|---|---|
| 1 | `ae_eval_eq_zero_of_integral_sq_eq_zero` | Moments | — | S, 10 | `integral_eq_zero_iff_of_nonneg_ae`, `integrable_eval_of_ae_mem_Icc` (with `pow`), `sq_eq_zero_iff` | 0 |
| 2 | `MatchesMoments.eq_of_ae_mem` | Moments | — | M, 40 | `Measure.ae_mem_finset_iff` on both; for $x \in s$, $\mu\{x\} = \int\ell_x\,d\mu$ via `setIntegral_finset`, `Measure.restrict_eq_self_of_ae_mem`, `Lagrange.eval_basis_self`, `eval_basis_of_ne`; `Lagrange.degree_basis` gives $\deg\ell_x < \lvert s\rvert$; `ofReal_measureReal` | 0 |
| 4 | `IsMomentPosDef.mono` | Basic | — | S, 5 | as `IsOrthogonalPolynomial.mono` | 0 |
| 13+14 | `monic_orthogonalPolynomial`, `natDegree_orthogonalPolynomial` | Recurrence | — | M, 35 | one job, one private helper proving both by two-step induction (`Nat.twoStepInduction`); `Monic.mul`, `monic_X_sub_C`, `Monic.sub_of_left`, `natDegree_mul'`, `natDegree_C_mul_le`; unfold by #9–#11 | 0 |
| 16 | `jacobiBeta_nonneg` | Recurrence | — | S, 8 | cases on `k`; `div_nonneg`, `integral_nonneg` (`sq_nonneg`), `measureReal_nonneg` | 0 |
| 26 | `isHermitian_jacobiMatrix` | Recurrence | — | S, 15 | `Matrix.IsHermitian.ext`; `star` trivial over ℝ; `split_ifs` with `omega` | 0 |
| 38 | `ae_mem_interpolatoryQuadrature` | Gauss | — | S, 15 | unfold; `Measure.ae_sum_iff`-style over the finset sum, `ae_dirac_iff`, `Measure.ae_smul_measure` | 0 |
| 39 | `interpolatoryQuadrature_eq_self_of_ae_mem` | Gauss | — | M, 35 | `Measure.ae_mem_finset_iff`; each weight $\int\ell_x\,d\mu = \mu.\mathrm{real}\{x\}$ (`setIntegral_finset`, `restrict_eq_self_of_ae_mem`, `Lagrange.eval_basis_self`/`_of_ne`); `ofReal_measureReal` | 0 |
| 46 | `Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec` | SpectralMeasure | — | M, 25 | `star_mulVec_dotProduct`, `(hA.aeval p).eq`, `Matrix.mulVec_mulVec`, `← map_mul`; `integral_eval_spectralMeasure`, `eval_mul`; `Matrix.IsHermitian.coe_re_quadForm` | 0 |
| 55a | `spectralMeasure_diagonal` | SpectralMeasure | — | S, 10 | `HasOrthonormalCols.spectralMeasure_eq_sum` with $\mathbf{U} = \mathbf{1}$ (`hasOrthonormalCols_one`-style, `conjTranspose_one`, `one_mulVec`) | 0 |
| 65 | **[SLQ-1]** `integrable_gaussQuadrature` | Gauss | — | S, 8 | unfold; `Integrable` of a finite sum of scaled Dirac masses (`integrable_finset_sum_measure`, `(integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top`), as in the existing `integral_interpolatoryQuadrature` proof | 0 |
| 69 | **[SLQ-1]** `MatchesMoments.smul` | Moments | — | S, 5 | `integral_smul_measure`, `congrArg` | 0 |
| 70 | **[SLQ-1]** `MatchesMoments.finsetSum` | Moments | — | S, 20 | `integral_finsetSum_measure` with integrability `integrable_eval_of_ae_mem_Icc` on each summand; `Finset.sum_congr` | 0 |
| 58 | `integral_eval_mul_eq_zero_of_integral_sq_eq_zero` | Moments | #1 | S, 10 | #1, `integral_eq_zero_of_ae` (`Filter.EventuallyEq` with `mul_eq_zero`) | 1 |
| 57 | `isMomentPosDef_iff_forall_finset` | Basic | #1 | M, 35 | ⇒: $s$ carries $\mu$ and $\lvert s\rvert < k$ give the nonzero `Lagrange.nodal s id` (degree $\lvert s\rvert$, `Lagrange.degree_nodal`) of norm $0$ (`integral_eq_zero_of_ae`, `Lagrange.eval_nodal_at_node`). ⇐: $p \ne 0$ of norm $0$ vanishes a.e. (#1), so $\mu$ is carried by `p.roots.toFinset`, of card $\le \deg p < k$ (`Multiset.toFinset_card_le`, `card_roots'`, `mem_roots`) | 1 |
| 15 | `degree_orthogonalPolynomial` | Recurrence | #13+14 | S, 3 | `degree_eq_natDegree` with `Monic.ne_zero` | 1 |
| 22 | `MatchesMoments.orthogonalPolynomial_eq` | Recurrence | #13+14 | M, 50 | two-step induction; rewrite $\int x\,p(x)^2$ as $\int (X p^2)(x)$ (`eval_mul`, `eval_pow`, `eval_X`); degree bounds `natDegree_mul_le`, `natDegree_pow_le`; `MatchesMoments.mono` | 1 |
| 29 | `card_gaussNodes_le` | Zeros | #13+14 | S, 5 | `Multiset.toFinset_card_le`, `card_roots'` | 1 |
| 47 | `Matrix.IsHermitian.norm_aeval_mulVec_sq` | SpectralMeasure | #46 | S, 10 | norm squared as `re (star v ⬝ᵥ v)` (as in `norm_arnoldiMatrix_col_last`), #46 with $r = p$ | 1 |
| 55b | `spectralMeasure_diagonal_sqrt_of_ae_mem` | SpectralMeasure | #55a | M, 25 | #55a; `Real.norm_eq_abs`, `sq_abs`, `Real.sq_sqrt` (`measureReal_nonneg`), `ENNReal.ofReal_toReal`; the sum over the subtype is `Finset.sum_coe_sort`; `Measure.ae_mem_finset_iff` | 1 |
| 50b | `aeval_orthogonalPolynomial_mulVec_sub_pow_mulVec_mem_krylovSpace` | LanczosPolynomials | #13+14 | S, 15 | $\pi_j - X^j$ has degree $< j$ (monic, `degree_sub_lt_left`); `aeval_mulVec_mem_krylovSpace`, `map_sub`, `Matrix.sub_mulVec` | 1 |
| 64 | **[SLQ-1]** `integral_gaussQuadrature_eq_sum` | Gauss | #38 | S, 15 | #38 and `Measure.ae_mem_finset_iff` (any finite measure carried by a finset), then `integral_finsetSum_measure`, `integral_smul_measure`, `integral_dirac`; or `setIntegral_finset` with `Measure.restrict_eq_self_of_ae_mem`; no support hypothesis on $\mu$ | 1 |
| 18 | `integral_orthogonalPolynomial_succ_sq` | Recurrence | #1, #58 | M, 30 | unfold `jacobiBeta`; if $\|\pi_k\|^2 \ne 0$, `div_mul_cancel₀`; else $\beta_k = 0$, so $\pi_{k+1} = (X - \alpha_k)\pi_k$ (#10, #11) and its square integral is $\int\pi_k\cdot(X - \alpha_k)^2\pi_k = 0$ (#58); $k = 0$: $\mu(\mathbb{R}) = 0$ gives $\mu = 0$ | 2 |
| 59 | `integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero` | Recurrence | #58 | S, 20 | unfold `jacobiAlpha`; `integral_sub`, `integral_mul_const`; if $\|\pi_k\|^2 \ne 0$, `div_mul_cancel₀`; else both integrals are $0$ (#58 with $r = X\pi_k$) | 2 |
| 17a | private `integral_orthogonalPolynomial_add_two_mul_eq_zero_of_degree_lt` | Recurrence | #13+14, #15 | M, 30 | expand #11; `integral_sub`, `integral_mul_const`; $\int\pi_{k+1}\,(Xr) = 0$ (`h1`, $\deg Xr < k + 1$), $\int\pi_{k+1}r = 0$ (`h1`), $\int\pi_k r = 0$ (`h0`); integrability `integrable_eval_of_ae_mem_Icc` | 2 |
| 23 | `MatchesMoments.jacobiAlpha_eq` | Recurrence | #22 | S, 15 | unfold; #22 with `mono`; two integrals of degree $\le 2k + 1$ | 2 |
| 24 | `MatchesMoments.jacobiBeta_eq` | Recurrence | #22 | S, 15 | cases; $k = 0$: `MatchesMoments.measureReal_univ_eq`; else #22 at $k + 1$, $k$ | 2 |
| 30a | private `IsMomentPosDef.false_of_ae_nonneg_mul` | Zeros | #57 | M, 25 | $\int pr = 0$ (`hp`, `hr`), $pr \ge 0$ a.e., so $pr = 0$ a.e. (`integral_eq_zero_iff_of_nonneg_ae`); with `hμ` and `hz`, $\mu$ is carried by $s$; #57 contradicts `hs` | 2 |
| 49 | `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff` | LanczosPolynomials | #47, #57 | M, 35 | ⇐: #47, #48. ⇒: $\mathbf{Q}$ spanning $\mathcal{K}_{\nu+1} = \mathcal{K}_\nu$ (`exists_hasOrthonormalCols_range_eq_krylovSpace`, `krylovSpace_eq_of_krylovGrade_le`), $s$ its Ritz values ($\lvert s\rvert \le \nu$); `HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero` gives $\pi_s(\mathbf{A})\mathbf{b} = \mathbf{0}$, so $\mu$ is carried by $s$ (#47, #1); #57 | 2 |
| 17b | private `integral_orthogonalPolynomial_add_two_mul_succ` | Recurrence | #59, #15 | M, 25 | expand #11: $\int(x - \alpha_{k+1})\pi_{k+1}^2 - \beta_{k+1}\int\pi_k\pi_{k+1}$; the first is #59, the second `h1` with $\deg\pi_k = k$ (#15) | 3 |
| 17c | private `integral_orthogonalPolynomial_add_two_mul_self` | Recurrence | #18, #15, #13+14 | M, 35 | expand #11; $X\pi_k = \pi_{k+1} + (X\pi_k - \pi_{k+1})$ with the bracket of degree $\le k$ (monic, #13+14), so $\int\pi_{k+1}\cdot X\pi_k = \|\pi_{k+1}\|^2$ by `h1`; $\int\pi_{k+1}\pi_k = 0$ by `h1`; then $\|\pi_{k+1}\|^2 - \beta_{k+1}\|\pi_k\|^2 = 0$ by #18 | 3 |
| 25 | `MatchesMoments.jacobiMatrix_eq` | Recurrence | #23, #24 | S, 20 | `ext i j`; unfold; `split_ifs`; #23, #24 with `mono` (indices $< k$) | 3 |
| 62 | `integral_orthogonalPolynomial_sq_eq_prod` | Recurrence | #18 | S, 15 | induction; $k = 0$: $\int 1 = \mu.\mathrm{real}\,\mathbb{R}$ (`integral_const`, `jacobiBeta_zero`); step #18, `Finset.prod_range_succ` | 3 |
| 17d | private `isOrthogonalPolynomial_orthogonalPolynomial_add_two` | Recurrence | #17a, #17b, #17c, #13+14, #15 | M, 40 | for $\deg r < k + 2$: $r = c\,\pi_{k+1} + c'\pi_k + r_0$ with $\deg r_0 < k$ (`modByMonic_add_div` twice, `degree_modByMonic_lt`, the quotients are constants by degree); `integral_add`, `integral_const_mul`; #17a, #17b, #17c | 4 |
| 17 | `isOrthogonalPolynomial_orthogonalPolynomial` | Recurrence | #17d, #59 | S, 20 | `Nat.twoStepInduction`; $k = 0$ vacuous (`degree_lt_zero`… $r = 0$); $k = 1$: $r = C\,c$ (`eq_C_of_degree_le_zero`), $\int(x - \alpha_0)\,c = 0$ from #59 at $0$ ($\pi_0 = 1$); step #17d | 5 |
| 19 | `integral_mul_orthogonalPolynomial_mul_orthogonalPolynomial_succ` | Recurrence | #17, #15 | M, 35 | $x\pi_k = \pi_{k+1} + \alpha_k\pi_k + \beta_k\pi_{k-1}$ from #10/#11 (cases $k = 0$, $k + 1$); `integral_add`, #17 at $k+1$ against $\pi_k$, $\pi_{k-1}$ (#15) | 6 |
| 20 | `isMomentPosDef_succ_iff` | Recurrence | #17, #18, #13+14, #15 | M, 40 | ⇒: $p = \pi_k$. ⇐: norms are positive for $j \le k$ (contrapositive of #18 by induction); for $p \ne 0$ of degree $d \le k$, $p = c\,\pi_d + r$, $c$ the leading coefficient, $\deg r < d$, and $\int p^2 = c^2\|\pi_d\|^2 + \int r^2$ by #17 | 6 |
| 21 | `IsMomentPosDef.eq_orthogonalPolynomial` | Recurrence | #17, #13+14, #15 | M, 25 | $d = p - \pi_k$, $\deg d < k$ (`degree_sub_lt_left`); $\int d^2 = \int d\,p - \int d\,\pi_k = 0$; definiteness gives $d = 0$ | 6 |
| 30 | `IsMomentPosDef.card_roots_orthogonalPolynomial` | Zeros | #30a, #13+14, #17 | M, 35 | `exists_prod_multiset_X_sub_C_mul`: $\pi = Rg$, $g$ root-free, monic (`Monic.of_mul_monic_left`, `monic_multisetProd_X_sub_C`), so $g > 0$ (Mathlib `Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`, vacuous root hypothesis); if $\deg R < k$, #30a with $r = R$ ($\pi R = R^2 g \ge 0$) and $s$ = roots of $R$ | 6 |
| 31 | `IsMomentPosDef.nodup_roots_orthogonalPolynomial` | Zeros | #30a, #13+14, #17 | M, 30 | `Multiset.nodup_iff_count_le_one`, `count_roots`; multiplicity $\ge 2$ (`le_rootMultiplicity_iff`) gives $\pi = (X - x)^2h$; #30a with $r = h$ ($\pi h = ((X - x)h)^2$), $s$ = roots of $(X - x)h$, card $\le k - 1$ | 6 |
| 34 | `IsMomentPosDef.gaussNodes_subset_Icc` | Zeros | #30a, #17, #13+14 | M, 35 | a root $x < a$ gives $\pi = (X - x)h$ (`mul_divByMonic_eq_iff_isRoot`); #30a with $r = h$ ($\pi h = (X - x)h^2 \ge 0$ on $[a, b]$, a.e. by `hμ`), $s$ = roots of $h$; $x > b$ with $r = -h$ | 6 |
| 50a | `Matrix.IsHermitian.star_dotProduct_aeval_orthogonalPolynomial_mulVec_eq_zero_of_mem` | LanczosPolynomials | #17, #46 | M, 35 | `krylovSpace_eq_span`, `Submodule.span_induction` (or `mem_span_range_iff_exists_fun`); for $\mathbf{A}^i\mathbf{b} = X^i(\mathbf{A})\mathbf{b}$, #46 and #17 ($i < j$); `dotProduct` linearity in the first slot with `star` | 6 |
| 32 | `IsMomentPosDef.nodal_gaussNodes` | Zeros | #30, #31, #13+14 | S, 15 | `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`; `Lagrange.nodal_eq`; `Multiset.toFinset_val`, `Multiset.Nodup.dedup` | 7 |
| 33 | `IsMomentPosDef.card_gaussNodes` | Zeros | #30, #31 | S, 5 | `Multiset.toFinset_card_of_nodup` | 7 |
| 35 | `ae_mem_gaussNodes_of_not_isMomentPosDef` | Zeros | #20, #18, #1, #13+14 | M, 35 | $k = j + 1$ (definiteness at $0$ is vacuous); #20 gives $\|\pi_j\|^2 = 0$, #18 $\|\pi_k\|^2 = 0$, #1 a.e. zero; a zero of the monic $\pi_k$ is in `roots.toFinset` (`Multiset.mem_toFinset`, `mem_roots`) | 7 |
| 50c | `Matrix.IsHermitian.aeval_orthogonalPolynomial_mulVec_eq_zero_of_krylovGrade_le` | LanczosPolynomials | #49, #20, #47 | S, 15 | #49 at $j + 1$ is false, so #20 gives $\|\pi_j\|^2 \le 0$; #47, `norm_eq_zero` | 7 |
| 50d | private `arnoldiMatrix_col_last_eq_of_lt_krylovGrade` | LanczosPolynomials | #50a, #50b, #47 | M, 45 | `exists_gramSchmidtR_smul_arnoldiMatrix_col_last`: $r_j\mathbf{q}_j - \pi_j(\mathbf{A})\mathbf{b} \in \mathcal{K}_j$ (#50b); both orthogonal to $\mathcal{K}_j$ (`star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem`, #50a), so equal; $r_j = \|\pi_j(\mathbf{A})\mathbf{b}\| \ne 0$ (`norm_arnoldiMatrix_col_last`, `gramSchmidtR_apply_self_nonneg`, `gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff`) | 7 |
| 60 | `HasOrthonormalCols.nodal_eq_orthogonalPolynomial` | Quadrature | #21, #49 | S, 20 | #21 with #49 (`hq`), `Lagrange.nodal_monic`, `natDegree_nodal` and `card_spectrum_conjTranspose_mul_mul_eq` (degree $q$), `HasOrthonormalCols.isOrthogonalPolynomial_nodal` | 7 |
| 36 | `isOrthogonalPolynomial_nodal_gaussNodes` | Zeros | #32, #33, #17, #35 | M, 30 | `by_cases`; definite: #32, #33, #17; else the nodal polynomial vanishes on the nodes (`Lagrange.eval_nodal_at_node`), which carry $\mu$ (#35): `integral_eq_zero_of_ae` | 8 |
| 42 | **[SLQ-1]** `ae_mem_Icc_gaussQuadrature` | Gauss | #38, #34, #39, #35 | S, 20 | `by_cases`; definite: #38, #34; else #39, #35, `hμ` | 8 |
| 50 | `Matrix.IsHermitian.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec` | LanczosPolynomials | #50c, #50d | S, 15 | `arnoldiMatrix_col_eq_col_last`; below the grade #50d; from the grade on `arnoldiMatrix_col_last_eq_zero_iff` and #50c (`smul_zero`) | 8 |
| 61 | `HasOrthonormalCols.gaussNodes_spectralMeasure_eq` | Quadrature | #60 | S, 10 | rewrite #60 backwards; `Lagrange.nodal_eq`, `Polynomial.roots_prod_X_sub_C`, `Finset.val_toFinset` | 8 |
| 40 | **[SLQ-1]** `matchesMoments_gaussQuadrature` | Gauss | #36, #33, #39, #35 | S, 15 | `by_cases`; definite: `IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature` with #36, #33; else #39, #35, `MatchesMoments.refl` | 9 |
| 41 | `integral_gaussQuadrature` | Gauss | #36 | S, 5 | `IsOrthogonalPolynomial.integral_interpolatoryQuadrature` with #36 | 9 |
| 44 | `IsMomentPosDef.gaussQuadrature_real_singleton_pos` | Gauss | #36, #33 | M, 30 | the mass at $x$ of the Dirac sum (`Measure.coe_finsetSum`, `dirac_apply`, distinct nodes) is $\int\ell_x = \int\ell_x^2$ (`integral_eval_basis_eq_integral_sq`, #36) $> 0$ (`Lagrange.basis_ne_zero`, `degree_basis`, #33) | 9 |
| 51 | `Matrix.IsHermitian.lanczosAlpha_lanczosState` | LanczosPolynomials | #50, #46, #47 | M, 40 | `lanczosTridiagonal_eq` at $q = j + 1$, entry $(j, j)$; `NLAlib.conjTranspose_mul_apply`; #50; #46 with $r = X\pi_j$ (`aeval_mul`, `aeval_X`); #47; `RCLike.ofReal_inj` | 9 |
| 52 | `Matrix.IsHermitian.lanczosState_beta` | LanczosPolynomials | #50, #46, #47, #19, #18 | M, 45 | entry $(j+1, j)$ at $q = j + 2$; #50 twice; #46; #19; $\|\pi_{j+1}\|^2/(\|\pi_{j+1}\|\|\pi_j\|) = \sqrt{\beta_{j+1}}$ (`Real.sqrt_div'`, `Real.sqrt_sq`; zero cases apart) | 9 |
| 43 | **[SLQ-1]** `gaussQuadrature_real_univ` | Gauss | #40 | S, 5 | `(#40).measureReal_univ_eq`, `.symm` | 10 |
| 45 | `MatchesMoments.eq_gaussQuadrature` | Gauss | #2, #29, #38, #40 | M, 25 | $T = s \cup$ `gaussNodes μ k`; both carried by $T$ (#38); `h.symm.trans` #40; $\lvert T\rvert \le 2k$ (`Finset.card_union_le`, #29); `mono`; #2 (with the instance #63) | 10 |
| 53 | `Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix` | LanczosPolynomials | #51, #52 | S, 20 | `ext i j`; unfold, `Matrix.map_apply`, `split_ifs`; #51, #52, `RCLike.algebraMap_eq_ofReal` | 10 |
| 54 | **[SLQ-1]** `Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature` | Quadrature | #45 | S, 25 | `exists_hasOrthonormalCols_range_eq_krylovSpace`; `HasOrthonormalCols.lanczosQuadrature_eq`; carried by the Ritz values (`spectralMeasure_compl_spectrum_eq_zero`), at most $q$ (private `card_spectrum_le_of_range_eq`); `(hA.matchesMoments_lanczosQuadrature b q).symm`; an interval containing the finite spectrum and `ae_mem_Icc_spectralMeasure`; #45 | 11 |
| 66 | **[SLQ-1]** `abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn` | Gauss | #40, #42, #43, #65 | S, 15 | M0 (`MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn`) with #40, `hμ`, #42, `hf`, #65; mass by #43 for $k > 0$; $k = 0$: the rule is $0$ (`gaussNodes μ 0 = ∅`) and $\varepsilon \ge 0$ unless $[a, b]$ is empty | 11 |
| 55 | `spectralMeasure_jacobiMatrix` | Quadrature | #55b, #54, #53, #25, #29, #38, #40, #42, #43, #45 | M, 45 | $\nu$ := the Gauss rule; #55b realises it as $\mu_{\mathbf{D},\mathbf{w}}$ on the index type `gaussNodes μ (k + 1)` (with #38, #63); `lanczosQuadrature_succ_eq` for $(\mathbf{D}, \mathbf{w})$, #53, #54; #45 with `refl`, #42, #29 ($\nu$ is its own Gauss rule); #25 with #40; $\|\mathbf{w}\|^2 = \nu(\mathbb{R}) = \mu(\mathbb{R})$ (`spectralMeasure_real_univ`, #43); `Matrix.map_id` | 12 |
| 68 | **[SLQ-1]** `abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith` | Gauss | #66 | S, 15 | `exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith` in degree $2k + 1$ (𝕜 := ℝ); integrability from `LipschitzOnWith.continuousOn`, `ContinuousOn.integrableOn_Icc`, `Measure.restrict_eq_self_of_ae_mem`; #66; `field_simp`, `ring` (as the KS4 Lanczos corollary) | 12 |
| 67 | **[SLQ-1]** `spectralMeasure_map_jacobiMatrix` | Quadrature | #55 | M, 35 | diagonalise the real $\mathbf{J}$ (`Matrix.IsHermitian.eigenvectorUnitary` over ℝ), map the factorisation to 𝕜 (`Matrix.map_mul`, `RCLike.ofReal` casts), `HasOrthonormalCols.spectralMeasure_eq_sum` on both sides; the two Dirac sums agree entrywise (`‖(r : 𝕜)‖ = |r|`); then #55 | 13 |
| 56 | `HasOrthonormalCols.gaussQuadrature_succ_eq_sum` | Quadrature | #55 | S, 15 | rewrite #55, `HasOrthonormalCols.spectralMeasure_eq_sum` (`hr` by `rfl`, the diagonal's casts by `simp`); $(\mathbf{U}^{\mathsf{H}}\mathbf{e}_0)_i = \mathbf{U}_{0,i}$ | 13 |

**Counts.** 73 declarations to prove: 66 public theorems, 1 instance, 6 private steps. S 42 (6
of them in the skeleton), M 31, L 0. Dispatched: 66 jobs (#13 and #14 are one job), about 1,500
lines of proof. The longest rows are #22 (50), #50d, #52 and #55 (45 each).

**[SLQ-1]** marks the SLQ interface ("Interface for SLQ"): #40, #42, #43, #54, #64–#70. They are
fixed in the skeleton for SLQ's first wave and get priority along their chains; the wave column
still gives when each can be proved.

**Waves.** 0: #1, 2, 4, 13+14, 16, 26, 38, 39, 46, 55a, 65, 69, 70 (13 jobs); 1: #58, 57, 15, 22,
29, 47, 55b, 50b, 64; 2: #18, 59, 17a, 23, 24, 30a, 49; 3: #17b, 17c, 25, 62; 4: #17d; 5: #17;
6: #19, 20, 21, 30, 31, 34, 50a; 7: #32, 33, 35, 50c, 50d, 60; 8: #36, 42, 50, 61; 9: #40, 41, 44,
51, 52; 10: #43, 45, 53; 11: #54, 66; 12: #55, 68; 13: #56, 67. #18 precedes #17 (wave 2 against
5). The critical path is #1 → #58 → #59 → #17b → #17d → #17 → #20 → #35 → #36 → #40 → #45 → #54 →
#55 → #56/#67, 14 waves; the waves are a safety order, and with the scaffold in place several can
be released together if the orchestrator accepts the risk of a prover meeting a false dependency
(none is expected: each statement was checked by hand and by the reviewer, the unconditional ones
also in exact arithmetic).

**For the prover brief.** The degenerate cases ($\|\pi_k\| = 0$, $\mu = 0$, $q$ past the grade)
are part of every unconditional statement (#17 and its steps, #18, #36, #40, #42, #50–#54); a proof
that assumes nondegeneracy is incomplete. Integrability always comes from
`integrable_eval_of_ae_mem_Icc` (finite measure, compact support). `x / 0 = 0` is Lean's
convention and is what the junk values rely on. The private steps' hypotheses `h1`, `h0` are the
inductive hypotheses; their statements may not be changed by the job.

## 11. Mathlib search (pinned commit)

| Need | Found | Use |
|---|---|---|
| measure carried by a finite set | `MeasureTheory.Measure.ae_mem_finset_iff` (`μ = ∑ a ∈ s, μ {a} • dirac a`) | #2, #39, #55b |
| integral over a finite set | `MeasureTheory.setIntegral_finset`, `Measure.restrict_eq_self_of_ae_mem` | #2, #39 |
| nonnegative function with zero integral | `integral_eq_zero_iff_of_nonneg_ae` | #1 |
| factor off the real roots | `Polynomial.exists_prod_multiset_X_sub_C_mul`, `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`, `card_roots'`, `count_roots`, `le_rootMultiplicity_iff` | #30–#33 |
| positivity of a root-free real polynomial | `Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg` (`Mathlib/Analysis/Polynomial/Order.lean`; also the `≤`, `<` and mirror forms). My first search (`roots = 0` with `eval`, `eval_pos`) missed it; found by the review | #30 |
| Lagrange basis, nodal polynomial | `Lagrange.basis`, `nodal_eq`, `nodal_monic`, `eval_basis_self`, `degree_basis`, `basis_ne_zero`, `eq_interpolate` | #2, #32, #39, #44 |
| orthogonal polynomials of a measure, Stieltjes procedure, three-term recurrence | searched (`orthogonal`, `three.term`, `Stieltjes`), none beyond Chebyshev `T_add_two` and `Chebyshev/Orthogonality.lean` for `measureT` | definitions §2 |
| Gram–Schmidt | `InnerProductSpace.gramSchmidt` (needs an inner-product space) | not used, §0 item 2 |
| Jacobi matrix | `Algebra.PreSubmersivePresentation.jacobiMatrix` (unrelated) | name collision noted, OQ4 |
| Hankel matrix | searched (`hankel`, `Hankel`), none by name; it is `Matrix.gram` of the monomials in $L^2(\mu)$, with `Matrix.posDef_gram_iff_linearIndependent` (`Analysis/InnerProductSpace/GramMatrix.lean`) | §8 item 7, OQ5(b) |
| roots of a nodal polynomial | `Polynomial.roots_prod_X_sub_C` | #61 |
| Christoffel–Darboux, Gauss–Radau | searched, none | §8 |
| tridiagonal determinant | `Matrix.det_succ_row` only | §8 item 9 |
| measure support | `MeasureTheory.Measure.support` | §8 item 7 |
