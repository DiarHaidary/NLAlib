# Design note: Krylov stage K2b, sharpness of the Krylov bounds

Status: draft, 2026-10-17, for review before any proof. Sources: the K2 note
(`Krylov-Functions.md` §6, which fixes Theorem 2's statement and lists the foreseen shared
lemmas), the K1 note (`Krylov-LinearSystems.md` L11, §3.8), the proved `NLAlib/Krylov/**` and
`Polynomial/Chebyshev/Residual.lean` at `ec180ed`, and `ChenPersson2026` (arXiv:2608.07160:
Theorem 2 and its proof, Lemmas 8 and 9, (13) to (16)). The skeleton,
`~/Documents/NLA-lib/krylov-scratch/skeleton-k2b/` (one file per new file, `Additions/` per
addition), elaborates in one file through its `check.py` against the built worktree under
`lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 -Dlinter.missingDocs=true
-Dweak.linter.mathlibStandardSet=true`, with only `sorry` warnings (27). It is the
specification; this note repeats the headline signatures.

The maintainer's request (2026-10-17): "for CG do we also have the spectrum optimal bound? We
can prove that this bound, the sqrt(cond) bound etc are sharp when you look at all problem
instances (i.e. exhibit a problem attaining the bound). I guess this is partly contained in the
stieltjes function thing". The interval case is done (`WorstCase.lean`, Chebyshev extrema);
K2b adds Theorem 2 with its CG reading (Remark 3) and Greenbaum's theorem on every spectrum.

Conventions, as in K2: squared norms `RCLike.re (quadForm N (w - y))`, unsquared Euclidean
norms `‖WithLp.toLp 2 _‖`; the best approximation is never named, a lower bound says "some `y`
in the Krylov space is this much better", which bounds the minimum.

## 1. Overview and the main design findings

K2b proves (1) **Greenbaum's theorem**: for every positive definite $\mathbf{A}$, start and $q$
some right-hand side makes the CG error equal to `residualMinimax (spectrum ℝ A) q` times the
initial error, and likewise for the MINRES residual for every Hermitian $\mathbf{A}$; with K1's
upper bounds, the worst case over $\mathbf{b}$ equals the spectrum minimax value. (2)
**Theorem 2**: with at least $q + 1 \ge 2$ distinct eigenvalues, the Lanczos-FA error for some
$(z + s)^{-1}$ and $\mathbf{b}$ is within $1 - \eta$ of the factor
$\tfrac12(\kappa^{E/2} + \kappa^{-E/2})$ times the error of a Krylov vector; its general form
(any shift, any norm $\nu(\mathbf{A})$, any two eigenvalues) shows Theorem 5 optimal for every
$\nu$ and $s$; its CG reading shows the Euclidean factor $\tfrac12(\sqrt\kappa + 1/\sqrt\kappa)$
optimal.

**Finding 1: Theorem 2 needs no Ritz values and no Gauss quadrature; the orthogonal
polynomial step is one divided-difference lemma.** The paper computes the Ritz polynomial of a
prescribed weighting
(Lemma 8) from its uniqueness as the monic degree-$q$ orthogonal polynomial. In the library,
Lanczos-FA for $(z + s)^{-1}$ is already CG on $\mathbf{A} + s\mathbf{I}$
(`Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate`), and CG's Galerkin condition
(`Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero`) says that its
residual polynomial $\pi$ is orthogonal, in the spectral weights $w$ of $\mathbf{b}$, to every
polynomial of degree less than $q$. On $q + 1$ nodes the orthogonal complement of those
polynomials is spanned by the nodal weights (a divided-difference fact), so $w\pi$ is a multiple
of the nodal weights. That is Lemma 8's content without Ritz values, the grade, or monicity. So the
foreseen "Ritz polynomial of a prescribed weighting" and "Ritz values as Gauss nodes and
weights" are not built: explicit Lanczos on few eigenvalues reduces to one Matrix lemma (a
vector with prescribed spectral weights) and one divided-difference lemma.

**Finding 2: the discrete minimax duality is Mathlib's Sion theorem.** Mathlib has
`Sion.minimax` (`Mathlib/Topology/Sion.lean`) with only one compact side. Applied to
$-\sum_x w_x p(x)^2$ on the standard simplex (compact, linear in $w$) and the convex set of
residual polynomials (concave in $p$), it gives the dual weights. No alternation theorem
(de la Vallée-Poussin, equioscillation) is needed, and none would hold in the MINRES case:
$x, \dots, x^q$ is not a Haar system on a set with points on both sides of $0$. No minimiser
of the minimax problem is needed either.

**Finding 3: no new interface.** One new definition, `dividedDifference`, with its bridge to
Mathlib's `Lagrange` (the only new §5.3 row; question 1). The prescribed-weights vector is
produced by an existence lemma, not carried by a predicate: no consumer needs "a vector with
spectral weights $w$" as a hypothesis yet (rejected: a predicate `HasSpectralWeights A v w s`,
§11).

## 2. Headline statements

Common context `{𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]`, `open
Polynomial`.

**Greenbaum, CG** (`Krylov/LinearSystems/WorstCase.lean`):

```lean
theorem _root_.Matrix.PosDef.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul
    {A : Matrix n n 𝕜} (hA : A.PosDef) [Nonempty n] (x₀ : n → 𝕜) (q : ℕ) :
    ∃ xs : n → 𝕜, xs ≠ x₀ ∧
      RCLike.re (quadForm A (xs - cgIterate A (A *ᵥ xs) x₀ q)) =
        residualMinimax (spectrum ℝ A) q ^ 2 * RCLike.re (quadForm A (xs - x₀))
```

**Greenbaum, MINRES** (same file):

```lean
theorem _root_.Matrix.IsHermitian.exists_norm_sub_mulVec_gmresIterate_eq_residualMinimax_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) [Nonempty n] (x₀ : n → 𝕜) (q : ℕ) :
    ∃ b : n → 𝕜, b ≠ A *ᵥ x₀ ∧
      ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ =
        residualMinimax (spectrum ℝ A) q * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖
```

Their corollaries `Matrix.PosDef.isGreatest_re_quadForm_sub_cgIterate_div` and
`Matrix.IsHermitian.isGreatest_norm_sub_mulVec_gmresIterate_div` state
`IsGreatest (ratio '' {xs | xs ≠ x₀}) (residualMinimax (spectrum ℝ A) q ^ 2)` (resp. the
residual ratio over `{b | b ≠ A *ᵥ x₀}` and the unsquared value).

Shape: the start is a parameter and the witness the solution (resp. right-hand side), as in
the upper bounds `…_le_residualMinimax_sq_mul` and `…_le_residualMinimax_mul`; the equation is
primary (§5.2), `IsGreatest` the "worst case equals" corollary; `[Nonempty n]` excludes the empty
matrix. MINRES needs no definiteness or invertibility: on a singular $\mathbf{A}$ the value is $1$.

**Theorem 2, general form** (`Krylov/Functions/Optimality.lean`):

```lean
theorem _root_.Matrix.PosDef.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA
    {A : Matrix n n 𝕜} (hA : A.PosDef) {q : ℕ} (hq : 0 < q)
    (hcard : q + 1 ≤ (spectrum ℝ A).ncard) {ν : ℝ → ℝ} (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x)
    {s : ℝ} (hs : 0 ≤ s) {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ spectrum ℝ A) (hx₂ : x₂ ∈ spectrum ℝ A)
    {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) :
    ∃ b : n → 𝕜,
      0 < RCLike.re (quadForm (cfc ν A)
        (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q)) ∧
      ∃ y ∈ krylovSpace A b q,
        (1 - η) ^ 2 * ((ν x₁ * (x₂ + s) + ν x₂ * (x₁ + s)) ^ 2 /
            (4 * (ν x₁ * (x₂ + s)) * (ν x₂ * (x₁ + s)))) *
          RCLike.re (quadForm (cfc ν A) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - y)) ≤
        RCLike.re (quadForm (cfc ν A)
          (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q))
```

The factor is $(R + 1)^2/(4R)$ with $R = \frac{\nu(x_1)(x_2 + s)}{\nu(x_2)(x_1 + s)}$, written
symmetrically so that no ratio is nested. For $\mu = \delta_s$ the smallest $R$ admissible in
Theorem 5 (`Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure`)
is the maximum of this $R$ over pairs of eigenvalues, so this theorem says Theorem 5 is optimal
for every $\nu$ and every $s \ge 0$: a statement stronger than the paper's and the core of the
other two. `x₁ = x₂` is allowed (factor $1$). The lower-bound names carry `inv_add` because the
conclusion is about the shifted inverse $(x + s)^{-1}$ the witness uses, as in
`Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate`; the upper bounds hold for every Stieltjes
$f$ and carry no such tag.

**Theorem 2** (same file; the skeleton-k2 draft, unchanged):

```lean
theorem _root_.Matrix.PosDef.exists_inv_add_le_re_quadForm_rpow_cfc_mulVec_sub_lanczosFA
    {A : Matrix n n 𝕜} (hA : A.PosDef) {q : ℕ} (hq : 0 < q)
    (hcard : q + 1 ≤ (spectrum ℝ A).ncard) (α : ℝ) {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) :
    ∃ (b : n → 𝕜) (s : ℝ), 0 ≤ s ∧
      0 < RCLike.re (quadForm (A ^ α)
        (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q)) ∧
      ∃ y ∈ krylovSpace A b q,
        ((1 - η) * ((pseudoConditionNumber A ^ (max α (1 - α) / 2) +
            pseudoConditionNumber A ^ (-(max α (1 - α) / 2))) / 2)) ^ 2 *
          RCLike.re (quadForm (A ^ α) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - y)) ≤
        RCLike.re (quadForm (A ^ α)
          (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q))
```

`Result: lanczos-fa-near-optimality-lower-bound`. `hq` is needed (at $q = 0$ the ratio is $1$),
`hη₁` too ($(1 - \eta)^2$ grows past $\eta = 2$); the positive error excludes trivial instances;
the paper's $\kappa > 1$ follows from two distinct positive eigenvalues.

**CG, Euclidean norm** (same file; the paper's Remark 3 says the hard instance at $\alpha = 0$
is CG):

```lean
theorem _root_.Matrix.PosDef.exists_le_norm_sub_cgIterate {A : Matrix n n 𝕜} (hA : A.PosDef)
    {q : ℕ} (hq : 0 < q) (hcard : q + 1 ≤ (spectrum ℝ A).ncard) {η : ℝ} (hη : 0 < η)
    (hη₁ : η ≤ 1) :
    ∃ xs : n → 𝕜, 0 < ‖WithLp.toLp 2 (xs - cgIterate A (A *ᵥ xs) 0 q)‖ ∧
      ∃ y ∈ krylovSpace A (A *ᵥ xs) q,
        (1 - η) * ((Real.sqrt (pseudoConditionNumber A) +
            (Real.sqrt (pseudoConditionNumber A))⁻¹) / 2) * ‖WithLp.toLp 2 (xs - y)‖ ≤
          ‖WithLp.toLp 2 (xs - cgIterate A (A *ᵥ xs) 0 q)‖
```

Unsquared, as its upper bound `Matrix.IsHermitian.norm_sub_cgIterate_le_mul_norm_sub`; zero
start (a start $\mathbf{x}_0$ is the same instance with $\mathbf{r}_0$ for $\mathbf{b}$). Not
stated, for lack of a consumer: the interval form of Theorem 2 (any diagonal matrix with $q + 1$
entries including $a, a'$) and CG in $\mathbf{A}^\alpha$-norms, $\alpha \le 1/2$ (Theorem 2 at
$s = 0$).

## 3. Shared lemmas and their homes

**Divided differences** (`Polynomial/Interpolation/DividedDifference.lean`, new; namespace
`NLAlib`, field `F`, nodes `v : ι → F` on `s : Finset ι`, Mathlib's `Lagrange` shape):

```lean
noncomputable def dividedDifference (s : Finset ι) (v : ι → F) (r : ι → F) : F :=
  ∑ i ∈ s, Lagrange.nodalWeight s v i * r i

theorem exists_eq_mul_nodalWeight (hvs : Set.InjOn v s) (hs : #s = q + 1) {z : ι → F}
    (hz : ∀ p : F[X], p.degree < q → ∑ i ∈ s, z i * p.eval (v i) = 0) :
    ∃ c : F, ∀ i ∈ s, z i = c * Lagrange.nodalWeight s v i
theorem isLeast_sum_mul_sq_sub_eval {v : ι → ℝ} (hvs : Set.InjOn v s) (hs : #s = q + 1)
    {u : ι → ℝ} (hu : ∀ i ∈ s, 0 < u i) (r : ι → ℝ) :
    IsLeast ((fun p : ℝ[X] => ∑ i ∈ s, u i * (r i - p.eval (v i)) ^ 2) '' {p | p.degree < q})
      (dividedDifference s v r ^ 2 / ∑ i ∈ s, Lagrange.nodalWeight s v i ^ 2 / u i)
```

with `dividedDifference_eq_coeff_interpolate` (the coefficient of $X^q$ of the interpolant),
`dividedDifference_eval_eq_coeff` and `dividedDifference_eval_eq_zero` (on values of $p$ with
$\deg p \le q$, resp. $< q$). The last is Lemma 9; the one before is the content of Lemma 8 and
of Lemma 9's proof. Also public, as a general Lagrange fact:
`nodalWeight_map (f : F →+* K) : Lagrange.nodalWeight s (fun j => f (v j)) i =
f (Lagrange.nodalWeight s v i)` (used with `algebraMap ℝ 𝕜`). The count is `#s = q + 1` with
`p.degree < q` (§5.3: no truncated
subtraction; Mathlib's `Lagrange.coeff_eq_sum` uses `#s - 1`). §5.3 row (question 1):
"divided difference | `dividedDifference s v r` | `dividedDifference_eq_coeff_interpolate`".

**Discrete minimax duality** (`Polynomial/Chebyshev/ResidualMinimax.lean`, new):

```lean
theorem exists_residualMinimax_sq_le_sum_mul_norm_sq (𝕜 : Type*) [RCLike 𝕜] {s : Finset ℝ}
    (hs : s.Nonempty) (q : ℕ) :
    ∃ w : ℝ → ℝ, (∀ x ∈ s, 0 ≤ w x) ∧ ∑ x ∈ s, w x = 1 ∧
      ∀ p : 𝕜[X], p.degree ≤ q → p.eval 0 = 1 →
        residualMinimax s q ^ 2 ≤ ∑ x ∈ s, w x * ‖p.eval (x : 𝕜)‖ ^ 2
```

The saddle form, which is what both Greenbaum proofs apply. The reverse inequality
($\sum_x w_x\lvert p(x)\rvert^2 \le \max_x\lvert p(x)\rvert^2$) is one line and not stated. Over
$\Bbbk[X]$ because CG and GMRES produce residual polynomials over $\Bbbk$
(`exists_sub_cgIterate_eq_aeval`, `exists_sub_mulVec_gmresIterate_eq_aeval`). No `0 ∉ s`: with
$0 \in s$ the value is $1$ and $\delta_0$ works.

**A vector with prescribed spectral weights** (`Matrix/Functions/Polynomial.lean`, addition):

```lean
theorem _root_.Matrix.IsHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {s : Finset ℝ} (hs : spectrum ℝ A = ↑s)
    {w : ℝ → ℝ} (hw : ∀ x ∈ s, 0 ≤ w x) :
    ∃ v : n → 𝕜, ∀ (g : ℝ → ℝ) (p r : 𝕜[X]),
      star (aeval A p *ᵥ v) ⬝ᵥ (cfc g A *ᵥ (aeval A r *ᵥ v)) =
        ∑ x ∈ s, ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜))
```

This is "the reduction of $\mathbf{b}$ to $q + 1$ eigenvectors": weights vanishing off
$T \subseteq s$. The sesquilinear form serves Euclidean ($g = 1$), $\mathbf{A}$- ($g =
\mathrm{id}$) and $\nu(\mathbf{A})$-norms and the Galerkin inner products ($p = X^k$). The
spectrum enters as `hs : spectrum ℝ A = ↑s` (no proof term in the statement; `s` from
`Set.Finite.exists_finset_coe`), and no eigenvector is quantified (§5.2).

**Private to `Optimality.lean`**, each with signature and docstring in the skeleton: the three
parts of the exact ratio (§5.3), the assembly `exists_re_quadForm_eq_mul_sum` (the ratio
(15)), `exists_mul_sq_div_le_sum` (the weighting), `exists_mul_sq_le_rpow` (the shift for
$\mathbf{A}^\alpha$). The three parts take the spectral weights of $\mathbf{b}$ as the raw
hypothesis `hb` (the Matrix lemma's conclusion over $T$); that repetition is why question 3 asks
about a predicate.

## 4. The sources in the library's vocabulary

| Source | Library |
|---|---|
| $\min_{p}\max_{\lambda\in\sigma(\mathbf{A})}\lvert p(\lambda)\rvert$ | `residualMinimax (spectrum ℝ A) q` (K1, L11) |
| Greenbaum's worst case: $\max_{\mathbf{b}}$ of the error ratio | `IsGreatest (ratio '' {xs \| xs ≠ x₀}) (residualMinimax …)`, from the equation form |
| dual weights on the spectrum | `w` with `∀ x ∈ s, 0 ≤ w x`, `∑ x ∈ s, w x = 1`; Mathlib's `stdSimplex` inside the proof only |
| $\mathbf{b} = \sum_i \hat b_i\mathbf{w}_i$, $\lvert\hat b_i\rvert^2$ prescribed, (14) | `exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum` with weights supported on $T$ |
| $\omega_i = \prod_{k\ne i}(\lambda_i - \lambda_k)$ | `(Lagrange.nodalWeight T id x)⁻¹` |
| $f[\lambda_1, \dots, \lambda_{m+1}]$ | `dividedDifference T id f` |
| Lemma 8 ($\pi_m(\lambda_i) = g_i\omega_i/G$) | Galerkin condition of shifted CG and `exists_eq_mul_nodalWeight`: $w\pi = cW$ on $T$ |
| Lemma 9 | `isLeast_sum_mul_sq_sub_eval` |
| $h_i$, $\varphi_{i,s} = \lambda_i^\alpha/(\lambda_i + s)$, ratio (15) | private `exists_re_quadForm_eq_mul_sum`, weights `h`, `ν x / (x + s)` |
| the limits $\delta \to 0$ and $s \to \infty$ | explicit choices: $\delta = \eta/(1 + \sum_T\varphi)$; $s = 0$ for $\alpha \le 1/2$, $s = a'/(1 - \theta)$ with $\theta = (1 - \eta/2)^2$ otherwise |
| "at least $m + 1$ distinct eigenvalues" | `q + 1 ≤ (spectrum ℝ A).ncard` |

## 5. Proof plans

Sizes are lines of proof with docstrings. "Easy", "medium", "hard" as in K2.

### 5.1 KB1: divided differences and discrete minimax duality (Polynomial layer)

**Divided differences** (about 220 lines; easy to medium). The bridge and `_eval_eq_coeff`:
`Lagrange.coeff_eq_sum` (for the interpolant, `Lagrange.degree_interpolate_lt`,
`Lagrange.eval_interpolate_at_node`) and `Lagrange.nodalWeight` unfolded; 40.
`exists_eq_mul_nodalWeight`: $c = \sum_i z_i v_i^q$; $d = z - cW$ is orthogonal to degrees below
$q$ (hypothesis, `_eq_zero`) and to $X^q$ (`_eq_coeff`: $\sum_i W_i v_i^q = 1$), hence to all
degrees up to $q$; `Lagrange.basis s v j` (`Lagrange.eval_basis_self`, `eval_basis_of_ne`,
`natDegree_basis`) gives $d_j = 0$; 50. Lemma 9: $r[s] = (r - p)[s]$ and Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`, factors $\sqrt{u_i}(r_i - p(v_i))$ and $W_i/\sqrt{u_i}$);
attained by `Lagrange.interpolate s v (r - t W/u)`, $t = r[s]/\sum W^2/u$, of degree below $q$
since its divided difference vanishes (`Polynomial.degree_lt_iff_coeff_zero`); 90.

**Discrete minimax duality** (300 to 400 lines; medium), split as CONTRIBUTING §7 asks, with
two proof-local definitions on `ι = ↥s`:

```lean
private def residualValues (s : Finset ℝ) (q : ℕ) : Set (↥s → ℝ) :=
  {v | ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧ v = fun x : ↥s => p.eval (x : ℝ)}
private noncomputable def weightedResidualMin (s : Finset ℝ) (q : ℕ) (w : ↥s → ℝ) : ℝ :=
  ⨅ v : residualValues s q, ∑ i, w i * (v : ↥s → ℝ) i ^ 2
private theorem convex_residualValues (s : Finset ℝ) (q : ℕ) : Convex ℝ (residualValues s q)
private theorem isLUB_sum_mul_sq_stdSimplex {s : Finset ℝ} (hs : s.Nonempty) (v : ↥s → ℝ) :
    IsLUB ((fun w : ↥s → ℝ => ∑ i, w i * v i ^ 2) '' stdSimplex ℝ ↥s) (⨆ i, v i ^ 2)
private theorem isGLB_iSup_sq_residualValues {s : Finset ℝ} (hs : s.Nonempty) (q : ℕ) :
    IsGLB ((fun v : ↥s → ℝ => ⨆ i, v i ^ 2) '' residualValues s q) (residualMinimax s q ^ 2)
private theorem isLUB_weightedResidualMin {s : Finset ℝ} (hs : s.Nonempty) (q : ℕ) :
    IsLUB (weightedResidualMin s q '' stdSimplex ℝ ↥s) (residualMinimax s q ^ 2)
private theorem exists_weightedResidualMin_eq {s : Finset ℝ} (hs : s.Nonempty) (q : ℕ) :
    ∃ w ∈ stdSimplex ℝ ↥s, weightedResidualMin s q w = residualMinimax s q ^ 2
private theorem exists_abs_eval_le_norm_eval {𝕜 : Type*} [RCLike 𝕜] {q : ℕ} {p : 𝕜[X]}
    (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    ∃ p' : ℝ[X], p'.degree ≤ q ∧ p'.eval 0 = 1 ∧ ∀ x : ℝ, |p'.eval x| ≤ ‖p.eval (x : 𝕜)‖
```

Convexity: a convex combination of residual polynomials is one (30). The simplex supremum:
every value is at most the maximum, the vertex `Pi.single i 1` attains it (40). The infimum:
`Real.iInf` over the residual subtype, `Real.iSup` over `x ∈ s`, squaring monotone (60, the
fiddliest). Sion (`isLUB_weightedResidualMin`, 80): `Sion.minimax` with $X$ = the simplex
(`isCompact_stdSimplex`, `convex_stdSimplex`), $Y$ = `residualValues`,
$f(w, v) = -\sum_i w_i v_i^2$ (continuous in each variable, linear in $w$, concave in $v$,
`ConcaveOn.quasiconcaveOn`), and the negatives of the three previous facts as witnesses.
Attainment (50): `weightedResidualMin` is upper semicontinuous (an infimum of continuous
functions) and `UpperSemicontinuousOn.exists_isMaxOn`. Real part (40): $\sum_k
\operatorname{Re}(p_k)X^k$ (`Polynomial.eval_eq_sum_range`, `RCLike.abs_re_le_norm`). The theorem
(30): the maximiser extended by $0$ off $s$.

Fallback: separation (attain the minimax polynomial with `IsClosed.exists_infDist_eq_dist`,
separate $0$ from the convex hull of the signed extremal evaluations,
`geometric_hahn_banach_point_closed`, `Finset.mem_convexHull`, perturb). Same statement, about
300 lines.

### 5.2 KB2: Greenbaum's theorem for CG and MINRES

**The Matrix lemma** (120 to 150 lines; medium). For each $x \in s$ an index $i_x$ with
`hA.eigenvalues i_x = x` (`Matrix.IsHermitian.spectrum_eq_image_eigenvalue`), $\mathbf{u}_x$
that column of `hA.eigenvectorUnitary` (orthonormal across distinct $x$),
$\mathbf{v} = \sum_x\sqrt{w_x}\,\mathbf{u}_x$; $r(\mathbf{A})\mathbf{u}_x = r(x)\mathbf{u}_x$
and $g(\mathbf{A})\mathbf{u}_x = g(x)\mathbf{u}_x$
(`Matrix.IsHermitian.cfc_mulVec_of_mulVec_eq_smul`, `cfc_polynomial`); cross terms vanish.

**CG** (about 60 lines; easy). For $x_0$, take $s$ with `spectrum ℝ A = ↑s` (nonempty since
`[Nonempty n]`), the dual weights $w$ of KB1 with $\Bbbk$, the vector $\mathbf{e}$ with spectral
weights $w_x/x$ ($x > 0$, `Matrix.PosDef.spectrum_subset_Ioi` or the eigenvalue form), and
$\mathbf{x}_\star = \mathbf{x}_0 + \mathbf{e}$; $\mathbf{e} \ne \mathbf{0}$ since
$\|\mathbf{e}\|_{\mathbf{A}}^2 = \sum_x w_x = 1$ (the lemma with $g = \mathrm{id}$, $p = r = 1$,
`cfc_id'`). The CG error is $p(\mathbf{A})\mathbf{e}$ (`exists_sub_cgIterate_eq_aeval` with
$\mathbf{b} = \mathbf{A}\mathbf{x}_\star$), of squared $\mathbf{A}$-norm
$\sum_x w_x\lvert p(x)\rvert^2 \ge E^2$; `le_antisymm` with
`Matrix.PosDef.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul`. `IsGreatest`: membership
from the equation, upper bound from the K1 bound divided by the positive denominator; 20.

**MINRES** (about 60 lines; easy). Same with $g = 1$ and weights $w$ for $\mathbf{r}_0$,
$\mathbf{b} = \mathbf{A}\mathbf{x}_0 + \mathbf{r}_0$, `exists_sub_mulVec_gmresIterate_eq_aeval`,
`EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct`, square roots
(`Real.sqrt_le_sqrt`, `sq_le_sq'`), and
`Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul`. `IsGreatest`: 20.

### 5.3 KB3: Theorem 2

**Step 1, the exact ratio** (250 to 350 lines once split; the hard part). Three named
lemmas, then a 60-line assembly. All take $\mathbf{A}$ positive definite, eigenvalues
`hTA : ↑T ⊆ spectrum ℝ A`, and the spectral weights of $\mathbf{b}$ on $T$:

```lean
(hb : ∀ (g : ℝ → ℝ) (p r : 𝕜[X]),
  star (aeval A p *ᵥ b) ⬝ᵥ (cfc g A *ᵥ (aeval A r *ᵥ b)) =
    ∑ x ∈ T, ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜)))

-- (a) the residual polynomial of shifted CG, the content of Lemma 8 (about 120 lines)
private theorem exists_mul_eval_eq_mul_nodalWeight … (hT : #T = q + 1)
    (hw : ∀ x ∈ T, 0 < w x) (hb) {s : ℝ} (hs : 0 ≤ s) {p : 𝕜[X]} (hp : p.degree < q)
    (hpL : lanczosFA A (fun x => (x + s)⁻¹) b q = aeval A p *ᵥ b) :
    ∃ c : 𝕜, c ≠ 0 ∧ ∀ x ∈ T, (w x : 𝕜) * (1 - (X + C (s : 𝕜)) * p).eval (x : 𝕜) =
      c * ((Lagrange.nodalWeight T (id : ℝ → ℝ) x : ℝ) : 𝕜)
-- (b) the error of any Krylov vector in spectral weights (about 60 lines)
private theorem re_quadForm_cfc_inv_add_mulVec_sub_aeval_mulVec_eq … (hb) (ν : ℝ → ℝ)
    {s : ℝ} (hs : 0 ≤ s) (p : 𝕜[X]) :
    RCLike.re (quadForm (cfc ν A) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - aeval A p *ᵥ b)) =
      ∑ x ∈ T, w x * ν x * ‖(((x + s)⁻¹ : ℝ) : 𝕜) - p.eval (x : 𝕜)‖ ^ 2
-- (c) the comparison vector from Lemma 9 (about 70 lines)
private theorem exists_mem_krylovSpace_re_quadForm_eq … (hT : #T = q + 1)
    (hw : ∀ x ∈ T, 0 < w x) (hν : ∀ x ∈ T, 0 < ν x) (hb) {s : ℝ} (hs : 0 ≤ s)
    {p₀ : 𝕜[X]} (hp₀ : p₀.degree < q) {c : 𝕜} {e : ℝ → ℝ}
    (he : ∀ x ∈ T, (((x + s)⁻¹ : ℝ) : 𝕜) - p₀.eval (x : 𝕜) = c * (e x : 𝕜)) :
    ∃ y ∈ krylovSpace A b q,
      RCLike.re (quadForm (cfc ν A) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - y)) =
        ‖c‖ ^ 2 * (dividedDifference T id e ^ 2 /
          ∑ x ∈ T, Lagrange.nodalWeight T id x ^ 2 / (w x * ν x))
```

(a): `lanczosFA_inv_add_eq_cgIterate` and
`Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero` for
$\mathbf{A} + s\mathbf{I}$ with the zero start; `krylovSpace_add_smul_one`,
`pow_mulVec_mem_krylovSpace` give $\langle\mathbf{A}^k\mathbf{b}, \pi(\mathbf{A})\mathbf{b}\rangle
= 0$ for $k < q$, $\pi = 1 - (X + s)p$ ($(\mathbf{A} + s\mathbf{I})$ times the error, `cfc_mul`
on the spectrum); `hb` with $g = 1$ makes it $\sum_T w\pi r = 0$ for $\deg r < q$;
`exists_eq_mul_nodalWeight` with nodes `algebraMap ℝ 𝕜` and `nodalWeight_map`; $c \ne 0$ since
$\pi(-s) = 1$, $-s \notin T$, and `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`.
(b): $f = L$ on the spectrum for the real interpolant $L$
(`Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq`) and `hb` with $g = \nu$, $p = r = L - p$.
With (a) and $w = W^2/(h\nu)$ it reads $\lvert c\rvert^2\sum_T h\varphi^2$, $\varphi = \nu/(x + s)$.
(c): `isLeast_sum_mul_sq_sub_eval` with weights $w\nu$ gives a real $\tilde p$;
$\mathbf{y} = (p_0 + c\tilde p)(\mathbf{A})\mathbf{b}$ (`Polynomial.map (algebraMap ℝ 𝕜)`) and (b).
Assembly (`exists_re_quadForm_eq_mul_sum`): $W$ the nodal weights, $u = W^2/h$, $w = u/\nu$ on
$T$ and $0$ off it, $\mathbf{b}$ from the Matrix lemma; (a), (b), and (c) with $p_0 = p$ and
$e = W\varphi/u$, since $e[T] = \sum_T h\varphi$ and $\sum_T W^2/u = \sum_T h$.
$C = \lvert c\rvert^2$.

**Step 2, the weighting** (private `exists_mul_sq_div_le_sum`, about 50 lines; easy).
$h = 1/\varphi$ at $x_1, x_2$, $h = \delta = \eta/(1 + \sum_T\varphi)$ elsewhere. Then
$\sum_T h\varphi^2 \ge \varphi_1 + \varphi_2$, $\sum_T h \ge 1/\varphi_1 + 1/\varphi_2$,
$\sum_T h\varphi \le 2 + \eta$, and
$(1 - \eta)^2\frac{(\varphi_1 + \varphi_2)^2}{4\varphi_1\varphi_2}\cdot
\frac{(2 + \eta)^2}{1/\varphi_1 + 1/\varphi_2} = (1 - \eta)^2(2 + \eta)^2\frac{\varphi_1 +
\varphi_2}{4} \le \varphi_1 + \varphi_2$ because $(1 - \eta)(2 + \eta) \le 2$.

**Step 3, the fixed-shift theorem** (about 70 lines; easy). If $x_1 = x_2$ the factor is $1$:
take $\mathbf{b}$ from any pair $x_1 \ne x_3$ (it exists, $q + 1 \ge 2$) for the positive error,
and $\mathbf{y}$ = the Lanczos-FA vector itself, since $(1 - \eta)^2 \le 1$.
Otherwise `Finset.exists_subsuperset_card_eq` gives $T$ with
$\{x_1, x_2\} \subseteq T \subseteq S$, $\#T = q + 1$ (`Set.ncard_coe_finset`), then Steps 2
and 1; the error is $C\sum_T h\varphi^2 > 0$; and
$(R + 1)^2/(4R) = (\varphi_1 + \varphi_2)^2/(4\varphi_1\varphi_2)$ with the pair form of the
statement after multiplying through by $(x_1 + s)(x_2 + s)$ (`field_simp`).

**Step 4, the shift for $\mathbf{A}^\alpha$** (private `exists_mul_sq_le_rpow`, about 80 lines;
medium, real powers). With $\psi(R) = (R + 1)^2/(4R)$: $\psi(1/R) = \psi(R)$;
$\psi(\kappa^E) = (\tfrac12(\kappa^{E/2} + \kappa^{-E/2}))^2$ (`Real.rpow_add`, `Real.rpow_neg`,
`Real.rpow_natCast`); $\psi(\vartheta K) \ge \vartheta\psi(K)$ for $0 < \vartheta \le 1$ (it is
$\vartheta K + 1 \ge \vartheta(K + 1)$ squared). For $\alpha \le 1/2$, $s = 0$ and the pair ratio
is $(a'/a)^{1 - \alpha} = \kappa^E$ exactly (`Real.div_rpow`, `Real.rpow_sub_one`). For
$\alpha > 1/2$, $s = a'/(1 - \theta)$ makes $s/(a' + s) = 1/(2 - \theta) \ge \theta$, so the
inverse pair ratio $\kappa^\alpha\frac{a + s}{a' + s}$ lies in $[\theta\kappa^\alpha,
\kappa^\alpha]$.

**Step 5, Theorem 2** (about 70 lines; easy to medium). $a = $ `eigenvalue A k` with
$k + 1 = $ `Fintype.card n` and $a' = $ `eigenvalue A 0`
(`Matrix.IsHermitian.eigenvalue_mem_spectrum`, both positive), $a < a'$ from two distinct
eigenvalues
(`Matrix.IsHermitian.spectrum_subset_iff`), $\kappa = a'/a$
(`Matrix.PosDef.pseudoConditionNumber_eq`); Step 4 with $\theta = (1 - \eta/2)^2$; Step 3 with
$\nu(x) = x^\alpha$, $\eta/2$, $x_1 = a$, $x_2 = a'$; `CFC.rpow_eq_cfc_real` (with
`hA.posSemidef.nonneg`) to turn `cfc (· ^ α) A` into `A ^ α`; and
$(1 - \eta/2)^4 \ge (1 - \eta)^2$.

**Step 6, CG** (about 40 lines; easy). Step 3 with $\nu = 1$, $s = 0$, the extreme
eigenvalues (factor $(a + a')^2/(4aa') = (\tfrac12(\sqrt\kappa + 1/\sqrt\kappa))^2$),
`Matrix.IsHermitian.lanczosFA_inv_eq_cgIterate` (after `add_zero` under the binder),
$\mathbf{x}_\star = \mathbf{A}^{-1}\mathbf{b}$ = `cfc (·⁻¹) A *ᵥ b` (`Matrix.PosDef.inv_eq_cfc`),
`cfc_const_one`, `EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct` and square roots.

## 6. Files, imports, placement, sizes

| File | Defs + theorems | Skeleton lines | Expected when proved |
|---|---|---|---|
| `Polynomial/Interpolation/DividedDifference.lean` (new) | 1 + 6 | 130 | 230 |
| `Polynomial/Chebyshev/ResidualMinimax.lean` (new) | 0 + 1, 2 + 6 private | 120 | 300 to 400 |
| `Matrix/Functions/Polynomial.lean` (addition) | 0 + 1 | 40 | +120 to 150 |
| `Krylov/LinearSystems/WorstCase.lean` (addition) | 0 + 4 | 110 | +200 (463 to about 660) |
| `Krylov/Functions/Optimality.lean` (new) | 0 + 3, 6 private | 320 | 700 to 800 |
| **K2b** | **1 + 15 public** | | **about 1500 to 1700** |

Imports ("uses" is a direct import): DividedDifference uses Mathlib's `LinearAlgebra.Lagrange`;
ResidualMinimax uses `Polynomial/Chebyshev/Residual`, Mathlib's `Analysis.Convex.StdSimplex`,
`Topology.Sion`; WorstCase gains ResidualMinimax; Optimality uses `Krylov/Functions/NearOptimality`
(its docstrings cite the upper bounds), `Matrix/Functions/Polynomial`,
`Matrix/Pseudoinverse/ConditionNumber`, DividedDifference. No cycle: Polynomial files import only
Mathlib and Polynomial; Krylov imports both.

**Placement** (§8 item 5):

| Declaration | Home | Reason |
|---|---|---|
| `dividedDifference`, its lemmas, Lemma 9 | `Polynomial/Interpolation/DividedDifference.lean` (new) | interpolation algebra on finite nodes, the topic map's `Interpolation/`; a definition, so not ForMathlib (question 1) |
| `exists_residualMinimax_sq_le_sum_mul_norm_sq` | `Polynomial/Chebyshev/ResidualMinimax.lean` (new) | decided (coordinator, 2026-10-17): the residual minimax value on finite sets, a file importing `Residual.lean`; the definition `residualMinimax` stays in `Residual.lean`, so Mathlib's Sion file never reaches the CG import chain. The K1 note's file table does not list this file, so it needs no amendment |
| `nodalWeight_map` | DividedDifference | a general Lagrange fact, next to its only use in the Polynomial layer; an upstream candidate |
| `Matrix.IsHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum` | `Matrix/Functions/Polynomial.lean` | polynomials and functions of one Hermitian matrix on a vector; no Krylov content |
| Greenbaum CG and MINRES (4) | `Krylov/LinearSystems/WorstCase.lean` | the K1 note's planned home |
| Theorem 2, general form, CG corollary | `Krylov/Functions/Optimality.lean` (new) | `NearOptimality.lean` (596) would pass 1000; the K2 note's split by statement; the CG corollary sits with its proof, as the CG upper corollaries sit in NearOptimality |

No placement flag is open.

## 7. Checkpoints and order

One proof agent per file, at most two at once (§11).

1. **KB1, Polynomial layer** (550 to 650 lines): DividedDifference and ResidualMinimax, independent
   of each other and of everything in Krylov; two agents may run in parallel. Commit.
2. **KB2a, the Matrix lemma** (120 to 150): the addition to `Matrix/Functions/Polynomial.lean`.
   Needed by KB2 and KB3; may run in parallel with KB1.
3. **KB2, Greenbaum** (about 200): the WorstCase additions, after KB1 (ResidualMinimax) and KB2a.
   Commit; the maintainer's "spectrum optimal bound is sharp" is answered here.
4. **KB3a, the fixed shift** (450 to 550): Optimality Steps 1 to 3 and 6 (the exact ratio, the
   weighting, the general-$\nu$ theorem, the CG corollary), after DividedDifference and KB2a;
   independent of KB2. Commit: the matrix argument of Theorem 2 can be reviewed here.
5. **KB3b, Theorem 2** (about 150): Steps 4 and 5, the real-power algebra. Commit.

Along with the last commit, the docstring follow-ups of §10 and the bookkeeping (ledger, status,
references, §5.3 row, result ids).

## 8. The hard parts, honestly

- **KB3 Step 1, the exact ratio** (250 to 350 lines in four lemmas): not deep but long. It threads
  the
  Lanczos-FA/CG identity, the Galerkin condition across the shift, the spectral-weights lemma,
  divided differences over $\Bbbk$ with real nodes, root counting, the interpolant of $f$ on the
  spectrum and Lemma 9, with $\Bbbk$-valued polynomials beside real weights. The likeliest place
  for a private statement to change; lemma (a) is the one to prove first.
- **The Sion bookkeeping in KB1**: explicit `IsLUB`/`IsGLB` witnesses, quasiconvexity on sets,
  and $\inf_v\max_x v_x^2 = $ `residualMinimax s q ^ 2` through `Real.iInf`/`Real.iSup` over a
  subtype, as in K1's `…_le_residualMinimax_sq_mul`. Fallback in §5.1.
- **The real powers of KB3 Step 4**: signed exponents, the split at $\alpha = 1/2$, the
  statement's `pseudoConditionNumber A ^ (max α (1 - α) / 2)`. Fiddly, short.
- Nothing needs a new interface, a Mathlib gap filled, or a limit.

## 9. Mathlib search and records

Used: `Sion.minimax` (`Mathlib/Topology/Sion.lean`; the inf-sup form `Sion.minimax'` needs a
complete linear order, so the `IsGLB` form is the one for ℝ), `stdSimplex`,
`isCompact_stdSimplex`, `convex_stdSimplex`, `UpperSemicontinuousOn.exists_isMaxOn`,
`Lagrange.coeff_eq_sum`, `Lagrange.nodalWeight` (`_ne_zero`), `Lagrange.basis`,
`Lagrange.interpolate`, `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`,
`Finset.exists_subsuperset_card_eq`, `Set.ncard_coe_finset`. Present, not needed:
`ProperCone.hyperplane_separation` (Farkas), `geometric_hahn_banach_point_closed`. Searched,
none: divided differences beyond `Lagrange.coeff_eq_sum`; weighted polynomial least squares on
finite nodes; alternation, equioscillation or Haar systems; linear-programming duality;
worst-case Krylov results; vectors with a prescribed spectral measure.
`docs/design/Mathlib-deviations.md`: nothing (`dividedDifference` is an addition with a bridge).
`docs/constants.toml`: nothing.

## 10. Literature, result ids, docstring follow-ups

New keys, added before citing:

```bibtex
@article{Greenbaum1979,
  author = {Greenbaum, Anne},
  title = {Comparison of splittings used with the conjugate gradient algorithm},
  journal = {Numerische Mathematik},
  volume = {33}, number = {2}, pages = {181--193}, year = {1979}
}
@article{GreenbaumGurvits1994,
  author = {Greenbaum, Anne and Gurvits, Leonid},
  title = {Max-min properties of matrix factor norms},
  journal = {SIAM Journal on Scientific Computing},
  volume = {15}, number = {2}, pages = {348--358}, year = {1994}
}
```

`Greenbaum1979` is from the paper's reference list ([Gre79], its Remark 7);
`GreenbaumGurvits1994` is from memory and must be checked against the article. Locators to
verify: the worst-case theorem in each; `Greenbaum1997` §3.1; `Higham2008` (1.10), locator to
verify (divided difference as leading coefficient, as the paper cites it). The paper's Remark 7
also points to Amsel, Chen, Greenbaum, Musco and Musco 2024, Appendix C; `references.bib` has no
key for it, so it is not cited (add the key first if the maintainer wants the pointer).
`ChenPersson2026` locators: Theorem 2
and its proof, Remarks 3 and 7, Lemmas 8 and 9, (13) to (16). Result ids:
`cg-spectrum-minimax-sharp`, `minres-spectrum-minimax-sharp` (the style of WorstCase's
`cg-chebyshev-sharp`),
`lanczos-fa-near-optimality-lower-bound` (K2's id).

Docstring follow-ups, last commit: `CG.lean` and `MINRES.lean` (the minimax bounds' "stage K2b"
becomes the new names); `WorstCase.lean` (module docstring: Greenbaum joins the main results);
`NearOptimality.lean` (module docstring points to `NLAlib.Krylov.Functions.Optimality`);
`Residual.lean` (one line pointing to the duality); `Krylov-Functions.md` §6 and
`Krylov-LinearSystems.md` L11 (one line each).

## 11. Alternatives considered

| Alternative | Verdict |
|---|---|
| The paper's route through Ritz values and uniqueness of the monic orthogonal polynomial | replaced by the Galerkin condition and `exists_eq_mul_nodalWeight` (Finding 1); Gauss quadrature likewise unused |
| Equioscillation on a finite set for Greenbaum | false for MINRES in general (no Haar system across $0$), longer for CG |
| A predicate `HasSpectralWeights A v w s` | question 3: K2b's private lemmas repeat the raw hypothesis `hb` three times |
| Limits through filters ($\delta \to 0$, $s \to \infty$) | explicit choices; no filter anywhere |
| Theorem 2 in `NearOptimality.lean` | over the 1000-line budget; split by statement |
| The duality as an equation $E^2 = \max_w\min_p\sum_x w_x\lvert p(x)\rvert^2$ | the saddle form is what both consumers apply |

## 12. Consumers

The duality: KB2; later worst cases for PCG and PMINRES through their split forms. The
spectral-weights lemma: KB2, KB3; later lower bounds for Lanczos and block methods (K4, K5) and
SLQ examples (K7). Divided differences and Lemma 9: KB3; later derivative interpolation error
(`docs/PORT_POLYNOMIAL.md` Poly5). The fixed-shift theorem: Theorem 2, the CG corollary, a future
rational-function lower bound.

## 13. Questions for the maintainer

1. **A named divided difference.** Recommended: `NLAlib.dividedDifference s v r` in
   `Polynomial/Interpolation/DividedDifference.lean`, a new §5.3 row with the bridge
   `dividedDifference_eq_coeff_interpolate` to Mathlib's `Lagrange`. The alternative is to write
   `∑ i ∈ s, Lagrange.nodalWeight s v i * r i` inline (it occurs in three statements) and put the
   lemmas in `ForMathlib/LinearAlgebra/Lagrange.lean` as upstream candidates. The name is
   vocabulary, hence the question; the home is cheap to move.
2. **Greenbaum for GMRES with normal matrices** (Greenbaum–Gurvits: worst-case GMRES equals the
   minimax over the complex spectrum). Not in K2b: it needs a minimax value over complex points
   and complex residual polynomials, a second definition beside the real `residualMinimax`
   (or a generalisation of it to `Set 𝕜`). Recommended: defer until a consumer appears; the
   duality proof carries over unchanged.
3. **A predicate for prescribed spectral weights.** The three private parts of KB3 Step 1 take
   the Matrix lemma's conclusion as a raw hypothesis `hb`; making part (a) public (Lemma 8 is
   reusable for K4 and K7) would repeat it in public statements, which §1.2 turns into an
   interface `HasSpectralWeights A b w T` (the sesquilinear identity, with a constructor from the
   Matrix lemma). Recommended: keep the three parts private in K2b and decide the predicate with
   K4 or K7, its first public consumer.
