# Lanczos with full reorthogonalization in finite precision

2026-11-06. Design note; **status: all 51 statements proved and in `NLAlib` (§8)**. Branch `design/lanczos-reorth` from `origin/main` @
`a08339af` (PR #58). Decision sheet: harness `state/decisions/LANCZOS-REORTH.json`
(ids FR1–FR9 below).

The maintainer asked for Lanczos with **full** reorthogonalization (every new Lanczos vector is
orthogonalized against *all* previous ones), stated abstractly through a guarantee on the
orthogonalization scheme, inside the model of computation, and asked what stability can be
proved. Partial or selective reorthogonalization and CG with reorthogonalization are not part of
this stage.

Label convention: **known** means a published result (citation; "locator to verify" when the
theorem number has not been checked against the text); **planned** means a statement this note
proposes to prove here, with a proof sketch; **conjectured** means we do not have a proof route.
Constants written $c_\bullet$ are fixed by the proof and recorded in `docs/constants.toml`; the
leading-order forms given here are proof-sketch values, not claims.

## Summary

* **Modular, settled at the level main already uses for products** (FR1). The shared rounded
  Lanczos proofs on main take the matrix–vector product as a step-indexed routine family
  `mv : ℕ → Builder P ι ℕ ℕ Unit` with a certificate `∀ t, IsMatvecRoutine …`
  (`Computation/MatvecRoutine.lean`), while each registered tree is concrete. The orthogonalization
  step works the same way: a routine family `orth : ℕ → Builder P ι ℕ ℕ Unit` with a certificate
  `∀ t, IsOrthRoutine …`. Every Lanczos stability theorem depends only on the certificate's
  parameters $(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$. One concrete instance is proved
  in this stage: **CGS2**, two classical Gram–Schmidt passes built from main's `dot`/`gemv`/`axpy`,
  whose rounding lemmas are already on main. The registered trees use CGS2.
* **Contract** (FR2). For a computed basis $\mathbf V$ with $\|\mathbf V^{\mathsf T}\mathbf V-\mathbf I\|_2\le\eta_0$
  and input $\mathbf w$, the routine returns coefficients $\mathbf h$ and $\mathbf w'$ with
  $$\mathbf w=\mathbf V\mathbf h+\mathbf w'+\mathbf f,\quad \|\mathbf f\|\le\varepsilon_2\|\mathbf w\|,\qquad
  \|\mathbf V^{\mathsf T}\mathbf w'\|\le\varepsilon_1\|\mathbf w'\|+\varepsilon_3\|\mathbf w\|.$$
  The $\varepsilon_3$ term carries the "twice is enough" idea: it is first order ($\approx\eta_0+c\,u$)
  for one CGS pass and second order ($\approx(\eta_0+c\,u)^2$) for two passes. Nothing in the
  contract mentions breakdown. Admissibility ("$\mathbf w$ is not numerically in
  $\operatorname{range}\mathbf V$", $\|\mathbf w'\|\ge\tau\|\mathbf w\|$) is a property of the
  computed run that can be read off the outputs, and the Lanczos analysis uses it.
* **Model of computation.** Main's `Prog` is enough. CGS2 needs loops whose bound is the loop
  index (`forRange (.var j + 1)`, already used by `trsvLower` and `gramSchmidtProg`), `dot`, `gemv`
  on a column block, `axpy`, `nrm2`, `rscl`, `ite`. No extension is needed for this stage.
  A QR-kernel instance would need COMPDYN's `kcall`, which is not on main (later, §2.5).
* **Stability menu** (§3), ranked by value/cost. (S1) the perturbed Lanczos relation, with the
  discarded reorthogonalization coefficients bounded by an induction that uses symmetry; (S2)
  $\|\mathbf V_{k+1}^{\mathsf T}\mathbf V_{k+1}-\mathbf I\|_F\le\sqrt{3(k+1)}\,\mu$ on the admissible
  prefix; (S3) an **$n\times n$ symmetric backward model**: $\mathbf T_k$ is exactly the Lanczos
  tridiagonal of $(\mathbf A+\mathbf E,\tilde{\mathbf b})$ with $\|\mathbf E\|_F=O(k\mu\|\mathbf A\|)$,
  so no dilation is needed; (S4) consequences: interlacing up to $\|\mathbf E\|$, converged Ritz
  values are not duplicated (a residual-gated count, not a consequence of interlacing alone), Ritz
  residuals, transfer of Kaniel–Paige–Saad and of Gauss quadrature. All are known in substance
  (Paige 1970, the original analysis of Lanczos with reorthogonalization; Simon 1984;
  Giraud–Langou–Rozložník–van den Eshof 2005; Kahan–Parlett–Jiang 1982). The explicit theorems with constants, in this contract form, are planned. Forward
  statements about $\mathcal K_k(\mathbf A,\mathbf b)$ or about the exact $\mathbf T_k(\mathbf A,\mathbf b)$
  are out of reach because they are false in general (§3.6).
* **First stage**: 48 statements (S 27, M 14, L 5, H 2), §4.
* **Review.** Fable review 2026-11-06 (`reports/Review-Fable-LanczosReorth-Design.md`), approve with
  fixes; all findings applied (§6).

## 0. What main already has (reused, not re-derived)

| Piece | Where (origin/main) | Used for |
|---|---|---|
| Scalar contract `IsRelErrSem`, `AddsZeroExactly`, `roundingFactor` (γ), `IsRoundingProduct` | `Computation/Contract.lean`, `Computation/Rounding.lean` | every rounded step |
| Kernel rounding: `IsRelErrSem.exec_dot_abs_sum_mul_sub_le`, `exec_axpy`, `exec_gemv_abs_mulVec_sub_le`, `exec_gemv_eq_add_mulVec`, `exec_rscl`, normalization (`NormalizationErrors.lean`) | `Computation/BLAS/RoundingErrors.lean` | the CGS2 pass lemma (C3) |
| Routine certificate `IsMatvecRoutine`, `ExecutionComposable`, block-write frames | `Computation/MatvecRoutine.lean`, `ScalarFrames.lean` | template for `IsOrthRoutine` |
| Plain Lanczos programs `lanczosProg`, `lanczosOracleProg`, targets `StoredEntriesLanczos`, `MatrixFreeLanczos`, rounded execution `LanczosImplementation.exec_rounded_compiled(_backward)` with `lanczosImplementationRoundoffBound N u = 16(N+1)²u` | `Krylov/Processes/Lanczos*` | the FRO program is that body plus one `orth` call and one stored norm; the shared phase proofs are reused |
| `LanczosData` (generic symmetric three-term data): `mul_basis`, `residual`, `mulVec_basis_mulVec_sub_smul` | `Krylov/FinitePrecision/LanczosData.lean` | the perturbed relation (S1), Ritz residual identity |
| `LanczosRun`, Paige, dilation backward model `400q³ε‖A‖`/`1000q²ε‖A‖` | `Krylov/FinitePrecision/*` | the baseline the FRO results are compared with; not consumed |
| `lanczosState_eq_of_orthonormal_recurrence` | `Krylov/Processes/LanczosRecurrence.lean` | exact Lanczos on the backward model (E4) |
| `gramSchmidtQ`, `gramSchmidtR`, `IsQR`, `orthAgainst`, `mgsSweep`, `gramSchmidtProg` | `Matrix/Factorizations/GramSchmidt*.lean`, `QR.lean` | MGS2 instance later (`orthAgainst`); `gramSchmidtQ` only for the alternative QR route of E2 (§3.3) |
| `arnoldiState`, `mgsArnoldiHessenberg` | `Krylov/Processes/ArnoldiRecurrence.lean` | the exact FRO recurrence for non-symmetric input (A1) |
| Weyl `IsHermitian.abs_eigenvalue_sub_le`, Poincaré `eigenvalue_conjTranspose_mul_mul_le`, `eigenvalue_le_eigenvalue_conjTranspose_mul_mul`, residual `exists_abs_eigenvalue_sub_mul_norm_le`, Kaniel–Paige–Saad `eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le`, Kittaneh `frobNorm_cfc_sub_cfc_le`, Gauss quadrature (`Polynomial/Orthogonal/Gauss.lean`) | `Matrix/Spectral`, `Matrix/Perturbation`, `Krylov/Eigenvalues/Ritz.lean`, `Krylov/FinitePrecision` | the spectral consequences (S4) |

Main has no reorthogonalization code. The only mention is a remark in
`Krylov-CG-FinitePrecision-Bounds.md` that the CG experiment uses none. Older design branches
(`design/lanczos-fp`, `design/fp-toolkit`, COMPDYN, `research/cg-reorth`) were read as history only.
Nothing here depends on them.

## 1. The orthogonalization scheme: an abstract contract

### 1.1 The step and its guarantee

One step reduces $\mathbf w\in\mathbb R^n$ against the first $j$ columns of the computed basis
$\mathbf V=\mathbf V_j\in\mathbb R^{n\times j}$. It writes coefficients $\mathbf h\in\mathbb R^j$ and
overwrites $\mathbf w$ with $\mathbf w'$. **Normalization stays outside the scheme**: the Lanczos body
computes $\beta=\mathrm{nrm2}(\mathbf w')$ and $\mathbf v_{j+1}=\mathbf w'/\beta$ with the existing
`nrm2`/`rscl` code and its existing lemmas. This keeps the contract linear and identical for every
scheme. It also lets the plain-Lanczos normalization proofs on main carry over unchanged.

```lean
/-- The decoded guarantee of one orthogonalization step against a nearly orthonormal basis.
Every quantity is a decoded value of the run; the parameters may depend on n, j, u. -/
structure IsOrthErr {n j : ℕ} (η₀ ε₁ ε₂ ε₃ : ℝ) (V : Matrix (Fin n) (Fin j) ℝ)
    (w : Fin n → ℝ) (h : Fin j → ℝ) (w' : Fin n → ℝ) : Prop where
  /-- Residual (representation) relation. -/
  residual : specNorm (Vᵀ * V - 1) ≤ η₀ →
    ‖WithLp.toLp 2 (w - V *ᵥ h - w')‖ ≤ ε₂ * ‖WithLp.toLp 2 w‖
  /-- Local loss of orthogonality: relative to the output, plus a carried-over input term. -/
  orth : specNorm (Vᵀ * V - 1) ≤ η₀ →
    ‖WithLp.toLp 2 (Vᵀ *ᵥ w')‖ ≤ ε₁ * ‖WithLp.toLp 2 w'‖ + ε₃ * ‖WithLp.toLp 2 w‖
```

Why this shape (FR2):

* **No coefficient clause.** $\|\mathbf h\|$ follows from the residual relation:
  $\mathbf V^{\mathsf T}\mathbf V\mathbf h=\mathbf V^{\mathsf T}(\mathbf w-\mathbf w'-\mathbf f)$, so
  $\|\mathbf h\|\le(\|\mathbf V^{\mathsf T}\mathbf w\|+\|\mathbf V^{\mathsf T}\mathbf w'\|+\sqrt{1+\eta_0}\,\varepsilon_2\|\mathbf w\|)/(1-\eta_0)$
  (B4, planned, S). This is the bound the Lanczos analysis needs: it shows the coefficients are
  small when $\mathbf w$ is already nearly orthogonal to $\operatorname{range}\mathbf V$.
* **No admissibility inside.** The contract is unconditional apart from $\eta_0$. The quantity
  that admissibility controls, $\|\mathbf w\|/\|\mathbf w'\|$, appears only when the output is normalized:
  $\|\mathbf V^{\mathsf T}\mathbf w'/\|\mathbf w'\|\|\le\varepsilon_1+\varepsilon_3\|\mathbf w\|/\|\mathbf w'\|$ (B5).
  The run can therefore test admissibility from its own computed values. No hypothesis is placed
  on the unknown exact angle between $\mathbf w$ and $\operatorname{range}\mathbf V$.
* **Separating $\varepsilon_1$ and $\varepsilon_3$ is what tells the schemes apart.** Known
  results, in this form (locators to verify):

| scheme | $\varepsilon_1$ | $\varepsilon_3$ | consequence over $k$ steps | literature |
|---|---|---|---|---|
| CGS (one pass) | $c_1$ | $\approx\eta_0+c_1$ (first order) | $\mu_j\lesssim c_1+(\eta_j+c_1)/\tau_j$: orthogonality decays with the cancellation $1/\tau$ ($\tau_j$, the admissibility ratio of §1.2), $O(u\kappa^2)$ for QR | Giraud–Langou–Rozložník–van den Eshof 2005 Thm 1; Smoktunowicz–Barlow–Langou 2006 |
| **CGS2** | $\approx c_1$ | $\approx(\eta_0+c_1)^2$ | $O(c_1)$ per column whenever $\tau\gtrsim k c_1$ | Giraud et al. 2005 Thm 2 ($\|\mathbf I-\mathbf Q^{\mathsf T}\mathbf Q\|\le c\,mn^{3/2}u$ under $c'\,m^2n^3u\kappa<1$); Daniel–Gragg–Kaufman–Stewart 1976; Parlett 1998 §6.9 (Kahan's "twice is enough") |
| MGS2 | $\approx c_1$ | second order | as CGS2 | Giraud–Langou–Rozložník 2005 (CAMWA); Björck 1994 |
| Householder (implicit $\mathbf Q$) | $O(nu)$, any input | $0$ | $O(knu)$, no admissibility | Walker 1988; Drkošová–Greenbaum–Rozložník–Strakoš 1995; Higham 2002 Ch. 19 |
| block CGS2 / BCGS2 | as CGS2 under block conditions | — | later (block Lanczos) | Barlow–Smoktunowicz 2013; Carson–Lund–Rozložník–Thomas 2022 (survey) |

Here $c_1$ is the error coefficient of one rounded pass, $\approx\sqrt j\,(N+j+2)\,u$ (C3).

### 1.2 Composition over $k$ steps (B6, planned, S)

Write $\mathbf G_m=\mathbf V_m^{\mathsf T}\mathbf V_m$, $\mathbf g_j=\mathbf V_j^{\mathsf T}\mathbf v_{j+1}$,
$d_j=\|\mathbf v_{j+1}\|^2-1$. Adding one column gives exactly
$$\|\mathbf G_{m}-\mathbf I\|_F^2=\sum_{j<m}\bigl(2\|\mathbf g_j\|^2+d_j^2\bigr).$$
So if every column satisfies $\|\mathbf g_j\|,|d_j|\le\mu$, then
$\|\mathbf G_m-\mathbf I\|_2\le\|\mathbf G_m-\mathbf I\|_F\le\sqrt{3m}\,\mu$. The answer to "linear in $k$
or $O(\varepsilon)$ per column?" is: **$O(\mu)$ per column, $\sqrt k$ in Frobenius norm**. This holds
as long as the induction hypothesis $\sqrt{3m}\,\mu\le\eta_0$ survives. The spectral-norm recursion
$\eta_{m+1}\le\eta_m+\|\mathbf g_m\|+|d_m|$ would give the weaker linear bound; it is not used. The
recursion is closed because $\mu$ is absolute: $\mu\le\varepsilon_1+\varepsilon_3/\tau+\gamma_{\rm nrm}$
does not contain $\eta_m$ except through $\varepsilon_3(\eta_0)$. That is exactly why a
first-order $\varepsilon_3$ (one CGS pass) does not close without a $\tau$-dependent blow-up.

**Admissible prefix.** Let the program store $\nu_j=\mathrm{nrm2}(\mathbf z_j)$, the norm *before*
orthogonalization, next to $\beta_j=\mathrm{nrm2}(\mathbf z_j')$. Step $j$ is **$\tau$-admissible** if
$\tau\nu_j<\beta_j$ (strict, so $\beta_j\ne0$: exact breakdown $\nu_j=\beta_j=0$ is never admissible,
matching main's "the run ends at the first zero $\beta$"), a comparison of two stored outputs. The
analysis covers the steps up to the first non-admissible one, $k=$ `reorthSteps τ ν β q`. Steps are
numbered $j=1,\dots,k$ and produce $\mathbf v_2,\dots,\mathbf v_{k+1}$; Lean statements use the 0-based
`j < k`. This is Paige's stopping criterion in substance: Paige 1970 shows that Lanczos with
reorthogonalization needs a stopping criterion to obtain a priori error bounds (Paige 1970, locator
to verify); our $\tau$-test is that criterion in contract form. We state and prove our own version;
we do not follow his proof. Two facts justify reading $k$ off the outputs:

* (B7/D8, planned, S) if $\eta<1$ then $\mathbf V_{k+1}$ has full column rank, so the admissible
  prefix has $k+1\le n$ (with strict admissibility no extra hypothesis is needed). Full reorthogonalization "terminates" by step $n$
  for this reason alone.
* (F3) if the prefix stops at a non-admissible step, then $\beta_k<\tau\nu_k\le\tau c\|\mathbf A\|$.
  The computed space is then nearly invariant: every Ritz value is within $\tau c\|\mathbf A\|+\|\mathbf E\|$
  of an eigenvalue. This is the numerical form of a lucky breakdown.

**Closure as a fixed-point condition.** $\eta_0$ and $\tau$ are free parameters of the theorems. Put
$\mu(\eta_0,\tau):=\varepsilon_1(\eta_0)+\varepsilon_3(\eta_0)/\tau+c\,\gamma_{N+1}$; the hypothesis `hsmall` is
$$\sqrt{3(k+1)}\;\mu(\eta_0,\tau)\le\eta_0\le1/4 .$$
The induction closes because $\varepsilon_3$ takes the fixed certificate parameter $\eta_0$, not the running
$\eta_m$. A consistent CGS2 instance (sketch values, Fable review finding 2): allowing $\varepsilon_1\le1.1c_1$,
$\gamma_{N+4}\le c_1$, $\varepsilon_3/\tau\le c_1$ gives $\mu\le4c_1$; take $\eta_0:=4\sqrt{3(k+1)}\,c_1$ (so $\eta_0\le1/4$ iff
$c_1\le1/(16\sqrt{3(k+1)})$) and $\tau\ge(4\sqrt{3(k+1)}+1)^2c_1\approx60(k+1)c_1$. So the threshold is a tiny
multiple of $u$ ($\approx60(k+1)^{3/2}(N+k)u$). Steps that fail it are the ones where $\mathbf z_j$ is numerically in the
span of the basis. Without admissibility, orthogonality can be lost entirely. **Known**: for
$\mathbf w\in\operatorname{range}\mathbf V$ up to rounding, $\mathbf w'$ is rounding noise with
$\|\mathbf V^{\mathsf T}\mathbf w'\|/\|\mathbf w'\|=O(1)$ (Björck 1994; Giraud et al. 2005, the full-rank
hypothesis). The condition cannot be dropped.

### 1.3 The routine certificate (B2)

The certificate mirrors `IsMatvecRoutine` line by line. Fixed layout: the basis in buffer `Vb` (column-major,
$N$ rows), the work vector at `wb[wo..wo+N)`, coefficients at `hb[ho..ho+j)`.

```lean
structure IsOrthRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P) (N j : ℕ)
    (η₀ ε₁ ε₂ ε₃ : ℝ) (pre : Store P K → Prop) (Vb wb hb : ℕ) (wo ho : IExp ℕ)
    (routine : Builder P ι ℕ ℕ Unit) : Prop where
  composable : ExecutionComposable I routine
  run : ∀ (st : St P K C) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ), pre st.store →
    HoldsDecoded st.store dec tag Vb 0 V → (decoded w at wb, wo) →
    (hb allocated with ≥ ho + j cells, disjoint from Vb and wb) →
    ∃ (out : St P K C) (W : Fin N → K) (Hw : Fin j → K),
      exec I routine.run st = some out ∧
      (out.store = the two block writes of W at (wb, wo) and Hw at (hb, ho), nothing else;
       in particular out.store.shape = st.store.shape: scratch is scoped) ∧
      IsOrthErr η₀ ε₁ ε₂ ε₃ V w (dec tag ∘ Hw) (dec tag ∘ W)
```

The Lanczos proofs take `orth : ℕ → Builder P ι ℕ ℕ Unit` and
`horth : ∀ t, IsOrthRoutine I dec tag N (t+1) (η₀ t) (ε₁ t) (ε₂ t) (ε₃ t) pre 1 7 hb 0 (·) (orth t)`.
This is the same pattern as `hmv : ∀ t, IsMatvecRoutine … (mv t)` in
`LanczosImplementation.exec_rounded_work`. The coefficient buffer `hb` ($q+1$ cells) is allocated once,
outside the loop, like `work`; the routine's own scratch (`s`, `h₂`, one cell) is fresh under `scope`,
which the `gemv`/`axpy` frames on main require. For CGS2 `pre` is `True` (the basis is an explicit
premise); the stored-matrix tree's `pre` for the matvec stays `HoldsDecoded store dec tag 6 0 A`.

### 1.4 How the parameterization is expressed in `Prog` (FR1)

Three options were considered:

* **(a) Routine family plus certificate, concrete trees** (recommended, the pattern already on main).
  Builders and proofs are generic in `orth`. Each registered tree is compiled from one concrete
  instance: `lanczosReorthProg tag N q …` calls `cgs2 tag N (.var j + 1) V w h`, and
  `lanczosReorthProg.compiled` is `ProgFamily.compile … |>.get rfl` as for `lanczosProg`. `compile`
  evaluates by `rfl`, so it needs a concrete builder; a tree compiled "for any scheme" does not
  exist. The scheme-generic theorems are stated about any builder whose iteration-$t$ body is
  `orth t`. The CGS2 corollaries then become statements about the registered tree, with the
  certificate discharged by C6. Adding MGS2 later means a new builder, a new tree and one
  certificate proof. The Lanczos analysis is untouched.
* (b) Fix CGS2 everywhere, no abstraction. Fewer definitions, but the Lanczos analysis would be
  tied to CGS2's constants, and every later scheme would need a re-proof.
* (c) A primitive orthogonalization kernel (`kcall`) whose interpretation carries the contract.
  This needs COMPDYN's `kcall`, which is not on main, and it would make orthogonalization an
  unanalysed black box. Keep it as a later *instance* of (a): a kcall routine with `IsQRErr`
  semantics meets `IsOrthRoutine` (§2.5).

Modularity is not awkward in main's `Prog`: (a) adds one structure and reuses the existing
composability machinery. We therefore do not recommend (b).

## 2. The algorithm inside the model of computation

### 2.1 Variant and outputs (FR4, FR5)

The body is main's `lanczosProg` loop body verbatim (Paige's A(1) order, `nrm2`, exact zero test,
zero continuation), with two insertions after the second `axpy`:

| line | operation | code |
|---|---|---|
| 1–5 | $\mathbf u=\mathbf A\mathbf v_j$; $\mathbf w=\mathbf u-\beta_{j-1}\mathbf v_{j-1}$; $\alpha_j=\mathbf v_j^{\mathsf T}\mathbf w$; $\mathbf z=\mathbf w-\alpha_j\mathbf v_j$ | unchanged (`gemv`/`apply`, `axpy`, `dot`, `axpy`) |
| 6 | $\nu_j\leftarrow\|\mathbf z\|$ | **new** `nrm2 tag ⟨nu, .var j⟩ work 0 N` |
| 7 | $(\mathbf h,\mathbf z')\leftarrow\mathrm{orth}(\mathbf V_{j+1},\mathbf z)$ | **new** `orth` routine against columns $0..j$ of `V` |
| 8–9 | $\beta_j=\|\mathbf z'\|$; zero test; $\mathbf v_{j+1}=\mathbf z'/\beta_j$ | unchanged |

**Returned**: `b` (kept), all $q+1$ basis columns `V`, `alpha` ($q$), `beta` ($q+1$), `inputNorm`,
`prev`, and **new** `nu` ($q$). The reorthogonalization coefficients go to a scoped scratch buffer
and are discarded (FR5 (a)). This is what practical FRO codes return (the tridiagonal
$\mathbf T_k$), and it is what SLQ and Ritz computations consume. The analysis accounts for the
discarded coefficients: they enter the residual of the three-term relation,
$\mathbf F_k\mathbf e_j=\mathbf f_j+\mathbf V_j\mathbf h_j$. Lemma D4 shows they are small, and that
lemma needs $\mathbf A=\mathbf A^{\mathsf T}$. FR5 (b) also returns the coefficient columns
($q(q+1)/2$ words, the Arnoldi Hessenberg). Then $\mathbf F_k$ is pure rounding and D4 becomes a
statement about outputs, but the tree and the counts change. FR5 (c), "$\alpha_j\mathrel{+}=h_{jj}$",
is used in some codes. We do not recommend it: the exact output would no longer equal
`lanczosAlpha`, and the gain is $O(u)$.

**Admissibility in the control flow (FR4).** (a) Recommended: keep main's exact zero test.
The program never compares against $\tau$. $\nu$ is stored, and the admissible prefix is read off
the outputs (§1.2). The exact program then still computes `lanczosState`, and $\tau$ is a parameter
of theorems, not of trees. (b) Stop at $\beta_j<\tau\nu_j$, with $\tau$ a declared input: one `ite`
on a rounded product, a new exact spec with a stopping index, and data-dependent counts.
(c) A hypothesis "every step is admissible": a condition on the run, rejected as in main's
practice.

### 2.2 The CGS2 routine (C1)

```lean
/-- One classical Gram–Schmidt pass of w[wo..] against the first j columns of V:
h ← Vᵀ w (j dots), s ← V h (gemv), w ← w − s (axpy with −1). Scratch: s (N cells), one cell. -/
def cgsPass (p : P) (N j : IExp VI) (V : VB) (w : VB) (wo : IExp VI) (h : VB) (ho : IExp VI) :
    Builder P ι VB VI Unit := scope do
  let s ← alloc p N;  let t ← alloc p 1
  forRange j fun i => dot p ⟨h, ho + .var i⟩ V (N * .var i) w wo N
  gemv p N j V 0 h ho s 0
  ins (.lit p ⟨t, 0⟩ (-1));  axpy p ⟨t, 0⟩ s 0 w wo N
/-- CGS2: two passes; h ← h₁ + h₂ (j adds). -/
def cgs2 (p) (N j) (V w wo h ho) : Builder P ι VB VI Unit := scope do
  let h₂ ← alloc p j
  cgsPass p N j V w wo h ho;  cgsPass p N j V w wo h₂ 0
  forRange j fun i => ins (.bin p .add ⟨h, ho + .var i⟩ ⟨h, ho + .var i⟩ ⟨h₂, .var i⟩)
```

It uses only kernels on main. The literal $-1$ is **not** exact under main's contract: `lit_err` gives
$q(1+\delta)$, $|\delta|\le u$, for every rational literal, and only $0$ is exact (`AddsZeroExactly`).
Negating a cell does not avoid this, since $\mathbf w\leftarrow\mathbf w-\mathbf s$ needs a scalar $\pm1$ in
`axpy`. C3 accounts for it: the extra term is $u\|\mathbf s\|\le u(1+\eta_0)(1+c_1)\|\mathbf w\|$, absorbed in $c_1$.

### 2.3 Programs, trees, targets (G1–G5; draft statements only, AGENTS rule 2)

Names follow main's Lanczos pair (`lanczosProg`/`StoredEntriesLanczos`,
`lanczosOracleProg`/`MatrixFreeLanczos`): **`lanczosReorthProg`** (stored matrix from ROM, `gemv`),
**`lanczosReorthOracleProg`** (oracle `apply`), with `.compiled : Prog P ι 1 7` and
`toStmt_compiled` by `rfl`. Exact targets (drafts for the maintainer to register; FR6, FR7):

```lean
def StoredEntriesLanczosReorth : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P),
    StoredEntries (𝕜 := ℝ) tag (lanczosReorthProg.compiled (ι := ι) tag)
      (fun _ _ => True) (fun N _ => Fin N → ℝ) (inputs: b, then 6 empty buffers)
      (fun N _ => N ^ 2) (fun N q => lanczosReorthCount tag N (q 0)) (memory formula)
      (fun N q b vals _ st =>
        let A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j)
        Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
        Holds st.store tag 1 0 (lanczosReorthMatrix A b (q 0 + 1)) ∧
        Holds st.store tag 2 0 (fun j _ => (lanczosReorthState A b j).alpha) ∧
        Holds st.store tag 3 0 (fun j _ => (lanczosReorthState A b j).beta) ∧
        st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
        Holds st.store tag 5 0 (fun i _ => (lanczosReorthState A b (q 0)).prev i) ∧
        Holds st.store tag 6 0 (fun j _ => (lanczosReorthState A b j).nu))
```

The target, like `StoredEntriesLanczos`, has no symmetry premise. For non-symmetric $\mathbf A$ the
reorthogonalization coefficients are nonzero even in exact arithmetic, so the spec is an exact
FRO recurrence `lanczosReorthState` (A1; a truncated Arnoldi/Gram–Schmidt step, written as a
total recursion with $0^{-1}=0$ like `arnoldiState`). A separate theorem identifies it with
`lanczosState` for symmetric $\mathbf A$ (A2): in exact arithmetic $\mathbf V_j^{\mathsf T}\mathbf z_j=\mathbf 0$,
so both passes subtract exact zeros, and zero columns after breakdown contribute zero coefficients.
FR6 (b) adds a symmetric premise instead; that departs from main's no-premise practice.

Counts: $\mathrm{lanczosCount}$ plus, per step $j$, $2(j+1)$ dots, 2 gemv of width $j+1$, 2 axpys,
$j+1$ adds and one `nrm2`, so $\approx 4N\sum_j(j+1)\approx 2Nq^2$ extra multiplications. Memory adds
$N+2(q+1)+q$ cells. Both come from `StaticCost` on the tree, as on main.

Rounded results (no new access model): `LanczosReorthImplementation.exec_rounded_compiled` and the
oracle twin, stated on `(lanczosReorthProg.compiled tag).exec I N ![q] st` under `IsRelErrSem`,
`AddsZeroExactly` and unit charges, exactly in the shape of `LanczosImplementation.exec_rounded_compiled`
(dense, ROM words decoding to symmetric $\mathbf A$, the explicit `hsmall`). Conclusion: success,
the decoded output ties, the static cost bound, and a `LanczosReorthRun` (§3.1) whose fields are the
decoded outputs.

### 2.4 Exact real arithmetic is used only in specifications and analysis

Every data operation of the trees is a rounded kernel instruction. Mathematical objects ($\mathbf U$, the polar factor of
the decoded basis, $\mathbf E$, $\mathbf G$) appear only in theorem statements and
proofs. The one value that is "exact" in the program is the zero test `cmp .eq`, which main already
uses. $\tau$ never enters a tree (FR4 (a)).

### 2.5 Later instances (not this stage)

* **MGS2**: `orthAgainst` twice (main's sweep). It meets the contract with $\varepsilon_3$ of second order.
  The rounded sweep analysis is not on main (only the exact `mgsSweep_eq_sub_sum`): M–L.
* **DGKS conditional second pass** (second pass only if $\|\mathbf w'\|<\|\mathbf w\|/\sqrt2$): needs an
  `ite` on a rounded comparison. Same contract, with $\varepsilon_3$ by cases.
* **Householder-based FRO** (implicit $\mathbf Q$ from stored reflectors): the routine's `pre` holds
  the reflectors, and the basis buffer is an output of the routine. That needs a richer certificate
  (state invariant), H.
* **QR kernel**: with COMPDYN's `kcall` and `IsQRErr` (not on main), QR of $[\mathbf V\;\mathbf w/\|\mathbf w\|]$
  gives $\varepsilon_3=0$ unconditionally, at $O(nj^2)$ per step. It is a reference instance.

## 3. What stability can be proved

### 3.1 The run interface (D1)

`LanczosReorthRun n k` is a structure modelled on `LanczosRun`. It has the same Paige-order local
clauses (`u_eq`, `w_eq`, `α_eq`, `z_eq` with their ε bounds, the `ε_le` local field as generalized
on main), and it replaces `smul_v_eq`/`norm_δ_le` with:

* `nu_eq`: $\nu_j=\|\mathbf z_j\|(1+\theta)$, with $|\theta|\le\gamma_{N+1}$;
* `orth_eq`: `IsOrthErr (η₀ j) (ε₁ j) (ε₂ j) (ε₃ j) (basis j) (z j) (h j) (z' j)`;
* `smul_v_eq`: $\beta_j\mathbf v_{j+1}=\mathbf z_j'+\boldsymbol\delta_j$, with $\|\boldsymbol\delta_j\|\le\varepsilon\|\mathbf z_j'\|$ and nearly unit $\mathbf v_{j+1}$ when $\beta_j\ne0$;
* `admissible`: $\tau\nu_j<\beta_j$ for $j<k$ (0-based; true by the definition of $k$);
* the horizon is **not** a field: theorems take `hsmall`, as on main after
  `Krylov-FinitePrecision-Runs.md`.

`toLanczosData` forgets to the generic three-term data. The perturbed relation and the Ritz identity
then come from `LanczosData.mul_basis`/`mulVec_basis_mulVec_sub_smul` for free (D2). A
`LanczosReorthRun` is *not* a `LanczosRun`: the correction $\mathbf V_j\mathbf h_j$ is absolute,
$O(j\mu\|\mathbf A\|)$, while `norm_ez_le` is relative to $\|\mathbf w\|$, which has no lower bound.
Main's Paige/dilation analysis therefore does not apply verbatim, and it is not needed.

### 3.2 The ranked menu

| # | Result | Hypotheses | Bound (sketch) | Status | Size | Reuses |
|---|---|---|---|---|---|---|
| S2 | **Orthogonality of the admissible prefix** $\|\mathbf V_{k+1}^{\mathsf T}\mathbf V_{k+1}-\mathbf I\|_F\le\sqrt{3(k+1)}\,\mu$, $\mu=\max_j(\varepsilon_1+\varepsilon_3/\tau+\gamma_{N+4})$ | contract, admissibility, $\sqrt{3(k+1)}\mu\le\eta_0$ | for CGS2: $\mu\le4c_1$ (§1.2) | known: Paige 1970 for Lanczos with reorthogonalization under a stopping criterion (locator to verify); Giraud et al. 2005 Thm 2 for the CGS2 kernel constants; planned here from the contract | M | B5, B6, B8 |
| S1 | **Perturbed Lanczos relation** $\mathbf A\mathbf V_k=\mathbf V_k\mathbf T_k+\beta_k\mathbf v_{k+1}\mathbf e_k^{\mathsf T}+\mathbf F_k$, $\|\mathbf F_k\|_F\le c_F\,k(\mu+\varepsilon)\|\mathbf A\|$, including the discarded coefficients | S2, $\mathbf A$ symmetric | $\|\mathbf h_j\|\lesssim\sqrt j(5\mu+2\varepsilon)\|\mathbf A\|$ (D4) | known in substance: Paige 1970 (the reorthogonalized relation; Paige 1976 for the plain rounding part); Simon 1984b is the semi-orthogonal generalization; planned | L | `LanczosData.mul_basis`, `LocalErrors`-style coefficient bounds |
| S1′ | **Projection form** $\|\mathbf V_k^{\mathsf T}\mathbf A\mathbf V_k-\mathbf T_k\|\le c(\mu\|\mathbf A\|+\|\mathbf F_k\|)$ | S1, S2 | — | known (Simon 1984b, semi-orthogonality suffices) | S | — |
| S3 | **$n\times n$ symmetric backward model.** With $\mathbf U=\mathbf V_{k+1}(\mathbf V_{k+1}^{\mathsf T}\mathbf V_{k+1})^{-1/2}$ (polar factor, orthonormal; $\|\mathbf u_1-\mathbf v_1\|\le\|\mathbf U-\mathbf V\|_2$), some symmetric $\mathbf E$ satisfies $(\mathbf A+\mathbf E)\mathbf U_k=\mathbf U_k\mathbf T_k+\beta_k\mathbf u_{k+1}\mathbf e_k^{\mathsf T}$ exactly, and $\|\mathbf E\|_F\le\sqrt2\bigl((\|\mathbf A\|+\|\underline{\mathbf T}_k\|)\|\mathbf U-\mathbf V\|_F+\|\mathbf F_k\|_F\bigr)$; hence $\mathbf T_k=$ `lanczosTridiagonal` $(\mathbf A+\mathbf E)$ $\mathbf u_1$ | S1, S2, admissible prefix ($\beta_j>0$, $j\le k$); terminal $\beta_k=0$ separately (E6) | $\|\mathbf E\|_F=O(k\mu\|\mathbf A\|)$ | known in substance: Paige 1970 (primary: the computed tridiagonal is close to that of a nearby matrix under the criterion; locator to verify); Simon 1984b; Stewart 2002 for Krylov decompositions; Paige 2010 for the plain case, by augmentation; this statement planned | L | E1, E2, `lanczosState_eq_of_orthonormal_recurrence` |
| S4a | **Interlacing up to $\|\mathbf E\|$** (F1): $\lambda_{i+n-k}(\mathbf A)-e\le\theta_i\le\lambda_i(\mathbf A)+e$ | S3 | $e=\|\mathbf E\|_2$ | follows from S3 + Poincaré + Weyl (proved on main) | S | Interlacing, Weyl |
| S4a′ | **Converged Ritz values are not duplicated** (F2): if $\lambda$ has multiplicity $m$ and gap $g>2e$, with $r_i=\beta_k|\mathbf e_k^{\mathsf T}\mathbf y_i|$, then $\#\{i:\theta_i\in(\lambda-e,\lambda+e),\ r_i<(g-2e)/\sqrt{m+1}\}\le m$. Interlacing alone does **not** give a count: $\mathbf A=\operatorname{diag}(1,0,-1)$, $\mathbf E=\mathbf 0$, $k=2$, $\mathbf u_1=(\delta,\sqrt{1-2\delta^2},\delta)$ gives Ritz values $\pm\sqrt2\delta$, two within $e$ of the simple eigenvalue $0$ (Fable review finding 1) | S3 | — | the phenomenon is known (Paige 1971; Parlett 1998 Ch. 13); this statement planned: $\mathbf A+\mathbf E$ has exactly $m$ eigenvalues in the window (Weyl), $\|(\mathbf I-\mathbf P)\mathbf x_i\|\le r_i/(g-2e)$ for orthonormal $\mathbf x_i=\mathbf U_k\mathbf y_i$ (F2a), and $\sum_i\|\mathbf P\mathbf x_i\|^2\le m$ | M | F2a, Weyl |
| S4b | **Ritz pairs**: each Ritz value has an eigenvalue of $\mathbf A$ within $(\beta_k|s_k|\,\|\mathbf v_{k+1}\|+\|\mathbf F_k\|)/\|\mathbf V_k\mathbf s\|$, and within $\beta_k|s_k|+e$ | S1 or S3 | — | known (Paige 1980 for plain; standard) | S | `exists_abs_eigenvalue_sub_mul_norm_le` |
| S4c | **Kaniel–Paige–Saad transfer**: the proved KPS bound for $(\mathbf A+\mathbf E,\mathbf u_1)$, with the hypothesis intervals widened by $e$ | S3, gap $>2e$ | the bound of `eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le` for $\mathbf A+\mathbf E$, plus $e$ | planned (direct); stating the tangent in $\mathbf A$'s data needs Davis–Kahan, later | M | Ritz.lean, Weyl |
| S4d | **Gauss quadrature / SLQ transfer**: $\|\tilde{\mathbf b}\|^2\mathbf e_1^{\mathsf T}p(\mathbf T_k)\mathbf e_1=\tilde{\mathbf b}^{\mathsf T}p(\mathbf A+\mathbf E)\tilde{\mathbf b}$ for $\deg p\le2k-1$, and for $L$-Lipschitz $f$, $|\tilde{\mathbf b}^{\mathsf T}f(\mathbf A+\mathbf E)\tilde{\mathbf b}-\mathbf b^{\mathsf T}f(\mathbf A)\mathbf b|\le L\|\mathbf E\|_F\|\mathbf b\|^2+2\|f\|_\infty\|\mathbf b\|\|\tilde{\mathbf b}-\mathbf b\|$ | S3 | — | exactness is classical (Golub–Meurant 2010); the transfer is planned via Kittaneh (proved) | M | Gauss.lean, `frobNorm_cfc_sub_cfc_le` |
| S5 | **Pure backward form** (exact $\mathbf b$): an orthogonal $\mathbf Z=$ `householder (u₁ + b̂) * householder u₁` (two reflectors; a rotation in $\operatorname{span}\{\mathbf u_1,\hat{\mathbf b}\}$, the identity on its complement; a single reflector has $\|\mathbf Z-\mathbf I\|_2=2$) with $\mathbf Z\mathbf u_1=\hat{\mathbf b}=\mathbf b/\|\mathbf b\|$, $\|\mathbf Z-\mathbf I\|_2=\|\mathbf u_1-\hat{\mathbf b}\|$; $\mathbf A'=\mathbf Z(\mathbf A+\mathbf E)\mathbf Z^{\mathsf T}$, $\|\mathbf A'-\mathbf A\|\le e+4\|\mathbf A\|\cdot O(u)$ | S3 + start-vector bound | — | standard construction; planned | M | Householder.lean |
| S6 | Ritz vector angles via Davis–Kahan | S3/S4b, gap | — | known (standard); later | M | DK |

The **payoff over plain Lanczos** is S3, S4a and S4a′. Main's plain-Lanczos model is a dilation of size
$n(k+1)$ with $400q^3\varepsilon\|\mathbf A\|$ (or $1000q^2\varepsilon$). It cannot give interlacing
with the spectrum of $\mathbf A$: ghost copies are real in plain finite-precision Lanczos (Paige 1971;
Greenbaum 1989). With full reorthogonalization the model has size $n\times n$, the Ritz values
interlace $\mathbf A$'s eigenvalues up to $e$, and converged Ritz values are not duplicated, because the
Ritz vectors $\mathbf U_k\mathbf y_i$ are orthonormal (for plain Lanczos $\mathbf V_k\mathbf y_i$ are not). The dimension count $k+1\le n$ is automatic.

### 3.3 Proof sketches

**D4, the coefficient lemma (the one place symmetry is needed).** Write the computed relation as
$\mathbf A\mathbf v_j=\beta_{j-1}\mathbf v_{j-1}+\alpha_j\mathbf v_j+\mathbf V_j\mathbf h_j+\beta_j\mathbf v_{j+1}+\mathbf f_j$.
By B4, $\|\mathbf h_j\|$ is controlled by $\|\mathbf V_j^{\mathsf T}\mathbf z_j\|$, so bound each component $\mathbf v_i^{\mathsf T}\mathbf z_j$:

* $i\le j-2$: $\mathbf v_i^{\mathsf T}\mathbf A\mathbf v_j=(\mathbf A\mathbf v_i)^{\mathsf T}\mathbf v_j$ by symmetry. Expand $\mathbf A\mathbf v_i$ by the relation at step $i$. Every resulting inner product with $\mathbf v_j$ is an off-diagonal Gram entry ($\le\mu$), apart from $\mathbf h_i^{\mathsf T}\mathbf V_i^{\mathsf T}\mathbf v_j$ ($\le\|\mathbf h_i\|\,\|\mathbf g_{j-1}\|\le\|\mathbf h_i\|\mu$, second order) and $\mathbf f_i^{\mathsf T}\mathbf v_j$. So $|\cdot|\le 5\|\mathbf A\|\mu+\mu\|\mathbf h_i\|+\|\mathbf f_i\|$.
* $i=j-1$: the $\beta_{j-1}$ terms cancel up to $\beta_{j-1}(\|\mathbf v_j\|^2-\|\mathbf v_{j-1}\|^2)=O(\varepsilon\|\mathbf A\|)$, plus the same $O(\|\mathbf A\|\mu+\mu\|\mathbf h_{j-1}\|+\|\mathbf f_{j-1}\|)$ terms as for $i\le j-2$.
* $i=j$: $\mathbf v_j^{\mathsf T}\mathbf z_j=\alpha_j(1-\|\mathbf v_j\|^2)+O(\varepsilon)=O(\varepsilon|\alpha_j|)$.

Induction on $j$ under $j\mu\le1/4$ gives $\|\mathbf h_j\|\le c_h\sqrt j(5\mu+2\varepsilon)\|\mathbf A\|$. Order of proof:
**D5 → D3 → D4 → D6 → D7.** S2 (D5) needs only the contract, admissibility, B5/B6/B8 and the `nrm2`
lemma, never $\|\mathbf A\|$ or the coefficients. With S2 in hand, expanding
$\|\mathbf z_j'\|^2=\mathbf z_j'^{\mathsf T}(\mathbf z_j-\mathbf V\mathbf h_j-\mathbf f_j)$ gives the coefficient bounds directly,
$|\alpha_j|,\beta_j\le(1+cj\mu)\|\mathbf A\|+\ldots$ (D3), with no $j$-growth and no later sharpening step. Without symmetry the components
$i\le j-2$ are $O(1)$: that is Arnoldi, and the coefficients cannot be discarded.

**S3, the symmetric completion (E1, planned, S; Kahan–Parlett–Jiang 1982, locator to verify).** Let
$\mathbf U$ have orthonormal columns and let $\mathbf R$ be such that $\mathbf S=\mathbf U^{\mathsf T}\mathbf R$ is
symmetric. Put $\mathbf E=-\mathbf R\mathbf U^{\mathsf T}-\mathbf U\mathbf R^{\mathsf T}+\mathbf U\mathbf S\mathbf U^{\mathsf T}$.
Then $\mathbf E=\mathbf E^{\mathsf T}$ and $\mathbf E\mathbf U=-\mathbf R$. With
$\mathbf R_\perp=(\mathbf I-\mathbf U\mathbf U^{\mathsf T})\mathbf R$ one gets
$\mathbf E=-\mathbf U\mathbf S\mathbf U^{\mathsf T}-\mathbf R_\perp\mathbf U^{\mathsf T}-\mathbf U\mathbf R_\perp^{\mathsf T}$,
so $\|\mathbf E\|_F^2=\|\mathbf S\|_F^2+2\|\mathbf R_\perp\|_F^2\le2\|\mathbf R\|_F^2$. Apply this with
$\mathbf R=\mathbf A\mathbf U_k-\mathbf U_{k+1}\underline{\mathbf T}_k$. Then
$\mathbf U_k^{\mathsf T}\mathbf R=\mathbf U_k^{\mathsf T}\mathbf A\mathbf U_k-\mathbf T_k$ is symmetric because $\mathbf A$ and
$\mathbf T_k$ are, and $\mathbf R=\mathbf A(\mathbf U-\mathbf V)_k-(\mathbf U-\mathbf V)_{k+1}\underline{\mathbf T}_k+\mathbf F_k$.
For E2 (planned, S): take the **polar factor** $\mathbf U=\mathbf V\mathbf G^{-1/2}$, $\mathbf G=\mathbf V^{\mathsf T}\mathbf V$,
$\|\mathbf G-\mathbf I\|_2\le\eta<1$. Then $\mathbf U$ has orthonormal columns and
$\|\mathbf U-\mathbf V\|_F=\|\mathbf G^{1/2}-\mathbf I\|_F\le\|\mathbf G-\mathbf I\|_F/(1+\sqrt{1-\eta})$, from main's
`frobNorm_cfc_sub_cfc_le` (Kittaneh) with $\sqrt{\cdot}$ Lipschitz on $[1-\eta,1+\eta]$, or directly from the
spectral decomposition. The QR route ($\mathbf U=$ `gramSchmidtQ` $\mathbf V$, which keeps $\mathbf u_1\parallel\mathbf v_1$)
was dropped: the bound $\|\boldsymbol\Delta\|_F\le\|\mathbf G-\mathbf I\|_F/(1-\|\mathbf G-\mathbf I\|_2)$ for the
Cholesky factor $\mathbf I+\boldsymbol\Delta$ only yields $x\le(g+x^2)/\sqrt2$, which needs an a-priori bound to
select the small root. A rigorous proof is a column-by-column Cholesky induction, M–L (Sun 1991;
Chang–Paige–Stewart 1997). The price of the polar factor is $\mathbf u_1\not\parallel\mathbf v_1$, but
$\|\mathbf u_1-\mathbf v_1\|\le\|\mathbf U-\mathbf V\|_2=O(\sqrt k\mu)$, which is dominated by $e/\|\mathbf A\|=O(k\mu)$
in S4d and S5, so no result loses order. E4: `lanczosState_eq_of_orthonormal_recurrence` on
$(\mathbf A+\mathbf E,\mathbf u_1)$ with $\beta_j>0$ for $j\le k$ (strict admissibility) and $k+1$ orthonormal
$\mathbf u_1,\dots,\mathbf u_{k+1}$ gives the exact Lanczos tridiagonal. The terminal case $\beta_k=0$
($\mathbf v_{k+1}=\mathbf 0$) is a separate statement E6: either an orthonormal completion ($k<n$) or a variant
of the lemma that never reads $\mathbf u_{k+1}$.

**C3–C5, CGS2 meets the contract (planned, M each).** One pass, from main's kernel lemmas:
$\mathbf h_1=\mathbf V^{\mathsf T}\mathbf w+\mathbf e_h$ with $|\mathbf e_h|\le\gamma_N|\mathbf V|^{\mathsf T}|\mathbf w|$, and
$\mathbf w'=\mathbf w-\mathbf V\mathbf h_1+\mathbf e$ with $|\mathbf e|\le\gamma_{j+1}(|\mathbf w|+|\mathbf V||\mathbf h_1|)$. Using
$\|\mathbf V\|_F\le\sqrt{j(1+\eta_0)}$ this gives $\mathbf w'=(\mathbf I-\mathbf V\mathbf V^{\mathsf T})\mathbf w+\mathbf f_1$ with
$\|\mathbf f_1\|\le c_1\|\mathbf w\|$, $c_1\approx\sqrt j(N+j+2)u$ (including the rounded literal $-1$, §2.2). Then
$\mathbf V^{\mathsf T}\mathbf w'=(\mathbf I-\mathbf V^{\mathsf T}\mathbf V)\mathbf V^{\mathsf T}\mathbf w+\mathbf V^{\mathsf T}\mathbf f_1$, so
$\|\mathbf V^{\mathsf T}\mathbf w'\|\le\sqrt{1+\eta_0}(\eta_0+c_1)\|\mathbf w\|$: one pass meets the contract with
first-order $\varepsilon_3$ (C7). A second pass on $\mathbf w'$ gives
$\|\mathbf V^{\mathsf T}\mathbf w''\|\le\eta_0\|\mathbf V^{\mathsf T}\mathbf w'\|+\sqrt{1+\eta_0}\,c_1\|\mathbf w'\|$, and
$\|\mathbf w'\|\le(\|\mathbf w''\|+(1+\eta_0)(\eta_0+c_1)\|\mathbf w\|)/(1-c_1)$. So
$\varepsilon_1\approx c_1$ and $\varepsilon_3\approx(\eta_0+c_1)^2$. The residual relation sums the two
passes plus the rounding of $\mathbf h_1+\mathbf h_2$: $\varepsilon_2\approx2c_1+u(1+\eta_0)$. All ingredients
except the algebra are on main.

### 3.4 Constants, to first order (sketch; fixed by proofs)

$c_1\approx\sqrt k(N+k)u$, $\mu\le4c_1$, $\eta_0=4\sqrt{3(k+1)}c_1$, $\|\mathbf V^{\mathsf T}\mathbf V-\mathbf I\|_F\lesssim 4\sqrt3\,k(N+k)u$,
$\|\mathbf F_k\|_F\lesssim c\,k^{3/2}(N+k)u\|\mathbf A\|$, $\|\mathbf E\|_F\lesssim c\,k^{3/2}(N+k)u\|\mathbf A\|$, with
admissibility threshold $\tau\approx60(k+1)^{3/2}(N+k)u$. For comparison, Giraud et al. (2005) prove
$O(mn^{3/2})u$ loss for CGS2 QR. Practical FRO behaves like $O(\sqrt k\,u)$ (conjectured; we do not
claim it).

### 3.5 Dependencies of hypotheses

* `hsmall`: the fixed-point condition $\sqrt{3(k+1)}\,\mu(\eta_0,\tau)\le\eta_0\le1/4$ of §1.2, and $k(\mu+\varepsilon)\le1/100$-type. These are
  explicit in $N$, $k$, $u$, $\tau$, like main's horizons.
* $\mathbf A=\mathbf A^{\mathsf T}$ (decoded): needed for D4, A2 and S3.
* Unbounded-range standard model (`IsRelErrSem`). Main's bounded-format and mixed-error guarantees
  (PR #58) apply to the same trees later. This is not a decision: main settled the model.

### 3.6 Out of reach or false

* **Forward closeness of $\operatorname{span}\mathbf V_k$ to $\mathcal K_k(\mathbf A,\mathbf b)$, or of $\mathbf T_k$ to the exact
  $\mathbf T_k(\mathbf A,\mathbf b)$.** False in general. Krylov subspaces and the Lanczos tridiagonal are
  ill-conditioned functions of $(\mathbf A,\mathbf b)$ once a Ritz value converges
  (Carpraux–Godunov–Kuznetsov 1996; Kuznetsov 1997; known). Only backward statements (S3) and their
  spectral consequences are available.
* **Orthogonality without admissibility.** False (§1.2, known).
* **Relative accuracy of small eigenvalues.** Not available from a normwise $\mathbf E$. The bounds are absolute, $O(\|\mathbf E\|)$.
* **$k$-independent constants** ($\|\mathbf V^{\mathsf T}\mathbf V-\mathbf I\|=O(u)$ uniformly in $k$). Conjectured
  practical behaviour, with no proof route under a normwise contract.
* **Transfer of KPS stated purely in $\mathbf A$'s spectral data.** Needs perturbation of the spectral
  weights (Davis–Kahan plus gap). Later (S6).

## 4. Recommended first stage

48 statements in 8 groups. Files in brackets. A: Krylov layer. B, C: Computation/Matrix layer.
D–F: `Krylov/FinitePrecision`. G: `Krylov/Processes`.

| id | statement sketch | size | deps |
|---|---|---|---|
| **A1** | `lanczosReorthStep`, `lanczosReorthState`, `lanczosReorthMatrix`: the exact FRO recurrence (Paige order, two exact CGS passes, `nu`), total with $0^{-1}=0$ [`LanczosReorthRecurrence.lean`] | S | — |
| A2 | `lanczosReorthState_eq_lanczosState`: equal for $\mathbf A^{\mathsf H}=\mathbf A$, every $q$, no breakdown hypothesis | M | A1, `LanczosRecurrence` |
| A3 | `lanczosReorthState_nu`: $\nu_j=\beta_j$ for Hermitian $\mathbf A$ (exact arithmetic subtracts nothing) | S | A2 |
| **B1** | `IsOrthErr` (def, §1.1) [`Matrix/Computation/OrthErr.lean`] | S | — |
| B2 | `IsOrthRoutine` (def, §1.3) [`Computation/OrthRoutine.lean`] | S | — |
| B3 | `IsOrthRoutine.mono`, `IsOrthErr.mono` in all four parameters | S | B1, B2 |
| B4 | `IsOrthErr.norm_coef_le`: the coefficient bound of §1.1 | S | B1 |
| B5 | `IsOrthErr.norm_transpose_mulVec_normalize_le`: $\|\mathbf V^{\mathsf T}\mathbf w'/\|\mathbf w'\|\|\le\varepsilon_1+\varepsilon_3\|\mathbf w\|/\|\mathbf w'\|$ | S | B1 |
| B6 | `frobNorm_transpose_mul_self_sub_one_sq`: the column-append identity, and `frobNorm_transpose_mul_self_sub_one_le` ($\sqrt{3m}\mu$) | S | — |
| B7 | `injective_of_specNorm_gram_sub_one_lt_one` and the corollary $m\le n$ | S | — |
| B8 | `specNorm_le_sqrt_one_add`, `frobNorm_le_sqrt_mul_one_add`: $\|\mathbf V\|_2\le\sqrt{1+\eta_0}$, $\|\mathbf V\|_F\le\sqrt{j(1+\eta_0)}$ from $\|\mathbf V^{\mathsf T}\mathbf V-\mathbf I\|_2\le\eta_0$ | S | — |
| **C1** | `cgsPass`, `cgs2` builders (§2.2) [`Matrix/Computation/CGS2.lean`] | S | — |
| C2 | `exec_cgs2_exactInterp`: in exact arithmetic, the two passes compute $(\mathbf I-\mathbf V\mathbf V^{\mathsf T})$ twice and $\mathbf h=\mathbf V^{\mathsf T}\mathbf w+\mathbf V^{\mathsf T}(\mathbf I-\mathbf V\mathbf V^{\mathsf T})\mathbf w$ (any $\mathbf V$) | M | C1 |
| C3 | `IsRelErrSem.exec_cgsPass`: decoded $\mathbf w'=(\mathbf I-\mathbf V\mathbf V^{\mathsf T})\mathbf w+\mathbf f_1$, $\mathbf h_1=\mathbf V^{\mathsf T}\mathbf w+\mathbf e_h$, explicit $c_1$ (`cgsPassBound N j u η₀`) | M | C1, kernel lemmas |
| C4 | `norm_transpose_mulVec_le_of_norm_sub_le`: $\|\mathbf V^{\mathsf T}\mathbf w'\|\le\sqrt{1+\eta_0}(\eta_0+c_1)\|\mathbf w\|$ | S | C3 |
| C5 | `isOrthErr_cgs2`: CGS2 meets `IsOrthErr` with $(\varepsilon_1,\varepsilon_2,\varepsilon_3)$ explicit | M | C3, C4 |
| C6 | `IsRelErrSem.isOrthRoutine_cgs2`: the certificate (success, frames, composable) | L | C5, `ScalarFrames` |
| C7 | `isOrthErr_cgsPass`: one pass meets the contract with first-order $\varepsilon_3$ (documents why one pass is not enough) | S | C4 |
| **D1** | `LanczosReorthRun n k` (def, §3.1), `reorthSteps τ ν β q` (def) [`LanczosReorthRun.lean`] | S | B1 |
| D2 | `LanczosReorthRun.toLanczosData`; `recurrenceError_eq`: $\mathbf f_j+\mathbf V_j\mathbf h_j$ | S | D1 |
| D5 | `frobNorm_transpose_mul_self_sub_one_le`: S2 on the admissible prefix (first: needs no coefficient bound) | M | B5, B6, B8 |
| D3 | coefficient bounds `abs_α_le`, `β_le`, `norm_z_le`: $(1+cj\mu)\|\mathbf H\|+\ldots$, no $j$-growth | M | D1, D5 |
| D4 | `norm_coef_le`: $\|\mathbf h_j\|\le c_h\sqrt j(5\mu+2\varepsilon)\|\mathbf H\|$ (symmetric $\mathbf H$, induction) | L | B4, D3, D5 |
| D6 | `frobNorm_residual_le`: S1 | M | D2, D4 |
| D7 | `specNorm_transpose_mul_mul_sub_tridiagonal_le`: S1′ | S | D5, D6 |
| D8 | `steps_succ_le_card`: $k+1\le n$ when $\beta_k\ne0$ | S | B7, D5 |
| **E1** | `exists_symm_mul_eq_neg`: the symmetric completion, $\|\mathbf E\|_F\le\sqrt2\|\mathbf R\|_F$ [`Matrix/Perturbation/SymmetricBackward.lean`] | S | — |
| E2 | `frobNorm_polar_sub_le`: polar factor $\mathbf U=\mathbf V\mathbf G^{-1/2}$ is orthonormal and $\|\mathbf U-\mathbf V\|_F\le\|\mathbf G-\mathbf I\|_F/(1+\sqrt{1-\eta})$ | S | `frobNorm_cfc_sub_cfc_le` |
| E3 | `LanczosReorthRun.exists_backward`: S3's identity and bound [`LanczosReorthBackward.lean`] | L | D6, D5, E1, E2 |
| E4 | `lanczosTridiagonal_backward`: $\mathbf T_k=$ exact Lanczos of $(\mathbf H+\mathbf E,\mathbf u_1)$, $\beta_j>0$ for $j\le k$ | M | E3, `lanczosState_eq_of_orthonormal_recurrence` |
| E5 | `exists_orthogonal_mulVec_eq` (two reflectors, $\|\mathbf Z-\mathbf I\|_2=\|\mathbf u_1-\hat{\mathbf b}\|$) + pure-backward corollary (S5) | M | E3, `Householder` |
| E6 | `lanczosTridiagonal_backward_of_beta_eq_zero`: the terminal case $\beta_k=0$ | S | E4 |
| **F1** | `eigenvalue_tridiagonal_le_add`, `le_eigenvalue_tridiagonal_add`: interlacing up to $e$ [`LanczosReorthSpectral.lean`] | S | E4, Interlacing, Weyl |
| F2a | `norm_sub_spectralProjector_mulVec_le`: for Hermitian $\mathbf M$, unit $\mathbf x$, $\|(\mathbf I-\mathbf P)\mathbf x\|\le\|\mathbf M\mathbf x-\theta\mathbf x\|/d$, $\mathbf P$ the spectral projector of the eigenvalues within distance $<d$ of $\theta$ (not on main: `Residual.lean` has no residual-to-projector lemma) [`Matrix/Perturbation/Residual.lean`] | S | — |
| F2 | `card_ritz_mem_window_le`: residual-gated count, converged Ritz values not duplicated (S4a′) | M | F2a, E3, Weyl |
| F3 | `exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul`: Ritz-pair residual, and the non-admissible-stop corollary | S | D6 or E3 |
| F4 | `ritz_mem_Icc`: containment $[\lambda_{\min}-e,\lambda_{\max}+e]$ | S | F1 |
| F5 | `eigenvalue_zero_sub_eigenvalue_tridiagonal_le`: KPS transfer for $\mathbf H+\mathbf E$ (S4c) | M | E4, Ritz.lean |
| F6 | `gaussQuadrature_backward`: polynomial exactness for $(\mathbf H+\mathbf E,\tilde{\mathbf b})$ | M | E4, Gauss.lean |
| F7 | `abs_quadForm_cfc_sub_le`: Lipschitz-$f$ transfer to $\mathbf b^{\mathsf T}f(\mathbf H)\mathbf b$ (S4d) | M | F6, Kittaneh |
| **G1** | `lanczosReorthProg`, `lanczosReorthOracleProg` builders (CGS2), `.compiled`, `toStmt_compiled` | S | C1 |
| G2 | `lanczosReorthCount`, memory formula; `StoredEntriesLanczosReorth`, `MatrixFreeLanczosReorth` (**drafts in this note; registration by the maintainer**) | S | G1, A1 |
| G3 | proofs of the two exact targets | L | G1, G2, A1, C2 |
| G4 | `LanczosReorthProgramStaticCost`: counts and memory from the trees | M | G1 |
| G5 | scheme-generic rounded loop: `exec_rounded_reorth_work` with `orth : ℕ → Builder` + `∀ t, IsOrthRoutine` | H | B2, main's `exec_rounded_work` pattern |
| G6 | `LanczosReorthImplementation.exec_rounded_compiled` (+ oracle twin): success, outputs, cost, `LanczosReorthRun` | H | G5, C6 |
| G7 | `exec_rounded_compiled_backward`: G6 composed with E3/E4 and the start-vector bound | L | G6, E4 |
| G8 | `exec_rounded_compiled_interlacing`: G7 composed with F1/F2 (the program-level headline) | S | G7, F1, F2 |

Totals: S 27, M 14, L 5, H 2 (48). The two H items are the program bridges, as for plain Lanczos
on main, where the rounded bridge was the largest item. Critical path: B1 → C3–C5 → D5 → D3 → D4 → E3 →
F1 (the mathematics, independent of programs), in parallel with A1 → G1 → G3 and C6 → G5 → G6 → G7.

**Later stages**: MGS2 (rounded `orthAgainst`), DGKS conditional pass, threshold-stopping program
(FR4 (b)), Householder FRO and QR-kcall instances, KPS in $\mathbf A$'s data and Ritz vectors (S6),
returning the Hessenberg column (FR5 (b)), complex Hermitian data, bounded format, block FRO
(BCGS2), and then partial/selective reorthogonalization as instances that weaken S2 to
semi-orthogonality (Simon 1984b).

## 5. Decisions (sheet `LANCZOS-REORTH.json`)

* **FR1, modularity.** (a) routine family + `IsOrthRoutine` certificate, concrete CGS2 trees [rec.];
  (b) fix CGS2 throughout; (c) orthogonalization kernel via `kcall`.
* **FR2, contract form.** (a) two-term $\varepsilon_1\|\mathbf w'\|+\varepsilon_3\|\mathbf w\|$ with residual
  $\varepsilon_2$, conditional only on $\eta_0$ [rec.]; (b) absolute $\|\mathbf V^{\mathsf T}\mathbf q\|\le\varepsilon_1$
  with admissibility inside the contract; (c) a $k$-step basis-level contract.
* **FR3, first instance.** (a) CGS2 (dots + `gemv` + `axpy`) [rec.]; (b) MGS2 via `orthAgainst`;
  (c) DGKS conditional.
* **FR4, breakdown/admissibility.** (a) exact zero test, store $\nu_j$, strictly admissible prefix
  ($\tau\nu_j<\beta_j$) read off outputs; the criterion is Paige 1970's stopping criterion in substance [rec.]; (b) threshold stop in the tree; (c) hypothesis.
* **FR5, outputs.** (a) $\alpha,\beta,\mathbf V,\nu$ + main's other outputs; coefficients discarded
  and analysed [rec.]; (b) also return the coefficient columns; (c) fold $h_{jj}$ into $\alpha_j$.
* **FR6, exact spec.** (a) exact FRO recurrence, no premise, equality with `lanczosState` for
  symmetric $\mathbf A$ [rec.]; (b) target with a symmetric premise.
* **FR7, names.** (a) `lanczosReorthProg`/`lanczosReorthOracleProg`, `StoredEntriesLanczosReorth`/
  `MatrixFreeLanczosReorth`, `LanczosReorthRun`, `IsOrthErr`/`IsOrthRoutine`, algorithm tag
  `lanczos-reorth` [rec.]; (b) `…FullReorth…`.
* **FR8, backward form.** (a) mixed: $n\times n$ symmetric $\mathbf E$, $\mathbf U$ the polar factor of the
  computed basis, $\tilde{\mathbf b}=\|\mathbf b\|\mathbf u_1$, plus the pure-backward corollary E5; headline:
  interlacing up to $e$ and converged Ritz values not duplicated [rec.]; (b) Simon's projection form only.
* **FR9, scope.** (a) the 48 statements of §4 [rec.]; (b) mathematics only (A–F + C), programs later.

## References

In `docs/references.bib`: Paige1970 (added on this branch: C. C. Paige, "Practical use of the
symmetric Lanczos process with re-orthogonalization", BIT 10 (1970) 183–195,
doi:10.1007/BF01936866), Paige1976, Paige1980, Paige2010, Greenbaum1989, Parlett1998, Higham2002,
GolubMeurant2010, GolubVanLoan2013, MeurantStrakos2006, Kittaneh1985, DavisKahan1970, Saad2011.
To add at implementation (verify locators then): Simon 1984a (Math. Comp. 42, 115–142) and 1984b (LAA
61, 101–131); Parlett–Scott 1979 (Math. Comp. 33); Daniel–Gragg–Kaufman–Stewart 1976 (Math. Comp. 30,
772–795); Björck 1967 (BIT 7), Björck 1994 (LAA 197–198, 297–316); Björck–Paige 1992 (SIMAX 13);
Giraud–Langou–Rozložník–van den Eshof 2005 (Numer. Math. 101, 87–100); Giraud–Langou–Rozložník 2005
(Comput. Math. Appl. 50); Smoktunowicz–Barlow–Langou 2006 (Numer. Math. 105); Barlow–Smoktunowicz 2013
(Numer. Math. 123); Carson–Lund–Rozložník–Thomas 2022 (LAA 638); Walker 1988 (SISC 9);
Drkošová–Greenbaum–Rozložník–Strakoš 1995 (BIT 35); Paige–Rozložník–Strakoš 2006 (SIMAX 28);
Kahan–Parlett–Jiang 1982 (SINUM 19); Stewart 2002 (LAA 340); Sun 1991 (BIT 31); Chang–Paige–Stewart
1997 (SIMAX 18); Carpraux–Godunov–Kuznetsov 1996 (LAA 248); Kaniel 1966 (Math. Comp. 20).

## 6. Review changes (Fable review 2026-11-06, applied)

1 (blocker) The "no ghosts from interlacing" claim was false (counterexample in S4a′). It is replaced
by the residual-gated count F2, with the new lemma F2a; Summary, S4a and FR8 reworded. 2 Closure
constants: $\eta_0=4\sqrt{3(k+1)}c_1$, $\tau\gtrsim60(k+1)c_1$; `hsmall` is a fixed-point condition in
$(\eta_0,\tau)$ (§1.2, §3.4, §3.5). 3 E2 now uses the polar factor through Kittaneh (S); the QR route
and its size are recorded in §3.3. 4 Proof order D5 → D3 → D4; D9 dropped; the D4 $\mathbf h_i$ term
fixed. 5 Paige 1970 credited at §1.2/FR4, S1, S2, S3 and added to `docs/references.bib`; Simon 1984b
kept for S1′ and the semi-orthogonal generalization. Minor: rounded literal $-1$ (§2.2, C3); strict
admissibility and the index convention (§1.2, §3.1); S5 by two reflectors; E4 terminal case E6; `hb`
allocation, shape and `pre` in §1.3; B8 added; the $\|\mathbf v_{k+1}\|$ factor in S4b; forward reference
to $\tau_j$ in §1.1.

## 7. Skeleton (2026-11-06)

Definitions, sorry-free, in `NLAlib/` (added to `NLAlib.lean`): `IsOrthErr`
(`Matrix/Perturbation/OrthErr.lean`, Matrix layer so that the run interface does not import
Computation), `Computation.IsOrthRoutine` (`Matrix/Computation/OrthRoutine.lean`), `cgsPass`,
`cgs2`, `cgsPassBound` (`Matrix/Computation/ClassicalGramSchmidt.lean`, registered in
`docs/constants.toml`), `cgsProject`,
`LanczosReorthState`, `lanczosReorthStep`/`State`/`Matrix` (`Krylov/Processes/LanczosReorthRecurrence.lean`),
`LanczosReorthRun` with `basisOf`, `toLanczosData`, `orthLevel`, `recLevel`, `backwardRadius`,
`colSeq`, and `reorthSteps` (`Krylov/FinitePrecision/LanczosReorthRun.lean`), the generic
`lanczosReorthLoop`, the CGS2 trees `lanczosReorthProg`/`lanczosReorthOracleProg` with
`.compiled` and `toStmt_compiled` (proved by `rfl`) and the drafted count `lanczosReorthCount`
(`Krylov/Processes/LanczosReorthProgramTree.lean`), and `LanczosReorthOutputs`
(`Krylov/Processes/LanczosReorthProgramRounding.lean`). So A1, B1, B2, C1, D1 and G1 are definitions,
not targets. G2 stays a draft here: no `*Targets.lean` and no registry entry (AGENTS rule 2).

51 sorried statements in `NLAlibScaffold/` (S 30, M 15, L 5, H 1), targets file
`~/nlalib-harness/pilot/lanczos-reorth-targets.json` (`bin/check-skeleton --strict`: 0 missing
imports, 0 unresolved). Jobs: J1 Matrix layer (B3–B8, C2–C7, E1, E2, E5 rotation, F2a; 20), J2 exact
recurrence and run analysis (A2, A3, D2–D8, prefixes; 12), J3 backward model and spectral
consequences (E3–E5, F1–F7; 12), J4 programs (G3–G8; 7). Order: J1 → J2 → J3; J4's G3–G6 after J1,
G7–G8 after J3.

Changes from §4 made while writing exact statements:

* Several rows became two declarations (B6, B7, B8, E2, F1, F3; the rotation of E5 is its own
  Matrix lemma; the per-column lemma D5a and A2's basis corollary are separate; G6 has an oracle
  twin). Hence 51 statements instead of 48.
* The common hypotheses are `η₀ ≤ 1/100` (not $1/4$), the fixed-point condition
  `√(3(k+1)) * orthLevel ≤ η₀`, and for the coefficient bounds `recLevel ≤ 1/100` and `τ ≤ 1`, with
  `orthLevel = 2(ε₁ + ε₃/τ + ε)` and `recLevel = orthLevel + ε + ε₂`. The constants are generous
  sketch values: D3 $\tfrac32$, D4 $24\sqrt{j+1}$, D6 $30(k+1)$, D7 $50(k+1)$, backward radius
  $100(k+1)$, CGS2 $(2c_1, 3c_1, 2(\eta_0+c_1)^2)$ with
  $c_1 = 2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$ (Fable outline review: D4 was $16\sqrt{j+1}$, which
  a straightforward accounting misses by a hair at $j = 1$; D6, D7 follow).
* E2's bound is $\|\mathbf U - \mathbf V\|_F \le \|\mathbf G - \mathbf I\|_F/(2\sqrt{1-\eta})$, the
  Lipschitz constant of $\sqrt{\cdot}$ on $[1-\eta, 1+\eta]$ that Kittaneh gives (the
  $1/(1+\sqrt{1-\eta})$ of §3.3 needs the eigenvalue sum directly; nothing downstream needs it).
  The rotation lemma of E5 also returns $\|\mathbf Z - \mathbf I\|_F \le \sqrt2\|\mathbf x - \mathbf y\|$,
  which the pure-backward bound uses (no rank lemma is on main).
* In the drafted target of §2.3 the `nu` buffer holds `(lanczosReorthState A b (j + 1)).nu` at
  index `j` (the norm computed at step `j` is a field of the next state); the skeleton's G3 has it.
* E6 (terminal $\beta_k = 0$) is replaced by `LanczosReorthRun.exists_ofLE` (prefixes are runs).
  Strict admissibility of every step of the run, the last one included, makes $\beta_k > 0$, so
  the terminal case cannot occur inside a run.
* G3 is the exact `exec` theorem with the target's output clause, not the target proof.
* G6 is L, not H: the generic loop G5 (H) carries the work.
* The spectral results use the Frobenius radius `backwardRadius` ($\ge \|\mathbf E\|_2$).
* `lakefile.toml` gains the `NLAlibScaffold` lean_lib, as the other stage branches do.

**Update (full build).** The skeleton first added its own `polarFactor`, which clashed with main's
`NLAlib.polarFactor A = A * pinv (CFC.sqrt (Aᴴ * A))` (`Matrix/Factorizations/Polar.lean`). The
duplicate is deleted. E2–E4 use main's definition, which for full column rank is
$\mathbf{V}(\mathbf{V}^{\mathsf{T}}\mathbf{V})^{-1/2}$. E2's orthonormality is now
`hasOrthonormalCols_polarFactor_iff` plus the injectivity lemma B7, and its bound starts from
`polarFactor_mul_sqrt`. The statements are unchanged.

## 8. End of stage (2026-11-06): status, proof routes, statement changes, layout

**Status.** All 51 statements of §7 are proved, sorry-free, and live in `NLAlib`;
`NLAlibScaffold` is removed and `lakefile.toml` is main's again. `#print axioms` of all 51:
`propext`, `Classical.choice`, `Quot.sound`. Branch `cleanup/reorth`.

**C3, as proved** (`Computation.IsRelErrSem.exec_cgsPass`, `ClassicalGramSchmidtProgram.lean`).
The route is not the $\gamma_N$ forward bound of §3.3 but a partial-sum trace: every rounded
dot and every row of the rounded `gemv` is an `IsDotTrace` (main's kernel lemmas), and
`IsDotTrace.abs_sub_sum_le_partial`, `IsDotTrace.abs_sub_mulVec_le`
(`ClassicalGramSchmidtRoundingError.lean`) bound the error by
$(1+u)^n u\bigl((\lvert\mathbf A\rvert\lvert\mathbf x\rvert)_i + \sum_{r<n}\lvert(\mathbf A\mathbf x_{\le r})_i\rvert\bigr)$;
summed over rows this is $\le (100/99)\,u(\|\mathbf A\|_{\mathsf F} + n\|\mathbf A\|_2)\|\mathbf x\|$,
with $(1+u)^n \le 100/99$ from $(N+j+2)u \le 1/100$ and $a = \sqrt{1+\eta_0} \ge \|\mathbf V\|_2$,
$\|\mathbf V\|_{\mathsf F} \le \sqrt j\,a$. Hence the dots satisfy
$\|\mathbf h_1 - \mathbf V^{\mathsf T}\mathbf w\| \le (100/99)\,u\,a(\sqrt j + N)\|\mathbf w\|$, the `gemv`
$\|\mathbf y - \mathbf V\mathbf h_1\| \le (100/99)\,u\,a(\sqrt j + j)\|\mathbf h_1\|$, and the `axpy`
with the rounded literal $-1$ adds $3.1u\|\mathbf y\| + u\|\mathbf w\|$; `cgsPass_arith` collects
everything under $c_1 = 2a^2\sqrt{j+1}\,(N+j+2)\,u$ = `cgsPassBound`. The proof uses
$\eta_0 \ge 0$ only (through $a$); the hypothesis $\eta_0 \le 1/100$ and the conjunct `wb ≠ Vb`
of the distinctness hypothesis, which it did not use, are dropped (maintainer decision S3,
2026-11-06; C3 is strictly stronger, its callers C6 and the programs are unchanged). C2, the exact run, is now derived from the rounded run at $u = 0$, where the bounds force
the exact values.

**G5, as proved** (`LanczosReorthImplementation.exec_rounded_loop`,
`LanczosReorthProgramRoundedLoop.lean`). The scoped lemma `exec_lanczosReorthLoop` is
instantiated with the guarantee `IsOrthErr`. The three scoped allocations give an 11-buffer
workspace; `exec_initPhase` writes the zeros, the input norm and the guarded $\mathbf v_1$;
`exec_loop` runs the $q$ steps under the invariant "`StoreContext` after $t$ steps, input norm
kept, `RoundedSteps` for $j < t$". A step (`exec_stepBody`, `LanczosReorthProgramRoundedStep.lean`)
has three phases: the work phase (product, the two Paige updates, $\alpha$ and $\nu$), the
certified orthogonalization call and $\beta$, and the commit (copy of the previous vector and
guarded normalization). Main's normalization lemmas need unit charges; the new
`Computation.exists_exec_withCharge_eq_some` (`Computation/ExecCharge.lean`) transfers a
run to any charge. The per-step witnesses are assembled into a `LanczosReorthRun` for every
admissible prefix; $\|\mathbf v_{j+2}\|$ near $1$ follows from $\beta > \tau\nu \ge 0$.

**Statement changes during proving and clean-up** (none weakens a conclusion):
* G5 `exec_rounded_loop`: the orthogonalization certificate is required only for the executed
  steps, `∀ t < q` instead of `∀ t` (strictly stronger; replaces the provers' private variant).
  Earlier, during proving (08aa72a5): `hpreFrame` transports `pre` along the first 8 shape entries
  instead of equal shapes, because `mv` runs in the 11-buffer workspace (the old form could not be
  discharged).
* G6, G6o, G7, G8: the unused hypothesis `hc : ∀ k, I.charge k = Finsupp.single k 1` is dropped
  (the conclusions have no cost clause).
* G7, G8 (stage review, ccbc59a9): the prefix run $L$ comes with its parameters
  ($L.\varepsilon$, $L.\tau$, $L.\eta_0$, $L.\varepsilon_{1,2,3}$ equal to the CGS2 ones), so the
  fixed-point premise $\sqrt{3(m+1)}\,\mu \le \eta_0$ is about known quantities (strictly stronger).
* `Computation.exists_exec_eq_some_of_exec_eq_some` → `exists_exec_withCharge_eq_some`
  (decision S4: the name says charge; the file `Computation/ExecCharge.lean` is kept).
* C3 `IsRelErrSem.exec_cgsPass` (decision S3): `η₀ ≤ 1/100` and `wb ≠ Vb` dropped (unused).
* Unused hypotheses dropped: `IsOrthErr.norm_coef_le` (`hε₂`), `isOrthErr_of_one_pass` and
  `norm_transpose_mulVec_le_of_norm_sub_le` (`hc₁`), `LanczosReorthRun.coeff_le` (`hτ`).
* F6 `exists_pure_backward_gauss`: the proof term `⟨0, L.k_pos⟩` in the statement (rule T9) is the
  new definition `LanczosReorthRun.firstIndex`; definitionally the same statement.
* Renames for the name checker: `…_gram_sub_one_…` → `…_transpose_mul_self_sub_one_…` (N5: B6,
  B7, B8, D5), `norm_transpose_mulVec_cgsPass_le` → `norm_transpose_mulVec_le_of_norm_sub_le`
  (N4, C4), `exists_transpose_eq_mul_eq_neg_of_hasOrthonormalCols` →
  `HasOrthonormalCols.exists_transpose_eq_mul_eq_neg` and
  `card_le_card_eigenvalue_mem_of_hasOrthonormalCols` → `Matrix.IsHermitian.…` (N18: E1, F2a).

**Layout** (lines):
* Matrix layer: `Matrix/Perturbation/OrthErr.lean` 271 (B1, B3–B8),
  `Matrix/Perturbation/SymmetricBackward.lean` 391 (E1, E2, the rotation of E5, F2a),
  `Matrix/Computation/ClassicalGramSchmidt.lean` 307 (C1, `cgsPassBound`, C4, C5, C7),
  `ClassicalGramSchmidtRoundingError.lean` 475 (the norm analysis of one rounded pass),
  `ClassicalGramSchmidtProgram.lean` 787 (C2, C3, C6), `OrthRoutine.lean` (B2).
* Computation: `Computation/ExecCharge.lean` 173 (runs that differ only in their charges).
* Krylov: `Processes/LanczosReorthRecurrence.lean` 305 (A1–A3);
  `FinitePrecision/LanczosReorthRun.lean` 460 (D1, D2, D5, D8, prefixes),
  `LanczosReorthCoefficients.lean` 743 (D3, D4), `LanczosReorthResidual.lean` 315 (D6, D7),
  `LanczosReorthBackward.lean` 403 (E3–E5), `LanczosReorthSpectral.lean` 479 (F1–F7);
  `Processes/LanczosReorthProgramTree.lean` (G1), `…Rounding.lean` (outputs),
  `…RoundedStep.lean` 815 (one step), `…RoundedLoop.lean` 641 (G5),
  `LanczosReorthProgram.lean` 430 (G3, G4), `…Rounded.lean` 308 (G6, G6o, G7, G8).

**Open.** The fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$ stays a hypothesis of the
run-level and program-level results (G7, G8 assume it for the prefix); a theorem that discharges
it from explicit bounds on $u$, $N$, $k$, $	au$ for CGS2 (§3.4) is not part of this stage. G2
(targets, registration) is the maintainer's.

