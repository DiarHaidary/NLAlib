# Lanczos with full reorthogonalization in finite precision

2026-11-06. Design note, no proofs yet. Branch `design/lanczos-reorth` from `origin/main` @
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
  so no dilation is needed; (S4) consequences: interlacing up to $\|\mathbf E\|$ and therefore no
  ghost Ritz values, Ritz residuals, transfer of Kaniel–Paige–Saad and of Gauss quadrature. All are
  known in substance (Simon 1984; Giraud–Langou–Rozložník–van den Eshof 2005; Kahan–Parlett–Jiang
  1982). The explicit theorems with constants, in this contract form, are planned. Forward
  statements about $\mathcal K_k(\mathbf A,\mathbf b)$ or about the exact $\mathbf T_k(\mathbf A,\mathbf b)$
  are out of reach because they are false in general (§3.6).
* **First stage**: 46 statements (S 24, M 15, L 5, H 2), §4.

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
| `gramSchmidtQ`, `gramSchmidtR`, `IsQR`, `orthAgainst`, `mgsSweep`, `gramSchmidtProg` | `Matrix/Factorizations/GramSchmidt*.lean`, `QR.lean` | orthonormalization of the computed basis (E2); MGS2 instance later |
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
| CGS (one pass) | $c_1$ | $\approx\eta_0+c_1$ (first order) | $\mu_j\lesssim c_1+(\eta_j+c_1)/\tau_j$: orthogonality decays with the cancellation $1/\tau$, $O(u\kappa^2)$ for QR | Giraud–Langou–Rozložník–van den Eshof 2005 Thm 1; Smoktunowicz–Barlow–Langou 2006 |
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
$\tau\nu_j\le\beta_j$, a comparison of two stored outputs. The analysis covers the steps up to the first
non-admissible one, $k=$ `reorthSteps τ ν β q` (the analogue of `lanczosSteps` in the earlier design).
Two facts justify reading $k$ off the outputs:

* (B7/D8, planned, S) if $\eta<1$ then $\mathbf V_{k+1}$ has full column rank, so the admissible
  prefix has $k+1\le n$ whenever $\beta_k\ne0$. Full reorthogonalization "terminates" by step $n$
  for this reason alone.
* (F3) if the prefix stops at a non-admissible step, then $\beta_k<\tau\nu_k\le\tau c\|\mathbf A\|$.
  The computed space is then nearly invariant: every Ritz value is within $\tau c\|\mathbf A\|+\|\mathbf E\|$
  of an eigenvalue. This is the numerical form of a lucky breakdown.

For CGS2, $\eta_0=2\sqrt{3k}\,c_1$ and $\tau\ge 50\,k\,c_1$ make $\varepsilon_3/\tau\le c_1$ and close the
induction with $\mu\le 3c_1+\gamma_{N+4}$ (sketch values). So the threshold is a tiny multiple of $u$
($\approx 50k^{3/2}(N+k)u$). Steps that fail it are the ones where $\mathbf z_j$ is numerically in the
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
    HoldsDecoded st.store dec tag Vb 0 V → (decoded w at wb, wo) → (hb writable for j cells) →
    ∃ (out : St P K C) (W : Fin N → K) (Hw : Fin j → K),
      exec I routine.run st = some out ∧
      (out.store = the two block writes of W at (wb, wo) and Hw at (hb, ho), nothing else) ∧
      IsOrthErr η₀ ε₁ ε₂ ε₃ V w (dec tag ∘ Hw) (dec tag ∘ W)
```

The Lanczos proofs take `orth : ℕ → Builder P ι ℕ ℕ Unit` and
`horth : ∀ t, IsOrthRoutine I dec tag N (t+1) (η₀ t) (ε₁ t) (ε₂ t) (ε₃ t) pre 1 7 hb 0 (·) (orth t)`.
This is the same pattern as `hmv : ∀ t, IsMatvecRoutine … (mv t)` in
`LanczosImplementation.exec_rounded_work`.

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

It uses only kernels on main. The literal $-1$ is exact (`lit_err` with integer literal; or use `un
.neg` on a copied cell as main's `lanczosProg` does, which avoids any literal rounding question).
An exact negation is preferred, so that the proof reuses the plain-Lanczos `roundedUpdate` pattern.

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

Every data operation of the trees is a rounded kernel instruction. Mathematical objects ($\mathbf U$ from
`gramSchmidtQ` of the decoded basis, $\mathbf E$, $\mathbf G$) appear only in theorem statements and
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
* `admissible`: $\tau\nu_j\le\beta_j$ for $j<k$ (true by the definition of $k$);
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
| S2 | **Orthogonality of the admissible prefix** $\|\mathbf V_{k+1}^{\mathsf T}\mathbf V_{k+1}-\mathbf I\|_F\le\sqrt{3(k+1)}\,\mu$, $\mu=\max_j(\varepsilon_1+\varepsilon_3/\tau+\gamma_{N+4})$ | contract, admissibility, $\sqrt{3(k+1)}\mu\le\eta_0$ | for CGS2: $\mu\approx 3c_1$ | known for CGS2 as a QR statement (Giraud et al. 2005 Thm 2); planned here from the contract | M | B6 |
| S1 | **Perturbed Lanczos relation** $\mathbf A\mathbf V_k=\mathbf V_k\mathbf T_k+\beta_k\mathbf v_{k+1}\mathbf e_k^{\mathsf T}+\mathbf F_k$, $\|\mathbf F_k\|_F\le c_F\,k(\mu+\varepsilon)\|\mathbf A\|$, including the discarded coefficients | S2, $\mathbf A$ symmetric | $\|\mathbf h_j\|\lesssim\sqrt j(5\mu+2\varepsilon)\|\mathbf A\|$ (D4) | known in substance (Paige 1976 for the rounding part; Simon 1984b for reorthogonalized variants); planned | L | `LanczosData.mul_basis`, `LocalErrors`-style coefficient bounds |
| S1′ | **Projection form** $\|\mathbf V_k^{\mathsf T}\mathbf A\mathbf V_k-\mathbf T_k\|\le c(\mu\|\mathbf A\|+\|\mathbf F_k\|)$ | S1, S2 | — | known (Simon 1984b, semi-orthogonality suffices) | S | — |
| S3 | **$n\times n$ symmetric backward model.** With $\mathbf U=$ `gramSchmidtQ` $\mathbf V_{k+1}$ (orthonormal, $\mathbf u_1=\mathbf v_1/\|\mathbf v_1\|$), some symmetric $\mathbf E$ satisfies $(\mathbf A+\mathbf E)\mathbf U_k=\mathbf U_k\mathbf T_k+\beta_k\mathbf u_{k+1}\mathbf e_k^{\mathsf T}$ exactly, and $\|\mathbf E\|_F\le\sqrt2\bigl((\|\mathbf A\|+\|\underline{\mathbf T}_k\|)\|\mathbf U-\mathbf V\|_F+\|\mathbf F_k\|_F\bigr)$; hence $\mathbf T_k=$ `lanczosTridiagonal` $(\mathbf A+\mathbf E)$ $\mathbf u_1$ | S1, S2, $\beta_j>0$ for $j<k$ | $\|\mathbf E\|_F=O(k\mu\|\mathbf A\|)$ | known in substance (Simon 1984b; Stewart 2002 for Krylov decompositions; Paige 2010 for the plain case, by augmentation); this statement planned | L | E1, E2, `lanczosState_eq_of_orthonormal_recurrence` |
| S4a | **Interlacing up to $\|\mathbf E\|$, no ghosts**: $\lambda_{i+n-k}(\mathbf A)-e\le\theta_i\le\lambda_i(\mathbf A)+e$; for an eigenvalue with gap $>2e$, at most its multiplicity of Ritz values in the gap window | S3 | $e=\|\mathbf E\|_2$ | follows from S3 + Poincaré + Weyl (proved on main); the qualitative statement is known (Simon 1984b; Parlett 1998 Ch. 13) | S | Interlacing, Weyl |
| S4b | **Ritz pairs**: each Ritz value has an eigenvalue of $\mathbf A$ within $(\beta_k|s_k|+\|\mathbf F_k\|)/\|\mathbf V_k\mathbf s\|$, and within $\beta_k|s_k|+e$ | S1 or S3 | — | known (Paige 1980 for plain; standard) | S | `exists_abs_eigenvalue_sub_mul_norm_le` |
| S4c | **Kaniel–Paige–Saad transfer**: the proved KPS bound for $(\mathbf A+\mathbf E,\mathbf u_1)$, with the hypothesis intervals widened by $e$ | S3, gap $>2e$ | the bound of `eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le` for $\mathbf A+\mathbf E$, plus $e$ | planned (direct); stating the tangent in $\mathbf A$'s data needs Davis–Kahan, later | M | Ritz.lean, Weyl |
| S4d | **Gauss quadrature / SLQ transfer**: $\|\tilde{\mathbf b}\|^2\mathbf e_1^{\mathsf T}p(\mathbf T_k)\mathbf e_1=\tilde{\mathbf b}^{\mathsf T}p(\mathbf A+\mathbf E)\tilde{\mathbf b}$ for $\deg p\le2k-1$, and for $L$-Lipschitz $f$, $|\tilde{\mathbf b}^{\mathsf T}f(\mathbf A+\mathbf E)\tilde{\mathbf b}-\mathbf b^{\mathsf T}f(\mathbf A)\mathbf b|\le L\|\mathbf E\|_F\|\mathbf b\|^2+2\|f\|_\infty\|\mathbf b\|\|\tilde{\mathbf b}-\mathbf b\|$ | S3 | — | exactness is classical (Golub–Meurant 2010); the transfer is planned via Kittaneh (proved) | M | Gauss.lean, `frobNorm_cfc_sub_cfc_le` |
| S5 | **Pure backward form** (exact $\mathbf b$): an orthogonal $\mathbf Z$ with $\mathbf Z\mathbf u_1=\mathbf b/\|\mathbf b\|$, $\|\mathbf Z-\mathbf I\|\le2\|\mathbf u_1-\mathbf b/\|\mathbf b\|\|$; $\mathbf A'=\mathbf Z(\mathbf A+\mathbf E)\mathbf Z^{\mathsf T}$, $\|\mathbf A'-\mathbf A\|\le e+4\|\mathbf A\|\cdot O(u)$ | S3 + start-vector bound | — | standard construction; planned | M | Householder.lean |
| S6 | Ritz vector angles via Davis–Kahan | S3/S4b, gap | — | known (standard); later | M | DK |

The **payoff over plain Lanczos** is S3 and S4a. Main's plain-Lanczos model is a dilation of size
$n(k+1)$ with $400q^3\varepsilon\|\mathbf A\|$ (or $1000q^2\varepsilon$). It cannot give interlacing
with the spectrum of $\mathbf A$: ghost copies are real in plain finite-precision Lanczos (Paige 1971;
Greenbaum 1989). With full reorthogonalization the model has size $n\times n$ and the Ritz values
interlace $\mathbf A$'s eigenvalues up to $e$. The dimension count $k+1\le n$ is automatic.

### 3.3 Proof sketches

**D4, the coefficient lemma (the one place symmetry is needed).** Write the computed relation as
$\mathbf A\mathbf v_j=\beta_{j-1}\mathbf v_{j-1}+\alpha_j\mathbf v_j+\mathbf V_j\mathbf h_j+\beta_j\mathbf v_{j+1}+\mathbf f_j$.
By B4, $\|\mathbf h_j\|$ is controlled by $\|\mathbf V_j^{\mathsf T}\mathbf z_j\|$, so bound each component $\mathbf v_i^{\mathsf T}\mathbf z_j$:

* $i\le j-2$: $\mathbf v_i^{\mathsf T}\mathbf A\mathbf v_j=(\mathbf A\mathbf v_i)^{\mathsf T}\mathbf v_j$ by symmetry. Expand $\mathbf A\mathbf v_i$ by the relation at step $i$. Every resulting inner product with $\mathbf v_j$ is an off-diagonal Gram entry ($\le\mu$), apart from $\mathbf h_i^{\mathsf T}\mathbf V_i^{\mathsf T}\mathbf v_j$ ($\le\|\mathbf h_i\|\sqrt i\,\mu$, second order) and $\mathbf f_i^{\mathsf T}\mathbf v_j$. So $|\cdot|\le 5\|\mathbf A\|\mu+\sqrt i\,\mu\|\mathbf h_i\|+\|\mathbf f_i\|$.
* $i=j-1$: the $\beta_{j-1}$ terms cancel up to $\beta_{j-1}(\|\mathbf v_j\|^2-\|\mathbf v_{j-1}\|^2)=O(\varepsilon\|\mathbf A\|)$.
* $i=j$: $\mathbf v_j^{\mathsf T}\mathbf z_j=\alpha_j(1-\|\mathbf v_j\|^2)+O(\varepsilon)=O(\varepsilon|\alpha_j|)$.

Induction on $j$ under $j\mu\le1/4$ gives $\|\mathbf h_j\|\le c_h\sqrt j(\mu+\varepsilon)\|\mathbf A\|$. The
coefficient bounds $|\alpha_j|,\beta_j\le(1+O(\eta))\|\mathbf A\|+\ldots$ first come out crude ($\tfrac54 j$-type, as
in main's `LocalErrors`) and are then sharpened through S1′. Without symmetry the components
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
For E2 (planned, M; Sun 1991, Chang–Paige–Stewart 1997, locators to verify): $\mathbf V=\mathbf U\mathbf R_{\rm GS}$ with
$\mathbf R_{\rm GS}^{\mathsf T}\mathbf R_{\rm GS}=\mathbf G$ and $\mathbf R_{\rm GS}$ upper triangular with positive diagonal. Writing
$\mathbf R_{\rm GS}=\mathbf I+\boldsymbol\Delta$ gives
$\|\mathbf U-\mathbf V\|_F=\|\boldsymbol\Delta\|_F\le\|\mathbf G-\mathbf I\|_F/(1-\|\mathbf G-\mathbf I\|_2)$
(the upper part of $\boldsymbol\Delta+\boldsymbol\Delta^{\mathsf T}+\boldsymbol\Delta^{\mathsf T}\boldsymbol\Delta$).
QR is used instead of the polar factor because it keeps $\mathbf u_1\parallel\mathbf v_1$, i.e. the start
vector. E4: `lanczosState_eq_of_orthonormal_recurrence` on $(\mathbf A+\mathbf E,\mathbf u_1)$ with $\beta_j>0$
($j<k$, from admissibility) gives the exact Lanczos tridiagonal.

**C3–C5, CGS2 meets the contract (planned, M each).** One pass, from main's kernel lemmas:
$\mathbf h_1=\mathbf V^{\mathsf T}\mathbf w+\mathbf e_h$ with $|\mathbf e_h|\le\gamma_N|\mathbf V|^{\mathsf T}|\mathbf w|$, and
$\mathbf w'=\mathbf w-\mathbf V\mathbf h_1+\mathbf e$ with $|\mathbf e|\le\gamma_{j+1}(|\mathbf w|+|\mathbf V||\mathbf h_1|)$. Using
$\|\mathbf V\|_F\le\sqrt{j(1+\eta_0)}$ this gives $\mathbf w'=(\mathbf I-\mathbf V\mathbf V^{\mathsf T})\mathbf w+\mathbf f_1$ with
$\|\mathbf f_1\|\le c_1\|\mathbf w\|$, $c_1\approx\sqrt j(N+j+2)u$. Then
$\mathbf V^{\mathsf T}\mathbf w'=(\mathbf I-\mathbf V^{\mathsf T}\mathbf V)\mathbf V^{\mathsf T}\mathbf w+\mathbf V^{\mathsf T}\mathbf f_1$, so
$\|\mathbf V^{\mathsf T}\mathbf w'\|\le\sqrt{1+\eta_0}(\eta_0+c_1)\|\mathbf w\|$: one pass meets the contract with
first-order $\varepsilon_3$ (C7). A second pass on $\mathbf w'$ gives
$\|\mathbf V^{\mathsf T}\mathbf w''\|\le\eta_0\|\mathbf V^{\mathsf T}\mathbf w'\|+\sqrt{1+\eta_0}\,c_1\|\mathbf w'\|$, and
$\|\mathbf w'\|\le(\|\mathbf w''\|+(1+\eta_0)(\eta_0+c_1)\|\mathbf w\|)/(1-c_1)$. So
$\varepsilon_1\approx c_1$ and $\varepsilon_3\approx(\eta_0+c_1)^2$. The residual relation sums the two
passes plus the rounding of $\mathbf h_1+\mathbf h_2$: $\varepsilon_2\approx2c_1+u(1+\eta_0)$. All ingredients
except the algebra are on main.

### 3.4 Constants, to first order (sketch; fixed by proofs)

$c_1\approx\sqrt k(N+k)u$, $\mu\approx3c_1$, $\|\mathbf V^{\mathsf T}\mathbf V-\mathbf I\|_F\lesssim 5k(N+k)u$,
$\|\mathbf F_k\|_F\lesssim c\,k^{3/2}(N+k)u\|\mathbf A\|$, $\|\mathbf E\|_F\lesssim c\,k^{3/2}(N+k)u\|\mathbf A\|$, with
admissibility threshold $\tau\approx50k^{3/2}(N+k)u$. For comparison, Giraud et al. (2005) prove
$O(mn^{3/2})u$ loss for CGS2 QR. Practical FRO behaves like $O(\sqrt k\,u)$ (conjectured; we do not
claim it).

### 3.5 Dependencies of hypotheses

* `hsmall`: $\sqrt{3(k+1)}\mu\le\eta_0\le1/4$ and $k(\mu+\varepsilon)\le1/100$-type. These are
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

46 statements in 8 groups. Files in brackets. A: Krylov layer. B, C: Computation/Matrix layer.
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
| B6 | `frobNorm_gram_sub_one_sq_eq`: the column-append identity, and `frobNorm_gram_sub_one_le` ($\sqrt{3m}\mu$) | S | — |
| B7 | `injective_of_specNorm_gram_sub_one_lt_one` and the corollary $m\le n$ | S | — |
| **C1** | `cgsPass`, `cgs2` builders (§2.2) [`Matrix/Computation/CGS2.lean`] | S | — |
| C2 | `exec_cgs2_exactInterp`: in exact arithmetic, the two passes compute $(\mathbf I-\mathbf V\mathbf V^{\mathsf T})$ twice and $\mathbf h=\mathbf V^{\mathsf T}\mathbf w+\mathbf V^{\mathsf T}(\mathbf I-\mathbf V\mathbf V^{\mathsf T})\mathbf w$ (any $\mathbf V$) | M | C1 |
| C3 | `IsRelErrSem.exec_cgsPass`: decoded $\mathbf w'=(\mathbf I-\mathbf V\mathbf V^{\mathsf T})\mathbf w+\mathbf f_1$, $\mathbf h_1=\mathbf V^{\mathsf T}\mathbf w+\mathbf e_h$, explicit $c_1$ (`cgsPassBound N j u η₀`) | M | C1, kernel lemmas |
| C4 | `norm_transpose_mulVec_cgsPass_le`: $\|\mathbf V^{\mathsf T}\mathbf w'\|\le\sqrt{1+\eta_0}(\eta_0+c_1)\|\mathbf w\|$ | S | C3 |
| C5 | `isOrthErr_cgs2`: CGS2 meets `IsOrthErr` with $(\varepsilon_1,\varepsilon_2,\varepsilon_3)$ explicit | M | C3, C4 |
| C6 | `IsRelErrSem.isOrthRoutine_cgs2`: the certificate (success, frames, composable) | L | C5, `ScalarFrames` |
| C7 | `isOrthErr_cgsPass`: one pass meets the contract with first-order $\varepsilon_3$ (documents why one pass is not enough) | S | C4 |
| **D1** | `LanczosReorthRun n k` (def, §3.1), `reorthSteps τ ν β q` (def) [`LanczosReorthRun.lean`] | S | B1 |
| D2 | `LanczosReorthRun.toLanczosData`; `recurrenceError_eq`: $\mathbf f_j+\mathbf V_j\mathbf h_j$ | S | D1 |
| D3 | coefficient bounds `abs_α_le`, `β_le`, `norm_z_le` (crude, $j$-growth) | M | D1 |
| D4 | `norm_coef_le`: $\|\mathbf h_j\|\le c_h\sqrt j(\mu+\varepsilon)\|\mathbf H\|$ (symmetric $\mathbf H$, induction) | L | B4, D3, D5 |
| D5 | `frobNorm_gram_sub_one_le`: S2 on the admissible prefix | M | B5, B6 |
| D6 | `frobNorm_residual_le`: S1 | M | D2, D4 |
| D7 | `specNorm_transpose_mul_mul_sub_tridiagonal_le`: S1′ | S | D5, D6 |
| D8 | `steps_succ_le_card`: $k+1\le n$ when $\beta_k\ne0$ | S | B7, D5 |
| D9 | sharpened coefficient bounds $|\alpha_j|,\beta_j\le(1+c\,\eta)\|\mathbf H\|+c\|\mathbf F\|$ | M | D7 |
| **E1** | `exists_symm_mul_eq_neg`: the symmetric completion, $\|\mathbf E\|_F\le\sqrt2\|\mathbf R\|_F$ [`Matrix/Perturbation/SymmetricBackward.lean`] | S | — |
| E2 | `frobNorm_gramSchmidtQ_sub_le`: $\|\mathbf U-\mathbf V\|_F\le\|\mathbf G-\mathbf I\|_F/(1-\|\mathbf G-\mathbf I\|_2)$ | M | `GramSchmidt`, `QR` |
| E3 | `LanczosReorthRun.exists_backward`: S3's identity and bound [`LanczosReorthBackward.lean`] | L | D6, D5, E1, E2 |
| E4 | `lanczosTridiagonal_backward`: $\mathbf T_k=$ exact Lanczos of $(\mathbf H+\mathbf E,\mathbf u_1)$ | M | E3, `lanczosState_eq_of_orthonormal_recurrence` |
| E5 | `exists_orthogonal_mulVec_eq` + pure-backward corollary (S5) | M | E3, `Householder` |
| **F1** | `eigenvalue_tridiagonal_le_add`, `le_eigenvalue_tridiagonal_add`: interlacing up to $e$ [`LanczosReorthSpectral.lean`] | S | E4, Interlacing, Weyl |
| F2 | `card_ritz_gt_le`: no ghosts (count in a gap window) | S | F1 |
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

Totals: S 24, M 15, L 5, H 2 (46). The two H items are the program bridges, as for plain Lanczos
on main, where the rounded bridge was the largest item. Critical path: B1 → C3–C5 → D5/D4 → E3 →
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
* **FR4, breakdown/admissibility.** (a) exact zero test, store $\nu_j$, admissible prefix read off
  outputs [rec.]; (b) threshold stop in the tree; (c) hypothesis.
* **FR5, outputs.** (a) $\alpha,\beta,\mathbf V,\nu$ + main's other outputs; coefficients discarded
  and analysed [rec.]; (b) also return the coefficient columns; (c) fold $h_{jj}$ into $\alpha_j$.
* **FR6, exact spec.** (a) exact FRO recurrence, no premise, equality with `lanczosState` for
  symmetric $\mathbf A$ [rec.]; (b) target with a symmetric premise.
* **FR7, names.** (a) `lanczosReorthProg`/`lanczosReorthOracleProg`, `StoredEntriesLanczosReorth`/
  `MatrixFreeLanczosReorth`, `LanczosReorthRun`, `IsOrthErr`/`IsOrthRoutine`, algorithm tag
  `lanczos-reorth` [rec.]; (b) `…FullReorth…`.
* **FR8, backward form.** (a) mixed: $n\times n$ symmetric $\mathbf E$ and $\tilde{\mathbf b}=\|\mathbf b\|\mathbf u_1$,
  plus the pure-backward corollary E5 [rec.]; (b) Simon's projection form only.
* **FR9, scope.** (a) the 46 statements of §4 [rec.]; (b) mathematics only (A–F + C), programs later.

## References

In `docs/references.bib`: Paige1976, Paige1980, Paige2010, Greenbaum1989, Parlett1998, Higham2002,
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
