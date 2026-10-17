# Design note: Krylov stage K1, linear systems

Status: 2026-10-17, revised after an independent review (every statement found true) and the
maintainer's additions A to C. Drafted from `docs/PORT_KRYLOV.md` (D1 to D12) and
`docs/design/Krylov-CG.md`, after K0 was proved (`ebfa556`). The statements live in the skeleton
`~/Documents/NLA-lib/krylov-scratch/skeleton-k1/NLAlib/`, one file per planned library file
(files marked `skeleton: additions` hold only what is added to an existing file; `CG.lean`,
`CGRecurrence.lean`, `CGLanczos.lean` are edited copies). No repository Lean file was touched.
`check/concat.py` joins the files in import order into `check/All.lean` (autoImplicit off, the
long-line and unused-instance linters on), checked with `lake env lean`: 151 `sorry` warnings
and nothing else; `scripts/check_latex.mjs` on the skeleton: 259 docstrings, 0 problems. The
files are the specification; this note gives names, claims, proof plans and decisions.

## Summary: what the maintainer gets

- `cgIterate A b x₀ q` with a start; PCG, GMRES and preconditioned MINRES defined the same way,
  basis-free, with the preconditioner applied as `M` and never factored.
- Every rate in $\kappa = a'/a$ on `Set.Icc a a'`: $2\rho^q$, squared $4\rho^{2q}$, with
  $\rho = \frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}$; outlier bounds; spectrum-optimal bounds
  through `residualMinimax`; CGLS in $\kappa(\mathbf{A})$.
- Sharpness: explicit matrices and right-hand sides on which CG and MINRES attain
  $T_q(\frac{a'+a}{a'-a})^{-1} = \frac{2\rho^q}{1+\rho^{2q}}$, on $[a, a']$ and on
  $[-a', -a] \cup [a, a']$.
- Realisations: preconditioned Hestenes–Stiefel (one $\mathbf{M}$ per step), MGS Arnoldi,
  preconditioned Lanczos, GMRES through Arnoldi plus Givens QR and back substitution, and the
  Paige–Saunders MINRES recurrence, each proved equal to its mathematical definition.
- Givens QR of Hessenberg and tridiagonal matrices in `Matrix/Factorizations/Givens.lean`, beside
  `Householder.lean`, with its realisation (`IsQR`) and the progressive least-squares form.

## 0. The request

The maintainer, verbatim: "cg should allow an initial guess. Define preconditioned CG and
preconditioned HS implementation (that does a single apply per iteration rather than using the
square root). For the convergence bound, I want it in the kappa form b/a and make the right
endpoint b. Do the similar thing for MINRES and then add Arnoldi and GMRES. ... Throughout, keep in
mind where new functions should be placed in the library."

Corrections and additions since, verbatim: "right hand side vector remains b. a' and a is fine";
"also add the 'killing off eigenvalues' bound"; "yes, but make sure givens is in the right
place". So: the right-hand side is `b`, the interval `Set.Icc a a'`, $\kappa = a'/a$; outlier
bounds for CG, PCG, MINRES; the Paige–Saunders recurrence and the Givens solution of the GMRES
problem are in this round, with Givens QR in `Matrix/Factorizations/Givens.lean`; a
spectrum-optimal bound (B); and instances attaining the Chebyshev bound (C).

## 1. Decisions

**L1. The start is an argument of every iterate.** `cgIterate A b x₀ q`, `pcgIterate A M b x₀ q`,
`gmresIterate A b x₀ q`, `pminresIterate A M b x₀ q` (brief O2 order, as K0's `cgState A b x₀`).
Corrections lie in the Krylov space of $\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$,
written out as `krylovSpace A (b - A *ᵥ x₀) q`; the zero start is `x₀ = 0`, with no second
name. The Hestenes–Stiefel realisation becomes `(cgState A b x₀ k).x = cgIterate A b x₀ k`. K2
already uses `cgIterate A b 0 q`.[^L1]

**L2. One rate spelling.** Inline `(Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)` with
`0 < a` and the spectrum in `Set.Icc a a'` (brief O6). Squared weighted norms (CG and PCG errors
in the $\mathbf{A}$-norm, PMINRES residuals in the $\mathbf{M}$-norm, `RCLike.re (quadForm _ _)`)
get `4 * ρ ^ (2 * q)`; Euclidean residuals (GMRES, MINRES, `‖WithLp.toLp 2 _‖`, unsquared) get
`2 * ρ ^ q`. K0's `re_quadForm_sub_cgIterate_le_two_mul_pow` (the $\sqrt{a'}$, $\sqrt a$ form) is
replaced by `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow`, which takes the
`cg-chebyshev-bound` id; the $\kappa(\mathbf{A})$ form stays as the corollary
`…_four_mul_pow_pseudoConditionNumber` (different hypothesis, only `A.PosDef`).[^L2]

**L3. The polynomial-bound constant is `η`**, since `M` names the preconditioner (a binder
rename in K0's CG polynomial bound).

**L4. Preconditioners are applied as `M` and located by the spectrum of `M * A`.** $\mathbf{M}$
approximates $\mathbf{A}^{-1}$ and is what the algorithm multiplies by; definitions take no
hypothesis on it and contain no factor of it. Bounds take `hM : M.PosDef` and
`spectrum ℝ (M * A) ⊆ s` (D8's format, so intervals, unions and outliers work as for
$\mathbf{A}$). Bridges: `Matrix.PosDef.spectrum_mul_subset_Icc_of_le` from
$a\mathbf{M}^{-1} \preceq \mathbf{A} \preceq a'\mathbf{M}^{-1}$, the existing
`Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset` for a preconditioner given as the matrix
$\mathbf{P}$ it approximates (`M = P⁻¹`), and `spectrum_mul_conjTranspose_mul` for the split
matrix. Sources that write the preconditioner as $\mathbf{P} \approx \mathbf{A}$ (Saad,
Elman–Silvester–Wathen) are flagged once per module docstring: "their $\mathbf{M}$ is our
$\mathbf{M}^{-1}$". CONTRIBUTING §5.3: a new row "preconditioner" (`M` applied, `M ≈ A⁻¹`,
`spectrum ℝ (M * A) ⊆ s`, these bridges); the existing "spectral equivalence" row, which uses `M`
for the approximated matrix, is respelled with `P` in the same PR (planned here, edited when the
stage lands).[^L4]

**L5. Two cores, MINRES has no definition.** `minResidualInverse A X := pinv (A * rangeProjector X)`
(D3, approved), for any $m \times n$ $\mathbf{A}$ and $n$-row $\mathbf{X}$: the least-norm
minimiser of $\|\mathbf{b} - \mathbf{A}\mathbf{y}\|$ on the column space, residual
$(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{X}})\mathbf{b}$, frame form $\mathbf{Q}(\mathbf{A}\mathbf{Q})^{+}$,
and the Galerkin inverse of the normal equations (`minResidualInverse_eq_galerkinInverse`).
Rectangular $\mathbf{A}$ serves sketched GMRES ($\mathbf{S}\mathbf{A}$, K6) and LSQR-type methods.
`gmresIterate` is its square Krylov instance; MINRES is `gmresIterate` with `A.IsHermitian`
(brief §1.7). Preconditioned MINRES minimises the $\mathbf{M}$-norm residual, which `pinv` cannot
express without a factor of $\mathbf{M}$, so it uses the Galerkin core:
`galerkinInverse (Aᴴ * M * A) K *ᵥ (Aᴴ *ᵥ (M *ᵥ r₀))`, `K = krylovMatrix (M * A) (M *ᵥ r₀) q`;
`pminresIterate_one` shows $\mathbf{M} = \mathbf{I}$ is GMRES.[^L5]

**L6. Affine optimality** is `IsMinOn` on Mathlib's `AffineSubspace.mk' x₀ K` (brief O8);
membership unfolds by `AffineSubspace.mem_mk'` to `y -ᵥ x₀ ∈ K`.

**L7. Realisations carry no hypothesis on the grade or on computed quantities.** The maintainer,
2026-10-17, verbatim: "past the grade it isn't important what happens. we don't want the
hypothesis for GMRES to involve something like this externally" and "in other words, the GMRES
algorithm should just return the same iterate once it reaches the grade (same with CG etc)". So
every realisation holds for every $q$ (or $k$), and its only hypotheses are problem-level
(`A.PosDef`, `A.IsHermitian`, `IsUnit A`, `M.PosDef`, or a factor `M = C * Cᴴ` in a
correspondence). The algorithms freeze at the grade by their own arithmetic ($0^{-1} = 0$, zero
Lanczos and Arnoldi vectors, `givensCoeffs 0 0 = (1, 0)`, zero pivots that `backSubst` turns into
zero coefficients), so no guard is needed in any step function. Small systems are written with
`pinv` wherever an inverse would fail past the grade ($\mathbf{T}^{+} =
\operatorname{diag}(\mathbf{T}_\nu^{-1}, \mathbf{0})$ there). Two partial-isometry pinv identities
make the canonical-basis forms hold past the grade; two `backSubst` lemmas
(`Matrix/Factorizations/Triangular.lean`) do the same for back substitution. Lemmas that
characterise computed quantities (pivots nonzero iff $q \le \nu$) remain, as lemmas used inside
proofs. Finite termination theorems keep their grade hypothesis: there the grade is the content,
not a guard. §4 lists every realisation with its hypotheses.

**L8. Preconditioned algorithms are realised through the split system.** For any factor
$\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$ the preconditioned Hestenes–Stiefel and Lanczos
states correspond step by step, with equal scalars, to K0's states for
$\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$ and $\mathbf{C}^{\mathsf{H}}\mathbf{b}$; the
correspondences are public theorems for every $\mathbf{A}$ and every factor
(`pcgState_x_eq_mulVec_cgState_x`, `preconditionedLanczosState_z_eq_mulVec` and its three
siblings). The factor appears in theorems and proofs only. Existence of a factor:
`Matrix.PosDef.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose`.

**L9. Algorithms are recursions on a state indexed by the step** (§5.3 "algorithm" row). Arnoldi's
state is the prefix of computed vectors (`arnoldiState A b j : ℕ → n → 𝕜`), with the MGS sweep
`mgsSweep` in `GramSchmidt.lean`; outputs `mgsArnoldiMatrix`, `mgsArnoldiHessenberg` (the name
`arnoldiMatrix` is the canonical basis, as `lanczosMatrix` beside it is the computed Lanczos basis).
Givens QR's state is (accumulated unitary, partially triangularised matrix), as
`householderState`. Paige–Saunders' state is the preconditioned Lanczos state, two rotations, the
residual estimate, two directions and the iterate. Naming: `pcg…` and `pminres…` follow the
standard acronyms of the methods; the preconditioned Lanczos process has no standard acronym and
is spelled out (`preconditionedLanczos…`).

**L10. Outliers are a `Finset ℝ`, steps `T.card + d`.** Hypothesis
`spectrum ℝ A ⊆ Set.Icc a a' ∪ ↑T`, rate in `d` (no truncated subtraction, CONTRIBUTING §5.2),
constant through `∀ x ∈ Set.Icc a a', |∏ t ∈ T, (1 - x / t)| ≤ C`. Corollaries: $C = 1$ when
every outlier is at least $a'$; $C = \prod_{t \in T}(a'/t - 1)$ when every outlier lies in
$(0, a)$ (the growth the maintainer asked to be stated). CG and PCG need no hypothesis on $T$ or on
$a \le a'$ (their bounds are squares); MINRES needs `0 ∉ T` and `a ≤ a'`. One scalar lemma,
`exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow`, gives all of them and, at
$T = \emptyset$, the plain $\kappa$ bounds.

**L11. The spectrum-optimal bound uses a named minimax value.** `residualMinimax s q` is
$\inf_p\sup_{x \in s}\lvert p(x) \rvert$ over real $p$ with `p.degree ≤ q`, `p.eval 0 = 1` (K0's
degree convention, brief O1, rather than `natDegree`); a named quantity, as CONTRIBUTING §4 asks
for a formula repeated across statements (CG, PCG, MINRES, and K2b's Greenbaum theorem). Junk
values: $0$ for $s = \emptyset$, and for unbounded $s$ when $q \ge 1$ (at $q = 0$ it is $1$ on any
nonempty $s$); meaningful for finite and bounded $s$. It sits in `Residual.lean` beside its
Chebyshev bridge and may move to a residual-polynomial file if K2b grows one. Bridge to the
Chebyshev theory: `residualMinimax_Icc` (from `isLeast_chebyshev_minimax`). Each method gets the
minimax form (`…_le_residualMinimax_sq_mul`, `…_le_residualMinimax_mul`); CG and MINRES also get
the per-polynomial form with $\sup_{\sigma(\mathbf{A})}\lvert p \rvert$ (`…_le_iSup_sq_mul`,
`…_le_iSup_mul`), which is the polynomial bound with $s$ the spectrum.

**L12. Scope.** In: all of §3. Deferred, each with its reason:
- MINRES-QLP (singular $\mathbf{A}$ in Paige–Saunders): no consumer; about 600 lines.
- The general two-interval bound on $[a, b'] \cup [c, a']$ of equal lengths (D12's Polynomial
  addition), about 200 lines; the symmetric case is in, attained (C).
- Real GMRES with complex eigenvalues through `complexify`, about 120 lines; the normal-matrix
  corollary of the diagonalisable bound (ℂ only).
- PMINRES outlier bound and PMINRES frame forms: no consumer.
- Richardson and Chebyshev iterations (`polyIterate`, brief §1.8), about 300 lines: not
  requested in K1, no K1 consumer; they are definitions by a fixed polynomial, not by optimality,
  and belong with the polynomial-iteration material of a later stage.
- Greenbaum's theorem (for every positive definite $\mathbf{A}$ some $\mathbf{b}$ attains
  `residualMinimax (spectrum ℝ A) q`): stage K2b, with the machinery it shares there.
- CGLS is **in**, at no definition cost: `cgIterate (Aᴴ * A) (Aᴴ *ᵥ b) x₀ q` and its
  $\kappa(\mathbf{A})$ bound, about 15 lines in `CG.lean`.

## 2. Definitions

The five method definitions, verbatim from the skeleton (`r₀ = b - A *ᵥ x₀` written out):

```lean
noncomputable def cgIterate (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  x₀ + galerkinInverse A (krylovMatrix A (b - A *ᵥ x₀) q) *ᵥ (b - A *ᵥ x₀)

noncomputable def pcgIterate (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  x₀ + galerkinInverse A (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) *ᵥ (b - A *ᵥ x₀)

noncomputable def minResidualInverse (A : Matrix m n 𝕜) (X : Matrix n p 𝕜) : Matrix n m 𝕜 :=
  pinv (A * rangeProjector X)

noncomputable def gmresIterate (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  x₀ + minResidualInverse A (krylovMatrix A (b - A *ᵥ x₀) q) *ᵥ (b - A *ᵥ x₀)

noncomputable def pminresIterate (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  x₀ + galerkinInverse (Aᴴ * M * A) (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) *ᵥ
    (Aᴴ *ᵥ (M *ᵥ (b - A *ᵥ x₀)))
```

Junk values: `galerkinInverse`'s for a singular compression (CG, PCG); least-norm minimisers for
singular $\mathbf{A}$ (GMRES: least Euclidean norm; PMINRES: least Euclidean norm, while its split
form picks least $\mathbf{M}^{-1}$-norm, so the two agree only for invertible $\mathbf{A}$).

Other definitions, by file:

| Name | File | Content |
|---|---|---|
| `residualMinimax s q` | `Polynomial/Chebyshev/Residual` | $\inf_p\sup_s\lvert p \rvert$ over residual polynomials |
| `chebyshevExtremum a a' q k`, `chebyshevWeight a a' q k` | same | $\xi_k = \frac{a'+a}{2} - \frac{a'-a}{2}\cos\frac{k\pi}{q}$; $\omega_k = \lvert\ell_k(0)\rvert$ (Mathlib `Lagrange.basis`) |
| `givensCoeffs u v`, `givensOf x i j` | `Matrix/Factorizations/Givens` | $(\bar u/r, \bar v/r)$, or $(1, 0)$ at $r = 0$; the clearing rotation |
| `givensHessenbergStep`, `givensHessenbergState`, `givensHessenbergQ`, `givensHessenbergR` | same | Givens QR of a Hessenberg `Matrix (Fin m) (Fin p) 𝕜` |
| `mgsSweep V w i` | `Matrix/Factorizations/GramSchmidt` | modified Gram–Schmidt reduction |
| `PCGState`, `pcgStep A M`, `pcgState A M b x₀` | `LinearSystems/PCGRecurrence` | fields `x r z p`; $\rho_k = \operatorname{Re}\langle\mathbf{r}_k, \mathbf{z}_k\rangle$, $\mathbf{z}_{k+1} = \mathbf{M}\mathbf{r}_{k+1}$ |
| `arnoldiStep`, `arnoldiState`, `mgsArnoldiMatrix`, `mgsArnoldiHessenberg` | `Processes/ArnoldiRecurrence` | MGS Arnoldi on the vector prefix |
| `PreconditionedLanczosState` and five companions | `Processes/PreconditionedLanczos` | fields `prev cur z beta`, $\mathbf{z}_j = \mathbf{M}\mathbf{v}_j$, $\beta_{j+1} = \sqrt{\operatorname{Re}\langle\mathbf{w}, \mathbf{M}\mathbf{w}\rangle}$ |
| `MINRESState`, `minresStep A M`, `minresState A M b x₀` | `LinearSystems/MINRESRecurrence` | Lanczos state, rotations $(c_{k-1}, s_{k-1})$, $(c_{k-2}, s_{k-2})$, $\bar\varphi_k$, $\mathbf{d}_{k-1}$, $\mathbf{d}_{k-2}$, $\mathbf{x}_k$ |
| `chebyshevExtremaMatrix`, `chebyshevErrorVector`, `chebyshevWeightVector`, `chebyshevTwoIntervalMatrix`, `chebyshevTwoIntervalVector` | `LinearSystems/WorstCase` | the attaining instances |

The Paige–Saunders step: rotate the new column $(\beta_k, \alpha_k, \beta_{k+1})$ of
$\underline{\mathbf{T}}$ by the two previous rotations
($\varepsilon_k = s_{k-2}\beta_k$, $\delta'_k = \bar c_{k-2}\beta_k$,
$\delta_k = c_{k-1}\delta'_k + s_{k-1}\alpha_k$,
$\bar\gamma_k = -\bar s_{k-1}\delta'_k + \bar c_{k-1}\alpha_k$), take
$(c_k, s_k) = \mathsf{givensCoeffs}(\bar\gamma_k, \beta_{k+1})$,
$\gamma_k = c_k\bar\gamma_k + s_k\beta_{k+1}$, $\tau_k = c_k\bar\varphi_k$,
$\bar\varphi_{k+1} = -\bar s_k\bar\varphi_k$,
$\mathbf{d}_k = \gamma_k^{-1}(\mathbf{z}_k - \varepsilon_k\mathbf{d}_{k-2} - \delta_k\mathbf{d}_{k-1})$,
$\mathbf{x}_{k+1} = \mathbf{x}_k + \tau_k\mathbf{d}_k$; one $\mathbf{A}$ and one $\mathbf{M}$ per
step, inside the Lanczos step.

New §5.3 rows, in the PRs that prove them: "minimal residual approximation"
(`minResidualInverse`, bridge `minResidualInverse_eq_galerkinInverse`), "Krylov methods for
linear systems" (the four iterates; MINRES as Hermitian `gmresIterate`), "preconditioner" (L4),
"residual minimax value" (`residualMinimax`, bridge `residualMinimax_Icc`); the "algorithm" row's
examples gain `cgState`, `pcgState`, `arnoldiState`, `givensHessenbergState`, `minresState`.

## 3. Theorems

Names, claims, proof plans; the statements are in the skeleton. New `Result:` ids:
`pcg-optimality`, `pcg-chebyshev-bound`, `pcg-recurrence`, `gmres-optimality`, `gmres-arnoldi`,
`arnoldi-recurrence`, `minres-polynomial-bound`, `minres-chebyshev-bound`, `minres-lanczos`,
`minres-recurrence`, `pminres-optimality`, `pminres-lanczos`,
`preconditioned-lanczos-recurrence`, `cg-chebyshev-sharp`, `minres-chebyshev-sharp`; K0's four CG
ids are kept.

The three $\kappa$ statements, verbatim:

```lean
theorem _root_.Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q) *
        RCLike.re (quadForm A (xs - x₀))

theorem _root_.Matrix.IsHermitian.re_quadForm_sub_pcgIterate_le_four_mul_pow
    {A M : Matrix n n 𝕜} (hA : A.IsHermitian) (hM : M.PosDef) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ (M * A) ⊆ Set.Icc a a') {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    RCLike.re (quadForm A (xs - pcgIterate A M b x₀ q)) ≤
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q) *
        RCLike.re (quadForm A (xs - x₀))

theorem _root_.Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (b x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
      2 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ q *
        ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖
```

### 3.1 Lower-layer additions

- `Matrix/Pseudoinverse/Pinv.lean`: `pinv_mul_of_conjTranspose_mul_self_mul_eq`,
  `pinv_mul_conjTranspose_of_mul_conjTranspose_mul_self_eq` (L7). Plan: `IsPinv.pinv_eq`, the four
  Penrose identities; the second from the first by `pinv_conjTranspose`.
- `Matrix/Factorizations/GramSchmidt.lean`: `mgsSweep`, `mgsSweep_eq_sub_sum` (MGS equals
  classical for pairwise orthogonal vectors; induction).
- `Matrix/Factorizations/Givens.lean` (the existing file beside `Householder.lean`; its
  `givens`, `hasOrthonormalCols_givens`, `exists_givens_mulVec_apply_eq_zero` are the base):
  - `givensCoeffs` with `norm_givensCoeffs_fst_sq_add`, `givensCoeffs_fst_mul_add`,
    `neg_star_givensCoeffs_snd_mul_add` (the scalar algebra the existing existence proof does
    inline; that proof is then a corollary); `givensOf` with `hasOrthonormalCols_givensOf`,
    `givensOf_mulVec_apply_right` (clears), `givensOf_mulVec_apply_left`;
  - Givens QR: `hasOrthonormalCols_givensHessenbergState_fst`, `givensHessenbergState_fst_mul_snd`
    (every step), `isUpperTrapezoidal_givensHessenbergR` (Hessenberg input: after $k$ steps the
    first $k$ columns are trapezoidal, the rest still Hessenberg), `isQR_givensHessenberg`
    (`isQR_submatrix_castLE`, as `isQR_householder`);
  - the tridiagonal case `givensHessenbergR_apply_eq_zero_of_add_two_lt` (only
    `IsUpperHessenberg Hᴴ`, which a rectangular tridiagonal matrix satisfies; no new predicate:
    $\mathbf{R}$ has three diagonals);
  - `forall_givensHessenbergR_apply_self_ne_zero_iff` (nonzero pivots iff full column rank);
  - the progressive form `pinv_submatrix_mulVec_single_eq_backSubst` and
    `norm_sub_mulVec_pinv_submatrix_mulVec_single_eq`: after $k$ steps, the leading
    $(k+1) \times k$ problem with right-hand side $\mathbf{e}_0$ is solved by `backSubst` on the
    leading $k \times k$ block, residual the modulus of entry $k$ of the rotated $\mathbf{e}_0$, when
    the leading block has full column rank (a hypothesis on the input matrix, not on pivots).
    Plan: rotations of steps $j < k$ touch rows $j, j + 1 \le k$, so the restricted state is the
    Givens QR of the block; `IsQR.isLeastSquaresSolution_backSubst`; uniqueness at full rank.
- `Matrix/Factorizations/Triangular.lean`: `backSubst_castLE_of_apply_eq_zero` and
  `backSubst_apply_eq_zero_of_le`: on a matrix whose rows and columns from $r$ on vanish, back
  substitution is that of the leading block, extended by zeros (the freeze of L7).
- `Matrix/Functions/HermitianCalculus.lean` (beside `spectrum_subset_Icc_of_le`):
  `Matrix.IsHermitian.smul_one_le_iff_spectrum_subset_Ici`,
  `Matrix.IsHermitian.le_smul_one_iff_spectrum_subset_Iic`, the public converses; the two private
  lemmas of `Matrix/Inequalities/Order.lean` (`smul_one_le_iff_forall_le_spectrum`,
  `le_smul_one_iff_forall_spectrum_le`) are reproved from them. The quadratic-form fact the Elman
  bound needs exists: `re_quadForm_hermitianPart`.
- `Matrix/Inequalities/Order.lean`: `spectrum_mul_conjTranspose_mul` (`spectrum.units_conjugate`),
  `Matrix.PosDef.spectrum_mul_subset_Icc_of_le` (L4).
- `Polynomial/Chebyshev/Residual.lean`:
  - `residualMinimax`, `residualMinimax_nonneg`, `residualMinimax_le` (any admissible $p$ bounds
    it), `residualMinimax_Icc` (the Chebyshev value), `inv_eval_T_real_eq_two_mul_pow_div`
    ($T_q(\frac{a'+a}{a'-a})^{-1} = \frac{2\rho^q}{1+\rho^{2q}}$, from `eval_T_real_eq_of_one_le`);
  - `exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow` (L10; renamed from the first
    draft's `exists_eval_eq_zero_of_mem_abs_eval_le`): $\prod_{t}(1 - X/t)$ times
    `chebyshevResidual a a' d`, or $(1 - X/a)^d$ at $a = a'$, or the product alone for $a' < a$;
  - `chebyshevExtremum` with `chebyshevExtremum_mem_Icc`, `strictMono_chebyshevExtremum`,
    `eval_chebyshevResidual_chebyshevExtremum` (alternation, from
    `eval_T_real_cos_int_mul_pi_div`); `chebyshevWeight` with `chebyshevWeight_pos`,
    `sum_neg_one_pow_mul_chebyshevWeight_mul_eval` ($\sum_k(-1)^k\omega_k p(\xi_k) = p(0)$ for
    $\deg p \le q$, over any `RCLike` field: the sign of $\ell_k(0)$ is $(-1)^k$ and
    `Lagrange.eq_interpolate` at $0$), `sum_chebyshevWeight` ($\sum_k\omega_k = T_q(\frac{a'+a}{a'-a})$).
- `Krylov/Basic/Space.lean`: `krylovMatrix_mul_mulVec`, `krylovSpace_mul_mulVec`
  ($\mathbf{K}_q(\mathbf{C}\mathbf{B}, \mathbf{C}\mathbf{v}) = \mathbf{C}\mathbf{K}_q(\mathbf{B}\mathbf{C}, \mathbf{v})$,
  the prototype's `krylovSpace_mul_mulVec_eq_map`); `Krylov/Basic/Grade.lean`:
  `krylovGrade_mul_mulVec` (`Matrix.rank_mul_eq_right_of_isUnit_det`).
- `Krylov/Processes/Lanczos.lean`: the column API of `arnoldiMatrix`, all stated on
  `(arnoldiMatrix A b (j + 1)).col (Fin.last j)` with the coefficient
  `gramSchmidtR (krylovMatrix A b (j + 1)) (Fin.last j) (Fin.last j)` (no public `arnoldiVec`,
  which would be a second spelling): `arnoldiMatrix_col_eq_col_last`,
  `star_arnoldiMatrix_col_last_dotProduct_of_ne`, `gramSchmidtR_krylovMatrix_apply`,
  `exists_gramSchmidtR_smul_arnoldiMatrix_col_last`, `arnoldiMatrix_col_last_mem_krylovSpace`,
  `star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem`,
  `star_arnoldiMatrix_col_last_dotProduct_mulVec_of_lt`,
  `gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff`, `arnoldiMatrix_col_last_eq_zero_iff`,
  `norm_arnoldiMatrix_col_last`. These are K0's private layer of `LanczosRecurrence.lean`
  (`lanczosVec`, `lanczosR`, `arnoldiMatrix_col_eq`, `exists_lanczosR_smul`, `lanczosVec_mem`,
  `star_lanczosVec_dotProduct_eq_zero`, `star_lanczosVec_dotProduct_mulVec_of_lt`,
  `lanczosR_eq_zero_iff`, `lanczosVec_eq_zero`, `norm_lanczosVec`) made public; Arnoldi needs the
  same bookkeeping. **`LanczosRecurrence.lean` is therefore edited**: its private layer is
  removed and its proofs repointed (no statement changes; about 150 lines fewer). New beside them:
  `arnoldiMatrix_col_succ` (the canonical Arnoldi step) and
  `conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_submatrix_castSucc`
  ($\underline{\mathbf{H}}_q$ as the first $q$ columns of the square compression).

### 3.2 CG (`LinearSystems/CG.lean`, edited) and its K0 companions

Every K0 statement gains `x₀` and lives on $\mathbf{x}_0 + \mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$
(`cgIterate_sub_mem_krylovSpace`, `cgIterate_zero`, both frame forms, the Galerkin condition and
characterisation, `isMinOn_cgIterate`, `exists_sub_cgIterate_eq_aeval`, the comparison, the
polynomial bound, finite termination); proofs are K0's through `add_sub_cancel_left`. Bounds:
- `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow` ($\kappa$; L10 at $T = \emptyset$)
  and the kept `…_four_mul_pow_pseudoConditionNumber`;
- the outlier bound `Matrix.PosDef.re_quadForm_sub_cgIterate_le_four_mul_sq_mul_pow`
  ($4C^2\rho^{2d}$ after $\lvert T \rvert + d$ steps; plan: L10's lemma, then the polynomial bound
  with $s$ the spectrum and $\eta = \lvert 2C\rho^d \rvert$, the absolute value covering $a' < a$,
  where $C$ may be negative and the polynomial vanishes on the spectrum), with
  `…_four_mul_pow_of_forall_le` ($C = 1$) and `…_four_mul_sq_mul_pow_of_forall_lt`;
- the spectrum-optimal forms `Matrix.PosDef.re_quadForm_sub_cgIterate_le_iSup_sq_mul` and
  `…_le_residualMinimax_sq_mul` (L11; `Matrix.finite_real_spectrum` for boundedness, then
  `le_ciInf` on square roots);
- CGLS, `re_quadForm_sub_cgIterate_conjTranspose_mul_le_four_mul_pow`: for $\mathbf{A}$ of full
  column rank, $4\bigl(\frac{\kappa - 1}{\kappa + 1}\bigr)^{2q}$ with $\kappa = \kappa(\mathbf{A})$
  in the $\mathbf{A}^{\mathsf{H}}\mathbf{A}$-norm (`posDef_conjTranspose_mul_self_iff`,
  `pseudoConditionNumber_conjTranspose_mul_self`, the $\kappa(\mathbf{A})$ corollary).

`CGRecurrence.lean`: only `Matrix.PosDef.cgState_x_eq` changes (now proved in the skeleton).
`CGLanczos.lean` (L7): K0's `Matrix.PosDef.cgIterate_eq_arnoldiMatrix` and
`Matrix.PosDef.cgIterate_eq_lanczosMatrix` took $q + 1 \le \nu$ and $\mathbf{T}^{-1}$; they become
`cgIterate_eq_arnoldiMatrix` (every $\mathbf{A}$, every $q$) and
`Matrix.IsHermitian.cgIterate_eq_lanczosMatrix` (Hermitian, every $q$, proved in the skeleton),
with $\mathbf{T}^{+}$, through the new `galerkinInverse_krylovMatrix_eq_arnoldiMatrix`
($\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}$ on the canonical
basis, every $q$). Below the grade and for positive definite $\mathbf{A}$,
$\mathbf{T}^{+} = \mathbf{T}^{-1}$ by `pinv_of_isUnit`. K2's note cites the two K0 names; they are
renamed here.

### 3.3 PCG (`LinearSystems/PCG.lean`, `PCGRecurrence.lean`)

`pcgIterate_sub_mem_krylovSpace`, `pcgIterate_zero`, `pcgIterate_one` (CG at $\mathbf{M} = \mathbf{I}$);
`Matrix.PosDef.pcgIterate_eq` (frame form); the Galerkin characterisation and
`Matrix.PosDef.isMinOn_pcgIterate` (every $\mathbf{M}$, from `Galerkin.lean`);
`Matrix.PosDef.pcgIterate_eq_mulVec_cgIterate` (**PCG is CG on the split system**, any invertible
factor; `krylovMatrix_mul_mulVec` with $\mathbf{B} = \mathbf{C}^{\mathsf{H}}\mathbf{A}$, matching
Galerkin conditions); the polynomial, $\kappa$, outlier and spectrum-optimal bounds in the
spectrum of $\mathbf{M}\mathbf{A}$ (each the CG theorem for $\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$
through the split form and `spectrum_mul_conjTranspose_mul`); finite termination. Recurrence:
`pcgState_r_eq`, `pcgState_z_eq`, `pcgState_x_sub_mem_krylovSpace`,
`pcgState_x_eq_mulVec_cgState_x` (the correspondence, §4), `Matrix.PosDef.pcgState_x_eq` (**the
realisation**, every $k$), $\mathbf{M}$-orthogonal residuals and conjugate directions,
`Matrix.PosDef.pcgState_r_eq_zero_iff` (breakdown at the grade, `krylovGrade_mul_mulVec`).

### 3.4 Minimal residual core (`LinearSystems/MinResidual.lean`)

All for rectangular $\mathbf{A}$: `minResidualInverse_eq_of_range_eq` (proved),
`HasOrthonormalCols.minResidualInverse_eq`, `minResidualInverse_mulVec_mem`,
`mul_minResidualInverse` ($\mathbf{P}_{\mathbf{A}\mathbf{X}}$), `isMinOn_minResidualInverse_mulVec`,
`minResidualInverse_eq_galerkinInverse` (`pinv_eq_pinv_conjTranspose_mul_self_mul`); at full
column rank (`Function.Injective A.mulVec`, the §5.3 spelling, which generalises the first
draft's `IsUnit A`) the Petrov–Galerkin characterisation and exactness; and
`Matrix.PosDef.isMinOn_galerkinInverse_conjTranspose_mul_mul_mulVec` (the $\mathbf{M}$-norm
residual, `M : Matrix m m 𝕜`, every $\mathbf{A}$: with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$
the vector is $\mathbf{B}^{+}\mathbf{C}^{\mathsf{H}}\mathbf{b}$,
$\mathbf{B} = \mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{P}_{\mathbf{X}}$, by
`isLeastSquaresSolution_iff_isMinOn`).

### 3.5 GMRES (`LinearSystems/GMRES.lean`, `GMRESArnoldi.lean`)

`gmresIterate_sub_mem_krylovSpace`, `gmresIterate_zero`, `HasOrthonormalCols.gmresIterate_eq`,
`sub_mulVec_gmresIterate`, `eq_gmresIterate_of_conjTranspose_mul_krylovMatrix_mulVec_sub_eq_zero`
(invertible $\mathbf{A}$, the parallel of CG's characterisation), `isMinOn_gmresIterate`,
`norm_sub_mulVec_gmresIterate_succ_le`, the residual polynomial over `𝕜` and the comparison,
finite termination; the diagonalisable bound
`norm_sub_mulVec_gmresIterate_le_pseudoConditionNumber_mul` (`hV : IsUnit V`,
`A * V = V * diagonal d`, $\kappa(\mathbf{V})\eta\|\mathbf{r}_0\|$;
`aeval_mul_eq_mul_aeval_of_mul_eq_mul`, `specNorm_diagonal_le`); the field-of-values (Elman)
bound `norm_sub_mulVec_gmresIterate_le_sqrt_one_sub_sq_pow` ($(1 - a^2/a'^2)^{q/2}$ for
`spectrum ℝ (hermitianPart A) ⊆ Set.Ici a`, `specNorm A ≤ a'`; residual polynomial
$(1 - \alpha X)^q$, `Matrix.IsHermitian.smul_one_le_iff_spectrum_subset_Ici`,
`re_quadForm_hermitianPart`). Realisations: `gmresIterate_eq_arnoldiMatrix` (canonical basis,
small problem by `pinv`, every $\mathbf{A}$ and $q$), `gmresIterate_eq_mgsArnoldiMatrix` (proved),
`gmresIterate_eq_backSubst_givensHessenberg` (**the standard implementation**: Arnoldi, Givens QR of
$\underline{\mathbf{H}}_q$, back substitution; invertible $\mathbf{A}$, every $q$; past the grade
the frozen arithmetic of L7), `norm_sub_mulVec_gmresIterate_eq_norm_givensHessenbergQ` (the
residual estimate, same hypothesis), `forall_givensHessenbergR_mgsArnoldiHessenberg_ne_zero_iff`
(for invertible $\mathbf{A}$ the pivots are nonzero iff $q \le \nu$; a lemma inside the proof).
Invertibility is needed: for singular $\mathbf{A}$ the last pivot before the grade can vanish while
its column is not zero, and back substitution then differs from the least-norm solution.

### 3.6 Arnoldi (`Processes/ArnoldiRecurrence.lean`)

`arnoldiState_apply_of_le`, `mgsArnoldiMatrix_eq_arnoldiMatrix` (every $\mathbf{A}$ and $q$),
`mgsArnoldiHessenberg_eq`, `isUpperHessenberg_mgsArnoldiHessenberg`, `mul_mgsArnoldiMatrix`,
`mgsArnoldiHessenberg_apply_succ_eq_zero_iff` (breakdown at the grade). Plan: induction on $j$,
the computed prefix equals the canonical columns, which are pairwise orthogonal, so
`mgsSweep_eq_sub_sum` and `gramSchmidtQ_mul_conjTranspose` give
$(\mathbf{I} - \mathbf{P}_{\mathcal{K}_{j+1}})\mathbf{A}\mathbf{q}_j$ and `arnoldiMatrix_col_succ`
closes the step.

### 3.7 MINRES and preconditioned MINRES

`LinearSystems/MINRES.lean`. MINRES: the polynomial bound
`Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le` (any $s$; split off the empty index type,
since `specNorm_aeval_le` takes $0 \le \eta$), the $\kappa$ bound, the symmetric two-interval
bound `…_le_two_mul_pow_div_two` (`chebyshevResidual (a ^ 2) (a' ^ 2) k` composed with $X^2$; at
$a = a'$ use $(1 - X^2/a^2)^k$, since that residual is $0$ at $0$ for odd $k$; $a' < a$ is
empty), the outlier bound `…_le_two_mul_mul_pow` (`0 ∉ T`, `a ≤ a'`) and its $C = 1$ corollary,
the spectrum-optimal forms `…_le_iSup_mul` and `…_le_residualMinimax_mul`. PMINRES:
`pminresIterate_sub_mem_krylovSpace`, `pminresIterate_one`, `Matrix.PosDef.isMinOn_pminresIterate`
([ElmanSilvesterWathen2014, §4.2]), `pminresIterate_eq_mulVec_gmresIterate` (invertible
$\mathbf{A}$, L5's asymmetry), the polynomial and $\kappa$ bounds in the squared $\mathbf{M}$-norm,
`pminresIterate_eq_of_krylovGrade_le`.

`LinearSystems/MINRESLanczos.lean`: `Matrix.IsHermitian.gmresIterate_eq_lanczosMatrix` (Lanczos
plus $\underline{\mathbf{T}}_q^{+}$, every $q$) and
`Matrix.IsHermitian.pminresIterate_eq_preconditionedLanczosMatrix` (invertible $\mathbf{A}$).
`Processes/PreconditionedLanczos.lean`: the four correspondence theorems, the realisation
`Matrix.IsHermitian.preconditionedLanczosMatrix_eq` and `…Tridiagonal_eq` (any factor),
`range_preconditionedLanczosMatrix`.

`LinearSystems/MINRESRecurrence.lean` (A): `Matrix.IsHermitian.minresState_x_eq` (**the
Paige–Saunders iterates are the PMINRES iterates**, invertible Hermitian $\mathbf{A}$, positive
definite $\mathbf{M}$, every $k$), `…_x_eq_gmresIterate` ($\mathbf{M} = \mathbf{I}$, MINRES),
`norm_minresState_phi_sq` (the residual estimate $\lvert\bar\varphi_k\rvert^2 =
\|\mathbf{r}_k\|_{\mathbf{M}}^2$). Plan: by induction the rotations are the steps of
`givensHessenbergState` on the computed $\underline{\mathbf{T}}$ (each new column has three
nonzeros, so two old rotations and one new suffice; signs follow `givens`, not the paper's
reflections), $(\varepsilon_k, \delta_k, \gamma_k)$ is
column $k$ of the three-diagonal $\mathbf{R}$, $\mathbf{D}_k\mathbf{R}_k = \mathbf{Z}_k$ and
$\mathbf{x}_k = \mathbf{x}_0 + \mathbf{D}_k\mathbf{t}_k$; then the progressive form, whose pivots
are nonzero ($\gamma_k \ge \beta_{k+1} > 0$ for $k \le \nu - 2$; $\gamma_{\nu-1} \ne 0$ because the
square $\mathbf{T}_\nu$ is the compression of $\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$ to the
invariant $\mathcal{K}_\nu$, invertible for invertible $\mathbf{A}$), and
`pminresIterate_eq_preconditionedLanczosMatrix`. Past the grade $\bar\varphi = 0$, the new
rotation is the identity, $\gamma = 0$, $\mathbf{d} = \mathbf{0}$ and the state is frozen.

### 3.8 Sharpness (`LinearSystems/WorstCase.lean`, C)

`posDef_chebyshevExtremaMatrix`, `spectrum_chebyshevExtremaMatrix_subset_Icc`;
`re_quadForm_sub_cgIterate_chebyshevExtremaMatrix`: on the diagonal matrix of the $q + 1$
Chebyshev extrema with initial error $\sqrt{\omega_k/\xi_k}$ the squared CG error ratio is
**exactly** $T_q(\frac{a'+a}{a'-a})^{-2}$, and `…_eq_four_mul_pow_div` writes it as
$\frac{4\rho^{2q}}{(1+\rho^{2q})^2}$: the bound $4\rho^{2q}$ is tight up to $(1+\rho^{2q})^2 \le 4$,
a factor tending to $1$. `norm_sub_mulVec_gmresIterate_chebyshevExtremaMatrix`: MINRES likewise,
ratio $\frac{2\rho^q}{1+\rho^{2q}}$. `norm_sub_mulVec_gmresIterate_chebyshevTwoIntervalMatrix`:
on $\pm\sqrt{\xi_j}$ for the extrema of $[a^2, a'^2]$ at degree $\lfloor q/2 \rfloor$, MINRES attains
$T_{\lfloor q/2 \rfloor}(\frac{a'^2+a^2}{a'^2-a^2})^{-1}$, the two-interval rate up to the same
factor (odd steps gain nothing: the even part of a residual polynomial does at least as well on
symmetric data). Plan: the error is $p(\mathbf{A})\mathbf{e}_0$ for a residual $p$ (K0's
`exists_sub_cgIterate_eq_aeval`), with squared norm $\sum_k\omega_k\lvert p(\xi_k) \rvert^2$;
Cauchy–Schwarz with $\sum_k(-1)^k\omega_k p(\xi_k) = 1$ gives at least $1/\sum_k\omega_k$; the
Chebyshev residual attains it; $\sum_k\omega_k = T_q$. No hypothesis on the Krylov space is
needed: `krylovSpace` is by definition the image of the polynomials of degree less than $q$, so
for every matrix and vector the minimum over $\mathbf{x}_0 + \mathcal{K}_q$ is the minimum over
residual polynomials of degree at most $q$. For two intervals, with $u = p(\sqrt{\xi_j})$ and
$v = p(-\sqrt{\xi_j})$, $\lvert u \rvert^2 + \lvert v \rvert^2 \ge 2\lvert (u + v)/2 \rvert^2$ reduces
$p$ to its even part $P(x^2)$, $\deg P \le \lfloor q/2 \rfloor$, with no uniqueness argument.

## 4. How the preconditioned realisations work

The recurrences apply $\mathbf{M}$ once per step and form no factor. The proofs use a factor,
any $\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$, in one place each: a
correspondence induction against K0. For PCG: $\mathbf{x}_k = \mathbf{C}\hat{\mathbf{x}}_k$,
$\mathbf{C}^{\mathsf{H}}\mathbf{r}_k = \hat{\mathbf{r}}_k$, $\mathbf{z}_k = \mathbf{C}\hat{\mathbf{r}}_k$,
$\mathbf{p}_k = \mathbf{C}\hat{\mathbf{p}}_k$, with $\operatorname{Re}\langle\mathbf{r}_k,
\mathbf{z}_k\rangle = \|\hat{\mathbf{r}}_k\|^2$ and $\mathbf{p}_k^{\mathsf{H}}\mathbf{A}\mathbf{p}_k =
\hat{\mathbf{p}}_k^{\mathsf{H}}\hat{\mathbf{A}}\hat{\mathbf{p}}_k$ for $\hat{\mathbf{A}} =
\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$; then K0's `Matrix.PosDef.cgState_x_eq` and the split
form. For preconditioned Lanczos: $\mathbf{C}^{\mathsf{H}}\mathbf{v}_j = \hat{\mathbf{q}}_j$,
$\mathbf{z}_j = \mathbf{C}\hat{\mathbf{q}}_j$, equal $\alpha_j$, $\beta_j$ (since
$\sqrt{\operatorname{Re}\langle\mathbf{w}, \mathbf{M}\mathbf{w}\rangle} = \|\mathbf{C}^{\mathsf{H}}\mathbf{w}\|$);
then K0's `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`. Neither correspondence needs
invertibility or Hermitian symmetry; they are public, so later stages (Nyström PCG, K8) can reuse
them. Paige–Saunders sits on top: preconditioned Lanczos computes $\mathbf{Z}$ and
$\underline{\mathbf{T}}$, Givens QR is progressive, so the short recurrence is the incremental
form of `pminresIterate_eq_preconditionedLanczosMatrix`.

**Every realisation and its hypotheses** (all for every $q$ or $k$; none on the grade or on
computed quantities):

| Theorem | Hypotheses |
|---|---|
| `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`, `…lanczosTridiagonal_eq` (K0) | `A.IsHermitian` |
| `Matrix.PosDef.cgState_x_eq` (K0, edited) | `A.PosDef` |
| `cgIterate_eq_arnoldiMatrix` | none |
| `Matrix.IsHermitian.cgIterate_eq_lanczosMatrix` | `A.IsHermitian` |
| `pcgState_x_eq_mulVec_cgState_x` | `M = C * Cᴴ`, `C *ᵥ y₀ = x₀` |
| `Matrix.PosDef.pcgState_x_eq` | `A.PosDef`, `M.PosDef` |
| `mgsArnoldiMatrix_eq_arnoldiMatrix`, `mgsArnoldiHessenberg_eq`, `mul_mgsArnoldiMatrix` | none |
| `preconditionedLanczosState_z_eq_mulVec` and its three siblings | `M = C * Cᴴ` |
| `Matrix.IsHermitian.preconditionedLanczosMatrix_eq`, `…Tridiagonal_eq` | `A.IsHermitian`, `M = C * Cᴴ` |
| `gmresIterate_eq_arnoldiMatrix`, `gmresIterate_eq_mgsArnoldiMatrix` | none |
| `gmresIterate_eq_backSubst_givensHessenberg`, `norm_sub_mulVec_gmresIterate_eq_norm_givensHessenbergQ` | `IsUnit A` |
| `Matrix.IsHermitian.gmresIterate_eq_lanczosMatrix` | `A.IsHermitian` |
| `Matrix.IsHermitian.pminresIterate_eq_preconditionedLanczosMatrix` | `A.IsHermitian`, `IsUnit A`, `M.PosDef` |
| `Matrix.IsHermitian.minresState_x_eq`, `norm_minresState_phi_sq` | `A.IsHermitian`, `IsUnit A`, `M.PosDef` |
| `Matrix.IsHermitian.minresState_x_eq_gmresIterate` | `A.IsHermitian`, `IsUnit A` |
| `isQR_givensHessenberg` (Matrix layer) | `IsUpperHessenberg H`, `p ≤ m` (input) |

## 5. Files, imports, placement, order

Imports ("uses" is a direct import; Processes import no LinearSystems file):
- additions use only their file's imports, plus `Mathlib.LinearAlgebra.Lagrange` for `Residual`,
  `Hessenberg` and `QR` for `Givens`;
- `Processes/ArnoldiRecurrence` uses `Processes/Lanczos`, `GramSchmidt`;
  `Processes/PreconditionedLanczos` uses `Processes/LanczosRecurrence`;
- `LinearSystems/CG` adds the affine-subspace file; `PCG` uses `CG`, `Order`; `PCGRecurrence` uses
  `CGRecurrence`, `PCG`; `MinResidual` uses `Galerkin`; `GMRES` uses `Grade`, `MinResidual`,
  `ConditionNumber`, `Diagonalizable`, `HermitianPart`; `GMRESArnoldi` uses `GMRES`,
  `ArnoldiRecurrence`, `Givens`; `MINRES` uses `GMRES`, `Matrix/Functions/Polynomial`, `Order`,
  `Residual`; `WorstCase` uses `CG`, `MINRES`; `MINRESLanczos` uses `GMRESArnoldi`, `MINRES`,
  `PreconditionedLanczos`; `MINRESRecurrence` uses `MINRESLanczos`.

| File | Kind | Skeleton defs + theorems | Expected lines when proved |
|---|---|---|---|
| `Matrix/Pseudoinverse/Pinv` | addition | 0 + 2 | +60 |
| `Matrix/Factorizations/GramSchmidt` | addition | 1 + 1 | +50 |
| `Matrix/Factorizations/Triangular` | addition | 0 + 2 | +40 |
| `Matrix/Factorizations/Givens` | addition (259 now) | 6 + 14 | +450 |
| `Matrix/Functions/HermitianCalculus` | addition | 0 + 2 | +30 |
| `Matrix/Inequalities/Order` | addition | 0 + 2 | +40 |
| `Polynomial/Chebyshev/Residual` | addition | 3 + 11 | +350 |
| `Krylov/Basic/Space`, `Grade` | addition | 0 + 3 | +75 |
| `Krylov/Processes/Lanczos` | addition | 0 + 12 | +250 |
| `Krylov/Processes/LanczosRecurrence` | edited | private layer moved | about 320 (now 466) |
| `Krylov/Processes/ArnoldiRecurrence` | new | 4 + 6 | 450 |
| `Krylov/Processes/PreconditionedLanczos` | new | 6 + 8 | 350 |
| `Krylov/LinearSystems/CG` | edited | 1 + 19 | 450 (now 288) |
| `Krylov/LinearSystems/CGRecurrence`, `CGLanczos` | edited | 3 + 11 | 450 (now 425) |
| `Krylov/LinearSystems/PCG` | new | 1 + 12 | 370 |
| `Krylov/LinearSystems/PCGRecurrence` | new | 3 + 8 | 250 |
| `Krylov/LinearSystems/MinResidual` | new | 1 + 9 | 300 |
| `Krylov/LinearSystems/GMRES` | new | 1 + 12 | 470 |
| `Krylov/LinearSystems/GMRESArnoldi` | new | 0 + 5 | 250 |
| `Krylov/LinearSystems/MINRES` | new | 1 + 15 | 550 |
| `Krylov/LinearSystems/WorstCase` | new | 5 + 7 | 400 |
| `Krylov/LinearSystems/MINRESLanczos` | new | 0 + 2 | 150 |
| `Krylov/LinearSystems/MINRESRecurrence` | new | 3 + 3 | 700 |

New declarations: 35 definitions and 143 theorems (K0's 23 restated theorems not counted). New
lines when proved: about 5650. Every file stays under 1000 lines (`Givens.lean` about 710).

Placement, with reasons (CONTRIBUTING §8 item 5):
- Givens QR goes into the existing `Matrix/Factorizations/Givens.lean`, beside `Householder.lean`
  (the maintainer's "right place"): the rotation is there already, and the QR recursion follows
  `Householder.lean`'s pattern of rotation and QR in one topic file. Back substitution is reused
  from `Triangular.lean`, not redefined.
- `minResidualInverse` has its own file beside `Galerkin.lean` (a projection method on any
  subspace; K6 and deflation consume it with other `X`).
- PCG and PMINRES live with their methods, MINRES gets `MINRES.lean` (bounds and PMINRES) and
  `MINRESRecurrence.lean` (Paige–Saunders), like `CG`/`CGRecurrence`.
- The worst-case instances get `WorstCase.lean`, a topic file that K2b's Greenbaum theorem will
  join; their scalar part (extrema, dual weights, the minimax value) goes to
  `Polynomial/Chebyshev/Residual.lean`.
- The Loewner converses go beside `spectrum_subset_Icc_of_le`; `mgsSweep` to `GramSchmidt.lean`;
  the column API to `Processes/Lanczos.lean`, where `arnoldiMatrix` is.
- Realisations through the processes get LinearSystems files (`GMRESArnoldi`, `MINRESLanczos`),
  as K0's `CGLanczos`, so Processes stays below LinearSystems.
No placement flag is open.

**Order of proof and commit checkpoints.** Sharpness is placed after PCG as asked and numbered
2b, so that the Givens checkpoint keeps the number 5 the maintainer gave it.
1. *CG with a start* (about 450 lines changed): `Residual` (outlier lemma, `residualMinimax`),
   `CG`, `CGRecurrence`, `CGLanczos`; one interface change, landing together.
2. *PCG* (about 735): `Space`, `Grade`, `Order` additions, `PCG`, `PCGRecurrence`.
2b. *Sharpness for CG* (about 450): `Residual` (extrema, dual weights,
   `inv_eval_T_real_eq_two_mul_pow_div`), `WorstCase` with its CG statements; its MINRES
   statements join it in checkpoint 3.
3. *Minimal residual, GMRES, MINRES* (about 1550): `Pinv`, `HermitianCalculus` additions,
   `MinResidual`, `GMRES`, `MINRES`, the MINRES part of `WorstCase`.
4. *Arnoldi and the Lanczos realisations* (about 1250): `GramSchmidt` and `Lanczos` additions with
   the `LanczosRecurrence` edit, `ArnoldiRecurrence`, `PreconditionedLanczos`, `GMRESArnoldi`
   (canonical and MGS forms), `MINRESLanczos`.
5. *Givens and Paige–Saunders* (about 1350): the `Triangular` and `Givens` additions, the Givens theorems of
   `GMRESArnoldi`, `MINRESRecurrence`.
Parallel proving: in 3 to 5, two agents on disjoint chains (`MinResidual`, `GMRES`, `MINRES` /
`GramSchmidt`, `Lanczos`, `ArnoldiRecurrence`, `PreconditionedLanczos`; then `Givens` /
`GMRESArnoldi`), `MINRESRecurrence` last.

## 6. Mathlib search and deviations

Searched in `.lake/packages/mathlib/Mathlib`: `AffineSubspace.mk'`, `AffineSubspace.mem_mk'`
(used); `spectrum.units_conjugate` (used), `spectrum.nonzero_mul_comm`;
`Matrix.rank_mul_eq_right_of_isUnit_det` (used); `InnerProductSpace.gramSchmidt` (classical only,
so `mgsSweep` is new); `Lagrange.basis`, `Lagrange.eq_interpolate` (used for the dual weights);
`Polynomial.Chebyshev.eval_T_real_cos_int_mul_pi_div` (alternation); `Matrix.PosDef.inv`. Mathlib
has no matrix pseudoinverse, Givens QR, Krylov method, Arnoldi process, GMRES, MINRES or residual
minimax value. Every new definition is an addition; the Krylov entry of
`docs/design/Mathlib-deviations.md` grows by the new names, no numbered deviation. Prototype
material: `Solvers/Preconditioned.lean` (split reduction, ported), `Solvers/GMRES.lean`,
`Solvers/GMRESArnoldi.lean` (residual algebra; `IsGMRESIterate` and `ArnoldiDecomp` not
reproduced, by D3 and D5), `Processes/ArnoldiProcess.lean` (classical; replaced by MGS).

## 7. Consumers

- `cgIterate A b x₀ q`, `…_four_mul_pow`: K2 (`Krylov-Functions.md` already uses
  `cgIterate A b 0 q` and the rename), K6, K8.
- `pcgIterate` and its outlier bound: K8 Nyström PCG (low-rank-plus-identity preconditioners);
  the PCG correspondence: K8's implementation statement.
- `minResidualInverse` (rectangular): GMRES, sketched GMRES (K6), block and deflated GMRES later.
- `residualMinimax`, `WorstCase.lean`: K2b (Greenbaum's worst case on every spectrum).
- `givensHessenberg…`: GMRES, MINRES; a later QR-algorithm stage (Hessenberg QR steps).
- `mgsArnoldi…`, the `arnoldiMatrix` column API: K4 (non-Hermitian Ritz values).
- `exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow`: CG, PCG, MINRES; K4.

## 8. Statements expected to be hard

1. `Matrix.IsHermitian.minresState_x_eq` (about 450 of `MINRESRecurrence`'s 700 lines): the
   induction ties three objects (preconditioned Lanczos, progressive Givens QR of a tridiagonal,
   the direction recursion), with the freeze past the grade.
2. The Givens progressive form and `isUpperTrapezoidal_givensHessenbergR`: index bookkeeping of
   rotations on `Fin` rows, the restriction to leading blocks.
3. `arnoldiMatrix_col_succ` and the Arnoldi realisations (450 to 600 lines with the moved layer).
4. `norm_sub_mulVec_gmresIterate_chebyshevTwoIntervalMatrix` (evenness by uniqueness) and the
   dual-weight identity `sum_neg_one_pow_mul_chebyshevWeight_mul_eval` (sign of $\ell_k(0)$).
5. `preconditionedLanczosState_z_eq_mulVec` and siblings: the square root and the
   $\mathbb{R} \to \Bbbk$ coercions in the step lemma.
6. The weighted `IsMinOn` for singular $\mathbf{A}$ and `pminresIterate_eq_mulVec_gmresIterate`.
The PCG and PMINRES bounds, the frame forms and the corollaries are short given these.

## 9. Questions for the maintainer

Only where the answer changes the design; recommendations in brackets.

1. **Preconditioned MINRES as a definition** through the Galerkin core (L5), or theorems only about
   $\mathbf{C}\,\mathsf{gmresIterate}(\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}, \dots)$, which
   puts a factor into statements? [Keep the definition.]
2. **The preconditioner hypothesis**: `spectrum ℝ (M * A) ⊆ s` with Loewner bridges (L4), or the
   spectral equivalence $a\mathbf{M}^{-1} \preceq \mathbf{A} \preceq a'\mathbf{M}^{-1}$ as
   primary? [Spectrum, D8's format.]
3. **A named rate**: $\rho$ appears in about fifteen statements; inline (brief O6) or a named
   `cgRate`? [Inline.]

[^L1]: Reversal: low, a mechanical rewrite.
[^L2]: Reversal: low.
[^L4]: Reversal: medium (every preconditioned statement).
[^L5]: Rejected: (a) one core only, GMRES as `galerkinInverse (Aᴴ * A) K * Aᴴ`: one definition
    fewer, but D3 approved `minResidualInverse` and its projector form is the natural GMRES
    residual; (b) a weighted core `minResidualInverse A M X`: a third name for one use. Reversal:
    low.

## 10. Bibliography

Present: `Saad2003`, `Saad2011`, `TrefethenBau1997`, `GolubVanLoan2013`, `HestenesStiefel1952`,
`Paige1972`, `HornJohnson2013`. New keys, added before citing, locators "to verify" until
checked: `Greenbaum1997` (§2.5, §3.1, §8.1, §8.2), `SaadSchultz1986` (Proposition 4),
`PaigeSaunders1975`, `EisenstatElmanSchultz1983` (Theorem 3.3), `ElmanSilvesterWathen2014`
(§4.2, Algorithm 4.1, Theorem 4.14). `Saad2003` locators (§6.5.3, §8.3, §9.2, Algorithms 6.2,
6.9, 9.1, Propositions 6.4 to 6.18, Theorem 6.30) and `TrefethenBau1997` Lectures 35 and 38 are
from memory and are verified before the PR.

## Implementation notes (2026-10-17)

- Checkpoint 1 landed with no statement changes. The two `Pinv` lemmas of §3.1
  (`pinv_mul_of_conjTranspose_mul_self_mul_eq`, `pinv_mul_conjTranspose_of_mul_conjTranspose_mul_self_eq`)
  were proved early, because `galerkinInverse_krylovMatrix_eq_arnoldiMatrix` needs them; checkpoint 3
  does not add them again. Bib keys `Greenbaum1997`, `PaigeSaunders1975` added (Greenbaum locators to
  verify).
- Checkpoint 5, Matrix layer: the six Givens QR theorems that mention `IsUpperHessenberg` live in a
  new `Matrix/Factorizations/GivensHessenberg.lean` (imports `Givens` and `Hessenberg`), not in
  `Givens.lean`: `Hessenberg.lean` defines `IsUpperHessenberg` and already imports `Givens.lean`, so
  the planned placement is an import cycle. The alternative, moving the definition of
  `IsUpperHessenberg` into `Triangular.lean` so the theorems can join `Givens.lean`, was not taken
  (it edits `Hessenberg.lean`, outside the stage's file list); it remains open for the maintainer.
  Five step lemmas of `Givens.lean` are public because the new file uses them.
- Checkpoint 2 landed with no statement changes. `PCG.lean` imports `Matrix/Spectral/Congruence.lean`
  for the factor `M = C Cᴴ` (`Matrix.PosDef.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose`),
  which no module of the chain imported before; no cycle. New public lemmas: `krylovMatrix_mul_mulVec`,
  `krylovSpace_mul_mulVec` (Space), `krylovGrade_mul_mulVec` (Grade), `spectrum_mul_conjTranspose_mul`,
  `Matrix.PosDef.spectrum_mul_subset_Icc_of_le` (Order). The PCG realisation takes only `A.PosDef`
  and `M.PosDef`.
- Checkpoint 2b (sharpness for CG): `eval_chebyshevResidual_chebyshevExtremum` drops its unused
  hypothesis `0 < a` (alternation needs only `a < a'`). `WorstCase.lean` holds only the CG part
  (`chebyshevExtremaMatrix`, `chebyshevErrorVector`, their positivity and spectrum, the two CG
  theorems); `chebyshevWeightVector`, the two-interval definitions and the MINRES theorems join it in
  checkpoint 3, with the import of `MINRES`.
