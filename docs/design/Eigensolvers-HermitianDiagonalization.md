# Design note: Hermitian diagonalization in linear precision — Newton–Schulz sign, randomized deflation and spectral bisection under black-box multiplication and QR (stage HDIAG)

Status: reviewed (Fable, `~/nlalib-harness/reports/Review-Fable-HDIAG-Design.md`: approve with
changes); APPROVE and OQ1–OQ13 pending with the maintainer (decision sheet
`~/nlalib-harness/state/decisions/HDIAG.json`). Review changes (second commit): items 1–3 applied
(new public EB1a child invariant and EB1b rank recovery; $\mathbf{P}_\pm$ stored by
`roundHermitian`), Event I now includes "seed in $[-1, 1]$" (without it EB1 was false: the sampler
contract says nothing outside $[-1, 1]$), and the non-blocking items 4–10 (EB4 route and label, UB1
without measurability of the bad sets, EB2 outline, R2 route and `0 ≤ u` on R2/R5/R6, EV7 at
$n = 0$, relabels, N10 orientation of `IsQRErr`/`IsUnifSampler`); 60 statements. Branch
`design/hdiag` (worktree `~/nlalib-design-hdiag`, from `origin/main` 4d4e9fc9). Targets:
`~/nlalib-harness/pilot/hdiag-targets.json` (60 statements).
Source read in full: R. Shah, *Fast Hermitian Diagonalization with Nearly Optimal Precision*,
arXiv:2408.09880v1 (LaTeX source; §1.2 model, Proposition 1.1, Definitions 1.1–1.4, §2 Lemmas
2.1–2.5 and Theorem 2.6, §3 Lemmas 3.1–3.2 and Theorem 3.3, §4 Algorithm 3, Lemma 4.1,
Theorem 4.2). The SODA 2025 version ("Hermitian diagonalization in linear precision") may number
or scale differently; it is not used. Library read: `NLAlib/Computation/{Contract,Rounding,Grid,
StaticCost,Syntax,Model,Exact}.lean`, `Matrix/Computation/BLAS.lean`, `Matrix/Basic/MatvecOracle.lean`,
`Matrix/Factorizations/QR.lean`, `Matrix/Perturbation/{DavisKahan,DavisKahanGap,Pseudospectrum}.lean`,
`Matrix/Functions/HermitianCalculus.lean`, `Matrix/Spectral/{HermitianPart,Inertia,Weyl,
LeastSingularValue}.lean`, `RandomMatrix/Gaussian/{Basic,Invariance,ExtremeSingularValues}.lean`,
`RandomMatrix/UnitaryInvariance.lean`, `Probability/Law.lean`, and the notes
`docs/design/{Computation,Matrix-Rounded-BLAS,Computation-Norm-Rounding,Matrix-Pseudospectrum,
Matrix-SpectralProjections,Matrix-EigenvectorDeflation}.md`.

Checks on the skeleton (all run on this branch, `LEAN_NUM_THREADS=2`, module targets only):
`lake build --wfail` of the seven new `NLAlib` modules (definitions only) succeeds;
`lake build NLAlibScaffold` gives exactly 60 `declaration uses sorry` warnings and nothing else;
`scripts/check_rules.py --files` on every touched file (0 errors; one warning, C8 on `Demmel1997`,
predates this stage), `check_refs.py`, `check_constants.py`, `check_latex.mjs` (KaTeX 0.16.22) and
both `lake exe mk_all --module --lib NLAlib --check` and `… --lib NLAlibScaffold --check` are
clean; `bin/check-skeleton --strict` (rule G3): 60 targets, 0 names missing an import, 0
unresolved. The extraction-based name check (N1–N18) was not run; names for review are in §9.

## Maintainer decisions already made (2026-11-05)

1. **Arithmetic model: unbounded exponent, pure relative error first**, on main's contract layer,
   with the bounded-exponent model (Codex's uncommitted `binaryFloatSem`, real only, in progress)
   a later drop-in. Consequence here: every contract carries a floor $\tau$ (absolute error below
   $\tau$, gradual underflow) and a range $\Omega$ (overflow), $\tau = 0$ and $\Omega$ arbitrary in
   the unbounded model; every theorem carries the range hypotheses it needs, so the bridge (§12)
   rewrites no statement.
2. **Port the essence**: constants may change. Edelman's $\sigma_{\min}$ law (Lemma 3.1) is
   replaced by an elementary bound losing a factor $2n$ (OQ7); the contour Lemma 2.2 by a
   Hermitian Davis–Kahan bound (OQ6).
3. **Black-box MM and QR are hypotheses** (normwise predicates with $\mu_{\mathrm{MM}}$,
   $\mu_{\mathrm{QR}}$, $\mathrm{MM}(\mathbf{A}, \mathbf{A}^{\mathsf{H}})$ exactly Hermitian), not
   implementations; runtime is out of scope (OQ11 on static counts).

## 0. Summary

| | |
|---|---|
| Model (new) | a rounding function $\mathrm{fl} : \mathbb{R} \to \mathbb{R}$ with `IsRoundingFn u τ Ω fl` ($\lvert \mathrm{fl}(x) - x \rvert \le u\max(\lvert x \rvert, \tau)$ for $\lvert x \rvert \le \Omega$), applied to real and imaginary parts; Hermitian-preserving roundings `roundDiag`, `roundHermitian`, `roundedSum`; black-box contracts `IsMatMulErr u τ Ω μ mm`, `IsQRErr u τ Ω μ qr`, sampler couplings `IsUnifSampler`, `IsNormalSampler`; the witness `isRoundingFn_roundNearest` ties the model to `Computation.gridSem`, which meets `IsRelErrSem` |
| Algorithms (new definitions, `NLAlib`, build `--wfail`) | `newtonSchulz` and `newtonSchulzSteps` (scalar); `newtonSchulzRounded`, `IsNewtonSchulzConverged`, `newtonSchulzLoop`, `newtonSchulzSign` (Algorithm 1); `deflate` (Algorithm 2); `EighPrimitives`, `EighSample`, `leadingBlock`, `bisectionSignTol`, `bisectionDepth`, `EighStep`, `EighStep.IsSplit`, `eighStep`, `eighAux`, `eigh` (Algorithm 3), `EighNode`, `eighChild`, `eighNodeAt` (the recursion tree), `IsApproxDiagonalization` (output guarantee), `IsEighGoodSample` (Events I, II); `complexGaussian`, `complexGaussianVector`, `complexGaussianMatrix` |
| Headline | Theorem 4.2 (EV6): with probability at least $1 - \theta$, $\mathsf{eigh}$ returns $(\mathbf{U}, \mathbf{d})$ with $\|\mathbf{A} - \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}\|_2 \le 2\varepsilon R_0$ and $\sigma_i(\mathbf{U}) \in [1 \pm \varepsilon/3]$, under explicit precision hypotheses; in bits (EV7) $\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ |
| Other results | Lemmas 2.1, 2.3–2.5, Theorem 2.6 (SIGN, SN4), Theorem 3.3 (deterministic DF2, probabilistic DP1), Lemma 4.1 (EB1), Proposition 1.1 (LB3, OQ5); the replacements of Lemmas 2.2 (SG2) and 3.1 (CG6) |
| Paper gaps found and fixed | G1 the iterates of SIGN and the compressions $\mathbf{C}_\pm$ are treated as Hermitian but MM does not make them so (fixed by rounded Hermitian parts, OQ8); G2 the probability of missing Event I is $nw\ell/R$, not $nw/R$ (factor $\ell$ dropped, OQ9; costs one $\log_2\log_2(1/\varepsilon)$); G3 Proposition 1.1's sign-of-entries argument bounds the Frobenius norm, not the spectral norm (fixed by choosing the sign from $\mathbf{1}^{\mathsf{T}}\mathbf{R}\mathbf{1}$, same conclusion); G4 Lemma 4.1's bound on $\|\mathbf{D}_\pm\|_2$ drops the $R_0$ part of the children's residual (absorbed by the slack $\varepsilon R_0/\ell$). Side condition (not a paper gap): Lemma 2.5 needs $\varepsilon > 0$ and $x_0 \ne 0$ explicitly because $u = 0$ is allowed. Also noted: the paper's depth check compares $R_\ell$ with $\varepsilon$, not $\varepsilon_\ell$; its Lemma 2.5 proof needs $\lvert x_k\rvert \ge 20u$ throughout (NS9) |
| Statements | 60 sorried: S 19, M 26, L 12, H 3, in 12 scaffold files (§3.11) |
| Staging | W1 scalar, rounding, contracts, sign facts (28); W2 SIGN (4); W3 complex Gaussian and DEFLATE (10); W4 union bound and EIGH (15); LB Proposition 1.1 (3); W5 bounded-exponent bridge later (§12) |
| Open questions | 13 (§10), each with a recommendation |

## 1. Scope

**In.** (i) A shallow finite-precision model for dense complex Hermitian computations: a rounding
function with floor and range, entrywise Hermitian roundings, rounded summation, normwise
black-box contracts for matrix multiplication and QR, and coupling contracts for the two samplers
(Definitions 1.1–1.4). (ii) The scalar Newton–Schulz iteration under perturbation (Lemmas
2.3–2.5) and the Hermitian matrix sign: perturbation (replacing Lemma 2.2), the one-step error
(Lemma 2.1) and the accuracy of Algorithm 1 (Theorem 2.6). (iii) The standard complex Gaussian
law, its realification and unitary invariance, the norm tail (Lemma 3.2) and an elementary
smallest-singular-value tail (replacing Lemma 3.1); deflation, deterministic and with Gaussian
probability (Theorem 3.3). (iv) Algorithm 3 as a total function of its primitives and a tree of
ideal samples, its local guarantee (Lemma 4.1), depth and counts, the global deterministic
guarantee, a generic union bound for adaptively chosen events with fresh samples, the
independence of the nodes from their own samples, and Theorem 4.2 in tail form and in bits.
(v) Proposition 1.1 (lower bound, OQ5).

**Out** (§11): operation counts and runtime ($T_{\mathrm{MM}}$, $T_{\mathrm{QR}}$, the
$O(\log(1/\varepsilon)\cdots T_{\mathrm{MM}}(n))$ of Theorem 4.2; OQ11); implementations of fast
MM/QR meeting the contracts (DDH07, DDHK07) and any complex gemm through the real BLAS kernels;
the bounded-exponent instance (§12, needs Codex's model on main); boosting the success probability
(the remark after Theorem 4.2); the non-Hermitian case; real symmetric input with a real Gaussian
start (the complex algorithm already covers it by embedding).

## 2. Objects

### 2.1 Rounding (`NLAlib/Matrix/Computation/EntrywiseRounding.lean`, written)

```lean
def IsRoundingFn (u τ Ω : ℝ) (fl : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, |x| ≤ Ω → |fl x - x| ≤ u * max |x| τ
noncomputable def roundScalar (fl : ℝ → ℝ) (z : 𝕜) : 𝕜          -- fl(Re z) + fl(Im z) i
noncomputable def roundDiag [DecidableEq n] (fl) (X : Matrix n n 𝕜) : Matrix n n 𝕜
noncomputable def roundHermitian [LinearOrder n] (fl) (X : Matrix n n 𝕜) : Matrix n n 𝕜
noncomputable def roundedSum (fl : ℝ → ℝ) {k : ℕ} (x : Fin k → ℝ) : ℝ   -- left to right
```

The paper's model is $\lvert \mathrm{fl}(z) - z \rvert \le u\lvert z \rvert$ for complex $z$, every
operation rounding its exact result. Here a rounding *function* of the exact real value is applied
to real and imaginary parts separately (componentwise complex storage, as hardware does), which
gives the paper's bound for $\tau = 0$ (R2) and keeps Hermitian structure exact by construction:
`roundHermitian` rounds the strict upper triangle and the real diagonal and mirrors, so it is
Hermitian for every rounding (R3), with no oddness assumption on $\mathrm{fl}$ (round-half-up
is not odd). The relation to main's contract layer (decision 1) is the witness R1:
`Real.roundNearest t`, the rounding of `Computation.gridSem t`, which meets
`Computation.IsRelErrSem` (`Computation.isRelErrSem_gridSem`), satisfies
`IsRoundingFn (2⁻¹ ^ t) 0 Ω` for every $\Omega$. Contract.lean is not modified (OQ2).

### 2.2 Black boxes (`NLAlib/Matrix/Computation/Primitives.lean`, written)

```lean
abbrev MatMulMap (𝕜) := ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) 𝕜 → Matrix (Fin m) (Fin n) 𝕜 → Matrix (Fin l) (Fin n) 𝕜
abbrev QRMap (𝕜) := ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) 𝕜 → Matrix (Fin m) (Fin m) 𝕜 × Matrix (Fin m) (Fin n) 𝕜
structure IsMatMulErr (u τ Ω : ℝ) (μ : ℕ → ℝ) (mm : MatMulMap 𝕜) : Prop where
  specNorm_mul_sub_le : ∀ {l m n} (A) (B), specNorm A * specNorm B ≤ Ω →
    specNorm (A * B - mm A B) ≤ μ (max l (max m n)) * u * max (specNorm A * specNorm B) τ
  isHermitian_conjTranspose : ∀ {m n} (A : Matrix (Fin m) (Fin n) 𝕜), Matrix.IsHermitian (mm A Aᴴ)
def IsQRErr (u τ Ω) (μ) (qr : QRMap 𝕜) : Prop :=
  ∀ {m n} (A), specNorm A ≤ Ω → IsUpperTrapezoidal (qr A).2 ∧ ∃ Q', HasOrthonormalCols Q' ∧
    specNorm (Q' - (qr A).1) ≤ μ (max m n) * u ∧ specNorm (A - Q' * (qr A).2) ≤ μ (max m n) * u * max (specNorm A) τ
def IsUnifSampler (u) (unif : ℝ → ℝ → ℝ) : Prop :=        -- scale s, ideal seed v ∈ [-1, 1]
  ∀ s v, 0 ≤ s → v ∈ Set.Icc (-1) 1 → |unif s v| ≤ s ∧ |s * v - unif s v| ≤ s * u
def IsNormalSampler (u c) (normal : ℂ → ℂ) : Prop := ∀ z, ‖z - normal z‖ ≤ c * u * ‖z‖
```

Routines are total functions on `Fin`-indexed matrices of every shape (the recursion changes sizes,
so `Fin` carries content, T6); $\mu$ is a function of the largest dimension. The samplers are
deterministic perturbations of ideal samples: the paper's "there is a coupling" is realised by the
ideal sample itself, which is what the probability argument conditions on. Witnesses: exact
multiplication (C1) and an exact QR (C2) meet the contracts for every $u \ge 0$, so they are
satisfiable. Errors are written exact minus computed (N10).

### 2.3 Algorithms (`NLAlib/Matrix/Computation/{NewtonSchulzSign,Deflation,SpectralBisection}.lean`, written)

* `newtonSchulzRounded mm fl A` $= \mathrm{roundHermitian}\bigl(\tfrac12\operatorname{herm}\,
  \mathrm{mm}(\mathbf{A}, \mathrm{roundDiag}(3\mathbf{I} - \mathrm{mm}(\mathbf{A},\mathbf{A})))\bigr)$;
  `newtonSchulzLoop mm fl η N` tests (`IsNewtonSchulzConverged`: every entry of the computed
  $\mathbf{I} - \mathrm{mm}(\mathbf{A},\mathbf{A})$ has $\lvert\operatorname{Re}\rvert,
  \lvert\operatorname{Im}\rvert \le \eta$) and steps at most $N$ times; `newtonSchulzSign mm fl ε b N A`
  starts from the rounded $\mathbf{A}/b$ with $\eta = \varepsilon/(4n)$.
* `deflate mm qr normal r P G`: the first $r$ columns of $\mathrm{qr}(\mathrm{mm}(\mathbf{P},
  \mathbf{G}.\mathrm{map}\ \mathrm{normal}))$.
* `eighStep P N signFuel R₀ ρ A R ε ℓ s : EighStep k` is one node: leaf
  ($k \le 1$: $(\mathbf{I}, \operatorname{Re}\operatorname{diag}\mathbf{A})$; $R \le \varepsilon R_0$:
  $(\mathbf{I}, \mathbf{0})$), one child (`shift b A' σ`, all eigenvalues on one side), or a split
  (`split kp h Qp Qm Ap Am σ`). `eighAux` recurses on a budget and assembles
  $[\mathrm{mm}(\mathbf{Q}_+, \mathbf{U}_+)\ \mathrm{mm}(\mathbf{Q}_-, \mathbf{U}_-)]$ with
  $\mathrm{fl}(d_\pm \pm R/2)$; `eigh` is the root call ($\rho = \theta/(4n)$, $\ell$ =
  `bisectionDepth ε` $= \lceil\log_2(1/\varepsilon)\rceil + 5$, budget $\ell + 1$). The scale $R_0$ is
  an input with $\|\mathbf{A}\|_2 \le R_0$ (the paper's $R_0 = \|\mathbf{A}\|_2$, not a floating-point
  primitive; $R_0 = \|\mathbf{A}\|_{\mathsf F}$ is a computable choice).
* Randomness: a tree of ideal samples `s : List Bool → EighSample N`,
  `EighSample N = ℝ × (Bool → Matrix (Fin N) (Fin N) ℂ)` (seed, two Gaussian matrices); the node at
  path `a` uses `s a` and its children the subtrees `fun a' => s (b :: a')`; a node of size $k$
  uses the leading $k \times k$ blocks. `eighNodeAt` computes the node at a path; the probability
  argument works with it (OQ3).
* `IsApproxDiagonalization A U d η κ` (structure): residual $\le \eta$ and
  $(1-\kappa)^2\mathbf{I} \preceq \mathbf{U}^{\mathsf{H}}\mathbf{U} \preceq (1+\kappa)^2\mathbf{I}$
  (vocabulary: spectral bound on a factor in Loewner form). `IsEighGoodSample w x t y s`: Event I
  ($\lvert\lambda - c'\rvert \ge w$ for all eigenvalues, $c' = (R/\ell)v$) and Event II (for each
  side with true projector of rank $0 < r < k$ and every orthonormal basis $\mathbf{V}$ of it,
  $\|\mathbf{G}\|_2 < t$ and $\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) > x$).

Modelling deviations from Algorithms 1 and 3 (OQ12): scalar parameters $R$, $\varepsilon$,
$\ell$, $\beta$ exact; $k_- = k - k_+$ with $k_+$ capped at $k$; stopping test componentwise and
applied before each step (the paper's repeat–until steps first; harmless: a passing start is
already accurate); explicit step caps (`signFuel`, recursion budget) whose sufficiency is a
hypothesis/theorem; rounded Hermitian parts of the iterates and compressions (OQ8); the projectors
$\mathbf{P}_\pm = \tfrac12(\mathbf{I} \pm \mathbf{B})$ stored by `roundHermitian` (every entry
rounded), so a bounded-exponent model never needs exact halving of subnormals (review item 3);
Event I of `IsEighGoodSample` includes "seed in $[-1, 1]$" (a null event under the law).

### 2.4 Complex Gaussian (`NLAlib/RandomMatrix/Gaussian/Complex.lean`, written)

`complexGaussian` = law of $x + iy$, $x, y \sim \mathcal{N}(0, 1/2)$ independent ($\mathbb{E}\lvert
z\rvert^2 = 1$, the paper's normalisation); `complexGaussianVector n`, `complexGaussianMatrix m n`
are `Measure.pi` abbrevs as the real `gaussianVector`, `gaussianMatrix` (rows of vectors). Bridges:
CG0 to Mathlib's `stdGaussian ℂ` (variance $1$ per part, so $\sqrt2$ times ours), CG1 to the real
`gaussianMatrix (m ⊕ m) n` (realification). A `docs/design/Mathlib-deviations.md` entry for
"`complexGaussian` next to `stdGaussian ℂ`" is due with the implementation PR; that file is being
edited elsewhere now, so it is not touched here (OQ4).

### 2.5 Sample law (`NLAlibScaffold/Eigensolvers/SpectralBisection.lean`, scaffold definition)

`eighSampleLaw N := (cond volume (Icc (-1) 1)).prod (Measure.pi fun _ : Bool =>
complexGaussianMatrix (Fin N) (Fin N))`. It needs RandomMatrix, so it lives in the new folder (OQ1)
and is a scaffold definition until that folder has a layer.

## 3. Statements

The exact Lean signatures are in the skeleton; each docstring has the statement in LaTeX, the
citation and a `Proof:` line with difficulty; the targets file has the outline per declaration.

### 3.1 Scalar Newton–Schulz (NS1–NS12, `Polynomial/Approximation/NewtonSchulz.lean`)

$g(x) = \tfrac12x(3 - x^2)$. NS2 is the identity $1 - g(x)^2 = (1 - x^2)^2(4 - x^2)/4$, which gives
NS3 ($\lvert g \rvert \le 1$ on $[-2, 2]$) and NS7 (Lemma 2.4b) at once. NS4/NS5 are Lemma 2.3,
NS6 Lemma 2.4a, NS10 Lemma 2.5: for $0 < \varepsilon \le 3/80$, $10u \le \varepsilon$,
$0 < \lvert x_0\rvert$, $20u \le \lvert x_0\rvert \le 3/2$ and $\lvert x_{k+1} - g(x_k)\rvert \le
u$, $\lvert 1 - x_N^2\rvert \le \varepsilon$ for every natural $N \ge$ `newtonSchulzSteps x₀ ε`.
NS8 and NS9 are the invariants $\lvert x_{k+1}\rvert \le 1 + u$ and $\lvert x_k\rvert \ge
\min(\lvert x_0\rvert, 1/2)$ (the latter used implicitly in Theorem 2.6 when every step is bounded
by $a/b$). NS11/NS12: monotonicity of the step count. Degenerate cases:
$u = 0$ is exact arithmetic (allowed; then $x_0 \ne 0$ is needed, hence `h₀`); $\varepsilon = 0$
would make NS10 false (the iteration converges only in the limit), hence `hε`.

### 3.2 The Hermitian sign (SG1–SG6, `Matrix/Functions/Sign.lean`)

The sign is `cfc Real.sign A` (vocabulary row "function of a Hermitian matrix"). **SG2** replaces
Lemma 2.2: for Hermitian $\mathbf{A}, \mathbf{B}$ with $\lvert\lambda\rvert \ge a > 0$ on the
spectrum of $\mathbf{A}$, $\|\operatorname{sign}\mathbf{A} - \operatorname{sign}\mathbf{B}\|_2 \le
2\|\mathbf{A} - \mathbf{B}\|_2/a$ — dimension-free and with no size condition (the paper:
$n\|\mathbf{E}\|/(a - \|\mathbf{E}\|)$). Proof by the library's Davis–Kahan theorem
(`Matrix.IsHermitian.specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap`), gap $\ge 2a$, equal
ranks by Weyl. SG1 ($g$ of a Hermitian matrix is the polynomial), SG3 ($\operatorname{sign}\circ g
= \operatorname{sign}$ on $0 < \lvert x\rvert < \sqrt3$), SG4 ($\|\mathbf{A} -
\operatorname{sign}\mathbf{A}\|_2 \le \max\lvert 1 - \lambda^2\rvert$), SG5 (frames of the spectral
projectors, invariance, spectrum of the compression), SG6 (trace of the projector = inertia).

### 3.3 Rounding and contracts (R1–R7, C1–C3)

R1 the grid witness; R2 scalar error $u(\lvert z\rvert + 2\tau)$; R3, R4 Hermitian; R5
$\|\mathbf{X} - \mathrm{roundHermitian}\,\mathbf{X}\|_2 \le u(\sqrt n\|\mathbf{X}\|_2 + 2n\tau)$;
R6 $\|\mathbf{X} - \mathrm{roundDiag}\,\mathbf{X}\|_2 \le u\max(\|\mathbf{X}\|_2, \tau)$ (diagonal
error, as the paper notes in Lemma 2.1); R7 rounded summation $2ku(\sum\lvert x_i\rvert + k\tau)$
for $ku \le 1/2$. C1, C2 witnesses; **C3** the bridge (b) of §12: a mixed bound
$\mu u\|\mathbf{A}\|\|\mathbf{B}\| + \eta$ with $\eta \le \mu u\tau$ gives `IsMatMulErr` with $2\mu$.

### 3.4 Algorithm 1 (SN1–SN4, `Matrix/Computation/NewtonSchulzSign.lean`)

**SN3** (Lemma 2.1): for Hermitian $\|\mathbf{A}\|_2 \le 11/10$, $u(8 + \mu(n)) \le 1/10$,
$2n\tau \le 1$, $\Omega \ge 8$: $\|g(\mathbf{A}) - \tilde g(\mathbf{A})\|_2 \le 4\sqrt n(8 +
\mu(n))u$. Stated in the iteration's regime rather than for every $a$: with floors, a general-$a$
statement needs $a$-dependent floor conditions, and the only consumer is SN4. The $\sqrt n$ is the
price of storing the step Hermitian (G1/OQ8).

**SN4** (Theorem 2.6): Hermitian $\mathbf{A}$, $\|\mathbf{A}\|_2 \le b$, $\lvert\lambda\rvert \ge
a > 0$, $0 < \varepsilon \le 1/2$, $N_0 = N(a/(2b), \varepsilon/(16n))$,
$640n^{3/2}(8 + \mu(n))(N_0 + 1)u \le (a/b)\varepsilon$, step cap $\ge N_0$:
$\|\operatorname{sign}\mathbf{A} - \mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)\|_2 \le
\varepsilon$. Constants derived in the docstring's proof sketch: start error $2\sqrt nu$; step
error $\nu u$, $\nu = 4\sqrt n(8 + \mu)$; scalar chains via NS9/NS10 at tolerance
$\varepsilon/(16n)$; stop by step $\lceil N_0\rceil$; at the stop $\|\mathbf{I} -
\mathbf{A}_M^2\|_2 \le 0.37\varepsilon$; telescoped signs $\le 8(N_0 + 1)\nu u\,b/a \le
\varepsilon/(20n)$. Compared with the paper ($u \le \frac ab\varepsilon/(4\max(Nn\mu_g,
n^2))$): $n\mu_g$ becomes $n^{3/2}(8 + \mu)$.

### 3.5 Complex Gaussian (CG0–CG6, `RandomMatrix/Gaussian/Complex.lean`)

CG0 Mathlib bridge, CG1 realification, CG2 $\mathbf{V}^{\mathsf{H}}\mathbf{G}$ is standard complex
Gaussian for $\mathbf{V}$ with orthonormal columns (through the real orthogonal invariance
`hasLaw_const_mul_of_hasLaw_gaussianMatrix` on the realified $\mathbf{V}^{\mathsf{H}}$), CG3
submatrices. **CG4** (Lemma 3.2): $\mathbb{P}[\sqrt2(\sqrt m + \sqrt n + t) \le \|\mathbf{G}\|_2]
\le 2e^{-t^2/2}$ from the real Gordon tail. **CG6** (Lemma 3.1, OQ7):
$\mathbb{P}[\sigma_{\min}(\mathbf{G}) \le x] \le r^2x^2$ for $r \times r$, via the library's
`exists_iInf_norm_mulVec_le_of_singularValues_le` (a small $\sigma_{\min}$ puts a column within
$\sqrt r\,x$ of the span of the others) and **CG5**: $\mathbb{P}[\|\mathbf{\Pi}\mathbf{g}\| \le s]
\le s^2$ for a nonzero projector $\mathbf{\Pi}$ (two real degrees of freedom per complex
coordinate: $\lvert z\rvert^2 \sim \mathrm{Exp}(1)$). Edelman: $(r/2)x^2$ (paper) or $1 -
e^{-rx^2}$; the loss $2r$ costs $\le \log_2 n + 1$ bits.

### 3.6 Algorithm 2 (DF1, DF2 `Matrix/Computation/Deflation.lean`; DP1 `Eigensolvers/RandomizedDeflation.lean`)

**DF1** (the "three inequalities", exact): $\mathbf{U}, \mathbf{Q}'$ orthonormal columns,
$\|\mathbf{Q}_1 - \mathbf{Q}'\|_2 \le \nu \le \delta \le 1/5$, $\|\mathbf{U} -
\mathbf{Q}_1\mathbf{C}\|_2 \le \delta$ ⟹ $\|\mathbf{U}\mathbf{W} - \mathbf{Q}_1\|_2 \le 6\delta$
for a unitary $\mathbf{W}$ (polar factor of $\mathbf{U}^{\mathsf{H}}\mathbf{Q}_1$; this is the
square-root-free step that is the paper's §3 contribution). **DF2** (Theorem 3.3, deterministic):
$\mathbf{A} = \mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$ (general invertible $\mathbf{S}$, the
paper's $\mathbf{\Sigma}$), $\|\mathbf{A} - \widetilde{\mathbf{A}}\|_2 \le \beta$,
$\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ invertible, $m = (\|\mathbf{S}\|_2 + \beta +
1)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$, $m\beta \le
1/5$, $(4\mu_{\mathrm{QR}} + 2\sqrt nc_{\mathrm N} + 2\mu_{\mathrm{MM}})u \le \beta$, floor/range
conditions ⟹ $\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le
6m\beta$. **DP1**: with $\mathbf{G}$ standard complex Gaussian, $\bar m = (\|\mathbf{S}\|_2 +
2)\|\mathbf{S}^{-1}\|_2\sqrt2(2\sqrt n + t)/x$, failure $\le 2e^{-t^2/2} + r^2x^2$.

### 3.7 Union bound with fresh samples (UB1, `Probability/AdaptiveUnionBound.lean`)

Index set countable (paths), samples $\zeta_i \sim \nu$, states $X_i$ with countable range,
measurable fibres $\{X_i = y\}$ independent of $\zeta_i$, bad sets $S_i(y)$ (not assumed
measurable; the proof passes to `toMeasurable`) with $\nu(S_i(y)) \le
\int q_i(y, \cdot)\,d\nu$, $\sum_i q_i(X_i, \zeta_i) \le \theta$ surely ⟹ $\mathbb{P}[\exists i,
\zeta_i \in S_i(X_i)] \le \theta$. The charge $q$ lets the bound count "expected number of splits"
(Event II is charged only at splits, as in the paper's $\lvert X_D\rvert = n - 1$) although the
split is decided by the node's own sample. Independence is stated with the Prop-valued indicator,
so no measurable space on the (dependent-type) node states is needed.

### 3.8 Algorithm 3, deterministic (EB1–EB5, `Matrix/Computation/SpectralBisection.lean`)

**EB1b** (rank recovery on Event I, public so that EV2 can use it): for an internal node with
seed in $[-1, 1]$ and Event I, the step splits iff $0 < i_+(\mathbf{A} - c'\mathbf{I}) < k$.
**EB1a** (child invariant): under EB1's hypotheses without the children's guarantee, every child
has a Hermitian matrix of norm at most its window — what EB5's induction needs at each child.
**EB1** (Lemma 4.1): node contracts and precision hypotheses (written in §3.11's table and the
docstring), good sample when internal ($k \ge 2$, $R > \varepsilon R_0$), children approximate
diagonalizations with $(\varepsilon'(R' + R_0), \varepsilon'/3)$ ⟹ node output with
$(\varepsilon(R + R_0), \varepsilon/3)$, using EB1a and EB1b. EB2 depth $\le \ell$ (exact telescoping
$\prod_{i<\ell}\frac{\ell+i+4}{\ell+i} = \frac{2\ell(2\ell+1)(2\ell+2)(2\ell+3)}{\ell(\ell+1)(\ell+2)(\ell+3)}$
against $\varepsilon_\ell = \varepsilon(\ell-1)/(2\ell-1)$; the paper compares with $\varepsilon$
instead of $\varepsilon_\ell$, which is also fine but by a margin of order $1/\ell$). EB3 at most
$(n+1)(\ell+1)$ nodes, EB4 at most $n$ splits (by induction on the path length, since the tree
may be infinite without depth hypotheses). **EB5**: every internal node good ⟹
$\mathsf{eigh}$ is an approximate diagonalization with $(2\varepsilon R_0, \varepsilon/3)$, under
the global hypotheses with
$$\beta = \frac{\varepsilon\sqrt\theta}{2880\,\ell n^{3/2}(2\sqrt n + \sqrt{2\log(16n/\theta)})}
,\quad N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac\beta{16n}\Bigr),$$
$640n^{3/2}(8 + \mu_{\mathrm{MM}})(N_* + 1)\cdot16n(n+1)\ell(\ell+1)u \le \theta\beta$,
$(4\mu_{\mathrm{QR}} + 2\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}} + 1)u \le \beta$, step cap
$\ge N_*$, $4n\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon R_0/3)$, $16(R_0 + n +
\sqrt{\log(16n/\theta)}) \le \Omega$. Node parameters: $w_y = \theta R_y/(2k_y\ell_y(n+1)(\ell+1))$
(the corrected Event I budget, G2), $x_y = \sqrt{\rho/2}/k_y$, $t_y = \sqrt2(2\sqrt{k_y} +
\sqrt{2\log(4/\rho)})$, $\rho = \theta/(4n)$; with these the deflation tolerance
`bisectionSignTol` gives output error exactly $\eta = \varepsilon'/(5\ell)$ and $m\beta = \eta/6$.

### 3.9 Algorithm 3, probability (EV1–EV7, `Eigensolvers/SpectralBisection.lean`)

EV1 the shift misses a finite set: $\le \lvert\Lambda\rvert w/c$ (with $c = R/\ell$: $nw\ell/R$,
G2). EV2 node bad-event bound $kw\ell/R + 2\rho\,\mathbb{P}[\text{split}]$. EV3–EV5: the node at
a path has countably many values, measurable fibres, and is independent of its own sample —
**without any measurability assumption on MM, QR or fl**: the computed samples are measurable maps
of the ideal ones into countable sets (floating-point numbers are countable), and every node is a
function of finitely many of them (OQ3). **EV6** (Theorem 4.2): the global hypotheses of EB5,
samplers measurable with countable ranges, $(\zeta_a)$ independent with law `eighSampleLaw n` ⟹
failure probability $\le \theta$. **EV7**: the same with the precision conditions replaced by
$$\log_2\tfrac1u \ge \log_2\tfrac1\varepsilon + \tfrac32\log_2\tfrac1\theta +
\log_2\bigl(n^4(n+1)(8 + \mu_{\mathrm{MM}}) + n^{3/2}(4\mu_{\mathrm{QR}} + 2\sqrt n(c_{\mathrm N}+1)
+ 2\mu_{\mathrm{MM}} + 1)\bigr) + \log_2(N_* + 1) + 3\log_2(\ell + 1) + \log_2(2\sqrt n +
\sqrt{2\log(16n/\theta)}) + 25,$$
i.e. $\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$
(paper: $n^{4.5}\mu$ and $2\log_2\log_2(1/\varepsilon)$; ours $n^5\mu$ and $3\log_2\ell$, from
the Hermitian rounding, the stopping test and G2).

### 3.10 Proposition 1.1 (LB1–LB3, `LowerBounds/Eigensolvers/Precision.lean`, OQ5)

LB1: for every $\mathbf{M}$ one of $\mathbf{M} \pm \delta\mathbf{J}$ has norm $\ge \delta n$ (the
sign chosen from $\operatorname{Re}\mathbf{1}^{\mathsf{H}}\mathbf{M}\mathbf{1}$; G3). LB2: a method
seeing only rounded input, with backward error $\varepsilon\|\mathbf{A}\|_2$ on all real symmetric
$\mathbf{A}$, and a symmetric $\mathbf{H}$ whose entries absorb $\pm\delta$ under the rounding,
has $\delta n \le \varepsilon(\|\mathbf{H}\|_2 + \delta n)$. LB3: Walsh–Hadamard
($n = 2^b$, `walshHadamard`) and `Real.roundNearest t`, $\delta = 2^{-t}/4$: $t \ge
\log_2(1/\varepsilon) + b/2 - 2 + \log_2(1 - \varepsilon)$.

### 3.11 Full list

**Polynomial/Approximation/NewtonSchulz.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| NS1 | `newtonSchulz_neg` | S | 0 | — |
| NS2 | `one_sub_newtonSchulz_sq` | S | 0 | — |
| NS3 | `abs_newtonSchulz_le_one` | S | 1 | NS2 |
| NS4 | `mul_newtonSchulz_add_pos` | M | 1 | NS1 |
| NS5 | `abs_le_abs_newtonSchulz_add` | S | 1 | NS1 |
| NS6 | `abs_one_sub_sq_newtonSchulz_add_le` | M | 1 | NS1, NS2 |
| NS7 | `abs_one_sub_sq_newtonSchulz_add_le_add` | S | 2 | NS2, NS3 |
| NS8 | `abs_le_one_add_of_abs_sub_newtonSchulz_le` | S | 2 | NS3 |
| NS9 | `min_abs_le_abs_of_abs_sub_newtonSchulz_le` | M | 3 | NS5, NS8 |
| NS10 | `abs_one_sub_sq_le_of_newtonSchulzSteps_le` | L | 4 | NS5, NS6, NS7, NS8, NS9 |
| NS11 | `newtonSchulzSteps_le_of_le_abs` | S | 0 | — |
| NS12 | `newtonSchulzSteps_le_of_le` | S | 0 | — |

**Matrix/Functions/Sign.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| SG1 | `Matrix.IsHermitian.cfc_newtonSchulz` | M | 0 | — |
| SG2 | `Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le` | M | 0 | — |
| SG3 | `Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz` | M | 2 | NS4 |
| SG4 | `Matrix.IsHermitian.specNorm_sub_cfc_sign_le` | S | 0 | — |
| SG5 | `Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq` | M | 0 | — |
| SG6 | `Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign` | M | 0 | — |

**Matrix/Computation/EntrywiseRounding.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| R1 | `isRoundingFn_roundNearest` | S | 0 | — |
| R2 | `IsRoundingFn.norm_sub_roundScalar_le` | M | 0 | — |
| R3 | `isHermitian_roundHermitian` | S | 0 | — |
| R4 | `Matrix.IsHermitian.isHermitian_roundDiag` | S | 0 | — |
| R5 | `IsRoundingFn.specNorm_sub_roundHermitian_le` | M | 1 | R2 |
| R6 | `IsRoundingFn.specNorm_sub_roundDiag_le` | M | 0 | — |
| R7 | `IsRoundingFn.abs_sum_sub_roundedSum_le` | M | 0 | — |

**Matrix/Computation/Primitives.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| C1 | `isMatMulErr_mul` | S | 0 | — |
| C2 | `exists_isQRErr` | S | 0 | — |
| C3 | `IsMatMulErr.of_specNorm_mul_sub_le_add` | S | 0 | — |

**Matrix/Computation/NewtonSchulzSign.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| SN1 | `isHermitian_newtonSchulzRounded` | S | 1 | R3 |
| SN2 | `isHermitian_newtonSchulzSign` | S | 2 | R3, SN1 |
| SN3 | `IsMatMulErr.specNorm_sub_newtonSchulzRounded_le` | M | 2 | R5, R6 |
| SN4 | `IsMatMulErr.specNorm_cfc_sign_sub_newtonSchulzSign_le` | L | 5 | SN3, SG1, SG2, SG3, SG4, NS9, NS10, NS11, NS12, R5, R6 |

**RandomMatrix/Gaussian/Complex.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| CG0 | `complexGaussian_eq_map_stdGaussian` | M | 0 | — |
| CG1 | `complexGaussianMatrix_eq_map_gaussianMatrix` | L | 0 | — |
| CG2 | `hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix` | M | 1 | CG1 |
| CG3 | `hasLaw_submatrix_of_hasLaw_complexGaussianMatrix` | M | 1 | CG1 |
| CG4 | `measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix` | M | 1 | CG1 |
| CG5 | `measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector` | L | 2 | CG2 |
| CG6 | `measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix` | L | 3 | CG5, CG3 |

**Matrix/Computation/Deflation.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| DF1 | `HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le` | M | 0 | — |
| DF2 | `IsMatMulErr.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` | L | 1 | DF1 |

**Eigensolvers/RandomizedDeflation.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| DP1 | `IsMatMulErr.measureReal_not_exists_specNorm_mul_sub_deflate_le_le` | M | 4 | DF2, CG2, CG3, CG4, CG6 |

**Probability/AdaptiveUnionBound.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| UB1 | `measureReal_exists_mem_le_of_forall_measure_le_lintegral` | L | 0 | — |

**Matrix/Computation/SpectralBisection.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| EB1b | `eighStep_isSplit_iff_of_forall_le_abs_sub` | M | 6 | SN4, SG2, SG6, R5, R6, R7 |
| EB1a | `isHermitian_and_specNorm_le_of_eighChild_eq_some` | M | 7 | EB1b, SG5, DF2, R3, R4, R5, R6 |
| EB1 | `isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` | H | 8 | EB1a, EB1b, SG5, DF1, DF2, R5 |
| EB2 | `eighNodeAt_eq_none_of_bisectionDepth_lt_length` | M | 0 | — |
| EB3 | `encard_eighNodeAt_ne_none_le` | L | 1 | EB2 |
| EB4 | `encard_eighNodeAt_isSplit_le` | L | 0 | — |
| EB5 | `isApproxDiagonalization_eigh_of_forall_isEighGoodSample` | H | 9 | EB1, EB1a, EB2, NS11, NS12 |

**Eigensolvers/SpectralBisection.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| EV1 | `measureReal_exists_abs_sub_lt_le` | M | 0 | — |
| EV2 | `measure_not_isEighGoodSample_le` | L | 7 | EV1, EB1b, CG2, CG3, CG4, CG6, SG5 |
| EV3 | `countable_range_eighNodeAt` | M | 0 | — |
| EV4 | `measurableSet_eighNodeAt_eq` | L | 1 | EV3 |
| EV5 | `indepFun_eighNodeAt_eq` | H | 2 | EV4 |
| EV6 | `measureReal_not_isApproxDiagonalization_eigh_le` | L | 10 | EB5, UB1, EV2, EV3, EV4, EV5, EB3, EB4 |
| EV7 | `measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le` | M | 11 | EV6 |

**LowerBounds/Eigensolvers/Precision.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| LB1 | `exists_mul_card_le_specNorm_add_smul` | S | 0 | — |
| LB2 | `mul_card_le_of_forall_specNorm_sub_le` | S | 1 | LB1 |
| LB3 | `logb_inv_add_le_of_forall_specNorm_sub_le` | M | 2 | LB2 |

## 4. Map to the source

| [Shah2024] | here | deviation |
|---|---|---|
| §1.2 model $\lvert\mathrm{fl}(z) - z\rvert \le u\lvert z\rvert$ | `IsRoundingFn` on parts, `roundScalar`, R1–R2 | componentwise; floor $\tau$, range $\Omega$ |
| Prop 1.1 | LB1–LB3 | spectral-norm argument corrected (G3); $+\log_2(1-\varepsilon)$ |
| Def 1.1 MM, Def 1.2 QR | `IsMatMulErr`, `IsQRErr`, C1–C3 | floor/range; rectangular shapes |
| Def 1.3 Unif, Def 1.4 Normal | `IsUnifSampler`, `IsNormalSampler` | coupling = deterministic map of the ideal sample |
| (2.4) $\mathsf g$, Algorithm 1 | `newtonSchulzRounded`, `newtonSchulzLoop`, `newtonSchulzSign` | Hermitian part each step (G1); componentwise test; step cap |
| Lemma 2.1 | SN3 | regime $\|\mathbf{A}\| \le 1.1$; $4\sqrt n(8 + \mu)$ in place of $\tfrac12(7 + (6+\mu)a^2)a$ |
| Lemma 2.2 | SG2 | Davis–Kahan, $2\|\mathbf{E}\|/a$, Hermitian only (OQ6) |
| Lemmas 2.3, 2.4, 2.5 | NS4–NS5, NS6–NS7, NS10 (+ NS2, NS3, NS8, NS9) | $\varepsilon > 0$, $x_0 \ne 0$ explicit (side condition) |
| Theorem 2.6 | SN4 (+ SG1, SG3, SG4) | constants (§3.4) |
| Algorithm 2 | `deflate` | — |
| Lemma 3.1 (Edelman) | CG6 (+ CG5, library's distance lemma) | $r^2x^2$ in place of $(r/2)x^2$ (OQ7) |
| Lemma 3.2 (BKMS21) | CG4 (+ CG0–CG3) | $\sqrt2(2\sqrt n + t)$, $2e^{-t^2/2}$ |
| Theorem 3.3 | DF1, DF2 (deterministic), DP1 (probability) | general invertible $\mathbf{S}$ |
| Algorithm 3, root call | `eighStep`, `eighAux`, `eigh` | §2.3 modelling deviations; $R_0$ an input |
| Lemma 4.1 | EB1 with EB1a (child invariant), EB1b (rank recovery); EV1–EV2 (probabilities) | Event I bound $nw\ell/R$ (G2); $R_0$ term (G4); rounded compressions (G1) |
| Theorem 4.2, residual/probability | EB2–EB5, UB1, EV3–EV6 | $w$ smaller by $\ell_x(n+1)/n$ (G2); counts $(n+1)(\ell+1)$, $n$ |
| Theorem 4.2, bits | EV7 | constants (§3.9) |
| Theorem 4.2, flops; Remarks | — | out of scope (OQ11) |

## 5. Consumers

* `IsMatMulErr`, `IsQRErr`, `IsRoundingFn`, the Hermitian roundings: every later analysis of a
  dense algorithm against black boxes (QDWH/Zolo-pd polar iterations, Banks et al.'s general
  diagonalization, randomized rank-revealing QR, the Hermitian pencil case, fast inversion); the
  bounded-exponent instance (§12) supplies them.
* SG2: any Hermitian sign/projector perturbation (spectral projectors in `Matrix/Perturbation`,
  Davis–Kahan consumers, contour-free proofs of projector stability).
* NS*: polynomial sign iterations and their composition with other polynomials (Chebyshev
  filtering); SN4 is the first stable inverse-free matrix-sign theorem in the library.
* CG*: every complex Gaussian argument (smoothed analysis, complex sketches, the planned complex
  extensions of `RandomMatrix/Gaussian`); CG6 is the complex analogue of the real
  invertibility-via-distance results.
* DF1, DF2, DP1: randomized range finders without oversampling, rank-revealing factorizations.
* UB1: any randomized recursion with fresh samples (randomized divide-and-conquer, adaptive
  sketching).
* `IsApproxDiagonalization`: every diagonalization algorithm's output (QR algorithm, Jacobi,
  divide-and-conquer), and Prop 1.1's form.
* EV6/EV7: the precision claim of the stage; LB3 is its matching lower bound (OQ5).

## 6. Files and placement

New `NLAlib` files (definitions, written, `--wfail`):

| file | declarations | reason |
|---|---|---|
| `Polynomial/Approximation/NewtonSchulz.lean` | `newtonSchulz`, `newtonSchulzSteps` | scalar approximation of sign by a polynomial iteration; P11 holds (imports Mathlib only) |
| `Matrix/Computation/EntrywiseRounding.lean` | `IsRoundingFn`, `roundScalar`, `roundDiag`, `roundHermitian`, `roundedSum` | finite-precision matrix computation, with the rounded BLAS of `Matrix/Computation/BLAS.lean` |
| `Matrix/Computation/Primitives.lean` | `MatMulMap`, `QRMap`, `IsMatMulErr`, `IsQRErr`, `IsUnifSampler`, `IsNormalSampler` | black-box contracts at matrix level (not `Computation/`, whose files may not import Matrix, E5) |
| `Matrix/Computation/NewtonSchulzSign.lean` | Algorithm 1 | deterministic, Matrix layer |
| `Matrix/Computation/Deflation.lean` | `deflate` | deterministic given the sample |
| `Matrix/Computation/SpectralBisection.lean` | Algorithm 3, the tree, `IsApproxDiagonalization`, `IsEighGoodSample` | deterministic given the samples; the probability needs layer 2 |
| `RandomMatrix/Gaussian/Complex.lean` | `complexGaussian`, `complexGaussianVector`, `complexGaussianMatrix` | next to the real Gaussian laws |

No existing file is modified except the generated `NLAlib.lean` (seven import lines),
`lakefile.toml` (the `NLAlibScaffold` library, as on the LB-C design branch) and
`docs/references.bib` (six entries: Shah2024, BanksGarzaVargasKulkarniSrivastava2020,
BanksKulkarniMukherjeeSrivastava2021, DemmelDumitriuHoltz2007, DemmelDumitriuHoltzKleinberg2007,
Edelman1988). Not touched: `Computation/Contract.lean`, `docs/constants.toml` (no named bound:
the precision conditions are explicit formulas with auxiliary variables, OQ10),
`docs/design/Mathlib-deviations.md` (entry for `complexGaussian` due with the PR, OQ4),
CONTRIBUTING's vocabulary table (rows for the model, `IsApproxDiagonalization` and the complex
Gaussian are proposed here and added with the implementation PRs).

Scaffold files (paths mirror the homes) and imports (G3, `check-skeleton --strict` clean):

| scaffold file | ids | imports beyond its NLAlib file |
|---|---|---|
| `Polynomial/Approximation/NewtonSchulz.lean` | NS1–NS12 | `Mathlib.Analysis.SpecialFunctions.Pow.Real` |
| `Matrix/Functions/Sign.lean` (new home) | SG1–SG6 | `Matrix.Functions.HermitianCalculus`, `Matrix.Perturbation.DavisKahanGap`, `Matrix.Spectral.{Inertia,Weyl}`, scaffold NewtonSchulz |
| `Matrix/Computation/EntrywiseRounding.lean` | R1–R7 | `Computation.Grid`, `Matrix.Norms.Compare` |
| `Matrix/Computation/Primitives.lean` | C1–C3 | `Matrix.Factorizations.QR` |
| `Matrix/Computation/NewtonSchulzSign.lean` | SN1–SN4 | scaffold EntrywiseRounding, Sign, NewtonSchulz |
| `RandomMatrix/Gaussian/Complex.lean` | CG0–CG6 | `RandomMatrix.Gaussian.{ExtremeSingularValues,Invariance}`, `Matrix.Spectral.LeastSingularValue`, `Matrix.Basic.Projector`, Mathlib multivariate Gaussian |
| `Matrix/Computation/Deflation.lean` | DF1, DF2 | `Matrix.Factorizations.{Polar,QR}`, `Matrix.Norms.Compare`, `Matrix.Spectral.LeastSingularValue` |
| `Eigensolvers/RandomizedDeflation.lean` (new folder, OQ1) | DP1 | scaffold Deflation, Complex |
| `Probability/AdaptiveUnionBound.lean` (new home) | UB1 | Mathlib independence and laws only |
| `Matrix/Computation/SpectralBisection.lean` | EB1–EB5 | scaffold Deflation, NewtonSchulzSign |
| `Eigensolvers/SpectralBisection.lean` (new folder) | `eighSampleLaw`, EV1–EV7 | scaffold RandomizedDeflation, SpectralBisection, AdaptiveUnionBound |
| `LowerBounds/Eigensolvers/Precision.lean` (new subfolder) | LB1–LB3 | `Matrix.Structured.Walsh`, `ForMathlib.Algebra.Order.Round` |

Placement decisions (P10): deterministic algorithms and analyses in `Matrix/Computation/`
(Matrix is layer 0 and may import Polynomial); the probabilistic guarantees need RandomMatrix
(layer 2) and are about an algorithm, not a random matrix, hence the new folder
`NLAlib/Eigensolvers/` (OQ1; it needs a `LAYER` entry in `scripts/check_rules.py` and a §2 line,
maintainer edits, so it holds scaffold files only here); UB1 is general probability (layer 1.5);
EV1 stays with its only consumer (a uniform shift against a spectrum). Expected sizes: NewtonSchulz
≈ 450 lines, NewtonSchulzSign ≈ 450, Deflation ≈ 350, SpectralBisection (Matrix) ≈ 900 (split
`SpectralBisectionLocal.lean` off if EB1 exceeds 400 lines; amendment then), Complex ≈ 500.

## 7. Material

No prior formal development of the paper. Proof material: the library's Davis–Kahan
(`DavisKahanGap.lean`) for SG2, `HermitianCalculus.lean` (`cfc` lemmas, `specNorm_cfc_le`,
`re_trace_cfc`) for SG1–SG6, Weyl (`abs_eigenvalue_sub_le`) for SN4, `exists_hasOrthonormalCols_mul_isUpperTrapezoidal`
for C2, `polarFactor` for DF1, the real Gaussian invariance and Gordon tail
(`hasLaw_const_mul_of_hasLaw_gaussianMatrix`, `measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix`)
for CG2/CG4, `exists_iInf_norm_mulVec_le_of_singularValues_le` (Rudelson–Vershynin's distance
step, already in `LeastSingularValue.lean`) for CG6, `walshHadamard_mul_self` for LB3,
`Real.abs_sub_roundNearest_le` for R1. Not reproduced: the contour proof of Lemma 2.2, Edelman's
Wishart density, the paper's operation counts.

## 8. Mathlib and NLAlib search (pinned v4.33.1)

Floating-point model: Mathlib none (`Mathlib.Data.FP` has no theorems); NLAlib: `Computation.RelErr`,
`IsRelErrSem` (real decodings), `gridSem`/`Real.roundNearest` (used, R1); no complex decoding.
Matrix sign: Mathlib `cfc`, `Real.sign`; no sign-perturbation lemma (searched `cfc` + `sign`,
none); NLAlib none. Newton–Schulz: none in either. Davis–Kahan: NLAlib's (used). Spectral
projector frames: none as stated (SG5; `HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose`
is the tool). Complex Gaussian: Mathlib `stdGaussian ℂ` (variance 1 per part; bridge CG0), no
complex normal law; NLAlib only real laws (`gaussianReal`, `gaussianVector`, `gaussianMatrix`).
Uniform law on an interval: Mathlib `ProbabilityTheory.cond volume (Set.Icc a b)` (used).
Smallest singular value of a Gaussian matrix: NLAlib real Gordon bound
(`measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix`, rectangular, useless for square);
none complex. QR: NLAlib `IsQR`, full QR existence (used). Hadamard: NLAlib `walshHadamard`
(used); Mathlib `Matrix.IsHadamard` none relevant. Union bound over adaptive events: none.
Static costs: `Computation.StaticCost` applies to deep-embedded `Prog`s only (OQ11).

## 9. Names for review

`IsRoundingFn` (alternatives `IsRelRoundingFn`, `IsFloorRelErr`), `roundScalar`, `roundDiag`,
`roundHermitian`, `roundedSum`; `MatMulMap`, `QRMap`, `IsMatMulErr` (parallel to
`Computation.IsMatvecErr`), `IsQRErr`, `IsUnifSampler`, `IsNormalSampler`; `newtonSchulz`,
`newtonSchulzSteps`, `newtonSchulzRounded`, `IsNewtonSchulzConverged`, `newtonSchulzLoop`,
`newtonSchulzSign`; `deflate`; `EighPrimitives`, `EighSample`, `EighStep`, `EighNode`, `eighStep`,
`eighAux`, `eigh`, `eighChild`, `eighNodeAt`, `bisectionSignTol`, `bisectionDepth`, `leadingBlock`
(the "Eigh" prefix follows the paper's EIGH; `spectralBisection*` is the alternative);
`IsApproxDiagonalization`, `IsEighGoodSample`; `complexGaussian*`; `eighSampleLaw`. Theorem names
follow N2/N3/N10/N14/N15 by hand; the extraction check (N1–N18) runs at clean-up. Awkward:
`logb_inv_add_le_of_forall_specNorm_sub_le` (LB3, an arithmetic conclusion) and
`measure_not_isEighGoodSample_le` (a measure, not `measureReal`, because the right side carries an
`ℝ≥0∞` charge).

## 10. Open questions (recommendations in bold; the decision sheet has them one line each)

1. **Folder for the randomized layer** — (a) **new top-level `NLAlib/Eigensolvers/` at layer 3**
   (one `LAYER` entry in `scripts/check_rules.py` and a §2 line, both maintainer edits; until
   then its files stay in the scaffold); (b) the probabilistic theorems in `RandomMatrix/`
   (they are about an algorithm, not a random matrix); (c) `LowRank/Random/` next to the range
   finder (deflation fits, Hermitian diagonalization does not). (a): the deterministic parts are
   already placed in `Matrix/Computation/`; only DP1, EV*, `eighSampleLaw` need the folder, and
   later randomized eigensolvers (randomized block Krylov with Gaussian starts, shattering) have a
   home.
2. **Complex rounding model** — (a) **a real rounding function applied to real and imaginary
   parts (`IsRoundingFn`), tied to the contract layer by the witness R1**; (b) generalize
   `IsRelErrSem` to `RCLike` decodings in `Computation/Contract.lean` (collides with the current
   bounded-model work; can follow later and would give (a) as a corollary); (c) the paper's
   complex model $\lvert\mathrm{fl}(z) - z\rvert \le u\lvert z\rvert$ for a complex rounding
   function. (a) is what hardware does, keeps Hermitian structure exact without an oddness
   assumption, and implies (c) at $\tau = 0$ (R2).
3. **Representation of the randomized recursion** — (a) **total Lean functions of the black boxes
   and a tree of ideal samples `List Bool → sample`; samplers with countable ranges make every
   node a measurable, countably-valued function of earlier samples, so no measurability of MM, QR
   or fl is assumed**; (b) a deep-embedded `Prog` with random tapes (the program layer has no
   recursion with data-dependent sizes and no QR oracle); (c) relational run structures
   (`PCGRun`-style) quantified over measurable selections. (a) keeps every statement about a
   concrete function; (b) is a program-layer project of its own.
4. **Complex Gaussian law** — (a) **build the minimal one now** (`complexGaussian` =
   $\mathcal{N}_{\mathbb C}(0,1)$ as a product law, bridges to Mathlib's `stdGaussian ℂ` and to the
   real `gaussianMatrix`, invariance, tails; Mathlib-deviations entry with the PR); (b) wait for a
   general complex-Gaussian design. (a): seven statements, all reductions to the real library.
5. **Proposition 1.1 (lower bound)** — (a) **include** (3 statements, `LowerBounds/Eigensolvers/`,
   with the corrected spectral-norm argument G3); (b) defer. (a) is cheap, and it is the matching
   lower bound for the stage's headline.
6. **Lemma 2.2** — (a) **replace by the Hermitian Davis–Kahan bound $2\|\mathbf{E}\|_2/a$
   (SG2)**; (b) formalize the contour/pseudospectrum argument. (a) is stronger (dimension-free,
   no size condition), shorter, and uses the library's Davis–Kahan.
7. **Lemma 3.1 (Edelman)** — (a) **elementary $r^2x^2$ via distance to the span and the complex
   small ball (CG5, CG6)**; (b) Edelman's exact law ($1 - e^{-rx^2}$, Wishart densities). (a)
   loses a factor $2r$, i.e. at most $\log_2 n + 1$ bits.
8. **Hermitian symmetry of the iterates and compressions (gap G1)** — (a) **store the rounded
   Hermitian part (`roundHermitian ∘ hermitianPart`) after each sign step and for
   $\mathbf{C}_\pm$** ($n^2$ flops, error factor $\sqrt n$); (b) strengthen the MM contract to
   "Hermitian output whenever the exact product is Hermitian" (no fast algorithm guarantees it);
   (c) mirror the upper triangle without averaging (exact, but the error grows by
   $\sqrt{2n}$). (a) keeps the black-box contract of the paper.
9. **Event I probability (gap G2)** — (a) **correct the bound to $nw\ell/R$ and shrink $w$ by
   the factor $\ell_x(n+1)/n$**, costing about one $\log_2\log_2(1/\varepsilon)$ bit term
   ($\ell^3$ in place of $\ell^2$); (b) draw the shift on $[-R/2, R/2]$ instead (density
   $1/R$, no $\ell$) and re-derive the window recursion (changes Algorithm 3). (a) keeps the
   algorithm.
10. **Form of the precision conditions** — (a) **explicit formulas with auxiliary variables
    (`hβ : β = …`, `hN : N = …`) and the bits corollary EV7 with additive constant 25**;
    (b) named bounds (`…Bound`) in `docs/constants.toml` (a shared file under concurrent edit;
    can be done at clean-up without changing any statement's content). The constants are this
    note's derivation (§3.4, §3.8): a prover who needs more slack reports it as an amendment.
11. **Operation counts** — (a) **out of scope now**; count the black-box calls later with a
    shallow counter (2 MM per sign step, one MM and one QR per deflation) if wanted; (b) state
    `Computation.StaticCost` bounds (only for deep-embedded programs, OQ3(b)). (a): decision 3
    puts runtime out of scope.
12. **Modelling deviations and staging** — (a) **accept the deviations of §2.3 and dispatch
    HDIAG-1 (W1 + W2 + LB, 35 targets) and HDIAG-2 (W3, 10) now, HDIAG-3 (W4, 15) after a Fable
    re-check of the H/L outlines** (review items 1–3 are already applied); (b) round the scalar
    parameters too and approve the sub-stages separately.
13. **The Hermitian-exactness clause of `IsMatMulErr`** — (a) **keep it** (classical gemm with
    round-to-nearest-even meets it; SN3 uses it so that the diagonal of $\mathrm{mm}(\mathbf{A},
    \mathbf{A})$ is real); (b) drop it and let `roundDiag` discard the imaginary part of that
    diagonal, at an extra $1.21\mu u$ in SN3 (Strassen-type products do not meet the clause, so
    (b) widens the bridge). Fable leans to considering (b) for the bounded bridge; the statements
    change only in SN3's constant.

## 11. Deferred, with what each needs

* Operation counts and runtime (Theorem 4.2's flop bound): a cost semantics for shallow
  algorithms or a deep-embedded program (OQ11).
* The bounded-exponent instance (§12): Codex's model on main and its rounding function.
* Implementations meeting `IsMatMulErr`/`IsQRErr`: classical $O(n^3)$ complex gemm and Householder
  QR in finite precision (complex decodings in the contract layer, OQ2(b)); the fast algorithms of
  [DemmelDumitriuHoltzKleinberg2007], [DemmelDumitriuHoltz2007].
* Boosting the success probability by residual checks (remark after Theorem 4.2): a randomized
  residual estimator.
* Faster sign iterations (QDWH, Zolo-pd): need per-row backward-stable QR, a different contract.
* A real Gaussian start for real symmetric input: a linear small-ball bound (costs more bits); not
  needed (the complex algorithm covers real input).
* Named bounds for the precision conditions (OQ10(b)).

## 12. Bridge to bounded exponent

The unbounded-first statements already carry what the bounded model needs: every contract has
the floor $\tau$ and range $\Omega$, and every theorem has explicit range hypotheses
($4n\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon R_0/3)$ and $16(R_0 + n +
\sqrt{\log(16n/\theta)}) \le \Omega$ for EIGH; $2n\tau \le 1$, $\Omega \ge 8$ for SIGN;
$\tau \le \|\mathbf{S}\|_2x$, $2(\|\mathbf{S}\|_2 + 1)\sqrt2(2\sqrt n + t) \le \Omega$ for
DEFLATE). In the unbounded model ($\tau = 0$, $\Omega$ as large as needed) they are trivial. W5,
after the bounded model is on main, adds three statements and changes none:

* **(a) Semantics level.** For the bounded-exponent binary format with $t$ significant bits and
  exponent range $[e_{\min}, e_{\max}]$: its round-to-nearest function satisfies
  `IsRoundingFn (2⁻¹ ^ t) τ Ω` with $\tau = 2^{e_{\min}}$, the smallest normal number (gradual
  underflow errs by at most half the subnormal spacing, $2^{e_{\min}-t} = u\tau$) and $\Omega$
  the largest finite number, and a semantics `binaryFloatSem` meeting the mixed contract
  on its `safe` set rounds every arithmetic result by that function (the analogue of R1 for
  `gridSem`). Shape: `isRoundingFn_<boundedRound> (t emin emax) : IsRoundingFn (2⁻¹ ^ t)
  (2 ^ emin) (<maxFinite>) (<boundedRound> t emin emax)`; real, as the model is, which suffices
  since our complex numbers are stored componentwise.
* **(b) Matrix multiplication.** A componentwise mixed bound $\lvert\mathbf{A}\mathbf{B} -
  \mathrm{fl}(\mathbf{A}\mathbf{B})\rvert \le \gamma_d\lvert\mathbf{A}\rvert\lvert\mathbf{B}\rvert +
  d\eta$ (Codex's underflow BLAS) gives the normwise mixed bound with $\mu = d\gamma_d/u$ and
  absolute $\eta' = d^2\eta$ (Frobenius), and C3 (already in the skeleton) turns it into
  `IsMatMulErr u τ Ω (2μ)` with $\tau = \eta'/(\mu u)$, i.e. the normwise bound holds once
  $\|\mathbf{A}\|_2\|\mathbf{B}\|_2 \ge 2^{e_{\min}}\operatorname{poly}(d)/u$ — the condition of
  decision 1(b), here absorbed into the floor rather than assumed per call.
* **(c) Exponent bits.** Scale the input by a power of two (exact) so that $R_0 \in [1/2, 1]$.
  Then the hypotheses read $\tau \le \operatorname{poly}(\varepsilon\theta/n)$ and
  $\Omega \ge \operatorname{poly}(n/\theta)$, so $\log_2(\Omega/\tau) = O(\log(n/(\varepsilon\theta)))$
  and $\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits suffice — the paper's
  $\lg\lg(n/\varepsilon) + O(1)$ with the $\theta$ it omits. Where the range invariants come from:
  in SIGN every iterate has $\|\mathbf{A}_k\|_2 \le 1.1$ and every intermediate is at most $4.9$
  (SN3's proof), and every rounding or product error is bounded through the *upper* magnitude it
  uses, $\max(\cdot, \tau) \le$ that magnitude, so the floor only needs $\tau \le 1/(2n)$; in
  DEFLATE the products have $\|\mathbf{G}\|_2 \in [x, \sqrt2(2\sqrt n + t)]$ on Event II; in EIGH
  every node-scale magnitude is at most $1.1R_y \le 1.1R_0$, and every error budget of an
  internal node is at least $\varepsilon_y R_0 \ge \varepsilon R_0/3$ (an internal node has
  $R_y > \varepsilon_y R_0$), which is where $\tau \le \varepsilon R_0/(12n)$ comes from; tiny
  entries are harmless because their errors are charged to the node's budget, not to their own
  size. The statement for W5: EV6 instantiated with (a) and (b) and the scaling, concluding
  "with $t$ significant bits as in EV7 and $e \ge \log_2\log_2(C n/(\varepsilon\theta))$ exponent
  bits the guarantee holds".

## 13. Proof plan for dispatch

Waves (from `hdiag-targets.json`, the longest dependency chain): wave 0, 27 independent
targets (C1, C2, C3, CG0, CG1, DF1, EB2, EB4, EV1, EV3, LB1, NS1, NS11, NS12, NS2, R1, R2, R3, R4, R6, R7, SG1, SG2, SG4, SG5, SG6, UB1); then the chains NS2→NS3→{NS7, NS8}→NS9→NS10→SN4→EB1b→EB1a→EB1→EB5→EV6→EV7,
NS1→{NS4, NS5, NS6}, NS4→SG3, R2→R5→SN3→SN4, R3→SN1→SN2, CG1→{CG2, CG3, CG4}→CG5→CG6→{DP1, EV2},
DF1→DF2→{DP1, EB1a}, EB1b→EV2, EB2→EB3, EV3→EV4→EV5→EV6, LB1→LB2→LB3. Difficulties (after the
review's relabels): S 19, M 26, L 12, H 3. By group: W1 28, W2 4, W3 10,
W4 15, LB 3. Model tiers: S and M on haiku first with sonnet escalation, L and H on opus from the
start (`--hard L,H`); failed L/H targets get Opus continuation sessions. Dependents may start on
sorried dependencies. HDIAG-1 and HDIAG-2 can go now; HDIAG-3 after a Fable re-check of the
amended outlines of EB1, EB1a, EB1b, EB4, EB5, EV2, EV5, EV6.

## 14. Literature

[Shah2024] (arXiv:2408.09880v1, read in full from the LaTeX source; numbering of v1);
[BanksGarzaVargasKulkarniSrivastava2020] (context: the deflation it streamlines, the square-root
loss); [DemmelDumitriuHoltzKleinberg2007], [DemmelDumitriuHoltz2007] (the black boxes; not read,
cited in module docstrings only); [Edelman1988, Theorem 3.2] and
[BanksKulkarniMukherjeeSrivastava2021, Lemma 2.2] (cited by the paper for Lemmas 3.1, 3.2; replaced,
not read); [Higham2002, (2.4), Theorem 2.2, (4.4)] (standard model, rounding to nearest, recursive
summation; (4.4) locator to verify); [RudelsonVershynin2008, Lemma 3.5] (the distance step, via the
library). New bibliography entries: the six of §6.
