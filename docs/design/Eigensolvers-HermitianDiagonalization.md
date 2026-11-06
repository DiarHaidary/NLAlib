# Design note: Hermitian diagonalization in linear precision — Newton–Schulz sign, randomized deflation and spectral bisection under black-box multiplication and QR (stage HDIAG)

Status: proved and moved into `NLAlib` (end of stage, §16, 2026-11-06). Earlier: reviewed (Fable, `~/nlalib-harness/reports/Review-Fable-HDIAG-Design.md`: approve with
changes) and amended twice; APPROVE and OQ1–OQ13 pending with the maintainer (decision sheet
`~/nlalib-harness/state/decisions/HDIAG.json`). Review changes (second commit): Fable's items 1–3
(public EB1a child invariant and EB1b rank recovery; projectors stored Hermitian), Event I with
"seed in $[-1, 1]$" (without it EB1 was false), items 4–10. Machine changes (third commit,
maintainer comments on OQ2, OQ3, OQ7 and COMPDYN §8.2): every algorithm is written generically
over a `FloatMachine` (§2.0), with every scalar parameter computed by the machine, one rounding
per primitive operation, componentwise IEEE complex rounding, the rank conversion
$\lfloor\mathrm{fl}(t + 1/2)\rfloor_+$ clamped by $k$, $\beta$ and $\ell$ as precomputed
thresholds, the exact machine as the satisfiability witness, and §15 on a deep-embedded version.
Bounded model now (fourth commit, after rebasing onto `origin/main` a08339af, which has Codex's
`AbsRelErr`, `binaryFloatRound`, `binaryFloatSem`): the floor/range contracts already are the
mixed model, the samplers got floors, and three targets make the bounded format an instance and
prove the exponent-bit count (§12, OQ14); 64 statements. Fable delta fixes (fifth commit): DF2 gains $\|\mathbf{G}\|_2 \le \Omega$ (it was false without it;
DP1 and EB1a/EB1 supply it), SN3 needs $\Omega \ge 9$ (SN4 $9(n+1) \le \Omega$), EB2/EB3 take the
absolute floor bound $100\tau \le \varepsilon\min(R_0, 1)$ (false before) and EB5/EV6/EV7 the
global $100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$; EB1/EB5 outlines cover the
rounded `eighNextParams`. W4 outline check (sixth commit,
`~/nlalib-harness/reports/Review-Fable-HDIAG-W4.md`): EB5/EV6/EV7 take
$16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)}) \le \Omega$ (the old range did not give the node
lemmas' at the root or at $\ell_y = 2\ell$); new targets EB1c (computed projectors), EB1d (a split
node), EB2a (node parameters); EB1b outline with modulus $w - 1.4uR$; EB1 with an explicit residual
budget closing through $\varepsilon' = (1 - 1/\ell)\varepsilon$; EV2 by a measurable superset (H);
EB2, EV7, EV8 relabelled L. HDIAG-1/2 statements unchanged; the W4 targets (67 statements in
all) are in `~/nlalib-harness/pilot/hdiag3-targets.json`. Branch
`design/hdiag` (worktree `~/nlalib-design-hdiag`, from `origin/main` 4d4e9fc9). Targets:
`~/nlalib-harness/pilot/hdiag-targets.json` (64 statements, the file of the HDIAG-1/2 dispatch;
its W4 entries are superseded by `~/nlalib-harness/pilot/hdiag3-targets.json`, 19 statements).
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
`lake build NLAlibScaffold` gives exactly 64 `declaration uses sorry` warnings and nothing else;
`scripts/check_rules.py --files` on every touched file (0 errors; one warning, C8 on `Demmel1997`,
predates this stage), `check_refs.py`, `check_constants.py`, `check_latex.mjs` (KaTeX 0.16.22) and
both `lake exe mk_all --module --lib NLAlib --check` and `… --lib NLAlibScaffold --check` are
clean; `bin/check-skeleton --strict` (rule G3): 64 targets, 0 names missing an import, 0
unresolved. The extraction-based name check (N1–N18) was not run; names for review are in §9.

## Maintainer decisions already made (2026-11-05)

1. **Arithmetic model: unbounded exponent, pure relative error first**, on main's contract layer,
   with the bounded-exponent model (Codex's `binaryFloatSem`, then uncommitted, since merged in
   a08339af) a later drop-in — now targeted directly (§12, OQ14). Consequence here: every contract carries a floor $\tau$ (absolute error below
   $\tau$, gradual underflow) and a range $\Omega$ (overflow), $\tau = 0$ and $\Omega$ arbitrary in
   the unbounded model; every theorem carries the range hypotheses it needs, so the bridge (§12)
   rewrites no statement.
2. **Port the essence**: constants may change. Edelman's $\sigma_{\min}$ law (Lemma 3.1) is
   replaced by an elementary bound losing a factor $2n$ (OQ7); the contour Lemma 2.2 by a
   Hermitian Davis–Kahan bound (OQ6).
3. **Black-box MM and QR are hypotheses** (normwise predicates with $\mu_{\mathrm{MM}}$,
   $\mu_{\mathrm{QR}}$, $\mathrm{MM}(\mathbf{A}, \mathbf{A}^{\mathsf{H}})$ exactly Hermitian), not
   implementations; runtime is out of scope (OQ11 on static counts).
4. **Machine interface (2026-11-06, comments on OQ2, OQ3, OQ7)**: keep shallow total functions
   and fuel recursion, but write every algorithm against a `FloatMachine` so that it cannot
   compute outside the model (§2.0); complex rounding componentwise as IEEE; σ_min constant
   marked as improvable by Edelman's law; a note on what a deep-embedded version needs (§15).

## 0. Summary

| | |
|---|---|
| Model (new) | `FloatMachine F Su Sg`: the only operations an algorithm may apply to stored numbers (rounded $+,-,\times,/$, `ofNat`; exact `neg`, `le`, floor `toNat`, $0$, $1$; black-box `mm`, `qr` on `F × F` matrices; samplers from abstract ideal samples), its contract `FloatMachine.IsAccurate` (`IsRoundingOf` per operation with floor $\tau$ and range $\Omega$; `IsMatMulErr`, `IsQRErr`, `IsUnifSampler`, `IsNormalSampler` through the decoding); entrywise Hermitian operations built from the scalar ones; witnesses: the exact machine (C1) and `Real.roundNearest` of `gridSem` (R1) |
| Algorithms (new definitions, `NLAlib`, build `--wfail`) | `newtonSchulz`, `newtonSchulzSteps` (scalar); `FloatMachine.hermFrom`, `hermShift`, `hermScale`, `hermAvg`, `negMat`, `conjTransposeMat`, `identityMat`, `zeroMat`, `traceRe`; `newtonSchulzRounded`, `newtonSchulzTest`, `newtonSchulzLoop`, `newtonSchulzSign` (Algorithm 1); `deflate` (Algorithm 2); `EighSample`, `leadingBlock`, `EighStep`, `EighStep.IsSplit`, `eighNextParams`, `eighStep`, `eighAux`, `eigh` (Algorithm 3), `EighNode`, `eighChild`, `eighNodeAt`; analysis-side `bisectionSignTol`, `bisectionDepth`, `IsApproxDiagonalization`, `IsEighGoodSample`; `complexGaussian`, `complexGaussianVector`, `complexGaussianMatrix`. All algorithm definitions are computable and generic over the machine |
| Headline | Theorem 4.2 (EV6): with probability at least $1 - \theta$, $\mathsf{eigh}$ returns $(\mathbf{U}, \mathbf{d})$ with $\|\mathbf{A} - \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}\|_2 \le 2\varepsilon R_0$ and $\sigma_i(\mathbf{U}) \in [1 \pm \varepsilon/3]$, under explicit precision hypotheses; in bits (EV7) $\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ |
| Other results | Lemmas 2.1, 2.3–2.5, Theorem 2.6 (SIGN, SN4), Theorem 3.3 (deterministic DF2, probabilistic DP1), Lemma 4.1 (EB1), Proposition 1.1 (LB3, OQ5); the replacements of Lemmas 2.2 (SG2) and 3.1 (CG6) |
| Paper gaps found and fixed | G1 the iterates of SIGN and the compressions $\mathbf{C}_\pm$ are treated as Hermitian but MM does not make them so (fixed by rounded Hermitian parts, OQ8); G2 the probability of missing Event I is $nw\ell/R$, not $nw/R$ (factor $\ell$ dropped, OQ9; costs one $\log_2\log_2(1/\varepsilon)$); G3 Proposition 1.1's sign-of-entries argument bounds the Frobenius norm, not the spectral norm (fixed by choosing the sign from $\mathbf{1}^{\mathsf{T}}\mathbf{R}\mathbf{1}$, same conclusion); G4 Lemma 4.1's bound on $\|\mathbf{D}_\pm\|_2$ drops the $R_0$ part of the children's residual (absorbed by the slack $\varepsilon R_0/\ell$). Side condition (not a paper gap): Lemma 2.5 needs $\varepsilon > 0$ and $x_0 \ne 0$ explicitly because $u = 0$ is allowed. Also noted: the paper's depth check compares $R_\ell$ with $\varepsilon$, not $\varepsilon_\ell$; its Lemma 2.5 proof needs $\lvert x_k\rvert \ge 20u$ throughout (NS9) |
| Statements | 64 sorried: S 19, M 30, L 12, H 3, in 12 scaffold files (§3.11) |
| Staging | W1 scalar, machine operations, contracts, sign facts (31); W2 SIGN (4); W3 complex Gaussian and DEFLATE (10); W4 union bound and EIGH, with the bounded-format corollary (16); LB Proposition 1.1 (3) |
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

### 2.0 The machine interface, and what typing enforces (amendment 2, maintainer comment on OQ3)

The maintainer's requirement: the shallow recursion must not cheat outside the model of
computation, since it is an example for future code. The algorithms stay shallow total functions
with fuel recursion, but they are written against an interface that makes cheating impossible by
construction:

```lean
structure FloatMachine (F Su Sg : Type*) where           -- NLAlib/Matrix/Computation/Primitives.lean
  zero one : F
  ofNat : ℕ → F                                           -- rounded conversion of a natural
  add sub mul div : F → F → F                             -- one rounding each
  neg : F → F                                             -- exact
  le : F → F → Bool                                       -- exact comparison
  toNat : F → ℕ                                           -- exact floor ⌊x⌋₊ (IEEE truncation)
  mm : MatMulMap (F × F)                                  -- black box on stored complex matrices
  qr : QRMap (F × F)                                      -- black box
  unif : F → Su → F                                       -- stored scale, ideal seed ↦ stored shift
  normal : Sg → F × F                                     -- ideal sample ↦ stored complex number
```

Stored complex numbers are pairs `F × F`, and every complex entrywise operation
(`hermShift`, `hermScale`, `hermAvg`, `negMat`, `conjTransposeMat`, `identityMat`, `traceRe`, in
`EntrywiseRounding.lean`) is *defined* from the real scalar operations, real and imaginary parts
separately: the rounding is componentwise IEEE, as the maintainer asked (OQ2), and one rounding
happens per primitive operation (no fused roundings; $(\mathbf{I} \pm \mathbf{B})/2$ is a shift
then a rounded division, $(\mathbf{Y} + \mathbf{Y}^{\mathsf{H}})/4$ an addition then a rounded
division), so a bounded-exponent model needs no exact-halving hypothesis (review item 3). The
analysis decodes by `dec : F → ℝ`; the contract `FloatMachine.IsAccurate dec u τ Ω μM μQ cN`
gives each operation's error relation (`IsRoundingOf u τ Ω a z`, $|a| \le \Omega \Rightarrow
|a - z| \le u\max(|a|, \tau)$, for $+, -, \times, /$, `ofNat`; exactness of $0$, $1$, `neg`,
`le`, `toNat`) and the black-box and sampler contracts `IsMatMulErr`, `IsQRErr`,
`IsUnifSampler`, `IsNormalSampler`, now stated through the decoding (so they are the functional
contracts that the planned `KernelContracts.lean` of COMPDYN lifts). C1 shows the contract is
satisfiable (the exact machine at $u = 0$); R1 shows `Real.roundNearest`, the rounding of
`Computation.gridSem`, is an `IsRoundingOf` rounding, so the machine whose scalar operations
round with it meets the scalar part of the contract.

**Enforced by typing.** `newtonSchulzRounded`, `newtonSchulzTest`, `newtonSchulzLoop`,
`newtonSchulzSign`, `deflate`, `eighStep`, `eighNextParams`, `eighAux`, `eigh`, `eighChild`,
`eighNodeAt` are generic in `F`, `Su`, `Sg`. `F` has no instances, so an exact operation on a
stored number (or on the ideal samples, of abstract types `Su`, `Sg`) does not typecheck: data
flows only through the machine's fields. The definitions are computable `def`s (no
`noncomputable`), so Lean would reject any data that depends on classical choice, such as an
`if` on an undecidable proposition about stored values; all branching is on the machine's `le`
or on natural numbers. Every scalar parameter is computed by the machine: $\mathrm{fl}(R/\ell)$,
$\mathrm{fl}(R/2)$, $\mathrm{fl}(2R)$, the next window and tolerance (`eighNextParams`), the
leaf test $R \le \mathrm{fl}(\varepsilon R_0)$, the sign threshold
$\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$, and the rank
$k_+ = \min(k, \lfloor\mathrm{fl}(t + \mathrm{fl}(1/2))\rfloor_+)$, which is the clamped
conversion `bindIdx` of COMPDYN's programs. The exact-scalar-parameter deviation of the first
draft is gone.

**Not enforced by typing.** (i) Natural-number bookkeeping is exact and free: sizes $k$, $k_+$,
the depth counter $\ell$, the step limits, `List Bool` paths, as the integer side of the paper's
model also assumes; an algorithm could in principle extract digits of a stored number through
`toNat` and repeated rounded scalings and compute with them exactly in ℕ — legal in this model,
and visible in the code. (ii) Nothing counts operations (OQ11). (iii) The *theorems* are free to
use exact real arithmetic on decodings, as analyses must. (iv) Two inputs are precomputed
thresholds rather than computed: the depth counter $\ell \ge \lceil\log_2(1/\varepsilon)\rceil + 5$
and the accuracy $\beta$ (any stored number at most the analysis bound; a lower bound suffices,
so no square root or logarithm is computed). This is the "abstract routine" choice of COMPDYN
§8.2(2): the argument carries exactly the inequalities the proofs use (`hβle`, `hℓ`), and a
bit-length routine (COMPDYN §4.7) can supply them later without changing a statement (OQ10).

### 2.1 Entrywise operations (`NLAlib/Matrix/Computation/EntrywiseRounding.lean`, written)

`hermFrom up dg` builds a stored Hermitian matrix from its strict upper triangle and real
diagonal, mirroring with the exact negation (decoding exactly Hermitian, R2, whatever the
rounding does with signs). `hermShift X c` ($\mathbf{X} - c\mathbf{I}$: one `sub` per diagonal
entry), `hermScale X c` ($\mathbf{X}/c$: one `div` per part), `hermAvg X c`
($(\mathbf{X} + \mathbf{X}^{\mathsf{H}})/c$: an `add` or `sub`, then a `div`, per part),
`traceRe` (left-to-right `add`), and the exact `negMat`, `conjTransposeMat`, `identityMat`,
`zeroMat`.

### 2.2 Contracts (`NLAlib/Matrix/Computation/Primitives.lean`, written)

```lean
structure IsMatMulErr (dec : K → 𝕜) (u τ Ω : ℝ) (μ : ℕ → ℝ) (mm : MatMulMap K) : Prop where
  specNorm_mul_sub_le : ∀ A B, ‖Ā‖‖B̄‖ ≤ Ω → ‖Ā B̄ - (mm A B)‾‖ ≤ μ d * u * max (‖Ā‖‖B̄‖) τ
  isHermitian_of_map_eq_conjTranspose : ∀ A B, B̄ = Āᴴ → ((mm A B)‾).IsHermitian
def IsQRErr (dec) (u τ Ω) (μ) (qr : QRMap K) : Prop :=   -- R̄ upper trapezoidal, unitary Q' with
  ... specNorm (Q' - Q̄) ≤ μ d * u ∧ specNorm (Ā - Q' * R̄) ≤ μ d * u * max ‖Ā‖ τ
def IsUnifSampler (dec) (u) (unif : F → ℝ → F) : Prop := ∀ s v, 0 ≤ s̄ → v ∈ [-1, 1] →
  |unif s v|‾ ≤ s̄ ∧ |s̄ * v - (unif s v)‾| ≤ s̄ * u
def IsNormalSampler (dec : K → ℂ) (u c) (normal : ℂ → K) : Prop := ∀ z, ‖z - (normal z)‾‖ ≤ c*u*‖z‖
```

Errors are exact minus computed (N10). The Hermitian clause is OQ13.

### 2.3 Algorithms (`NLAlib/Matrix/Computation/{NewtonSchulzSign,Deflation,SpectralBisection}.lean`, written)

* `newtonSchulzRounded M A = hermAvg (mm A (negMat (hermShift (mm A A) (ofNat 3)))) (ofNat 4)`;
  `newtonSchulzTest M η A`: every part of every entry of `hermShift (mm A A) one` in
  $[-\eta, \eta]$ by the machine's `le`; `newtonSchulzLoop` (tests, then steps, at most $N$
  times); `newtonSchulzSign M ε b N A` starts from `hermScale A b` with threshold
  `div ε (ofNat (4 n))`.
* `deflate M r P G`: the first $r$ columns of `(qr (mm P (G.map normal))).1`.
* `eighStep M N signFuel R₀ β A R ε ℓ s : EighStep F k`: leaf ($k \le 1$, or the machine's test
  $R \le \mathrm{fl}(\varepsilon R_0)$), one child, or a split; `eighAux` recurses on a budget with
  `eighNextParams`; `eigh M signFuel ℓ A R₀ ε β s` is the root call (budget $\ell + 1$). $R_0$,
  $\varepsilon$, $\beta$ are stored inputs, $\ell$ a natural input.
* Randomness: `s : List Bool → EighSample Su Sg N`, `EighSample Su Sg N = Su × (Bool → Matrix
  (Fin N) (Fin N) Sg)`; the node at path `a` uses `s a`, its children the subtrees.
* `IsApproxDiagonalization A U d η κ` (on ℂ; theorems apply it to decodings), `IsEighGoodSample
  dec w x t y s` (Event I with the seed in $[-1, 1]$, Event II).

Remaining modelling deviations from Algorithms 1 and 3 (OQ12): $k_- = k - k_+$; the test is
componentwise and applied before each step; explicit step caps; one accuracy $\beta$ for all
nodes (a node-wise accuracy would be larger, so this only lengthens the sign iterations); stored
Hermitian iterates, projectors and compressions (OQ8); Event I includes "seed in $[-1, 1]$".

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

### 3.3 Machine operations and contracts (R1–R9, C1, C3)

R1: `Real.roundNearest t` returns an `IsRoundingOf` $2^{-t}$ $0$ $\Omega$ rounding (the grid
rounding of `gridSem`). R2: `hermFrom` decodes Hermitian. R3–R5: `negMat`, `conjTransposeMat`,
`identityMat` decode exactly. R6 $\|(\bar{\mathbf{X}} - \bar c\mathbf{I}) -
\overline{\mathrm{hermShift}}\|_2 \le u\max(\|\bar{\mathbf{X}} - \bar c\mathbf{I}\|_2, \tau)$
(diagonal error, as the paper notes in Lemma 2.1); R7 $\|\bar{\mathbf{X}}/\bar c -
\overline{\mathrm{hermScale}}\|_2 \le u(\sqrt k\|\cdot\|_2 + 2k\tau)$; R8 the same with $3u$ for
`hermAvg` (two roundings per part, $|\bar c| \ge 1$); R9 the rounded trace,
$2ku(\sum\lvert x_i\rvert + k\tau)$ for $ku \le 1/2$. C1: the exact machine meets
`IsAccurate` at $u = 0$ (so all hypotheses are consistent). R1b: `binaryFloatRound` (Codex's
bounded format, gradual underflow) is an `IsRoundingOf` $2^{-p}$ rounding with floor the smallest
normal number $2^{e_{\min}+p-1}$ and range the largest finite number; C1b: the machine with those
scalar operations meets `IsAccurate` (bounded model as an instance). **C3** the bridge (b) of §12.

### 3.4 Algorithm 1 (SN1–SN4, `Matrix/Computation/NewtonSchulzSign.lean`)

**SN3** (Lemma 2.1): for Hermitian $\|\mathbf{A}\|_2 \le 11/10$, $u(8 + \mu(n)) \le 1/10$,
$2n\tau \le 1$, $\Omega \ge 8$ (stored constants $3$, $4$ by `ofNat`): $\|g(\mathbf{A}) - \tilde g(\mathbf{A})\|_2 \le 4\sqrt n(8 +
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
e^{-rx^2}$; the loss $2r$ costs $\le \log_2 n + 1$ bits. Per the maintainer's comment on OQ7,
this can be improved when the proof is written: Edelman's sharp law would improve the constant
(a follow-up; CG6's docstring says so).

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
1/5$, $(4\mu_{\mathrm{QR}} + 2\sqrt nc_{\mathrm N} + 2\mu_{\mathrm{MM}})u \le \beta$,
$\mu_{\mathrm{MM}}(n), u \ge 0$ (§3.12), floor/range conditions ⟹ $\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le
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

**EB1c** (computed projectors, W4 outline check): on Event I the stored $\mathbf{P}_\pm$ are
within $\beta$ of $\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c'\mathbf{I}))$ (SN4
applied once, with modulus $w - 1.4uR$; $w/2$ is not covered by `husign`), at a node that is not
a leaf (§3.12).
**EB1b** (rank recovery on Event I, public so that EV2 can use it): for an internal node with
seed in $[-1, 1]$ and Event I, the step splits iff $0 < i_+(\mathbf{A} - c'\mathbf{I}) < k$.
**EB1d** (a split node): frames $\mathbf{V}_\pm$, unitaries $\mathbf{W}_\pm$ with
$\|\mathbf{V}_\pm\mathbf{W}_\pm - \mathbf{Q}_\pm\|_2 \le \eta$ and the stored children within
$(2 + 2\eta)R\eta$ of the shifted compressions (DF2 applied once); EB1a and EB1 use it.
**EB2a** (node parameters): $\lvert a\rvert \le \ell$, $k_y \le k$, $\ell_y = \ell + \lvert a\rvert$,
$\varepsilon_y \in [\varepsilon/3, \varepsilon]$, $R_y \le R_0$, shared by EB5 and EV6.
**EB1a** (child invariant): under EB1's hypotheses without the children's guarantee, every child
has a Hermitian matrix of norm at most its window — what EB5's induction needs at each child.
**EB1** (Lemma 4.1): node contracts and precision hypotheses (written in §3.11's table and the
docstring), good sample when internal ($k \ge 2$ and the machine's leaf test $R \le \mathrm{fl}(\varepsilon R_0)$
fails), children approximate
diagonalizations with $(\varepsilon'(R' + R_0), \varepsilon'/3)$ ⟹ node output with
$(\varepsilon(R + R_0), \varepsilon/3)$, using EB1a and EB1b. EB2 depth $\le \ell$ for any counter $\ell \ge \lceil\log_2(1/\varepsilon)\rceil + 5$ (telescoping, now
with the machine's rounded parameters, absorbed for $100\ell^2u \le 1$:
$\prod_{i<\ell}\frac{\ell+i+4}{\ell+i} = \frac{2\ell(2\ell+1)(2\ell+2)(2\ell+3)}{\ell(\ell+1)(\ell+2)(\ell+3)}$
against $\varepsilon_\ell = \varepsilon(\ell-1)/(2\ell-1)$; the paper compares with $\varepsilon$
instead of $\varepsilon_\ell$, which is also fine but by a margin of order $1/\ell$). EB3 at most
$(n+1)(\ell+1)$ nodes, EB4 at most $n$ splits (by induction on the path length, since the tree
may be infinite without depth hypotheses). **EB5**: every internal node good ⟹
$\mathsf{eigh}$ is an approximate diagonalization with $(2\varepsilon R_0, \varepsilon/3)$, under
the global hypotheses with the stored accuracy (a precomputed threshold)
$$0 < \beta \le \frac{\varepsilon\sqrt\theta}{2880\,\ell n^{3/2}(2\sqrt n + \sqrt{2\log(16n/\theta)})}
,\quad N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac\beta{16n}\Bigr),$$
$640n^{3/2}(8 + \mu_{\mathrm{MM}})(N_* + 1)\cdot16n(n+1)\ell(\ell+1)u \le \theta\beta$,
$(4\mu_{\mathrm{QR}} + 2\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}} + 1)u \le \beta$, step cap
$\ge N_*$, $100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$,
$16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)}) \le \Omega$ (the factors $2$: the node lemmas
need $R_y + R_0$ and $\ell_y \le 2\ell$; W4 outline check item 1). All quantities are decodings of stored values; the
machine-computed node parameters differ from the exact ones by factors $(1 \pm u)^{4j}$ at
depth $j$, absorbed in the slack of the constants (2880 against the 2274 Fable derived). Node parameters: $w_y = \theta R_y/(2k_y\ell_y(n+1)(\ell+1))$
(the corrected Event I budget, G2), $x_y = \sqrt{\rho/2}/k_y$, $t_y = \sqrt2(2\sqrt{k_y} +
\sqrt{2\log(4/\rho)})$, $\rho = \theta/(4n)$; with these the deflation tolerance
`bisectionSignTol` (an analysis-side bound, with $\beta$ below it) gives output error at most
$\eta = \varepsilon'/(5\ell)$ and $m\beta \le \eta/6$.

### 3.9 Algorithm 3, probability (EV1–EV7, `Eigensolvers/SpectralBisection.lean`)

EV1 the shift misses a finite set: $\le \lvert\Lambda\rvert w/c$ (with $c = R/\ell$: $nw\ell/R$,
G2). EV2 node bad-event bound $kw\ell/R + 2\rho\,\mathbb{P}[\text{split}]$. EV3–EV5: the node at
a path has countably many values, measurable fibres, and is independent of its own sample —
**without any measurability assumption on MM, QR or fl**: the computed samples are measurable maps
of the ideal ones into countable sets (floating-point numbers are countable), and every node is a
function of finitely many of them (OQ3). **EV6** (Theorem 4.2): the global hypotheses of EB5,
samplers with measurable fibres and countable ranges, $(\zeta_a)$ independent with law `eighSampleLaw n` ⟹
failure probability $\le \theta$. **EV7**: the same with the precision conditions replaced by
$$\log_2\tfrac1u \ge \log_2\tfrac1\varepsilon + \tfrac32\log_2\tfrac1\theta +
\log_2\bigl(n^4(n+1)(8 + \mu_{\mathrm{MM}}) + n^{3/2}(4\mu_{\mathrm{QR}} + 2\sqrt n(c_{\mathrm N}+1)
+ 2\mu_{\mathrm{MM}} + 1)\bigr) + \log_2(N_* + 1) + 3\log_2(\ell + 1) + \log_2(2\sqrt n +
\sqrt{2\log(16n/\theta)}) + 26,$$
for an accuracy within a factor $2$ of its bound, $\beta_*/2 \le \beta \le \beta_*$ (one more bit
than the first draft because $\beta$ is now a precomputed threshold, not the exact bound),
i.e. $\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$
(paper: $n^{4.5}\mu$ and $2\log_2\log_2(1/\varepsilon)$; ours $n^5\mu$ and $3\log_2\ell$, from
the Hermitian rounding, the stopping test and G2). **EV8**: in a bounded binary format with $E$
exponent bits, $\log_2(\log_2(1536(n+\ell+2)^2/(\varepsilon\theta)) + 2) + 1 \le E$ suffices
(input scaled to $R_0 \in [1/2, 1]$): the paper's $\lg\lg(n/\varepsilon) + O(1)$ exponent bits
as a theorem, with $\theta$.

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
| R1 | `isRoundingOf_roundNearest` | S | 0 | — |
| R1b | `isRoundingOf_binaryFloatRound` | M | 0 | — |
| R2 | `FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom` | S | 0 | — |
| R3 | `FloatMachine.IsAccurate.decodeMatrix_negMat` | S | 0 | — |
| R4 | `FloatMachine.IsAccurate.decodeMatrix_conjTransposeMat` | S | 0 | — |
| R5 | `FloatMachine.IsAccurate.decodeMatrix_identityMat` | S | 0 | — |
| R6 | `FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le` | M | 0 | — |
| R7 | `FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermScale_le` | M | 0 | — |
| R8 | `FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le` | M | 0 | — |
| R9 | `FloatMachine.IsAccurate.abs_sum_sub_traceRe_le` | M | 0 | — |

**Matrix/Computation/Primitives.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| C1 | `exists_floatMachine_isAccurate` | M | 0 | — |
| C1b | `exists_floatMachine_isAccurate_binaryFloatRound` | M | 1 | R1b, C1 |
| C3 | `IsMatMulErr.of_specNorm_mul_sub_le_add` | S | 0 | — |

**Matrix/Computation/NewtonSchulzSign.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| SN1 | `FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzRounded` | S | 1 | R2 |
| SN2 | `FloatMachine.IsAccurate.isHermitian_decodeMatrix_newtonSchulzSign` | S | 2 | R2, SN1 |
| SN3 | `FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le` | M | 1 | R3, R6, R8 |
| SN4 | `FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le` | L | 5 | SN3, R7, SG1, SG2, SG3, SG4, NS9, NS10, NS11, NS12 |

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
| DF2 | `FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` | L | 1 | DF1 |

**Eigensolvers/RandomizedDeflation.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| DP1 | `FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le` | M | 4 | DF2, CG2, CG3, CG4, CG6 |

**Probability/AdaptiveUnionBound.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| UB1 | `measureReal_exists_mem_le_of_forall_measure_le_lintegral` | L | 0 | — |

**Matrix/Computation/SpectralBisection.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| EB1c | `FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le` | M | 6 | SN4, SG2, R3, R6, R7 |
| EB1b | `FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub` | M | 7 | EB1c, SG6, R9 |
| EB1a | `FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some` | M | 9 | EB1d, EB1b, R2, R6 |
| EB1d | `FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split` | L | 8 | EB1c, EB1b, SG5, DF2, R2, R4, R6, R8 |
| EB1 | `FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` | H | 10 | EB1c, EB1d, EB1a, EB1b, R4, R5, R8 |
| EB2 | `FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length` | L | 0 | — |
| EB2a | `FloatMachine.IsAccurate.eighNodeAt_eq_some_params` | M | 1 | EB2 |
| EB3 | `FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le` | L | 1 | EB2 |
| EB4 | `encard_eighNodeAt_isSplit_le` | L | 0 | — |
| EB5 | `FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample` | H | 11 | EB1, EB1a, EB2, EB2a, NS11, NS12 |

**Eigensolvers/SpectralBisection.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| EV1 | `measureReal_exists_abs_sub_lt_le` | M | 0 | — |
| EV2 | `FloatMachine.IsAccurate.measure_not_isEighGoodSample_le` | H | 8 | EV1, EB1b, CG2, CG3, CG4, CG6, SG5 |
| EV3 | `countable_range_eighNodeAt` | M | 0 | — |
| EV4 | `measurableSet_eighNodeAt_eq` | L | 1 | EV3 |
| EV5 | `indepFun_eighNodeAt_eq` | H | 2 | EV4 |
| EV6 | `FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le` | L | 12 | EB5, UB1, EV2, EV3, EV4, EV5, EB2, EB2a, EB3, EB4 |
| EV7 | `FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le` | L | 13 | EV6 |
| EV8 | `FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le` | L | 14 | EV7 |

**LowerBounds/Eigensolvers/Precision.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| LB1 | `exists_mul_card_le_specNorm_add_smul` | S | 0 | — |
| LB2 | `mul_card_le_of_forall_specNorm_sub_le` | S | 1 | LB1 |
| LB3 | `logb_inv_add_le_of_forall_specNorm_sub_le` | M | 2 | LB2 |

### 3.12 Statement corrections found while proving

Two scaffold statements were false as written; the provers proved corrected versions and the
public statements now carry the extra hypotheses (integration of `prove/hdiag-core`, 2026-11-06).
No caller's statement changed.

* **DF2** (`FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`) gains
  `(hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u)`. Counterexample without them: $u = 1$, $\mu_{\mathrm{MM}} \equiv
  -4$, $n = r = 1$ (the size condition on $u$ then holds for small $\beta$; since the product
  contract on the stored identity forces $\mu_{\mathrm{MM}}(n) \ge 0$ when $u > 0$ and
  $\Omega \ge 1$, the counterexample lives at a small range $\Omega$). Callers: EB1d supplies
  its own `hμM`, `hu` through its private deflation helper. DP1 derives them: its range
  $\Omega \ge 4\sqrt2$ ($n \ge 1$) and the conversion contract give $u \ge 0$, and the product
  contract on the stored identity gives $\mu_{\mathrm{MM}}(n) \ge 0$ when $u > 0$; at $u = 0$ the
  contract holds with $\mu_{\mathrm{MM}} \equiv 0$ and DF2 is applied with that constant; $r = 0$
  is trivial.
* **EB1c** (`FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le`) gains the
  non-leaf condition `(hint : M.le y.R (M.mul y.ε R₀) = false)`, i.e. $\mathrm{fl}(R) >
  \mathrm{fl}(\varepsilon R_0)$. Without it the window $R$ can lie far below $u\tau$, the
  roundings of the shift are no longer relative to $R$, and the bound fails; with it the floor
  $\tau$ is below $R/2$ and every rounding is relative. Its callers (EB1b and the private
  helpers of EB1d) sit at an internal node and already have `hint`.

## 4. Map to the source

| [Shah2024] | here | deviation |
|---|---|---|
| §1.2 model $\lvert\mathrm{fl}(z) - z\rvert \le u\lvert z\rvert$ | `FloatMachine`, `IsAccurate` (`IsRoundingOf` per operation), complex as pairs, R1 | componentwise IEEE complex; floor $\tau$, range $\Omega$; one rounding per operation |
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

* `FloatMachine` and its contract, `IsMatMulErr`, `IsQRErr`, the entrywise operations: every later analysis of a
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
| `Matrix/Computation/EntrywiseRounding.lean` | `FloatMachine.hermFrom`, `hermShift`, `hermScale`, `hermAvg`, `negMat`, `conjTransposeMat`, `identityMat`, `zeroMat`, `traceRe` | entrywise operations built from the machine's scalar operations |
| `Matrix/Computation/Primitives.lean` | `MatMulMap`, `QRMap`, `IsRoundingOf`, `IsMatMulErr`, `IsQRErr`, `IsUnifSampler`, `IsNormalSampler`, `FloatMachine`, `decodeComplex`, `decodeMatrix`, `FloatMachine.IsAccurate` | the machine and its contract at matrix level (not `Computation/`, whose files may not import Matrix, E5; COMPDYN's `KernelContracts.lean` lifts these contracts) |
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

`FloatMachine` (alternatives `RoundingMachine`, `FloatOps`), `IsRoundingOf`, `decodeComplex`,
`decodeMatrix`, `hermFrom`, `hermShift`, `hermScale`, `hermAvg`, `negMat`, `traceRe`; `MatMulMap`, `QRMap`, `IsMatMulErr` (parallel to
`Computation.IsMatvecErr`), `IsQRErr`, `IsUnifSampler`, `IsNormalSampler`; `newtonSchulz`,
`newtonSchulzSteps`, `newtonSchulzRounded`, `IsNewtonSchulzConverged`, `newtonSchulzLoop`,
`newtonSchulzSign`, `newtonSchulzTest`; `deflate`; `EighSample`, `eighNextParams`, `EighStep`, `EighNode`, `eighStep`,
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
   parts, through the machine's scalar operations (componentwise IEEE), tied to the contract
   layer by the witness R1** — confirmed by the maintainer ("the same way IEEE works"); (b) generalize
   `IsRelErrSem` to `RCLike` decodings in `Computation/Contract.lean` (collides with the current
   bounded-model work; can follow later and would give (a) as a corollary); (c) the paper's
   complex model $\lvert\mathrm{fl}(z) - z\rvert \le u\lvert z\rvert$ for a complex rounding
   function. (a) is what hardware does, keeps Hermitian structure exact without an oddness
   assumption, and implies (c) at $\tau = 0$ (R2).
3. **Representation of the randomized recursion** — decided by the maintainer: shallow total
   functions with fuel recursion, made non-cheating by construction. (a) **chosen: every
   algorithm generic over a `FloatMachine F Su Sg` (§2.0)** — stored numbers and ideal samples of
   abstract types, only the machine's operations on them, computable definitions, natural-number
   bookkeeping exact; samplers with countable ranges make every node a measurable,
   countably-valued function of earlier samples, so no measurability of MM, QR or the scalar
   operations is assumed; (b) a deep-embedded `Prog` (COMPDYN; §15 lists what it needs, and the
   intended refinement is an equality with these definitions); (c) relational run structures.
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
   loses a factor $2r$, i.e. at most $\log_2 n + 1$ bits. Maintainer: "indicate that this can be
   improved when writing the proof" — CG6's docstring and §3.5 now say that Edelman's sharp law
   would improve the constant, as a follow-up.
8. **Hermitian symmetry of the iterates and compressions (gap G1)** — (a) **store the rounded
   Hermitian part (`hermAvg`, one rounding per operation) after each sign step and for
   $\mathbf{C}_\pm$** ($n^2$ flops, error factor $\sqrt n$); (b) strengthen the MM contract to
   "Hermitian output whenever the exact product is Hermitian" (no fast algorithm guarantees it);
   (c) mirror the upper triangle without averaging (exact, but the error grows by
   $\sqrt{2n}$). (a) keeps the black-box contract of the paper.
9. **Event I probability (gap G2)** — (a) **correct the bound to $nw\ell/R$ and shrink $w$ by
   the factor $\ell_x(n+1)/n$**, costing about one $\log_2\log_2(1/\varepsilon)$ bit term
   ($\ell^3$ in place of $\ell^2$); (b) draw the shift on $[-R/2, R/2]$ instead (density
   $1/R$, no $\ell$) and re-derive the window recursion (changes Algorithm 3). (a) keeps the
   algorithm.
10. **Form of the precision conditions and of the thresholds** — (a) **explicit formulas with
    auxiliary variables (`hN : N = …`), the accuracy $\beta$ and the depth counter $\ell$ as
    precomputed inputs carrying exactly the inequalities the proofs use (`hβle`, `hℓ`), and the
    bits corollary EV7 with constant 26** (a lower bound suffices for $\beta$, so the algorithm
    computes no square root or logarithm; COMPDYN §8.2(2), "routine left abstract"); (b) compute
    $\beta$ and $\ell$ in the algorithm with COMPDYN §4.7's bit-length routine (no statement
    change, a lemma that its output meets `hβle`, `hℓ`); (c) named bounds in
    `docs/constants.toml` (a shared file under concurrent edit; at clean-up).
11. **Operation counts** — (a) **out of scope now**; count the black-box calls later with a
    shallow counter (2 MM per sign step, one MM and one QR per deflation) if wanted; (b) state
    `Computation.StaticCost` bounds (only for deep-embedded programs, OQ3(b)). (a): decision 3
    puts runtime out of scope.
12. **Remaining modelling deviations and staging** — (a) **accept the deviations of §2.3 ($k_-
    = k - k_+$, componentwise test before stepping, step caps, one accuracy for all nodes; the
    exact-scalar-parameter deviation is gone, every scalar parameter is machine-computed) and
    dispatch HDIAG-1 (W1 + W2 + LB, 38 targets) and HDIAG-2 (W3, 10) now, HDIAG-3 (W4, 16) after
    a Fable re-check of the H/L outlines** (review items 1–3 applied); (b) approve the sub-stages
    separately.
13. **The Hermitian-exactness clause of `IsMatMulErr`** — (a) **keep it** (classical gemm with
    round-to-nearest-even meets it; SN3 uses it so that the diagonal of $\mathrm{mm}(\mathbf{A},
    \mathbf{A})$ is real); (b) drop it and let `hermShift` discard the imaginary part of that
    diagonal, at an extra $1.21\mu u$ in SN3 (Strassen-type products do not meet the clause, so
    (b) widens the bridge). Fable leans to considering (b) for the bounded bridge; the statements
    change only in SN3's constant.
14. **Target the bounded-exponent model now?** — (a) **now (done)**: the floor/range contracts
    are the mixed model, sampler floors added, R1b, C1b, EV8 (§12); (b) a later bridge. (a): the
    pure-relative case is the $\tau = 0$ instance and the proof routes are unchanged.

## 11. Deferred, with what each needs

* Operation counts and runtime (Theorem 4.2's flop bound): a cost semantics for shallow
  algorithms or a deep-embedded program (OQ11).
* The agreement lemma between the machine of C1b and `binaryFloatSem` on the `safe` set (§12).
* Implementations meeting `IsMatMulErr`/`IsQRErr`: classical $O(n^3)$ complex gemm and Householder
  QR in finite precision (complex decodings in the contract layer, OQ2(b)); the fast algorithms of
  [DemmelDumitriuHoltzKleinberg2007], [DemmelDumitriuHoltz2007].
* Boosting the success probability by residual checks (remark after Theorem 4.2): a randomized
  residual estimator.
* Faster sign iterations (QDWH, Zolo-pd): need per-row backward-stable QR, a different contract.
* A real Gaussian start for real symmetric input: a linear small-ball bound (costs more bits); not
  needed (the complex algorithm covers real input).
* Named bounds for the precision conditions (OQ10(b)).

## 12. The bounded-exponent model (targeted now, OQ14)

Assessment after Codex's merge (`origin/main` a08339af: `Computation.AbsRelErr u η a z`,
$|a - z| \le u|a| + \eta$; `Computation.binaryFloatRound`, gradual underflow;
`Computation.binaryFloatSem` with `safe` $= |a| \le$ `maxFinite`; mixed-error gemm/gemv):

* **Generalization.** None is needed for the scalar operations: `IsRoundingOf u τ Ω a z`
  ($|a| \le \Omega \Rightarrow |a - z| \le u\max(|a|, \tau)$) is the mixed model in floor form
  ($u|a| + \eta \le 2u\max(|a|, \eta/u)$; conversely the floor form gives $\eta = u\tau$), and
  $\Omega$ is exactly `binaryFloatSem`'s `safe` range. The pure-relative statements are the
  $\tau = 0$ instance. Two contracts had no floor and were not satisfiable by a bounded format:
  `IsUnifSampler` (now $|\bar sv - \bar c| \le u\max(\bar s, \tau)$) and `IsNormalSampler` (now
  $|z - \bar z| \le c\,u\max(|z|, \tau)$ for $|z| \le \Omega$). Changed statements: DF2 and DP1
  gain $\sqrt n\,\tau \le \|\mathbf{G}\|_2$ (resp. $\le x$) and the coefficient $4\sqrt n\,c_{\mathrm
  N}$ (was $2$); the node and global theorems (EB1a, EB1b, EB1, EV2, EB5, EV6, EV7) get
  $4\sqrt k(c_{\mathrm N} + 1)$ and $4k^{3/2}\tau$ (was $4k\tau$). Eleven statements changed, no
  difficulty change: in each proof the floor is absorbed by the upper magnitude already used,
  $\max(\cdot, \tau) \le$ that magnitude.
* **Instantiation.** R1b: `binaryFloatRound` is an `IsRoundingOf` $2^{-p}$ rounding with
  $\tau = 2^{e_{\min}+p-1}$ (the smallest normal number) and $\Omega$ = `maxFinite`, with no factor
  lost (half the subnormal spacing is $2^{-p}\tau$). C1b: the machine on stored reals whose
  operations are `binaryFloatRound` of the exact result meets `IsAccurate` (black boxes exact, normal
  sampler $c_{\mathrm N} = \sqrt2$). The machine is total where `binaryFloatSem` fails out of range;
  they agree on the `safe` set, which the theorems' $\Omega$ hypotheses guarantee (an equality
  refinement in the sense of COMPDYN §7.1 needs that agreement lemma, deferred with §15).
* **Extra hypotheses** (already present, in the floor/range form): $100n^{3/2}\tau \le
  \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$, i.e. $R_0 \ge 12n^{3/2}2^{e_{\min}}/(2u\varepsilon)$ —
  $\|\mathbf{A}\|$ bounded below relative to $2^{e_{\min}}\operatorname{poly}(n)/u$ — and
  $16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)}) \le \Omega$. The range invariants come from: SIGN's
  normalized iterates ($\le 1.1$, intermediates $\le 4.9$); DEFLATE's $\|\mathbf{G}\|_2 \in [x,
  t]$ on Event II; EIGH's node budgets ($\ge \varepsilon_yR_0$ at internal nodes, magnitudes $\le
  1.1R_0$).
* **Exponent bits.** EV8: with $E$ exponent bits, $\log_2(\log_2(1536(n+\ell+2)^2/(\varepsilon\theta))
  + 2) + 1 \le E$ and $R_0 \in [1/2, 1]$ (an exact power-of-two scaling) imply both range
  hypotheses, using $e_{\min} + p - 1 = 2 - 2^{E-1}$ and `maxFinite` $\ge 2^{2^{E-1}-1}$.
* **Complex with underflow.** Fine: every complex operation is two real operations, each with
  its own floor; a stored complex entry errs by at most $u\sqrt{\max(|\operatorname{Re}|,\tau)^2 +
  \max(|\operatorname{Im}|,\tau)^2} \le u(|z| + 2\tau)$ (R7, R8 already carry the $2k\tau$ term).
* **Not done**: the black boxes in the bounded format. `IsMatMulErr`/`IsQRErr` are hypotheses; C3
  turns Codex's mixed gemm bound (real) into the floor form, and a complex gemm over pairs is
  COMPDYN's kernel work.

## 13. Proof plan for dispatch

Waves (from `hdiag-targets.json`, the longest dependency chain): wave 0, 30 independent
targets (C1, C3, CG0, CG1, DF1, EB2, EB4, EV1, EV3, LB1, NS1, NS11, NS12, NS2, R1, R1b, R2, R3, R4, R5, R6, R7, R8, R9, SG1, SG2, SG4, SG5, SG6, UB1); then the chains NS2→NS3→{NS7, NS8}→NS9→NS10→SN4→EB1c→EB1b→EB1d→EB1a→EB1→EB5→EV6→EV7→EV8,
NS1→{NS4, NS5, NS6}, NS4→SG3, R6/R8→SN3→SN4, R7→SN4, R2→SN1→SN2, {R1b, C1}→C1b,
CG1→{CG2, CG3, CG4}→CG5→CG6→{DP1, EV2}, DF1→DF2→{DP1, EB1d}, EB1b→EV2, EB2→{EB3, EB2a}, EB2a→{EB5, EV6}, EV3→EV4→EV5→EV6,
LB1→LB2→LB3. Difficulties (67 statements): S 19, M 29, L 15, H 4. By group: W1 31, W2 4,
W3 10, W4 19 (M 6, L 9, H 4), LB 3. Model tiers: S and M on haiku first with sonnet escalation, L and H on opus from
the start (`--hard L,H`). HDIAG-1 (W1 + W2 + LB, 38) and HDIAG-2 (W3, 10) can go now; HDIAG-3 (W4,
19, `~/nlalib-harness/pilot/hdiag3-targets.json`, kept apart from the running HDIAG-1/2 file)
after the W4 outline check's items 1–7 (applied in the sixth commit).

## 14. Literature

[Shah2024] (arXiv:2408.09880v1, read in full from the LaTeX source; numbering of v1);
[BanksGarzaVargasKulkarniSrivastava2020] (context: the deflation it streamlines, the square-root
loss); [DemmelDumitriuHoltzKleinberg2007], [DemmelDumitriuHoltz2007] (the black boxes; not read,
cited in module docstrings only); [Edelman1988, Theorem 3.2] and
[BanksKulkarniMukherjeeSrivastava2021, Lemma 2.2] (cited by the paper for Lemmas 3.1, 3.2; replaced,
not read); [Higham2002, (2.4), Theorem 2.2, (4.4)] (standard model, rounding to nearest, recursive
summation; (4.4) locator to verify); [RudelsonVershynin2008, Lemma 3.5] (the distance step, via the
library). New bibliography entries: the six of §6.

## 15. Toward a deep-embedded version

What `Computation.Prog` would need to express Algorithms 1–3 so that a refinement theorem is an
*equality* with these shallow definitions (COMPDYN, `design/computation-dynamic` eb0c135d,
§§4, 7.1; that track owns the details):

1. **Data-dependent sizes**: a bounded index binder (`bindIdx`, reading a cell, converting by
   the floor, clamping by a bound) for $k_+ = \min(k, \lfloor\mathrm{fl}(t + 1/2)\rfloor_+)$ and
   sized allocation from it; the shallow code already uses exactly this conversion.
2. **Recursion** over the binary tree of nodes with a depth budget ($\ell + 1$), or an explicit
   work stack, with sizes per node.
3. **Black-box kernel calls** for MM and QR with contracts at matrix level that lift
   `IsMatMulErr`/`IsQRErr` functionally on decodings, with a conjugate-transpose flag (here an
   exact `conjTransposeMat` before the call).
4. **Complex data as interleaved real pairs** with named kernels for the entrywise operations of
   §2.1 (one real instruction per rounding, as here).
5. **Samplers** reading a uniform and a Gaussian tape, with the computed sample a deterministic
   function of the tape value (`unif`, `normal`), and a lazy-sampling lemma mapping the program's
   tape reads onto the path-indexed tree `List Bool → EighSample N` (kept here).
6. **Correctly rounded semantics as a function** (`IsCorrectlyRounded fl dec enc sem`), so that
   the machine built from `fl` is the program's arithmetic; exact floor conversion; exact
   negation and comparison.
7. **Precomputed thresholds** $\beta$, $\ell$ as inputs (or the bit-length routine of COMPDYN
   §4.7) and the step limits as sizes.

## 16. End of stage (2026-11-06)

**Proved.** All 67 statements (the 64 of HDIAG-1/2 with the 19 of the W4 file, which superseded
16 of them) are proved and in `NLAlib`; the scaffold library is gone and `lakefile.toml` is
main's again. `#print axioms` of EB5, EV6, EV7, EV8, EB1, DP1, SN4 and LB3 gives `propext`,
`Classical.choice` and `Quot.sound` only. 61 statements were proved by the harness (35 by haiku,
11 by haiku then opus, 15 by opus) and six (DF2, EB1c, EB1d, EB1a, EB1, EV2) by dedicated Opus
provers after their harness batches timed out (branches `prove/hdiag-core`, `prove/hdiag-ev2`).

**Statement corrections.** Besides those made before dispatch (EB1's seed in $[-1, 1]$; DF2's
$\|\mathbf{G}\|_2 \le \Omega$; EB2/EB3's absolute floor; the global range of EB5/EV6/EV7), the
provers found DF2 and EB1c false as written and proved them with the extra hypotheses of §3.12;
no caller's statement changed. Unused hypotheses, kept until the maintainer decides: EV2
`FloatMachine.IsAccurate.measure_not_isEighGoodSample_le` (`hμQ`, `hcN`, `hudefl`), C1
`exists_floatMachine_isAccurate` (`hcN`), LB1 `exists_mul_card_le_specNorm_add_smul` (`hδ`); each
proof references them with `have _ := …`.

**Deviations from the paper** (§0, §4), all now theorems: G1 the iterates of SIGN and the
compressions are stored as rounded Hermitian parts (SN1–SN3, EB1d); G2 the probability of missing
Event I is $nw\ell/R$ (EV1, EV2), which costs the third power of $\ell$ in EV7; G3 Proposition
1.1 chooses the sign of $\pm\delta\mathbf{J}$ from $\mathbf{1}^{\mathsf{T}}\mathbf{R}\mathbf{1}$
(LB1); G4 the $R_0$ part of the children's residual is absorbed by the slack $\varepsilon R_0/\ell$
(EB1). Lemma 2.2 is replaced by Davis–Kahan (SG2) and Edelman's law by the elementary $r^2x^2$
(CG6). Final bit count (EV7): $\log_2(1/u) \ge \log_2(1/\varepsilon) + \tfrac32\log_2(1/\theta) +
\log_2(n^4(n+1)(8 + \mu_{\mathrm{MM}}) + n^{3/2}(4\mu_{\mathrm{QR}} + 4\sqrt n(c_{\mathrm N} + 1) +
2\mu_{\mathrm{MM}} + 1)) + \log_2(N_* + 1) + 3\log_2(\ell + 1) + \log_2(2\sqrt n +
\sqrt{2\log(16n/\theta)}) + 26$, against the paper's $\log_2\max(n^{1.5}\mu_{\mathrm{QR}},
n^2c_{\mathrm N}, n^{4.5}\mu_{\mathrm{MM}}) + 2\log_2\log_2(1/\varepsilon) + \log_2\log_2(n
\log_2(1/\varepsilon)/\theta) + 23$ with the same leading $\log_2(1/\varepsilon) +
1.5\log_2(1/\theta)$.

**Bounded model** (§12): R1b (`binaryFloatRound` is an `IsRoundingOf` with floor the smallest
normal and range the largest finite number), C1b (a bounded-format machine meets `IsAccurate`) and
EV8 ($\log_2(\log_2(1536(n+\ell+2)^2/(\varepsilon\theta)) + 2) + 1 \le E$ exponent bits suffice
for $R_0 \in [1/2, 1]$) are proved. Still deferred: the agreement lemma between C1b's machine and
`binaryFloatSem` on the `safe` set, and the black boxes in the bounded format.

**Bridge to the deep embedding.** COMPDYN S1c/S1d (`design/compdyn-s1cd`,
`docs/design/Computation-SignDeflatePrograms.md`) writes SIGN and DEFLATE as registered `Prog`
trees and proves that every successful run computes exactly `newtonSchulzSign` and `deflate` on
the machine `ScalarSem.toFloatMachine` read off the program's semantics; its targets
`MatrixFreeRoundedProbNewtonSchulzSign` and `MatrixFreeRoundedProbDeflate` transfer SN4 and DP1.
Its three HDIAG-blocked statements (TR1–TR3) can be dispatched once this stage is on main; TR1
(the stopping test passes within $N_0 + 1$ steps, shown inside SN4's proof but not stated) is
owned by HDIAG. Landing note: COMPDYN S1's `Matrix/Computation/KernelContracts.lean` also defines
`MatMulMap`, `QRMap`, `IsMatMulErr` and `IsQRErr` (in this note's shape); whichever lands second
deduplicates them (S1cd plans to use this stage's). Further suggestions from S1cd: split
`IsAccurate` into a scalar-and-`mm` part (SIGN uses no QR or sampler), and restate C1 for every
$u \ge 0$. EIGH itself needs S2 (`bindIdx`, recursion), §15.

**Files** (amendment to §6, D8 move at clean-up): the statements are in the files of §6, with
these changes. `Matrix/Functions/Sign.lean`, `Probability/AdaptiveUnionBound.lean`,
`Eigensolvers/RandomizedDeflation.lean`, `Eigensolvers/SpectralBisection.lean` (sample law,
EV1–EV5), `Eigensolvers/SpectralBisection/Global.lean` (EV6–EV8, new: F10) and
`LowerBounds/Eigensolvers/Precision.lean` are new; C1, C1b and C3 are in `Primitives.lean`, which
no longer imports `EntrywiseRounding` (the scaffold import made a cycle after the move). The
deterministic analysis of Algorithm 3 (5241 scaffold lines) is split into
`Matrix/Computation/SpectralBisection/{Projectors (EB1c, EB1b), Split (EB1d), Child (EB1a),
Node (EB1), Tree (EB2, EB2a, EB3, EB4), Global (EB5)}.lean`; `Node` is 1111 lines (F10 warning). The folder `NLAlib/Eigensolvers/` (OQ1 (a)) still needs its `LAYER` entry in
`scripts/check_rules.py` and its CONTRIBUTING §2 line (maintainer edits).
