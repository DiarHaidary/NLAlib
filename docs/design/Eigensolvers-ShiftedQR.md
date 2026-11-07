# Design note: global convergence of the Hessenberg shifted QR algorithm — potential, promising Ritz values, exceptional shifts (stage SHIFTED-QR)

Status: proved and moved into `NLAlib` (end of stage, §16, 2026-11-07). Earlier: design; Fable review applied (second commit, §13). Branch `design/shifted-qr` (worktree `~/nlalib-design-sqr`, from
`origin/main` 0e9d7d6c). Decision sheet `~/nlalib-harness/state/decisions/SHIFTED-QR.json`
(APPROVE, OQ1–OQ10; reviewer fields empty for Fable). Targets
`~/nlalib-harness/pilot/shifted-qr-targets.json` (stage SQR-1, 50 statements). Board card T109.

Sources read in full from the LaTeX (data, `~/nlalib-harness/research/shifted-qr/`):

* [BanksGarzaVargasSrivastava2021] J. Banks, J. Garza-Vargas, N. Srivastava, *Global convergence
  of Hessenberg shifted QR I: exact arithmetic*, arXiv:2111.07976 (FoCM). Source dated
  2023-10-16 (post-referee). **Numbering below is that of this source**, computed from its
  environments (one counter per section, shared by theorems, lemmas, definitions and remarks).
  Part II (below) cites an earlier numbering of Part I: its "Lemma 2.2, 2.3, 2.4, 2.7, 2.8,
  Definition 1.2, Remark 1.4" are Lemma 2.3, 2.5, 4.2, 4.5, 4.6, Definition 1.5, Remark 1.8 here.
* [BanksGarzaVargasSrivastava2022] *… II: numerical stability*, arXiv:2205.06810, source dated
  2022-05-13 (v1), numbering of that source.
* Part III (*… III: approximate Ritz values via shifted inverse iteration*, arXiv:2205.06804)
  was **not fetched**: Part I takes a Ritz-value finder as a black box (Definition 1.5) and
  Part II takes the small eigensolver $\mathsf{SmallEig}$ as a black box (Definition 1.2,
  Theorem 1.3 citing Part III, Corollary 1.3); no proof in I or II uses Part III's arguments.

Library read: `Matrix/Factorizations/{QR,Hessenberg,Givens,GivensHessenberg,Householder}.lean`,
`Matrix/Spectral/{Diagonalizable,Normal,Schur,EigenvalueListing,SpectralMeasure}.lean`,
`Matrix/Perturbation/{Residual,Pseudospectrum}.lean` (Bauer–Fike is
`NLAlib.exists_norm_sub_le_pseudoConditionNumber_mul_specNorm`),
`Matrix/Pseudoinverse/ConditionNumber.lean`, `Matrix/Computation/KernelContracts.lean`,
`ForMathlib/Probability/Moments/PaleyZygmund.lean`; notes `Computation.md`,
`Computation-DynamicPrograms.md` (COMPDYN), the HDIAG note and its final code on `feat/hdiag`
(`~/nlalib-cleanup-hdiag`: `FloatMachine`, `Primitives.lean`, `EntrywiseRounding.lean`,
`Probability/AdaptiveUnionBound.lean`), the Lanczos-reorth note.

Checks on the skeleton (this branch, `LEAN_NUM_THREADS=2`): §15.

## Maintainer rules this design follows

1. **No cheating outside the model of computation.** Part I is a theorem about exact arithmetic,
   so it is designed as *mathematics about an exact iteration*: noncomputable definitions of the
   QR step, the potential and the shift rule, tagged `Algorithm: shifted-qr (specification)`.
   They claim no cost and are not examples of implementable code; they are the specification
   that the stage-2 machine algorithm refines (§2.0, OQ2). Part II's algorithm is designed
   through the model (§9, OQ4).
2. **Essence, not verbatim.** Finite weighted sums replace the random variable $Z_H$; an
   explicit square grid replaces the maximal net; the iteration is one Lean sequence with a
   Ritz-value oracle; singular shifts are handled by a lemma instead of being "ignored"; constants
   change where the paper's are wrong or where the grid costs a factor (§4).
3. Results go to main only complete; no "new/improved" wording in docstrings.
4. Theory first; no numerics were used (the constants were checked by hand, §10).
5. Modular and staged (§13): stage SQR-1 (this skeleton, 50 targets, ≈ HDIAG-1+2) and stage
   SQR-2 (Part II in finite precision, ≈ 60 targets, §9), with an explicit dependency graph.

## 0. Summary

| | |
|---|---|
| Objects (new, `NLAlib`, build `--wfail`) | `IsDecoupled`, `hessenbergPotential` ($\psi_k$), `shiftPoly`, `shiftedQRStep` (one Givens QR step), `multiShiftedQRStep` (degree $k$ step as $k$ single steps), `trailingBlock`, `ritzValues`; `lastRowWeights` (the law of $Z_H$); `IsOptimalRitzValues`, `IsPromisingRitzValue`, `findRitz` (Find); `squareGrid`, `exceptionalRadius`, `exceptionalSpacing`, `IsShiftSuccess`, `shqrCandidates`, `shqrShift`, `shqrStep`, `shqrIterate` ($\mathsf{Sh}_{k,B}$ and the iteration) |
| Headline (M3) | For $\mathbf{H}_0$ upper Hessenberg, $\mathbf{H}_0\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, $k = 2^m \le n$, $\theta$-optimal Ritz oracle, $B^{4m} \le \alpha^k$, $0 < \gamma < 1$: some $t \le \lceil\log(1/\delta)/\log(1/(1-\gamma))\rceil$ has $\mathbf{H}_t$ $\delta$-decoupled (Theorem 1.6(1)) |
| Other results | variational formula (Lemma 2.3), $\psi_k(\widehat{\mathbf{H}}) \le \tau_p(\mathbf{H})$ (Lemma 2.5) and the singular case, approximate functional calculus (Lemma 4.2), moment comparison and almost-monotonicity (Lemma 4.4), Find (Lemma 4.5), stagnation implies support (Lemma 4.6), Exc (Lemma 4.7), one iteration (M1), shifts per iteration (Theorem 1.6(2) as a count, M4/M5), normal case (N1, Theorem 1.2); from Part II the exact-arithmetic composition lemma (3.2) and the dichotomy (Lemma 4.2, Theorem 4.1) |
| Paper gaps found | 17 (§10); four change statements: G1 the normal-case exceptional net does not reduce the potential as printed; G2 "$\mathrm{dec}_\delta \le 4\log(1/\delta)$" is false for $\delta$ near 1; G4 the singular case of Lemma 2.5; G10 the dichotomy's constant $\tfrac12$ is not reached (true: $\tfrac12k^{-1/(2k)} \ge \tfrac25$) |
| Statements (SQR-1) | 50 sorried: S 26, M 16, L 8, H 0, in 8 scaffold files |
| Waves | 0–6 (§13); critical path Q0 → Q1 → Q3 → Q6 → M1 → M3 → N1 |
| Stage 2 (SQR-2) | Part II in finite precision, ≈ 60 statements (S ≈ 12, M ≈ 25, L ≈ 16, H ≈ 6), §9 |
| Open questions | 10 (§12) |

## 1. Scope

**In (SQR-1).** (i) The exact Hessenberg shifted QR step built from the library's Givens QR, its
Hessenberg invariance, its factorisation of the shift polynomial, norm and eigenvector-condition
invariance, and the exact singular case. (ii) The potential $\psi_k$, its variational
characterisation and the bound $\psi_k(\widehat{\mathbf{H}}) \le \tau_p(\mathbf{H})$. (iii) The
approximate functional calculus for a diagonalised $\mathbf{H}$, finite weighted Paley–Zygmund.
(iv) $\theta$-optimal and $\alpha$-promising Ritz values, the binary search Find, the moment
comparison and almost-monotonicity. (v) Stagnation implies support, the exceptional grid, one
iteration of $\mathsf{Sh}_{k,B}$, the rapid-decoupling theorem, the count of shifts tried per
iteration with the paper's parameter instance, the normal case. (vi) From Part II, the
exact-arithmetic dichotomy (§4.1 there), which needs no arithmetic model and front-loads the
hardest new mathematics of Part II.

**Out of SQR-1.** Operation counts ($T_{\mathsf{iqr}} \le 7kn^2$, the $O(kn^2\log k)$ of Find,
$T_{\mathrm{OptRitz}}$): Part I counts operations of an implementation it never defines, so a
count belongs with the stage-2 algorithm (§9; the count of QR steps per iteration *is* in, M4).
The Ritz-value finder itself (Part III, or any provable eigensolver): an oracle hypothesis.
Deflation and the full algorithm, $\kappa_V$ and gap perturbation, all floating-point analysis:
stage 2. Smoothed analysis (Remark 1.8, random perturbation regularises $\kappa_V$): needs
pseudospectral regularization Banks–Garza-Vargas–Kulkarni–Srivastava 2020 (pseudospectral shattering; in the bibliography of `feat/hdiag`), deferred (§11).

## 2. Objects

### 2.0 The exact iteration and the model of computation (OQ2)

The QR step is `shiftedQRStep H s := Qᴴ * H * Q` with `Q = givensHessenbergQ (H - s • 1)`, the
library's Givens QR (`Matrix/Factorizations/Givens.lean`), and the degree $k$ step is the fold of
single steps, exactly the "implicit QR step" of Part I (Definition 2.1, black box there) and the
$\mathsf{iqr}$ of Part II (§3.1, composed degree-1 steps). Using Givens rather than "the QR with
positive diagonal" has three effects: it is a total function (no case on invertibility); it
keeps the Hessenberg form also for singular shifts, which the paper's singular case silently
needs (G4); and it is literally the computation that stage 2 rounds, so the forward-error lemmas
of Part II compare `iqr` with this `shiftedQRStep` and nothing else.

The shift rule `shqrShift` compares exact real numbers and decides $\det(\mathbf{H} -
r\mathbf{I}) = 0$ (classical decidability, `Classical.propDecidable`, local to each definition;
no file-level `open Classical`). That is legitimate for a specification and illegitimate for an
implementation; the module docstrings say so, and the definitions are tagged as specifications.
No statement of SQR-1 is about cost or arithmetic. Stage 2 defines the implemented algorithm
over a machine (§9) and proves it refines this specification up to the forward errors of
Part II; with the exact machine ($u = 0$) the refinement is an equality, as in COMPDYN §7.1.

### 2.1 Definitions (`NLAlib/Matrix/QRIteration/`, written, `--wfail`)

Matrices are `Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ` (T6: order matters; ℂ because the
eigenvalues of a nonsymmetric matrix are complex, T7 does not apply). The last row
$\mathbf{e}_n^{\mathsf{H}}\mathbf{M}$ is `M (Fin.last n)` and its norm
`‖WithLp.toLp 2 (M (Fin.last n))‖` (T1). Subdiagonal entry $i < n$ is `H i.succ i.castSucc`.

* `ShiftedQR.lean`: `IsDecoupled δ H` ($\exists i$, $\lvert\mathbf{H}_{i+1,i}\rvert \le
  \delta\|\mathbf{H}\|_2$; $\delta = 0$ is "reduced"); `hessenbergPotential k H` $=
  (\prod_{n-k \le i < n}\lvert\mathbf{H}_{i+1,i}\rvert)^{1/k}$; `shiftPoly ss` $=\prod(X - C s)$;
  `shiftedQRStep`, `multiShiftedQRStep`; `trailingBlock k H` (indices clamped, junk for $k > n+1$);
  `ritzValues k H` (roots of the charpoly of the trailing block, `Multiset.toList`).
* `EigenvectorWeights.lean`: `lastRowWeights V i` $=\lvert\mathbf{V}_{n,i}\rvert^2/
  \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2$ (OQ8).
* `Ritz.lean`: `IsOptimalRitzValues θ H ss` ($\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\| \le
  (\theta\psi_k)^k$, the minimum of Definition 1.5 written as $\psi_k^k$ by Lemma 2.3);
  `IsPromisingRitzValue α V d ss r` (Definition 4.3, membership included);
  `findRitz H m e ss` (Find: halve, keep the half with the larger
  $\|\mathbf{e}_n^{\mathsf{H}}p_h(\mathbf{H})^{-e}\|$, double $e$).
* `Strategy.lean`: `squareGrid c R ε` ($(m+1)^2$ points, $m = \lceil\sqrt2/\varepsilon\rceil$);
  `exceptionalRadius k B θ α ψ` $=(2B)^{1/k}\theta\alpha\psi$; `exceptionalSpacing k B θ α ρ`
  $=(\rho/((14B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)}$; `IsShiftSuccess γ k H s`;
  `shqrCandidates` (Find's $r$, then the grid); `shqrShift` (a Ritz value that is an eigenvalue,
  else a success, else $r$, by `open Classical in` and `if h : ∃ … then h.choose`); `shqrStep`; `shqrIterate B θ α γ m ritz H₀ t`.

**Eigenvector condition (OQ9).** No definition of $\kappa_V$: every statement takes
`(hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)` and `pseudoConditionNumber V ≤ B` (or
$\kappa = $ `pseudoConditionNumber V`), the library's Bauer–Fike convention. $\kappa_V(\mathbf{H})
\le B$ is "some such $\mathbf{V}$ exists", and the infimum (attained, Part I §2) is never needed.

**$Z_H$ (OQ8).** $\mathbb{E}f(Z_H) = \sum_i w_if(\mathbf{d}_i)$ with $w$ = `lastRowWeights V`,
$\mathbb{P}[Z_H \in S] = \sum_{\mathbf{d}_i \in S} w_i$. The paper's proofs use only finite
Jensen, AM–GM and Paley–Zygmund, so the matrix files need no measure theory; Paley–Zygmund for
finite weighted sums is one ForMathlib lemma (W1).

**Degenerate shifts.** Lean divides by zero to $0$, so every moment statement assumes no shift
is an eigenvalue (`hd : ∀ i, ∀ s ∈ ss, d i ≠ s`). The strategy discharges this by its first
clause (a Ritz value that is an eigenvalue decouples exactly, Q9), and Exc's conclusion has the
alternative "$\det(\mathbf{H} - s\mathbf{I}) = 0$" (OQ6).

## 3. Statements

Each docstring has the statement in LaTeX, the citation, a `Proof:` paragraph naming the library
lemmas, and the difficulty; the targets file copies the outline.

### 3.1 Potential (P1–P6, `QRIteration/ShiftedQR.lean`)

P2a, P2b: the last row of $p(\mathbf{H})$ vanishes before column $n - k$ and equals
$\prod\mathbf{H}_{i+1,i}$ there. P3 ($\psi_k^k \le \|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$,
Lemma 2.3 lower bound) and **P4** (equality for $\chi_k$ of the trailing block, Lemma 2.3, by
Cayley–Hamilton on the block). P5 $\psi_k \le \|\mathbf{H}\|_2$, P6 small potential ⇒
decoupled. All need $1 \le k \le n$ (for $k > n$ or $n = 0$ the product has fewer factors and P5
fails).

### 3.2 The QR step (Q0–Q9)

Q0 (`GivensHessenberg.lean`, an addition): the Givens unitary factor is Hessenberg for every
input. Q1/Q1b Hessenberg invariance; **Q3** $p(\mathbf{H}) = \mathbf{Q}\mathbf{R}$ with
`multiShiftedQRStep` $= \mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}$, no invertibility (Part II
Lemma 3.2 without its positive-diagonal uniqueness); Q4 norm, Q5 eigenvector matrix with the same
condition number. **Q6** (Lemma 2.5): $\psi_k(\widehat{\mathbf{H}})^k\|\mathbf{e}_n^{\mathsf{H}}
p(\mathbf{H})^{-1}\| \le 1$ for invertible $p(\mathbf{H})$. **Singular case** (G4): Q8 a zero
subdiagonal persists through a Givens step (the rotation at that index is diagonal); Q7 a
singular single shift gives a zero at $(n, n-1)$ (unreduced: $\mathbf{R}_{n,n} = 0$); Q8b, Q9 the
multi-step versions. Together: for every shift, the step is reduced or Q6 applies.

### 3.3 Approximate functional calculus (F1–F6, W1)

F1, F2, F2b (`Spectral/Diagonalizable.lean`, additions, general `Fintype` index):
$p(\mathbf{H})$, $p(\mathbf{H})^{-1}$ and powers of $\mathbf{V}\operatorname{diag}(\mathbf{g})
\mathbf{V}^{-1}$ in the eigenbasis. F6: a normal matrix has an eigenvector matrix of condition
$1$. F5, F5a: the weights are a probability vector. **F3/F4** (Lemma 4.2, the two sides as two
theorems, T11): $\sum_iw_i\lvert\mathbf{g}_i\rvert^2 \le \kappa^2\|\mathbf{e}_n^{\mathsf{H}}
\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}\|^2$ and the converse, squared to avoid
roots. W1 (ForMathlib, `Analysis/MeanInequalities.lean`): finite weighted Paley–Zygmund
$(1 - t)^2(\mathbb{E}X)^2 \le \mathbb{E}X^2\,\mathbb{P}[X > t\mathbb{E}X]$.

### 3.4 Ritz values (R1a–R5, L1)

R1a/R1b: exact Ritz values are $k$ in number and $1$-optimal (so a θ-optimal oracle exists for
every $\theta \ge 1$). R2: $\lvert\rho\rvert \le \|\mathbf{H}\|_2$. **R3** (Lemma 4.4, (4.2)):
$1 \le \kappa(\alpha\theta\psi)^k\,\mathbb{E}\lvert Z - r\rvert^{-k}$. R4 almost-monotonicity
$\psi_k(\widehat{\mathbf{H}}) \le \kappa^{2/k}\alpha\theta\psi_k(\mathbf{H})$ (Lemma 4.4; not
used by M3, kept because it is the paper's explanation of why degree $\log\kappa_V$ works, and is
cheap). **L1** one halving of Find loses $\kappa^4$ (with the squares the printed chain omits,
G5); **R5** (Lemma 4.5) Find returns an $\alpha$-promising value whenever $\kappa^{4m} \le
\alpha^{2^m}$.

### 3.5 Stagnation and exceptional shifts (S1–S4, E1)

**S1** (Lemma 4.6) under the weaker hypothesis $\tau_{(z-r)^k} \ge \xi\psi$ (Part II (2.2)):
$(1-t)^2\xi^{2k} \le \kappa^4(\alpha\theta)^{2k}\,\mathbb{P}[\lvert Z - r\rvert \le
\alpha\theta(\kappa/t)^{1/k}\psi]$. S2–S4 the grid: covering, $\le 12/\varepsilon^2$ points for
$\varepsilon \le 1$, within $\sqrt2R$ of the centre. **E1** (Lemma 4.7): with stagnation ratio
$\xi$ and spacing $\varepsilon = (\xi(1-\gamma)/((14B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)}$, some
grid point is an eigenvalue or has $\tau_{(z-s)^k} \le (1-\gamma)\psi$. The constant $14 \ge
\sqrt{192}$ replaces the paper's $12 = \sqrt{144}$ because the grid has $12/\varepsilon^2$ points,
not $9/\varepsilon^2$ (OQ7). $\xi$ is general so that stage 2 reuses E1 with
$\xi = 0.999^{1/k}(1-\gamma)$.

### 3.6 The iteration (M1–M5, N1)

**M1** one iteration: reduced, or $\psi_k$ drops by $1-\gamma$ (no positivity hypothesis: a
reduced input stays reduced). M2a–c invariants along `shqrIterate`. **M3** (Theorem 1.6(1),
headline): decoupled within $\lceil\log(1/\delta)/\log(1/(1-\gamma))\rceil$ steps. M4: at most
$1 + 12/\varepsilon^2$ candidates per iteration. M5: at $\theta = 2$, $\gamma = 0.2$,
$\alpha = B^{4m/k}$, $\varepsilon \ge 0.0018B^{-(8m+4)/(k-1)}$ (paper $0.002$ with $12$). N1
(Theorem 1.2): normal $\mathbf{H}_0$, exact Ritz values, $B = \theta = \alpha = 1$, any $k = 2^m$.

The headline signature:

```lean
theorem IsUpperHessenberg.exists_le_isDecoupled_shqrIterate
    {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H₀)
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H₀ * V = V * Matrix.diagonal d)
    {B θ α γ : ℝ} (hB : pseudoConditionNumber V ≤ B) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n)
    (hθ : 1 ≤ θ) (hα1 : 1 ≤ α) (hα : B ^ (4 * m) ≤ α ^ 2 ^ m) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ}
    (hritz : ∀ H', IsUpperHessenberg H' → 0 < hessenbergPotential (2 ^ m) H' →
      (ritz H').length = 2 ^ m ∧ IsOptimalRitzValues θ H' (ritz H'))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t ≤ ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊,
      IsDecoupled δ (shqrIterate B θ α γ m ritz H₀ t)
```

The oracle hypothesis quantifies over all Hessenberg matrices with $\psi_k > 0$ (the iterates
are Hessenberg by M2a), as Definition 1.5 requires a Ritz-value finder to succeed only when the
minimum is nonzero, and as stage 2's Regularize delivers (for $\varepsilon$-unreduced input);
the proof uses the oracle only at unreduced iterates (review item 3). It is satisfiable by
`ritzValues` (R1b, monotone in $\theta$).

### 3.7 The dichotomy (D1, D2; Part II §4.1, exact)

**D1** (Part II Lemma 4.2): perturbing the roots by $\le \beta \le c\Gamma$ raises
$\mathbb{E}\lvert q(Z)\rvert^2$ beyond $(1 + 2c)^{2k}$ times only through weight within
$\beta/(2c)$ of the roots. **D2** (Part II Theorem 4.1): forward-approximate Ritz values are
$\theta$-optimal, or one is an eigenvalue, or one has
$\tfrac25\psi(1 - x/\theta) \le \kappa^{2/k}(\|\mathbf{H}\|_2 + \beta)\beta\,\tau^{-1}$ — constant
$\tfrac25$ (G10) and strict $\beta < c\Gamma$ (G10b).

### 3.8 Full list

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| Q0 | `isUpperHessenberg_givensHessenbergQ` | M | 0 | — |
| P1 | `hessenbergPotential_pow` | S | 0 | — |
| P2a | `IsUpperHessenberg.aeval_apply_last_eq_zero` | M | 0 | — |
| P2b | `IsUpperHessenberg.aeval_apply_last_eq_prod` | M | 0 | — |
| P3 | `IsUpperHessenberg.hessenbergPotential_pow_le_norm_aeval` | S | 1 | P1, P2b |
| P4 | `IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq` | L | 1 | P1, P2a, P2b |
| P5 | `hessenbergPotential_le_specNorm` | S | 0 | — |
| P6 | `isDecoupled_of_hessenbergPotential_le` | S | 1 | P1 |
| Q1 | `IsUpperHessenberg.isUpperHessenberg_shiftedQRStep` | S | 1 | Q0 |
| Q1b | `IsUpperHessenberg.isUpperHessenberg_multiShiftedQRStep` | S | 2 | Q1 |
| Q3 | `IsUpperHessenberg.exists_isQR_aeval_shiftPoly` | M | 2 | Q1 |
| Q4 | `specNorm_multiShiftedQRStep` | S | 0 | — |
| Q5 | `exists_isUnit_mul_eq_mul_diagonal_multiShiftedQRStep` | S | 0 | — |
| Q6 | `IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le` | M | 3 | Q3, Q1b, P3 |
| Q8 | `IsUpperHessenberg.shiftedQRStep_apply_succ_castSucc_eq_zero` | M | 1 | Q0 |
| Q8b | `IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep` | S | 2 | Q8, Q1 |
| Q7 | `IsUpperHessenberg.isDecoupled_zero_shiftedQRStep_of_det_eq_zero` | L | 2 | Q8 |
| Q9 | `IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero` | M | 3 | Q7, Q8b, Q1 |
| F1 | `aeval_eq_mul_diagonal_mul_inv` | S | 0 | — |
| F2 | `inv_aeval_eq_mul_diagonal_mul_inv` | S | 1 | F1 |
| F2b | `mul_diagonal_mul_inv_pow` | S | 0 | — |
| F6 | `IsStarNormal.exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_eq_one` | S | 0 | — |
| W1 | `Finset.sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter` | M | 0 | — |
| F5a | `lastRowWeights_nonneg` | S | 0 | — |
| F5 | `sum_lastRowWeights` | S | 0 | — |
| F3 | `sum_lastRowWeights_mul_sq_le` | M | 0 | — |
| F4 | `norm_mul_diagonal_mul_inv_last_sq_le` | M | 0 | — |
| R1a | `length_ritzValues` | S | 0 | — |
| R1b | `IsUpperHessenberg.isOptimalRitzValues_one_ritzValues` | S | 2 | P4, R1a |
| R2 | `norm_le_specNorm_of_mem_ritzValues` | S | 0 | — |
| R3 | `IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div` | M | 1 | F1, F3, F5, F5a |
| R4 | `IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_replicate_le` | M | 4 | R3, F2, F2b, F3, Q6 |
| L1 | `sum_lastRowWeights_div_norm_eval_shiftPoly_le` | M | 2 | F2, F2b, F3, F4, F5a |
| R5a | `findRitz_mem` | S | 0 | — |
| R5 | `isPromisingRitzValue_findRitz` | M | 3 | L1, R5a |
| S1 | `IsOptimalRitzValues.sq_mul_pow_le_mul_sum_lastRowWeights_filter` | M | 2 | R3, W1, F2, F2b, F3, F5, F5a |
| S2 | `exists_mem_squareGrid_norm_sub_le` | M | 0 | — |
| S3 | `length_squareGrid_le` | S | 0 | — |
| S4 | `norm_sub_le_of_mem_squareGrid` | S | 0 | — |
| E1 | `IsOptimalRitzValues.exists_mem_squareGrid_det_eq_zero_or_one_le` | L | 3 | S1, S2, S3, F2, F2b, F3, F5a |
| M1 | `IsUpperHessenberg.isDecoupled_zero_shqrStep_or_hessenbergPotential_le` | L | 4 | E1, R5, R5a, Q6, Q9, Q8b, F1, F2 |
| M2a | `IsUpperHessenberg.isUpperHessenberg_shqrIterate` | S | 3 | Q1b |
| M2b | `specNorm_shqrIterate` | S | 1 | Q4 |
| M2c | `exists_isUnit_mul_eq_mul_diagonal_shqrIterate` | S | 1 | Q5 |
| M3 | `IsUpperHessenberg.exists_le_isDecoupled_shqrIterate` | L | 5 | M1, M2a, M2b, M2c, P5, P6 |
| M4 | `length_shqrCandidates_le` | S | 1 | S3 |
| M5 | `exceptionalSpacing_ge` | L | 0 | — |
| N1 | `IsStarNormal.exists_le_isDecoupled_shqrIterate_ritzValues` | S | 6 | M3, F6, R1a, R1b |
| D1 | `sum_lastRowWeights_mul_norm_eval_sq_sub_le` | L | 1 | F5a |
| D2 | `IsUpperHessenberg.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le` | L | 2 | D1, F1, F2, F2b, F3, F4, P4, R1a, R2 |

## 4. Map to the source and deviations

| source | here | deviation and reason |
|---|---|---|
| I, Def 2.1 (implicit QR, black box) | `shiftedQRStep`, `multiShiftedQRStep` | defined by Givens QR; total; Hessenberg also when singular (G4) |
| I, Def 2.2 potential | `hessenbergPotential` | $k$ factors, not the printed $k+1$ (G3) |
| I, Lemma 2.3 | P2a, P2b, P3, P4 | split into the row structure and the two inequalities |
| I, Def 2.4 $\tau_p$, Lemma 2.5 | Q6 (invertible), Q7–Q9 (singular) | product form $\psi^k\|\cdot\| \le 1$, no $\tau$ definition; singular case gives "reduced", not $\psi_k = 0$ |
| I, Def 1.5 θ-optimal | `IsOptimalRitzValues` | the minimum written as $\psi_k^k$ (Lemma 2.3) |
| I, Def 4.1 $Z_H$, Lemma 4.2 | `lastRowWeights`, F3, F4 | finite sums; any invertible $\mathbf{V}$ (no normalisation $\|\mathbf{V}\| = \|\mathbf{V}^{-1}\|$); $f(\mathbf{H})$ only as $\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}$ |
| I, Def 4.3, Lemma 4.4 | `IsPromisingRitzValue`, R3, R4 | no-eigenvalue hypothesis explicit |
| I, Find, Lemma 4.5 | `findRitz`, L1, R5 | halves by `take`/`drop`; any $\alpha$ with $\kappa^{4m} \le \alpha^k$ |
| I, Lemma 4.6 | S1 | Part II's weaker stagnation hypothesis; ratio $\xi$ general |
| I, Exc, Lemma 4.7 | `squareGrid`, `exceptionalSpacing`, S2–S4, E1 | explicit square grid, $12/\varepsilon^2$ points, constant $14$; ratio $\xi$ general; "or an eigenvalue" |
| I, $\mathsf{Sh}_{k,B}$ | `shqrCandidates`, `shqrShift`, `shqrStep` | first clause for a Ritz value that is an eigenvalue (OQ6); any success, by classical choice (the paper: the first in order) |
| I, Thm 1.6(1) | M3 | ceiling (G2); oracle hypothesis on all Hessenberg matrices |
| I, Thm 1.6(2) | M4, M5 | count of QR steps per iteration instead of arithmetic operations; $0.0018$ for $0.002$ |
| I, Thm 1.2 / Thm 3.3, Lemma 3.2 | N1 | via the general strategy with $B = 1$, not the separate greedy Wilkinson $\mathsf{Sh}_{2,1}$ (whose printed net is wrong, G1); Lemma 3.2 is S1 at $\kappa = 1$ |
| I, Remarks 1.7–1.9, 3.4, 3.5, 4.8 | — | not formalised (§11) |
| II, Lemma 3.2 | Q3 | no invertibility, no uniqueness |
| II, Lemma 4.2, Thm 4.1 | D1, D2 | constant $\tfrac25$, strict gap (G10, G10b) |

## 5. Consumers

* `shiftedQRStep`, Q0–Q9: stage 2 (forward error compares `iqr` with it), any later QR-iteration
  analysis (Wilkinson shift on tridiagonal matrices, Part II Remark 1.7; unitary Hessenberg
  QR; aggressive early deflation).
* `hessenbergPotential`, P3/P4: the Krylov connection (the potential is the Arnoldi residual
  product; GMRES/Arnoldi minimal polynomials in `Krylov/`).
* `lastRowWeights`, F3/F4: any argument "spectral measure up to $\kappa_V$" for nonnormal
  matrices (pseudospectral bounds on Krylov methods, non-Hermitian Lanczos).
* `IsOptimalRitzValues`, D2: stage 2's Regularize; any later analysis of Ritz-value shifts.
* W1: other finite Paley–Zygmund uses (anti-concentration of quadratic forms).
* M3: the stage's claim; stage 2's main theorem is its finite-precision counterpart.

## 6. Files and placement

New `NLAlib` files (definitions only, written): `Matrix/QRIteration/{ShiftedQR,
EigenvectorWeights,Ritz,Strategy}.lean`. The new Matrix subfolder `QRIteration/` (OQ5): the
QR iteration is a topic of its own (dynamics of an iteration, not a factorization), and stage 2
adds `QRIteration/Dichotomy.lean` and, for its rounded parts, files in `Matrix/Computation/`
(deterministic) and `Eigensolvers/` (probabilistic, the HDIAG folder). Additions to existing
files (homes): Q0 → `Matrix/Factorizations/GivensHessenberg.lean` (a property of Givens QR);
F1, F2, F2b, F6 → `Matrix/Spectral/Diagonalizable.lean` (functions of a diagonalised matrix);
W1 → new `ForMathlib/Analysis/MeanInequalities.lean` (scalar, P9; upstream next to Mathlib's
`Analysis/MeanInequalities.lean`).

Scaffold files (paths mirror the homes): `NLAlibScaffold/Matrix/Factorizations/
GivensHessenberg.lean` (Q0), `…/Matrix/Spectral/Diagonalizable.lean` (F1, F2, F2b, F6),
`…/ForMathlib/Analysis/MeanInequalities.lean` (W1), `…/Matrix/QRIteration/{ShiftedQR (P*, Q*),
EigenvectorWeights (F3–F5a), Ritz (R*, L1), Strategy (S*, E1, M*, N1), Dichotomy (D1, D2)}.lean`.

Other edits: `NLAlib.lean` (four generated import lines), `lakefile.toml` (the `NLAlibScaffold`
library, as on the HDIAG and LB-C design branches; a build-pin edit under AGENTS.md rule 1,
needed only for the sorried statements, which **must not reach main**: it is dropped before the
stage lands),
`docs/references.bib` (two entries). Not touched: `docs/constants.toml` (no named bound: the
spacing and radius are definitions with explicit formulas, OQ10), CONTRIBUTING's vocabulary
(rows for `hessenbergPotential`, `IsDecoupled`, `lastRowWeights`, `IsOptimalRitzValues` proposed
here, added with the implementation PR; V7 warns until then), Mathlib-deviations (no deviation:
Mathlib has no Hessenberg QR iteration).

**Names for review.** `hessenbergPotential` (alternatives `subdiagPotential`,
`ritzPotential`), `IsDecoupled`, `shiftPoly`, `shiftedQRStep`, `multiShiftedQRStep`,
`trailingBlock`, `ritzValues`, `lastRowWeights`, `IsOptimalRitzValues`, `IsPromisingRitzValue`,
`findRitz`, `squareGrid`, `exceptionalRadius`, `exceptionalSpacing` (not `…Factor`/`…Bound`: they
are algorithm parameters, not named bounds, so B1/N11 do not apply), `IsShiftSuccess`, and the
`shqr` prefix for the strategy ($\mathsf{ShiftedQR}$ of the papers; `shiftedQRStrategy…` is the
long alternative). The Hessenberg-preservation theorems are
`IsUpperHessenberg.isUpperHessenberg_shiftedQRStep` (and `…_multiShiftedQRStep`, `…_shqrIterate`)
rather than `IsUpperHessenberg.shiftedQRStep`: inside the namespace the short name would shadow
the definition in every later `IsUpperHessenberg.*` statement (found by the first build). The
extraction-based name check (N1–N18) was not run. `shqrShift` is `open Classical in` with `if h : ∃ … then
h.choose` (review item 2; the first draft's `List.find?` with `@decide` drew an S3 warning).

Expected sizes: ShiftedQR ≈ 600 lines, EigenvectorWeights ≈ 200, Ritz ≈ 450, Strategy ≈ 700
(split `ExceptionalShifts.lean` off if E1 + grid exceed 350; amendment then), Dichotomy ≈ 350.

## 7. Material

Reused: Givens QR (`givensHessenbergState`, `isQR_givensHessenberg`,
`forall_givensHessenbergR_apply_self_ne_zero_iff`, `givensCoeffs_snd_zero`), `IsQR`,
`IsUpperHessenberg.isUpperTriangular_mul`, the implicit Q theorem (not needed: Q3 is direct),
`pseudoConditionNumber_of_isUnit`, `isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose`,
Mathlib's Cayley–Hamilton (`Matrix.aeval_self_charpoly`), `Polynomial.prod_multiset_X_sub_C_of_
monic_of_roots_card_eq`, weighted means (`Real.inner_le_nnorm_mul_nnorm`,
`Real.geom_mean_le_arith_mean_weighted`, `ConvexOn.map_sum_le`). Not reproduced: the
triangular-lattice net count of Armentano et al. (2018, Lemma 2.6), which the paper adapts (the grid is simpler, OQ7); the
arithmetic-operation counts; the "opportunistic" variant of Find (Remark 4.8).

## 8. Mathlib and NLAlib search (pinned v4.33.1)

Hessenberg QR iteration, shifted QR: Mathlib none; NLAlib `IsQR.mul_add_smul_one_eq` (one shifted
step, abstract), `IsQR.isUpperHessenberg_mul`, Givens QR (used). Potential / last row of
$p(\mathbf{H})$: none (searched `Hessenberg`, `aeval` + `last`). Eigenvector condition number:
none as a definition; Bauer–Fike uses `pseudoConditionNumber V` (followed). Spectral measure of a
nonnormal matrix: none (`SpectralMeasure.lean` is Hermitian). Paley–Zygmund: NLAlib measure form
(ForMathlib), no finite form (W1). Nets of a disk: none. Ritz values: none (Krylov has Hermitian
Ritz values via Lanczos; not reused). Polynomial of a diagonalised matrix: searched `aeval_diagonal`, `diagonal_aeval`, none; F1 proves it
from `Polynomial.aeval_algEquiv` (conjugation by $\mathbf{V}$).

## 9. Stage 2 (SQR-2): Part II in finite precision (plan, sizes, model)

Not skeletonised here (OQ1): its machine interface depends on HDIAG's `FloatMachine` (on
`feat/hdiag`, not yet on main) and on COMPDYN S2 (`bindIdx`, recursion), both in flight. The
plan below fixes the statements, the model options and the sizes.

### 9.1 Arithmetic model (OQ4)

Part II's model is Higham's: $+, -, \times, /, \sqrt{}$ with relative error $u$, no
under/overflow; random perturbations exact; $\psi_k^k$ exact; $k$-th roots by an unspecified
routine (Lemma 2.1); $\mathsf{SmallEig}$ a randomized black box (Definition 1.2). Options:

* **(a) Machine interface (recommended first).** Extend HDIAG's `FloatMachine` with a rounded
  `sqrt` and complex scalars as pairs (as `EntrywiseRounding.lean`); a disk sampler contract
  `IsDiskSampler` (coupling of an ideal uniform sample on $\mathbb{D}(0,1)$, with floor, as
  `IsUnifSampler`); a small-eigensolver contract `IsSmallEigSolver β φ` (a map of an ideal
  sample whose failure set has probability $\le \varphi$). The degree-1 step `iqrStep` is
  *implemented* by Givens over the machine (two loops, as Part II's box), and its backward
  contract (Definition 3.4, both inequalities) is a theorem (Lemma 3.5) — so downstream lemmas
  use only the contract and a black-box `iqr` kernel is a drop-in. $\psi^k$ is computed (one
  product, $(1\pm u)^{k}$ absorbed), $\tilde\psi = (\psi^k)^{1/k}$ by Newton over the machine
  (Lemma 2.1 as a theorem with its constants). All algorithm definitions generic over the
  machine (no exact arithmetic on stored values), computable.
* (b) `iqr` and $k$-th roots as black-box kernel contracts only (KernelContracts style). Less
  work, but leaves Lemma 3.5, the heart of Part II's backward analysis, as an assumption.
* (c) **Genuine `Prog`s** (the end goal): after COMPDYN S2 (data-dependent sizes for deflation
  blocks, recursion over the deflation tree, `kcall` for $\mathsf{SmallEig}$), a registered
  `shqrProg` refining (a) by equality, as COMPDYN S1c/S1d did for HDIAG's SIGN and DEFLATE.
  Recommended as the follow-up of (a), not instead of it: the analysis needs (a)'s shallow
  definitions anyway.

### 9.2 Statement plan (ids II-*, Part II numbering)

| group | statements | diff |
|---|---|---|
| machine (W5) | complex entrywise rounding with sqrt (2×2 Givens apply: error $8u\|y\|$, Part II §2) ×3; disk sampler and small-eig contracts, exact witnesses ×2; $k$-th root by Newton (Lemma 2.1) | S×3, M×2, L |
| iqr (W6) | composition with positive diagonal and $R_{nn}$ (Lemmas 3.2, 3.3) ×2; single-step backward stability (Lemma 3.5, both inequalities, $\nu = 32n^{3/2}$) ; multi-step backward (Lemma 3.6); QR perturbation (Lemma 3.7, Sun 1991) ; forward error (Lemma 3.8, with G8 fixed); comptau (Lemma 3.9, G9) | M×2, L, L, H, L, M |
| regularization (W6) | uniform disk law, area of a disk intersection; Lemma 3.10 (shift regularization) | M, M |
| Ritz (W7) | Optimal (Lemma 4.5); Regularize (Lemma 4.6, with G10/G11 constants), its failure probability | M, L, M |
| one step (W8) | potential approximation (Lemma 5.2, G12); Find in floating point (Lemma 5.1); Exc with randomized translate (Lemma 5.3, G13: covering budget, 7 points per eigenvalue) ; Sh (Lemma 5.4) | S, M, L, L |
| full algorithm (W9) | Bauer–Fike gap (Lemma 6.1a); eigenvector perturbation (BGKS20 Prop 1.1) ; $\kappa_V$ perturbation (Lemma 6.1b); $\kappa_V$ and gap of a diagonal block (Lemma 6.2, G15) ; deflate and its backward error ; the while loop (Lemma 6.4) ; backward error of $\mathsf{ShiftedQR}$ (Theorem 6.3) ; failure probability by the adaptive union bound (HDIAG UB1) ; node independence/measurability (as HDIAG EV3–EV5) ×3 ; precision in bits (Theorem 1.4) ; Hermitian corollary (Remark 1.7) | M, H, M, M, S, L, H, L, M/H×3, L, M |
| program (W10, optional) | `shqrProg` refinement (option c) ×4 | L, H |

About 60 statements: S ≈ 12, M ≈ 25, L ≈ 16, H ≈ 6, i.e. HDIAG-sized. The H items: QR
perturbation (needs Cholesky perturbation or Sun's argument), eigenvector perturbation under
distinct eigenvalues, the global backward-error assembly (block embedding of the deflation tree),
independence of the adaptively chosen random shifts. Prerequisites: `FloatMachine` and UB1 on
main (feat/hdiag), and for W10 COMPDYN S2.

## 10. Paper gaps and errors (checked by hand; statement-changing ones in bold)

Part I:

* **G1 (Theorem 3.3, normal case).** With $\varepsilon = (1-\gamma)^2/\sqrt{27}$ (Line 3 of
  $\mathsf{Sh}_{2,1}$) the proof gives $\tau_{(z-s)^2} \le 27^{1/4}\sqrt\varepsilon\,\psi/(1-\gamma)
  = \psi$: no reduction. It needs $\varepsilon = (1-\gamma)^4/\sqrt{27}$, so
  $\lvert\mathcal{S}\rvert \le 12\cdot27/(1-\gamma)^8$ ($\approx 1931$ at $\gamma = 0.2$, not
  $792$); also "$(1-t)^2(1-\gamma)^2$" for $(1-\gamma)^4$ in the choice of $s$, and the packing
  count omits the boundary layer ($(R + \varepsilon/2)^2/(\varepsilon/2)^2$). Theorem 1.2's
  "$792 T_{\mathsf{iqr}}$" inherits this. Here: N1 through the general strategy.
* **G2 (Theorems 1.2, 1.6(1)).** $\mathrm{dec}_\delta \le 4\log_2(1/\delta)$ is false for $\delta$
  near $1$: the cyclic shift (unitary, $\kappa_V = 1$, all subdiagonals $= \|\mathbf{H}\|$) at
  $\delta = 0.9$ needs a step while $4\log_2(1/0.9) < 1$. Correct: $\lceil\log(1/\delta)/
  \log(1/(1-\gamma))\rceil$ (M3).
* G3 (Definition 2.2) $k+1$ factors printed; and in the proof of Lemma 2.5 "$p(\widehat{\mathbf{H}}
  )_{1,k+1}$" for the entry $(n, n-k)$.
* **G4 (Lemma 2.5, singular case).** "For any QR decomposition $R_{n,n} = 0$" needs $\mathbf{H}$
  unreduced and a rank argument; "$\psi_k(\widehat{\mathbf{H}}) = 0$" needs $\widehat{\mathbf{H}}$
  Hessenberg, which an arbitrary unitary factor does not give. Fixed by Q7–Q9 (Givens step;
  conclusion "reduced").
* G5 (Lemma 4.5 proof) two displays lack squares ($j = 1$ left side; last line of the induction);
  the constant $\kappa^{4\log k}$ is right.
* G6 (Lemma 4.7 statement) exponent $(8\log k + 4)/k$ should be $/(k-1)$ (as in Theorem 1.6 and
  the proof); Exc's line 3 "$\varepsilon R$-net of $R\psi(H)$" doubles $\psi$; the first display
  of the proof writes $\mathbb{P}[\lvert Z - r\rvert \le D(r, R)]$.
* G7 (Lemma 4.2) "any complex function $f$" — $f(\mathbf{H})$ is $\mathbf{V}f(\mathbf{D})
  \mathbf{V}^{-1}$, dependent on $\mathbf{V}$ beyond polynomials and their inverses; harmless
  (only those are used).

Part II:

* G8 (Lemma 3.8) the hypothesis $u \le u_{\mathsf{iqr}}$ lacks the factor $(2 + 2C)^{-k}$ needed
  for $\|\mathbf{E}\|\|p(\mathbf{H})^{-1}\| \le \tfrac12$; the $\widehat{\mathbf{H}}$ bound omits
  the backward term $1.4k(1+C)\|\mathbf{H}\|\nu u$; $\|\mathbf{E}\| \le 2(\cdot)^k$ vs Lemma 3.6's
  $4(\cdot)^k$.
* G9 (Lemma 3.9) the precision requirement needs $\kappa_V^2$ and $24000$, not $\kappa_V$ and
  $6000$.
* **G10 (Theorem 4.1).** The last display drops the $2$ in $\psi/(2\kappa^{1/k}(\|\mathbf{H}\|+
  \beta))$ and uses $(2k)^{-1/(2k)}$ for $k^{-1/(2k)}$; the true constant is $\tfrac12k^{-1/(2k)}
  \ge 0.416$, not $\tfrac12$. In Regularize (Lemma 4.6) "$\ge 2/\varepsilon$" becomes
  $\ge 1.66/\varepsilon$, so $\tau \le 0.6\varepsilon$ and the decoupling test with forward error
  $\varepsilon/2$ reaches $1.1\varepsilon$, not $\varepsilon$; fix by $\beta \leftarrow \beta/1.25$.
  G10b: with $\beta = c\,\mathrm{gap}$ two eigenvalues can be at distance exactly $\beta/(2c)$ of
  one Ritz value; strict inequality restores "at most one".
* G11 (Lemma 4.6 proof) "$\psi_k(\mathbf{H}) \le \varepsilon$" should be $\ge$
  ($\varepsilon$-unreduced).
* G12 (Lemma 5.2 proof) the product runs over all $n-1$ subdiagonals; it must be the last $k$
  (else $1.001^{(n-1)/k}$).
* G13 (Lemma 5.3, Exc) (i) rounding budget $0.1\varepsilon\widetilde R$ plus net spacing
  $0.99\varepsilon\widetilde R$ exceeds the covering radius $\varepsilon\widetilde R$; (ii)
  intersecting with $\mathbb{D}(r, \widetilde R)$ can drop the only points covering the boundary;
  (iii) "each eigenvalue is within $\varepsilon\widetilde R$ of at most three net points" — a
  $0.99\varepsilon\widetilde R$-separated set has up to $7$; (iv) (5.3) writes $1.998$, $B$ for
  $1.998^{1/k}$, $B^{1/k}$.
* G14 (Sh in floating point) line 4 outputs $\mathsf{exactqr}$ for $\mathsf{iqr}$; the Exc call
  uses $0.999(1-\gamma)$ where the proof derives $0.999^{1/k}(1-\gamma)$ (harmless).
* G15 (Lemma 6.2) "every $\mathbf{V}$ diagonalising $\mathbf{M}$ is block triangular" is false
  when the diagonal blocks share an eigenvalue; true under distinct eigenvalues, which Part II
  assumes.
* G16 (Appendix, Lemma 3.6) the step $((1 + 2\nu u)^m - 1) \le (3/2)^m\nu u/4$ is false ($m=1$);
  the final bound $4(2(1+C)\|\mathbf{H}\|)^m\nu u$ holds by convexity on $[0, 1/4]$; a factor
  $\nu u$ is missing in the product display.
* G17 (Part II Lemma 2.5, restating Part I Lemma 4.6) writes $(1 + \theta)$ for $\theta$ and
  "$\gamma, \theta \in (0,1)$" for $\theta \ge 1$.

## 11. Deferred, with what each needs

* Arithmetic-operation counts of Part I (Theorems 1.2, 1.6(2) in operations): stage 2's
  algorithm and a cost semantics (COMPDYN, option (c)).
* Smoothed analysis (Remark 1.8): pseudospectral regularization by Gaussian perturbation
  Banks–Garza-Vargas–Kulkarni–Srivastava 2020 (pseudospectral shattering; in the bibliography of `feat/hdiag`); with HDIAG's complex Gaussian law.
* The annulus refinement and lattice nets (Remarks 3.5, Lemma 4.7's lattice count): constants only.
* Opportunistic Find (Remark 4.8).
* A Ritz-value finder with guarantees (Part III): replaces the oracle hypothesis of M3.

## 12. Open questions (recommendations in bold; the decision sheet has them one line each)

1. **Stage split** — (a) **SQR-1 = Part I + Part II's exact dichotomy (50 targets) now; SQR-2 =
   Part II in floating point (≈ 60) designed in a second pass once `FloatMachine` is on main**;
   (b) Part I only (48), the dichotomy into SQR-2; (c) one stage I + II (≈ 110). (a): balanced,
   front-loads the exact mathematics, and the stage-2 model depends on work in flight.
2. **Exact iteration vs the model of computation** — (a) **noncomputable specification
   definitions (`Algorithm: shifted-qr (specification)`), no cost claims, refined by stage 2**;
   (b) purely relational statements (∀ sequences with a step relation) and no iteration
   definition; (c) write Part I over HDIAG's machine at $u = 0$ now. (a): one named sequence for
   the theorem, honest labelling, and the same `shiftedQRStep` stage 2 compares with.
3. **Headline strategy** — (a) **general $\mathsf{Sh}_{k,B}$, $k = 2^m$ arbitrary (M3), normal case
   as corollary N1, parameter instance M5**; (b) the greedy Wilkinson $\mathsf{Sh}_{2,1}$ for
   normal matrices as a separate headline (Theorem 3.3, with G1 fixed; +4 targets); (c) fix $k$
   by Part II's (2.3) as the headline instance. (a): one strategy, all $k$; (b) is a different
   strategy (quadratic shift, argmax over two Ritz values) whose printed constant is wrong.
4. **Part II arithmetic model** — (a) **`FloatMachine` extended (sqrt, complex pairs, disk sampler,
   small-eig contract), `iqr` implemented by Givens over it with Definition 3.4 proved (Lemma
   3.5)**, then (c) genuine `Prog`s after COMPDYN S2; (b) `iqr` and roots as black-box contracts
   only. (a) keeps Part II's main backward analysis a theorem; (c) is the end goal.
5. **Folder** — (a) **new `NLAlib/Matrix/QRIteration/`** (stage 2 adds `Matrix/Computation/`
   and `Eigensolvers/` files); (b) `Matrix/Factorizations/` next to Hessenberg; (c)
   `Eigensolvers/ShiftedQR/` for everything (layer 3, not on main). (a): deterministic,
   Matrix layer, findable.
6. **Ritz value equal to an eigenvalue** — (a) **an explicit first clause in `shqrShift`
   (exact decoupling, Q9)**; (b) prepend all Ritz values to the candidates (k extra steps); (c)
   a hypothesis excluding it. (a) matches the paper's "ignore" at no cost.
7. **The net** — (a) **explicit square grid, $\le 12/\varepsilon^2$ points, constant 14**; (b)
   triangular lattice with the paper's count (Armentano et al.); (c) an abstract
   $\varepsilon R$-net hypothesis. (a) is computable, simple, costs a constant factor.
8. **$Z_H$** — (a) **finite weighted sums of `lastRowWeights`**; (b) a discrete probability
   measure on $\mathbb{C}$ and integrals (reuses measure PZ). (a): no measure theory in matrix
   files; one ForMathlib lemma.
9. **$\kappa_V$** — (a) **hypotheses `IsUnit V`, `H * V = V * diagonal d`, `pseudoConditionNumber V
   ≤ B` (library convention)**; (b) a definition $\kappa_V(\mathbf{H}) = \inf$ with attainment.
   (a): every proof uses one fixed $\mathbf{V}$; the infimum adds API for nothing.
10. **Part III** — (a) **not needed: Ritz finder and small eigensolver stay oracles/contracts**;
    (b) fetch and design Part III (its own stage). (a): no proof of I or II uses it.

## 13. Proof plan and dependency graph

Waves (longest dependency chain, from the targets file): wave 0: Q0, P1, P2a, P2b, P5, Q4, Q5, F1, F2b, F6, W1, F5a, F5, F3, F4, R1a, R2, R5a, S2, S3, S4, M5 (22); wave 1: P3, P4, P6, Q1, Q8, F2, R3, M2b, M2c, M4, D1 (11); wave 2: Q1b, Q3, Q8b, Q7, R1b, L1, S1, D2 (8); wave 3: Q6, Q9, R5, E1, M2a (5); wave 4: R4, M1 (2); wave 5: M3 (1); wave 6: N1 (1).

Chains: Q0 → Q1 → {Q1b, Q3} → Q6 → {R4, M1}; Q0 → Q8 → {Q7, Q8b} → Q9 → M1; P1/P2a/P2b → P4 →
{R1b, D2}; F1–F5a → {R3, L1, S1, E1}; W1 → S1 → E1 → M1 → M3 → N1; L1 → R5 → M1; D1 → D2.
Model tiers: S and M on haiku with sonnet escalation, L on opus from the start
(`--hard L`). Review applied (Fable, `~/nlalib-harness/reports/Review-Fable-ShiftedQR-Design.md`, approve
with changes): items 1–3 (R3 cites F3, `shqrShift` restructured, M3's oracle needs $\psi_k > 0$),
labels Q7, P4, M3, M5, D2 → L, and nits 5–7, 9. Suggested dispatch: SQR-1a = waves 0–2 (41 targets, including D1, D2) then SQR-1b = waves 3–6
(Q6, Q9, R5, E1, M2a, R4, M1, M3, N1; 9 targets) after a Fable outline check of E1, M1, D1, D2.

## 14. Literature

[BanksGarzaVargasSrivastava2021] (read in full, numbering of the 2023-10-16 source);
[BanksGarzaVargasSrivastava2022] (read in full, v1); Part III (not read, not needed);
[GolubVanLoan2013, §5.2.5, §7.5] (Givens QR, shifted QR step); [TrefethenBau1997, Theorem 34.1]
(variational characterisation of Ritz values); [HornJohnson2013, Theorem 2.5.3] (normal matrices);
[PaleyZygmund1932, Lemma 19]; Banks–Garza-Vargas–Kulkarni–Srivastava 2020 (pseudospectral shattering; in the bibliography of `feat/hdiag`) (smoothed analysis,
deferred). New bibliography entries: the two Banks–Garza-Vargas–Srivastava papers.

## 15. Checks run on the skeleton

On this branch, `LEAN_NUM_THREADS=2`: `lake build NLAlib NLAlibScaffold` (full, 4282 jobs)
succeeds with exactly 50 `declaration uses 'sorry'` warnings and nothing else; `lake build
--wfail` of the four new `NLAlib/Matrix/QRIteration/` modules succeeds; `lake exe mk_all --module
--lib NLAlib --check` and `… --lib NLAlibScaffold --check` are clean; `scripts/check_rules.py
--files` on every touched file: 0 errors, 0 warnings; `check_refs.py`, `check_constants.py`, `check_latex.mjs`: 0 problems;
`bin/check-skeleton --strict`: 50 targets, 0 names missing an import, 0 unresolved. Not run:
`scripts/stage_check.sh` (the full suite; the machine was memory-bound by other jobs) and the
extraction-based name check (N1–N18).

## 16. End of stage (2026-11-07)

**Proved.** All 50 SQR-1 statements are proved and in `NLAlib`. The scaffold library is gone, and
`lakefile.toml` is main's again. `#print axioms` of M3, N1, D2, M1, E1, Q9, D1 and M5 gives
`propext`, `Classical.choice` and `Quot.sound` only. 41 statements were proved by haiku, Q8 by
opus after a haiku batch miss, and the eight L statements (D1, D2, E1, M1, M3, M5, P4, Q7) by
opus. The elaborated types of the 112 public constants are unchanged by the clean-up. No
statement was found false.

**Files.** Statements sit after the definitions in `Matrix/QRIteration/{ShiftedQR,
EigenvectorWeights, Ritz, Strategy}.lean`, in the new `Matrix/QRIteration/Dichotomy.lean` (D1,
D2) and `ForMathlib/Analysis/MeanInequalities.lean` (W1). Q0 is in
`Matrix/Factorizations/GivensHessenberg.lean`, and F1, F2, F2b, F6 are in
`Matrix/Spectral/Diagonalizable.lean`. Strategy stayed under 1000 lines, so no
`ExceptionalShifts.lean` split was needed (§6).

**Unused hypotheses**, kept until the maintainer decides (each proof references them with
`have _ := …`):
- D1 `sum_lastRowWeights_mul_norm_eval_sq_sub_le`: `hgap` and `hβc`. The proof is pointwise, so
  D1 holds without an eigenvalue gap.
- R3 `IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div`: `hα` (Fable's note 10).

**New public helpers** from the clean-up (14), which replace private copies:
`isUnit_aeval_of_forall_eval_ne_zero`, `inv_sub_smul_one_pow_eq_mul_diagonal_mul_inv`,
`det_sub_smul_one_eq_zero_of_mul_eq_mul_diagonal`, `det_sub_smul_one_ne_zero_of_forall_ne`,
`norm_le_specNorm_of_mul_eq_mul_diagonal` (Diagonalizable); `hessenbergPotential_nonneg`,
`shiftPoly_monic_and_natDegree`, `norm_eval_shiftPoly`, `eval_shiftPoly_ne_zero`,
`shiftPoly_append`, `aeval_shiftPoly_replicate`,
`IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_replicate_pow_mul_le` (ShiftedQR);
`shiftPoly_ritzValues`, `sum_lastRowWeights_div_pow_le` (Ritz).

**Model of computation.** As OQ2 decided: the `shqr*`, `shiftedQRStep` and `findRitz`
definitions are specifications with no `Prog` and no cost claim, so there is no registry entry.
SQR-2 proves the refinement (§9).
