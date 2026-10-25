# Design note: lower bounds for specific low-rank estimators (stage S10)

Status: approved by the maintainer (all OQs (a)), 2026-10-25, on `design/lb-estimators` (rebased
onto `origin/main` `59e1792`); revised after the Fable review
(`~/nlalib-harness/reports/Review-Fable-S10-Design.md`: E8 import and exact fourth moment, W6
pointwise limit through `HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom`, three outline
names, OQ9 bibliography, E7 without hypotheses on $\theta$, OQ8 lemmas public). Decision sheet: `~/nlalib-harness/state/decisions/S10.json`. Targets:
`~/nlalib-harness/pilot/s10-targets.json` (29 rows, outlines for every row).

S10 proves lower bounds **for fixed estimators** (sketch-and-solve, randomized SVD, Nyström,
generalized Nyström, early-truncated randomized SVD, truncated generalized Nyström) on explicit
hard instances. It does not use the matrix-vector query model and does not depend on stage LB-A
(`~/nlalib-design-lb-foundations`), as the maintainer decided (`MatvecLowerBounds.json`,
STAGE-FIRST (a)). The two stages touch no common file.

Sources: Epperly–Webber 2026 (arXiv:2605.19096v2, [EpperlyWebber2026]; statements re-read from the
arXiv HTML for this note) and two internal research notes of the workflow,
`~/nlalib-harness/reports/OP1-EarlyTruncatedRSVD.md` (OP1) and
`~/nlalib-harness/reports/OP2-TruncatedGN.md` (OP2). The OP1 and OP2 results are **new**: they have
no printed source, so their docstrings say "No printed source. New (research note …)" and carry no
"Source value". Correction applied (maintainer, 2026-10-25): OP2's remark that BWZ16 Lemma 51
rules out a $p = \Omega(k/\varepsilon^2)$ lower bound for sketch-only estimators is wrong (Lemma 51
is existence only; computing its $\mathbf{X}$ needs extra matvecs). Nothing here uses BWZ, and
nothing states or implies that $p = O(k/\varepsilon)$ suffices for truncated generalized Nyström;
that is Conjecture C1 of OP2, not a target (§5).

Skeleton: 29 sorried statements in 11 scaffold files; `lake build NLAlibScaffold` gives 29
`declaration uses sorry` warnings and nothing else. `check_rules.py --files` (70 rules; N1–N18 and
extraction rules skipped, no extraction of the scaffold), `check_refs.py`, `check_latex.mjs`
(KaTeX), `check_constants.py`: 0 problems. The dispatcher's `locate` finds all 29 targets, each
with a `sorry` body; no sorried declaration is untargeted. The deterministic statements T2, T3,
E1 and W1 were checked numerically on random instances (§8) before being stated.

## 0. Summary

| | |
|---|---|
| New definitions | none (instances are spelled inline or through a hypothesis `hA : A = …`) |
| New interfaces | none |
| New files | `LowRank/Optimality/{EarlyTruncation,TruncatedGeneralizedNystrom,RotationInvariant}.lean`, `ForMathlib/Probability/Moments/PaleyZygmund.lean` |
| Additions to existing files | 7 files (§6): ChiSquareMoments, Structural/Truncation, Gaussian/TruncatedGeneralizedNystrom, Pseudoinverse/NormBounds, Haar/Blocks, Regression/SketchAndSolve, Gaussian/RotationInvariantFactor |
| Statements | 29 sorried: S 14, M 10, L 3, H 2 |
| Novel (no printed source) | OP1: E1–E8; OP2: T1–T3, G1–G3, L1–L2 (16 statements) |
| Published (EW) | W1–W10 (EW Lemma 5.8, Prop. 5.7, Thm 2.2, Lemma 6.2, Thms 3.3, 3.6(b), 4.2(b)) |
| ForMathlib | PZ1 (Paley–Zygmund), not in Mathlib v4.33.1 (searched `paley`, `zygmund`) |
| Open questions | 9 (§9), each with a recommendation |

Headlines:

1. **Early-truncated RSVD needs $\Theta(k/\varepsilon^2)$ samples** (OP1). $k = 1$: on
   $\operatorname{diag}(1, 1 - \delta)$, $\delta = 1/(4\sqrt\ell)$, the expected error is at least
   $(1 + 1/(100\sqrt\ell))$ times optimal for $\ell \ge 100$ (E3), and $(1+\varepsilon)$ needs
   $\ell \ge 10^{-4}/\varepsilon^2$ (E5); "$O(k/\varepsilon)$ suffices" is refuted formally (E6).
   General $k$ (E8): excess $\ge c\sqrt{k/\ell}$ for $k \ge K_0$, existential constants.
2. **Truncated GN on EW's instance** (OP2). Exact identities (G1: noise in the dominant subspace
   costs exactly $k/(p-\ell-1)$; G2: oracle truncation), two new deterministic lemmas (T2:
   sharpened perturbed truncation with $\gamma_P$; T3: reverse perturbed truncation), and the lower
   bound $\liminf_{a\to\infty}$ excess $\ge k(n-\ell)/(p-\ell-1)$ (L1), so $(1+\varepsilon)$ needs
   $p - \ell - 1 \ge k(n-\ell)/((n-k)\varepsilon)$ (L2). Untruncated GN pays $\ell/(p-\ell-1)$ on
   the same instance: truncation gains $\ell/k$.
3. **EW's factors are sharp** for rotation-invariant test matrices (W6–W10, "type (i)"), and the
   sketch-and-solve minimax bound for **every** sketch law (W3–W5, "type (ii)").

## 1. Scope

In:

* EW Lemma 5.8 (W1), Proposition 5.7 for a general weight (W2), Theorem 2.2 in three forms (W3 a
  fixed sketch averaged over a Haar rotation of the problem; W4 one rotation; W5 any random sketch,
  in `lintegral`), Lemma 6.2 as a limit (W6), Theorems 3.6(b), 3.3, 4.2(b) for left unitarily
  invariant range laws (W7–W10; 4.2(b) with Gaussian and with Haar co-range).
* OP1: the $2 \times 2$ instance in full (E1–E6), and the general-$k$ block instance (E7–E8) for
  $k \ge K_0$ with existential constants.
* OP2: I2, I3 and the I3 upper bound (G1–G3), D2 sharpened (T2), the reverse perturbed truncation
  (T3, new here), "truncated GN never beats truncated RSVD" (T1), the lower bound on
  $\operatorname{diag}(a\mathbf{I}_k, \mathbf{I})$ (L1) and its co-range consequence (L2).
* Paley–Zygmund (PZ1) and the two moments of a difference of independent $\chi^2$ (X1, X2).

Deferred (§4): EW Theorems 3.3, 3.6(b), 4.2(b) for an arbitrary full-rank law (type (ii)); the
complex field; EW §4.2's "$k + \ell \ge (4/\varepsilon^2 + 2)q$" arithmetic over $\mathbb{R}$; the
general-$k$ OP1 bound for $2 \le k < K_0$; OP2's expectation corollary of D2 (constants
$8000 \to \approx 3000$); OP2 Conjecture C1.

## 2. Objects

No new definitions or predicates. Reused: `earlyTruncatedRSVD`, `truncatedSVD`, `rsvd`,
`generalizedNystrom`, `nystrom`, `obliqueProjector`, `rangeProjector`, `sketchAndSolve`, `pinv`,
`frobNorm`/`specNorm`/`nuclearNorm`, `singularValues` (ℕ-indexed), `gaussianMatrix`,
`gaussianVector`, `haarFrame`, `IsLeftUnitarilyInvariant`, `HasOrthonormalCols`, and the named
factors `gaussianProjectionFactor`, `haarProjectionFactor`, `rotationInvariantFactor` (value
markers in every docstring that uses them).

The core noise $\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{R})$ is written out as `obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)`, as the
existing perturbed-truncation lemmas do. The hard instances are inline:
`Matrix.diagonal ![1, s]`, `Matrix.fromBlocks 1 0 0 (s • 1)`,
`Matrix.fromBlocks (a • 1) 0 0 1`; where the expression would repeat inside a binder, the statement
takes `A` with `hA : A = …` (E7, E8). A `let` in a statement type is avoided: the dispatcher splits a
statement at its first top-level `:=`.

The oracle truncation $\llbracket\mathbf{R}\rrbracket_k + \mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}
\mathbf{N}$ (G2, G3) is an analysis device, not an estimator, and gets no name (OQ6).

## 3. Statements

IDs are the targets' `note_id`. Every statement was checked for degenerate parameters; the check is
recorded under each. Full docstrings and `Proof:` lines are in the skeleton; outlines in the targets
JSON.

### 3.1 OP1: early-truncated RSVD (`LowRank/Optimality/EarlyTruncation.lean`, new)

Instance $\mathbf{A} = \operatorname{diag}(1, s)$, $s = 1 - \delta$, $\delta = 1/(4\sqrt\ell)$;
$\mathbf{\Omega}$ standard Gaussian $2 \times \ell$ with rows $\omega_1, \omega_2$.

* **E1** (M, deterministic) `add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq`: for
  $0 \le s \le 1$ and $\|\omega_1\|^2 < s^2\|\omega_2\|^2$, the error is $\ge s^2 + (1-s^2)/2$.
  *Proof.* With $\mathbf{P}$ the rank-$\le 1$ range projector of
  $\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_1$, $p_i = \mathbf{P}_{ii}$: error
  $= 1 + s^2 - p_1 - s^2p_2 \ge 1 - (1-s^2)p_1$. The swapped projector
  $\mathbf{S}\mathbf{P}\mathbf{S}$ competes (Eckart–Young), and
  $\operatorname{tr}((\mathbf{S}\mathbf{P}\mathbf{S} - \mathbf{P})\mathbf{Y}\mathbf{Y}^{\mathsf{T}})
  = (b-a)(p_1 - p_2)$, so $a < b$ forces $p_1 \le p_2$, $p_1 \le 1/2$. This replaces OP1's
  $2\times 2$ eigenvector formula (no eigenvectors needed) and holds for the choice `truncatedSVD`
  makes. *Degenerate:* $\mathbf{Y} = 0$ is excluded by $a < b$ only if $b > 0$; with
  $\mathbf{Y} = 0$, $\mathbf{P} = 0$ and the error is $1 + s^2$, still $\ge$; $s = 1$ gives $a < b$
  with bound $1 = $ OPT, true.
* **E2** (M) `le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix`: for $\ell \ge 100$,
  $\mathbb{P}[\|\omega_1\|^2 < s^2\|\omega_2\|^2] \ge 1/12$. *Proof* (OP1 §1): Paley–Zygmund on
  $Z = X^2$, $X = \|\omega_1\|^2 - \|\omega_2\|^2$, $\theta = 1/4$, with $\mathbb{E}Z = 4\ell$,
  $\mathbb{E}Z^2 = 48\ell^2 + 96\ell$ (X1, X2) gives $\mathbb{P}[X^2 > \ell] \ge 9\ell/(48\ell+96)$;
  symmetry of $X$ halves it: $\mathbb{P}[X \le -\sqrt\ell] \ge 0.0919$ at $\ell \ge 100$. On
  $\{X \le -\sqrt\ell\} \cap \{\|\omega_2\|^2 < 2\ell\}$ the event holds since
  $(1 - s^2)\cdot 2\ell < 2\delta\cdot 2\ell = \sqrt\ell$. The library's chi-square upper tail at
  $\beta = 2$ bounds the complement by $e^{-0.153\ell} \le e^{-15}$. Constants: OP1's
  "$0.087 - e^{-\ell/8}$ for $\ell \ge 25$" gives only $\approx 0.063$ at $\ell = 25$ and its final
  "$0.02/\sqrt\ell$" holds only asymptotically; the statement uses $\ell \ge 100$ and $1/12$ (true
  margin: $0.0919 - 10^{-6}$ vs $0.0833$) (OQ2).
* **E3** (M) `le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix`:
  $(1 + 1/(100\sqrt\ell))\,\mathrm{OPT}^2 \le \mathbb{E}\,\mathrm{err}$ for $\ell \ge 100$.
  *Proof:* err $\ge s^2$ always, $\ge s^2 + (1-s^2)/2$ on E2's event; integrate:
  excess $\ge (1-s^2)/24 \ge 1.97\delta/24 = 0.0205/\sqrt\ell \ge s^2/(100\sqrt\ell)$. Result id
  `early-truncated-rsvd-lower-bound`.
* **E4** (S) the probability form: for $16\varepsilon^2\ell < 1$,
  $\mathbb{P}[\mathrm{err} > (1+\varepsilon)\mathrm{OPT}^2] \ge 1/12$ (on E2's event
  err $\ge (1+\delta)s^2$ and $\delta > \varepsilon$). *Degenerate:* $\varepsilon \le 0$ is
  allowed and trivially covered.
* **E5** (S) `one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le`: if
  $(1+\varepsilon)$ in expectation holds for all $2 \times 2$ matrices at $\ell \ge 100$, then
  $1 \le 10^4\varepsilon^2\ell$.
* **E6** (S) `not_exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`:
  the negation of the $\varepsilon^{-1}$ twin of the library's
  `exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix` (same
  binder shape, `C * (k / ε) ≤ card l`). *Proof:* $k = 1$, $\Omega = $ the Gaussian matrix space,
  $\ell = \lceil\max(C/\varepsilon, 100)\rceil$ with $\varepsilon$ small, then E5.

General $k$, instance $\operatorname{diag}(\mathbf{I}_k, s\mathbf{I}_k)$,
$\delta = \sqrt{k/\ell}/4$, $T = \operatorname{tr}\mathbf{P}_{22}$ the tail content of the
sketch's dominant frame:

* **E7** (M, deterministic) `frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational`:
  error $\ge ks^2 + (1-s^2)T$, and OP1 §4 steps 1–3:
  $T(s^2\|\mathbf{\Omega}_2\|_2^2 - \sigma_{k-1}(\mathbf{\Omega}_1)^2) +
  2s\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2\sqrt{kT} \ge
  2s\sin\theta\cos\theta\,\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_* -
  \sin^2\theta(\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 - s^2\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2)$
  for $\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \ge k$ and every $\theta$. I checked
  each step of OP1's derivation (the expansion of $f(\mathbf{U})$, $\operatorname{tr}(\mathbf{I} -
  \mathbf{U}_h\mathbf{U}_h^{\mathsf{T}}) = T$, the competitor and Ky Fan maximality). Two
  condition OP1 leaves implicit is a hypothesis: $s \ge 0$ (cross term). No condition on $\theta$
  is needed: with $\mathbf{R}$ the polar factor the competitor's value is an identity for every
  $\theta$ (Fable review; the draft's $0 \le \theta \le \pi/2$ was dropped, which strengthens the
  statement). *Degenerate:* $k = 0$ gives $0 \le 0$.
* **E8** (H) `exists_forall_le_integral_frobNorm_sub_earlyTruncatedRSVD_sq_of_hasLaw_gaussianMatrix`:
  $\exists\, c, C > 0, K_0$: for $k \ge K_0$, $\ell \ge Ck$,
  $(1 + c\sqrt{k/\ell})\mathrm{OPT}^2 \le \mathbb{E}\,\mathrm{err}$. **Why $k \ge K_0$:** OP1 §4
  step 4 claims all concentration events with probability $1 - O(e^{-t^2/2})$, but at small $k$
  the trace difference $\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 - \|\mathbf{\Omega}_2\|_{\mathsf{F}}^2$
  fluctuates by $\Theta(\sqrt{k\ell})$ against a signal $\Theta(k\sqrt{k\ell})$, and
  $\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_*$ is not concentrated (for $k = 1$ it is
  $|\omega_1\cdot\omega_2|$). For large $k$ every event holds with probability $1 - O(1/k)$ by
  Chebyshev, and the arithmetic closes (recomputed: right side $\ge 0.16k\sqrt{k\ell}$, left side
  $\le \sqrt{k\ell}(5T + 4.4\sqrt{kT})$, so $T \ge 10^{-4}k$, $c = 10^{-4}/8$). The statement is
  true as stated (proof complete at that level); for $2 \le k < K_0$ it is expected (numerics,
  OP1 §2(b)) but unproved (OQ3). One caveat for the prover: the variance of
  $\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_{\mathsf{F}}^2$ must be computed exactly
  ($2k^2\ell^2 + O(k^3\ell)$); the library's bound
  `integral_frobNorm_mul_mul_pow_four_le_of_hasLaw_gaussianMatrix` gives only
  $\mathrm{Var} \le 2\,\mathrm{mean}^2$, useless for Chebyshev. The outline uses the exact
  `integral_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix` conditionally on
  $\mathbf{\Omega}_2$ ($\mathbf{A} = \mathbf{I}$, $\mathbf{B} = \mathbf{\Omega}_2^{\mathsf{T}}$:
  conditional variance $2k\|\mathbf{\Omega}_2\mathbf{\Omega}_2^{\mathsf{T}}\|_{\mathsf{F}}^2$)
  plus $\mathrm{Var}(k\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2) = 2k^3\ell$.

### 3.2 OP2: truncated generalized Nyström

Notation: $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, $\mathbf{N}$ the core noise,
$\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}$ = `rangeProjector (truncatedSVD (rsvd A Ω) k)`.
Deterministic statements are over `RCLike 𝕜` with the rank condition of the existing perturbed
truncation lemma; Gaussian ones are real.

`LowRank/Structural/Truncation.lean` (additions):

* **T1** (S) truncated GN never beats truncated RSVD:
  $\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 \le
  \|\mathbf{A} - \llbracket\mathsf{gn}\rrbracket_k\|_{\mathsf{F}}^2$ (core form + Eckart–Young).
  Needed by L1; new as a stated lemma, elementary.
* **T2** (M) `frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm_mul_frobNorm`
  (OP2 D1–D2): error $\le \|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|^2 +
  4\sqrt k\|\mathbf{N}\|_2\gamma_k + 12k\|\mathbf{N}\|_2^2$ with
  $\gamma_k = \|\llbracket\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}$
  (the next $k$ singular values only; $\le \min(\gamma, \sqrt k\sigma_k(\mathbf{R}))$, so it covers
  OP2's three-way minimum). **Constants recomputed:** OP2 states $8\sqrt k e\gamma_P + 11ke^2$ via
  "$3w$"; solving the quadratic directly gives $4\sqrt k e\gamma_P + (6 + 4\sqrt2)ke^2$, so the
  statement uses $4$ and $12$ (true with margin; the cross term halves, the noise term grows from
  OP2's $11$; the library's lemma has $4\sqrt{2k}\gamma e + 8ke^2$). Numerically: 20 000 random
  instances, minimum slack $\ge 0$ up to rounding (§8). *Degenerate:* $k = 0$: both sides
  $\|\mathbf{A}\|^2$.
* **T3** (M) `le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq` (new, this design): for
  $k \ge 1$ and a gap $g = \sigma_{k-1}(\mathbf{R})^2 - \sigma_k(\mathbf{R})^2 > 0$,
  $\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|^2 + \|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}
  \mathbf{N}\|_{\mathsf{F}}^2 - \|\mathbf{N}\|_{\mathsf{F}}^4/g \le$ error. *Proof:*
  $x \ge g\,t$ with $t = \sum_{i<k}(1 - \mathbf{u}_i^{\mathsf{H}}\mathbf{P}\mathbf{u}_i)$,
  $\|\mathbf{P} - \mathbf{P}_B\|_{\mathsf{F}}^2 \le 2t$, and
  $|\|\mathbf{P}\mathbf{E}\|^2 - \|\mathbf{P}_B\mathbf{E}\|^2| \le \sqrt{2t}\|\mathbf{E}\|_{\mathsf{F}}^2$;
  minimise over $t$ (gives $1/(2g)$; stated with $1/g$). This is what makes OP2's "routine
  $a \to \infty$ limit" a proof: it controls the misalignment $\mathbf{P} \ne \mathbf{P}_B$
  without Davis–Kahan.

`LowRank/Gaussian/TruncatedGeneralizedNystrom.lean` (additions; Gaussian $\mathbf{\Omega}$,
$\mathbf{\Psi}$ independent):

* **G1** (M) I2: $\mathbb{E}\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2
  = \tfrac{k}{p-\ell-1}\mathbb{E}\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2$ for $k \le \ell$,
  $\ell + 2 \le p$. *Degenerate:* $\operatorname{rank}\mathbf{A} < \ell$: $\mathbf{R} = \mathbf{A}$
  a.s., both sides $0$; otherwise $\operatorname{rank}\mathbf{R} = \ell \ge k$ a.s. so the projector
  has rank exactly $k$; $k = 0$: both $0$. ($k > \ell$ would need $\min(k,\ell)$; excluded.)
* **G2** (S) I3, the oracle truncation, exactly: expectation $=
  \mathbb{E}\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|^2 + \tfrac{k}{p-\ell-1}\mathbb{E}\|\mathbf{A}
  - \mathbf{R}\|^2$ (cross term vanishes by the reflection symmetry of $\mathbf{\Psi}$).
* **G3** (S) its bound $\le (1 + \tfrac{k}{\ell-k-1})(1 + \tfrac{k}{p-\ell-1})\mathrm{OPT}_k^2$.
  Worded as a statement about an analysis device: the dominant subspace of $\mathbf{R}$ is not
  computable from the sketches, so G3 says nothing about what a sketch-only estimator achieves.

`LowRank/Optimality/TruncatedGeneralizedNystrom.lean` (new), instance
$\mathbf{A}_a = \operatorname{diag}(a\mathbf{I}_k, \mathbf{I}_{n-k})$ on `s ⊕ t`, $k = |s|$:

* **L1** (H) `eventually_le_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq`:
  for $k + 2 \le \ell$, $\ell + 2 \le p$ and every $\eta > 0$, eventually in $a$,
  $|t| + k(n-\ell)/(p-\ell-1) - \eta \le \mathbb{E}\,\mathrm{err}_a$. Result id
  `truncated-gn-lower-bound`. *Proof:* T1 and T3 pointwise; G1 and
  $\|\mathbf{A}_a - \mathbf{R}_a\|^2 \ge n - \ell$ in expectation; the defect
  $\min(\|\mathbf{P}\mathbf{N}_a\|^2, \|\mathbf{N}_a\|^4/g_a)$ tends to $0$ in expectation because
  (i) HMT's deterministic bound gives an $a$-free envelope $\|\mathbf{A}_a - \mathbf{R}_a\|_{\mathsf{F}}^2
  \le D^2 = |t| + \|\mathbf{\Omega}_2\mathbf{\Omega}_1^{+}\|_{\mathsf{F}}^2$, integrable for
  $k + 2 \le \ell$, (ii) Weyl gives $g_a \ge a^2/8$ on $\{D \le a/2\}$, (iii) conditionally on
  $\mathbf{\Omega}$ the noise is dominated by $\|\mathbf{G}_1^{+}\|_2\|\mathbf{G}_2\|_2 D$ with
  $(\mathbf{G}_1, \mathbf{G}_2)$ of a fixed law, integrable for $\ell + 2 \le p$; dominated
  convergence. OP2 stated L1 as a $\liminf$ "proven modulo a routine $a \to \infty$ limit"; the
  limit is not routine in Lean, and this route (T3 instead of "$\mathbf{P} \to \mathbf{P}_B$") is
  the design's. *Degenerate:* $n \le \ell$: $\mathbf{R} = \mathbf{A}$, the bound is below $|t|$;
  $k = 0$: trivial. The hypotheses $k + 2 \le \ell$, $\ell + 2 \le p$ are what the proof needs
  (integrability of $D^2$ and of $\|\mathbf{G}_1^{+}\|^2$), not what the truth needs (OQ5).
* **L2** (S): if $(1+\varepsilon)$ holds on every $\mathbf{A}_a$, $a \ge 1$, then
  $k(n-\ell) \le \varepsilon(p-\ell-1)|t|$. *Degenerate:* $|t| = 0$ forces $k(k-\ell) \le 0$, true;
  negative $\varepsilon$ is excluded by the hypothesis itself when $|t| > 0$.

### 3.3 Epperly–Webber

* **W1** (M) Lemma 5.8, `NLAlib/Matrix/Pseudoinverse/NormBounds.lean`:
  $\|\mathbf{M}^{+}\|_{\mathsf{F}} \le \|(\mathbf{R}^{\mathsf{H}}\mathbf{M})^{+}\mathbf{R}^{\mathsf{H}}\|_{\mathsf{F}}$,
  any $\mathbf{M}$, invertible $\mathbf{R}$, over `RCLike`. Numerically checked including
  rank-deficient $\mathbf{M}$.
* **W2** (L) Proposition 5.7 with weight, `RandomMatrix/Haar/Blocks.lean`, in the block form of
  the existing $\mathbf{R} = \mathbf{I}$ equality `integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame`.
  The integrand is integrable (bounded by $\|\mathbf{R}\|_2^2\|\mathbf{R}^{-1}\|_2^2$ times the
  $\mathbf{R} = \mathbf{I}$ one), so the Bochner lower bound is not a junk trap.
* **W3** (L), **W4** (S), **W5** (M) Theorem 2.2, `Regression/SketchAndSolve.lean`: for a fixed
  full-column-rank sketch $\mathbf{\Omega}_0$, the Haar-rotated problem
  $(\mathbf{U}\mathbf{A}, \mathbf{U}\mathbf{B})$ has expected residual $\ge$
  `haarProjectionFactor m ℓ r` times the optimum (W3), so some orthogonal $\mathbf{U}$ works (W4);
  for a random sketch of **any** law with full rank a.s., some $\mathbf{U}$ works in `lintegral`
  (W5; Bochner would return $0$ on non-integrable laws, EW's caveat). Result id
  `sketch-and-solve-lower-bound` on W5. EW's statement is a supremum over problems of rank $r$;
  W4/W5 give the supremum's witness for each problem, which is stronger.
* **W6** (L) Lemma 6.2 as `Tendsto … atTop (𝓝 (rotationInvariantFactor … * (b * |t|)))`, in
  `LowRank/Gaussian/RotationInvariantFactor.lean`, whose docstring reserves the file for it.
  Dominated convergence with the existing pointwise bound as dominator (it equals the limit).
  *Degenerate:* $b = 0$ (error $0$), $\ell = r$ (factor $0$, Nyström exact).
* **W7** (M) Theorem 3.6(b), **W8** (S) Theorem 3.3, **W9**, **W10** (S) Theorem 4.2(b) with
  Gaussian / Haar co-range, `LowRank/Optimality/RotationInvariant.lean`: for every
  $c <$ factor there is a matrix of rank $r$ with $c\cdot\mathrm{OPT}_q < \mathbb{E}\,\mathrm{err}$.
  Hypotheses mirror the upper bounds ($q + 2 \le \ell \le r$, $r \le n$ resp. $\min(m,n)$, full rank
  a.s., and $\ell + 2 \le p$ ($\le m$ for Haar)). *Degenerate:* $\ell = r$ makes the factor $0$;
  then $c < 0$ and the claim holds since $\mathrm{OPT}_q > 0$ at rank $r > q$. The strict
  "for every $c$ below" form is how a supremum attained only in a limit is stated without `sSup`.
  Result ids `randomized-nystrom-lower-bound`, `randomized-svd-lower-bound`,
  `generalized-nystrom-lower-bound` (new ids).

**Type (i) versus type (ii).** EW's 3.3/3.6(b)/4.2(b) hold for every full-rank law of
$\mathbf{\Omega}$ (and $\mathbf{\Psi}$, not even independent), by composing the instance with an
independent Haar rotation $\mathbf{U}$ (and $\mathbf{V}$) and the probabilistic method. W7–W10
cover left unitarily invariant laws, where no rotation is needed and the statements are the
sharpness of the library's own upper bounds. The type (ii) lift is W5's Tonelli argument plus a
bounded-convergence step in $a$; it is deferred (OQ1) because it doubles the size of the EW part
for laws the library never instantiates.

### 3.4 ForMathlib and moments

* **PZ1** (S) `ProbabilityTheory.sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt`, new file
  `ForMathlib/Probability/Moments/PaleyZygmund.lean`:
  $(1-\theta)^2(\mathbb{E}Z)^2 \le \mathbb{E}Z^2\cdot\mathbb{P}[Z > \theta\mathbb{E}Z]$ for $Z \ge 0$
  a.s., `MemLp Z 2`, $0 \le \theta \le 1$ (both bounds on $\theta$ necessary: constant $Z$
  counterexamples in the docstring; `MemLp Z 2` necessary since Bochner's junk $\mathbb{E}Z^2 = 0$
  would make it false). Product form, no division. Result id `paley-zygmund-inequality`; cited
  [PaleyZygmund1932] (locator to check), new bib entry: 28(2), 190–205, DOI verified; the lemma
  number is unverified, and the companion note 28(3), 266–272 may hold the inequality (OQ9).
* **X1**, **X2** (S) in `Probability/Distributions/ChiSquareMoments.lean`:
  $\mathbb{E}(\|\mathbf{g}\|^2 - \|\mathbf{h}\|^2)^2 = 4d$, $\mathbb{E}(\cdot)^4 = 48d^2 + 96d$ for
  independent standard Gaussian vectors. Checked by expanding with $\chi^2$ moments
  $d(d+2)\cdots(d+2j-2)$: $2d(d+2)(d+4)(d+6) - 8d^2(d+2)(d+4) + 6d^2(d+2)^2 = 48d(d+2)$.

## 4. Deferred, with what each needs

| item | needs | size |
|---|---|---|
| EW 3.3/3.6(b)/4.2(b) for any full-rank law (type ii) | Haar rotation of the instance, Tonelli (as W5), bounded convergence in $a$ for $\mathbb{E}_{\mathbf{U}}$, two independent rotations for 4.2(b) | ≈ 8 decls |
| complex field ($\alpha_{\mathbb{C}} = 0$) | complex Gaussian/Haar laws (absent) | large |
| EW §4.2 "$k + \ell \ge (4/\varepsilon^2 + 2)q$" | over $\mathbb{R}$ ($\alpha = 1$) EW give no derivation; the $\alpha = 0$ algebra is elementary but the library is real | 1–2 decls |
| OP1 general $k$ for $2 \le k < K_0$ | a positive-probability (not high-probability) version of OP1 §4 step 4, or an $a\to\infty$ embedding of the $k = 1$ instance | research |
| OP2 D2 in expectation ($8000 \to \approx 3000$) | §3.4 arithmetic of OP2 on T2 | ≈ 3 decls, low value |
| OP2 Conjecture C1 ($p = \Theta(k/\varepsilon)$ suffices) | Gaussian width over rank-$k$ projectors; open research, not a target | — |

## 5. What S10 does and does not say about one-pass LRA

S10's lower bounds are for the named estimators only. Together with the library's upper bounds:
early-truncated RSVD is $\Theta(k/\varepsilon^2)$ in $\ell$ (E3/E5/E6 against $900k/\varepsilon^2$);
untruncated GN is $\Theta(q/\varepsilon^2)$ in $k' + \ell$ (W9/W10 against the library's 4.2(a));
truncated GN needs $p - \ell = \Omega(k/\varepsilon)$ on EW's instance (L2), and the library proves
$p = O(k/\varepsilon^2)$ sufficient. Whether truncated GN needs $p = \Omega(k/\varepsilon^2)$ in the
worst case is open (OP2 C1, conjectured no); no statement here asserts or implies an
$O(k/\varepsilon)$ upper bound for it or for any sketch-only estimator.

## 6. Files and placement

New files (topic: optimality of a named estimator):

* `NLAlib/LowRank/Optimality/EarlyTruncation.lean`: E1–E8.
* `NLAlib/LowRank/Optimality/TruncatedGeneralizedNystrom.lean`: L1–L2.
* `NLAlib/LowRank/Optimality/RotationInvariant.lean`: W7–W10 (the file PORT_LOWRANK planned for S10).
* `NLAlib/ForMathlib/Probability/Moments/PaleyZygmund.lean`: PZ1 (upstream candidate).

Additions to existing files (scaffold mirrors at the same path):

| statements | home | reason |
|---|---|---|
| X1, X2 | `Probability/Distributions/ChiSquareMoments.lean` | $\chi^2$ moments |
| T1, T2, T3 | `LowRank/Structural/Truncation.lean` | next to the perturbed-truncation lemmas they sharpen or reverse |
| G1, G2, G3 | `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean` | Gaussian expectations of truncated GN |
| W1 | `Matrix/Pseudoinverse/NormBounds.lean` | a pseudoinverse norm inequality |
| W2 | `RandomMatrix/Haar/Blocks.lean` | next to its $\mathbf{R} = \mathbf{I}$ equality |
| W3, W4, W5 | `Regression/SketchAndSolve.lean` | next to the exact Haar sketch-and-solve identity |
| W6 | `LowRank/Gaussian/RotationInvariantFactor.lean` | the file's docstring reserves it for this |

No placement flags. `docs/references.bib`: new entry `PaleyZygmund1932` (alphabetical, between
`PaigeWei1994` and `Parlett1998`). Skeleton rule: every scaffold file imports the scaffold files
its `Proof:` lines name (E2/E3 → PaleyZygmund, ChiSquareMoments; L1 → Structural/Truncation,
Gaussian/TruncatedGeneralizedNystrom; W2 → NormBounds; W3–W5 → Blocks; W7–W10 →
RotationInvariantFactor).

Library lemmas the proofs need that were private: `exists_core_generalizedNystrom`
(`Structural/Truncation.lean`, T1–T3) and `ae_rank_conjTranspose_mul_mul_eq`
(`Gaussian/TruncatedGeneralizedNystrom.lean`, L1). Per OQ8 (a) both are public on this branch
before dispatch; the first is extended to return the basis $\mathbf{Q}$ with
$\mathbf{N} = \mathbf{Q}\mathbf{E}$, $\mathbf{C} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}$ and
$\llbracket\mathsf{gn}\rrbracket_k = \mathbf{Q}\mathbf{Y}$.

## 7. Material

Read: EW (HTML v2: Thms 2.1, 2.2, 3.2, 3.3, 3.6, 4.2, Lemma 5.1, Prop. 5.6, 5.7, Lemma 5.8,
Lemma 6.2, §4.2, §5.5, §6.4, §6.5), OP1 and OP2 in full, `MatvecLowerBounds.md` (S10 and B1),
`PORT_LOWRANK.md` D6/D15/S10, the library files named in §6 and `Gaussian/EarlyTruncation.lean`,
`Gaussian/GeneralizedNystrom.lean`, `Gaussian/RotationInvariant.lean`. D15's "$2 \times 2$
lower bound for early truncation (draft only, no rigorous source)" is E1–E5 here, now with a
complete proof. No prototype exists for any S10 statement; outlines follow OP1/OP2/EW.

## 8. Checks

* `LEAN_NUM_THREADS=2 lake build NLAlibScaffold`: 29 `sorry` warnings, nothing else (`--wfail`
  fails on the sorries by design).
* `check_rules.py --files <11 scaffold files>`: 0 errors (70 rules; N1–N18 need the extraction,
  which covers `NLAlib` only; names chosen by hand against CONTRIBUTING §4, OQ4).
* `check_refs.py`, `check_constants.py`, `check_latex.mjs` (KaTeX at `~/node_modules`):
  0 problems.
* Dispatcher `locate` (`dispatch.py`): all 29 targets found with `sorry` bodies; no untargeted sorry.
* Numerics (scratch script, not committed; sanity checks of deterministic inequalities, not rate
  evidence): T2 and T3 on 20 000 random instances ($m, n \le 11$, spectra flat to cubic decay,
  all $k \le \ell$, $p \ge \ell$), E1 on random $2 \times \ell$ sketches, W1 on 50 000 random
  $\mathbf{M}$ (including rank-deficient) and $\mathbf{R}$: no violation beyond rounding
  ($10^{-11}$ relative); apparent violations at $k = \ell$ were all at absolute error $10^{-21}$.

## 9. Open questions for the maintainer

**OQ1 (EW scope).** Type (i) (left unitarily invariant laws) for 3.3/3.6(b)/4.2(b) now, type (ii)
for 2.2 only; or type (ii) for all four now (≈ +8 declarations, W5's pattern twice more plus a
two-rotation Fubini). *Recommend:* type (i) now; type (ii) deferred until a non-invariant sketch
(sparse, SRHT) needs it.

**OQ2 (OP1 constants at $k = 1$).** $\ell \ge 100$, excess $1/(100\sqrt\ell)$, probability $1/12$
(safe, proof margins ≥ 10%); or OP1's $\ell \ge 25$, $0.02/\sqrt\ell$ (false at small $\ell$ as
written: the $e^{-\ell/8}$ term costs too much; would need Laurent–Massart). *Recommend:* the safe
constants; the rate is the content, the true constant ($\approx 0.46$) is out of reach either way.

**OQ3 (OP1 general $k$).** (a) $k \ge K_0$ with existential $c, C, K_0$ (proof complete at
Chebyshev level); (b) drop E7–E8 until a small-$k$ argument exists; (c) state for all $k \ge 1$
(true by numerics, unproved). *Recommend:* (a); it pins the $k$-dependence and costs one H job.

**OQ4 (names).** Lower bounds are named by the conclusion's left side: `le_integral_…`,
`le_measureReal_…`, `mul_le_integral_…`, `exists_lt_integral_…`, `one_le_mul_card_of_forall_…`,
`not_exists_forall_…`, `eventually_le_integral_…`, `tendsto_integral_…`. N1–N18 were not run on
the scaffold. *Recommend:* accept; rerun `check_names.py` on the extraction when the first proofs
land.

**OQ5 (form of L1).** (a) $\forall\eta > 0$, eventually in $a$ (stated); (b) a $\liminf$;
(c) an explicit finite-$a$ bound (needs $p \ge \ell + 4$, $\ell \ge k + 4$ for fourth moments).
*Recommend:* (a): it is what L2 consumes, and (c) adds hypotheses for no use.

**OQ6 (no new definitions).** Instances inline (with `hA : A = …` where they would repeat inside
binders), the core noise and the oracle truncation spelled out. *Recommend:* keep; name them only if
a second stage reuses them (N11 applies to repeated *named quantities*; these are hard instances).

**OQ7 (Result ids).** New ids: `early-truncated-rsvd-lower-bound` (E3, E8),
`truncated-gn-lower-bound` (L1), `sketch-and-solve-lower-bound` (W5),
`randomized-nystrom-lower-bound` (W7), `randomized-svd-lower-bound` (W8),
`generalized-nystrom-lower-bound` (W9, W10), `paley-zygmund-inequality` (PZ1). *Recommend:* accept;
add them to the explorer's literature map with the lower-bounds section (MatvecLowerBounds
EXPLORER-TIMING (a): when results land).

**OQ8 (private core lemma).** Make `exists_core_generalizedNystrom` public and extend it to return
the basis $\mathbf{Q}$ with $\mathbf{N} = \mathbf{Q}\mathbf{E}$ (one PR before dispatch), or let
T1–T3 jobs copy it. *Recommend:* make it public (three jobs reuse it; copies would be deleted as
duplicates at clean-up).

**OQ9 (Paley–Zygmund citation).** [PaleyZygmund1932] ("On some series of functions (3)",
Proc. Camb. Phil. Soc. 28(2), 190–205, 1932, DOI 10.1017/S0305004100010860: verified by the Fable
review). The locator "Lemma 19" is unverified (marked "locator to check"); the companion note "A
note on analytic functions in the unit circle", 28(3), 266–272 (1932), may be the source. *Recommend:*
keep the entry with its "to be checked" note and verify at clean-up, or cite a textbook statement
instead if the maintainer has one at hand.
