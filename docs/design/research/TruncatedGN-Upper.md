# Research design note: truncated generalized Nyström with $O(k/\varepsilon)$ sketches

**Status: RESEARCH, not for `main`.** Branch `research/tgn-upper` (from `origin/main` `79f8cc2`).
Formalization plan for the maintainer's derivation (2026-10-26) that late-truncated generalized
Nyström reaches $(1+\varepsilon)$ with $\ell, p = O(k/\varepsilon)$, as verified and repaired in
`~/nlalib-harness/reports/OP6-TruncatedGN-Upper.md` (OP6, the authoritative proof; its lemma
numbers are used as note ids). Context: `reports/OP2-TruncatedGN.md`. Targets:
`~/nlalib-harness/pilot/tgnup-targets.json` (22 rows). Skeleton: 22 sorried statements in 6
scaffold files; `lake build NLAlibScaffold` gives exactly 22 `declaration uses sorry` warnings;
`check_rules.py --files` (scaffold), `check_latex.mjs` and `check-skeleton --strict` clean.

## 1. Statement

Library conventions: $\mathbf{\Omega}$ is `X` ($n \times \ell$), $\mathbf{\Psi}$ is $m \times p$
(OP6's $s = \ell$, $t = p$, $\mathbf{S} = \mathbf{\Psi}^{\mathsf{T}}$), output
`truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k`, $T = \|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, $g = 1 + k/(\ell - k - 1)$
(`gaussianProjectionFactor`).

**M1.** $\exists C > 0$: for $4k \le \ell$, $4\ell \le p$,
$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{gn}\rrbracket_k\|_{\mathsf{F}}^2 \le
(g + C(k/p + k/\sqrt{\ell p}))\,T$. **M2.** $\exists C$: $0 < \varepsilon \le 1$,
$Ck \le \varepsilon\ell$, $4\ell \le p$ $\Rightarrow$ $\le (1+\varepsilon)T$.
Constants existential (`exists_forall_` form; OP6 has explicit $c_1 \le 7.4\cdot10^6$,
$c_2 \le 9.1\cdot10^3$ under $\ell \ge 6k$, $p \ge 2\ell + 2$; ours use the library's
$4k \le \ell$, $4\ell \le p$ hypotheses and its constants $25$, $4$, $121$).

## 2. Decomposition (note ids = targets)

All deterministic statements are over $\mathbb{R}$ (generalization to `RCLike` deferred), for
arbitrary $\mathbf{B}, \mathbf{N} \in \mathbb{R}^{m \times n}$ and a best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{B} + \mathbf{N}$ (`IsBestRankApprox`), in **left** coordinates
($\mathbf{Z} = \mathbf{P}_{\mathbf{Y}}$, $\mathbf{P}_i$ = range projector of
$\llbracket\mathbf{B}\rrbracket_i$; OP6 works with right projectors, the transpose). No new
definitions: the window projectors are $\mathbf{L} = \mathbf{P}_b - \mathbf{P}_a$ and
$\mathbf{L}' = \mathbf{P}'_b - \mathbf{P}'_a$ ($\mathbf{P}'_i$ = range projector of
$\llbracket\mathbf{B}\rrbracket_i^{\mathsf{H}}$), well defined because every truncation is built
from the one chosen SVD (`truncatedSVD_def`). $\theta = \sigma_{k-1}(\mathbf{B})$ (0-indexed),
window $a \le k \le b$: $\sigma_i \ge 2\theta$ ($i < a$), $\sigma_a \le 2\theta$,
$\sigma_b \le \theta/2$; $q = b - k$; $D = \|(\mathbf{I}-\mathbf{Z})\mathbf{B}\|^2 -
\|(\mathbf{I}-\mathbf{P}_k)\mathbf{B}\|^2$; $\eta = \|\mathbf{N}\|_2$;
$\mu = \|\mathbf{L}\mathbf{N}\mathbf{L}'\|_2$.

| id | Lean name (namespace `NLAlib`) | statement | diff | deps |
|---|---|---|---|---|
| S1 | `sq_mul_frobNorm_mul_sub_rangeProjector_sq_le` | $c \le \sigma_i$ on $[a,j)$ $\Rightarrow$ $c^2\|\mathbf{W}(\mathbf{P}_j-\mathbf{P}_a)\|^2 \le \|\mathbf{W}(\mathbf{B}_j - \mathbf{B}_a)\|^2$ | M | – |
| W1 | `exists_singularValues_window` | window exists, $q\theta^2 \le 4\|\mathbf{B}-\mathbf{B}_k\|^2$ (OP6 §4.4) | S | – |
| L31a | `IsBestRankApprox.frobNorm_sub_sq_eq_add` | $\|\mathbf{B}-\mathbf{Y}\|^2 = \|(\mathbf{I}-\mathbf{Z})\mathbf{B}\|^2 + \|\mathbf{Z}\mathbf{N}\|^2$ (I1) | S | – |
| L31b | `frobNorm_one_sub_mul_sq_sub_eq_add` | weighted identity, basis-free, any $\theta$ (I2) | S | – |
| L32 | `IsBestRankApprox.frobNorm_one_sub_rangeProjector_mul_sq_sub_le` | $D \le 2\langle(\mathbf{Z}-\mathbf{P}_k)\mathbf{B},\mathbf{N}\rangle + \|\mathbf{Z}\mathbf{N}\|^2 - \|\mathbf{P}_k\mathbf{N}\|^2$ | S | – |
| L33 | `IsBestRankApprox.frobNorm_sub_sq_le_add_singularValues_mul_specNorm` | excess $\le 4k\sigma_k\eta + 12k\eta^2$ (large noise) | S | – |
| L34h | `mul_frobNorm_mul_truncatedSVD_sq_add_le` | head weight $\ge \frac38\|\mathbf{W}\mathbf{B}_a\|^2 + \frac32\theta^2\|\mathbf{W}\mathbf{P}_a\|^2$ | S | S1 |
| L34t | `mul_frobNorm_mul_one_sub_sq_add_le` | tail weight $\ge \frac38\theta^2\|\mathbf{W}(\mathbf{I}-\mathbf{P}_b)\|^2 + \frac32\|\mathbf{W}(\mathbf{B}-\mathbf{B}_b)\|^2$ | S | – |
| L34a | `rank_sub_mul_mul_le` | $\operatorname{rank}\mathbf{R} \le 4k$ | S | – |
| L34b | `frobNorm_sub_mul_mul_sq_le` | $\|\mathbf{R}\|_{\mathsf{F}}^2 \le 15D$, $\mathbf{R} = \mathbf{\Delta}\mathbf{B} - \mathbf{L}\mathbf{\Delta}\mathbf{B}\mathbf{L}'$ | M | L31b, L34h, L34t |
| L35 | `nuclearNorm_mul_sub_mul_le` | $\|\mathbf{L}\mathbf{\Delta}\mathbf{L}\|_* \le 4\min(k,q) + 6D/\theta^2$ | M | L31b, L34h, L34t |
| P36 | `IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_sq_add_window` | excess $\le 500k\eta^2 + 40\theta\min(k,q)\mu$ | L | L31a, L31b, L32, L33, L34a, L34b, L35 |
| T1 | `generalizedNystrom_eq_rsvd_add` | $\mathsf{gn} = \mathbf{R} + \mathbf{N}$ under the rank event | S | – |
| T2 | `frobNorm_sub_truncatedSVD_generalizedNystrom_sq_eq_add` | Pythagoras (OP6 §2.1) | S | – |
| T3 | `frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_window` | P36 at $\mathbf{B} = \mathsf{rsvd}$, $\mathbf{N}$ = core noise | S | T1, T2, P36 |
| G1 | `integral_specNorm_mul_mul_pinv_mul_le_of_hasLaw_gaussianMatrix` | $\mathbb{E}\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\mathbf{T}\| \le \beta(\|\mathbf{S}\|\|\mathbf{T}\|_{\mathsf{F}} + \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|)$ | M | – |
| G2 | `integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix` | $\mathbb{E}\|\mathbf{F}\mathbf{\Pi}\mathbf{E}\| \le \beta(\|\mathbf{E}\|\|\mathbf{F}\|_{\mathsf{F}} + \|\mathbf{E}\|_{\mathsf{F}}\|\mathbf{F}\|)$ | M | G1 |
| G43 | `integral_specNorm_mul_obliqueProjector_mul_sub_rsvd_mul_le_of_hasLaw_gaussianMatrix` | fixed $\mathbf{x}$: $\mathbb{E}\|\mathbf{F}\mathbf{N}\mathbf{T}\| \le \frac{4}{\sqrt p}(\ldots)$ (OP6 §4.3) | S | G2 |
| R51 | `integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix` | $\mathbb{E}\|\mathbf{A}-\mathbf{R}\|_2^2 \le 121T/\ell$ (public copy of a private library lemma; OP6 §5.1) | S | – |
| C45 | `exists_forall_…_sq_le_of_gaussianMatrix` | conditional on $\mathbf{x}$: $\le \|\mathbf{A}-\llbracket\mathbf{R}\rrbracket_k\|^2 + Ck((\|\mathbf{E}\|_{\mathsf{F}}^2 + \ell\|\mathbf{E}\|^2)/p + \|\mathbf{E}\|\gamma/\sqrt p)$ (OP6 Cor. 4.5) | L | T3, W1, G43 |
| M1 | `exists_forall_…_sq_le_add_of_hasLaw_gaussianMatrix` | §1 | M | C45, R51 |
| M2 | `exists_forall_…_sq_le_one_add_of_hasLaw_gaussianMatrix` | §1 | S | M1 |

Waves (dependency depth): 0: S1 W1 L31a L31b L32 L33 L34t L34a T1 T2 G1 R51; 1: L34h G2;
2: L34b L35 G43; 3: P36; 4: T3; 5: C45; 6: M1; 7: M2. Difficulty: S 13, M 7, L 2.
Every docstring carries the statement and a `Proof:` paragraph; the targets file has step-by-step
outlines.

## 3. Proof sketches (short; full outlines in the targets file)

* **P36** (OP6 Prop. 3.6). Excess $= D + \|\mathbf{Z}\mathbf{N}\|^2 \le D + k\eta^2$ (L31a). If
  $\theta \le 100\mu$ ($\le 100\eta$, incl. $\theta = 0$): L33 gives $\le 412k\eta^2$. Else
  L32, split $\mathbf{\Delta}\mathbf{B} = \mathbf{R} + \mathbf{L}\mathbf{\Delta}\mathbf{L}\,
  (\mathbf{B}_b - \mathbf{B}_a)$; $|\langle\mathbf{R},\mathbf{N}\rangle| \le
  2\sqrt{15kD}\,\eta$ (L34a, L34b, Hölder), the window part $\le (4\min(k,q) + 6D/\theta^2)\,
  2\theta\mu$ (L35, $\|\mathbf{B}_b - \mathbf{B}_a\| \le \sigma_a \le 2\theta$); absorb
  $24(\mu/\theta)D \le D/4$, Young: $D \le 482k\eta^2 + 32\theta\mu\min(k,q)$.
* **L31b** is the basis-free form of OP6's (I2): with $\mathbf{H}_\pm$ the parts of
  $\mathbf{B}\mathbf{B}^{\mathsf{T}} - \theta^2\mathbf{I}$ on and off $\mathbf{P}_k$,
  $D = \operatorname{tr}((\mathbf{I}-\mathbf{Z})\mathbf{H}_+) + \operatorname{tr}(\mathbf{Z}
  \mathbf{H}_-) + \theta^2(\operatorname{tr}\mathbf{P}_k - \operatorname{tr}\mathbf{Z})$. The last
  term (rank deficit of $\mathbf{Y}$) is what OP6 removes by padding $\widehat{\mathbf{P}}$ to
  rank $k$; here it is kept and is $\ge 0$. L34h/L34t are the window-boundary constants
  ($\sigma > 2\theta$: $\sigma^2 - \theta^2 \ge \frac34\sigma^2, 3\theta^2$; $\sigma <
  \theta/2$), reduced to the single SVD fact S1.
* **L34b**: three row-orthogonal pieces $\mathbf{\Delta}\mathbf{B}_a$,
  $\mathbf{\Delta}(\mathbf{B} - \mathbf{B}_b)$, $(\mathbf{I}-\mathbf{L})\mathbf{Z}\mathbf{L}
  (\mathbf{B}_b - \mathbf{B}_a)$; gives $(32/3)D$ (Fable pre-dispatch review) (stated $15D$ as in OP6).
* **L35**: block expansion of $\mathbf{L}\mathbf{Z}\mathbf{L} - (\mathbf{P}_k - \mathbf{P}_a)$
  and the trace balance $\|\mathbf{Z}\|_{\mathsf{F}}^2 \le k$ (OP6 proves the sharper
  $2\min(k,q) + \frac43 D/\theta^2$ by Weyl; the block route avoids eigenvalue interlacing in Lean).
* **G-series** (OP6 §4). $\mathbb{E}\eta^2 \le \frac{25}{p}\|\mathbf{E}\|_{\mathsf{F}}^2 +
  \frac{4\ell}{p}\|\mathbf{E}\|_2^2$ is already in the library
  (`integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_div_card_of_hasLaw_gaussianMatrix`):
  it applies Chevet conditionally on $\mathbf{G}_1$ with the right factor
  $\mathbf{G}_1^{+}$, which is OP6's repair (iii) in another form (no $\sqrt p$ loss). G1/G2 are
  the same route with a left factor, giving $\mathbb{E}\mu \le 8\sqrt{w/p}\,\|\mathbf{E}\|$,
  $w = b - a \le k + q$ (OP6 §4.3 via $\mathbf{M}^{1/2}\mathbf{G}$; equivalent).
* **R** (OP6 §5). The joint baseline $\mathbb{E}\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k
  \|^2 \le gT$ is already the library's
  `integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix` (OP6 repair (ii) is
  thus already formalized); only R51 (public $121T/\ell$) is new.
* **C45/M1/M2**: integrate T3 over $\mathbf{\Psi}$, then over $\mathbf{\Omega}$ with
  `IndepFun.integral_comp_le_of_integral_le`; Cauchy–Schwarz or AM–GM for
  $\mathbb{E}\|\mathbf{E}\|\gamma$; arithmetic.

## 4. Changes against the maintainer's sketch

* Large-noise case (OP6 repair (i)): not "rank-truncation optimality" but L33, which is the
  library's private next-$k$ perturbed truncation (spectral, $4\sqrt k\,\eta\gamma_k$) with
  $\gamma_k \le \sqrt k\,\sigma_k$; OP6's Lemma 3.3 route (L32 + $\|\mathbf{B}\mathbf{\Delta}\|^2 =
  D + 2L$) is noted as an alternative.
* Case threshold $\theta \le 100\mu$ (not $\eta \gtrsim \theta$): the absorption needs only
  $\mu \ll \theta$, and $\mu \le \eta$ makes the other case large-noise.
* Constants: L34b $15$, L35 $(4, 6)$, P36 $(500, 40)$ — checked numerically
  (20000 random instances incl. ties and rank deficiency: max $\|\mathbf{R}\|^2/D = 1.67$, trace
  balance slack $\ge 0$ at $(4,5)$, excess/bound $\le 0.014$).
* Nothing in the sketch is false (agrees with OP6 §9).

## 5. Library: present / missing

Present and reused: `exists_core_generalizedNystrom`, `IsBestRankApprox` API,
`truncatedSVD_def`/`svdU`/`isSVD_svdU_svdV`, `rangeProjector_truncatedSVD_mul`,
`mul_rangeProjector_conjTranspose_truncatedSVD`, `range_truncatedSVD_mono`, Ky Fan/Hölder
(`abs_frobInner_le_nuclearNorm_mul_specNorm`, `nuclearNorm_le_sqrt_rank_mul_frobNorm`,
`nuclearNorm_mul_le_frobNorm_mul_frobNorm`), projector norms (`Matrix/Norms/Projector.lean`),
Chevet with random factors (`integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun`),
Gaussian pinv moments and `gaussianPinvSpecNormBound(_le)`, the sketch-and-solve frames
(`exists_hasOrthonormalCols_frames_range_compl`, `obliqueProjector_mul_one_sub_rangeProjector_mul_eq`),
the spectral core-noise bound (above), HMT 10.5/9.1 and the joint baseline.

Missing (= the targets): the whole localized deterministic lemma (S1–P36), the two-sided Gaussian
block bound (G1, G2, G43), public versions of two private library lemmas (L33 ← Truncation.lean's
next-$k$ lemma; R51 ← TGN file's spectral residual, both copied by the worker), the GN split
(T1, T2) and the assembly. Not needed: Davis–Kahan/Wedin (present in `Matrix/Perturbation`, unused),
Weyl monotonicity, the $\mathbf{M}^{1/2}\mathbf{G}$ conditioning (replaced by Chevet conditional on
$\mathbf{G}_1$).

## 6. Open questions

1. Generalize the deterministic file to `RCLike` before any move to `main` (CONTRIBUTING §1.5).
2. Explicit constants (OP6's) instead of `exists_forall_` once proved; and whether to replace
   the library's $p \ge 8000\ell/\varepsilon$ theorem (OP6 §10.5; maintainer's rule: only as the
   complete theorem).
3. File placement if promoted: `Matrix/Perturbation/BestRankApprox.lean` is a new topic file;
   G1/G2/R51 join existing files; the private-lemma copies (L33, R51) should then become the
   library lemmas made public instead.
