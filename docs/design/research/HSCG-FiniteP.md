# Finite-precision Hestenes–Stiefel CG through the Lanczos reduction: research note

**Status: RESEARCH (open question, partial results).** Branch `research/hscg-fp` (worktree
`~/nlalib-research-hscg`, from `design/lanczos-fp` @ `8ec9b88`). Companion copy:
`docs/design/research/HSCG-FiniteP.md`. Date: 2026-10-29.

Question (maintainer): can finite-precision HSCG be analysed by the direct reduction used for
Lanczos (`LanczosRun` → normalised perturbed recurrence → Greenbaum-type backward model
`frobNorm_backwardH_sub_dilatedH_le`), given that "the way the roundoff errors enter seems very
different"?

**Short answer.** Yes, but with an extra factor that is intrinsic to the reduction. In the
normwise standard model used by the toolkit, the normalised CG residuals
$\bar{\mathbf v}_{j+1} = (-1)^j\mathbf r_j/\|\mathbf r_j\|$ and the tridiagonal matrix built from
the *computed* $a_j, b_j$ satisfy the library's normalised interface with

$$\|\bar{\mathbf f}_j\| \le C\,\varepsilon\|\mathbf A\|\,(1+\Pi_k),\qquad
|\bar p_j| \le C\,(j+1)\,\varepsilon\|\mathbf A\|\,\bigl[(1+\Pi_k)^2 + K_k\bigr],\qquad
\Pi_k := \max_{j<k}\frac{\|\mathbf p_j\|}{\|\mathbf r_j\|},\quad K_k \le 1.04\,\kappa(\mathbf A),$$

and a priori $\Pi_k^2 \le 1.2\,\kappa(\mathbf A)$ once $\varepsilon\,\mathrm{poly}(k)\,\kappa(\mathbf A)\le 1/100$.
So the `LanczosRun`-form bound holds with
$\varepsilon_{\mathrm{CG}} = C\,k\,\varepsilon\,\kappa(\mathbf A)$ (or, with the observable
certificate $\Pi_k$, $\varepsilon_{\mathrm{CG}} = C\,k\,\varepsilon\,(1+\Pi_k)^2$), and the backward
model follows with $\|\tilde{\mathbf A} - \mathbf I\otimes\mathbf A\|_F \le 2000k^4\varepsilon_{\mathrm{CG}}\|\mathbf A\|$
by the existing proof, after a refactor of its interface. The factor $\kappa(\mathbf A)$ (through
$\Pi_k^2$) is unavoidable for the interface quantities in the normwise model (§2.7); residual-norm
*ratios* do not appear as independent amplifiers (§2.5), which corrects part of the worry.
Nothing of this is in the literature as a theorem: the closest rigorous result (Strakoš–Tichý
2002, Thm 9.1) bounds a different local quantity, with $\kappa(\mathbf A)$, and imports one
exact-arithmetic fact.

---

## 1. Literature: what is actually proved

Sources read in full text: Greenbaum–Liu–Chen 2021 (arXiv 1905.05874v2), Meurant–Strakoš 2006
(Acta Numerica 15, pp. 471–542; sections 4.3, 5.1–5.2), Strakoš–Tichý 2002 (ETNA 13, pp. 56–80;
sections 7–10), Carson–Rozložník–Strakoš–Tichý–Tůma 2018 (SISC 40(5), A3549–A3580; §§3–4),
Carson–Liesen–Strakoš 2024 (LAA 692, pp. 241–291; §§2.3, 2.6, 2.8), Paige 2019 (SIMAX 40(4);
§§14–16), Gutknecht–(Paige)–Strakoš (TR V-764, 1997; = SIMAX 22(1), 2000, pp. 213–229; §9).
Not accessible in full text (publisher paywall; cited through the above): Greenbaum 1989 (LAA
113, pp. 7–63), Greenbaum–Strakoš 1992 (SIMAX 13(1), pp. 121–137), Notay 1993 (Numer. Math.
65, pp. 301–317). Abstract only: Bake–Carson–Ma (arXiv 2510.11379, v3 2026), Sinha (arXiv
2609.08066, 2026).

| Work | Object | Rigorous from a rounding model? | Hypotheses / factors | Not proved |
|---|---|---|---|---|
| Paige 1976/1980 (as stated in Meurant–Strakoš Thm 4.1) | Lanczos A(1) | yes | $\varepsilon_0 = 2(n+4)\varepsilon_M$, $\varepsilon_1 = 2(7+m_A\beta)\varepsilon_M$; $\|\delta\mathbf v_j\|\le\varepsilon_1\|\mathbf A\|$, $\eta_{j+1}\lvert\mathbf v_j^T\mathbf v_{j+1}\rvert\le 2\varepsilon_0\|\mathbf A\|$ | anything about CG |
| Greenbaum 1989 | perturbed Lanczos recurrence (1.1)–(1.3) of GLC; CG via normalised residuals (p. 24; Thm 3 pp. 26–29 for the $\mathbf A$-norm of the error) | the extension theorem is rigorous *given* (1.1)–(1.3): $\|\mathbf f_j\|\le\epsilon\|\mathbf A\|$, $\|\mathbf q_j\|\in[1\pm\epsilon]$, $\lvert\langle\beta_j\mathbf q_{j+1},\mathbf q_j\rangle\rvert\le\epsilon\|\mathbf A\|$ | eigenvalues of the extended $T$ within $O(n+m_k)^3\max\{\varepsilon_M\|\mathbf A\|, \|\mathbf f_j\|\}$ (MS06 Thm 4.9); perturbation of order $\epsilon^{1/4}$ (eq. (7.10), maintainer's note) | that *finite-precision HSCG* satisfies (1.1)–(1.3) with $\epsilon = O(\varepsilon_M)$ (MS06 §5.2: "the analysis … will also apply … see Greenbaum (1989, p. 24)" — i.e. the perturbation terms are derived, their size is not bounded in terms of $\varepsilon_M$ alone) |
| Greenbaum–Strakoš 1992 | a priori model (eigenvalues spread in tiny intervals) | no — numerical "prediction" | interval width not derived from the rounding model (MS06 p. 512: "a rigorous mathematical quantification of this approach is still incomplete") | everything quantitative |
| Notay 1993 | delay of convergence with outliers | rigorous *given* Greenbaum's hypotheses (MS06 §5.2, CLS24 §2.3) | inherits (1.1)–(1.3) | the hypotheses for HSCG |
| Gutknecht–Strakoš 2000 (TR 1997 with Paige) | residual gap $\mathbf r_n - (\mathbf b - \mathbf A\mathbf x_n)$ for two three-term vs. three two-term recurrences | yes (standard model) | three-term: local errors amplified by multipliers $\prod_{j=i}^k \gamma_{j-1}/\gamma_j = (\omega_k/\omega_{i-1})\,\|\mathbf r_k\|^2/\|\mathbf r_{i-1}\|^2$ (TR (9.7)), bounded via Hestenes–Stiefel Thm 5:5 by $\kappa(\mathbf A)$-type factors; two-term (HSCG): no amplification (Greenbaum 1997 SIMAX 18:535–551; Sleijpen–van der Vorst–Fokkema 1994) | nothing about the Lanczos backward model; the residual ratios here are *gap* amplifiers, not interface quantities |
| Strakoš–Tichý 2002 | HSCG, standard model (7.1)–(7.5), local bounds (7.9)–(7.14) | yes, with two imports | (7.14): $\lvert\varepsilon_{\gamma_j}\rvert\le\varepsilon\kappa(\mathbf A)\gamma_j O(n+c)$ (relative error of $a_j$ carries $\kappa$ via $\|\mathbf A\|\|\mathbf p\|^2/\mathbf p^T\mathbf A\mathbf p\le\kappa$); **Thm 9.1**: $\lvert\mathbf p_j^T\mathbf r_{j+1}\rvert\le\varepsilon\|\mathbf r_j\|^2\kappa(\mathbf A)\,O((j+1)(8+2c+n+3j))$ under $\varepsilon(n+c)\kappa\ll1$; **Thm 10.1**: $\|\mathbf x-\mathbf x_j\|_A^2-\|\mathbf x-\mathbf x_{j+d}\|_A^2=\eta_{j,d}(1+E^{(1)})+\|\mathbf x-\mathbf x_j\|_A E^{(2)}$ | (9.13) $\|\mathbf p_i\|/\|\mathbf r_i\|\le 1+i\kappa^{1/2}$ uses (7.20) $\|\mathbf r_j\|/\|\mathbf r_i\|\le\kappa^{1/2}$ for $j\ge i$, justified by "monotonicity of the $\mathbf A$-norm … preserved (with small additional inaccuracy) also in finite precision (see [19], [22])" — imported from Greenbaum's theory, not re-proved; (7.19)–(7.20) also assume the gap is small ("final accuracy not reached"). Local orthogonality is $\mathbf p_j^T\mathbf r_{j+1}$ (line search), not $\mathbf r_j^T\mathbf r_{j+1}$; no backward model |
| Meurant–Strakoš 2006 | survey; Thm 5.1 (CG–Lanczos recurrence $\eta_{k+1}\mathbf w_{k+1}=\mathbf A\mathbf w_k-\alpha_k\mathbf w_k-\eta_k\mathbf w_{k-1}+\Delta_k^w$) | derivation yes; bounds on $\Delta^w_k$ "left to Meurant (2006)" | states that CG local-orthogonality bounds "depend, in addition to $\varepsilon_M$, $n$ and $\|\mathbf A\|$ also on $\kappa(\mathbf A)$ and $\|\mathbf r_k\|^2$" (§5.1) | — |
| Greenbaum–Liu–Chen 2021 (SISC 43(5) S496–S515) | HSCG, CGCG, GVCG | **no**: "We do not rigorously prove these properties for any particular implementation" (§1, p. 3) | derives (2.2)–(2.4): $\mathbf f_k = \frac{(-1)^k}{\|\mathbf r_{k-1}\|}\bigl(\frac{b_{k-1}}{a_{k-2}}\delta_{r_{k-1}} + \mathbf A\delta_{p_{k-1}} - \frac1{a_{k-1}}\delta_{r_k}\bigr)$ with $\|\delta_{r_k}\|\le\epsilon(\|\mathbf r_{k-1}\|+2\|a_{k-1}\mathbf A\mathbf p_{k-1}\|+c\|\mathbf A\|\|a_{k-1}\mathbf p_{k-1}\|)$, $\|\delta_{p_k}\|\le\epsilon(\|\mathbf r_k\|+2\|b_k\mathbf p_{k-1}\|)$; errors in $a_k,b_k$ "included in the $\delta$ terms"; then "might therefore be expected to be of order $\epsilon\|\mathbf A\|$"; conditions (1.2)–(1.3) checked numerically ($\epsilon_1,\epsilon_2$ in (3.2)) | the bound $\|\mathbf f_k\|\le\epsilon\|\mathbf A\|$ (the term $\mathbf A\delta_{p_{k-1}}/\|\mathbf r_{k-1}\|$ alone is $\le\epsilon\|\mathbf A\|(1+\|b_{k-1}\mathbf p_{k-2}\|/\|\mathbf r_{k-1}\|)$) |
| Carson et al. 2018 | methodology (gap §3, delay §4.2) | gap: yes; delay: no | §4.2: Greenbaum's "positive answer … for Algorithm 1.1 [HSCG]"; "analogous analysis for [pipelined] … yet to be done" | — |
| Paige 2019 | **Lanczos-CG** ($\mathbf x_k=\mathbf V_k\mathbf T_k^{-1}\mathbf e_1\beta_1$), §14 (14.3)–(14.5) | yes (Paige's model, augmented-matrix result of Paige 2010), assuming $Q^{(k)}_{22}=0$ | backward-stable solutions "made available" | §16: "We would also like to show that CG as implemented in [Hestenes–Stiefel] is backward stable" — HSCG open |
| Carson–Liesen–Strakoš 2024 | survey | — | §2.8 "tunnel" statement (13) "has not been shown to hold … in general" | — |
| Bake–Carson–Ma 2025/26 | mixed-precision PCG | claimed rigorous (abstract) | backward error $O(u)$, forward $O(u)\kappa^{1/2}$ "after sufficiently many iterations", without assuming the updated residual is small | attainable accuracy only; no delay / backward model |
| Sinha 2026 | symmetric Krylov, dense left-to-right order | claimed (abstract) | precision bound for a prescribed backward error "within $n$ updates" | unverified; not a Greenbaum-type model |
| Chen 2026 (`simple-lanczos-stability`, this library) | Lanczos A(1) | yes (Lean) | $\|\Delta\|_F\le 2000k^4\varepsilon\|\mathbf H\|$ | CG |

**Corrections to the summaries in the task statement.**
1. GLC 2021 does not prove a rate or a model for any variant; it derives the perturbation terms
   and checks (1.2)–(1.3) numerically. Its remark that (2.4) "involves only local rounding
   errors" is correct, but local errors scaled by $1/\|\mathbf r_{k-1}\|$ carry
   $\|\mathbf p\|/\|\mathbf r\|$.
2. The only rigorous standard-model result on HSCG local orthogonality (Strakoš–Tichý Thm 9.1)
   concerns $\mathbf p_j^T\mathbf r_{j+1}$, carries $\kappa(\mathbf A)$, and uses the
   finite-precision monotonicity of error norms as an input. Its $\kappa$ comes partly from the
   crude bound $\|\mathbf A\|\|\mathbf p\|^2/\mathbf p^T\mathbf A\mathbf p\le\kappa$ for the
   dot-product error (Kantorovich gives $(\kappa+1)/(2\sqrt\kappa)$ for
   $\|\mathbf p\|\|\mathbf A\mathbf p\|/\mathbf p^T\mathbf A\mathbf p$) and partly from the
   matrix–vector error, where $\kappa$ is sharp (§2.7).
3. "Paige's CG results" are for Lanczos-CG; Paige himself lists HSCG backward stability as open.
4. The residual ratios in Gutknecht–Strakoš amplify the *residual gap* of three-term
   implementations. For the Lanczos interface of HSCG they do not appear as independent
   amplifiers (§2.5); they enter only through $\|\mathbf p_j\|/\|\mathbf r_j\|$
   (in exact arithmetic $\|\mathbf p_j\|^2/\|\mathbf r_j\|^2=\sum_{i\le j}\|\mathbf r_j\|^2/\|\mathbf r_i\|^2$, Hestenes–Stiefel).

---

## 2. Derivation

### 2.1 Model and notation

$\mathbf A\in\mathbb R^{n\times n}$ symmetric positive definite. Kernel contract as in
`LanczosRun` / `ass:arithmetic` with one parameter $\varepsilon\le 1/100$
($\varepsilon=\max(\varepsilon_{mv},\gamma_{N+c})$ for the program):
$\mathrm{fl}(\mathbf x^T\mathbf y)=\mathbf x^T\mathbf y+e$, $|e|\le\varepsilon\|\mathbf x\|\|\mathbf y\|$;
$\mathrm{fl}(\mathbf x\pm\alpha\mathbf y)=\mathbf x\pm\alpha\mathbf y+\mathbf e$,
$\|\mathbf e\|\le\varepsilon(\|\mathbf x\|+|\alpha|\|\mathbf y\|)$;
$\mathrm{fl}(\mathbf A\mathbf v)=\mathbf A\mathbf v+\mathbf e$, $\|\mathbf e\|\le\varepsilon\|\mathbf A\|\|\mathbf v\|$;
scalar operations with relative error $\le\varepsilon$. Steps $j=0,\dots,k-1$; the computed
quantities are

$$\begin{aligned}
\mathbf s_j &= \mathbf A\mathbf p_j+\mathbf e^s_j, &\mu_j &= \mathbf p_j^T\mathbf s_j+e^\mu_j, &\nu_j&=\rho_j^2(1+\theta_j),\quad \rho_j:=\|\mathbf r_j\|,\\
a_j &= \frac{\nu_j}{\mu_j}(1+\delta_j), & \mathbf r_{j+1}&=\mathbf r_j-a_j\mathbf s_j+\mathbf e^r_j, & b_j&=\frac{\nu_{j+1}}{\nu_j}(1+\delta'_j)=\frac{\rho_{j+1}^2}{\rho_j^2}(1+\eta_j),\\
\mathbf p_{j+1}&=\mathbf r_{j+1}+b_j\mathbf p_j+\mathbf e^p_{j+1}, & \mathbf p_0&=\mathbf r_0,\ \mathbf e^p_0=\mathbf 0,
\end{aligned}$$

with $|\theta_j|,|\delta_j|,|\delta'_j|\le\varepsilon$, $|\eta_j|\le 3.1\varepsilon$,
$\|\mathbf e^s_j\|\le\varepsilon\|\mathbf A\|\|\mathbf p_j\|$, $|e^\mu_j|\le\varepsilon\|\mathbf p_j\|\|\mathbf s_j\|$,
$\|\mathbf e^r_j\|\le\varepsilon(\rho_j+a_j\|\mathbf s_j\|)$, $\|\mathbf e^p_{j+1}\|\le\varepsilon(\rho_{j+1}+b_j\|\mathbf p_j\|)$.
No breakdown: $\nu_j,\mu_j>0$, so $a_j,b_j>0$. The iterate update $\mathbf x_{j+1}$ does not
enter (it only enters the residual gap). Define the run quantities

$$\pi_j:=\frac{\|\mathbf p_j\|}{\rho_j},\qquad q_j:=\frac{\|b_{j-1}\mathbf p_{j-1}\|}{\rho_j}\ (q_0:=0),\qquad
\kappa_j:=\frac{\|\mathbf A\|\,a_j\|\mathbf p_j\|^2}{\rho_j^2}\ \Bigl(\approx\frac{\|\mathbf A\|\|\mathbf p_j\|^2}{\mathbf p_j^T\mathbf A\mathbf p_j}\Bigr),$$

$\Pi_j:=\max_{i\le j}\pi_i$, $K_j:=\max_{i\le j}\kappa_i$. From the $\mathbf p$-update,
$q_j\le(1+\pi_j+\varepsilon)/(1-\varepsilon)\le 1.02(1+\pi_j)$. From
$\mu_j\ge\lambda_{\min}\|\mathbf p_j\|^2-\varepsilon\|\mathbf A\|\|\mathbf p_j\|^2-\varepsilon\|\mathbf p_j\|\|\mathbf s_j\|$,
if $2.1\varepsilon\kappa(\mathbf A)\le 1/100$ then $\kappa_j\le 1.04\,\kappa(\mathbf A)$ and
$\pi_j^2\le 1.03\,\kappa(\mathbf A)\,(1/a_j)/\|\mathbf A\|$.

### 2.2 The three-term recurrence (exact identity in the computed data)

From $\mathbf A\mathbf p_j=\mathbf s_j-\mathbf e^s_j=(\mathbf r_j-\mathbf r_{j+1}+\mathbf e^r_j)/a_j-\mathbf e^s_j$ and
$\mathbf A\mathbf p_j=\mathbf A\mathbf r_j+b_{j-1}\mathbf A\mathbf p_{j-1}+\mathbf A\mathbf e^p_j$:

$$\mathbf A\mathbf r_j=\Bigl(\frac1{a_j}+\frac{b_{j-1}}{a_{j-1}}\Bigr)\mathbf r_j-\frac1{a_j}\mathbf r_{j+1}-\frac{b_{j-1}}{a_{j-1}}\mathbf r_{j-1}+\mathbf g_j,\qquad
\mathbf g_j:=\frac{\mathbf e^r_j}{a_j}-\mathbf e^s_j-\frac{b_{j-1}}{a_{j-1}}\mathbf e^r_{j-1}+b_{j-1}\mathbf e^s_{j-1}-\mathbf A\mathbf e^p_j$$

($b_{-1}/a_{-1}:=0$). The computed $a_j$ enters only through the exact rearrangement of the
$\mathbf r$-update: *the accuracy of $a_j$ is irrelevant for the recurrence*; it matters only for
orthogonality (§2.5). This is the first structural difference from Lanczos, where
$\alpha_j=\mathrm{fl}(\mathbf v_j^T\mathbf w_j)$ enforces local orthogonality directly.

### 2.3 Normalised interface

Set $\bar{\mathbf v}_{j+1}:=(-1)^j\mathbf r_j/\rho_j$ ($j=0,\dots,k$; exactly unit),
$\alpha_{j+1}:=1/a_j+b_{j-1}/a_{j-1}>0$, $\beta_{j+1}:=\rho_{j+1}/(a_j\rho_j)>0$ (so the
normalisation step $\beta_{j+1}\bar{\mathbf v}_{j+2}=(-1)^{j+1}\mathbf r_{j+1}/(a_j\rho_j)$ is exact).
Multiplying §2.2 by $(-1)^j/\rho_j$ and using $b_{j-1}\rho_{j-1}/(a_{j-1}\rho_j)=(1+\eta_{j-1})\beta_j$:

$$\mathbf A\bar{\mathbf v}_{j+1}=\beta_j\bar{\mathbf v}_j+\alpha_{j+1}\bar{\mathbf v}_{j+1}+\beta_{j+1}\bar{\mathbf v}_{j+2}+\bar{\mathbf f}_j,\qquad
\bar{\mathbf f}_j:=\frac{(-1)^j\mathbf g_j}{\rho_j}+\eta_{j-1}\beta_j\bar{\mathbf v}_j .$$

This is exactly `LanczosData.recurrenceError j` for the data $(\mathbf A,\bar{\mathbf v},\alpha,\beta)$;
the symmetric $T_k$ has the LDL$^T$ factors $D=\mathrm{diag}(1/a_j)$,
$|L_{j+1,j}|=\sqrt{b_j}$ up to the $(1+\eta)$ factors, i.e. exact CG on any model reproducing $T_k$
reproduces the computed $a_j$ and $b_j$ exactly, and the residual norms up to $\prod(1+\eta_i)^{1/2}\le 1+1.6k\varepsilon$.

### 2.4 Lemma A (recurrence error)

Term by term, with $\|\mathbf s_j\|\le(1+\varepsilon)\|\mathbf A\|\|\mathbf p_j\|$:

| term of $\|\bar{\mathbf f}_j\|$ | bound |
|---|---|
| $\|\mathbf e^r_j\|/(a_j\rho_j)$ | $\varepsilon/a_j+1.01\,\varepsilon\|\mathbf A\|\pi_j$ |
| $\|\mathbf e^s_j\|/\rho_j$ | $\varepsilon\|\mathbf A\|\pi_j$ |
| $(b_{j-1}/a_{j-1})\|\mathbf e^r_{j-1}\|/\rho_j$ | $1.04\,\varepsilon\beta_j+1.01\,\varepsilon\|\mathbf A\|q_j$ |
| $b_{j-1}\|\mathbf e^s_{j-1}\|/\rho_j$ | $\varepsilon\|\mathbf A\|q_j$ |
| $\|\mathbf A\mathbf e^p_j\|/\rho_j$ | $\varepsilon\|\mathbf A\|(1+q_j)$ |
| $|\eta_{j-1}|\beta_j$ | $3.1\,\varepsilon\beta_j$ |

$$\boxed{\ \|\bar{\mathbf f}_j\|\le\varepsilon\|\mathbf A\|\,(5.1\,\pi_j+4.1)+\varepsilon\,(\alpha_{j+1}+4.2\,\beta_j)\ }$$

(using $1/a_j\le\alpha_{j+1}$). Linear in $\pi_j$; no residual ratio. Compare Lanczos:
$\|\bar{\mathbf f}_j\|\le 12(j+1)\varepsilon\|\mathbf H\|$ (`norm_normalized_recurrenceError_le`).
The $\pi_j$ comes from the two places where an error made on $\mathbf p_j$ (matrix–vector product,
$\mathbf p$-update) is measured against $\|\mathbf r_j\|$; the $\|b_{j-1}\mathbf p_{j-1}\|/\rho_j$ terms are
where the consecutive residual ratio would appear, and $q_j\le 1.02(1+\pi_j)$ absorbs it.

### 2.5 Lemma B (local orthogonality is inherited, not enforced)

Write $\sigma_j:=\mathbf r_j^T\mathbf r_{j+1}$, $\tau_j:=\mathbf p_j^T\mathbf r_{j+1}$,
$\zeta_j:=\mathbf p_{j-1}^T\mathbf s_j$. The interface quantity is
$\bar p_j:=\beta_{j+1}\bar{\mathbf v}_{j+1}^T\bar{\mathbf v}_{j+2}=-\sigma_j/(a_j\rho_j^2)$
(`LanczosData.adjacentInner j`).

*Line search.* From the $\mathbf r$- and $\mathbf p$-updates and $a_j\mu_j=\rho_j^2(1+\theta_j)(1+\delta_j)$:

$$\tau_j=b_{j-1}\tau_{j-1}+M_j,\qquad M_j:=-\rho_j^2(\theta_j+\delta_j+\theta_j\delta_j)+\mathbf e^{pT}_j\mathbf r_j+a_je^\mu_j+\mathbf p_j^T\mathbf e^r_j,$$

$$\frac{|M_j|}{\rho_j^2}\le\varepsilon\,(4.1+2.1\,\pi_j+2.1\,\kappa_j)=:\varepsilon m_j .$$

This is Strakoš–Tichý (9.3)–(9.4); unrolled, $\tau_j/\rho_j^2=\sum_{i\le j}(1+O(j\varepsilon))M_i/\rho_i^2$:
in *normalised* form the multipliers $\prod b_l=\rho_j^2/\rho_i^2(1+\dots)$ cancel — no
residual-ratio amplification (their (9.6)). The $\kappa_j$ term is the relative error of $a_j$.

*Consecutive residuals.* $\sigma_j=\rho_j^2-a_j\mathbf r_j^T\mathbf s_j+\mathbf r_j^T\mathbf e^r_j$ with
$\mathbf r_j^T\mathbf s_j=\mu_j-e^\mu_j-b_{j-1}\zeta_j-\mathbf e^{pT}_j\mathbf s_j$ gives

$$\sigma_j=a_jb_{j-1}\zeta_j+\bigl[-\rho_j^2(\theta_j+\delta_j+\theta_j\delta_j)+a_je^\mu_j+a_j\mathbf e^{pT}_j\mathbf s_j+\mathbf r_j^T\mathbf e^r_j\bigr].$$

*Conjugacy defect.* Using the symmetry of $\mathbf A$ once,
$\mathbf p_{j-1}^T\mathbf A\mathbf p_j=\mathbf p_j^T(\mathbf s_{j-1}-\mathbf e^s_{j-1})$, then
$\mathbf s_{j-1}=(\mathbf r_{j-1}-\mathbf r_j+\mathbf e^r_{j-1})/a_{j-1}$, the $\mathbf p$-update, and
$b_{j-1}\rho_{j-1}^2=\rho_j^2(1+\eta_{j-1})$:

$$a_{j-1}\zeta_j=\sigma_{j-1}+\rho_j^2\eta_{j-1}-b_{j-1}M_{j-1}+E_j,$$
$$E_j:=b_{j-1}\mathbf e^{pT}_{j-1}\mathbf r_{j-1}+(\mathbf r_{j-1}-\mathbf r_j)^T\mathbf e^p_j+\mathbf e^{rT}_{j-1}\mathbf p_j-a_{j-1}\mathbf e^{sT}_{j-1}\mathbf p_j+a_{j-1}\mathbf p_{j-1}^T\mathbf e^s_j .$$

Dividing by $a_j\rho_j^2$ and using $b_{j-1}/\rho_j^2=(1+\eta_{j-1})/\rho_{j-1}^2$:

$$\boxed{\ \bar p_j=(1+\eta_{j-1})\,\bar p_{j-1}+L_j\ },\qquad
L_j=-\frac{(1+\eta_{j-1})(\rho_j^2\eta_{j-1}-b_{j-1}M_{j-1}+E_j)}{a_{j-1}\rho_{j-1}^2}
+\frac{\rho_j^2(\theta_j+\delta_j+\theta_j\delta_j)-a_je^\mu_j-a_j\mathbf e^{pT}_j\mathbf s_j-\mathbf r_j^T\mathbf e^r_j}{a_j\rho_j^2}.$$

So $\mathbf r_j\perp\mathbf r_{j+1}$ is *not* produced at step $j$; it is the previous step's
$\mathbf r_{j-1}\perp\mathbf r_j$ transported through the conjugacy $\mathbf p_{j-1}^T\mathbf A\mathbf p_j\approx0$,
plus local errors. This is the precise form of the maintainer's "needs
$\mathbf p_j^T\mathbf A\mathbf p_{j-1}\approx0$". The multiplier is $1+\eta_{j-1}$, not a residual
ratio: the normalised defect *accumulates* ($|\bar p_j|\le 1.04\sum_{i\le j}|L_i|$) but is not
amplified. Bounding the pieces of $L_j$ (details: the ratio $\rho_j/\rho_{j-1}$ appears in
$(\mathbf r_{j-1}-\mathbf r_j)^T\mathbf e^p_j$, $\mathbf e^{rT}_{j-1}\mathbf p_j$ and the two $\mathbf e^s$ terms,
and is absorbed as $(\rho_j/\rho_{j-1})\beta_j\le 1.04\alpha_{j+1}$ or as
$\|\mathbf p_{j-1}\|\|\mathbf p_j\|/\rho_{j-1}^2\le 1.1(q_j+q_j^2)$):

$$|L_j|\le\varepsilon\Bigl[\,6\,\|\mathbf A\|(1+\Pi_j)^2+\alpha_{j+1}\,(13+5\,\Pi_j+2.1\,\kappa_{j-1})+3\,\beta_j(1+\Pi_j)\Bigr],$$
$$\boxed{\ |\bar p_j|\le 1.04\,(j+1)\,\varepsilon\Bigl[\,6\,\|\mathbf A\|(1+\Pi_j)^2+\max_{i\le j+1}\alpha_i\,(13+5\,\Pi_j+2.1\,K_j)+3\max_{i\le j}\beta_i\,(1+\Pi_j)\Bigr]\ }$$

Constants are unoptimised and must be re-derived in Lean. Compare Lanczos:
$|\bar p_j|\le 8(j+1)\varepsilon\|\mathbf H\|$ — the same $(j+1)$ shape, with $(1+\Pi)^2$ and $K$
instead of 1. (The single term $e^\mu_j/\rho_j^2$ admits the Kantorovich bound
$\varepsilon\frac{\kappa+1}{2\sqrt\kappa}\alpha_{j+1}$ instead of $\varepsilon\|\mathbf A\|\pi_j^2$;
the $\mathbf e^s$ terms do not, see §2.7.)

### 2.6 Lemma C (coefficients) and the small-$\varepsilon$ closure

From the recurrence with unit vectors: $\alpha_{j+1}\le\|\mathbf A\|+|\bar p_j|+1.04|\bar p_{j-1}|+\|\bar{\mathbf f}_j\|$
(exact: $\bar{\mathbf v}_{j+1}^T\mathbf A\bar{\mathbf v}_{j+1}=\alpha_{j+1}+\bar p_j+(1+\eta_{j-1})\bar p_{j-1}+\bar{\mathbf v}_{j+1}^T\bar{\mathbf f}_j$),
and $\beta_{j+1}\le\|\mathbf A\|+\alpha_{j+1}+1.04\beta_j+\|\bar{\mathbf f}_j\|$ (triangle inequality;
linear growth in $j$, as the library's `β_le : β j ≤ 5/4 j ‖H‖`). The system
{Lemma A, Lemma B, Lemma C} is coupled only through terms carrying a factor $\varepsilon$; under

$$\text{(H)}\qquad C_0\,k^2\,\varepsilon\,\bigl[(1+\Pi_k)^2+K_k\bigr]\le\tfrac1{100}$$

it closes by induction on $j$ to $\alpha_{j+1}\le 1.1\|\mathbf A\|$, $\beta_j\le 2.3\,j\|\mathbf A\|$,
and then

$$\|\bar{\mathbf f}_j\|\le C_1\,(j+1)\,\varepsilon\|\mathbf A\|(1+\Pi_k),\qquad |\bar p_j|\le C_2\,(j+1)^2\,\varepsilon\|\mathbf A\|\bigl[(1+\Pi_k)^2+K_k\bigr].$$

(With the HSCG-specific identity $\rho_{j+1}^2=a_j^2\|\mathbf s_j\|^2-\rho_j^2+2a_jb_{j-1}\zeta_j+\dots$
one gets $\beta_{j+1}\le 1.01\|\mathbf A\|\pi_j+\sqrt{2.1\,\alpha_{j+1}|\bar p_{j-1}|}+\dots$, i.e. no
$j$-growth but a $\Pi$ factor; either is poly$(k,\Pi)$.)

**Lemma D (a priori certificate).** Under $\alpha_{j+1}\le1.1\|\mathbf A\|$ and
$2.1\varepsilon\kappa(\mathbf A)\le1/100$: $\pi_j^2\le1.03\kappa(\mathbf A)\alpha_{j+1}/\|\mathbf A\|\le1.14\,\kappa(\mathbf A)$
and $\kappa_j\le1.04\kappa(\mathbf A)$. Hence (H) may be replaced by the a priori hypothesis
$\text{(H')}\ C_0'\,k^2\,\varepsilon\,\kappa(\mathbf A)\le 1/100$ (the induction on $j$ closes with a
fixed-point step: $X:=\alpha_{j+1}/\|\mathbf A\|$ satisfies $X\le1+\varepsilon\,\mathrm{poly}(k)\,\kappa\max(X,1.1)$,
so $X\le1.1$). The exact-arithmetic analogue is the classical $\|\mathbf p_j\|^2/\|\mathbf r_j\|^2\le\kappa$
(via $\|\mathbf A\|\|\mathbf p\|^2/\rho^2\le\kappa\cdot\mathbf p^T\mathbf A\mathbf p/\rho^2\le\kappa\,\alpha_{j+1}\le\kappa\|\mathbf A\|$).

**Conclusion of §2.** Define
$\varepsilon_{\mathrm{CG}}:=C\,k\,\varepsilon\bigl[(1+\Pi_k)^2+K_k\bigr]\le C'\,k\,\varepsilon\,\kappa(\mathbf A)$.
The data $(\mathbf A,\bar{\mathbf v},\alpha,\beta)$ are a `LanczosData` with exactly unit columns,
$\beta_j>0$, $\|\bar{\mathbf f}_j\|,|\bar p_j|\le\varepsilon_{\mathrm{CG}}\|\mathbf A\|$,
$\alpha,\beta\le\mathrm{poly}(k)\|\mathbf A\|$, and $k\varepsilon_{\mathrm{CG}}\le1/100$ — the
hypotheses actually consumed by `Backward.lean` (see §3.2). Everything downstream
(`frobNorm_backwardH_sub_dilatedH_le`, `lanczosTridiagonal_backwardH_dilatedStart`, Paige's
bound, Weyl/Wasserstein consequences) then applies with $\varepsilon_{\mathrm{CG}}$ in place of
$12(k+1)\varepsilon$.

### 2.7 Is the extra factor unavoidable?

For the *interface quantities* in the normwise model, yes; both the linear and the quadratic
dependence on $\Pi$ are attained by admissible error choices.

1. *Recurrence error, factor $\pi_j$.* $\bar{\mathbf f}_j$ is a function of the computed data and of
   $T_k$ only (it does not depend on how one builds a backward model), and
   $\bar{\mathbf f}_j\ni-(-1)^j\mathbf e^s_j/\rho_j$. Choose $\mathbf e^s_j=\varepsilon\|\mathbf A\|\|\mathbf p_j\|\,\mathbf w$
   with $\mathbf w$ a unit vector orthogonal to $\mathbf r_{j-1},\mathbf r_j,\mathbf r_{j+1}$ and to the
   other error directions (admissible: the contract bounds only $\|\mathbf e^s_j\|$). Then
   $\|\bar{\mathbf f}_j\|\ge\varepsilon\|\mathbf A\|\pi_j-(\text{other terms})$. Any run with
   $\pi_j\gg1$ (i.e. $\|\mathbf r_j\|\gg\min_{i\le j}\|\mathbf r_i\|$, a residual-norm peak) gives
   $\|\bar{\mathbf f}_j\|\gg\varepsilon\|\mathbf A\|$. Residual-norm peaks of size up to $\sqrt\kappa$
   exist in exact CG (any positive sequences $a_j,b_j$ are realised by some SPD $\mathbf A$ and
   $\mathbf r_0$: Hestenes–Stiefel 1952 Thm 18:3, as used by Gutknecht–Strakoš §9).
2. *Local orthogonality, factor $\pi^2$.* $L_j\ni-(1+\eta_{j-1})\,\mathbf p_{j-1}^T\mathbf e^s_j/\rho_{j-1}^2$.
   Choose $\mathbf e^s_j=\pm\varepsilon\|\mathbf A\|\|\mathbf p_j\|\,\mathbf p_{j-1}/\|\mathbf p_{j-1}\|$:
   $|L_j|\approx\varepsilon\|\mathbf A\|\,\pi_{j-1}\pi_j\,(\rho_j/\rho_{j-1})$. At a step where the
   residual norm jumps by $R$ with $\pi_{j-1}\approx1$ one has $\pi_j\approx\sqrt{1+R^2}$, so
   $|L_j|\approx\varepsilon\|\mathbf A\|R^2$, i.e. $\varepsilon\|\mathbf A\|\kappa$ for $R\approx\sqrt\kappa$.
   The $\mathbf e^s$-terms are the ones that cannot be improved by Kantorovich: the contract allows
   an error of norm $\varepsilon\|\mathbf A\|\|\mathbf p_j\|$ in any direction, including along
   $\mathbf p_{j-1}$, even when $\mathbf p_j$ is nearly an eigenvector of $\lambda_{\min}$.
   (In a componentwise model $|\Delta\mathbf A|\le\gamma|\mathbf A|$ the same size is reachable when
   $\||\mathbf A|\|\approx\|\mathbf A\|$ and the vectors are spread; the library's contracts are
   normwise anyway: `norm_eu_le : ‖eu‖ ≤ ε * specNorm H * ‖v‖`.)
3. *Whether a different backward construction avoids it* is open: the dilation's first block is
   $\bar{\mathbf V}\mathbf C$ with $\mathbf C=(\mathbf I+\bar{\mathbf R})^{-1}$, and
   $\Delta\hat{\mathbf V}=-\hat{\mathbf E}$ with $\hat{\mathbf E}$ built from $\bar{\mathbf F}$ by the
   exchange rule, so for *this* construction $\|\Delta\|\gtrsim\|\bar{\mathbf F}\|/\mathrm{poly}(k)$ is
   to be expected but I have not proved a lower bound; the question "does some exact Lanczos
   problem $(\tilde{\mathbf A},\tilde{\mathbf v})$ with $\|\tilde{\mathbf A}-\mathbf I\otimes\mathbf A\|\le\mathrm{poly}(k)\varepsilon\|\mathbf A\|$
   reproduce the computed $a_j,b_j$ regardless of $\Pi$?" is not settled here.

Sanity check (numerics, not evidence; `scratchpad/scripts/hscg_check.py`, double precision,
$u=2^{-53}$): on the GLC model problem (3.3) ($n=48$, $\kappa=10^3$), on a problem with two
eigenvalues $10^{-6}$ ($n=200$, $\kappa=10^6$) and on a well-conditioned problem ($\kappa=10$):
$\max_j\|\bar{\mathbf f}_j\|/(u\|\mathbf A\|(1+\pi_j))\in\{0.67, 2.6, 1.5\}$;
$\max_j|\bar p_j-\bar p_{j-1}|/(u\|\mathbf A\|(1+\pi_j)^2)\in\{0.17,0.93,0.56\}$ (the increments are
local, as Lemma B predicts), while $\max_j|\bar p_j|/(u\|\mathbf A\|)$ reached $8\cdot10^4$ in the
ill-conditioned run after $\pi_j$ had been $4\cdot10^2$ earlier (accumulation without decay);
$\max\pi_j\le0.42\sqrt\kappa$ in all runs; residual-norm increases occurred in 17 and 33 of the
steps of the first two runs. All consistent with §§2.4–2.6.

### 2.8 Alternatives considered

* **Direct dilation of the coupled two-term recurrences.** Equivalent, not better: once
  $\hat{\mathbf V}_{k+1}$ is orthonormal and satisfies the three-term recurrence exactly,
  $\hat{\mathbf P}:=\hat{\mathbf V}_k\,\mathrm{diag}(\rho)\,U^{-1}$ (with $U$ unit upper bidiagonal
  from the $b_j$) satisfies $\tilde{\mathbf A}\hat{\mathbf P}=\hat{\mathbf R}_{k+1}B$ exactly with the
  computed $a_j$ ($B$ lower bidiagonal with $1/a_j$); the perturbation is the same $\Delta$, and
  the interface quantities driving it are the same $\bar{\mathbf f}_j,\bar p_j$. Payoff: a clean
  corollary (exact CG on the model reproduces $a_j,b_j$ exactly and the updated residual norms to
  relative accuracy $1.6k\varepsilon$).
* **Other normalisations.** $\bar{\mathbf F}=\mathbf A\bar{\mathbf V}_k-\bar{\mathbf V}_{k+1}\underline{T}_k$
  depends only on $(\bar{\mathbf V},T)$; any model reproducing the computed $T_k$ from the
  normalised start has Lanczos vectors whose $n$-dimensional shadow is a rescaling of the
  $\mathbf r_j$. Normalising by $\|\mathbf p_j\|$ or working in the $\mathbf A$-inner product
  (where the $\mathbf p_j$ are the orthogonal family) moves $\sqrt\kappa$ factors into the
  norm equivalence instead of removing them.
* **$\kappa$-free alternatives are different theorems.** (i) Lanczos-CG (`cgIterate` through
  `lanczosMatrix`, Paige 2019 §14): the existing `LanczosRun` machinery applies verbatim and the
  only new work is the tridiagonal solve and $\mathbf x_k=\mathbf V_k\mathbf z_k$ — but it is not HSCG.
  (ii) The residual gap of HSCG,
  $\|(\mathbf b-\mathbf A\mathbf x_j)-\mathbf r_j\|\le O(j)\,\varepsilon\|\mathbf A\|(\|\mathbf x\|+\max_i\|\mathbf x_i\|)$
  (Greenbaum 1997; Strakoš–Tichý (7.16)): rigorous, local, no Lanczos reduction, no $\kappa$ — a
  cheap and useful target, orthogonal to the backward model.

---

## 3. Recommendation

### 3.1 Target (statement shape)

**Theorem (HSCG backward model, proposed).** Let $k$ steps of HSCG run on SPD $\mathbf A$ in the
kernel contract with parameter $\varepsilon$ (program-level: `IsRelErrSem`, $\varepsilon=\max(\varepsilon_{mv},\gamma_{N+c})$),
without breakdown, and let $\Pi_k=\max_{j<k}\|\mathbf p_j\|/\|\mathbf r_j\|$, $K_k=\max_j\kappa_j$ be
the run certificates. If $C_0k^2\varepsilon[(1+\Pi_k)^2+K_k]\le1/100$ then, with
$\varepsilon_{\mathrm{CG}}=Ck\varepsilon[(1+\Pi_k)^2+K_k]$, there is a symmetric
$\tilde{\mathbf A}\in\mathbb R^{n(k+1)\times n(k+1)}$ with
$\|\tilde{\mathbf A}-\mathbf I_{k+1}\otimes\mathbf A\|_F\le2000k^4\varepsilon_{\mathrm{CG}}\|\mathbf A\|$
such that exact Lanczos on $(\tilde{\mathbf A},\mathrm{col}(\mathbf r_0/\|\mathbf r_0\|,\mathbf 0,\dots))$
produces the tridiagonal matrix with entries $\alpha_{j+1}=1/a_j+b_{j-1}/a_{j-1}$,
$\beta_{j+1}=\|\mathbf r_{j+1}\|/(a_j\|\mathbf r_j\|)$ of the computed coefficients; equivalently
exact CG on $(\tilde{\mathbf A},\tilde{\mathbf b})$ produces the computed $a_j,b_j$ exactly and residual
norms $\|\mathbf r_j\|\prod_{i<j}(1+\eta_i)^{1/2}$. **Corollary** (a priori): if
$C_0'k^2\varepsilon\kappa(\mathbf A)\le1/100$ the hypothesis holds with
$(1+\Pi_k)^2+K_k\le 6\kappa(\mathbf A)$, so $\varepsilon_{\mathrm{CG}}\le C'k\varepsilon\kappa(\mathbf A)$.
Downstream: Paige's loss-of-orthogonality bound, Ritz values in
$[\lambda_{\min}-\delta,\lambda_{\max}+\delta]$, Wasserstein closeness of spectral measures — all
with $\varepsilon_{\mathrm{CG}}$. Not covered (say so in the docstring): the true residual
$\mathbf b-\mathbf A\mathbf x_j$ and attainable accuracy (separate gap theorem), and the $\mathbf A$-norm of
the error (Greenbaum 1989 Thm 3; genuinely harder).

Why this shape: it matches the library's existing style (hypotheses on the run as fields, e.g.
`abs_norm_v_sq_sub_one_le`), $\Pi_k$ and $K_k$ are computable a posteriori from the run, and the
$\kappa$-corollary gives the a priori statement the maintainer would quote. It is honest about
the extra factor instead of hiding it in "$\lesssim_k$".

### 3.2 Proof route

1. **Interface refactor (mechanical, do first).** `Backward.lean` and `BackwardSpectral.lean` use
   of `LanczosRun L` only: `L.normalized : LanczosData` with exactly unit columns
   (`norm_normalizedV`), `transpose_H`, `k_pos`, `β_pos`/`β_nonneg`,
   `norm_normalized_recurrenceError_le`, `abs_normalized_adjacentInner_le`, `β_le` (through the
   exchange-rule and Gram-commutator bounds), and $k\varepsilon\le1/100$. Extract a structure
   `NLAlib.PerturbedLanczos n k` (data `D : LanczosData n k`, `ε`, factor functions
   $c_f(j), c_p(j), c_\alpha(j), c_\beta(j)$, the bounds, unit columns, $\beta$ positivity,
   `k_mul_ε_le`) and restate `Backward*.lean` over it; `LanczosRun.toPerturbedLanczos` with
   $c_f=12(j+1)$, $c_p=8(j+1)$, $c_\beta=5j/4$ recovers the current theorems verbatim. Risk: the
   constants $160k^2$, $1000k^4$ were derived with these specific factor shapes; generalise them
   to $\max_j c_f(j)$ etc. (the Lean proofs bound sums by $k\cdot\max$ anyway).
2. **`HSCGRun n k`** (analogue of `LanczosRun`): fields $\mathbf r,\mathbf p,\mathbf s,a,b,\nu,\mu$, the
   error fields $\mathbf e^s,e^\mu,\theta,\delta,\delta',\mathbf e^r,\mathbf e^p$ with the contract
   bounds, no-breakdown ($\nu_j,\mu_j>0$), and certificate fields $\Pi, K$ with
   `pi_le : ‖p j‖ ≤ Π * ‖r j‖`, `kappa_le : ‖A‖ * a j * ‖p j‖^2 ≤ K * ‖r j‖^2`, and the smallness
   hypothesis (H). Program-level: `HSCGProgramRun` in the scaffold (same pattern as
   `LanczosProgramRun`), producing an `HSCGRun` with $\varepsilon=\max(\varepsilon_{mv},\gamma_{N+c})$.
3. **Lemma A** (§2.4): a short algebraic identity (`recurrenceError_eq`) plus norm bounds.
4. **Lemma B** (§2.5): three identities ($\tau$-recursion, $\sigma$ in terms of $\zeta$,
   $a_{j-1}\zeta_j$ via symmetry) then the $\bar p$-recursion and the sum bound.
5. **Lemma C/D** (§2.6): coefficient bounds by induction on $j$ and the fixed-point closure under
   (H); then the a priori corollary from (H').
6. **Assemble** `HSCGRun.toPerturbedLanczos` and instantiate the backward theorems; add the
   LDL$^T$ corollary (exact CG on the model reproduces $a_j,b_j$).

### 3.3 Risky step

Lemma B. It is where "the roundoff errors enter differently": the local orthogonality of the
normalised residuals is a telescoped quantity involving three computed inner-product identities,
the symmetry of $\mathbf A$ applied to *computed* products ($\mathbf s_j$ vs. $\mathbf A\mathbf p_j$), the
cancellation $b_{j-1}\rho_{j-1}^2-\rho_j^2=\rho_j^2\eta_{j-1}$, and residual ratios that must be
absorbed into $q_j$ or into $(\rho_j/\rho_{j-1})\beta_j\le1.04\alpha_{j+1}$ in the right places; any
slip reintroduces an unabsorbed $\rho_j/\rho_{j-1}$ and destroys the bound. Second risk: the
closure in Lemma C/D is a coupled induction whose smallness hypothesis must be stated once with
constants that are correct for *all* three lemmas (the Lanczos analogue had the much simpler
$k\varepsilon\le1/100$). Third (design, not mathematics): the interface refactor must keep the
Lanczos theorems and their constants unchanged; do it as a separate, reviewable commit.

### 3.4 What not to attempt now

A $\kappa$-free backward model for HSCG (§2.7(3)), the $\mathbf A$-norm error statement
(Greenbaum 1989 Thm 3), and the attainable-accuracy analysis through the backward model; the
latter two are separate projects, the first is an open question.

---

## References (as used above)

* Bake, Carson, Ma, *Forward and backward error bounds for a mixed precision preconditioned conjugate gradient algorithm*, arXiv:2510.11379 (v3, 2026). Abstract only.
* Carson, Liesen, Strakoš, *Towards understanding CG and GMRES through examples*, LAA 692 (2024) 241–291.
* Carson, Rozložník, Strakoš, Tichý, Tůma, *The numerical stability analysis of pipelined conjugate gradient methods: historical context and methodology*, SISC 40(5) (2018) A3549–A3580.
* Chen, *A simple stability analysis of the Lanczos algorithm in finite precision arithmetic*, arXiv:2608.21268 (2026); Lean: `tchen-research/simple-lanczos-stability`.
* Greenbaum, *Behavior of slightly perturbed Lanczos and conjugate-gradient recurrences*, LAA 113 (1989) 7–63. Cited via Meurant–Strakoš 2006 §§4.3, 5.2 and GLC 2021 §1.
* Greenbaum, *Estimating the attainable accuracy of recursively computed residual methods*, SIMAX 18 (1997) 535–551.
* Greenbaum, Liu, Chen, *On the convergence rate of variants of the conjugate gradient algorithm in finite precision arithmetic*, SISC 43(5) (2021) S496–S515; arXiv:1905.05874v2.
* Greenbaum, Strakoš, *Predicting the behavior of finite precision Lanczos and conjugate gradient computations*, SIMAX 13(1) (1992) 121–137.
* Gutknecht, Strakoš, *Accuracy of two three-term and three two-term recurrences for Krylov space solvers*, SIMAX 22(1) (2000) 213–229; TR V-764 (1997, with Paige).
* Hestenes, Stiefel, *Methods of conjugate gradients for solving linear systems*, J. Res. NBS 49 (1952); Thm 5:5, Thm 18:3.
* Meurant, Strakoš, *The Lanczos and conjugate gradient algorithms in finite precision arithmetic*, Acta Numerica 15 (2006) 471–542.
* Notay, *On the convergence rate of the conjugate gradients in presence of rounding errors*, Numer. Math. 65 (1993) 301–317.
* Paige, *Accuracy of the Lanczos process for the eigenproblem and solution of equations*, SIMAX 40(4) (2019) 1371–1398.
* Sinha, *Finite-precision symmetric Krylov methods: exact rounding examples, block Paige identities, and a variable-block Lanczos model*, arXiv:2609.08066 (2026). Abstract only.
* Strakoš, Tichý, *On error estimation in the conjugate gradient method and why it works in finite precision computations*, ETNA 13 (2002) 56–80.
