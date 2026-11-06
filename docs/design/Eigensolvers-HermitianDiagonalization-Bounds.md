# Design note: a sharper precision bound for Hermitian diagonalization (stage HDIAG-BOUNDS)

Status: research and design. Skeleton written (20 sorried statements, `NLAlibScaffold/`); nothing
dispatched, nothing pushed. No proved statement is changed: every improvement is a **new** theorem
next to the old one. Branch `research/hdiag-bounds` (worktree `~/nlalib-research-hdiag-bounds`),
stacked on `cleanup/hdiag` bd81bd1d (pushed as `feat/hdiag`, merge pending). Parent note:
`docs/design/Eigensolvers-HermitianDiagonalization.md` (§3.12 corrections, §16 status). Decision
sheet `~/nlalib-harness/state/decisions/HDIAG-BOUNDS.json`; targets
`~/nlalib-harness/pilot/hdiag-bounds-targets.json` (20: S 1, M 10, L 7, H 2). The closed-form
evaluator behind every number below is `~/nlalib-harness/research/hdiag/bounds/{ev7,pkg}.py`.

**Method** (maintainer's rule). Every improvement is derived analytically, from the Lean proofs'
own intermediate bounds or from the literature. Numerics only evaluate closed forms at the four test
points $(n, \varepsilon, \theta) = (1, 2^{-15}, 1)$, $(10, 2^{-15}, 1)$, $(1000, 2^{-15}, 1)$ and
$(1000, 2^{-40}, 1/2)$, with $\mu_{\mathrm{MM}} = \mu_{\mathrm{QR}} = 1$, $c_{\mathrm N} = \sqrt2$
and $\ell = \lceil\log_2(1/\varepsilon)\rceil + 5$. These are the conventions of Fable's stage
review. Labels:
- **proven**: a Lean theorem, or a short complete argument given here;
- **known**: in the literature, cited;
- **derived**: my algebra on the existing proof routes; the statements carry margins but are not
  machine-checked;
- **conjectured**: plausible, not derived in full.

At $n = 1$ the algorithm returns at the root, so the bound is vacuous in substance. It is
evaluated there only as asked.

## 0. Summary

| | EV7 (proved) | EV7' (this note, stated) | paper Thm 4.2 |
|---|---|---|---|
| $n = 1$, $\varepsilon = 2^{-15}$, $\theta = 1$ | 66.7 | **49.1** | 48.3 |
| $n = 10$, $\varepsilon = 2^{-15}$, $\theta = 1$ | 83.0 | **58.6** | 63.6 |
| $n = 1000$, $\varepsilon = 2^{-15}$, $\theta = 1$ | 119.5 | **74.9** | 94.5 |
| $n = 1000$, $\varepsilon = 2^{-40}$, $\theta = 1/2$ | 149.5 | **105.4** | 124.0 |

EV7' is $\log_2(1/\varepsilon) + \tfrac32\log_2(1/\theta) + \log_2\bigl(n(4\mu_{\mathrm{MM}} + 10 +
10\sqrt n)\bigr) + \tfrac12\log_2(n\min(n, \ell+1)\min(n, e)) + \log_2\hat T + 3\log_2\ell +
O(1)$, with $\hat T \approx 2\sqrt{2n}$. So:
- the polynomial factor is $n^{2.5}\max(\mu_{\mathrm{MM}}, \sqrt n)$ for $n \le \ell$ and
  $n^{2}\sqrt\ell\max(\mu_{\mathrm{MM}}, \sqrt n)$ beyond. EV7 has $n^5\mu_{\mathrm{MM}}$ and
  the paper $n^{4.5}\mu_{\mathrm{MM}}$;
- the $\log_2(N_*+1)$ term (the paper's $\log_2\log_2(n\log_2(1/\varepsilon)/\theta)$) is gone;
- the constant is $13 + \log_2 20$, against 26.

**Caveat on the comparison.** The paper assumes $\mu_{\mathrm{MM}} \ge 10$ (out.tex l. 226, used at
l. 1283), so its formula at $\mu = 1$ is outside its own derivation and the $\mu = 1$ convention
favours it. At $\mu_{\mathrm{MM}} = \mu_{\mathrm{QR}} = 10$: paper 51.1 / 66.9 / 97.8 / 127.3, EV7'
50.5 / 59.4 / 75.1 / 105.6. At $n = 1$ the auxiliary (stopping and deflation) condition of EV7'
is the binding one (49.1 against 49.0).

**Binary64 stays out of reach.** The stated EV7' asks for 52.1 bits at $n = 2$ and 53.9 at
$n = 3$ ($\varepsilon = 2^{-15}$, $\theta = 1$, and $\varepsilon \le 2^{-15}$ is a hypothesis).
So $p = 53$ suffices only for $n \le 2$, and at $\theta = 1/2$ only for $n = 1$. Even with the
unrecommended algorithm and model changes (I11, I12) it reaches only $n \le 3$.

**Binary128 now covers practical sizes.** At $\varepsilon = 2^{-15}$, $\theta = 1$ it needs 99.7
bits at $n = 10^6$; EV7 covered only $n \lesssim 400$. At $\varepsilon = 2^{-40}$, $\theta =
1/2$ it covers $n \le 1000$ (105.4 bits) but not $10^4$ (113.6).

**Bits saved by each item, added alone to EV7.** The four columns are the test points in the
order above. The items are not additive; the package total is in the table above.

| item | what | bits saved | Lean effort | new statements |
|---|---|---|---|---|
| I0 | state the two precision conditions as a max, exact constants | 1.3, 0.3, 0.3, 0.2 | S | EV7' |
| I1 | $\beta$ within $1 + 2^{-6}$ of its bound (was a factor 2) | 1.0, 1.0, 1.0, 1.0 | S | EV7' |
| I2 | sharp $\varepsilon_y \ge (\ell-1)\varepsilon/(2\ell-1)$ at the deepest node (was $\varepsilon/3$, with 2880) | 0.9, 0.9, 0.9, 0.9 | M | EB2a', EB5' |
| I3 | Event I charge proportional to the node size (drops the factor $n+1$), $\sum_j\ell_j = \tfrac32\ell(\ell+1)$, $\theta$ split $\tfrac23 : \tfrac13$ | 1.6, 4.2, 10.9, 10.9 | L | EB3', EV6', EB5' |
| I4 | Event II charge proportional to the node size | 0, 0, 2.8, 2.2 | M | EV6', EB5' |
| I5 | $\mathbb{P}[\sigma_{\min} \le x] \le \min(r^2, e r)x^2$ (was $r^2x^2$) | 0, 0.9, 4.3, 4.3 | L | CG7, CG6', DP1', EV2' |
| I6 | norm tail $e^{-t^2}$ above $\sqrt2(\sqrt m + \sqrt n)$ (was $2e^{-t^2/2}$ above $\sqrt2(\sqrt m + \sqrt n + t)$) | 0.8, 0.7, 0.5, 0.5 | M | CG4', DP1', EV2' |
| I7 | Procrustes constant $\sqrt2$ (was 6) and rounding charged at $\beta/16$ (factor 3 becomes $1 + 1/8$) | 3.6, 3.6, 3.6, 3.6 | M + L | DF1', DF2', DP1' |
| I8 | SN3 with $\sqrt n$ only on the rounding term: $4\mu + 10 + 10\sqrt n$ (was $4\sqrt n(8 + \mu)$) | 0.6, 1.3, 1.8, 1.8 | M | SN3' |
| I9 | SN4 with geometric error propagation: no $(N_0 + 1)$; the stopping test's $16n$ in a separate condition | 7.6, 11.3, 18.6, 18.7 | L | NS13, SN4' |
| I10 | EB1c feeds SN4 the modulus $w$, not $w/2$ | 1.1, 1.0, 1.0, 1.0 | M | EB1c' |
| I11 | *(algorithm change)* sign scale $(1 + 2/\ell)R$ (was $2R$) | 2.0, 1.9, 1.9, 2.0 (0.8 on top of the package) | L | not in the skeleton |
| I12 | *(model change)* exact halving | 1.0, 2.1, 3.0, 3.0 (0.4–1.2 on top) | M–L | not in the skeleton |
| — | node-dependent $\beta_x$ as in the paper | 0 beyond I2 | M–L | none (§1.2) |
| — | recovering G1's $\sqrt n$ by mirroring | $< 0.6$ after I8, negative for $\mu_{\mathrm{MM}} \gtrsim \sqrt n/\log n$ | H | none (§1.4) |
| — | recovering G2's $\ell$ by a fixed-width shift | 0.9 ($2^{-15}$), 2.0 ($2^{-40}$), conjectured | L–H, algorithm change | none (§1.5) |

**Recommended package:** I0–I10 (the skeleton; 20 statements: S 1, M 10, L 7, H 2). Its derived
value is 48.5, 58.1, 74.4, 104.9 bits; the stated EV7' (constants rounded up for margin) gives
49.1, 58.6, 74.9, 105.4.

A smaller first phase, the sign and accounting items without new Gaussian tails or deflation
constants (I0–I3, I8–I10), gives 52.9, 63.2, 85.5, 115.4.

## 1. Analysis

### 1.1 Where EV7's bits go

EV7 is proved by exponentiating `hbits` into the two conditions of EB5:
- `husign`: $640n^{3/2}(8+\mu)(N_*+1)\cdot16n(n+1)\ell(\ell+1)u \le \theta\beta$;
- `hudefl`: $(4\mu_{\mathrm{QR}} + 4\sqrt n(c_{\mathrm N}+1) + 2\mu_{\mathrm{MM}} + 1)u \le
  \beta$;

with $\beta \ge \beta_*/2$ and $\beta_* = \varepsilon\sqrt\theta/(2880\ell n^{3/2}S)$
(`Global.lean`, `mul_le_mul_and_mul_le_of_mul_le_mul_sqrt`). Factor by factor (**proven**, by
reading the proofs):

* **$n^4(n+1)$** is the product of three factors:
  - $n^{3/2}$ from $\beta$: $k$ from CG6's $r^2x^2$ (so $x = \sqrt{\rho/2}/k$), and $\sqrt n$ from
    $\rho = \theta/(4n)$;
  - $n(n+1)$ from the Event I distance $w_y = \theta R_y/(2k_y\ell_y(n+1)(\ell+1))$: an equal
    charge on each of at most $(n+1)(\ell+1)$ nodes (EB3);
  - $n^{3/2}$ from SN4: $\sqrt n$ is G1 (SN3), and $n$ is the componentwise stopping test,
    $10\delta \le \varepsilon/(16n)$.

  SN4's condition is a *product* $160n\delta(N_0 + 1) \le (a/b)\varepsilon$, so the stopping
  test's $n$ multiplies the binding term although it is needed only in a separate condition
  $\approx 52n\delta \le \varepsilon$. The subagent's reading of `NewtonSchulzSign.lean:742–835`
  (lines 774, 780) confirms this.
* **$2^{26} \ge 58\,982\,400 = 5760 \cdot 640 \cdot 16$.**
  - $5760 = 2 \cdot 2880$. The 2 is `hβge`. $2880 = 360 \cdot 8$, where $360 = 5$ (from $\eta =
    \varepsilon'/(5\ell)$) $\cdot\, 36 \cdot 2$ (from $\sqrt\rho$), and the 8 is $\varepsilon_y \ge
    \varepsilon/3$ together with $\ell_y \le 2\ell$ and rounding slack. The 36 itself is $6$ (DF1)
    $\cdot\, 3$ ($\|\mathbf{S}\|_2 + 2$ in DP1) $\cdot\, \sqrt2$ (CG4) $\cdot\, \sqrt2$ (from $x$).
  - $640 = 10 \cdot 16 \cdot 4$: the scalar lemma's $10u \le \varepsilon$, the tolerance
    $\varepsilon/(16n)$, and the 4 of SN3.
  - $16 = 2 \cdot 2 \cdot 2 \cdot 2$: Event I's half of $\theta$, $\ell_y \le 2\ell$, the
    modulus $w/2$ in EB1c (`Projectors.lean:388`), and the scale $b = 2R$.
* **$3\log_2(\ell+1)$**: $\eta \propto 1/\ell$; the $\ell + 1$ levels of the union bound; and G2's
  density $\ell_y/(2R)$.
* **$\log_2(N_* + 1)$**: the telescoped sign errors, $(N_0+1)\cdot 2\delta/s$.

### 1.2 Node-dependent $\beta_x$ (item 2 of the brief): no bits

**Proven.** The precision $u$ is one number, so it must satisfy the precision conditions at every
node, and the binding node has $k_y = n$ at depth $\approx \ell$. Such a node exists:
- for $\mathbf{A} = 0$ every shift leaves the whole spectrum on one side, so every node is a
  one-child node of size $n$;
- by EB2's telescoping the recursion runs to depth $\lceil\log_2(1/\varepsilon)\rceil + 4 \approx
  \ell - 1$;
- there $\ell_y \approx 2\ell$ and $\varepsilon_y \approx \varepsilon/2$.

At that node the paper's $\beta_x$ equals the global $\beta$ of EB5 up to the constant fixed by I2.
The paper's own bit count takes $\min_x \beta_x$ (its equations (a70) and (a73),
out.tex l. 1240 and 1270) and evaluates it at $n_x = n$, $\varepsilon/3$, $2\ell$.

Node dependence shortens the sign iterations at shallow or small nodes; that is runtime, which is
out of scope (OQ11 of the parent note). It would cost an algorithm change: $\beta_x$ is a function
of $(k, \varepsilon_y, \ell_y)$ needing $\sqrt\cdot$ and $\log$, or a table of precomputed
thresholds. EB1c/EB1/EB5 would need restating for little gain.

**Not recommended**; the attainable gain is I2 (0.9 bits), which needs no node dependence.

### 1.3 The sign function: I8, I9, I10

**I8: SN3' (derived from the Lean proof).**
- SN3's proof bounds the error of the Hermitian part of the product by $D \le (3.23\mu +
  6.23)u$ (`NewtonSchulzSign.lean:305`), and the rounding of `hermAvg` by $3u(2\sqrt n + 1)$
  (`:313`, `EntrywiseRounding.lean:458`).
- It then multiplies $D$ by $\sqrt n$ only to package the result as $4\sqrt n(8 + \mu)$
  (`:329–335`).
- Adding the two terms gives $(3.23\mu + 9.23 + 6\sqrt n)u \le (4\mu + 10 + 10\sqrt n)u =: \nu u$.

**I9: SN4' (derived).**
- Let $a_k$ be the least eigenvalue modulus of the $k$-th stored iterate, and $\delta = \nu u$.
- While $a_k \le 1/2$: $g(a) \ge \tfrac{11}{8}a$ there (NS13, **proven**: $g(a)/a = (3 -
  a^2)/2$), so with Weyl $a_{k+1} \ge \tfrac{11}{8}a_k - \delta \ge 1.325a_k$, using $\delta \le
  a_0/20$.
- Afterwards $a_k \ge 1/2$ (NS9).
- By SG2 a step moves the sign by at most $2\delta/g(a_k)$. Summing, the propagated error is at
  most
  $$\frac{2\delta}{1.375 a_0}\cdot\frac{1}{1 - 1/1.325} + 2.91\,\delta\,(N_0 + 1) \le
  \frac{5.93\,\delta}{a_0} + 2.91\,\delta\,(N_0+1) \,,$$
  a geometric series in place of SN4's $(N_0+1)\cdot 2\delta/s$.
- The stated second condition carries 640, not 160, so that it implies SN4's private-lemma
  hypothesis $640n(8+\mu)u \le \varepsilon$ for every $n$ (Fable F1); the budget's `stop_tol`
  (2048) already covers it, so no bit count moves.
- The stopping test spends $\tfrac23\varepsilon$ as in SN4, and the start error $2\sqrt n u$
  costs $\le \varepsilon/160$.
- So $32\nu u \le (a/b)\varepsilon$ together with $640(n + N_0 + 1)\nu u \le \varepsilon$ suffice
  (budget used: $0.19 + 0.006 + 0.045 \le 1/3$).

The second condition carries the stopping test's $n$ and the step count; in the bisection it is
non-binding by 5–8 bits (the auxiliary condition of EV7'). This removes from the binding condition:
- the factor $(N_* + 1)$, i.e. $\log_2(N_*+1) = 5.3$–$6.4$ bits;
- the stopping test's $16n$;
- the constants 10 and 4 of the scalar route.

The step count $N(x_0, \varepsilon) = 5/2 + 2\log_2(1/x_0) + \log_2\log_2(1/\varepsilon)$ is the
paper's. Its 2 is the "squared defect" route; the true linear rate gives $1/\log_2 1.5 = 1.71$.
After I9 it only sizes the fuel, so tightening NS10 (L) is **not recommended**.

**I10: EB1c' (derived).** EB1c has the modulus $w - 4uR$ available (`Projectors.lean:300`), but
calls SN4 with $a = w/2 + 2uw$ (`:388`). With $a = w - 4uR \ge (1 - 2^{-8})w$ and $b =
\mathrm{fl}(2R) \le 2R(1 + 7u)$ we get $a/b \ge (1 - 2^{-7})w/(2R)$.

**I11 (algorithm change, not recommended).**
- $b$ only needs $\|\mathbf{A} - c\mathbf{I}\|_2 \le (1 + 1/\ell)R + 4uR$
  (`Projectors.lean:298`), so the scale $\mathrm{fl}(\mathrm{fl}(1 + \mathrm{fl}(2/\ell))R)$ would
  save another 0.8 bits.
- But it changes `eighStep`, every node lemma and the COMPDYN S1cd refinement.

### 1.4 Gap G1: the $\sqrt n$ of the Hermitian rounding

**Genuine in the model (proven by example).**
- The stored iterate is the entrywise-rounded Hermitian part of a product near $2g(\mathbf{X})$.
- An entrywise relative perturbation $|E_{ij}| \le u|Z_{ij}|$ of a near-unitary $\mathbf{Z}$
  can have spectral norm $u\sqrt n\|\mathbf{Z}\|_2$. Take $\mathbf{Z} = \mathbf{H}/\sqrt n$ for a
  symmetric Hadamard $\mathbf{H}$ (unitary, a valid sign matrix) and $E_{ij} = u/\sqrt n = u\lvert Z_{ij}\rvert$ (all signs $+$);
  then $\mathbf{E} = (u/\sqrt n)\mathbf{J}$, of norm $u\sqrt n$.
- Every route that applies a rounded entrywise operation to all $n^2$ entries per step pays this.
- The halving in $g(x) = \tfrac12x(3 - x^2)$ is such an operation in the current model, which
  rounds every division (parent note §2.0).

**After I8 the cost is additive**: $\nu = 4\mu_{\mathrm{MM}} + 10 + 10\sqrt n$. G1 costs
$\log_2(\nu/(4\mu + 10))$, which is under 1 bit once $\mu_{\mathrm{MM}}(n) \gtrsim \sqrt n$ (true
of the normwise constant of every practical gemm). Under the review's $\mu = 1$ convention it is
4.6 bits at $n = 1000$.

**Ways back, none recommended now:**
1. **Exact halving** (I12, a model change). A contract field "division by `ofNat 2`/`ofNat 4`
   is exact up to $u\tau$" holds for binary formats with gradual underflow. Then `hermAvg`
   rounds once (the add), and the $\sqrt n$ coefficient drops from about 9 to about 3.
   That gives 0.4–1.2 bits on top of the package. Cost: a new `IsAccurate` field (or a
   structure extending it), re-proofs of C1/C1b, and SN3' in a variant.
2. **Mirroring instead of averaging.** Store the strict upper triangle and mirror it exactly
   (`hermFrom`); with exact halving no entry is rounded. The error is then $H(\mathbf{F}) =
   T(\mathbf{F}) + T(\mathbf{F})^{\mathsf H} + \operatorname{Re}\operatorname{diag}\mathbf{F}$ for
   the product error $\mathbf{F}$. The triangular truncation $T$ has norm $\Theta(\log n)$
   (**known**: Kwapień–Pełczyński; an elementary dyadic bound gives $\lceil\log_2 n\rceil$). So
   the step error is $(2\lceil\log_2 n\rceil + 1)(3.3\mu + 6.3)u$: better than $\nu$ only while
   $\mu\log n \lesssim \sqrt n$, and worse for realistic $\mu$. The parent note's OQ8(c) estimate
   "$\sqrt{2n}$" is the Frobenius bound; the operator bound is $O(\log n)$. This is H (the
   truncation lemma, a new step and SN1–SN4 variants) for less than 0.6 bits at $n = 1000$ after
   I8.
3. Not Hermitizing at all, as the paper does, needs a non-normal sign perturbation: the paper's
   contour Lemma 2.2, with its factor $n$. That is worse.

### 1.5 Gap G2: the factor $\ell$ in Event I

**Genuine for this algorithm (proven).** The ideal shift is uniform on $[-R/\ell, R/\ell]$
(density $\ell/(2R)$); a spectrum of $k$ well-separated eigenvalues excludes $2kw$ of it, so
$\mathbb{P}[\text{Event I fails}] = kw\ell/R$ exactly. EV1 is sharp.

**A fixed-width shift (conjectured, algorithm change).**
- A shift of half-width $\alpha R$ makes the density factor $1/\alpha$, but the child window
  becomes $(1/2 + \alpha + 1/\ell)R$.
- EB1's residual budget (the parent's §3.8: $(R' + R_0)\varepsilon' + \tfrac13R\varepsilon' +
  4R\eta \le (R + R_0)\varepsilon$) then forces $\alpha \lesssim 1/2 - 1/3 - 1.8/\ell$, about
  $0.07$ at $\ell = 20$.
- The depth grows by $1/\log_2(1/(1/2 + \alpha))$, and with it the $\ell$ inside $\eta$ and in
  the level count.
- With $\alpha = 1/16$ the net saving is $\log_2(2\ell\alpha) - 2\log_2(\ell_{\mathrm{new}}/\ell)$:
  about 0.9 bits at $\varepsilon = 2^{-15}$ and 2.0 bits at $2^{-40}$.
- It changes Algorithm 3, EB1–EB5, EV1–EV7 and the depth bound. **Not recommended now**; it is a
  research question for the maintainer (decision G2).

**The other two powers of $\ell$ are forced by the analysis.**
- $\eta \propto \varepsilon/\ell$ because the deviation of $\mathbf{U}$ from unitary adds up
  along a root-to-leaf path: a product of $d$ matrices with singular values in $[1 \pm \eta]$ is
  only within $(1 \pm \eta)^d$.
- The level count is the union bound over $\ell + 1$ depths, each charged equally (I3 already
  uses $\sum_j \ell_j = \tfrac32\ell(\ell+1)$ in place of $(\ell+1)\cdot2\ell$).
- The constant in $\eta = \varepsilon'/(5\ell)$ could be $\varepsilon/(4.25\ell)$, worth 0.3
  bits. Not pursued.

### 1.6 The union bound: I3 and I4 (new)

**I3, Event I (derived; the counting is proven by the structure of the tree).**
- At each depth the sizes of the nodes sum to at most $n$: a node has no child, one child of its
  size, or children of sizes $k_+$ and $k - k_+$. This is EB3', and it is also the paper's
  "$\sum_{x\in X_k} n_x \le n$", used there only for runtime.
- Charge node $y$ in proportion to its size: $w_y/R_y = c$ constant. Then $\sum_y k_y\ell_y c \le
  cn\sum_{j=0}^{\ell}(\ell + j) = \tfrac32cn\ell(\ell+1)$.
- With Event I's share $\tfrac23\theta$ this gives $w_y = 4\theta R_y/(9n\ell(\ell+1))$, against
  EV6's $\theta R_y/(2k_y\ell_y(n+1)(\ell+1))$, which is $\ge \theta R_y/(4n(n+1)\ell(\ell+1))$.
- The binding node ($k_y = n$) gains the factor $\tfrac{16}{9}(n+1)$.
- The paper's $w_x = \theta R_x/(2n_x n d)$ has the same $n_x n$ waste; it is fixed here.

**I4, Event II (derived).**
- Splits are charged $2\rho_y$ with $\rho_y = \theta k_y/(6nm)$, where $m = \min(n, \ell + 1)$.
  The split sizes sum to at most $n\min(n, \ell+1)$: per depth by EB3', and over at most $n$
  splits (EB4).
- Since $\beta_y \propto \sqrt{\rho_y}/(k_y\cdots)$ is still decreasing in $k_y$, the binding node
  is still $k_y = n$. There $\sqrt\rho$ improves by $\sqrt{n/m}$, which is a gain only for
  $n > \ell + 1$ (≤ 0.1 bit loss below, from the $\log(1/\rho)$ inside $t$).

**The $\theta$ split.** It is optimal at $\tfrac23 : \tfrac13$ because $\theta$ enters Event I
linearly and Event II under a square root: $\min_s[\log_2(1/s) + \tfrac12\log_2(1/(1 - s))]$ is
attained at $s = 2/3$. Worth 0.1 bits.

**$\tfrac32\log_2(1/\theta)$ is inherent** to a union bound with these tails, both of them sharp:
- Event I is exactly linear in $w$;
- the complex $\sigma_{\min}$ tail is exactly quadratic in $x$ [Edelman1988].

Removing it needs boosting by residual checks and restarts (the paper's closing remark), an
algorithm change out of scope.

### 1.7 Gaussian tails: I5, I6

**I5, CG6' (known argument, complex version derived).** Edelman's exact law for an $r \times r$
standard complex Gaussian is $\mathbb{P}[\sigma_{\min} \le x] = 1 - e^{-rx^2} \le rx^2$
[Edelman1988]. Its proof needs the complex Wishart density, which the library lacks (no Jacobian
of $\mathbf{G} \mapsto \mathbf{G}^{\mathsf H}\mathbf{G}$, no matrix densities): **H**, not
recommended.

The probe argument of [SankarSpielmanTeng2006, Lemma 3.2] gives $e\,rx^2$ instead. The steps:
1. Take an independent Gaussian probe $\mathbf{g}$. Then $\|\mathbf{G}^{-1}\mathbf{g}\| \ge
   \|\mathbf{G}^{-1}\|_2\,\lvert\mathbf{b}^{\mathsf H}\mathbf{g}\rvert$, and given $\mathbf{G}$,
   $\lvert\mathbf{b}^{\mathsf H}\mathbf{g}\rvert^2 \sim \mathrm{Exp}(1)$.
2. $\|\mathbf{G}^{-1}\mathbf{g}\|^2 \stackrel{d}{=} \|\mathbf{g}\|^2\,
   \|\mathbf{G}^{-1}\mathbf{e}_1\|^2$ by left unitary invariance, and $\|\mathbf{G}^{-1}
   \mathbf{e}_1\| = 1/\operatorname{dist}(\text{row}_1, \text{other rows})$.
3. That distance has the CG5 small-ball tail. So $\mathbb{P}[\|\mathbf{G}^{-1}\mathbf{g}\|^2 \ge
   T] \le r/T$.
4. Hence $e^{-s}\,\mathbb{P}[\sigma_{\min} \le x] \le rx^2/s$; take $s = 1$.

Everything except the exponential upper tail (CG7, M) and a row version of CG6's distance
helper exists. The real template is `RandomMatrix/Gaussian/InverseMoments/Spectral.lean`
(`specNorm_mul_dotProduct_sq_le`), which is moment-based and real, so the complex square case
must be a tail argument (L).

A CG5-only variant gives $4rx^2$ (0.3 bits worse), via $\mathbb{P}[\lvert z\rvert^2 \ge s] \ge
1 - s$. DP1' uses $\min(r^2, e\,r)$, so nothing is lost at $r \le 2$.

**Bits:** $\beta \propto x \propto 1/\sqrt{\min(k^2, ek)}$, a gain of $\tfrac12\log_2(n/e)$ for
$n \ge 3$.

**I6, CG4' (derived).** CG4 loses on three counts:
- the triangle inequality $\|\mathbf{G}\| \le (\|\mathbf{G}_1\| + \|\mathbf{G}_2\|)/\sqrt2$;
- a union bound over the two parts;
- and with them the exponent $t^2/2$ (`Complex.lean:338–357`).

The map $X \mapsto \|(X_1 + iX_2)/\sqrt2\|_2$ is $2^{-1/2}$-Lipschitz for the Frobenius norm of
the realification, so the library's Gaussian concentration
(`measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix`) gives $e^{-t^2}$ above the mean. The
mean is $\le \sqrt2(\sqrt m + \sqrt n)$ by the triangle inequality and the real mean bound (M).

The sharp mean $\sqrt m + \sqrt n$ is **conjectured** true (Haagerup–Thorbjørnsen-type results)
but not reachable by comparison. For the real process $\operatorname{Re}(\mathbf{u}^{\mathsf
H}\mathbf{G}\mathbf{v})$ the Sudakov–Fernique increments fail: phase rotations $\mathbf{u}' =
e^{i\theta}\mathbf{u}$, $\mathbf{v}' = e^{-i\theta}\mathbf{v}$ give a ratio of about 2. It is H
and worth about 0.5 bits more. Not recommended.

### 1.8 Deflation constants: I7

**DF1' (proven here, standard).**
- From $\|\mathbf{U} - \mathbf{Q}'\mathbf{C}\|_2 \le \delta$: for a unit $v$,
  $\|\mathbf{Q}'^{\mathsf H}\mathbf{U}v\|^2 = 1 - \|(\mathbf{I} -
  \mathbf{Q}'\mathbf{Q}'^{\mathsf H})\mathbf{U}v\|^2 \ge 1 - \delta^2$.
- Take $\mathbf{W}$ the polar factor of $\mathbf{U}^{\mathsf H}\mathbf{Q}'$, so
  $\mathbf{W}^{\mathsf H}\mathbf{U}^{\mathsf H}\mathbf{Q}' = \mathbf{P} \succeq 0$.
- Then $(\mathbf{U}\mathbf{W} - \mathbf{Q}')^{\mathsf H}(\mathbf{U}\mathbf{W} - \mathbf{Q}') =
  2(\mathbf{I} - \mathbf{P})$.
- Hence $\|\mathbf{U}\mathbf{W} - \mathbf{Q}'\|_2^2 = 2(1 - \sigma_{\min}) \le 2(1 - \sqrt{1 -
  \delta^2}) \le 2\delta^2$.

This is the orthogonal Procrustes bound $\max_i 2\sin(\theta_i/2)$ [StewartSun1990, Chapter I.5].
DF1 has $6\delta$ (the paper's three inequalities).

**DF2' (derived).** DF2's factor $\|\mathbf{S}\|_2 + \beta + 1$ comes from charging the sampler,
product and QR roundings at the full $\beta$ (`hudefl`). Charging them at $\beta/16$ costs 4 bits
in the non-binding deflation condition. The factor becomes $1 + 2\beta + \|\mathbf{S}\|_2/8$, and
with DF1' the output error is $\tfrac32m\beta$ (margin over $\sqrt2$ for the QR error and the
$O(m\beta)$ terms at $m\beta \le 1/64$).

For a projector ($\mathbf{S} = \mathbf{I}$) the node tolerance $\beta = \eta x/(18T)$ becomes
$\beta = \eta x/(2t)$ (the `defl_tol` field), a factor 9 in the derivation and 3.6 bits in the
evaluator.

### 1.9 Other constants

| constant | verdict |
|---|---|
| 2880 | becomes $52\ell^2(2\ell-1)/(\ell-1)^2 \approx 104\ell$ in EV7', i.e. $\eta$ at the deepest node with the sharp $\varepsilon_y$ (I2), with the deflation constants of I5–I7 inside |
| 640 | removed (I9) |
| 16 | becomes $\tfrac{9}{2}$ from I3 and I10 (the two genuine factors $\ell_y$ and $2R$ remain) |
| `husign` | becomes $146n\ell(\ell+1)\nu u \le \theta\beta$ |
| `hudefl` | non-binding after I0 |
| $N_*$ | removed from the bound (I9) |
| $3\log_2\ell$ | stays (§1.5) |
| $+5$ in $\ell$ | $+4$ would save 0.2 bits; not pursued |

## 2. Objects and interfaces (CONTRIBUTING §8 items 1–2)

One new definition, `NLAlib.FloatMachine.IsEighNodeBudget` (a `Prop` structure, §5.4): the
precision hypotheses of one node of [Shah2024, Lemma 4.1], **generic in the good-event parameters
$(w, x, t)$**.
- The node lemmas EB1c–EB1 repeat the same 17-hypothesis block, which hard-wires $x =
  \sqrt{\rho/2}/k$ and $t = \sqrt2(2\sqrt k + \sqrt{2\log(4/\rho)})$ through `bisectionSignTol`.
- The structure decouples the deterministic node analysis from the probabilistic choice of
  $(x, t)$. The deflation tolerance becomes the single field `defl_tol : 2t\beta/x \le \eta`.
- Any later sharpening of the Gaussian tails then touches EV2' and EB5' only.

Its raw-condition constructor is the anonymous constructor, with fields in the docstring's order.
Mathlib bridge: none (searched: no hypothesis bundle for a randomized recursion). No other new
definitions: `bisectionSignTol` is not replaced; the new tolerance is an explicit formula
(OQ10(a) of the parent note).

## 3. Statement shapes (item 3)

The exact signatures are in the skeleton:

| file | statements |
|---|---|
| `NLAlibScaffold/RandomMatrix/Gaussian/Complex.lean` | CG7, CG4', CG6' |
| `NLAlibScaffold/Matrix/Computation/Deflation.lean` | DF1', DF2' |
| `NLAlibScaffold/Eigensolvers/RandomizedDeflation.lean` | DP1' |
| `NLAlibScaffold/Polynomial/Approximation/NewtonSchulz.lean` | NS13 |
| `NLAlibScaffold/Matrix/Computation/NewtonSchulzSign.lean` | SN3', SN4' |
| `NLAlibScaffold/Matrix/Computation/SpectralBisection.lean` | `IsEighNodeBudget`, EB1c', EB1b', EB1d', EB1a', EB1', EB2a', EB3', EB5' |
| `NLAlibScaffold/Eigensolvers/SpectralBisection.lean` | EV2', EV6', EV7' |

Each statement has a docstring with the LaTeX statement, a citation, and a `Proof:` line with its
difficulty.

| id | declaration | diff | depends on |
|---|---|---|---|
| CG7 | `measureReal_le_normSq_le_of_hasLaw_complexGaussian` | M | — |
| CG4' | `measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix` | M | — |
| CG6' | `measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix` | L | CG7 |
| DF1' | `HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul` | M | — |
| DF2' | `FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le` | L | DF1' |
| DP1' | `FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix'` | M | DF2', CG4', CG6' |
| NS13 | `mul_abs_le_abs_newtonSchulz_of_abs_le` | S | — |
| SN3' | `FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add` | M | — |
| SN4' | `FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le` | L | SN3', NS13 |
| EB1c' | `FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget` | M | SN4' |
| EB1b' | `FloatMachine.IsAccurate.eighStep_isSplit_iff_of_isEighNodeBudget` | M | EB1c' |
| EB1d' | `FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget` | L | EB1c', EB1b', DF2' |
| EB1a' | `FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_isEighNodeBudget` | M | EB1d', EB1b' |
| EB1' | `FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget` | H | EB1c', EB1b', EB1d', EB1a' |
| EB2a' | `FloatMachine.IsAccurate.mul_le_dec_ε_of_eighNodeAt_eq_some` | M | — |
| EB3' | `sum_k_eighNodeAt_ofFn_le` | L | — |
| EB5' | `FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample'` | H | EB1', EB1a', EB2a' |
| EV2' | `FloatMachine.IsAccurate.measure_not_isEighGoodSample_le_of_isEighNodeBudget` | L | EB1b', DP1', CG4', CG6' |
| EV6' | `FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw'` | L | EB5', EV2', EB3' |
| EV7' | `FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw'` | M | EV6' |

Longest chain (9 waves): NS13/SN3' → SN4' → EB1c' → EB1b' → EB1d' → EB1a' → EB1' → EB5' → EV6'
→ EV7'.

**EV7'**, in bits:
$$\log_2\frac1u \ge \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta +
\log_2\bigl(n\nu\bigr) + \tfrac12\log_2\bigl(nm\min(n, e)\bigr) + \log_2\hat T +
\log_2(\ell(\ell+1)) + \log_2\frac{\ell^2(2\ell-1)}{(\ell-1)^2} + 13 \,,$$
with:
- $\nu = 4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n$, $m = \min(n, \ell+1)$ and $\hat T = 2\sqrt2\sqrt
  n + \sqrt{\log(96nm/\theta)}$;
- $\hat\beta/(1 + 2^{-6}) \le \beta \le \hat\beta$, where $\hat\beta = (\ell-1)^2\varepsilon
  \sqrt\theta/(52\ell^2(2\ell - 1)\sqrt{nm\min(n,e)}\,\hat T)$;
- the non-binding condition $\log_2(1/u) \ge \log_2(1/\beta) + \log_2(2048(n + N_* + 1)\nu +
  16(4\mu_{\mathrm{QR}} + 4\sqrt n(c_{\mathrm N}+1) + 2\mu_{\mathrm{MM}} + 1))$.

The constant: $146 \cdot 52 \cdot (1 + 2^{-6}) = 7711 \le 2^{13}$. It includes margins:
- 32 in SN4' against the derived 19;
- 2 in `defl_tol` against 1.6;
- 146 against 145.1.

Without the margins the derived bound is 0.5 bits lower.

**Risk.** Two earlier HDIAG statements were false as first written (parent §3.12), and these 20
are derived, not proved. The likeliest repairs are in side conditions: smallness facts that the
old proofs took from `bisectionSignTol` (`Projectors.lean:83`, `mul_le_of_le_bisectionSignTol`)
and that the budget restates as `mul_β_le` and the 2048 of `stop_tol`. They would not touch the
binding constants.

## 4. Consumers (item 4)

* EV7' replaces EV7 as the stage's precision claim. EV8' (exponent bits from EV7') is a
  follow-up target, to be written once EV7' is proved; its range now contains $\hat T$.
* `IsEighNodeBudget` and the generic node lemmas: any change of the Gaussian start or of the tail
  bounds, and the COMPDYN S2 version of EIGH (§15 of the parent note).
* CG4', CG6', CG7: every complex Gaussian argument (the parent's §5); CG6' is the complex
  counterpart of the real inverse-moment probe.
* DF1': any subspace-to-basis conversion (range finders, rank-revealing QR).
* SN4': any inverse-free sign iteration; its geometric propagation is the reusable part.
* EB3': runtime counts (OQ11 of the parent), which need exactly the per-depth size sum.

## 5. Files and placement (item 5)

Scaffold paths mirror the homes, each the file of the statement it sharpens:
- `RandomMatrix/Gaussian/Complex.lean` (CG7, CG4', CG6');
- `Matrix/Computation/Deflation.lean` (DF1', DF2');
- `Eigensolvers/RandomizedDeflation.lean` (DP1');
- `Polynomial/Approximation/NewtonSchulz.lean` (NS13);
- `Matrix/Computation/NewtonSchulzSign.lean` (SN3', SN4');
- `Matrix/Computation/SpectralBisection/` (`IsEighNodeBudget` and EB1c'/EB1b' in `Projectors`,
  EB1d' in `Split`, EB1a' in `Child`, EB1' in `Node`, EB2a'/EB3' in `Tree`, EB5' in `Global`;
  one scaffold file here);
- `Eigensolvers/SpectralBisection.lean` (EV2') and its `Global` (EV6', EV7').

`Node.lean` is already over 1000 lines (F10 warning); EB1' would push it to about 1400. Split it
at the move: generic matrix assembly to a Matrix file, as the stage report suggests.

Other changes:
- `docs/references.bib`: `SankarSpielmanTeng2006` added (cited by CG6').
- `lakefile.toml`: the `NLAlibScaffold` library entry, as on the HDIAG design branch; removed at
  the move.

## 6. Material (item 6)

Read:
- the paper's §§2–4 (out.tex, Lemma 3.1, Lemma 4.1 and the proof of Theorem 4.2);
- EV6–EV8, EB1–EB5, EB1a–d, EV2, SN3, SN4, DF1, DF2, DP1, CG4–CG6, NS10 and `newtonSchulzSteps`
  in `NLAlib`;
- the library's Gaussian comparison, concentration, χ² and inverse-moment files (two subagent
  surveys);
- the Fable reviews of the stage.

Reused:
- SN3's intermediate bounds (I8);
- SN4's stopping-test part (I9);
- DF1's polar-factor facts (DF1');
- DP1's event split;
- EV6's union-bound assembly with UB1;
- the real probe template for CG6'.

Deliberately not reproduced:
- Edelman's Wishart density (H, see I5);
- the sharp complex Gordon mean (H, I6);
- triangular-truncation norms (§1.4).

Searched, none:
- a complex Wishart density;
- a uniform measure on the complex sphere (the Gaussian probe avoids it);
- an exponential tail lemma for `complexGaussian`;
- a node-hypothesis bundle.

## 7. Open questions (item 7; recommendations in bold, one line each on the sheet)

1. **Scope.**
   - **(a) the full package I0–I10 (20 targets)**;
   - (b) phase 1, the sign and accounting items only (I0–I3, I8–I10; 52.9 / 63.2 / 85.5 / 115.4
     bits);
   - (c) defer.

   (a) Everything in it is M or L except EB1' and EB5', which are copies of proved H proofs.
2. **CG6' route.**
   - **(a) the probe argument with CG7, $e\,rx^2$**;
   - (b) the CG5-only variant, $4rx^2$ (no exponential law, 0.3 bits worse);
   - (c) Edelman's exact law (H).
3. **Old statements at clean-up.**
   - **(a) replace**: keep the primed versions under the old names and delete EV6/EV7/EV8, EB5,
     EB1–EB1d and EV2 at the move, with EV8 re-proved from EV7'. Keep SN3, SN4, DF1, DF2, DP1 and
     CG4, CG6 as general lemmas (CG6 is used by DP1');
   - (b) keep both sets.

   The primed statements are not literal generalizations, since $\beta$'s admissible window
   differs, so (a) is a maintainer decision.
4. **Exact halving in the model (I12).**
   - **(a) not now**;
   - (b) add a halving-exactness field later with the bounded bridge.
5. **Sign scale $(1 + 2/\ell)R$ (I11).**
   - **(a) no** (0.8 bits; it changes `eighStep` and the S1cd refinement);
   - (b) yes.
6. **G2 by a fixed-width shift.**
   - **(a) record as an open research question; no change**;
   - (b) design it (algorithm change, about 1–2 bits).
7. **Node-dependent $\beta_x$.**
   - **(a) do not pursue** (0 bits, §1.2);
   - (b) pursue for runtime only.
8. **Dispatch timing.**
   - **(a) after `feat/hdiag` is on main, from a fresh run worktree, at `--parallel 2`; EB1' and
     EB5' straight to dedicated Opus provers** (as last time);
   - (b) now, stacked on `cleanup/hdiag`.
