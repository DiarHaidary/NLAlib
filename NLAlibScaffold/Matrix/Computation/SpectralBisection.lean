/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisection
public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.Matrix.Computation.NewtonSchulzSign

/-!
# Deterministic analysis of randomized spectral bisection (scaffold)

Statements for `NLAlib/Matrix/Computation/SpectralBisection.lean` (stage HDIAG, wave W4, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.8): the local guarantee of one
node given its good events and the guarantees of its children ([Shah2024, Lemma 4.1]), the depth
of the recursion, the number of nodes and of splits, and the global deterministic guarantee: if
every internal node of the recursion tree has a good sample, the output is an approximate
diagonalization with residual $2\varepsilon R_0$ and singular values of $\mathbf{U}$ in
$[1 - \varepsilon/3, 1 + \varepsilon/3]$. The probability is in
`NLAlibScaffold/Eigensolvers/SpectralBisection.lean`.

## Main results

* `NLAlib.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`: Lemma 4.1.
* `NLAlib.eighNodeAt_eq_none_of_bisectionDepth_lt_length`: the depth.
* `NLAlib.encard_eighNodeAt_ne_none_le`, `NLAlib.encard_eighNodeAt_isSplit_le`: the counts.
* `NLAlib.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`: the global deterministic
  guarantee.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- **Rank recovery on Event I**: under the node hypotheses of
`NLAlib.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` (contracts, precision, step
limit, floor and range), for an internal node ($k \ge 2$, $R > \varepsilon R_0$) and a seed
$v \in [-1, 1]$ whose ideal shift $c' = (R/\ell)v$ is at distance at least $w$ from every
eigenvalue (Event I), the node's step splits exactly when $0 < i_+(\mathbf{A} - c'\mathbf{I}) < k$;
moreover then $k_+ = i_+(\mathbf{A} - c'\mathbf{I})$. [Shah2024, proof of Lemma 4.1], "the
estimates $k_\pm$ are the exact ranks".
Proof: the rounded shift is within $1.1Ru$ of $\mathbf{A} - c'\mathbf{I}$
(`NLAlib.IsUnifSampler`, `NLAlib.IsRoundingFn.specNorm_sub_roundDiag_le`), so its eigenvalues have
modulus $\ge w/2$; `NLAlib.IsMatMulErr.specNorm_cfc_sign_sub_newtonSchulzSign_le` (scale $2R$,
modulus $w/2$, accuracy $\beta$), `Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le` and
`NLAlib.IsRoundingFn.specNorm_sub_roundHermitian_le` put $\mathbf{P}_+$ within $\beta$ of the
true projector; its diagonal sum is within $k\beta$ of the trace
(`NLAlib.norm_apply_le_specNorm`), which is the inertia
(`Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign`); the rounded sum
(`NLAlib.IsRoundingFn.abs_sum_sub_roundedSum_le`) is within $1/4$ more, so `round` returns the
inertia; unfold `NLAlib.eighStep`. M, about 90 lines. -/
theorem eighStep_isSplit_iff_of_forall_le_abs_sub {P : EighPrimitives} {u τ Ω : ℝ} {μM : ℕ → ℝ}
    (hmm : IsMatMulErr u τ Ω μM P.mm)
    (hfl : IsRoundingFn u τ Ω P.fl) (hunif : IsUnifSampler u P.unif)
    {N signFuel : ℕ} {R₀ ρ w : ℝ} {y : EighNode}
    {smp : EighSample N} (hμM : 0 ≤ μM y.k)
    (hA : y.A.IsHermitian) (hR : specNorm y.A ≤ y.R) (hℓ : 20 ≤ y.ℓ) (hε : 0 < y.ε)
    (hε₁ : y.ε ≤ 1 / 8) (hR₀ : 0 ≤ R₀) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ y.R)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * y.R)) (bisectionSignTol y.k y.ε ρ y.ℓ / (16 * y.k)) + 1) * u ≤
        w / (4 * y.R) * bisectionSignTol y.k y.ε ρ y.ℓ)
    (hfuel : newtonSchulzSteps (w / (8 * y.R)) (bisectionSignTol y.k y.ε ρ y.ℓ / (16 * y.k)) ≤
      signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k) ≤ min (√(ρ / 2)) (y.ε * R₀))
    (hΩ : 16 * (y.R + y.k + √(Real.log (4 / ρ))) ≤ Ω)
    (hk : 2 ≤ y.k) (hRε : y.ε * R₀ < y.R) (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ y.A, w ≤ |e - y.R / y.ℓ * smp.1|) :
    (eighStep P N signFuel R₀ ρ y.A y.R y.ε y.ℓ smp).IsSplit ↔
      0 < inertiaPos (y.A - (y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ∧
        inertiaPos (y.A - (y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) < y.k := by
  sorry

/-- **The children of a good node satisfy the node invariant**: under the node hypotheses of
`NLAlib.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` (without the children's
guarantee), every child $y'$ of the node (`NLAlib.eighChild`) has a Hermitian matrix with
$\|\mathbf{A}'\|_2 \le R'$, its own window. [Shah2024, proof of Lemma 4.1], (4.10)–(4.13).
Proof: leaves have no child. A shift child (all eigenvalues on one side of $c'$, by
`NLAlib.eighStep_isSplit_iff_of_forall_le_abs_sub` and the inertia) has spectrum of
$\mathbf{A} \mp (R/2)\mathbf{I}$ in $[-(1/2 + 1/\ell)R, (1/2 + 1/\ell)R]$ since $\lvert c'\rvert
\le R/\ell$; add the diagonal rounding (`NLAlib.IsRoundingFn.specNorm_sub_roundDiag_le`,
`Matrix.IsHermitian.isHermitian_roundDiag`). A split child: `NLAlib.isHermitian_roundHermitian`;
for the norm, `Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq` gives the frame
$\mathbf{V}_\pm$ with spectrum of the compression in $[c', R]$ (resp. $[-R, c']$),
`NLAlib.IsMatMulErr.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` with Event II gives
$\|\mathbf{V}_\pm\mathbf{W}_\pm - \mathbf{Q}_\pm\|_2 \le \eta$, and the two products, the
Hermitian part and the rounding (`NLAlib.IsRoundingFn.specNorm_sub_roundHermitian_le`) add at most
$(2 + 2\eta)R\eta \le R/\ell$. M, about 120 lines. -/
theorem isHermitian_and_specNorm_le_of_eighChild_eq_some {P : EighPrimitives} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ}
    (hmm : IsMatMulErr u τ Ω μM P.mm) (hqr : IsQRErr u τ Ω μQ P.qr)
    (hfl : IsRoundingFn u τ Ω P.fl) (hunif : IsUnifSampler u P.unif)
    (hnormal : IsNormalSampler u cN P.normal) {N signFuel : ℕ} {R₀ ρ w : ℝ} {y : EighNode}
    {smp : EighSample N} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN)
    (hA : y.A.IsHermitian) (hR : specNorm y.A ≤ y.R) (hℓ : 20 ≤ y.ℓ) (hε : 0 < y.ε)
    (hε₁ : y.ε ≤ 1 / 8) (hR₀ : 0 ≤ R₀) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ y.R)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * y.R)) (bisectionSignTol y.k y.ε ρ y.ℓ / (16 * y.k)) + 1) * u ≤
        w / (4 * y.R) * bisectionSignTol y.k y.ε ρ y.ℓ)
    (hudefl : (4 * μQ y.k + 2 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤
      bisectionSignTol y.k y.ε ρ y.ℓ)
    (hfuel : newtonSchulzSteps (w / (8 * y.R)) (bisectionSignTol y.k y.ε ρ y.ℓ / (16 * y.k)) ≤
      signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k) ≤ min (√(ρ / 2)) (y.ε * R₀))
    (hΩ : 16 * (y.R + y.k + √(Real.log (4 / ρ))) ≤ Ω)
    (hgood : 2 ≤ y.k → y.ε * R₀ < y.R →
      IsEighGoodSample w (√(ρ / 2) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y smp)
    {b : Bool} {y' : EighNode} (hy' : eighChild P N signFuel R₀ ρ y smp b = some y') :
    y'.A.IsHermitian ∧ specNorm y'.A ≤ y'.R := by
  sorry

/-- **Local guarantee of a node of spectral bisection** (Lemma 4.1): let the primitives meet the
contracts `NLAlib.IsMatMulErr` $u$ $\tau$ $\Omega$ $\mu_{\mathrm{MM}}$, `NLAlib.IsQRErr` $u$
$\tau$ $\Omega$ $\mu_{\mathrm{QR}}$, `NLAlib.IsRoundingFn` $u$ $\tau$ $\Omega$,
`NLAlib.IsUnifSampler` $u$ and `NLAlib.IsNormalSampler` $u$ $c_{\mathrm N}$ with
$\mu_{\mathrm{MM}}(k), \mu_{\mathrm{QR}}(k), c_{\mathrm N} \ge 0$. Let the node $y$ have Hermitian
$\mathbf{A}$ of size $k$ with $\|\mathbf{A}\|_2 \le R$, $\ell \ge 20$, $0 < \varepsilon \le 1/8$,
let $R_0 \ge 0$, $0 < \rho \le 1$, $0 < w \le R$, and write $\beta$ for
`NLAlib.bisectionSignTol` $k$ $\varepsilon$ $\rho$ $\ell$ and
$N_y = N(w/(8R), \beta/(16k))$ (`NLAlib.newtonSchulzSteps`). Suppose
$$640\,k^{3/2}(8 + \mu_{\mathrm{MM}}(k))(N_y + 1)\,u \le \frac{w}{4R}\,\beta \,, \qquad
(4\mu_{\mathrm{QR}}(k) + 2\sqrt k(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(k) + 1)\,u \le \beta
\,,$$
the sign step limit is at least $N_y$, $0 \le \tau$,
$4k\tau \le \min(\sqrt{\rho/2}, \varepsilon R_0)$ and
$16(R + k + \sqrt{\log(4/\rho)}) \le \Omega$; that, when $k \ge 2$ and $R > \varepsilon R_0$, the
node's sample satisfies `NLAlib.IsEighGoodSample` with $w$, $x = \sqrt{\rho/2}/k$ and
$t = \sqrt2(2\sqrt k + \sqrt{2\log(4/\rho)})$; and that every child $y'$ of the node returns an
approximate diagonalization of its matrix with residual $\varepsilon'(R' + R_0)$ and singular
values within $\varepsilon'/3$ of $1$ (its own tolerance and window). Then the node returns an
approximate diagonalization (`NLAlib.IsApproxDiagonalization`) of $\mathbf{A}$ with residual
$\varepsilon(R + R_0)$ and singular values within $\varepsilon/3$ of $1$. [Shah2024, Lemma 4.1],
there with the probabilities of the events folded in, $R_0$-free bounds on the children's
$\|\mathbf{D}_\pm\|_2$ (the $R_0$ part is absorbed by the slack $\varepsilon R_0/\ell$), and
Events I–III as conditions.
Proof: unfold `NLAlib.eighAux` and `NLAlib.eighStep`. Leaves: $k \le 1$ is exact,
$R \le \varepsilon R_0$ has residual $\|\mathbf{A}\|_2 \le \varepsilon R_0$. Otherwise follow
[Shah2024, proof of Lemma 4.1]: the branch is the true one
(`NLAlib.eighStep_isSplit_iff_of_forall_le_abs_sub`, whose proof also gives
$\|\mathbf{P}_\pm - \mathbf{\Pi}_\pm\|_2 \le \beta$); the children satisfy the node invariant
(`NLAlib.isHermitian_and_specNorm_le_of_eighChild_eq_some`); on a split,
`Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq` gives
the frames $\mathbf{V}_\pm$ and
`NLAlib.IsMatMulErr.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` with Event II gives
$\|\mathbf{Q}_\pm - \mathbf{V}_\pm\mathbf{W}_\pm\|_2 \le \eta$; replace $\mathbf{V}_\pm$ by
$\mathbf{V}_\pm\mathbf{W}_\pm$. Then the source's estimates (4.14)–(4.20): the singular
values of $[\mathbf{W}_+\ \mathbf{W}_-]$, and the residual split into five terms, with
$\|\mathbf{D}_\pm\|_2$ bounded from the children's residual $\varepsilon'(R' + R_0)$ (its $R_0$
part, dropped by the source, is absorbed by the slack $\varepsilon R_0/\ell$). Split into private
lemmas: deflation, assembly of $\mathbf{U}$, residual. H, about 250 lines. -/
theorem isApproxDiagonalization_eighAux_succ_of_isEighGoodSample {P : EighPrimitives}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hmm : IsMatMulErr u τ Ω μM P.mm)
    (hqr : IsQRErr u τ Ω μQ P.qr) (hfl : IsRoundingFn u τ Ω P.fl)
    (hunif : IsUnifSampler u P.unif) (hnormal : IsNormalSampler u cN P.normal)
    {N signFuel f : ℕ} {R₀ ρ w : ℝ} {y : EighNode} {s : List Bool → EighSample N}
    (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hA : y.A.IsHermitian)
    (hR : specNorm y.A ≤ y.R) (hℓ : 20 ≤ y.ℓ) (hε : 0 < y.ε) (hε₁ : y.ε ≤ 1 / 8) (hR₀ : 0 ≤ R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ y.R)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * y.R)) (bisectionSignTol y.k y.ε ρ y.ℓ / (16 * y.k)) + 1) * u ≤
        w / (4 * y.R) * bisectionSignTol y.k y.ε ρ y.ℓ)
    (hudefl : (4 * μQ y.k + 2 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤
      bisectionSignTol y.k y.ε ρ y.ℓ)
    (hfuel : newtonSchulzSteps (w / (8 * y.R)) (bisectionSignTol y.k y.ε ρ y.ℓ / (16 * y.k)) ≤
      signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k) ≤ min (√(ρ / 2)) (y.ε * R₀))
    (hΩ : 16 * (y.R + y.k + √(Real.log (4 / ρ))) ≤ Ω)
    (hgood : 2 ≤ y.k → y.ε * R₀ < y.R →
      IsEighGoodSample w (√(ρ / 2) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y
        (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode), eighChild P N signFuel R₀ ρ y (s []) b = some y' →
      IsApproxDiagonalization y'.A
        (eighAux P N signFuel R₀ ρ f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1
        (eighAux P N signFuel R₀ ρ f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2
        (y'.ε * (y'.R + R₀)) (y'.ε / 3)) :
    IsApproxDiagonalization y.A (eighAux P N signFuel R₀ ρ (f + 1) y.A y.R y.ε y.ℓ s).1
      (eighAux P N signFuel R₀ ρ (f + 1) y.A y.R y.ε y.ℓ s).2 (y.ε * (y.R + R₀)) (y.ε / 3) := by
  sorry

/-- **The recursion stops by depth $\ell$**: for $0 < \varepsilon \le 2^{-15}$, $R_0 \ge 0$ and
$\ell = \lceil \log_2(1/\varepsilon) \rceil + 5$ (`NLAlib.bisectionDepth`), the tree of
`NLAlib.eighNodeAt` from the root $(\mathbf{A}, R_0, \varepsilon, \ell)$ has no node at a path
longer than $\ell$, for every primitives and samples. [Shah2024, proof of Theorem 4.2], "the
depth of the tree $d$ is no more than $\ell$".
Proof: a node at depth $j$ has window $R_j = R_0\prod_{i<j}(1/2 + 2/(\ell + i))$, tolerance
$\varepsilon_j = \varepsilon(\ell - 1)/(\ell + j - 1)$ and depth parameter $\ell + j$ (induction
on the path, unfolding `NLAlib.eighChild`); the products telescope:
$\prod_{i<\ell}(\ell + i + 4)/(\ell + i) = \frac{2\ell(2\ell+1)(2\ell+2)(2\ell+3)}
{\ell(\ell+1)(\ell+2)(\ell+3)} =: P_\ell$; with $2^{-\ell} \le \varepsilon/32$ (`Nat.le_ceil`,
`Real.rpow_logb`) it suffices that $P_\ell/32 \le (\ell - 1)/(2\ell - 1)$, i.e.
$(2\ell+1)(2\ell+3)(2\ell-1) \le 8(\ell-1)(\ell+2)(\ell+3)$, whose difference is
$20\ell^2 + 10\ell - 45 > 0$ for $\ell \ge 2$ (at $\ell = 20$: $0.4355 \le 0.487$), so
$R_\ell \le \varepsilon_\ell R_0$, and
the node at depth $\ell$ is a leaf of `NLAlib.eighStep`. M, about 60 lines. -/
theorem eighNodeAt_eq_none_of_bisectionDepth_lt_length (P : EighPrimitives) {N signFuel : ℕ}
    {R₀ ρ ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 ≤ R₀) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℂ) (s : List Bool → EighSample N) {a : List Bool}
    (ha : bisectionDepth ε < a.length) :
    eighNodeAt P N signFuel R₀ ρ a ⟨k, A, R₀, ε, bisectionDepth ε⟩ s = none := by
  sorry

/-- **The recursion tree has at most $(k + 1)(\ell + 1)$ nodes**: under the hypotheses of
`NLAlib.eighNodeAt_eq_none_of_bisectionDepth_lt_length`, the set of paths at which
`NLAlib.eighNodeAt` has a node has at most $(k + 1)(\ell + 1)$ elements, $k$ the size of the root.
[Shah2024, proof of Theorem 4.2], $\lvert X \rvert \le nd$ there.
Proof: below the root every node has size at least $1$, and the sizes of the nodes at one depth
sum to at most $k$ (a split partitions its size, a shift keeps it, a leaf has no child: unfold
`NLAlib.eighChild`, `NLAlib.eighStep`); with the depth bound, at most $k + 1$ nodes at each of the
depths $0, \dots, \ell$ (`Set.encard_le_card`-type counting over `List Bool` of bounded length,
`Set.encard_iUnion_le`). L, about 70 lines. -/
theorem encard_eighNodeAt_ne_none_le (P : EighPrimitives) {N signFuel : ℕ} {R₀ ρ ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 ≤ R₀) {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ)
    (s : List Bool → EighSample N) :
    {a : List Bool | eighNodeAt P N signFuel R₀ ρ a ⟨k, A, R₀, ε, bisectionDepth ε⟩ s ≠ none}.encard
      ≤ (k + 1) * (bisectionDepth ε + 1) := by
  sorry

/-- **At most $k$ nodes split**: for every root of size $k$, primitives and samples, the set of
paths at which `NLAlib.eighNodeAt` has a node whose step `NLAlib.eighStep` (with that path's
sample) is a split has at most $k$ elements. [Shah2024, proof of Theorem 4.2],
$\lvert X_D \rvert = n - 1$ there.
Proof: the tree may be infinite (chains of shifts), so do not induct on the size alone: prove
$S_m(x) \le \max(k - 1, 0)$ for the splits at paths of length at most $m$, by induction on $m$
uniformly in $x$ (a shift: $S_m(x) = S_{m-1}(x')$ with the same size; a split: children of sizes
$k_+, k - k_+ \ge 1$ and $\max(k_+ - 1, 0) + \max(k - k_+ - 1, 0) + 1 \le k - 1$; a leaf: $0$;
count with `Set.encard_union_le` over the paths starting with `true` and `false`), then pass to
the union over $m$ (`Set.encard_iUnion_le`-type monotone limit). L, about 80 lines. -/
theorem encard_eighNodeAt_isSplit_le (P : EighPrimitives) {N signFuel : ℕ} {R₀ ρ : ℝ}
    (x : EighNode) (s : List Bool → EighSample N) :
    {a : List Bool | ∃ y, eighNodeAt P N signFuel R₀ ρ a x s = some y ∧
      (eighStep P N signFuel R₀ ρ y.A y.R y.ε y.ℓ (s a)).IsSplit}.encard ≤ x.k := by
  sorry

/-- **Global deterministic guarantee of spectral bisection**: let the primitives meet the
contracts of `NLAlib.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` with
$\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$ monotone and nonnegative and $c_{\mathrm N} \ge 0$; let
$\mathbf{A} \in \mathbb{C}^{n \times n}$ be Hermitian with $\|\mathbf{A}\|_2 \le R_0$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $\ell$ = `NLAlib.bisectionDepth`
$\varepsilon$, and
$$\beta = \frac{\varepsilon\sqrt\theta}{2880\,\ell\, n^{3/2}\bigl(2\sqrt n +
\sqrt{2\log(16n/\theta)}\bigr)} \,, \qquad
N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac{\beta}{16n}\Bigr) \,.$$
Suppose $640\,n^{3/2}(8 + \mu_{\mathrm{MM}}(n))(N_* + 1)\cdot16n(n+1)\ell(\ell+1)\,u \le
\theta\beta$, $(4\mu_{\mathrm{QR}}(n) + 2\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u
\le \beta$, the sign step limit is at least $N_*$, $0 \le \tau$,
$4n\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon R_0/3)$ and
$16(R_0 + n + \sqrt{\log(16n/\theta)}) \le \Omega$. If every internal node $y$ (size at least
$2$, window above $\varepsilon_y R_0$) of the tree of `NLAlib.eighNodeAt` has a good sample
(`NLAlib.IsEighGoodSample` with $w_y = \theta R_y/(2k_y\ell_y(n+1)(\ell+1))$,
$x_y = \sqrt{\theta/(8n)}/k_y$, $t_y = \sqrt2(2\sqrt{k_y} + \sqrt{2\log(16n/\theta)})$), then
$\mathsf{eigh}(\mathbf{A}, \varepsilon, \theta)$ (`NLAlib.eigh`) is an approximate
diagonalization of $\mathbf{A}$ with residual $2\varepsilon R_0$ and singular values within
$\varepsilon/3$ of $1$. [Shah2024, Theorem 4.2], deterministic part.
Proof: induct on the fuel with the node-level hypotheses as a predicate over paths (the
children's trees are `eighNodeAt a y' (fun a' => s (b :: a'))` definitionally, so no snoc lemma
is needed); the depth is at most $\ell$ (`NLAlib.eighNodeAt_eq_none_of_bisectionDepth_lt_length`),
so the budget $\ell + 1$ of `NLAlib.eigh` is never exhausted. Treat leaves directly ($k \le 1$
exact; $R \le \varepsilon_y R_0$ residual $\le \varepsilon_y R_0$; the local lemma's $0 < w$
fails at a leaf with $R_y = 0$). At an internal node apply
`NLAlib.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`, its matrix hypotheses coming
from the parent through `NLAlib.isHermitian_and_specNorm_le_of_eighChild_eq_some` (at the root from
`hA`, `hR₀`), and its parameter hypotheses from the depth $j$: $k_y \le n$,
$\ell \le \ell_y \le 2\ell$,
$\varepsilon_y \ge \varepsilon/3$, $R_y \le R_0$, hence `NLAlib.bisectionSignTol` at $y$ is at least
$\beta$, $w_y/(4R_y) \ge \theta/(16n(n+1)\ell(\ell+1))$ and $N_y \le N_*$
(`NLAlib.newtonSchulzSteps_le_of_le_abs`, `NLAlib.newtonSchulzSteps_le_of_le`, monotone $\mu$).
At the root $R = R_0$ gives residual $2\varepsilon R_0$. H, about 200 lines. -/
theorem isApproxDiagonalization_eigh_of_forall_isEighGoodSample {P : EighPrimitives}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hmm : IsMatMulErr u τ Ω μM P.mm)
    (hqr : IsQRErr u τ Ω μQ P.qr) (hfl : IsRoundingFn u τ Ω P.fl)
    (hunif : IsUnifSampler u P.unif) (hnormal : IsNormalSampler u cN P.normal)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {R₀ ε θ : ℝ}
    (hR₀ : specNorm A ≤ R₀) (hε : 0 < ε) (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : ℓ = bisectionDepth ε) {β : ℝ}
    (hβ : β = ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * β)
    (hudefl : (4 * μQ n + 2 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (4 * n) ≤ min (√(θ / (8 * n))) (ε * R₀ / 3))
    (hΩ : 16 * (R₀ + n + √(Real.log (16 * n / θ))) ≤ Ω) {s : List Bool → EighSample n}
    (hgood : ∀ (a : List Bool) (y : EighNode),
      eighNodeAt P n signFuel R₀ (θ / (4 * n)) a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        y.ε * R₀ < y.R →
        IsEighGoodSample (θ * y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1))) (√(θ / (8 * n)) / y.k)
          (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (16 * n / θ)))) y (s a)) :
    IsApproxDiagonalization A (eigh P signFuel A R₀ ε θ s).1 (eigh P signFuel A R₀ ε θ s).2
      (2 * ε * R₀) (ε / 3) := by
  sorry

end NLAlib
