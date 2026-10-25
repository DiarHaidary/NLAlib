/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.GeneralizedNystrom
public import NLAlib.LowRank.Gaussian.RotationInvariant
public import NLAlibScaffold.LowRank.Gaussian.RotationInvariantFactor

/-!
# Epperly and Webber's factors are sharp for rotation-invariant test matrices

For a test matrix with a left unitarily invariant law and full column rank almost surely
(Gaussian, Haar, ...), the library proves Epperly and Webber's sharp upper bounds: Nyström and the
randomized SVD with the factor <!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$ over matrices of rank at most $r$, and
generalized Nyström with that factor times the co-range completion factor. This file shows the
factors cannot be lowered: for every constant below the factor some matrix of rank $r$ has a
larger expected error. The instance is $\operatorname{diag}(a\mathbf{I}_q, \mathbf{I}_{r-q},
\mathbf{0})$
for large $a$
(`NLAlib.tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant`).
These are Epperly and Webber's Theorems 3.3, 3.6(b) and 4.2(b) for rotation-invariant laws; their
versions for an arbitrary full-rank law (an extra Haar rotation of the instance) are deferred
(design note, §4). Real. Design: `docs/design/LowRank-EstimatorLowerBounds.md` §3.3. Proofs
deferred.

## Main results

* `NLAlib.exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant`: Nyström.
* `NLAlib.exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant`: the randomized SVD.
* generalized Nyström,
  [Gaussian co-range](https://nla-lib.org/explore/#d/NLAlib.exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix)
  and
  [Haar co-range](https://nla-lib.org/explore/#d/NLAlib.exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}
  [DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
  [IsLeftUnitarilyInvariant ν]

/-- **Epperly and Webber's Nyström factor is sharp**: for a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely, $q + 2 \le \ell \le r \le n$ and every
$c$ below the factor, <!-- value rotationInvariantFactor r \ell q -->
$$c < \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is a positive semidefinite $\mathbf{H}$ of rank $r$ with
$$c\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_* <
\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_*\,.$$
The matching upper bound is
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le`.
[EpperlyWebber2026, Theorem 3.6(b)]; there for every full-rank law (with a Haar rotation of the
instance), here for left unitarily invariant laws, which need none.
Proof: M, about 70 lines. Take $s = $ `Fin q`, $t = $ `Fin (r - q)`, an isometry
$\mathbf{V} \in \mathbb{R}^{n \times (s \oplus t)}$ (`exists_hasOrthonormalCols_range_eq` or a
selection matrix after `Fintype.equivFin`) and $\mathbf{H}_a =
\mathbf{V}\mathbf{D}_a\mathbf{V}^{\mathsf{H}}$,
$\mathbf{D}_a = \operatorname{diag}(a\mathbf{I}_s, \mathbf{I}_t)$. Then
$\mathsf{nystrom}(\mathbf{H}_a, \mathbf{X}) = \mathbf{V}\mathsf{nystrom}(\mathbf{D}_a,
\mathbf{V}^{\mathsf{H}}\mathbf{X})\mathbf{V}^{\mathsf{H}}$ (`nystrom_conjTranspose_mul_mul`), the
trace
norm is unchanged, $\mathbf{V}^{\mathsf{H}}\mathbf{X}$ has a left unitarily invariant law (extend an
orthogonal map of $s \oplus t$ to $n$) and full column rank a.s. (through the polar factor,
`ae_rank_mul_eq_min_of_hasLaw_haarFrame`). The limit
`tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant` at $b = 1$ and
$\|\mathbf{H}_a - \llbracket\mathbf{H}_a\rrbracket_q\|_* = \lvert t\rvert > 0$ for $a \ge 1$ give
$a$ with the strict inequality (`Filter.Tendsto.eventually_gt_atTop`-type, `eventually_ge_atTop`);
$\operatorname{rank}\mathbf{H}_a = r$ for $a > 0$.
Result: randomized-nystrom-lower-bound -/
theorem exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrn : r ≤ Fintype.card n) {c : ℝ}
    (hc : c < rotationInvariantFactor r (Fintype.card l) q) :
    ∃ H : Matrix n n ℝ, H.PosSemidef ∧ H.rank = r ∧
      c * nuclearNorm (H - truncatedSVD H q) < ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ := by
  sorry

/-- **Epperly and Webber's randomized SVD factor is sharp**: for a test matrix $\mathbf{X}$ with a
left unitarily invariant law and full column rank almost surely, $q + 2 \le \ell \le r$,
$r \le \min(m, n)$ and every $c$ below the factor, <!-- value rotationInvariantFactor r \ell q -->
$$c < \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2\,.$$
The matching upper bound is
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le`.
[EpperlyWebber2026, Theorem 3.3]; there for every full-rank law, here for left unitarily
invariant laws.
Proof: S, about 30 lines. The Gram correspondence: for $\mathbf{H}$ from
`exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant` write
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$ with $\mathbf{A} \in \mathbb{R}^{m \times n}$ of
rank $r$
($r \le m$: an isometry $\mathbb{R}^{r} \to \mathbb{R}^m$ times $\mathbf{H}^{1/2}$ compressed to its
range, `CFC.sqrt`, `exists_hasOrthonormalCols_range_eq`); then
`nuclearNorm_conjTranspose_mul_self_sub_nystrom` and
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD` turn both sides into the Frobenius ones.
Result: randomized-svd-lower-bound -/
theorem exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {c : ℝ} (hc : c < rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 < ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  sorry

-- A docstring line and the declaration name exceed 100 characters.
set_option linter.style.longLine false in
/-- **Epperly and Webber's generalized Nyström factor is sharp, Gaussian co-range**: for a test
matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely, an
independent standard Gaussian $\mathbf{\Psi}$ ($m \times p$), $q + 2 \le \ell \le r$,
$r \le \min(m, n)$, $\ell + 2 \le p$ and every $c$ below the factor, that
is <!-- value gaussianProjectionFactor \ell p --> <!-- value rotationInvariantFactor r \ell q -->
$$c < \Bigl(1 + \frac{\ell}{p - \ell - 1}\Bigr)
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{X}, \mathbf{\Psi})\|_{\mathsf{F}}^2\,.$$
So generalized Nyström needs $k' + \ell = \Theta(q/\varepsilon^2)$ for relative error
$1 + \varepsilon$ (Epperly and Webber, §4.2). The matching upper bound is
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix_of_rank_le`.
[EpperlyWebber2026, Theorem 4.2(b)]; there for every full-rank pair of laws and an orthonormal
co-range, here for a left unitarily invariant range law and a Gaussian co-range ($\gamma = 1$).
Proof: S, about 30 lines. The identity
`integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix` (any law of
$\mathbf{X}$) with $\operatorname{rank}(\mathbf{A}\mathbf{X}) = \ell$ a.s. for
$\operatorname{rank}\mathbf{A} \ge \ell$
(polar factor and `ae_rank_mul_eq_min_of_hasLaw_haarFrame`) gives the factor
`gaussianProjectionFactor ℓ p` times the randomized SVD error; apply
`exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant` at
$c / (1 + \ell/(p - \ell - 1))$ (`one_le_gaussianProjectionFactor`).
Result: generalized-nystrom-lower-bound -/
theorem
    exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (hlp : Fintype.card l + 2 ≤ Fintype.card p) {c : ℝ}
    (hc : c < gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
      rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 <
        ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ := by
  sorry

-- A docstring line and the declaration name exceed 100 characters.
set_option linter.style.longLine false in
/-- **Epperly and Webber's generalized Nyström factor is sharp, random orthonormal co-range**: for
a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
an independent $m \times p$ Haar frame $\mathbf{\Psi}$, $q + 2 \le \ell \le r$, $r \le \min(m, n)$,
$\ell + 2 \le p \le m$ and every $c$ below the
factor, <!-- value haarProjectionFactor m p \ell --> <!-- value rotationInvariantFactor r \ell q -->
$$c < \Bigl(1 + \frac{m - p}{m - \ell}\cdot\frac{\ell}{p - \ell - 1}\Bigr)
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{X}, \mathbf{\Psi})\|_{\mathsf{F}}^2\,.$$
The matching upper bound is
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame_of_rank_le`.
[EpperlyWebber2026, Theorem 4.2(b)]; there for every full-rank pair of laws, here for a left
unitarily invariant range law and a Haar co-range ($\gamma = (d - k)/(d - \ell)$ in their letters).
Proof: S, about 30 lines. As the Gaussian co-range version, with
`integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_haarFrame`'s conditional
form (`integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame` for a fixed range test
matrix, integrated) and `one_le_haarProjectionFactor`.
Result: generalized-nystrom-lower-bound -/
theorem
    exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame
    [DecidableEq p] (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hΨ : HasLaw Ψ (haarFrame m p) μ) (hXΨ : IndepFun X Ψ μ) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (hlp : Fintype.card l + 2 ≤ Fintype.card p)
    (hpm : Fintype.card p ≤ Fintype.card m) {c : ℝ}
    (hc : c < haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
      rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 <
        ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ := by
  sorry

end NLAlib
