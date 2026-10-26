/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Uniqueness

/-!
# The polar factor of a Gaussian matrix is independent of its Gram matrix (scaffold)

Statement for `NLAlib/RandomMatrix/Haar/Uniqueness.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.2): the Gaussianization step of the
Krylov coupling. A tall standard Gaussian matrix is its polar factor, a Haar frame, times the
square root of its Gram matrix, and the two factors are independent; so replacing the polar factor
by any Haar frame independent of the Gram matrix gives a standard Gaussian matrix again.

## Main results

* `NLAlib.indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k]

/-- **Polar factor and Gram matrix of a Gaussian matrix are independent**: for a standard Gaussian
$\mathbf{G} \in \mathbb{R}^{n \times k}$, the polar factor
$\mathbf{G}(\mathbf{G}^{\mathsf{H}}\mathbf{G})^{-1/2}$, a Haar frame, is independent of
$\mathbf{G}^{\mathsf{H}}\mathbf{G}$ when $\lvert k \rvert \le \lvert n \rvert$. (For a wide
$\mathbf{G}$ it is not: the Gram matrix fixes the row space of the polar factor.)
[Meckes2019, Ch. 1]; locator to verify.
Proof: for a Haar $\mathbf{O} \in O(n)$ independent of $\mathbf{G}$, $\mathbf{O}\mathbf{G}$ is
standard Gaussian (`NLAlib.hasLaw_mul_mul_of_hasLaw_gaussianMatrix`, frozen in $\mathbf{O}$ by
`ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq`), with polar factor
$\mathbf{O}\,\mathrm{polar}(\mathbf{G})$ and the same Gram matrix. So the pair
$(\mathrm{polar}(\mathbf{G}), \mathbf{G}^{\mathsf{H}}\mathbf{G})$ has the law of
$(\mathbf{O}\,\mathrm{polar}(\mathbf{G}), \mathbf{G}^{\mathsf{H}}\mathbf{G})$, and given the second
coordinate the first is left invariant on the Stiefel manifold (orthonormal columns a.s. for
$\lvert k \rvert \le \lvert n \rvert$), hence Haar
(`NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`
for the conditional law, or directly: the joint law is the product of the Haar frame law and the law
of the Gram matrix, tested on rectangles). Rank-deficient $\mathbf{G}$ has probability zero
(`NLAlib.ae_rank_eq_min_of_hasLaw_gaussianMatrix`). L, about 80 lines. -/
theorem indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix
    [DecidableEq k] {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    IndepFun (fun ω => polarFactor (G ω)) (fun ω => (G ω)ᴴ * G ω) μ := by
  sorry

end NLAlib
