/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.Matrix.Structured.BoundedOrthonormal
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.Probability.SubGaussianVector.NormMatrix
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Sampling.Leverage

/-!
# Flattening by a randomized unitary transform

Let $\mathbf{F}$ be a bounded orthonormal transform with constant $\beta$
(`NLAlib.IsBoundedOrthonormal F β`: unitary, $\lvert n \rvert \, \lvert \mathbf{F}_{i,j} \rvert^2
\le \beta$) and $\mathbf{D} = \operatorname{diag}(\boldsymbol{\xi})$ a diagonal of independent
random signs. For every $\mathbf{U}$ of rank $d$, the leverage scores of $\mathbf{F}\mathbf{D}
\mathbf{U}$ are all at most
$$\frac{\beta\,(d + 2\sqrt{d t} + 2t)}{\lvert n \rvert}$$
outside probability $\lvert n \rvert e^{-t}$: the randomized transform makes every subspace
incoherent (**flattening**). Row $i$ of $\mathbf{F}\mathbf{D}\mathbf{Q}$, for an orthonormal basis
$\mathbf{Q}$ of $\operatorname{range}\mathbf{U}$, is the image of the sign vector under a matrix
$\mathbf{M}_i$ with $\|\mathbf{M}_i\|_{\mathsf{F}}^2 \le \beta d / \lvert n \rvert$ and
$\|\mathbf{M}_i\|_2^2 \le \beta / \lvert n \rvert$, so the Hsu–Kakade–Zhang tail
(`NLAlib.IsSubgaussianVector.measure_norm_mulVec_sq_ge_le`) bounds it, over any `RCLike` field with
the real constant. `NLAlib.srhtRowBound` is the threshold at failure probability $\delta$.

The second half is generic: a sampler that injects (or embeds) every fixed subspace whose
leverage scores are at most $L / \lvert n \rvert$, composed with an independent random unitary
$\mathbf{T}$ that makes $\mathbf{T}\mathbf{U}$ so incoherent outside probability $\delta_2$,
injects (or embeds) $\operatorname{range}\mathbf{U}$ outside probability $\delta_1 + \delta_2$
(**flatten, then sample**). The subsampled randomized trigonometric transforms of
`NLAlib.Sketching.Structured.SRHT` instantiate it with uniform row sampling; rerandomized
transforms and sparse samplers are other instances.

Degenerate cases. Rank zero: every leverage score is $0$ and the flattening event is empty. Empty
`n`: every event is empty. For nonempty `n`, $\beta \ge 1$. The signs are $\pm 1$ only almost
surely, so $\mathbf{F}\mathbf{D}$ is unitary only almost surely. The transfer takes
$0 \le \delta_1$: with $L < 0$ its sampling hypothesis is vacuous. Design:
`docs/design/Sketching-S6.md` §3.2, §8.

This file is part of the skeleton of Sketching stage S6 (`docs/design/Sketching-S6.md` §8,
item 15); the proofs of the flattening tails and of the transfer are deferred.

## Main definitions

* `NLAlib.srhtRowBound`: the flattening threshold at failure probability $\delta$.

## Main results

* `NLAlib.ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector`: $\mathbf{F}\mathbf{D}$ is
  unitary almost surely.
* `NLAlib.measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector`:
  flattening; its $\delta$ form, in namespace `NLAlib`,
  `measureReal_not_forall_leverageScore_mul_diagonal_le_srhtRowBound_of_hasLaw_rademacherVector`.
* `NLAlib.srhtRowBound_nonneg`, `NLAlib.srhtRowBound_mono`, `NLAlib.srhtRowBound_le`: the API of
  the threshold.
* `NLAlib.hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le`,
  `NLAlib.hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le`: flatten, then sample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal

namespace NLAlib

/-! ### The row bound -/

/-- The **SRHT row bound** $d + 2\sqrt{d \log(n/\delta)} + 2 \log(n/\delta)$: flattening with
failure probability $\delta$ makes every leverage score at most $\beta$ times this over $n$
(`measureReal_not_forall_leverageScore_mul_diagonal_le_srhtRowBound_of_hasLaw_rademacherVector`).
The value the proof reaches, at $t = \log(n/\delta)$ in the Hsu–Kakade–Zhang tail. Tropp 2011a has
$(\sqrt{d} + \sqrt{8 \log(n/\delta)})^2$ ([Tropp2011a], cited by name, paper not in hand; the $8$
is as in [HalkoMartinssonTropp2011, Theorem 11.1], $[\sqrt{k} + \sqrt{8 \log(kn)}]^2$), which is
larger (`NLAlib.srhtRowBound_le`). Consumers use the API. Junk values: for $\delta > n$ the
logarithm is negative, the square root is $0$, and the value may be below $d$; the flattening tail
is then trivial. -/
noncomputable irreducible_def srhtRowBound (n d : ℕ) (δ : ℝ) : ℝ :=
  d + 2 * √(d * Real.log (n / δ)) + 2 * Real.log (n / δ)

/-- The SRHT row bound is nonnegative in its nontrivial range $0 < \delta \le n$. -/
theorem srhtRowBound_nonneg {n d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδn : δ ≤ n) :
    0 ≤ srhtRowBound n d δ := by
  rw [srhtRowBound_def]
  have : 0 ≤ Real.log (n / δ) := Real.log_nonneg ((one_le_div hδ).2 hδn)
  positivity

/-- The SRHT row bound is monotone in the dimensions $n \ge 1$ and $d$ and antitone in the
failure probability $\delta > 0$. -/
theorem srhtRowBound_mono {n n' d d' : ℕ} {δ δ' : ℝ} (hn : 0 < n) (hnn' : n ≤ n') (hd : d ≤ d')
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') : srhtRowBound n d δ' ≤ srhtRowBound n' d' δ := by
  rw [srhtRowBound_def, srhtRowBound_def]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hℓ : Real.log (n / δ') ≤ Real.log (n' / δ) :=
    Real.log_le_log (div_pos hn0 (hδ.trans_le hδδ'))
      (div_le_div₀ (Nat.cast_nonneg _) (Nat.cast_le.2 hnn') hδ hδδ')
  have hdd : (d : ℝ) ≤ d' := Nat.cast_le.2 hd
  have hsq : √(d * Real.log (n / δ')) ≤ √(d' * Real.log (n' / δ)) := by
    rcases le_or_gt (Real.log (n / δ')) 0 with h | h
    · rw [Real.sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h)]
      exact Real.sqrt_nonneg _
    · exact Real.sqrt_le_sqrt (mul_le_mul hdd hℓ h.le (Nat.cast_nonneg _))
  linarith

/-- The explicit comparison consumers invert with:
$\mathrm{srhtRowBound}(n, d, \delta) \le (\sqrt{d} + \sqrt{2 \log(n/\delta)})^2$, Tropp's form
with $2$ in place of $8$. No hypothesis: in the junk range $\log(n/\delta) < 0$ the left side is
$d + 2\log(n/\delta) < d$ and the right side is $d$. -/
theorem srhtRowBound_le (n d : ℕ) (δ : ℝ) :
    srhtRowBound n d δ ≤ (√(d : ℝ) + √(2 * Real.log (n / δ))) ^ 2 := by
  rw [srhtRowBound_def]
  have hd := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  rcases le_or_gt (Real.log (n / δ)) 0 with h | h
  · rw [Real.sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h),
      Real.sqrt_eq_zero'.2 (by linarith : 2 * Real.log (n / δ) ≤ 0)]
    nlinarith
  · have h1 : √(d * Real.log (n / δ)) ≤ √(d : ℝ) * √(2 * Real.log (n / δ)) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
      exact Real.sqrt_le_sqrt (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
    have h2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * Real.log (n / δ))
    nlinarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n r : Type*} [Fintype k] [Fintype n] [Fintype r] [DecidableEq n]
  {F : Matrix n n 𝕜} {ξ : Ω → n → ℝ} {β L a b t δ δ₁ δ₂ : ℝ}

/-! ### Flattening -/

/-- A unitary times a diagonal of random signs is unitary almost surely:
$(\mathbf{F}\mathbf{D})^{\mathsf{H}}\mathbf{F}\mathbf{D} = \mathbf{D}^2 = \mathbf{I}$ on the event
that every sign squares to $1$. -/
theorem ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector (hF : HasOrthonormalCols F)
    (hξ : HasLaw ξ (rademacherVector n) μ) :
    ∀ᵐ ω ∂μ, HasOrthonormalCols (F * Matrix.diagonal fun i => (ξ ω i : 𝕜)) := by
  filter_upwards [ae_sq_eq_one_of_hasLaw_rademacherVector hξ] with ω hω
  rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ,
    hF.conjTranspose_mul_self, Matrix.one_mul, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← sq, hω i,
    RCLike.ofReal_one]

/-- **Flattening**: a randomized unitary transform makes every subspace incoherent. For a bounded
orthonormal $\mathbf{F}$ with constant $\beta$, independent signs $\boldsymbol{\xi}$,
$\mathbf{D} = \operatorname{diag}(\boldsymbol{\xi})$, any $\mathbf{U}$ with
$d = \operatorname{rank}\mathbf{U}$ and $t \ge 0$, outside probability $\lvert n \rvert e^{-t}$
every leverage score satisfies
$$\ell_i(\mathbf{F}\mathbf{D}\mathbf{U}) \le \frac{\beta\,(d + 2\sqrt{d t} + 2t)}{\lvert n \rvert}
\,.$$
[CamanoEpperlyMeyerTropp2025, Imported Theorem 4.3] (there $O((d + \log(n/\delta))/n)$ for a
unitary Walsh–Hadamard, cosine or Fourier transform with entries $O(n^{-1/2})$; they note the
argument needs only these two features); [Tropp2011a] (real signs, Walsh;
$(\sqrt{d} + \sqrt{8 \log(\beta n)})^2 / n$, through CEMT, paper not in hand). Here any
$\mathbf{F}$ with $n \lvert \mathbf{F}_{i,j} \rvert^2 \le \beta$, any field, any $\mathbf{U}$, the
Hsu–Kakade–Zhang constant.
Proof: pass to an orthonormal basis $\mathbf{Q}$ of $\operatorname{range}\mathbf{U}$
(`NLAlib.leverageScore_eq_of_range_eq`); almost surely $\mathbf{F}\mathbf{D}\mathbf{Q}$ is
orthonormal and score $i$ is $\|(\mathbf{F}\mathbf{D}\mathbf{Q})_i\|^2 = \lvert n \rvert^{-1}
\|\mathbf{M}_i \boldsymbol{\xi}\|^2$ with $\mathbf{M}_i = \mathbf{Q}^{\mathsf{T}}
\operatorname{diag}(\sqrt{n}\,\mathbf{F}_{i,\cdot})$, $\|\mathbf{M}_i\|_{\mathsf{F}}^2 \le \beta d$,
$\|\mathbf{M}_i\|_2^2 \le \beta$; the Hsu–Kakade–Zhang tail at proxy $1$ per row, then a union over
the rows. About 150 lines, moderate.
Result: srht-flattening -/
theorem measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector
    (hF : IsBoundedOrthonormal F β) (hξ : HasLaw ξ (rademacherVector n) μ) (U : Matrix n r 𝕜)
    (ht : 0 ≤ t) :
    μ.real {ω | ¬ ∀ i, leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i ≤
        β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹} ≤
      Fintype.card n * Real.exp (-t) := by
  sorry

/-- **Flattening in $\delta$ form**: for a bounded orthonormal $\mathbf{F}$ with constant $\beta$,
independent signs and $\delta > 0$, outside probability $\delta$ every leverage score of
$\mathbf{F}\mathbf{D}\mathbf{U}$ is at most
$\beta \cdot \mathrm{srhtRowBound}(\lvert n \rvert, \operatorname{rank}\mathbf{U}, \delta) /
\lvert n \rvert$ (`NLAlib.srhtRowBound`).
The flattening tail at $t = \log(n/\delta)$ for $\delta \le n$, where $n e^{-t} = \delta$; for
$\delta > n \ge 1$ the bound exceeds $1$, and empty `n` has an empty event. -/
theorem measureReal_not_forall_leverageScore_mul_diagonal_le_srhtRowBound_of_hasLaw_rademacherVector
    (hF : IsBoundedOrthonormal F β) (hξ : HasLaw ξ (rademacherVector n) μ) (U : Matrix n r 𝕜)
    (hδ : 0 < δ) :
    μ.real {ω | ¬ ∀ i, leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i ≤
        β * srhtRowBound (Fintype.card n) U.rank δ * (Fintype.card n : ℝ)⁻¹} ≤ δ := by
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure_iff.2 inferInstance
  rcases isEmpty_or_nonempty n with hn | hn
  · have h : {ω | ¬ ∀ i, leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i ≤
        β * srhtRowBound (Fintype.card n) U.rank δ * (Fintype.card n : ℝ)⁻¹} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω => hω fun i => isEmptyElim i
    rw [h, measureReal_empty]
    exact hδ.le
  have hn0 : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  rcases le_or_gt δ (Fintype.card n) with hδn | hδn
  · have ht : 0 ≤ Real.log (Fintype.card n / δ) := Real.log_nonneg ((one_le_div hδ).2 hδn)
    have h := measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector
      hF hξ U ht
    rw [← srhtRowBound_def, Real.exp_neg, Real.exp_log (div_pos hn0 hδ), inv_div,
      mul_div_cancel₀ _ hn0.ne'] at h
    exact h
  · exact measureReal_le_one.trans (le_of_lt (lt_of_le_of_lt (Nat.one_le_cast.2 Fintype.card_pos)
      hδn))

/-! ### Flatten, then sample -/

/-- **Flatten, then sample** (injection). A random sketch $\mathbf{P}$ that is a subspace injection
with constant $a$ and failure probability $\delta_1$ for every fixed subspace of rank at most
$\operatorname{rank}\mathbf{U}$ whose leverage scores are at most $L / \lvert n \rvert$, composed
with an independent random unitary $\mathbf{T}$ that makes $\mathbf{T}\mathbf{U}$ so incoherent
outside probability $\delta_2$, is a subspace injection for $\operatorname{range}\mathbf{U}$ with
constant $a$ outside probability $\delta_1 + \delta_2$. $0 \le \delta_1$ is needed: for $L < 0$
and nonempty `n` the sampling hypothesis is vacuous. [Tropp2011a] (the structure of the SRHT
proof, through CEMT); [CamanoEpperlyMeyerTropp2025, §4.5] (the same two steps for SparseRTT, where
their Theorem 4.4 is the sampling hypothesis).
Proof: `ProbabilityTheory.IndepFun.measureReal_mem_le_add` with the open event
$\{(\mathbf{A}, \mathbf{B}) \mid \mathbf{A}\mathbf{B} \text{ is not an injection for }
\operatorname{range}\mathbf{U}\}$ and the measurable good set of unitaries $\mathbf{B}$ making
$\mathbf{B}\mathbf{U}$ incoherent; on it the section is the sampling hypothesis at
$\mathbf{B}\mathbf{U}$, since $(\mathbf{B}\mathbf{U})^{\mathsf{H}}\mathbf{B}\mathbf{U} =
\mathbf{U}^{\mathsf{H}}\mathbf{U}$. About 80 lines, moderate (the measurability of the good set). -/
theorem hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le [IsProbabilityMeasure μ]
    {P : Ω → Matrix k n 𝕜} {T : Ω → Matrix n n 𝕜} (hind : IndepFun P T μ)
    (hP : AEMeasurable P μ) (hT : AEMeasurable T μ) (hTU : ∀ᵐ ω ∂μ, HasOrthonormalCols (T ω))
    {U : Matrix n r 𝕜} (hδ₁ : 0 ≤ δ₁)
    (hsample : ∀ V : Matrix n r 𝕜, V.rank ≤ U.rank →
      (∀ i, leverageScore V i ≤ L * (Fintype.card n : ℝ)⁻¹) → HasSubspaceInjection P V a δ₁ μ)
    (hflat : μ.real {ω | ¬ ∀ i, leverageScore (T ω * U) i ≤ L * (Fintype.card n : ℝ)⁻¹} ≤ δ₂) :
    HasSubspaceInjection (fun ω => P ω * T ω) U a (δ₁ + δ₂) μ := by
  sorry

/-- **Flatten, then sample** (embedding). A random sketch $\mathbf{P}$ that is a subspace
embedding with constants $a$, $b$ and failure probability $\delta_1$ for every fixed subspace of
rank at most $\operatorname{rank}\mathbf{U}$ whose leverage scores are at most
$L / \lvert n \rvert$, composed with an independent random unitary $\mathbf{T}$ that makes
$\mathbf{T}\mathbf{U}$ so incoherent outside probability $\delta_2$, is a subspace embedding for
$\operatorname{range}\mathbf{U}$ with constants $a$, $b$ outside probability
$\delta_1 + \delta_2$. $0 \le \delta_1$ is needed, as in
`NLAlib.hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le`. [Tropp2011a];
[CamanoEpperlyMeyerTropp2025, §4.5].
Proof: as for the injection, with `NLAlib.isClosed_setOf_isSubspaceEmbedding`. About 20 lines on
a shared private lemma, easy once the injection is proved. -/
theorem hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le [IsProbabilityMeasure μ]
    {P : Ω → Matrix k n 𝕜} {T : Ω → Matrix n n 𝕜} (hind : IndepFun P T μ)
    (hP : AEMeasurable P μ) (hT : AEMeasurable T μ) (hTU : ∀ᵐ ω ∂μ, HasOrthonormalCols (T ω))
    {U : Matrix n r 𝕜} (hδ₁ : 0 ≤ δ₁)
    (hsample : ∀ V : Matrix n r 𝕜, V.rank ≤ U.rank →
      (∀ i, leverageScore V i ≤ L * (Fintype.card n : ℝ)⁻¹) → HasSubspaceEmbedding P V a b δ₁ μ)
    (hflat : μ.real {ω | ¬ ∀ i, leverageScore (T ω * U) i ≤ L * (Fintype.card n : ℝ)⁻¹} ≤ δ₂) :
    HasSubspaceEmbedding (fun ω => P ω * T ω) U a b (δ₁ + δ₂) μ := by
  sorry

end NLAlib
