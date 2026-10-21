/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Structural.RangeFinder
public import NLAlib.LowRank.Structural.Truncation
public import NLAlib.Regression.Oblivious

/-!
# The randomized SVD and Nyström with an oblivious subspace injection

Tail bounds for the randomized SVD $\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and randomized
Nyström $\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})$ for a random test matrix
$\mathbf{\Omega}$ of any law, from the Sketching predicates of its sketch
$\mathbf{\Omega}^{\mathsf{H}}$ (`fun ω => (X ω)ᴴ`). Every statement concludes about the output at
the test matrix itself, and its error is spelled as the matrix minus the named output.

**The range side.** The randomized SVD needs $\mathbf{\Omega}^{\mathsf{H}}$ to inject the one
subspace $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$, the dominant right
singular subspace of the library's truncation (`HasSubspaceInjection`), and, where Markov's
inequality bounds
$\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{\Omega}\|_{\mathsf{F}}^2$, isotropy
(`IsIsotropicSketch`). An oblivious subspace injection for dimension $k$ gives both:
`h.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)` and
`h.isotropic`; row sampling at the leverage scores of the head gives the first.
Nyström takes an OSI: its proofs pass to a factor $\mathbf{F}$ with
$\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$, whose dominant subspace is a different choice from
that of $\llbracket\mathbf{H}\rrbracket_k$ under a tie of eigenvalues.

**Three routes.** The injection route (constant factor $1 + t/a$, failure probability
$\delta + 1/t$; [CamanoEpperlyMeyerTropp2025, Theorem 2.2]), the bounded-sketch route
(factor $1 + L^2/a$ in every quadratic unitarily invariant norm, failure probability $\delta$;
[HalkoMartinssonTropp2011, Theorem 11.2]) and the approximate-multiplication route (factor
$1 + k\varepsilon^2/a^2$, which reaches $1 + \varepsilon$; [Woodruff2014, Lemma 45]). Each is a
composition of the structural bounds of `NLAlib.LowRank.Structural.RangeFinder` with the
Sketching predicates' tails. Design: `docs/design/LowRank-S7.md` §3.2, §8.

## Main results

* `NLAlib.HasSubspaceInjection.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le`,
  `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`,
  `NLAlib.HasSubspaceInjection.measureReal_specNorm_sub_rsvd_sq_gt_le`,
  `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le`: the injection
  route; `NLAlib.IsObliviousSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`, CEMT
  Theorem 2.2 as printed.
* in `HasSubspaceInjection`,
  `measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_specNorm_le`: the bounded-sketch
  route.
* `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_add_le`,
  `NLAlib.HasJLMoment.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le`,
  `NLAlib.HasJLMoment.measureReal_frobNorm_sub_rsvd_sq_gt_le`: the approximate-multiplication route,
  with its tail–head input, in `HasJLMoment`,
  `measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_rangeProjector_gt_le`.
* `NLAlib.IsObliviousSubspaceInjection.measureReal_nuclearNorm_sub_nystrom_gt_le` and its gauge,
  spectral and truncated forms; `NLAlib.HasJLMoment.measureReal_nuclearNorm_sub_nystrom_gt_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l 𝕜}

/-! ### The head frame and the Markov step -/

omit [Fintype l] [DecidableEq n] in
/-- A frame of the head: orthonormal columns spanning
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$, whose projector is
$\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}$ and with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$. -/
private theorem exists_frame_head (A : Matrix m n 𝕜) (k : ℕ) :
    ∃ Z : Matrix n (Fin (truncatedSVD A k)ᴴ.rank) 𝕜, HasOrthonormalCols Z ∧
      LinearMap.range Z.mulVecLin = LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin ∧
      Z * Zᴴ = rangeProjector (truncatedSVD A k)ᴴ ∧ A * Z * Zᴴ = truncatedSVD A k := by
  obtain ⟨Z, hZ, hR⟩ :=
    exists_hasOrthonormalCols_range_eq (truncatedSVD A k)ᴴ (Fintype.card_fin _)
  have hP : Z * Zᴴ = rangeProjector (truncatedSVD A k)ᴴ := by
    rw [← hZ.rangeProjector_eq, rangeProjector_inj, hR]
  exact ⟨Z, hZ, hR, hP, by rw [Matrix.mul_assoc, hP, mul_rangeProjector_conjTranspose_truncatedSVD]⟩

omit [Fintype l] [DecidableEq n] in
private theorem card_frame_head_le (A : Matrix m n 𝕜) (k : ℕ) :
    Fintype.card (Fin (truncatedSVD A k)ᴴ.rank) ≤ k := by
  rw [Fintype.card_fin, Matrix.rank_conjTranspose]
  exact rank_truncatedSVD_le A k

omit [Fintype m] [DecidableEq n] in
/-- The tail of the head is annihilated by the frame: $(\mathbf{A} - \mathbf{A}\mathbf{Z}
\mathbf{Z}^{\mathsf{H}})\mathbf{Z} = \mathbf{0}$. -/
private theorem sub_mul_mul_conjTranspose_mul_self {r : Type*} [Fintype r] [DecidableEq r]
    {Z : Matrix n r 𝕜} (hZ : HasOrthonormalCols Z) (A : Matrix m n 𝕜) :
    (A - A * Z * Zᴴ) * Z = 0 := by
  rw [Matrix.sub_mul, Matrix.mul_assoc (A * Z), show Zᴴ * Z = 1 from hZ, Matrix.mul_one, sub_self]

omit [DecidableEq n] in
/-- On the injection event, the competitor's correction is at most $\|\mathbf{E}\mathbf{\Omega}
\|_{\mathsf{F}}^2 / a$. -/
private theorem frobNorm_mul_pinv_sq_le_of_frame {r : Type*} [Fintype r] [DecidableEq r]
    {Z : Matrix n r 𝕜} (hZ : HasOrthonormalCols Z) {Ω : Matrix n l 𝕜} {a : ℝ}
    (h : IsSubspaceInjection Ωᴴ Z a) (ha : 0 < a) (E : Matrix m n 𝕜) :
    frobNorm (E * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤ frobNorm (E * Ω) ^ 2 / a := by
  have h' := h.frobNorm_mul_pinv_sq_le hZ ha (E * Ω)
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h'

/-- The Markov step of the injection route: if on the injection event an event $E$ forces
$t\|\mathbf{E}\|_{\mathsf{F}}^2 < \|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2$, then
$\mu(E) \le \delta + 1/t$. -/
private theorem measureReal_le_add_one_div_of_head [IsFiniteMeasure μ] {A : Matrix m n 𝕜}
    {k : ℕ} {a δ t : ℝ} (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ht : 0 < t) {E : Set Ω}
    (hE : ∀ ω ∈ E, IsSubspaceInjection (X ω)ᴴ (truncatedSVD A k)ᴴ a →
      t * frobNorm (A - truncatedSVD A k) ^ 2 < frobNorm ((A - truncatedSVD A k) * X ω) ^ 2) :
    μ.real E ≤ δ + 1 / t := by
  have e : ∀ ω, frobNorm ((A - truncatedSVD A k) * X ω) =
      frobNorm ((X ω)ᴴ * (A - truncatedSVD A k)ᴴ) := fun ω => by
    rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul]
  refine measureReal_le_add_one_div
    (G := {ω | IsSubspaceInjection (X ω)ᴴ (truncatedSVD A k)ᴴ a}) h
    (M := fun ω => frobNorm ((A - truncatedSVD A k) * X ω) ^ 2)
    (m := frobNorm (A - truncatedSVD A k) ^ 2) (fun ω => sq_nonneg _) ?_ ?_
    (fun h0 ω => ?_) ht (ae_of_all _ fun ω hω hEω => hE ω hEω hω)
  · simp_rw [e]
    exact hiso.integrable_frobNorm_mul_sq _
  · simp_rw [e]
    rw [hiso.integral_frobNorm_mul_sq, frobNorm_conjTranspose]
  · rw [frobNorm_eq_zero_iff.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), Matrix.zero_mul,
      frobNorm_zero, sq, mul_zero]

/-! ### The injection route -/

/-- **The tail of the randomized SVD under a subspace injection, Gram form**: if
$\mathbf{\Omega}^{\mathsf{H}}$ is isotropic and injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$ except
with probability $\delta$, then for every unitarily invariant norm and $t > 0$
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\bigr\|_{\Phi} \le
\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)^{\mathsf{H}}
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\bigr\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{t}{a}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$, with $\mathbf{e}_0$ the first unit coordinate sequence.
An OSI for dimension $k$ supplies both hypotheses. [CamanoEpperlyMeyerTropp2025, Theorem 2.2];
there an OSI, the Frobenius norm and $C/\alpha$ with probability $9/10$; here one fixed subspace,
every quadratic unitarily invariant norm, the factor and the failure probability explicit in $t$;
the shape of [TroppWebber2023, Theorem 8.1 (RSVD1)].
Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le
    [IsFiniteMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ha : 0 < a) (ht : 0 < t)
    (Φ : SymmetricGauge) :
    μ.real {ω | Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * (t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤ δ + 1 / t := by
  obtain ⟨Z, hZ, hR, -, hAZ⟩ := exists_frame_head A k
  refine measureReal_le_add_one_div_of_head h hiso ht fun ω hω hinj => ?_
  have hinjZ : IsSubspaceInjection (X ω)ᴴ Z a := hinj.of_range_le hR.le
  have hM := frobNorm_mul_pinv_sq_le_of_frame hZ hinjZ ha (A - truncatedSVD A k)
  have h1 := Φ.matrixNorm_conjTranspose_mul_self_sub_rsvd_le hZ (hinjZ.rank_mul_eq ha) A
  rw [hAZ] at h1
  have h2 := Φ.matrixNorm_le_apply_single_mul_nuclearNorm
    (((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω))ᴴ *
      ((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω)))
  rw [nuclearNorm_conjTranspose_mul_self] at h2
  have hω' : Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
      Φ (Finsupp.single 0 1) * (t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
        Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) := hω
  by_contra hc
  rw [not_lt] at hc
  have h3 := mul_le_mul_of_nonneg_left (hM.trans (div_le_div_of_nonneg_right hc ha.le))
    Φ.apply_single_pos.le
  have e : Φ (Finsupp.single 0 1) * (t / a) * frobNorm (A - truncatedSVD A k) ^ 2 =
      Φ (Finsupp.single 0 1) * (t * frobNorm (A - truncatedSVD A k) ^ 2 / a) := by ring
  linarith

/-- **The randomized SVD with a subspace injection**: if $\mathbf{\Omega}^{\mathsf{H}}$ is
isotropic and injects $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with
constant $a > 0$ except with probability $\delta$, then for $t > 0$
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{t}{a}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. The OSI form is
`NLAlib.IsObliviousSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.2]; there an OSI and $C/\alpha$ at probability $9/10$;
here one fixed subspace, the factor and the failure probability explicit in $t$.
Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t := by
  obtain ⟨Z, hZ, hR, -, hAZ⟩ := exists_frame_head A k
  refine measureReal_le_add_one_div_of_head h hiso ht fun ω hω hinj => ?_
  have h1 := (hinj.of_range_le hR.le).frobNorm_sub_rsvd_sq_le hZ ha A
  rw [hAZ] at h1
  have hω' : (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2 := hω
  by_contra hc
  rw [not_lt] at hc
  have h2 := div_le_div_of_nonneg_right hc ha.le
  have e : (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 =
      frobNorm (A - truncatedSVD A k) ^ 2 + t * frobNorm (A - truncatedSVD A k) ^ 2 / a := by
    ring
  linarith

/-- **The randomized SVD with an oblivious subspace injection**: if $\mathbf{\Omega}^{\mathsf{H}}$
is an OSI for dimension $k$ with constant $a > 0$ and failure probability $\delta$, then for
$t > 0$
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{t}{a}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. The fixed-subspace form, which also covers row sampling,
is `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.2]; there $C/\alpha$ at probability $9/10$.
Result: randomized-svd-tail -/
theorem IsObliviousSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t :=
  (h.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)
    ).measureReal_frobNorm_sub_rsvd_sq_gt_le h.isotropic ha ht

/-- **The randomized SVD with a subspace injection, spectral norm**: for
$\mathbf{A} \in \Bbbk^{m \times n}$, a target rank $k$, a finite measure $\mathbb{P}$ and a random
test matrix $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ whose sketch $\mathbf{\Omega}^{\mathsf{H}}$
is isotropic (square-integrable entries and
$\mathbb{E}[\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}] = \mathbf{I}$, `IsIsotropicSketch`) and
injects $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$
except with probability $\delta$ (the event that
$a\|\mathbf{y}\|^2 \le \|\mathbf{\Omega}^{\mathsf{H}}\mathbf{y}\|^2$ fails for some $\mathbf{y}$
in that range has probability at most $\delta$, `HasSubspaceInjection`), and any $t > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 >
\sigma_k(\mathbf{A})^2 + \frac{t}{a}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\Bigr] \le \delta + \frac{1}{t}\,,$$
singular values indexed from $0$. The spectral-norm companion of
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`. Its neighbour without
isotropy and without the Frobenius term is the bounded-sketch form
`HasSubspaceInjection.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_specNorm_le`
at the spectral gauge. [CamanoEpperlyMeyerTropp2025, Theorem 2.2], here in the spectral norm; the
shape of [TroppWebber2023, Theorem 8.1 (RSVD1)].
Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measureReal_specNorm_sub_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | singularValues A k ^ 2 + t / a * frobNorm (A - truncatedSVD A k) ^ 2 <
      specNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t := by
  obtain ⟨Z, hZ, hR, -, hAZ⟩ := exists_frame_head A k
  refine measureReal_le_add_one_div_of_head h hiso ht fun ω hω hinj => ?_
  have hinjZ : IsSubspaceInjection (X ω)ᴴ Z a := hinj.of_range_le hR.le
  have h1 := hZ.specNorm_sub_rsvd_sq_le (hinjZ.rank_mul_eq ha) A
  rw [hAZ, specNorm_sub_truncatedSVD] at h1
  have hM := frobNorm_mul_pinv_sq_le_of_frame hZ hinjZ ha (A - truncatedSVD A k)
  have hsf := pow_le_pow_left₀ (specNorm_nonneg _)
    (specNorm_le_frobNorm ((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω))) 2
  have hω' : singularValues A k ^ 2 + t / a * frobNorm (A - truncatedSVD A k) ^ 2 <
      specNorm (A - rsvd A (X ω)) ^ 2 := hω
  by_contra hc
  rw [not_lt] at hc
  have h2 := div_le_div_of_nonneg_right hc ha.le
  have e : t / a * frobNorm (A - truncatedSVD A k) ^ 2 =
      t * frobNorm (A - truncatedSVD A k) ^ 2 / a := by ring
  linarith

/-- **The rank-$k$ randomized SVD with a subspace injection**: for
$\mathbf{A} \in \Bbbk^{m \times n}$, a target rank $k$, a finite measure $\mathbb{P}$ and a random
test matrix $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ whose sketch $\mathbf{\Omega}^{\mathsf{H}}$
is isotropic (square-integrable entries and
$\mathbb{E}[\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}] = \mathbf{I}$, `IsIsotropicSketch`) and
injects $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$
except with probability $\delta$ (the event that
$a\|\mathbf{y}\|^2 \le \|\mathbf{\Omega}^{\mathsf{H}}\mathbf{y}\|^2$ fails for some $\mathbf{y}$
in that range has probability at most $\delta$, `HasSubspaceInjection`), and any $t > 0$,
$$\mathbb{P}\Bigl[
\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2 >
\Bigl(1 + \frac{t}{a}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\Bigr]
\le \delta + \frac{1}{t}\,,$$
the same constant as the untruncated output
(`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`).
[CamanoEpperlyMeyerTropp2025, remark after Theorem 1.3]; there by HMT Theorem 9.3, which is
spectral only; here in the Frobenius norm through the rank-$k$ competitor of [Woodruff2014,
Lemma 48].
Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2} ≤ δ + 1 / t := by
  obtain ⟨Z, hZ, hR, -, hAZ⟩ := exists_frame_head A k
  refine measureReal_le_add_one_div_of_head h hiso ht fun ω hω hinj => ?_
  have hinjZ : IsSubspaceInjection (X ω)ᴴ Z a := hinj.of_range_le hR.le
  have h1 := hZ.frobNorm_sub_truncatedSVD_rsvd_sq_le (hinjZ.rank_mul_eq ha) A
    (card_frame_head_le A k)
  rw [hAZ] at h1
  have hM := frobNorm_mul_pinv_sq_le_of_frame hZ hinjZ ha (A - truncatedSVD A k)
  have hω' : (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 := hω
  by_contra hc
  rw [not_lt] at hc
  have h2 := div_le_div_of_nonneg_right hc ha.le
  have e : (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 =
      frobNorm (A - truncatedSVD A k) ^ 2 + t * frobNorm (A - truncatedSVD A k) ^ 2 / a := by
    ring
  linarith

/-! ### The bounded-sketch route -/

omit [DecidableEq n] in
/-- **The randomized SVD with a bounded sketch**: if $\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$ except
with probability $\delta$ and $\|\mathbf{\Omega}\|_2 \le L$ almost surely, then for every unitarily
invariant norm
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\bigr\|_{\Phi} \le
\Bigl(1 + \frac{L^2}{a}\Bigr)\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)^{\mathsf{H}}
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\bigr\|_{\Phi}$$
except with probability $\delta$; at the spectral gauge the right side is
$(1 + L^2/a)\,\sigma_k(\mathbf{A})^2$. No isotropy and no Markov step. Its neighbour
`NLAlib.HasSubspaceInjection.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le` needs
isotropy and no bound on the sketch, and pays $\delta + 1/t$.
[HalkoMartinssonTropp2011, Theorem 11.2]; there the SRFT, $L^2 = n/\ell$, factor $1 + 7n/\ell$ in
the spectral and Frobenius norms and failure probability $O(k^{-1})$; here any sketch, every
quadratic unitarily invariant norm; at the SRHT a sharper factor ($1 + 2n/\ell$), an explicit
failure probability and an incomparable size condition.
Result: randomized-svd-tail -/
theorem
    HasSubspaceInjection.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_specNorm_le
    [IsFiniteMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a δ L : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ) (ha : 0 < a)
    (hL : ∀ᵐ ω ∂μ, specNorm (X ω) ≤ L) (Φ : SymmetricGauge) :
    μ.real {ω | (1 + L ^ 2 / a) *
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) <
      Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤ δ := by
  classical
  obtain ⟨Z, hZ, hR, -, hAZ⟩ := exists_frame_head A k
  unfold HasSubspaceInjection at h
  have hnull : μ.real {ω | ¬ specNorm (X ω) ≤ L} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).2 (ae_iff.1 hL)
  refine (measureReal_mono (s₂ := {ω | ¬ IsSubspaceInjection (X ω)ᴴ (truncatedSVD A k)ᴴ a} ∪
    {ω | ¬ specNorm (X ω) ≤ L}) fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (by rw [hnull, add_zero]; exact h))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
  obtain ⟨hinj, hLω⟩ := hc
  have hinjZ : IsSubspaceInjection (X ω)ᴴ Z a := hinj.of_range_le hR.le
  have h1 := Φ.matrixNorm_conjTranspose_mul_self_sub_rsvd_le hZ (hinjZ.rank_mul_eq ha) A
  rw [hAZ] at h1
  have hp : specNorm (pinv (Zᴴ * X ω)) ^ 2 ≤ a⁻¹ := by
    have h' := specNorm_pinv_sq_le_inv_of_smul_one_le ha (hZ.isSubspaceInjection_iff.1 hinjZ)
    rwa [← specNorm_conjTranspose, ← pinv_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] at h'
  have hL0 : 0 ≤ L := (specNorm_nonneg _).trans hLω
  have hsv : ∀ i, singularValues
      (((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω))ᴴ *
        ((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω))) i ≤
      singularValues (((L ^ 2 / a : ℝ) : 𝕜) •
        ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k))) i := by
    intro i
    rw [singularValues_conjTranspose_mul_self, singularValues_smul,
      singularValues_conjTranspose_mul_self, RCLike.norm_ofReal,
      abs_of_nonneg (by positivity)]
    have h2 : singularValues ((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω)) i ≤
        singularValues (A - truncatedSVD A k) i * specNorm (X ω) *
          specNorm (pinv (Zᴴ * X ω)) :=
      (singularValues_mul_le_mul_specNorm _ _ i).trans (mul_le_mul_of_nonneg_right
        (singularValues_mul_le_mul_specNorm _ _ i) (specNorm_nonneg _))
    have hσ := singularValues_nonneg (A - truncatedSVD A k) i
    calc singularValues ((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω)) i ^ 2
        ≤ (singularValues (A - truncatedSVD A k) i * specNorm (X ω) *
            specNorm (pinv (Zᴴ * X ω))) ^ 2 := pow_le_pow_left₀ (singularValues_nonneg _ _) h2 2
      _ = singularValues (A - truncatedSVD A k) i ^ 2 * specNorm (X ω) ^ 2 *
            specNorm (pinv (Zᴴ * X ω)) ^ 2 := by ring
      _ ≤ singularValues (A - truncatedSVD A k) i ^ 2 * L ^ 2 * a⁻¹ := by gcongr
      _ = L ^ 2 / a * singularValues (A - truncatedSVD A k) i ^ 2 := by ring
  have h3 := Φ.matrixNorm_le_of_singularValues_le hsv
  rw [Φ.matrixNorm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at h3
  have hω' : (1 + L ^ 2 / a) * Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) <
      Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) := hω
  have e : (1 + L ^ 2 / a) * Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) =
      Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        L ^ 2 / a * Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) := by ring
  linarith

/-! ### The approximate-multiplication route -/

omit [DecidableEq n] in
/-- **The rank-$k$ randomized SVD through an approximate-multiplication tail**, any field: if
$\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$ except
with probability $\delta$, and the tail–head multiplication error
$\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}
\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}}$ exceeds $\eta$ with
probability at most $\delta'$, then
$$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 + \frac{\eta^2}{a^2}$$
except with probability $\delta + \delta'$. The form a family with its own multiplication tail uses;
the JL-moment form is `NLAlib.HasJLMoment.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le`.
[Woodruff2014, proof of Lemma 45]; there constants $1 \pm 1/3$, here any injection constant and
any multiplication tail.
Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_add_le
    [IsFiniteMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a δ η δ' : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ) (ha : 0 < a)
    (hχ : μ.real {ω | η < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ)} ≤ δ') :
    μ.real {ω | frobNorm (A - truncatedSVD A k) ^ 2 + η ^ 2 / a ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2} ≤ δ + δ' := by
  classical
  obtain ⟨Z, hZ, hR, hP, hAZ⟩ := exists_frame_head A k
  have hEZ : (A - truncatedSVD A k) * Z = 0 := by
    have h0 := sub_mul_mul_conjTranspose_mul_self hZ A
    rwa [hAZ] at h0
  unfold HasSubspaceInjection at h
  refine (measureReal_mono (s₂ := {ω | ¬ IsSubspaceInjection (X ω)ᴴ (truncatedSVD A k)ᴴ a} ∪
    {ω | η < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ)}) fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add h hχ))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt] at hc
  obtain ⟨hinj, hηω⟩ := hc
  have hinjZ : IsSubspaceInjection (X ω)ᴴ Z a := hinj.of_range_le hR.le
  have h1 := hZ.frobNorm_sub_truncatedSVD_rsvd_sq_le (hinjZ.rank_mul_eq ha) A
    (card_frame_head_le A k)
  have h2 := hinjZ.matrixNorm_sub_mul_mul_pinv_le hZ ha (lpGauge 2) A
  rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h2
  rw [hAZ] at h1 h2
  have e : frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * Z) =
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * rangeProjector (truncatedSVD A k)ᴴ) := by
    rw [← hP, ← Matrix.mul_assoc, hZ.frobNorm_mul_conjTranspose_right]
  rw [hEZ, sub_zero, e] at h2
  have hη0 : 0 ≤ η := (frobNorm_nonneg _).trans hηω
  have h3 : frobNorm ((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω)) ^ 2 ≤ η ^ 2 / a ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (frobNorm_nonneg _) (h2.trans (div_le_div_of_nonneg_right hηω ha.le)) 2
  have hω' : frobNorm (A - truncatedSVD A k) ^ 2 + η ^ 2 / a ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 := hω
  linarith

section Real

omit [DecidableEq n] in
/-- **The tail–head multiplication error from the JL moment property**: if the real sketch
$\mathbf{\Omega}^{\mathsf{H}}$ has the $(\varepsilon, \delta', p)$ JL moment property,
$\varepsilon > 0$, $p \ge 2$, $\delta' \ge 0$, then
$$\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}
\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\bigr\|_{\mathsf{F}} \le
\varepsilon\sqrt{k}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$$
except with probability $\delta'$: the left side is an approximate-multiplication error, since
$(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)
\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}} = \mathbf{0}$, and
$\|\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}} \le \sqrt{k}$.
The hypothesis of
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_add_le`
and of the early-truncation tails at the JL moment. [Woodruff2014, proof of Lemma 45]. -/
theorem
    HasJLMoment.measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_rangeProjector_gt_le
    [IsFiniteMeasure μ] {X : Ω → Matrix n l ℝ}
    {A : Matrix m n ℝ} {k : ℕ} {ε δ' p : ℝ} (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ)
    (hX : AEMeasurable X μ) (hε : 0 < ε) (hp : 2 ≤ p) (hδ' : 0 ≤ δ') :
    μ.real {ω | ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * rangeProjector (truncatedSVD A k)ᴴ)} ≤
      δ' := by
  classical
  obtain ⟨Z, hZ, -, hP, hAZ⟩ := exists_frame_head A k
  have hEP : (A - truncatedSVD A k) * rangeProjector (truncatedSVD A k)ᴴ = 0 := by
    have h0 := sub_mul_mul_conjTranspose_mul_self hZ A
    rw [hAZ] at h0
    rw [← hP, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  have hS : AEMeasurable (fun ω => (X ω)ᴴ) μ :=
    continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hX
  by_cases h0 : A - truncatedSVD A k = 0 ∨ rangeProjector (truncatedSVD A k)ᴴ = 0
  · have he : {ω | ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) <
        frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
          rangeProjector (truncatedSVD A k)ᴴ)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rcases h0 with h0 | h0
      · rw [h0]
        simp
      · rw [h0, Matrix.mul_zero, frobNorm_zero]
        positivity
    rw [he, measureReal_empty]
    exact hδ'
  rw [not_or] at h0
  have hF := hJL.measureReal_frobNorm_conjTranspose_mul_sub_ge_le hε hp hS
    (A := (A - truncatedSVD A k)ᴴ) (B := rangeProjector (truncatedSVD A k)ᴴ)
    (by rw [Ne, Matrix.conjTranspose_eq_zero]; exact h0.1) h0.2
  refine (measureReal_mono fun ω hω => ?_).trans hF
  have hω' : ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
        rangeProjector (truncatedSVD A k)ᴴ) := hω
  have hPk : frobNorm (rangeProjector (truncatedSVD A k)ᴴ) ≤ √(k : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [frobNorm_rangeProjector_sq, Matrix.rank_conjTranspose]
    exact_mod_cast rank_truncatedSVD_le A k
  change ε * frobNorm (A - truncatedSVD A k)ᴴ * frobNorm (rangeProjector (truncatedSVD A k)ᴴ) ≤
    frobNorm ((A - truncatedSVD A k)ᴴᴴ * ((X ω)ᴴ)ᴴ * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ - (A - truncatedSVD A k)ᴴᴴ *
        rangeProjector (truncatedSVD A k)ᴴ)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, hEP, sub_zero,
    frobNorm_conjTranspose]
  calc ε * frobNorm (A - truncatedSVD A k) * frobNorm (rangeProjector (truncatedSVD A k)ᴴ)
      ≤ ε * frobNorm (A - truncatedSVD A k) * √(k : ℝ) := by gcongr
    _ = ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) := by ring
    _ ≤ _ := hω'.le

omit [DecidableEq n] in
/-- **The rank-$k$ randomized SVD to relative error through approximate multiplication**: if the
real sketch $\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$ except
with probability $\delta$ and has the $(\varepsilon, \delta', p)$ JL moment property,
$\varepsilon > 0$, $p \ge 2$, $\delta' \ge 0$, then
$$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{k\varepsilon^2}{a^2}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta'$. Its neighbour without the moment property,
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le`, has the constant
factor $1 + t/a$ at failure probability $\delta + 1/t$; this one reaches $1 + \varepsilon$ when
$\delta'$ decays with the sketch size. [Woodruff2014, Lemmas 44 and 45]; there constants
$1 \pm 1/3$ and the $(\sqrt{\varepsilon/k}, 9/10, \ell)$ moment; here any injection constant,
explicit.
Result: randomized-svd-tail -/
theorem HasJLMoment.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {X : Ω → Matrix n l ℝ} {A : Matrix m n ℝ} {k : ℕ} {a δ ε δ' p : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hX : AEMeasurable X μ) (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p) (hδ' : 0 ≤ δ') :
    μ.real {ω | (1 + (k : ℝ) * ε ^ 2 / a ^ 2) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2} ≤ δ + δ' := by
  classical
  refine (measureReal_mono fun ω hω => ?_).trans
    (h.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_add_le ha
      (hJL.measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_rangeProjector_gt_le hX
        hε
        hp hδ'))
  have hω' : (1 + (k : ℝ) * ε ^ 2 / a ^ 2) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 := hω
  change frobNorm (A - truncatedSVD A k) ^ 2 +
      (ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k)) ^ 2 / a ^ 2 <
    frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2
  have e : frobNorm (A - truncatedSVD A k) ^ 2 +
      (ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k)) ^ 2 / a ^ 2 =
        (1 + (k : ℝ) * ε ^ 2 / a ^ 2) * frobNorm (A - truncatedSVD A k) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    ring
  rwa [e]

omit [DecidableEq n] in
/-- **The randomized SVD to relative error through approximate multiplication**: if the real
sketch $\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$ except
with probability $\delta$ and has the $(\varepsilon, \delta', p)$ JL moment property,
$\varepsilon > 0$, $p \ge 2$, $\delta' \ge 0$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k\varepsilon^2}{a^2}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta'$. Its neighbour without the moment property is
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`, with the constant factor
$1 + t/a$; this one reaches $1 + \varepsilon$ at $\ell = O(k/(\varepsilon\delta'))$ for the dense
families. [Woodruff2014, Lemma 45]; there constants $1 \pm 1/3$ and the
$(\sqrt{\varepsilon/k}, 9/10, \ell)$ moment; here any injection constant, explicit.
Result: randomized-svd-tail -/
theorem HasJLMoment.measureReal_frobNorm_sub_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {X : Ω → Matrix n l ℝ} {A : Matrix m n ℝ} {k : ℕ} {a δ ε δ' p : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hX : AEMeasurable X μ) (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p) (hδ' : 0 ≤ δ') :
    μ.real {ω | (1 + (k : ℝ) * ε ^ 2 / a ^ 2) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + δ' := by
  classical
  refine (measureReal_mono fun ω hω => ?_).trans
    (hJL.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le h hX ha hε hp hδ')
  have hω' : (1 + (k : ℝ) * ε ^ 2 / a ^ 2) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2 := hω
  have h1 := frobNorm_sub_truncatedSVD_rsvd_sq A (X ω) k
  have h2 := sq_nonneg (frobNorm (rsvd A (X ω) - truncatedSVD (rsvd A (X ω)) k))
  change (1 + (k : ℝ) * ε ^ 2 / a ^ 2) * frobNorm (A - truncatedSVD A k) ^ 2 <
    frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2
  linarith

end Real

/-! ### Nyström -/

/-- **Randomized Nyström with an oblivious subspace injection**, trace norm: for positive
semidefinite $\mathbf{H}$ and an OSI $\mathbf{\Omega}^{\mathsf{H}}$ for dimension $k$ with constant
$a > 0$ and failure probability $\delta$, for $t > 0$
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_* \le
\Bigl(1 + \frac{t}{a}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
except with probability $\delta + 1/t$. An OSI, not a fixed subspace: the proof passes to a factor
$\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$, whose dominant subspace under a tie of
eigenvalues need not be that of $\llbracket\mathbf{H}\rrbracket_k$.
[CamanoEpperlyMeyerTropp2025, Corollary 2.5]; there $C/\alpha$ at probability $9/10$.
Result: randomized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measureReal_nuclearNorm_sub_nystrom_gt_le [IsFiniteMeasure μ]
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * nuclearNorm (H - truncatedSVD H k) <
      nuclearNorm (H - nystrom H (X ω))} ≤ δ + 1 / t := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [Matrix.star_eq_conjTranspose]
  simp only [nuclearNorm_conjTranspose_mul_self_sub_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact h.measureReal_frobNorm_sub_rsvd_sq_gt_le ha ht

/-- **Randomized Nyström with an oblivious subspace injection**, every unitarily invariant norm:
for a positive semidefinite $\mathbf{H} \in \Bbbk^{n \times n}$, a target rank $k$, a finite
measure $\mathbb{P}$ and a random test matrix $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ whose
sketch $\mathbf{\Omega}^{\mathsf{H}}$ is an oblivious subspace injection for dimension $k$ with
constant $a > 0$ and failure probability $\delta$ (isotropic,
$\mathbb{E}[\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}] = \mathbf{I}$, and for every
$\mathbf{U} \in \Bbbk^{n \times n}$ of rank at most $k$,
$a\|\mathbf{y}\|^2 \le \|\mathbf{\Omega}^{\mathsf{H}}\mathbf{y}\|^2$ for all
$\mathbf{y} \in \operatorname{range}\mathbf{U}$ except with probability $\delta$;
`IsObliviousSubspaceInjection`), any $t > 0$ and every symmetric gauge $\Phi$ (`SymmetricGauge`)
with its unitarily invariant norm $\|\cdot\|_{\Phi}$,
$$\mathbb{P}\Bigl[\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_{\Phi} >
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{t}{a}\,
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\Bigr] \le \delta + \frac{1}{t}\,,$$
with $\mathbf{e}_0$ the first unit coordinate sequence.
[CamanoEpperlyMeyerTropp2025, Corollary 2.5]; there the trace norm.
Result: randomized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measureReal_matrixNorm_sub_nystrom_gt_le [IsFiniteMeasure μ]
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t)
    (Φ : SymmetricGauge) :
    μ.real {ω | Φ.matrixNorm (H - truncatedSVD H k) +
        Φ (Finsupp.single 0 1) * (t / a) * nuclearNorm (H - truncatedSVD H k) <
      Φ.matrixNorm (H - nystrom H (X ω))} ≤ δ + 1 / t := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [Matrix.star_eq_conjTranspose]
  simp only [conjTranspose_mul_self_sub_nystrom,
    Φ.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact (h.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le F k)
    ).measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le h.isotropic ha ht Φ

/-- **Randomized Nyström with an oblivious subspace injection**, spectral norm: for a
positive semidefinite $\mathbf{H} \in \Bbbk^{n \times n}$, a target rank $k$, a finite
measure $\mathbb{P}$ and a random test matrix $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ whose
sketch $\mathbf{\Omega}^{\mathsf{H}}$ is an oblivious subspace injection for dimension $k$ with
constant $a > 0$ and failure probability $\delta$ (isotropic,
$\mathbb{E}[\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}] = \mathbf{I}$, and for every
$\mathbf{U} \in \Bbbk^{n \times n}$ of rank at most $k$,
$a\|\mathbf{y}\|^2 \le \|\mathbf{\Omega}^{\mathsf{H}}\mathbf{y}\|^2$ for all
$\mathbf{y} \in \operatorname{range}\mathbf{U}$ except with probability $\delta$;
`IsObliviousSubspaceInjection`), and any $t > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_2 >
\sigma_k(\mathbf{H}) + \frac{t}{a}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\Bigr]
\le \delta + \frac{1}{t}\,,$$
where $\sigma_k(\mathbf{H}) = \lambda_k(\mathbf{H})$, indexed from $0$. The form a
Nyström preconditioner consumes. [CamanoEpperlyMeyerTropp2025, Corollary 2.5]; there the trace
norm.
Result: randomized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measureReal_specNorm_sub_nystrom_gt_le [IsFiniteMeasure μ]
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | singularValues H k + t / a * nuclearNorm (H - truncatedSVD H k) <
      specNorm (H - nystrom H (X ω))} ≤ δ + 1 / t := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [Matrix.star_eq_conjTranspose]
  simp only [conjTranspose_mul_self_sub_nystrom, specNorm_conjTranspose_mul_self,
    singularValues_conjTranspose_mul_self, nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact (h.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le F k)
    ).measureReal_specNorm_sub_rsvd_sq_gt_le h.isotropic ha ht

/-- **Truncated randomized Nyström with an oblivious subspace injection**, trace norm: for
a positive semidefinite $\mathbf{H} \in \Bbbk^{n \times n}$, a target rank $k$, a finite
measure $\mathbb{P}$ and a random test matrix $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ whose
sketch $\mathbf{\Omega}^{\mathsf{H}}$ is an oblivious subspace injection for dimension $k$ with
constant $a > 0$ and failure probability $\delta$ (isotropic,
$\mathbb{E}[\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}] = \mathbf{I}$, and for every
$\mathbf{U} \in \Bbbk^{n \times n}$ of rank at most $k$,
$a\|\mathbf{y}\|^2 \le \|\mathbf{\Omega}^{\mathsf{H}}\mathbf{y}\|^2$ for all
$\mathbf{y} \in \operatorname{range}\mathbf{U}$ except with probability $\delta$;
`IsObliviousSubspaceInjection`), and any $t > 0$,
$$\mathbb{P}\Bigl[
\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\rrbracket_k\|_* >
\Bigl(1 + \frac{t}{a}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\Bigr]
\le \delta + \frac{1}{t}\,,$$
the bound of the untruncated output. [CamanoEpperlyMeyerTropp2025, remark after Theorem 1.3].
Result: randomized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measureReal_nuclearNorm_sub_truncatedSVD_nystrom_gt_le
    [IsFiniteMeasure μ] {H : Matrix n n 𝕜} (hH : H.PosSemidef) {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * nuclearNorm (H - truncatedSVD H k) <
      nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k)} ≤ δ + 1 / t := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [Matrix.star_eq_conjTranspose]
  simp only [nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact (h.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le F k)
    ).measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le h.isotropic ha ht

/-- **Randomized Nyström to relative error through approximate multiplication**, trace norm: for
real positive semidefinite $\mathbf{H}$ and a real OSI $\mathbf{\Omega}^{\mathsf{H}}$ for dimension
$k$ (constant $a > 0$, failure probability $\delta$) with the $(\varepsilon, \delta', p)$ JL moment
property, $\varepsilon > 0$, $p \ge 2$, $\delta' \ge 0$,
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_* \le
\Bigl(1 + \frac{k\varepsilon^2}{a^2}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
except with probability $\delta + \delta'$. Its constant-factor neighbour is
`NLAlib.IsObliviousSubspaceInjection.measureReal_nuclearNorm_sub_nystrom_gt_le`.
[Woodruff2014, Lemma 45] through [CamanoEpperlyMeyerTropp2025, Imported Theorem 2.4].
Result: randomized-nystrom-tail -/
theorem HasJLMoment.measureReal_nuclearNorm_sub_nystrom_gt_le [IsFiniteMeasure μ]
    {X : Ω → Matrix n l ℝ} {H : Matrix n n ℝ} (hH : H.PosSemidef) {k : ℕ} {a δ ε δ' p : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ)
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (hX : AEMeasurable X μ)
    (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p) (hδ' : 0 ≤ δ') :
    μ.real {ω | (1 + (k : ℝ) * ε ^ 2 / a ^ 2) * nuclearNorm (H - truncatedSVD H k) <
      nuclearNorm (H - nystrom H (X ω))} ≤ δ + δ' := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [Matrix.star_eq_conjTranspose]
  simp only [nuclearNorm_conjTranspose_mul_self_sub_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact hJL.measureReal_frobNorm_sub_rsvd_sq_gt_le
    (h.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le F k))
    hX ha hε hp hδ'

end NLAlib
