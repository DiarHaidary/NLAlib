/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Structural.Truncation

/-!
# Truncated generalized Nyström: the sharpened and the reverse perturbed truncation (stage S10)

Three deterministic statements for `NLAlib/LowRank/Structural/Truncation.lean`, next to
`NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm`. With
$\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and the core noise
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$:

* truncated generalized Nyström never beats the truncated randomized SVD;
* an upper bound in which the cross term carries
  $\|\llbracket\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}$, the energy
of
  the next $k$ singular values only, in place of $\|\mathbf{R} -
\llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}$;
* a lower bound: the error is at least the truncated randomized SVD error plus the noise in the
  oracle subspace, $\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2$, up
  to $\|\mathbf{N}\|_{\mathsf{F}}^4$ over the gap $\sigma_{k-1}(\mathbf{R})^2 -
\sigma_k(\mathbf{R})^2$.
  It feeds the lower bound on Epperly and Webber's instance
  (`NLAlib.LowRank.Optimality.TruncatedGeneralizedNystrom`).

Both are new (research note `reports/OP2-TruncatedGN.md` of the NLAlib workflow, §2, D1–D2;
the lower bound is this design's). Design: `docs/design/LowRank-EstimatorLowerBounds.md` §3.2.
Proofs deferred.

## Main results

* `NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq`
* `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm_mul_frobNorm`
* `NLAlib.le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq`
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype p]

/-- **Truncated generalized Nyström never beats the truncated randomized SVD**: for
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$
has the rank of $\mathbf{A}\mathbf{\Omega}$, and any $k$,
$$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2
\le
\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2\,:$$
both outputs lie in $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, and the truncated randomized
SVD
is the best rank-$k$ approximation there. For the choice `truncatedSVD` makes.
Proof: S, about 15 lines. The core form (`exists_core_generalizedNystrom`) gives the error as
$\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2 + \|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2$ with
$\mathbf{C} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}$ and $\operatorname{rank}\mathbf{Y} \le k$;
Eckart–Young (`frobNorm_sub_truncatedSVD_le_of_rank_le`) and the core's truncation-error conjunct
give
$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} \ge \|\mathbf{R} -
\llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}$;
Pythagoras (`truncatedSVD_rsvd_eq_rangeProjector_mul`, `sub_rsvd`) splits
$\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2$ the same way. -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 := by
  obtain ⟨Q, E, Y, -, -, -, hY, -, hsplit, hC, -⟩ := exists_core_generalizedNystrom h k
  have hEY : frobNorm (Qᴴ * A - truncatedSVD (Qᴴ * A) k) ≤ frobNorm (Qᴴ * A - Y) :=
    frobNorm_sub_truncatedSVD_le_of_rank_le _ hY.rank_le
  rw [hsplit, frobNorm_sub_truncatedSVD_rsvd_sq, ← hC]
  have := pow_le_pow_left₀ (frobNorm_nonneg _) hEY 2
  linarith

/-- A best approximation is the projection of the target onto its own column space:
$\mathbf{P}_{\mathbf{Y}}\mathbf{M} = \mathbf{Y}$. -/
private theorem IsBestRankApprox.rangeProjector_self_mul {M Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox M k Y) : rangeProjector Y * M = Y := by
  classical
  have hsplit := (isStarProjection_rangeProjector Y).frobNorm_sq_eq_add (M - Y)
  have e1 : rangeProjector Y * (M - Y) = rangeProjector Y * M - Y := by
    rw [Matrix.mul_sub, rangeProjector_mul_self]
  have e2 : (1 - rangeProjector Y) * (M - Y) = M - rangeProjector Y * M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul,
      rangeProjector_mul_self, sub_self, sub_zero]
  rw [e1, e2] at hsplit
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _) (hY.frobNorm_sub_le _
    ((Matrix.rank_mul_le_left (rangeProjector Y) M).trans
      (by rw [rank_rangeProjector]; exact hY.rank_le))) 2
  have hsq : frobNorm (rangeProjector Y * M - Y) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  exact sub_eq_zero.mp (frobNorm_eq_zero_iff.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

/-- The scalar step of the next-$k$ perturbed truncation. -/
private theorem le_add_mul_of_le_two_mul {S a w u q γ s r e : ℝ} (hs : 0 ≤ s) (he : 0 ≤ e)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hr2 : r ^ 2 = 2) (hqγ : q ≤ γ)
    (h1 : S ≤ 2 * (r * s * u * e + w)) (h2 : S = a - q ^ 2 + w) (h3 : u ^ 2 = a + q ^ 2)
    (hw : w ≤ s ^ 2 * e ^ 2) :
    S ≤ 4 * s * e * γ + 12 * s ^ 2 * e ^ 2 := by
  have hr3 : r ≤ 3 / 2 := by nlinarith
  have hsq : (u - r * s * e) ^ 2 ≤ (2 * s * e + r * q) ^ 2 := by
    have e1 : (u - r * s * e) ^ 2 = u ^ 2 - 2 * (r * s * u * e) + r ^ 2 * (s * e) ^ 2 := by ring
    have e2 : (2 * s * e + r * q) ^ 2 =
        4 * (s * e) ^ 2 + 4 * (r * s * e * q) + r ^ 2 * q ^ 2 := by ring
    rw [e1, e2, hr2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hr hs) he) hq]
  have hu' : u ≤ (r + 2) * s * e + r * q := by
    nlinarith [(abs_le_of_sq_le_sq' hsq (by positivity)).2]
  have hse : 0 ≤ r * s * e := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hu' hse, mul_le_mul_of_nonneg_left hqγ (mul_nonneg hs he),
    mul_le_mul_of_nonneg_right hr3 (sq_nonneg (s * e))]

/-- The optimality step of perturbed truncation: for any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 -
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 \le
2\langle\mathbf{Y} - \llbracket\mathbf{C}\rrbracket_k, \mathbf{E}\rangle_{\mathsf{F}}\,.$$ -/
private theorem IsBestRankApprox.frobNorm_sub_sq_sub_le_two_mul_frobInner
    {C E Y : Matrix m n 𝕜} {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ^ 2 - frobNorm (C - truncatedSVD C k) ^ 2 ≤
      2 * frobInner (Y - truncatedSVD C k) E := by
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _)
    (hY.frobNorm_sub_le (truncatedSVD C k) (rank_truncatedSVD_le C k)) 2
  have e1 : frobNorm (C - Y) ^ 2 =
      frobNorm (C + E - Y) ^ 2 - 2 * frobInner (C + E - Y) E + frobNorm E ^ 2 := by
    rw [← frobNorm_sub_sq, show C + E - Y - E = C - Y by abel]
  have e2 : frobNorm (C + E - truncatedSVD C k) ^ 2 =
      frobNorm (C - truncatedSVD C k) ^ 2 + 2 * frobInner (C - truncatedSVD C k) E +
        frobNorm E ^ 2 := by
    rw [← frobNorm_add_sq, show C - truncatedSVD C k + E = C + E - truncatedSVD C k by abel]
  have e3 : frobInner (C - truncatedSVD C k) E - frobInner (C + E - Y) E =
      frobInner (Y - truncatedSVD C k) E - frobNorm E ^ 2 := by
    rw [← frobInner_self, ← frobInner_sub_left, ← frobInner_sub_left]
    congr 1
    abel
  linarith

/-- The next-$k$ perturbed truncation in core coordinates: for any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$, with $\gamma_k =
\|\llbracket\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 +
4\sqrt{k}\,\|\mathbf{E}\|_2\,\gamma_k + 12k\,\|\mathbf{E}\|_2^2\,.$$ -/
private theorem IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm
    {C E Y : Matrix m n 𝕜} {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ^ 2 ≤ frobNorm (C - truncatedSVD C k) ^ 2 +
      4 * √(k : ℝ) * specNorm E * frobNorm (truncatedSVD (C - truncatedSVD C k) k) +
      12 * k * specNorm E ^ 2 := by
  classical
  set T := truncatedSVD C k with hT
  set B₂ := C - T with hB₂
  set P := rangeProjector Y with hPdef
  have hP : IsStarProjection P := isStarProjection_rangeProjector Y
  have hPY : P * (C + E) = Y := hY.rangeProjector_self_mul
  have hY' : Y = P * C + P * E := by rw [← hPY, Matrix.mul_add]
  have hrP : P.rank ≤ k := by rw [hPdef, rank_rangeProjector]; exact hY.rank_le
  have hrT : T.rank ≤ k := rank_truncatedSVD_le C k
  -- (D1) the optimality of `Y` against `T`
  have hS : frobNorm (C - Y) ^ 2 - frobNorm B₂ ^ 2 ≤ 2 * frobInner (Y - T) E :=
    hY.frobNorm_sub_sq_sub_le_two_mul_frobInner
  -- (D2) the row spaces of `T` and `B₂` are orthogonal
  have hTPB : frobInner T (P * B₂) = 0 := by
    have hCQ : C * rangeProjector Tᴴ = T := mul_rangeProjector_conjTranspose_truncatedSVD C k
    have hTQ : T * rangeProjector Tᴴ = T :=
      calc T * rangeProjector Tᴴ = C * rangeProjector Tᴴ * rangeProjector Tᴴ := by
            rw [hCQ]
        _ = T := by rw [Matrix.mul_assoc, rangeProjector_mul_rangeProjector, hCQ]
    have hBQ : B₂ * rangeProjector Tᴴ = 0 := by rw [hB₂, Matrix.sub_mul, hCQ, hTQ, sub_self]
    nth_rw 1 [← hTQ]
    rw [frobInner_mul_right, conjTranspose_rangeProjector, Matrix.mul_assoc, hBQ, Matrix.mul_zero,
      frobInner_zero_right]
  have hCY : frobNorm (C - Y) ^ 2 = frobNorm (T - P * T) ^ 2 +
      (frobNorm B₂ ^ 2 - frobNorm (P * B₂) ^ 2) + frobNorm (P * E) ^ 2 := by
    have h1 : C - Y = (C - P * C) - P * E := by rw [hY']; abel
    have h0 : frobInner (C - P * C) (P * E) = 0 := by
      rw [frobInner_comm, frobInner_mul_left, hP.conjTranspose_eq, Matrix.mul_sub,
        ← Matrix.mul_assoc, hP.mul_self, sub_self, frobInner_zero_right]
    have h2 : C - P * C = (T - P * T) + (B₂ - P * B₂) := by rw [hB₂, Matrix.mul_sub]; abel
    have h3 : frobInner (T - P * T) (B₂ - P * B₂) = 0 := by
      rw [hP.frobInner_sub_mul_sub_mul, frobInner_sub_left, frobInner_mul_left,
        hP.conjTranspose_eq, hTPB, frobInner_truncatedSVD_sub C k, sub_zero]
    have h4 := hP.frobNorm_sq_eq_add B₂
    rw [Matrix.sub_mul, Matrix.one_mul] at h4
    rw [h1, frobNorm_sub_sq_of_frobInner_eq_zero h0, h2, frobNorm_add_sq_of_frobInner_eq_zero h3]
    linarith
  have hD : frobNorm (P * C - T) ^ 2 = frobNorm (T - P * T) ^ 2 + frobNorm (P * B₂) ^ 2 := by
    have h1 : P * C - T = P * B₂ - (T - P * T) := by rw [hB₂, Matrix.mul_sub]; abel
    have h0 : frobInner (P * B₂) (T - P * T) = 0 := by
      rw [frobInner_sub_right, frobInner_mul_left, frobInner_mul_left, hP.conjTranspose_eq,
        ← Matrix.mul_assoc, hP.mul_self, sub_self]
    rw [h1, frobNorm_sub_sq_of_frobInner_eq_zero h0]
    ring
  have hYT : frobInner (Y - T) E = frobInner (P * C - T) E + frobNorm (P * E) ^ 2 := by
    rw [hY', show P * C + P * E - T = (P * C - T) + P * E by abel, frobInner_add_left,
      ← frobInner_self, frobInner_mul_left P E (P * E), hP.conjTranspose_eq, ← Matrix.mul_assoc,
      hP.mul_self, frobInner_comm (P * E) E]
  -- the cross term sees rank `2k`, the noise term rank `k`
  have hDE : frobInner (P * C - T) E ≤
      √2 * √(k : ℝ) * frobNorm (P * C - T) * specNorm E := by
    have hrank : (P * C - T).rank ≤ 2 * k := (Matrix.rank_sub_le _ _).trans
      (by have := (Matrix.rank_mul_le_left P C).trans hrP; omega)
    have h := frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le hrank E
    rwa [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul zero_le_two] at h
  have hw : frobNorm (P * E) ^ 2 ≤ √(k : ℝ) ^ 2 * specNorm E ^ 2 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg k)]
    exact (frobNorm_sq_le_rank_mul_specNorm_sq _).trans (mul_le_mul
      (by exact_mod_cast (Matrix.rank_mul_le_left P E).trans hrP)
      (pow_le_pow_left₀ (specNorm_nonneg _) (hP.specNorm_mul_le E) 2) (sq_nonneg _)
      (Nat.cast_nonneg k))
  -- Ky Fan for the rank-`k` projector `P`
  have hg : frobNorm (P * B₂) ≤ frobNorm (truncatedSVD B₂ k) := by
    have h1 := frobInner_le_frobNorm_mul_frobNorm_truncatedSVD_of_rank_le
      ((Matrix.rank_mul_le_left P B₂).trans hrP) B₂
    have h2 : frobInner (P * B₂) B₂ = frobNorm (P * B₂) ^ 2 := by
      rw [← frobInner_self, frobInner_mul_left P B₂ (P * B₂), frobInner_mul_left P B₂ B₂,
        hP.conjTranspose_eq, ← Matrix.mul_assoc, hP.mul_self]
    nlinarith [frobNorm_nonneg (P * B₂), frobNorm_nonneg (truncatedSVD B₂ k)]
  have h := le_add_mul_of_le_two_mul (S := frobNorm (C - Y) ^ 2 - frobNorm B₂ ^ 2)
    (a := frobNorm (T - P * T) ^ 2) (w := frobNorm (P * E) ^ 2) (Real.sqrt_nonneg (k : ℝ))
    (specNorm_nonneg E) (frobNorm_nonneg _) (Real.sqrt_nonneg 2) (Real.sq_sqrt zero_le_two)
    hg (by linarith) (by linarith) hD hw
  rw [Real.sq_sqrt (Nat.cast_nonneg k)] at h
  linarith

/-- **The perturbed truncation with the next-$k$ tail**: for
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$
has the rank of $\mathbf{A}\mathbf{\Omega}$, any $k$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})$,
the core noise $\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{R})$ and
$\gamma_k = \|\llbracket\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}
= (\sum_{k \le i < 2k}\sigma_i(\mathbf{R})^2)^{1/2}$,
$$\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2 \le \|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
4\sqrt{k}\,\|\mathbf{N}\|_2\,\gamma_k + 12k\,\|\mathbf{N}\|_2^2\,.$$
Since $\gamma_k \le \min(\|\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}},
\sqrt{k}\,\sigma_k(\mathbf{R}))$, it sharpens the cross term $4\sqrt{2k}\,\gamma\,\|\mathbf{N}\|_2$
of `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm` (expanded), at the
price of $12k$ for $8k$ in the noise term. For the choice `truncatedSVD` makes.
No printed source. New (research note OP2, §2, D2, with the constants recomputed here).
Proof: M, about 80 lines. Core form `exists_core_generalizedNystrom` (it returns the basis
$\mathbf{Q}$ with $\mathbf{N} = \mathbf{Q}\mathbf{E}$ and
$\llbracket\mathsf{gn}\rrbracket_k = \mathbf{Q}\mathbf{Y}$): the error is
$\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2 + \|\mathbf{B} - \mathbf{P}(\mathbf{B} +
\mathbf{E})\|_{\mathsf{F}}^2$
with $\mathbf{B} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}$ and $\mathbf{P}$ the range projector of the
best approximation $\mathbf{Y} = \mathbf{P}(\mathbf{B}+\mathbf{E})$. With
$\mathbf{P}_B$ the range projector of $\llbracket\mathbf{B}\rrbracket_k$, $x =
\|\llbracket\mathbf{B}\rrbracket_k\|_{\mathsf{F}}^2 - \|\mathbf{P}\mathbf{B}\|_{\mathsf{F}}^2$,
$w = \|\mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2$: (D1) optimality of $\mathbf{P}$ against
$\mathbf{P}_B$
gives $x + w \le 2\operatorname{Re}\langle(\mathbf{P} - \mathbf{P}_B)\mathbf{B}, \mathbf{E}\rangle +
2w$;
(D2) $\|(\mathbf{P} - \mathbf{P}_B)\mathbf{B}\|_{\mathsf{F}}^2 = x + 2\gamma_P^2$ with
$\gamma_P = \|\mathbf{P}(\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k)\|_{\mathsf{F}} \le \gamma_k$
(orthogonal row and column spaces of the two SVD pieces; Ky Fan
`exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm`-type bound for a rank-$k$ projector);
$\operatorname{rank}(\mathbf{P} - \mathbf{P}_B) \le 2k$ so the inner product is at most
$\sqrt{2k}\,\|\mathbf{E}\|_2\sqrt{x + 2\gamma_P^2}$; $w \le k\|\mathbf{E}\|_2^2$. With
$S = x + w$ and $u = \sqrt{S + 2\gamma_P^2}$: $u^2 - 2\gamma_P^2 \le 2\sqrt{2k}\,e\,u + 2ke^2$, so
$u \le \sqrt{2k}e + 2\sqrt{k}e + \sqrt2\gamma_P$ and
$S \le 4\sqrt{k}\,e\,\gamma_P + (6 + 4\sqrt2)ke^2$. -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm_mul_frobNorm
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 +
        4 * √(k : ℝ) * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) *
          frobNorm (truncatedSVD (rsvd A Ω - truncatedSVD (rsvd A Ω) k) k) +
        12 * k * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 2 := by
  obtain ⟨Q, E, Y, hQ, hP, -, hY, -, hsplit, hC, hE⟩ := exists_core_generalizedNystrom h k
  have hEq : specNorm E = specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) := by
    rw [← singularValues_zero_eq_specNorm, ← singularValues_zero_eq_specNorm, hE]
  have hr : rsvd A Ω = Q * (Qᴴ * A) := by
    change rangeProjector (A * Ω) * A = _
    rw [hP, Matrix.mul_assoc]
  have hγ : frobNorm (truncatedSVD (Qᴴ * A - truncatedSVD (Qᴴ * A) k) k) =
      frobNorm (truncatedSVD (rsvd A Ω - truncatedSVD (rsvd A Ω) k) k) := by
    rw [hr, ← lpGauge_two_matrixNorm, ← lpGauge_two_matrixNorm]
    exact SymmetricGauge.matrixNorm_congr _ (funext fun i => by
      rw [singularValues_truncatedSVD, singularValues_truncatedSVD,
        singularValues_sub_truncatedSVD, singularValues_sub_truncatedSVD,
        hQ.singularValues_mul_left])
  have hb := hY.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm
  rw [hsplit, frobNorm_sub_truncatedSVD_rsvd_sq, ← hγ, ← hC, ← hEq]
  linarith

/-- A best approximation is the projection of $\mathbf{C}$ onto its own column space:
$\mathbf{P}_{\mathbf{Y}}\mathbf{C} = \mathbf{Y}$. -/
private theorem IsBestRankApprox.rangeProjector_self_mul {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) : rangeProjector Y * C = Y := by
  classical
  have hPY : rangeProjector Y * Y = Y := rangeProjector_mul_self Y
  have hsplit := (isStarProjection_rangeProjector Y).frobNorm_sq_eq_add (C - Y)
  have e2 : (1 - rangeProjector Y) * (C - Y) = C - rangeProjector Y * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul, hPY,
      sub_self, sub_zero]
  have hrank : (rangeProjector Y * C).rank ≤ k :=
    (Matrix.rank_mul_le_left _ _).trans ((rank_rangeProjector Y).trans_le h.rank_le)
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _) (h.frobNorm_sub_le _ hrank) 2
  rw [e2] at hsplit
  have hsq : frobNorm (rangeProjector Y * (C - Y)) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  have h0 := frobNorm_eq_zero_iff.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  rwa [Matrix.mul_sub, hPY, sub_eq_zero] at h0

/-- The error of $\mathbf{P}(\mathbf{R} + \mathbf{N})$, for an orthogonal projector
$\mathbf{P}$, splits into three orthogonal pieces along
$\mathbf{R} = \llbracket\mathbf{R}\rrbracket_k +
(\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k)$. -/
private theorem frobNorm_sub_mul_add_sq_eq_add [DecidableEq m] {R : Matrix m n 𝕜}
    (N : Matrix m n 𝕜) {P : Matrix m m 𝕜} (hP : IsStarProjection P) (k : ℕ) :
    frobNorm (R - P * (R + N)) ^ 2 = frobNorm ((1 - P) * truncatedSVD R k) ^ 2 +
      frobNorm ((1 - P) * (R - truncatedSVD R k)) ^ 2 + frobNorm (P * N) ^ 2 := by
  set T := truncatedSVD R k
  have hTS : T * (R - T)ᴴ = 0 := by
    have hV := isStarProjection_rangeProjector Tᴴ
    have hRV : R * rangeProjector Tᴴ = T := mul_rangeProjector_conjTranspose_truncatedSVD R k
    rw [← hRV, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hV.conjTranspose_eq,
      Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (rangeProjector Tᴴ) (rangeProjector Tᴴ), hV.mul_self, sub_self]
  have e : R - P * (R + N) = ((1 - P) * T + (1 - P) * (R - T)) - P * N := by
    rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul]
    abel
  have h0 : frobInner ((1 - P) * T + (1 - P) * (R - T)) (P * N) = 0 := by
    rw [← Matrix.mul_add, add_sub_cancel, frobInner_comm]
    exact hP.frobInner_mul_one_sub_mul N R
  rw [e, frobNorm_sub_sq_of_frobInner_eq_zero h0, frobNorm_add_sq_of_mul_conjTranspose_eq_zero]
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ T, hTS,
    Matrix.mul_zero, Matrix.zero_mul]

/-- The reverse perturbed truncation for an arbitrary orthogonal projector $\mathbf{P}$ of rank
at most $k$ applied to $\mathbf{R} + \mathbf{N}$. -/
private theorem le_frobNorm_sub_mul_add_sq {R N : Matrix m n 𝕜} {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {k : ℕ} (hPk : P.rank ≤ k) (hk : 0 < k)
    (hgap : singularValues R k ^ 2 < singularValues R (k - 1) ^ 2) :
    frobNorm (R - truncatedSVD R k) ^ 2 + frobNorm (rangeProjector (truncatedSVD R k) * N) ^ 2 -
        frobNorm N ^ 4 / (singularValues R (k - 1) ^ 2 - singularValues R k ^ 2) ≤
      frobNorm (R - P * (R + N)) ^ 2 := by
  classical
  set T := truncatedSVD R k with hT
  set Pt := rangeProjector T
  set a := singularValues R (k - 1)
  set b := singularValues R k
  have hPt := isStarProjection_rangeProjector T
  have ha : 0 < a := by
    by_contra h0
    nlinarith [singularValues_nonneg R (k - 1), sq_nonneg b]
  have hrankT : T.rank = k := by
    rw [hT, rank_truncatedSVD, min_eq_left]
    have := (singularValues_pos_iff R).mp ha
    omega
  have hrankPt : Pt.rank = k := (rank_rangeProjector T).trans hrankT
  have hPtS : Pt * (R - T) = 0 := by
    rw [Matrix.mul_sub, rangeProjector_truncatedSVD_mul, rangeProjector_mul_self, sub_self]
  -- the right side splits into three orthogonal pieces
  have hrhs := frobNorm_sub_mul_add_sq_eq_add (R := R) N hP k
  have hS2 := hP.frobNorm_sq_eq_add (R - T)
  -- the leading block loses at least `a ^ 2 * t`
  have h4 : a ^ 2 * frobNorm ((1 - P) * Pt) ^ 2 ≤ frobNorm ((1 - P) * T) ^ 2 := by
    have hpinv : specNorm (pinv T) = a⁻¹ := by
      rw [specNorm_pinv T (k := k - 1) (by omega), hT, singularValues_truncatedSVD,
        if_pos (by omega)]
    have h := frobNorm_mul_le_frobNorm_mul_specNorm ((1 - P) * T) (pinv T)
    rw [Matrix.mul_assoc, mul_pinv, hpinv] at h
    have h' := (le_mul_inv_iff₀ ha).mp h
    rw [← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (by positivity) h' 2
  have hflip : frobNorm (P * (1 - Pt)) = frobNorm ((1 - Pt) * P) := by
    rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, hP.conjTranspose_eq,
      hPt.one_sub.conjTranspose_eq]
  -- the trailing block gains at most `b ^ 2 * u`
  have h5 : frobNorm (P * (R - T)) ^ 2 ≤ b ^ 2 * frobNorm ((1 - Pt) * P) ^ 2 := by
    have e : P * (R - T) = P * (1 - Pt) * (R - T) := by
      rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPtS, sub_zero]
    have h := frobNorm_mul_le_frobNorm_mul_specNorm (P * (1 - Pt)) (R - T)
    rw [← e, hflip, hT, specNorm_sub_truncatedSVD, ← hT] at h
    have := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
    rw [mul_pow] at this
    linarith
  have hu : frobNorm ((1 - Pt) * P) ^ 2 ≤ frobNorm ((1 - P) * Pt) ^ 2 := by
    have h1 := hP.frobNorm_sq_eq_add Pt
    have h2 := hPt.frobNorm_sq_eq_add P
    have hflip' : frobNorm (Pt * P) = frobNorm (P * Pt) := by
      rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, hP.conjTranspose_eq,
        hPt.conjTranspose_eq]
    rw [hPt.frobNorm_sq_eq_rank, hrankPt] at h1
    rw [hP.frobNorm_sq_eq_rank, hflip'] at h2
    have : (P.rank : ℝ) ≤ k := by exact_mod_cast hPk
    linarith
  have hd : frobNorm (Pt - P) ^ 2 =
      frobNorm ((1 - P) * Pt) ^ 2 + frobNorm ((1 - Pt) * P) ^ 2 := by
    have e : Pt - P = (1 - P) * Pt - P * (1 - Pt) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    have h0 : frobInner ((1 - P) * Pt) (P * (1 - Pt)) = 0 := by
      rw [frobInner_mul_left, hP.one_sub.conjTranspose_eq, ← Matrix.mul_assoc, Matrix.sub_mul,
        Matrix.one_mul, hP.mul_self, sub_self, Matrix.zero_mul, frobInner_zero_right]
    rw [e, frobNorm_sub_sq_of_frobInner_eq_zero h0, hflip]
  have h8 : frobNorm (Pt * N) ^ 2 - frobNorm (P * N) ^ 2 ≤ frobNorm (Pt - P) * frobNorm N ^ 2 := by
    have hq : ∀ X : Matrix m m 𝕜, IsStarProjection X →
        frobNorm (X * N) ^ 2 = frobInner N (X * N) := fun X hX => by
      rw [← frobInner_self, frobInner_mul_left, hX.conjTranspose_eq, ← Matrix.mul_assoc,
        hX.mul_self]
    rw [hq Pt hPt, hq P hP, ← frobInner_sub_right, ← Matrix.sub_mul]
    refine (frobInner_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left (frobNorm_mul_le (Pt - P) N) (frobNorm_nonneg N)]
  have hg : 0 < a ^ 2 - b ^ 2 := by linarith
  have hw : frobNorm N ^ 4 / (a ^ 2 - b ^ 2) * (a ^ 2 - b ^ 2) = frobNorm N ^ 4 :=
    div_mul_cancel₀ _ hg.ne'
  have hde : 2 * frobNorm (Pt - P) * frobNorm N ^ 2 ≤
      (a ^ 2 - b ^ 2) * frobNorm (Pt - P) ^ 2 + frobNorm N ^ 4 / (a ^ 2 - b ^ 2) := by
    refine le_of_mul_le_mul_left ?_ hg
    nlinarith [sq_nonneg ((a ^ 2 - b ^ 2) * frobNorm (Pt - P) - frobNorm N ^ 2)]
  have hw0 : 0 ≤ frobNorm N ^ 4 / (a ^ 2 - b ^ 2) := by positivity
  rw [hrhs]
  nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ a ^ 2 + b ^ 2)]

/-- **The reverse perturbed truncation**: for $\mathbf{A} \in \Bbbk^{m \times n}$,
$\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and $\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$ has the rank of $\mathbf{A}\mathbf{\Omega}$,
$k \ge 1$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ with a gap
$g = \sigma_{k-1}(\mathbf{R})^2 - \sigma_k(\mathbf{R})^2 > 0$, and the core noise
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$,
$$\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2 -
\frac{\|\mathbf{N}\|_{\mathsf{F}}^4}{g} \le
\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
Truncated generalized Nyström keeps the noise that falls in the dominant subspace of
$\mathbf{R}$, up to a perturbation that vanishes as the gap grows. For the choice
`truncatedSVD` makes (the left side is choice-free under the gap).
No printed source. New (this design, §3.2, after research note OP2, §1).
Proof: M, about 80 lines. Core form as in the previous statement: the excess over
$\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2$ is $x + w$ with
$\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N} = \mathbf{Q}\mathbf{P}_B\mathbf{E}$. With
$\mathbf{B}\mathbf{B}^{\mathsf{H}} = \sum_i \lambda_i\mathbf{u}_i\mathbf{u}_i^{\mathsf{H}}$, $w_i =
\mathbf{u}_i^{\mathsf{H}}\mathbf{P}\mathbf{u}_i \in [0,1]$, $\sum_i w_i \le k$ and
$t = \sum_{i<k}(1 - w_i)$: $x \ge (\lambda_{k-1} - \lambda_k)\,t = g\,t$ (split the sums at $k$);
$\|\mathbf{P} - \mathbf{P}_B\|_{\mathsf{F}}^2 = \operatorname{tr}\mathbf{P} - k + 2t \le 2t$; and
$\lvert\|\mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2 - \|\mathbf{P}_B\mathbf{E}\|_{\mathsf{F}}^2\rvert =
\lvert\langle\mathbf{P} - \mathbf{P}_B, \mathbf{E}\mathbf{E}^{\mathsf{H}}\rangle\rvert \le
\sqrt{2t}\,\|\mathbf{E}\|_{\mathsf{F}}^2$. So $x + w \ge \|\mathbf{P}_B\mathbf{E}\|_{\mathsf{F}}^2 +
g t - \sqrt{2t}\,\|\mathbf{E}\|_{\mathsf{F}}^2 \ge \|\mathbf{P}_B\mathbf{E}\|_{\mathsf{F}}^2 -
\|\mathbf{E}\|_{\mathsf{F}}^4/(2g)$ (minimise the quadratic in $\sqrt t$; the statement drops the
factor $2$). -/
theorem le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) {k : ℕ} (hk : 0 < k)
    (hgap : singularValues (rsvd A Ω) k ^ 2 < singularValues (rsvd A Ω) (k - 1) ^ 2) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 +
        frobNorm (rangeProjector (truncatedSVD (rsvd A Ω) k) *
          (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω))) ^ 2 -
        frobNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 4 /
          (singularValues (rsvd A Ω) (k - 1) ^ 2 - singularValues (rsvd A Ω) k ^ 2) ≤
      frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 := by
  classical
  obtain ⟨Q, E, Y, hQ, hP, hQE, hY, hZ, hsplit, -, -⟩ := exists_core_generalizedNystrom h k
  have hR : rsvd A Ω = Q * (Qᴴ * A) := by
    change rangeProjector (A * Ω) * A = _
    rw [hP, Matrix.mul_assoc]
  have hPZ : rangeProjector (Q * Y) * (rsvd A Ω + Q * E) = Q * Y := by
    rw [hQ.rangeProjector_mul, hR, ← Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc Qᴴ, hQ.conjTranspose_mul_self, Matrix.one_mul,
      hY.rangeProjector_self_mul]
  have hYk : (rangeProjector (Q * Y)).rank ≤ k := by
    rw [rank_rangeProjector, hQ.rank_mul]
    exact hY.rank_le
  have key := le_frobNorm_sub_mul_add_sq (N := Q * E) (isStarProjection_rangeProjector (Q * Y))
    hYk hk hgap
  rw [hPZ, hR, ← Matrix.mul_sub, ← hR] at key
  simp only [hQ.frobNorm_mul_left] at key
  rw [hsplit, frobNorm_sub_truncatedSVD_rsvd_sq, ← hQE, hQ.frobNorm_mul_left]
  linarith

end NLAlib
