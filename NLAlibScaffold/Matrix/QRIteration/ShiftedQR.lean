/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.QRIteration.ShiftedQR
public import NLAlibScaffold.Matrix.Factorizations.GivensHessenberg

/-!
# The potential and the shifted QR step (scaffold)

Statements for `NLAlib/Matrix/QRIteration/ShiftedQR.lean` (stage SHIFTED-QR, waves W0–W1, design
note `docs/design/Eigensolvers-ShiftedQR.md` §3.1–§3.2): the last row of $p(\mathbf{H})$ for an
upper Hessenberg $\mathbf{H}$, the variational formula for the potential
[BanksGarzaVargasSrivastava2021, Lemma 2.3], the shifted QR step as a unitary similarity that
keeps the Hessenberg form and factors $p(\mathbf{H})$ ([BanksGarzaVargasSrivastava2022,
Lemma 3.2]), the bound $\psi_k(\widehat{\mathbf{H}}) \le \tau_p(\mathbf{H})$
([BanksGarzaVargasSrivastava2021, Lemma 2.5]), and the singular case, which the paper treats in
one line: a singular shift decouples exactly, and an exact zero on the subdiagonal persists.

## Main results

* `NLAlib.IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq`: the variational formula.
* `NLAlib.IsUpperHessenberg.exists_isQR_aeval_shiftPoly`: the step is a QR step of
  $p(\mathbf{H})$.
* `NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le`: the potential
  after the step is at most $\tau_p(\mathbf{H})$.
* `NLAlib.IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero`: a singular shift
  polynomial decouples.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-! ### The potential and the last row of a polynomial in a Hessenberg matrix -/

/-- **The $k$-th power of the potential is the product of the last $k$ subdiagonal moduli**:
for $k \ge 1$,
$\psi_k(\mathbf{H})^k = \prod_{n - k \le i < n}\lvert\mathbf{H}_{i+1,i}\rvert$.
Proof: `Real.rpow_inv_natCast_pow` on the nonnegative product (`Finset.prod_nonneg`).
S, about 5 lines. -/
theorem hessenbergPotential_pow {k : ℕ} (hk : 0 < k) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    hessenbergPotential k H ^ k =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖ := by
  unfold hessenbergPotential
  exact Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => norm_nonneg _) hk.ne'

/-- **The last row of $p(\mathbf{H})$ is supported on the last $k + 1$ columns**: for upper
Hessenberg $\mathbf{H}$ and a polynomial $p$ of degree at most $k$,
$p(\mathbf{H})_{n,j} = 0$ for $j + k < n$. [BanksGarzaVargasSrivastava2021, proof of
Lemma 2.3].
Proof: by linearity (`Polynomial.aeval_eq_sum_range`) reduce to $\mathbf{H}^i$, $i \le k$; show
by induction on $i$ that $(\mathbf{H}^i)_{a,j} = 0$ for $j + i < a$ (`pow_succ`,
`Matrix.mul_apply`, the Hessenberg zero pattern `NLAlib.IsUpperHessenberg`).
M, about 35 lines. -/
theorem IsUpperHessenberg.aeval_apply_last_eq_zero {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) {p : Polynomial ℂ} {k : ℕ} (hp : p.natDegree ≤ k)
    {j : Fin (n + 1)} (hj : (j : ℕ) + k < n) : Polynomial.aeval H p (Fin.last n) j = 0 := by
  sorry

/-- **The corner entry of the last row of $p(\mathbf{H})$ is the product of subdiagonals**: for
upper Hessenberg $\mathbf{H}$, monic $p$ of degree $k$ and the column $j$ with $j + k = n$,
$$p(\mathbf{H})_{n,j} = \prod_{n - k \le i < n}\mathbf{H}_{i+1,i}\,.$$
[BanksGarzaVargasSrivastava2021, proof of Lemma 2.3].
Proof: with the induction of `NLAlib.IsUpperHessenberg.aeval_apply_last_eq_zero` strengthened to
$(\mathbf{H}^i)_{a,a-i} = \prod_{a - i \le l < a}\mathbf{H}_{l+1,l}$; the terms of degree below
$k$ vanish at that column, and the leading coefficient is $1$
(`Polynomial.Monic.coeff_natDegree`). M, about 45 lines. -/
theorem IsUpperHessenberg.aeval_apply_last_eq_prod {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) {p : Polynomial ℂ} (hp : p.Monic) {k : ℕ} (hpk : p.natDegree = k)
    {j : Fin (n + 1)} (hj : (j : ℕ) + k = n) :
    Polynomial.aeval H p (Fin.last n) j =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), H i.succ i.castSucc := by
  sorry

/-- **The potential bounds every monic polynomial's last row from below**: for upper Hessenberg
$\mathbf{H}$, $1 \le k \le n$ and monic $p$ of degree $k$,
$\psi_k(\mathbf{H})^k \le \|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$.
[BanksGarzaVargasSrivastava2021, Lemma 2.3], the lower bound.
Proof: the norm of the row is at least the modulus of its entry at column $n - k$
(`EuclideanSpace.norm_eq`, `Finset.single_le_sum`), which is the product of
`NLAlib.IsUpperHessenberg.aeval_apply_last_eq_prod`; then `NLAlib.hessenbergPotential_pow` and
`norm_prod`. S, about 15 lines. -/
theorem IsUpperHessenberg.hessenbergPotential_pow_le_norm_aeval
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {p : Polynomial ℂ}
    (hp : p.Monic) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (hpk : p.natDegree = k) :
    hessenbergPotential k H ^ k ≤ ‖WithLp.toLp 2 (Polynomial.aeval H p (Fin.last n))‖ := by
  sorry

/-- **The variational formula for the potential**: for upper Hessenberg $\mathbf{H}$ and
$1 \le k \le n$, the characteristic polynomial $\chi_k$ of the trailing block
$\mathbf{H}_{(k)}$ attains the lower bound,
$$\|\mathbf{e}_n^{\mathsf{H}}\chi_k(\mathbf{H})\| = \psi_k(\mathbf{H})^k\,,$$
so $\psi_k(\mathbf{H})^k = \min_p \|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$ over monic $p$ of
degree $k$. [BanksGarzaVargasSrivastava2021, Lemma 2.3]; [TrefethenBau1997, Theorem 34.1].
Proof: for $i \le k$ the last row of $\mathbf{H}^i$, restricted to the last $k$ columns, is the
last row of $\mathbf{H}_{(k)}^i$ (induction on $i$: for $i < k$ the row of $\mathbf{H}^i$ is
supported on the last $k$ columns, and there right multiplication by $\mathbf{H}$ only uses the
trailing block); so for $\deg p \le k$ the last $k$ entries of the row of $p(\mathbf{H})$ are
those of $\mathbf{e}_k^{\mathsf{H}}p(\mathbf{H}_{(k)})$. With Cayley–Hamilton
(`Matrix.aeval_self_charpoly`) they vanish for $\chi_k$; the entries before column $n - k$ vanish by
`NLAlib.IsUpperHessenberg.aeval_apply_last_eq_zero`, and the remaining one is the product of
`NLAlib.IsUpperHessenberg.aeval_apply_last_eq_prod` (`Matrix.charpoly_monic`,
`Matrix.charpoly_natDegree_eq_dim`). L, about 90 lines (split the restriction lemma off). -/
theorem IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) :
    ‖WithLp.toLp 2 (Polynomial.aeval H (trailingBlock k H).charpoly (Fin.last n))‖ =
      hessenbergPotential k H ^ k := by
  sorry

/-- **The potential is at most the norm**: for $1 \le k \le n$,
$\psi_k(\mathbf{H}) \le \|\mathbf{H}\|_2$. [BanksGarzaVargasSrivastava2021, proof of
Theorem 1.6].
Proof: each entry is at most the spectral norm (`NLAlib.norm_apply_le_specNorm` or the row
bound); the product of $k$ such factors is at most $\|\mathbf{H}\|_2^k$ (`Finset.prod_le_pow_card`
with the filter of card $k$), and take $k$-th roots (`Real.rpow_le_rpow`). S, about 20 lines. -/
theorem hessenbergPotential_le_specNorm {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : hessenbergPotential k H ≤ specNorm H := by
  sorry

/-- **A small potential means decoupling**: for $1 \le k \le n$ and $\delta \ge 0$, if
$\psi_k(\mathbf{H}) \le \delta\|\mathbf{H}\|_2$ then some subdiagonal entry has
$\lvert\mathbf{H}_{i+1,i}\rvert \le \delta\|\mathbf{H}\|_2$. [BanksGarzaVargasSrivastava2021,
proof of Theorem 1.6].
Proof: the geometric mean of the $k$ factors is at least their minimum (take the minimising
index `Finset.exists_min_image`; `Finset.pow_card_le_prod`), then `NLAlib.hessenbergPotential_pow`.
S, about 20 lines. -/
theorem isDecoupled_of_hessenbergPotential_le {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) {δ : ℝ}
    (hδ : 0 ≤ δ) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : hessenbergPotential k H ≤ δ * specNorm H) : IsDecoupled δ H := by
  sorry

/-! ### The shifted QR step -/

/-- **The shifted QR step keeps the Hessenberg form**: for upper Hessenberg $\mathbf{H}$ and any
shift $s$, `NLAlib.shiftedQRStep` $\mathbf{H}$ $s$ is upper Hessenberg, also when
$\mathbf{H} - s\mathbf{I}$ is singular.
Proof: with $\mathbf{Q}$, $\mathbf{R}$ the Givens factors of $\mathbf{H} - s\mathbf{I}$,
$\mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q} = \mathbf{R}\mathbf{Q} + s\mathbf{I}$
(`NLAlib.IsQR.mul_add_smul_one_eq` with `NLAlib.isQR_givensHessenberg`), $\mathbf{R}$
upper triangular
(`NLAlib.isUpperTrapezoidal_givensHessenbergR`) and $\mathbf{Q}$ upper Hessenberg
(`NLAlib.isUpperHessenberg_givensHessenbergQ`); `NLAlib.IsUpperHessenberg.isUpperTriangular_mul`.
S, about 20 lines. -/
theorem IsUpperHessenberg.isUpperHessenberg_shiftedQRStep {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (s : ℂ) : IsUpperHessenberg (shiftedQRStep H s) := by
  sorry

/-- **The multi-shift QR step keeps the Hessenberg form**: for upper Hessenberg $\mathbf{H}$
and any list of shifts, `NLAlib.multiShiftedQRStep` $\mathbf{H}$ `ss` is upper Hessenberg.
Proof: induction on `ss` (`List.foldl_cons`) with
`NLAlib.IsUpperHessenberg.isUpperHessenberg_shiftedQRStep`.
S, about 6 lines. -/
theorem IsUpperHessenberg.isUpperHessenberg_multiShiftedQRStep
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (ss : List ℂ) :
    IsUpperHessenberg (multiShiftedQRStep H ss) := by
  sorry

/-- **The multi-shift QR step is a QR step of the shift polynomial**: for upper Hessenberg
$\mathbf{H}$ and shifts $s_1, \dots, s_k$, there are $\mathbf{Q}$ unitary and $\mathbf{R}$
upper triangular with $p(\mathbf{H}) = \mathbf{Q}\mathbf{R}$, $p(z) = \prod_i (z - s_i)$, and
`NLAlib.multiShiftedQRStep` $\mathbf{H}$ `ss` $= \mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}$. No
invertibility is assumed. [BanksGarzaVargasSrivastava2022, Lemma 3.2], there for invertible
$p(\mathbf{H})$ with the positive-diagonal factorization.
Proof: induction on the list, generalising $\mathbf{H}$. With $\mathbf{H} - s_1\mathbf{I} =
\mathbf{Q}_1\mathbf{R}_1$ (`NLAlib.isQR_givensHessenberg`) and
$\mathbf{H}_2 = \mathbf{Q}_1^{\mathsf{H}}\mathbf{H}\mathbf{Q}_1$ Hessenberg, the hypothesis gives
$q(\mathbf{H}_2) = \mathbf{Q}'\mathbf{R}'$ for the remaining shifts; then
$p(\mathbf{H}) = q(\mathbf{H})(\mathbf{H} - s_1\mathbf{I}) =
\mathbf{Q}_1 q(\mathbf{H}_2)\mathbf{Q}_1^{\mathsf{H}}\mathbf{Q}_1\mathbf{R}_1 =
(\mathbf{Q}_1\mathbf{Q}')(\mathbf{R}'\mathbf{R}_1)$ (`Polynomial.aeval_algHom_apply` for the
conjugation, commutativity of polynomials in $\mathbf{H}$, `Matrix.IsUpperTriangular.mul`,
`NLAlib.HasOrthonormalCols.mul`). M, about 50 lines. -/
theorem IsUpperHessenberg.exists_isQR_aeval_shiftPoly {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (ss : List ℂ) :
    ∃ Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsQR (Polynomial.aeval H (shiftPoly ss)) Q R ∧ multiShiftedQRStep H ss = Qᴴ * H * Q := by
  sorry

/-- **The multi-shift QR step preserves the norm**:
$\|\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})\|_2 = \|\mathbf{H}\|_2$.
Proof: each single step is a unitary similarity
(`NLAlib.hasOrthonormalCols_givensHessenbergState_fst`; unitary invariance of `NLAlib.specNorm`);
induction on the list. S, about 12 lines. -/
theorem specNorm_multiShiftedQRStep (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    specNorm (multiShiftedQRStep H ss) = specNorm H := by
  sorry

/-- **The multi-shift QR step carries the eigenvector matrix**: if
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
then $\widehat{\mathbf{H}} = \mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has
$\widehat{\mathbf{H}}\mathbf{V}' = \mathbf{V}'\operatorname{diag}(\mathbf{d})$ for an invertible
$\mathbf{V}'$ with the same condition number, $\|\mathbf{V}'\|_2\|\mathbf{V}'^{-1}\|_2 =
\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$; so $\kappa_V$ is invariant along the iteration.
[BanksGarzaVargasSrivastava2021, §4].
Proof: $\mathbf{V}' = \mathbf{Q}^{\mathsf{H}}\mathbf{V}$ for the accumulated unitary
$\mathbf{Q}$; `NLAlib.pseudoConditionNumber_of_isUnit` and unitary invariance of the norm; induction
on the list. S, about 25 lines. -/
theorem exists_isUnit_mul_eq_mul_diagonal_multiShiftedQRStep
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (ss : List ℂ) :
    ∃ V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnit V' ∧
      multiShiftedQRStep H ss * V' = V' * Matrix.diagonal d ∧
      pseudoConditionNumber V' = pseudoConditionNumber V := by
  sorry

/-- **The potential after a QR step is at most $\tau_p$**: for upper Hessenberg $\mathbf{H}$,
shifts $s_1, \dots, s_k$ with $1 \le k \le n$ and $p(\mathbf{H})$ invertible,
$p(z) = \prod_i (z - s_i)$,
$$\psi_k(\widehat{\mathbf{H}})^k\,\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-1}\| \le 1\,,
\qquad \widehat{\mathbf{H}} = \mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})\,,$$
that is $\psi_k(\widehat{\mathbf{H}}) \le \tau_p(\mathbf{H}) =
\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-1}\|^{-1/k}$.
[BanksGarzaVargasSrivastava2021, Lemma 2.5], the invertible case.
Proof: with $p(\mathbf{H}) = \mathbf{Q}\mathbf{R}$ from
`NLAlib.IsUpperHessenberg.exists_isQR_aeval_shiftPoly`, $p(\widehat{\mathbf{H}}) =
\mathbf{Q}^{\mathsf{H}}p(\mathbf{H})\mathbf{Q} = \mathbf{R}\mathbf{Q}$, so
$\|\mathbf{e}_n^{\mathsf{H}}p(\widehat{\mathbf{H}})\| = \|\mathbf{e}_n^{\mathsf{H}}\mathbf{R}\| =
\lvert\mathbf{R}_{n,n}\rvert$ ($\mathbf{R}$ triangular, $\mathbf{Q}$ unitary), and
$\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-1} = \mathbf{R}_{n,n}^{-1}\mathbf{e}_n^{\mathsf{H}}
\mathbf{Q}^{\mathsf{H}}$ has norm $\lvert\mathbf{R}_{n,n}\rvert^{-1}$; the potential of
$\widehat{\mathbf{H}}$ (Hessenberg,
`NLAlib.IsUpperHessenberg.isUpperHessenberg_multiShiftedQRStep`) is bounded by
`NLAlib.IsUpperHessenberg.hessenbergPotential_pow_le_norm_aeval` (`shiftPoly` is monic of degree
$k$: `Polynomial.monic_multiset_prod_of_monic`, `Polynomial.natDegree_multiset_prod_of_monic`).
M, about 50 lines. -/
theorem IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {ss : List ℂ}
    (hk : 0 < ss.length) (hkn : ss.length ≤ n) (hp : IsUnit (Polynomial.aeval H (shiftPoly ss))) :
    hessenbergPotential ss.length (multiShiftedQRStep H ss) ^ ss.length *
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖ ≤ 1 := by
  sorry

/-- **A zero subdiagonal entry persists under a shifted QR step**: for upper Hessenberg
$\mathbf{H}$ with $\mathbf{H}_{i+1,i} = 0$ and any shift $s$, the step has
$(\mathsf{shiftedQRStep}(\mathbf{H}, s))_{i+1,i} = 0$.
Proof: in Givens QR of $\mathbf{H} - s\mathbf{I}$, row $i + 1$ is untouched before step $i$, so
step $i$ rotates the pair $(u, 0)$ and its rotation is diagonal (`NLAlib.givensCoeffs_snd_zero`);
hence the unitary factor has $\mathbf{Q}_{i+1,i} = 0$ besides being Hessenberg, and
$(\mathbf{R}\mathbf{Q})_{i+1,i} = \sum_{l \ge i+1}\mathbf{R}_{i+1,l}\mathbf{Q}_{l,i} = 0$.
M, about 50 lines. -/
theorem IsUpperHessenberg.shiftedQRStep_apply_succ_castSucc_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {i : Fin n}
    (hi : H i.succ i.castSucc = 0) (s : ℂ) : shiftedQRStep H s i.succ i.castSucc = 0 := by
  sorry

/-- **A reduced Hessenberg matrix stays reduced under multi-shift QR steps**: for upper
Hessenberg $\mathbf{H}$ with a zero subdiagonal entry, every
$\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has one (at the same index).
Proof: induction on `ss` with
`NLAlib.IsUpperHessenberg.shiftedQRStep_apply_succ_castSucc_eq_zero` and
`NLAlib.IsUpperHessenberg.isUpperHessenberg_shiftedQRStep`; `IsDecoupled 0` is a zero entry
(`norm_le_zero_iff`).
S, about 12 lines. -/
theorem IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (h : IsDecoupled 0 H)
    (ss : List ℂ) : IsDecoupled 0 (multiShiftedQRStep H ss) := by
  sorry

/-- **A singular shift decouples exactly**: for upper Hessenberg $\mathbf{H}$ of size at least
$2$ and a shift $s$ with $\det(\mathbf{H} - s\mathbf{I}) = 0$, the step
$\mathsf{shiftedQRStep}(\mathbf{H}, s)$ has a zero subdiagonal entry.
[BanksGarzaVargasSrivastava2021, proof of Lemma 2.5], where the claim that $\mathbf{R}_{n,n} = 0$
for every QR factorization is used without the unreduced hypothesis it needs.
Proof: if $\mathbf{H}$ is already reduced, by
`NLAlib.IsUpperHessenberg.shiftedQRStep_apply_succ_castSucc_eq_zero`. Otherwise the first $n$
columns of $\mathbf{H} - s\mathbf{I}$ are independent (nonzero subdiagonal), so the Givens
pivots $\mathbf{R}_{i,i}$, $i < n$, are nonzero
(`NLAlib.forall_givensHessenbergR_apply_self_ne_zero_iff` on the leading columns) and
$\det = 0$ forces $\mathbf{R}_{n,n} = 0$; then the last row of $\mathbf{R}\mathbf{Q}$ is
$\mathbf{R}_{n,n}\mathbf{e}_n^{\mathsf{H}}\mathbf{Q} = \mathbf{0}$, so the entry $(n, n - 1)$ of
$\mathbf{R}\mathbf{Q} + s\mathbf{I}$ vanishes. L, about 70 lines (the leading-block rank step). -/
theorem IsUpperHessenberg.isDecoupled_zero_shiftedQRStep_of_det_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (hn : 0 < n) {s : ℂ}
    (hs : (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0) :
    IsDecoupled 0 (shiftedQRStep H s) := by
  sorry

/-- **A singular shift polynomial decouples exactly**: for upper Hessenberg $\mathbf{H}$ of size
at least $2$ and shifts with $\det p(\mathbf{H}) = 0$, $p(z) = \prod_i (z - s_i)$, the step
$\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has a zero subdiagonal entry. This is the
singular case of [BanksGarzaVargasSrivastava2021, Lemma 2.5], where it reads
$\psi_k(\widehat{\mathbf{H}}) = 0$.
Proof: $\det p(\mathbf{H}) = \prod_i \det(\mathbf{H} - s_i\mathbf{I})$ (`Matrix.det_mul`,
`List.prod`), so some $s_j$ is an eigenvalue; the intermediate matrix before shift $s_j$ is
unitarily similar to $\mathbf{H}$, so its shift is singular too
(`NLAlib.IsUpperHessenberg.isDecoupled_zero_shiftedQRStep_of_det_eq_zero`), and the zero persists
(`NLAlib.IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep`). Induction on the list.
M, about 40 lines. -/
theorem IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (hn : 0 < n)
    {ss : List ℂ} (h : (Polynomial.aeval H (shiftPoly ss)).det = 0) :
    IsDecoupled 0 (multiShiftedQRStep H ss) := by
  sorry

end NLAlib
